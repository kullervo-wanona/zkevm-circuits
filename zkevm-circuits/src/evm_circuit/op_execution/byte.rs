use super::super::{
    BusMappingLookup, Case, Cell, Constraint, ExecutionStep, Lookup, Word,
};
use super::{
    CaseAllocation, CaseConfig, CoreStateInstance, OpExecutionState, OpGadget,
};
use bus_mapping::evm::OpcodeId;
use halo2::plonk::Error;
use halo2::{arithmetic::FieldExt, circuit::Region, plonk::Expression};
use std::convert::TryInto;

pub const GC_DELTA: u64 = 3;
pub const PC_DELTA: u64 = 1;
pub const SP_DELTA: u64 = 1;
pub const GAS: u64 = 3;

pub const OPCODE: OpcodeId = OpcodeId::BYTE;

#[derive(Clone, Debug)]
struct ByteSuccessAllocation<F> {
    case_selector: Cell<F>,
    word_idx: Word<F>,
    value: Word<F>,
    result: Word<F>,
    sum_inv: Cell<F>,
    diff_inv: [Cell<F>; 32],
}

#[derive(Clone, Debug)]
pub struct ByteGadget<F> {
    success: ByteSuccessAllocation<F>,
    stack_underflow: Cell<F>, // case selector
    out_of_gas: (
        Cell<F>, // case selector
        Cell<F>, // gas available
    ),
}

impl<F: FieldExt> OpGadget<F> for ByteGadget<F> {
    const RESPONSIBLE_OPCODES: &'static [OpcodeId] = &[OPCODE];

    const CASE_CONFIGS: &'static [CaseConfig] = &[
        CaseConfig {
            case: Case::Success,
            num_word: 3,  // value + idx + result
            num_cell: 33, // sum_inv + 32 diff_inv
            will_halt: false,
        },
        CaseConfig {
            case: Case::StackUnderflow,
            num_word: 0,
            num_cell: 0,
            will_halt: true,
        },
        CaseConfig {
            case: Case::OutOfGas,
            num_word: 0,
            num_cell: 0,
            will_halt: true,
        },
    ];

    fn construct(case_allocations: Vec<CaseAllocation<F>>) -> Self {
        let [mut success, stack_underflow, out_of_gas]: [CaseAllocation<F>; 3] =
            case_allocations.try_into().unwrap();
        Self {
            success: ByteSuccessAllocation {
                case_selector: success.selector.clone(),
                word_idx: success.words.pop().unwrap(),
                value: success.words.pop().unwrap(),
                result: success.words.pop().unwrap(),
                sum_inv: success.cells.pop().unwrap(),
                diff_inv: success.cells.try_into().unwrap(),
            },
            stack_underflow: stack_underflow.selector.clone(),
            out_of_gas: (
                out_of_gas.selector.clone(),
                out_of_gas.resumption.unwrap().gas_available.clone(),
            ),
        }
    }

    fn constraints(
        &self,
        state_curr: &OpExecutionState<F>,
        state_next: &OpExecutionState<F>,
    ) -> Vec<Constraint<F>> {
        let byte = Expression::Constant(F::from_u64(OPCODE.as_u8().into()));
        let OpExecutionState { opcode, .. } = &state_curr;
        let common_polys = vec![(opcode.expr() - byte.clone())];

        let success = {
            // interpreter state transition constraints
            let one = Expression::Constant(F::from_u64(1));
            let state_transition_constraints = vec![
                state_next.global_counter.expr()
                    - (state_curr.global_counter.expr()
                        + Expression::Constant(F::from_u64(GC_DELTA))),
                state_next.stack_pointer.expr()
                    - (state_curr.stack_pointer.expr()
                        + Expression::Constant(F::from_u64(SP_DELTA))),
                state_next.program_counter.expr()
                    - (state_curr.program_counter.expr()
                        + Expression::Constant(F::from_u64(PC_DELTA))),
                state_next.gas_counter.expr()
                    - (state_curr.gas_counter.expr()
                        + Expression::Constant(F::from_u64(GAS))),
            ];

            let ByteSuccessAllocation {
                case_selector,
                value,
                word_idx,
                result,
                sum_inv,
                diff_inv,
            } = &self.success;

            // If any of the non-LSB bytes are non-zero of the index word we never need to copy any bytes.
            // So just sum all the non-LSB byte values here and then check if it's non-zero
            // so we can use that as an additional condition when to copy the byte value.
            let mut index_byte_sum = Expression::Constant(F::from_u64(0));
            for idx in 1..32 {
                index_byte_sum =
                    index_byte_sum + word_idx.cells[idx as usize].expr()
            }
            let is_sum_zero_expression =
                one.clone() - index_byte_sum.clone() * sum_inv.expr();
            let mut byte_constraints = vec![];
            let mut is_zero_constraints = vec![
                index_byte_sum.clone() * is_sum_zero_expression.clone(),
                sum_inv.expr().clone() * is_sum_zero_expression.clone(),
            ];
            byte_constraints.append(&mut is_zero_constraints);

            // Now we just need to check that `result` is the sum of all copied bytes.
            // We go byte by byte and check if `idx - stack.idx` is zero.
            // If it's zero (at most once) we add the byte value to the sum, else we add 0.
            // The additional condition for this is that none of the non-LSB bytes are non-zero, see above.
            // At the end this sum needs to equal result.
            let mut result_sum_expr = result.cells[0].expr();
            for idx in 0..32 {
                // Check if this byte was selected looking only at the LSB of the index word
                let diff = word_idx.cells[0].expr()
                    - Expression::Constant(F::from_u64(31 - idx));
                let is_zero_expression =
                    one.clone() - diff.clone() * diff_inv[idx as usize].expr();
                let mut is_zero_constraints = vec![
                    diff * is_zero_expression.clone(),
                    diff_inv[idx as usize].expr().clone()
                        * is_zero_expression.clone(),
                ];
                byte_constraints.append(&mut is_zero_constraints);

                // Add the byte to the sum when this byte was selected
                result_sum_expr = result_sum_expr
                    - is_zero_expression
                        * is_sum_zero_expression.clone()
                        * value.cells[idx as usize].expr();
            }
            byte_constraints.push(result_sum_expr);

            // All bytes of result, except for the LSB, always need to be 0.
            for idx in 1..32 {
                byte_constraints.push(result.cells[idx as usize].expr());
            }

            #[allow(clippy::suspicious_operation_groupings)]
            let bus_mapping_lookups = vec![
                Lookup::BusMappingLookup(BusMappingLookup::Stack {
                    index_offset: 0,
                    value: word_idx.expr(),
                    is_write: false,
                }),
                Lookup::BusMappingLookup(BusMappingLookup::Stack {
                    index_offset: 1,
                    value: value.expr(),
                    is_write: false,
                }),
                Lookup::BusMappingLookup(BusMappingLookup::Stack {
                    index_offset: 1,
                    value: result.expr(),
                    is_write: true,
                }),
            ];

            Constraint {
                name: "ByteGadget success",
                selector: case_selector.expr(),
                polys: [
                    common_polys.clone(),
                    state_transition_constraints,
                    byte_constraints,
                ]
                .concat(),
                lookups: bus_mapping_lookups,
            }
        };

        let stack_underflow = {
            let (zero, minus_one) = (
                Expression::Constant(F::from_u64(1024)),
                Expression::Constant(F::from_u64(1023)),
            );
            let stack_pointer = state_curr.stack_pointer.expr();
            Constraint {
                name: "Byte stack underflow",
                selector: self.stack_underflow.expr(),
                polys: vec![
                    common_polys.clone(),
                    vec![
                        (stack_pointer.clone() - zero)
                            * (stack_pointer - minus_one),
                    ],
                ]
                .concat(),
                lookups: vec![],
            }
        };

        let out_of_gas = {
            let (one, two, three) = (
                Expression::Constant(F::from_u64(1)),
                Expression::Constant(F::from_u64(2)),
                Expression::Constant(F::from_u64(3)),
            );
            let (case_selector, gas_available) = &self.out_of_gas;
            let gas_overdemand = state_curr.gas_counter.expr() + three.clone()
                - gas_available.expr();
            Constraint {
                name: "BYTE out of gas",
                selector: case_selector.expr(),
                polys: [
                    common_polys,
                    vec![
                        (gas_overdemand.clone() - one)
                            * (gas_overdemand.clone() - two)
                            * (gas_overdemand - three),
                    ],
                ]
                .concat(),
                lookups: vec![],
            }
        };

        vec![success, stack_underflow, out_of_gas]
    }

    fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        op_execution_state: &mut CoreStateInstance,
        execution_step: &ExecutionStep,
    ) -> Result<(), Error> {
        match execution_step.case {
            Case::Success => self.assign_success(
                region,
                offset,
                op_execution_state,
                execution_step,
            ),
            Case::StackOverflow => {
                unimplemented!()
            }
            Case::OutOfGas => {
                unimplemented!()
            }
            _ => unreachable!(),
        }
    }
}

impl<F: FieldExt> ByteGadget<F> {
    fn assign_success(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        op_execution_state: &mut CoreStateInstance,
        execution_step: &ExecutionStep,
    ) -> Result<(), Error> {
        op_execution_state.global_counter += GC_DELTA as usize;
        op_execution_state.program_counter += PC_DELTA as usize;
        op_execution_state.stack_pointer += SP_DELTA as usize;
        op_execution_state.gas_counter += GAS as usize;

        self.success.word_idx.assign(
            region,
            offset,
            Some(execution_step.values[0]),
        )?;
        self.success.value.assign(
            region,
            offset,
            Some(execution_step.values[1]),
        )?;
        self.success.result.assign(
            region,
            offset,
            Some(execution_step.values[2]),
        )?;

        for (i, alloc) in self.success.diff_inv.iter().enumerate() {
            let diff_inv = (F::from_u64(execution_step.values[0][0] as u64)
                - F::from_u64((31 - i) as u64))
            .invert()
            .unwrap_or(F::zero());
            alloc.assign(region, offset, Some(diff_inv))?;
        }

        let mut byte_sum = F::from_u64(0);
        for idx in 1..32 {
            byte_sum += F::from_u64(execution_step.values[0][idx] as u64);
        }
        let sum_inv = byte_sum.invert().unwrap_or(F::zero());
        self.success.sum_inv.assign(region, offset, Some(sum_inv))?;

        self.success
            .case_selector
            .assign(region, offset, Some(F::from_u64(1)))
            .unwrap();
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::super::super::{
        test::TestCircuit, Case, ExecutionStep, Operation,
    };
    use bus_mapping::{evm::OpcodeId, operation::Target};
    use halo2::{arithmetic::FieldExt, dev::MockProver};
    use pasta_curves::pallas::Base;

    macro_rules! try_test_circuit {
        ($execution_steps:expr, $operations:expr, $result:expr) => {{
            let circuit =
                TestCircuit::<Base>::new($execution_steps, $operations);
            let prover = MockProver::<Base>::run(10, &circuit, vec![]).unwrap();
            assert_eq!(prover.verify(), $result);
        }};
    }

    #[test]
    fn byte_gadget() {
        // Select byte 29 (MSB is at 0)
        try_test_circuit!(
            vec![
                ExecutionStep {
                    opcode: OpcodeId::PUSH3,
                    case: Case::Success,
                    values: vec![
                        [
                            1, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, //
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ],
                        [
                            1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, //
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ]
                    ],
                },
                ExecutionStep {
                    opcode: OpcodeId::PUSH1,
                    case: Case::Success,
                    values: vec![
                        [
                            29, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, //
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ],
                        [
                            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, //
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ]
                    ],
                },
                ExecutionStep {
                    opcode: OpcodeId::BYTE,
                    case: Case::Success,
                    values: vec![
                        [
                            29, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, //
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ],
                        [
                            1, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, //
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ],
                        [
                            3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, //
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ]
                    ],
                }
            ],
            vec![
                Operation {
                    gc: 1,
                    target: Target::Stack,
                    is_write: true,
                    values: [
                        Base::zero(),
                        Base::from_u64(1023),
                        Base::from_u64(1 + 2 + 3),
                        Base::zero(),
                    ]
                },
                Operation {
                    gc: 2,
                    target: Target::Stack,
                    is_write: true,
                    values: [
                        Base::zero(),
                        Base::from_u64(1022),
                        Base::from_u64(29),
                        Base::zero(),
                    ]
                },
                Operation {
                    gc: 3,
                    target: Target::Stack,
                    is_write: false,
                    values: [
                        Base::zero(),
                        Base::from_u64(1022),
                        Base::from_u64(29),
                        Base::zero(),
                    ]
                },
                Operation {
                    gc: 4,
                    target: Target::Stack,
                    is_write: false,
                    values: [
                        Base::zero(),
                        Base::from_u64(1023),
                        Base::from_u64(1 + 2 + 3),
                        Base::zero(),
                    ]
                },
                Operation {
                    gc: 5,
                    target: Target::Stack,
                    is_write: true,
                    values: [
                        Base::zero(),
                        Base::from_u64(1023),
                        Base::from_u64(3),
                        Base::zero(),
                    ]
                },
            ],
            Ok(())
        );
        // Select byte 256 + 29
        try_test_circuit!(
            vec![
                ExecutionStep {
                    opcode: OpcodeId::PUSH3,
                    case: Case::Success,
                    values: vec![
                        [
                            1, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, //
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ],
                        [
                            1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, //
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ]
                    ],
                },
                ExecutionStep {
                    opcode: OpcodeId::PUSH2,
                    case: Case::Success,
                    values: vec![
                        [
                            29, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, //
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ],
                        [
                            1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, //
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ]
                    ],
                },
                ExecutionStep {
                    opcode: OpcodeId::BYTE,
                    case: Case::Success,
                    values: vec![
                        [
                            29, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, //
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ],
                        [
                            1, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, //
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ],
                        [
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, //
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ]
                    ],
                }
            ],
            vec![
                Operation {
                    gc: 1,
                    target: Target::Stack,
                    is_write: true,
                    values: [
                        Base::zero(),
                        Base::from_u64(1023),
                        Base::from_u64(1 + 2 + 3),
                        Base::zero(),
                    ]
                },
                Operation {
                    gc: 2,
                    target: Target::Stack,
                    is_write: true,
                    values: [
                        Base::zero(),
                        Base::from_u64(1022),
                        Base::from_u64(1 + 29),
                        Base::zero(),
                    ]
                },
                Operation {
                    gc: 3,
                    target: Target::Stack,
                    is_write: false,
                    values: [
                        Base::zero(),
                        Base::from_u64(1022),
                        Base::from_u64(1 + 29),
                        Base::zero(),
                    ]
                },
                Operation {
                    gc: 4,
                    target: Target::Stack,
                    is_write: false,
                    values: [
                        Base::zero(),
                        Base::from_u64(1023),
                        Base::from_u64(1 + 2 + 3),
                        Base::zero(),
                    ]
                },
                Operation {
                    gc: 5,
                    target: Target::Stack,
                    is_write: true,
                    values: [
                        Base::zero(),
                        Base::from_u64(1023),
                        Base::from_u64(0),
                        Base::zero(),
                    ]
                },
            ],
            Ok(())
        );
    }
}
