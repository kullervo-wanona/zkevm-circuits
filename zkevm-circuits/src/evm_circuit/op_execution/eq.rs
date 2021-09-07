use super::super::{
    BusMappingLookup, Case, Cell, Constraint, ExecutionStep, Lookup,
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

#[derive(Clone, Debug)]
struct EqSuccessAllocation<F> {
    case_selector: Cell<F>,
    a: Cell<F>,
    b: Cell<F>,
    diff_inv: Cell<F>,
}

#[derive(Clone, Debug)]
pub struct EqGadget<F> {
    success: EqSuccessAllocation<F>,
    stack_underflow: Cell<F>, // case selector
    out_of_gas: (
        Cell<F>, // case selector
        Cell<F>, // gas available
    ),
}

impl<F: FieldExt> OpGadget<F> for EqGadget<F> {
    const RESPONSIBLE_OPCODES: &'static [OpcodeId] = &[OpcodeId::EQ];

    const CASE_CONFIGS: &'static [CaseConfig] = &[
        CaseConfig {
            case: Case::Success,
            num_word: 0,
            num_cell: 3, // a + b + diff_inv
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
            success: EqSuccessAllocation {
                case_selector: success.selector.clone(),
                a: success.cells.pop().unwrap(),
                b: success.cells.pop().unwrap(),
                diff_inv: success.cells.pop().unwrap(),
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
        let eq =
            Expression::Constant(F::from_u64(OpcodeId::EQ.as_u8().into()));
        let OpExecutionState { opcode, .. } = &state_curr;
        let common_polys = vec![(opcode.expr() - eq.clone())];

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

            let EqSuccessAllocation {
                case_selector,
                a,
                b,
                diff_inv,
            } = &self.success;

            // Check if the difference is zero
            let diff = a.expr() - b.expr();

            let is_zero_expression = one - diff.clone() * diff_inv.expr();
            let is_zero_constraints = vec![
                // when `diff != 0` check `diff_inv = diff.invert()`: diff * (1 - diff * diff_inv)
                diff * is_zero_expression.clone(),
                // when `diff == 0` check `diff_inv = 0`: `diff_inv ⋅ (1 - diff * diff_inv)`
                diff_inv.expr().clone() * is_zero_expression.clone(),
            ];

            #[allow(clippy::suspicious_operation_groupings)]
            let bus_mapping_lookups = vec![
                Lookup::BusMappingLookup(BusMappingLookup::Stack {
                    index_offset: 0,
                    value: a.expr(),
                    is_write: false,
                }),
                Lookup::BusMappingLookup(BusMappingLookup::Stack {
                    index_offset: 1,
                    value: b.expr(),
                    is_write: false,
                }),
                Lookup::BusMappingLookup(BusMappingLookup::Stack {
                    index_offset: 1,
                    value: is_zero_expression,
                    is_write: true,
                }),
            ];

            Constraint {
                name: "EqGadget success",
                selector: case_selector.expr(),
                polys: [
                    common_polys.clone(),
                    state_transition_constraints,
                    is_zero_constraints,
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
                name: "Eq stack underflow",
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
                name: "Eq out of gas",
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

fn compress<F: FieldExt>(
    r: F,
    values: [u8; 32]
) -> F {
    let mut compressed = F::zero();
    for idx in 0..32 {
        compressed = compressed * r + F::from_u64(values[idx].into());
    }
    compressed
}

impl<F: FieldExt> EqGadget<F> {

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

        // TODO: need access to `r` here?
        let r = F::one();

        // Calculate compressed `a` and `b`
        let a = compress(r, execution_step.values[0]);
        let b = compress(r, execution_step.values[1]);

        let diff_inv = (a - b).invert().unwrap_or(F::zero());

        self.success.a.assign(region, offset, Some(a))?;
        self.success.b.assign(region, offset, Some(b))?;
        self.success.diff_inv.assign(region, offset, Some(diff_inv))?;

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
    fn eq_gadget() {
        // Values are equal
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
                    opcode: OpcodeId::EQ,
                    case: Case::Success,
                    values: vec![
                        [
                            1, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, //
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ],
                        [
                            1, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, //
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ],
                        [
                            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
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
                        Base::from_u64(1 + 2 + 3),
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
                        Base::from_u64(1 + 2 + 3),
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
                        Base::from_u64(1),
                        Base::zero(),
                    ]
                },
            ],
            Ok(())
        );
        // Values are not equal
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
                    opcode: OpcodeId::PUSH3,
                    case: Case::Success,
                    values: vec![
                        [
                            1, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
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
                    opcode: OpcodeId::EQ,
                    case: Case::Success,
                    values: vec![
                        [
                            1, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
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
                        Base::from_u64(1 + 2 + 4),
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
                        Base::from_u64(1 + 2 + 4),
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
