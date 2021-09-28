use super::super::{Case, Cell, Constraint, ExecutionStep, Word};
use super::constraint_builder::{ConstraintBuilder, StateTransitions};
use super::{
    CaseAllocation, CaseConfig, CoreStateInstance, OpExecutionState, OpGadget,
};
use crate::util::{Expr, ToWord};
use bus_mapping::evm::{GasCost, OpcodeId};
use halo2::plonk::Error;
use halo2::{arithmetic::FieldExt, circuit::Region, plonk::Expression};
use std::{array, convert::TryInto};

use array_init::array_init;

use super::math_gadgets::IsZeroGadget;

pub const OPCODE: OpcodeId = OpcodeId::BYTE;
pub const GC_DELTA: u64 = 3;
pub const PC_DELTA: u64 = 1;
pub const SP_DELTA: u64 = 1;
pub const GAS: u64 = 3;

#[derive(Clone, Debug)]
struct ByteSuccessAllocation<F> {
    case_selector: Cell<F>,
    word_idx: Word<F>,
    value: Word<F>,
    result: Word<F>,
    is_msb_sum_zero: IsZeroGadget<F>,
    is_byte_selected: [IsZeroGadget<F>; 32],
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
            num_cell: IsZeroGadget::<F>::NUM_CELLS * 33, // sum_inv + 32 diff_inv
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
                is_msb_sum_zero: IsZeroGadget::construct(&mut success),
                is_byte_selected: array_init(|_| IsZeroGadget::construct(&mut success)),
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
                is_msb_sum_zero,
                is_byte_selected,
            } = &self.success;

            let mut cb = ConstraintBuilder::default();

            // If any of the non-LSB bytes are non-zero of the index word we never need to copy any bytes.
            // So just sum all the non-LSB byte values here and then check if it's non-zero
            // so we can use that as an additional condition when to copy the byte value.
            let is_msb_sum_zero_expr = is_msb_sum_zero.constraints(&mut cb,
                 ConstraintBuilder::sum(word_idx.cells[1..32].to_vec())
            );

            // Now we just need to check that `result` is the sum of all copied bytes.
            // We go byte by byte and check if `idx - stack.idx` is zero.
            // If it's zero (at most once) we add the byte value to the sum, else we add 0.
            // The additional condition for this is that none of the non-LSB bytes are non-zero, see above.
            // At the end this sum needs to equal result.
            let mut result_sum_expr = result.cells[0].expr();
            for idx in 0..32 {
                // Check if this byte is selected looking only at the LSB of the index word
                let diff = word_idx.cells[0].expr() - (31 - idx).expr();
                let byte_selected = is_byte_selected[idx as usize].constraints(&mut cb, diff);

                // Add the byte to the sum when this byte is selected
                result_sum_expr = result_sum_expr
                    - (byte_selected
                        * is_msb_sum_zero_expr.clone()
                        * value.cells[idx as usize].expr());
            }
            cb.add_expression(result_sum_expr);

            // All bytes of result, except for the LSB, always need to be 0.
            for idx in 1..32 {
                cb.require_zero(result.cells[idx as usize].expr());
            }

            cb.stack_pop(word_idx.expr());
            cb.stack_pop(value.expr());
            cb.stack_push(result.expr());

            cb.constraint(case_selector.expr(), "ByteGadget success")
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

        // Add common expressions to all cases
        array::IntoIter::new([success, stack_underflow, out_of_gas])
            .map(move |mut constraint| {
                constraint.polys =
                    [common_polys.clone(), constraint.polys].concat();
                constraint
            })
            .collect()
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
            Some(execution_step.values[0].to_word()),
        )?;
        self.success.value.assign(
            region,
            offset,
            Some(execution_step.values[1].to_word()),
        )?;
        self.success.result.assign(
            region,
            offset,
            Some(execution_step.values[2].to_word()),
        )?;

        self.success.is_msb_sum_zero.assign(
            region,
            offset,
            ConstraintBuilder::<F>::from_bytes_witness(
                execution_step.values[0].to_word()[1..32].to_vec(),
            ),
        )?;

        for i in 0..32 {
            let diff = F::from_u64(execution_step.values[0].to_word()[0] as u64) - F::from_u64((31 - i) as u64);
            self.success.is_byte_selected[i].assign(
                region,
                offset,
                diff,
            )?;
        }

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
                        0x030201u64.into(),
                        0x010101u64.into(),
                    ],
                },
                ExecutionStep {
                    opcode: OpcodeId::PUSH1,
                    case: Case::Success,
                    values: vec![
                        29u64.into(),
                        0x01u64.into(),
                    ],
                },
                ExecutionStep {
                    opcode: OpcodeId::BYTE,
                    case: Case::Success,
                    values: vec![
                        29u64.into(),
                        0x030201u64.into(),
                        0x03u64.into(),
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
        // Select byte 256
        try_test_circuit!(
            vec![
                ExecutionStep {
                    opcode: OpcodeId::PUSH3,
                    case: Case::Success,
                    values: vec![
                        0x030201u64.into(),
                        0x010101u64.into(),
                    ],
                },
                ExecutionStep {
                    opcode: OpcodeId::PUSH2,
                    case: Case::Success,
                    values: vec![
                        0x0100u64.into(),
                        0x0101u64.into(),
                    ],
                },
                ExecutionStep {
                    opcode: OpcodeId::BYTE,
                    case: Case::Success,
                    values: vec![
                        0x0100u64.into(),
                        0x030201u64.into(),
                        0u64.into(),
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
                        Base::from_u64(1),
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
                        Base::from_u64(1),
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
