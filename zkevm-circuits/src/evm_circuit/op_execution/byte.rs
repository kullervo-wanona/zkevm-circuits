use super::super::{Case, Cell, Constraint, ExecutionStep, Word};
use super::constraint_builder::ConstraintBuilder;
use super::{
    CaseAllocation, CaseConfig, CoreStateInstance, OpExecutionState, OpGadget,
};
use crate::util::{Expr, ToWord};
use array_init::array_init;
use bus_mapping::evm::{GasCost, OpcodeId};
use halo2::plonk::Error;
use halo2::{arithmetic::FieldExt, circuit::Region};
use std::convert::TryInto;

use super::common_cases::{OutOfGasCase, StackUnderflowCase, StateTransitions};
use super::math_gadgets::{IsEqualGadget, IsZeroGadget};

const OPCODE: OpcodeId = OpcodeId::BYTE;
const GC_DELTA: usize = 3;
const PC_DELTA: usize = 1;
const SP_DELTA: usize = 1;
const GAS: GasCost = GasCost::FASTEST;

#[derive(Clone, Debug)]
struct ByteSuccessAllocation<F> {
    case_selector: Cell<F>,
    word_idx: Word<F>,
    value: Word<F>,
    result: Word<F>,
    is_msb_sum_zero: IsZeroGadget<F>,
    is_byte_selected: [IsEqualGadget<F>; 32],
}

#[derive(Clone, Debug)]
pub struct ByteGadget<F> {
    success: ByteSuccessAllocation<F>,
    stack_underflow: StackUnderflowCase<F>,
    out_of_gas: OutOfGasCase<F>,
}

impl<F: FieldExt> OpGadget<F> for ByteGadget<F> {
    const RESPONSIBLE_OPCODES: &'static [OpcodeId] = &[OPCODE];

    const CASE_CONFIGS: &'static [CaseConfig] = &[
        CaseConfig {
            case: Case::Success,
            num_word: 3, // value + word_idx + result
            num_cell: IsZeroGadget::<F>::NUM_CELLS * 33, // 1x is_msb_sum_zero + 32x is_byte_selected
            will_halt: false,
        },
        StackUnderflowCase::<F>::CASE_CONFIG,
        OutOfGasCase::<F>::CASE_CONFIG,
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
                is_byte_selected: array_init(|_| {
                    IsEqualGadget::construct(&mut success)
                }),
            },
            stack_underflow: StackUnderflowCase::construct(&stack_underflow),
            out_of_gas: OutOfGasCase::construct(&out_of_gas),
        }
    }

    fn constraints(
        &self,
        state_curr: &OpExecutionState<F>,
        state_next: &OpExecutionState<F>,
    ) -> Vec<Constraint<F>> {
        let OpExecutionState { opcode, .. } = &state_curr;

        // Success
        let success = {
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
            let is_msb_sum_zero_expr = is_msb_sum_zero.constraints(
                &mut cb,
                ConstraintBuilder::sum(word_idx.cells[1..32].to_vec()),
            );

            // Now we just need to check that `result[0]` is the sum of all copied bytes.
            // We go byte by byte and check if `idx == word_idx`.
            // If they are equal (at most once) we add the byte value to the sum, else we add 0.
            // The additional condition for this is that none of the non-LSB bytes are non-zero, see above.
            // At the end this sum needs to equal result.
            let mut result_sum_expr = result.cells[0].expr();
            for idx in 0..32 {
                // Check if this byte is selected looking only at the LSB of the index word
                let byte_selected = is_byte_selected[idx as usize].constraints(
                    &mut cb,
                    word_idx.cells[0].expr(),
                    (31 - idx).expr(),
                );

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

            // Pop the byte index and the value from the stack, push the result on the stack
            cb.stack_pop(word_idx.expr());
            cb.stack_pop(value.expr());
            cb.stack_push(result.expr());

            // State transitions
            let mut state_transitions = StateTransitions::default();
            state_transitions.gc_delta = Some(GC_DELTA.expr());
            state_transitions.sp_delta = Some(SP_DELTA.expr());
            state_transitions.pc_delta = Some(PC_DELTA.expr());
            state_transitions.gas_delta = Some(GAS.expr());
            state_transitions.constraints(&mut cb, state_curr, state_next);

            cb.constraint(case_selector.expr(), "ByteGadget success")
        };

        // Stack Underflow
        let stack_underflow = self.stack_underflow.constraint(
            state_curr.stack_pointer.expr(),
            2,
            "BYTE stack underflow",
        );

        // Out of gas
        let out_of_gas = self.out_of_gas.constraint(
            state_curr.gas_counter.expr(),
            GAS.as_usize(),
            "BYTE out of gas",
        );

        // Add common expressions to all cases
        ConstraintBuilder::batch_add_expressions(
            vec![success, stack_underflow, out_of_gas],
            vec![opcode.expr() - OPCODE.expr()],
        )
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
        op_execution_state.global_counter += GC_DELTA;
        op_execution_state.program_counter += PC_DELTA;
        op_execution_state.stack_pointer += SP_DELTA;
        op_execution_state.gas_counter += GAS.as_usize();

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
            self.success.is_byte_selected[i].assign(
                region,
                offset,
                F::from_u64(execution_step.values[0].to_word()[0] as u64),
                F::from_u64((31 - i) as u64),
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
                    values: vec![0x030201u64.into(), 0x010101u64.into(),],
                },
                ExecutionStep {
                    opcode: OpcodeId::PUSH1,
                    case: Case::Success,
                    values: vec![29u64.into(), 0x01u64.into(),],
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
                    values: vec![0x030201u64.into(), 0x010101u64.into(),],
                },
                ExecutionStep {
                    opcode: OpcodeId::PUSH2,
                    case: Case::Success,
                    values: vec![0x0100u64.into(), 0x0101u64.into(),],
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
