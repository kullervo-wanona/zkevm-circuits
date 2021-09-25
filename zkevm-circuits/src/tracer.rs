//! EVM tracer

use num::BigUint;
use pasta_curves::arithmetic::FieldExt;

use crate::evm_circuit::{Case, ExecutionStep, Operation};
use crate::util::ToWord;

use geth_utils::create_trace;

use bus_mapping::evm::{EvmWord, OpcodeId};
use bus_mapping::{operation::Target, BlockConstants, ExecutionTrace};

/// trace the specified byte code
pub fn trace<F: FieldExt>(code: &Vec<u8>) -> ExecutionTrace<F> {
    //println!("code: {:?}", code.clone());
    let trace = create_trace(code.clone());
    //println!("trace: {}", trace.clone().unwrap());

    let block_ctants = BlockConstants::new(
        EvmWord::from(0u8),
        F::zero(),
        F::zero(),
        F::zero(),
        F::zero(),
        F::zero(),
        F::zero(),
        F::zero(),
    );

    let exec_trace = ExecutionTrace::<F>::from_trace_bytes(
        trace.unwrap().as_bytes(),
        block_ctants,
    )
    .expect("Error generating trace");

    exec_trace
}

/// All code below to be removed once bus_mapping and evm_circuit use the same ExecutionSteps and Operations.

/// A bunch of hacks to translate bus_mapping::ExecutionSteps -> evm_circuit::ExecutionSteps
pub(crate) fn patch_steps_hack<F: FieldExt>(
    trace: &bus_mapping::ExecutionTrace<F>,
) -> Vec<ExecutionStep> {
    let mut evm_steps = vec![];
    for (idx, step) in trace.steps().iter().enumerate() {
        if *step.instruction() == OpcodeId::PUSH1 {
            let stack_value = trace.steps()[idx + 1].stack().0.last().unwrap();
            evm_steps.push(ExecutionStep {
                opcode: *step.instruction(),
                case: Case::Success,
                values: vec![
                    BigUint::from_bytes_le(&stack_value.to_bytes()),
                    BigUint::from(1u64),
                ],
            });
        } else {
            evm_steps.push(ExecutionStep {
                opcode: *step.instruction(),
                case: Case::Success,
                values: vec![],
            });
        }
    }
    evm_steps
}

fn compress<F: FieldExt>(bytes: [u8; 32]) -> F {
    bytes
        .iter()
        .fold(F::zero(), |acc, val| acc + F::from_u64(*val as u64))
}

/// A bunch of hacks to translate bus_mapping::Operation -> evm_circuit::Operation
pub(crate) fn patch_ops_hack<F: FieldExt>(
    trace: &bus_mapping::ExecutionTrace<F>,
) -> Vec<Operation<F>> {
    let mut evm_ops = vec![];
    for op in trace.ops().all_ops() {
        match op {
            bus_mapping::operation::Operation::Stack(stack_op) => {
                evm_ops.push(Operation {
                    gc: stack_op.gc().into(),
                    target: Target::Stack,
                    is_write: if stack_op.rw()
                        == bus_mapping::operation::RW::READ
                    {
                        false
                    } else {
                        true
                    },
                    values: [
                        F::zero(),
                        F::from_u64(stack_op.address().0 as u64),
                        compress(stack_op.value().as_big_uint().to_word()),
                        F::zero(),
                    ],
                });
            }
            _ => {}
        }
    }
    evm_ops
}
