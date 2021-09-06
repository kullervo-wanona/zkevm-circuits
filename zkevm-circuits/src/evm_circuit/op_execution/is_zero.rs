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

pub const GC_DELTA: u64 = 2;
pub const PC_DELTA: u64 = 1;
pub const SP_DELTA: u64 = 0;
pub const GAS: u64 = 3;

#[derive(Clone, Debug)]
struct IsZeroSuccessAllocation<F> {
    case_selector: Cell<F>,
    a: Cell<F>,
    result: Cell<F>,
    a_inv: Cell<F>,
}

#[derive(Clone, Debug)]
pub struct IsZeroGadget<F> {
    success: IsZeroSuccessAllocation<F>,
    stack_underflow: Cell<F>, // case selector
    out_of_gas: (
        Cell<F>, // case selector
        Cell<F>, // gas available
    ),
}

impl<F: FieldExt> OpGadget<F> for IsZeroGadget<F> {
    const RESPONSIBLE_OPCODES: &'static [OpcodeId] = &[OpcodeId::ISZERO];

    const CASE_CONFIGS: &'static [CaseConfig] = &[
        CaseConfig {
            case: Case::Success,
            num_word: 0,
            num_cell: 3, // a + result + a_inv
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
            success: IsZeroSuccessAllocation {
                case_selector: success.selector.clone(),
                a: success.cells.pop().unwrap(),
                result: success.cells.pop().unwrap(),
                a_inv: success.cells.pop().unwrap(),
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
        let is_zero =
            Expression::Constant(F::from_u64(OpcodeId::ISZERO.as_u8().into()));
        let OpExecutionState { opcode, .. } = &state_curr;
        let common_polys = vec![(opcode.expr() - is_zero.clone())];

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

            let IsZeroSuccessAllocation {
                case_selector,
                a,
                result,
                a_inv,
            } = &self.success;

            let is_zero_expression = one - a.expr() * a_inv.expr();
            let is_zero_constraints = vec![
                // when `a != 0` check `a_inv = a.invert()`: a * (1 - a * a_inv)
                a.expr().clone() * is_zero_expression.clone(),
                // when `a == 0` check `a_inv = 0`: `a_inv ⋅ (1 - a * a_inv)`
                a_inv.expr().clone() * is_zero_expression.clone(),
            ];

            #[allow(clippy::suspicious_operation_groupings)]
            let bus_mapping_lookups = vec![
                Lookup::BusMappingLookup(BusMappingLookup::Stack {
                    index_offset: 0,
                    value: a.expr(),
                    is_write: false,
                }),
                Lookup::BusMappingLookup(BusMappingLookup::Stack {
                    index_offset: 0,
                    value: result.expr(),
                    is_write: true,
                }),
            ];

            Constraint {
                name: "IsZeroGadget success",
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
                name: "IsZero stack underflow",
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
                name: "IsZero out of gas",
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

impl<F: FieldExt> IsZeroGadget<F> {
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

        let mut a = F::zero();
        for idx in 0..32 {
            a = a * r + F::from_u64(execution_step.values[0][idx].into());
        }
        let a_inv = a.invert().unwrap_or(F::zero());

        self.success.a.assign(region, offset, Some(a))?;
        self.success.result.assign(
            region,
            offset,
            Some(F::from_u64(execution_step.values[1][0] as u64)),
        )?;
        self.success.a_inv.assign(region, offset, Some(a_inv))?;

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
    fn iszero_gadget() {
        // Value is zero
        try_test_circuit!(
            vec![
                ExecutionStep {
                    opcode: OpcodeId::PUSH2,
                    case: Case::Success,
                    values: vec![
                        [
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
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
                    opcode: OpcodeId::ISZERO,
                    case: Case::Success,
                    values: vec![
                        [
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
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
                        Base::from_u64(0 + 0),
                        Base::zero(),
                    ]
                },
                Operation {
                    gc: 2,
                    target: Target::Stack,
                    is_write: false,
                    values: [
                        Base::zero(),
                        Base::from_u64(1023),
                        Base::from_u64(0 + 0),
                        Base::zero(),
                    ]
                },
                Operation {
                    gc: 3,
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
        // Value is not zero
        try_test_circuit!(
            vec![
                ExecutionStep {
                    opcode: OpcodeId::PUSH2,
                    case: Case::Success,
                    values: vec![
                        [
                            0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
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
                    opcode: OpcodeId::ISZERO,
                    case: Case::Success,
                    values: vec![
                        [
                            0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
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
                        Base::from_u64(0 + 1),
                        Base::zero(),
                    ]
                },
                Operation {
                    gc: 2,
                    target: Target::Stack,
                    is_write: false,
                    values: [
                        Base::zero(),
                        Base::from_u64(1023),
                        Base::from_u64(0 + 1),
                        Base::zero(),
                    ]
                },
                Operation {
                    gc: 3,
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
