//! Reusable utilities for the op code implementations.

use super::super::Constraint;
use halo2::{arithmetic::FieldExt, plonk::Expression};

pub(crate) mod common_cases;
pub(crate) mod constraint_builder;
pub(crate) mod math_gadgets;

pub(crate) fn batch_add_expressions<F: FieldExt>(
    constraints: Vec<Constraint<F>>,
    expressions: Vec<Expression<F>>,
) -> Vec<Constraint<F>> {
    constraints
        .into_iter()
        .map(|mut constraint| {
            constraint.polys =
                [constraint.polys.clone(), expressions.clone().to_vec()]
                    .concat();
            constraint
        })
        .collect()
}

pub(crate) mod sum {
    use super::super::Cell;
    use crate::util::Expr;
    use halo2::{arithmetic::FieldExt, plonk::Expression};

    pub(crate) fn expr<F: FieldExt>(cells: &[Cell<F>]) -> Expression<F> {
        cells.iter().fold(0.expr(), |acc, cell| acc + cell.expr())
    }

    pub(crate) fn value<F: FieldExt>(values: &[u8]) -> F {
        values
            .iter()
            .fold(F::zero(), |acc, value| acc + F::from_u64(*value as u64))
    }
}

/// Counts the number of repetitions
#[macro_export]
macro_rules! count {
    () => (0usize);
    ( $x:tt $($xs:tt)* ) => (1usize + crate::count!($($xs)*));
}

/// Common OpGadget implementer
#[macro_export]
macro_rules! impl_op_gadget {
    ([$first_op:ident $(,$op:ident)*], $name:ident { $($case:ident ($($args:expr),*) ),* $(,)? }) => {

        paste::paste! {
            #[derive(Clone, Debug)]
            pub struct $name<F> {
                $(
                    [<$case:snake>]: $case<F>,
                )*
            }
        }

        impl<F: FieldExt> OpGadget<F> for $name<F> {
            const RESPONSIBLE_OPCODES: &'static [OpcodeId] = &[OpcodeId::$first_op, $(OpcodeId::$op),*];

            const CASE_CONFIGS: &'static [CaseConfig] = &[
                $(
                    *$case::<F>::CASE_CONFIG,
                )*
            ];

            fn construct(case_allocations: Vec<CaseAllocation<F>>) -> Self {
                paste::paste! {
                    let [
                        $(
                            mut [<$case:snake>],
                        )*
                    ]: [CaseAllocation<F>; crate::count!($($case)*)] =
                        case_allocations.try_into().unwrap();
                    Self {
                        $(
                            [<$case:snake>]: $case::construct(&mut [<$case:snake>]),
                        )*
                    }
                }
            }

            fn constraints(
                &self,
                state_curr: &OpExecutionState<F>,
                state_next: &OpExecutionState<F>,
            ) -> Vec<Constraint<F>> {
                paste::paste! {
                    $(
                        let [<$case:snake>] = self.[<$case:snake>].constraint(
                            state_curr,
                            state_next,
                            $(
                                $args,
                            )*
                            concat!(stringify!($name), " ", stringify!([<$case:snake>])),
                        );
                    )*
                    let cases = vec![
                        $(
                            [<$case:snake>],
                        )*
                    ];
                }
                // Add common expressions to all cases
                utils::batch_add_expressions(
                    cases,
                    vec![
                        (state_curr.opcode.expr() - OpcodeId::$first_op.expr())
                        $(
                            * (state_curr.opcode.expr() - OpcodeId::$op.expr())
                        )*
                    ],
                )
            }

            paste::paste! {
                fn assign(
                    &self,
                    region: &mut Region<'_, F>,
                    offset: usize,
                    op_execution_state: &mut CoreStateInstance,
                    execution_step: &ExecutionStep,
                ) -> Result<(), Error> {
                    $(
                        if execution_step.case == $case::<F>::CASE_CONFIG.case {
                            return self.[<$case:snake>].assign(
                                region,
                                offset,
                                op_execution_state,
                                execution_step,
                            );
                        }
                    )*
                    else {
                        unreachable!();
                    }
                }
            }
        }
    };
}
