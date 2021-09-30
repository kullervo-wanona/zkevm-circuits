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
