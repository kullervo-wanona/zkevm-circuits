use super::super::Cell;
use super::CaseAllocation;
use crate::util::Expr;
use halo2::plonk::Error;
use halo2::{arithmetic::FieldExt, circuit::Region, plonk::Expression};

use super::constraint_builder::ConstraintBuilder;

// a == 0
#[derive(Clone, Debug)]
pub struct IsZeroGadget<F> {
    pub(super) inverse: Cell<F>,
}

impl<F: FieldExt> IsZeroGadget<F> {
    pub const NUM_CELLS: usize = 1;
    pub const NUM_WORDS: usize = 0;

    pub(super) fn construct(alloc: &mut CaseAllocation<F>) -> Self {
        Self {
            inverse: alloc.cells.pop().unwrap(),
        }
    }

    pub(super) fn constraints(
        &self,
        cb: &mut ConstraintBuilder<F>,
        value: Expression<F>,
    ) -> Expression<F> {
        let is_zero = 1.expr() - (value.clone() * self.inverse.expr());
        // when `a != 0` check `a_inv = a.invert()`: a * (1 - a * a_inv)
        cb.add_expression(value * is_zero.clone());
        // when `a == 0` check `a_inv = 0`: `a_inv ⋅ (1 - a * a_inv)`
        cb.add_expression(self.inverse.expr() * is_zero.clone());

        is_zero
    }

    pub(super) fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        value: F,
    ) -> Result<bool, Error> {
        let inverse = value.invert().unwrap_or(F::zero());
        self.inverse.assign(region, offset, Some(inverse))?;
        Ok(value.is_zero())
    }
}
