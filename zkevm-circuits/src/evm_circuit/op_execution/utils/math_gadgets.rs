use super::super::utils;
use super::super::CaseAllocation;
use super::super::Cell;
use crate::util::Expr;
use array_init::array_init;
use halo2::plonk::Error;
use halo2::{arithmetic::FieldExt, circuit::Region, plonk::Expression};

use super::constraint_builder::ConstraintBuilder;

/// Returns `1` when `value == 0`, and returns `0` otherwise.
#[derive(Clone, Debug)]
pub struct IsZeroGadget<F> {
    pub(crate) inverse: Cell<F>,
}

impl<F: FieldExt> IsZeroGadget<F> {
    pub const NUM_CELLS: usize = 1;
    pub const NUM_WORDS: usize = 0;

    pub(crate) fn construct(alloc: &mut CaseAllocation<F>) -> Self {
        Self {
            inverse: alloc.cells.pop().unwrap(),
        }
    }

    pub(crate) fn constraints(
        &self,
        cb: &mut ConstraintBuilder<F>,
        value: Expression<F>,
    ) -> Expression<F> {
        let is_zero = 1.expr() - (value.clone() * self.inverse.expr());
        // when `value != 0` check `inverse = a.invert()`: value * (1 - value * inverse)
        cb.add_expression(value * is_zero.clone());
        // when `value == 0` check `inverse = 0`: `inverse ⋅ (1 - value * inverse)`
        cb.add_expression(self.inverse.expr() * is_zero.clone());

        is_zero
    }

    pub(crate) fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        value: F,
    ) -> Result<F, Error> {
        let inverse = value.invert().unwrap_or(F::zero());
        self.inverse.assign(region, offset, Some(inverse))?;
        Ok(if value.is_zero() { F::one() } else { F::zero() })
    }
}

/// Returns `1` when `lhs == rhs`, and returns `0` otherwise.
#[derive(Clone, Debug)]
pub struct IsEqualGadget<F> {
    pub(crate) is_zero: IsZeroGadget<F>,
}

impl<F: FieldExt> IsEqualGadget<F> {
    pub const NUM_CELLS: usize = IsZeroGadget::<F>::NUM_CELLS;
    pub const NUM_WORDS: usize = IsZeroGadget::<F>::NUM_WORDS;

    pub(crate) fn construct(alloc: &mut CaseAllocation<F>) -> Self {
        Self {
            is_zero: IsZeroGadget::<F>::construct(alloc),
        }
    }

    pub(crate) fn constraints(
        &self,
        cb: &mut ConstraintBuilder<F>,
        lhs: Expression<F>,
        rhs: Expression<F>,
    ) -> Expression<F> {
        self.is_zero.constraints(cb, (lhs) - (rhs))
    }

    pub(crate) fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        lhs: F,
        rhs: F,
    ) -> Result<F, Error> {
        self.is_zero.assign(region, offset, lhs - rhs)
    }
}

/// Requires that the passed in value is within the specified range.
/// `NUM_BYTES` is required to be `<= 31`.
#[derive(Clone, Debug)]
pub struct RangeCheckGadget<F, const NUM_BYTES: usize> {
    parts: [Cell<F>; NUM_BYTES],
}

impl<F: FieldExt, const NUM_BYTES: usize> RangeCheckGadget<F, NUM_BYTES> {
    pub const NUM_CELLS: usize = NUM_BYTES;
    pub const NUM_WORDS: usize = 0;

    pub const PART_SIZE: u64 = 256;

    pub(crate) fn construct(alloc: &mut CaseAllocation<F>) -> Self {
        assert!(NUM_BYTES <= 31, "number of bytes too large");
        Self {
            parts: array_init(|_| alloc.cells.pop().unwrap()),
        }
    }

    pub(crate) fn constraints(
        &self,
        cb: &mut ConstraintBuilder<F>,
        value: Expression<F>,
    ) {
        // Range check the parts using lookups
        for part in self.parts.iter() {
            cb.require_in_range(part.expr(), Self::PART_SIZE);
        }
        // Require that the reconstructed value from the parts equals the original value
        cb.require_equal(value, utils::from_bytes::expr(self.parts.to_vec()));
    }

    pub(crate) fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        value: F,
    ) -> Result<(), Error> {
        let bytes = value.to_bytes();
        for (idx, part) in self.parts.iter().enumerate() {
            part.assign(region, offset, Some(F::from_u64(bytes[idx] as u64)))?;
        }
        Ok(())
    }
}

/// Returns (quotient: numerator/divisor, remainder: numerator%divisor),
/// with `numerator` an expression and `divisor` a constant.
/// Input requirements:
/// - `quotient < 256**NUM_BYTES`
/// - `quotient * divisor < field size`
/// - `remainder < divisor` currently requires a lookup table for `divisor`
#[derive(Clone, Debug)]
pub struct ConstantDivisionGadget<F, const NUM_BYTES: usize> {
    quotient: Cell<F>,
    remainder: Cell<F>,
    divisor: u64,
    quotient_range_check: RangeCheckGadget<F, NUM_BYTES>,
}

impl<F: FieldExt, const NUM_BYTES: usize> ConstantDivisionGadget<F, NUM_BYTES> {
    pub const NUM_CELLS: usize =
        2 + RangeCheckGadget::<F, NUM_BYTES>::NUM_CELLS;
    pub const NUM_WORDS: usize = RangeCheckGadget::<F, NUM_BYTES>::NUM_WORDS;

    pub(crate) fn construct(
        alloc: &mut CaseAllocation<F>,
        divisor: u64,
    ) -> Self {
        Self {
            quotient: alloc.cells.pop().unwrap(),
            remainder: alloc.cells.pop().unwrap(),
            divisor,
            quotient_range_check: RangeCheckGadget::construct(alloc),
        }
    }

    pub(crate) fn constraints(
        &self,
        cb: &mut ConstraintBuilder<F>,
        numerator: Expression<F>,
    ) -> (Expression<F>, Expression<F>) {
        // Require that remainder < divisor
        cb.require_in_range(self.remainder.expr(), self.divisor);

        // Require that quotient < 2**NUM_BYTES
        // so we can't have any overflow when doing `quotient * divisor`.
        self.quotient_range_check
            .constraints(cb, self.quotient.expr());

        // Check if the division was done correctly
        cb.require_equal(
            numerator - self.remainder.expr(),
            self.quotient.expr() * self.divisor.expr(),
        );

        // Return the quotient and the remainder
        (self.quotient.expr(), self.remainder.expr())
    }

    pub(crate) fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        numerator: u128,
    ) -> Result<(u128, u128), Error> {
        let divisor = self.divisor as u128;
        let quotient = numerator / divisor;
        let remainder = numerator % divisor;
        self.quotient
            .assign(region, offset, Some(F::from_u128(quotient)))?;
        self.remainder
            .assign(region, offset, Some(F::from_u128(remainder)))?;

        self.quotient_range_check.assign(
            region,
            offset,
            F::from_u128(quotient),
        )?;

        Ok((quotient, remainder))
    }
}

/// Returns `1` when `lhs < rhs`, and returns `0` otherwise.
/// lhs and rhs `< 256**NUM_BYTES`
/// `NUM_BYTES` is required to be `<= 31`.
#[derive(Clone, Debug)]
pub struct ComparisonGadget<F, const NUM_BYTES: usize> {
    lt: Cell<F>,
    diff: [Cell<F>; NUM_BYTES],
    range: F,
}

impl<F: FieldExt, const NUM_BYTES: usize> ComparisonGadget<F, NUM_BYTES> {
    pub const NUM_CELLS: usize = 1 + NUM_BYTES; // lt + diff
    pub const NUM_WORDS: usize = 0;

    pub(crate) fn construct(alloc: &mut CaseAllocation<F>) -> Self {
        assert!(NUM_BYTES <= 31, "unsupported number of bytes");
        Self {
            lt: alloc.cells.pop().unwrap(),
            diff: array_init(|_| alloc.cells.pop().unwrap()),
            range: utils::get_range(NUM_BYTES * 8),
        }
    }

    pub(crate) fn constraints(
        &self,
        cb: &mut ConstraintBuilder<F>,
        lhs: Expression<F>,
        rhs: Expression<F>,
    ) -> Expression<F> {
        let diff = utils::from_bytes::expr(self.diff.to_vec());
        // The comparison equation that needs to hold.
        cb.require_equal(lhs, rhs + diff - (self.lt.expr() * self.range));

        // `lt` needs to be boolean
        cb.require_boolean(self.lt.expr());
        // All parts of `diff` need to be bytes
        for byte in self.diff.iter() {
            cb.require_in_range(byte.expr(), 256);
        }

        self.lt.expr()
    }

    pub(crate) fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        lhs: F,
        rhs: F,
    ) -> Result<F, Error> {
        // Set `lt`
        let lt = lhs < rhs;
        self.lt.assign(
            region,
            offset,
            Some(F::from_u64(if lt { 1 } else { 0 })),
        )?;

        // Set the bytes of diff
        let diff = (lhs - rhs) + (if lt { self.range } else { F::zero() });
        let diff_bytes = diff.to_bytes();
        for (idx, diff) in self.diff.iter().enumerate() {
            diff.assign(
                region,
                offset,
                Some(F::from_u64(diff_bytes[idx] as u64)),
            )?;
        }

        Ok(if lt { F::one() } else { F::zero() })
    }
}

/// Returns `rhs` when `lhs < rhs`, and returns `lhs` otherwise.
/// lhs and rhs `< 256**NUM_BYTES`
/// `NUM_BYTES` is required to be `<= 31`.
#[derive(Clone, Debug)]
pub struct MaxGadget<F, const NUM_BYTES: usize> {
    comparison: ComparisonGadget<F, NUM_BYTES>,
}

impl<F: FieldExt, const NUM_BYTES: usize> MaxGadget<F, NUM_BYTES> {
    pub const NUM_CELLS: usize = ComparisonGadget::<F, NUM_BYTES>::NUM_CELLS;
    pub const NUM_WORDS: usize = ComparisonGadget::<F, NUM_BYTES>::NUM_WORDS;

    pub(crate) fn construct(alloc: &mut CaseAllocation<F>) -> Self {
        Self {
            comparison: ComparisonGadget::construct(alloc),
        }
    }

    pub(crate) fn constraints(
        &self,
        cb: &mut ConstraintBuilder<F>,
        lhs: Expression<F>,
        rhs: Expression<F>,
    ) -> Expression<F> {
        let lt = self.comparison.constraints(cb, lhs.clone(), rhs.clone());
        utils::select::expr(lt, rhs, lhs)
    }

    pub(crate) fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        lhs: F,
        rhs: F,
    ) -> Result<F, Error> {
        let lt = self.comparison.assign(region, offset, lhs, rhs)?;
        Ok(utils::select::value(lt, rhs, lhs))
    }
}
