use super::super::{BusMappingLookup, Cell, Constraint, FixedLookup, Lookup};
use crate::util::Expr;
use halo2::{arithmetic::FieldExt, plonk::Expression};

#[derive(Clone, Debug)]
pub struct ConstraintBuilder<F> {
    pub expressions: Vec<Expression<F>>,
    pub(super) lookups: Vec<Lookup<F>>,
    pub call_id: Expression<F>,
    pub stack_offset: i32,
}

impl<F: FieldExt> ConstraintBuilder<F> {
    pub(super) fn with_call_id(call_id: Expression<F>) -> Self {
        ConstraintBuilder {
            expressions: vec![],
            lookups: vec![],
            call_id: call_id,
            stack_offset: 0,
        }
    }

    pub(super) fn default() -> Self {
        Self::with_call_id(0.expr())
    }

    // Common

    pub(super) fn require_boolean(&mut self, value: Expression<F>) {
        self.add_expression(value.clone() * (1.expr() - value));
    }

    pub(super) fn require_zero(&mut self, expression: Expression<F>) {
        self.add_expression(expression);
    }

    pub(super) fn require_in_range(
        &mut self,
        value: Expression<F>,
        range: u64,
    ) {
        let table = match range {
            32 => FixedLookup::Range32,
            256 => FixedLookup::Range256,
            _ => unimplemented!(),
        };
        self.add_lookup(Lookup::FixedLookup(
            table,
            [value, 0.expr(), 0.expr()],
        ));
    }

    pub(super) fn require_in_set(
        &mut self,
        value: Expression<F>,
        set: Vec<Expression<F>>,
    ) {
        let mut expression = 1.expr();
        for set_value in set.iter() {
            expression = expression * (value.clone() - set_value.clone());
        }
        self.add_expression(expression);
    }

    // Stack

    pub(super) fn stack_pop(&mut self, value: Expression<F>) {
        self.stack_lookup(value, false);
        self.stack_offset += 1;
    }

    pub(super) fn stack_push(&mut self, value: Expression<F>) {
        self.stack_offset -= 1;
        self.stack_lookup(value, true);
    }

    fn stack_lookup(&mut self, value: Expression<F>, is_write: bool) {
        self.add_lookup(Lookup::BusMappingLookup(BusMappingLookup::Stack {
            index_offset: self.stack_offset,
            value: value,
            is_write: is_write,
        }));
    }

    // Memory

    pub(super) fn memory_write(
        &mut self,
        address: Expression<F>,
        bytes: Vec<Expression<F>>,
    ) {
        self.memory_lookup(address, bytes, true)
    }

    pub(super) fn memory_read(
        &mut self,
        address: Expression<F>,
        bytes: Vec<Expression<F>>,
    ) {
        self.memory_lookup(address, bytes, false);
    }

    fn memory_lookup(
        &mut self,
        address: Expression<F>,
        bytes: Vec<Expression<F>>,
        is_write: bool,
    ) {
        for idx in 0..bytes.len() {
            self.add_lookup(Lookup::BusMappingLookup(
                BusMappingLookup::Memory {
                    call_id: self.call_id.clone(),
                    index: address.clone()
                        + Expression::Constant(F::from_u64(idx as u64)),
                    value: bytes[bytes.len() - 1 - idx].clone(),
                    is_write: is_write,
                },
            ));
        }
    }

    // General

    pub(super) fn add_expression(&mut self, expression: Expression<F>) {
        self.expressions.push(expression);
    }

    pub(super) fn add_expressions(&mut self, expressions: Vec<Expression<F>>) {
        self.expressions.extend(expressions);
    }

    pub(super) fn add_lookup(&mut self, lookup: Lookup<F>) {
        self.lookups.push(lookup);
    }

    // Constraint

    pub(super) fn constraint(
        &self,
        selector: Expression<F>,
        name: &'static str,
    ) -> Constraint<F> {
        Constraint {
            name: name,
            selector: selector,
            polys: self.expressions.clone(),
            lookups: self.lookups.clone(),
        }
    }
}

/// Static utils
impl<F: FieldExt> ConstraintBuilder<F> {
    pub(super) fn batch_add_expressions(
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

    pub(super) fn from_bytes(bytes: Vec<Cell<F>>) -> Expression<F> {
        let mut multiplier = 1.expr();
        let mut value = 0.expr();
        for byte in bytes.iter() {
            value = value + byte.expr() * multiplier.clone();
            multiplier = multiplier * 256.expr();
        }
        value
    }

    pub(super) fn from_bytes_witness(bytes: Vec<u8>) -> F {
        let mut value = F::from_u64(0);
        let mut multiplier = F::from_u64(1);
        for byte in bytes.iter() {
            value = value + (F::from_u64(*byte as u64) * multiplier);
            multiplier = multiplier * F::from_u64(256);
        }
        value
    }

    pub(super) fn sum(cells: Vec<Cell<F>>) -> Expression<F> {
        let mut value = 0.expr();
        for cell in cells.iter() {
            value = value + cell.expr();
        }
        value
    }
}
