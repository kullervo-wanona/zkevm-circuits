use super::super::{BusMappingLookup, Cell, Constraint, FixedLookup, Lookup};
use super::OpExecutionState;
use crate::util::Expr;
use halo2::{arithmetic::FieldExt, plonk::Expression};

pub const STACK_START_IDX: usize = 1024;

// Allows updating the state transition without having to update all
// op codes that don't modify any of the new state variables.
#[derive(Clone, Debug, Default)]
pub struct StateTransitions<F> {
    pub gc_delta: Option<Expression<F>>,
    pub sp_delta: Option<Expression<F>>,
    pub pc_delta: Option<Expression<F>>,
    pub gas_delta: Option<Expression<F>>,
    pub next_memory_size: Option<Expression<F>>,
}

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
        Self::with_call_id(Expression::Constant(F::from_u64(0)))
    }

    // Common

    pub(super) fn boolean_constrain(&mut self, value: Expression<F>) {
        self.add_expression(value.clone() * (1.expr() - value));
    }

    pub(super) fn boolean_constrain_cell(&mut self, cell: &Cell<F>) {
        self.boolean_constrain(cell.expr());
    }

    pub(super) fn require_zero(&mut self, expression: Expression<F>) {
        self.add_expression(expression);
    }

    pub(super) fn range_check(&mut self, value: Expression<F>, range: u64) {
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

    // Sets

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

    // State transitions

    pub(super) fn do_state_transitions(
        &mut self,
        state_curr: &OpExecutionState<F>,
        state_next: &OpExecutionState<F>,
        state_transitions: StateTransitions<F>,
    ) {
        // GC
        self.add_expression(
            state_next.global_counter.expr()
                - (state_curr.global_counter.expr()
                    + state_transitions.gc_delta.unwrap_or(0.expr())),
        );
        // SP
        self.add_expression(
            state_next.stack_pointer.expr()
                - (state_curr.stack_pointer.expr()
                    + state_transitions.sp_delta.unwrap_or(0.expr())),
        );
        // PC
        self.add_expression(
            state_next.program_counter.expr()
                - (state_curr.program_counter.expr()
                    + state_transitions.pc_delta.unwrap_or(0.expr())),
        );
        // gas counter
        self.add_expression(
            state_next.gas_counter.expr()
                - (state_curr.gas_counter.expr()
                    + state_transitions.gas_delta.unwrap_or(0.expr())),
        );
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

    // Constraints

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

    pub(super) fn stack_underflow_constraint(
        selector: Expression<F>,
        stack_pointer: Expression<F>,
        num_popped: usize,
        name: &'static str,
    ) -> Constraint<F> {
        let mut cb = ConstraintBuilder::default();
        let mut set = vec![];
        for idx in 0..num_popped {
            set.push(Expression::Constant(F::from_u64(
                (STACK_START_IDX - idx) as u64,
            )));
        }
        cb.require_in_set(stack_pointer, set);
        cb.constraint(selector, name)
    }
}

/// Utils
impl<F: FieldExt> ConstraintBuilder<F> {
    pub(super) fn select(
        condition: Expression<F>,
        when_true: Expression<F>,
        when_false: Expression<F>,
    ) -> Expression<F> {
        condition.clone() * when_true + (1.expr() - condition) * when_false
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

    pub(super) fn get_range(num_bits: usize) -> F {
        F::from_u64(2).pow(&[num_bits as u64, 0, 0, 0])
    }
}
