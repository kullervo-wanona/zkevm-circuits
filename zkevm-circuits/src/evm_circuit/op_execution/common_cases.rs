use super::super::{Case, Cell, Constraint};
use super::constraint_builder::ConstraintBuilder;
use super::{CaseAllocation, CaseConfig, OpExecutionState};
use crate::util::Expr;
use halo2::{arithmetic::FieldExt, plonk::Expression};

pub const STACK_START_IDX: usize = 1024;

#[derive(Clone, Debug)]
pub(super) struct OutOfGasCase<F> {
    case_selector: Cell<F>,
    gas_available: Cell<F>,
}

impl<F: FieldExt> OutOfGasCase<F> {
    pub(super) const CASE_CONFIG: CaseConfig = CaseConfig {
        case: Case::OutOfGas,
        num_word: 0,
        num_cell: 0,
        will_halt: true,
    };

    pub(super) fn construct(alloc: &CaseAllocation<F>) -> Self {
        Self {
            case_selector: alloc.selector.clone(),
            gas_available: alloc
                .resumption
                .as_ref()
                .unwrap()
                .gas_available
                .clone(),
        }
    }

    pub(super) fn constraint(
        &self,
        gas_counter: Expression<F>,
        gas_used: usize,
        name: &'static str,
    ) -> Constraint<F> {
        let mut set = vec![];
        for idx in 1..=gas_used {
            set.push(idx.expr());
        }
        let gas_overdemand =
            gas_counter + gas_used.expr() - self.gas_available.expr();
        let mut cb = ConstraintBuilder::default();
        cb.require_in_set(gas_overdemand, set);
        cb.constraint(self.case_selector.expr(), name)
    }
}

#[derive(Clone, Debug)]
pub(super) struct StackUnderflowCase<F> {
    case_selector: Cell<F>,
}

impl<F: FieldExt> StackUnderflowCase<F> {
    pub(super) const CASE_CONFIG: CaseConfig = CaseConfig {
        case: Case::StackUnderflow,
        num_word: 0,
        num_cell: 0,
        will_halt: true,
    };

    pub(super) fn construct(alloc: &CaseAllocation<F>) -> Self {
        Self {
            case_selector: alloc.selector.clone(),
        }
    }

    pub(super) fn constraint(
        &self,
        stack_pointer: Expression<F>,
        num_popped: usize,
        name: &'static str,
    ) -> Constraint<F> {
        let mut set = vec![];
        for idx in 0..num_popped {
            set.push((STACK_START_IDX - idx).expr());
        }
        let mut cb = ConstraintBuilder::default();
        cb.require_in_set(stack_pointer, set);
        cb.constraint(self.case_selector.expr(), name)
    }
}

// Makes sure all state transition variables are always constrained
#[derive(Clone, Debug, Default)]
pub struct StateTransitions<F> {
    pub gc_delta: Option<Expression<F>>,
    pub sp_delta: Option<Expression<F>>,
    pub pc_delta: Option<Expression<F>>,
    pub gas_delta: Option<Expression<F>>,
    pub next_memory_size: Option<Expression<F>>,
}

impl<F: FieldExt> StateTransitions<F> {
    pub(super) fn constraints(
        &self,
        cb: &mut ConstraintBuilder<F>,
        state_curr: &OpExecutionState<F>,
        state_next: &OpExecutionState<F>,
    ) {
        // Global Counter
        cb.add_expression(
            state_next.global_counter.expr()
                - (state_curr.global_counter.expr()
                    + self.gc_delta.clone().unwrap_or(0.expr())),
        );
        // Stack Pointer
        cb.add_expression(
            state_next.stack_pointer.expr()
                - (state_curr.stack_pointer.expr()
                    + self.sp_delta.clone().unwrap_or(0.expr())),
        );
        // Program Counter
        cb.add_expression(
            state_next.program_counter.expr()
                - (state_curr.program_counter.expr()
                    + self.pc_delta.clone().unwrap_or(0.expr())),
        );
        // Gas Counter
        cb.add_expression(
            state_next.gas_counter.expr()
                - (state_curr.gas_counter.expr()
                    + self.gas_delta.clone().unwrap_or(0.expr())),
        );
    }
}
