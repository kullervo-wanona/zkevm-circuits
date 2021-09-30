use super::super::{
    Case, CaseAllocation, CaseConfig, Cell, Constraint, CoreStateInstance,
    ExecutionStep, OpExecutionState,
};
use super::constraint_builder::ConstraintBuilder;
use crate::util::Expr;
use halo2::plonk::Error;
use halo2::{arithmetic::FieldExt, circuit::Region, plonk::Expression};

pub const STACK_START_IDX: usize = 1024;

#[derive(Clone, Debug)]
pub(crate) struct OutOfGasCase<F> {
    case_selector: Cell<F>,
    gas_available: Cell<F>,
}

impl<F: FieldExt> OutOfGasCase<F> {
    pub(crate) const CASE_CONFIG: &'static CaseConfig = &CaseConfig {
        case: Case::OutOfGas,
        num_word: 0,
        num_cell: 0,
        will_halt: true,
    };

    pub(crate) fn construct(alloc: &CaseAllocation<F>) -> Self {
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

    pub(crate) fn constraint(
        &self,
        state_curr: &OpExecutionState<F>,
        _state_next: &OpExecutionState<F>,
        gas_used: usize,
        name: &'static str,
    ) -> Constraint<F> {
        let mut set = vec![];
        for idx in 1..=gas_used {
            set.push(idx.expr());
        }
        let gas_overdemand = state_curr.gas_counter.expr() + gas_used.expr()
            - self.gas_available.expr();
        let mut cb = ConstraintBuilder::default();
        cb.require_in_set(gas_overdemand, set);
        cb.constraint(self.case_selector.expr(), name)
    }

    pub(crate) fn assign(
        &self,
        _region: &mut Region<'_, F>,
        _offset: usize,
        _op_execution_state: &mut CoreStateInstance,
        _execution_step: &ExecutionStep,
    ) -> Result<(), Error> {
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub(crate) struct StackUnderflowCase<F> {
    case_selector: Cell<F>,
}

impl<F: FieldExt> StackUnderflowCase<F> {
    pub(crate) const CASE_CONFIG: &'static CaseConfig = &CaseConfig {
        case: Case::StackUnderflow,
        num_word: 0,
        num_cell: 0,
        will_halt: true,
    };

    pub(crate) fn construct(alloc: &CaseAllocation<F>) -> Self {
        Self {
            case_selector: alloc.selector.clone(),
        }
    }

    pub(crate) fn constraint(
        &self,
        state_curr: &OpExecutionState<F>,
        _state_next: &OpExecutionState<F>,
        num_popped: usize,
        name: &'static str,
    ) -> Constraint<F> {
        let mut set = vec![];
        for idx in 0..num_popped {
            set.push((STACK_START_IDX - idx).expr());
        }
        let mut cb = ConstraintBuilder::default();
        cb.require_in_set(state_curr.stack_pointer.expr(), set);
        cb.constraint(self.case_selector.expr(), name)
    }

    pub(crate) fn assign(
        &self,
        _region: &mut Region<'_, F>,
        _offset: usize,
        _op_execution_state: &mut CoreStateInstance,
        _execution_step: &ExecutionStep,
    ) -> Result<(), Error> {
        Ok(())
    }
}

// Makes sure all state transition variables are always constrained.
// This makes it impossible in opcodes to forget to constrain
// any state variables. If no update is specified it is assumed
// that the state variable needs to remain the same (which may not
// be correct, but this will easily be detected while testing).
#[derive(Clone, Debug, Default)]
pub(crate) struct StateTransitions<F> {
    pub gc_delta: Option<Expression<F>>,
    pub sp_delta: Option<Expression<F>>,
    pub pc_delta: Option<Expression<F>>,
    pub gas_delta: Option<Expression<F>>,
    pub next_memory_size: Option<Expression<F>>,
}

impl<F: FieldExt> StateTransitions<F> {
    pub(crate) fn constraints(
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
