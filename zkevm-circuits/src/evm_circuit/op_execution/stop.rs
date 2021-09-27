use super::super::{Case, Cell, Constraint, CoreStateInstance, ExecutionStep};
use super::{CaseAllocation, CaseConfig, OpExecutionState, OpGadget};
use crate::util::Expr;
use bus_mapping::evm::OpcodeId;
use halo2::{arithmetic::FieldExt, circuit::Region, plonk::Error};
use std::{array, convert::TryInto};

#[derive(Clone, Debug)]
pub struct StopGadget<F> {
    success: Cell<F>, // case selector
}

impl<F: FieldExt> OpGadget<F> for StopGadget<F> {
    const RESPONSIBLE_OPCODES: &'static [OpcodeId] = &[OpcodeId::STOP];

    const CASE_CONFIGS: &'static [CaseConfig] = &[CaseConfig {
        case: Case::Success,
        num_word: 0,
        num_cell: 0,
        will_halt: true,
    }];

    fn construct(case_allocations: Vec<CaseAllocation<F>>) -> Self {
        let [success]: [CaseAllocation<F>; 1] =
            case_allocations.try_into().unwrap();
        Self {
            success: (success.selector.clone()),
        }
    }

    fn constraints(
        &self,
        state_curr: &OpExecutionState<F>,
        _state_next: &OpExecutionState<F>,
    ) -> Vec<Constraint<F>> {
        let OpExecutionState { opcode, .. } = &state_curr;

        let common_polys = vec![(opcode.expr() - OpcodeId::STOP.expr())];

        let success = {
            Constraint {
                name: "STOP success",
                selector: self.success.expr(),
                polys: vec![],
                lookups: vec![],
            }
        };

        array::IntoIter::new([success])
            .map(move |mut constraint| {
                constraint.polys =
                    [common_polys.clone(), constraint.polys].concat();
                constraint
            })
            .collect()
    }

    fn assign(
        &self,
        _region: &mut Region<'_, F>,
        _offset: usize,
        _core_state: &mut CoreStateInstance,
        execution_step: &ExecutionStep,
    ) -> Result<(), Error> {
        match execution_step.case {
            Case::Success => Ok(()),
            _ => unreachable!(),
        }
    }
}

#[cfg(test)]
mod test {
    use super::super::super::test::TestCircuit;
    use crate::bytecode;
    use crate::bytecode::Bytecode;
    use crate::tracer;
    use halo2::dev::MockProver;
    use num::BigUint;
    use pasta_curves::pallas::Base;

    macro_rules! try_test_circuit {
        ($bytecode:expr, $result:expr) => {{
            let trace = tracer::trace::<Base>(&$bytecode.code());
            let circuit = TestCircuit::<Base>::new(
                tracer::patch_steps_hack(&trace),
                tracer::patch_ops_hack(&trace),
            );
            let prover = MockProver::<Base>::run(10, &circuit, vec![]).unwrap();
            assert_eq!(prover.verify(), $result);
        }};
    }

    #[test]
    fn stop_gadget() {
        let v = BigUint::from(0x10u64);
        try_test_circuit!(
            bytecode![
                (PUSH1 v),
                (PUSH1 BigUint::from(0x20u64)),
                (PUSH1 0x30u64)
            ],
            Ok(())
        );
    }
}
