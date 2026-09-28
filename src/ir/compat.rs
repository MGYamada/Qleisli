//! Internal adapters for the existing public gate vocabulary. This is not a
//! foreign-format importer or a checker: callers must verify raw IR first.

use super::{BitControl, CircuitAction, CircuitStep, ScalarPhase, SingleGate, UnitaryStep};

impl UnitaryStep {
    /// Use the existing finite circuit vocabulary instead of another numeric
    /// interpreter. The exact evidence extractor deliberately stays independent.
    pub(crate) fn to_circuit_step(self) -> CircuitStep {
        let (gate, target, controls) = match self {
            Self::Gate { gate, target_index } => (gate, target_index, vec![]),
            Self::Cnot {
                control_index,
                target_index,
            } => (SingleGate::X, target_index, vec![control_index]),
            Self::Toffoli {
                control_a_index,
                control_b_index,
                target_index,
            } => (
                SingleGate::X,
                target_index,
                vec![control_a_index, control_b_index],
            ),
            Self::ScalarPhase(phase) => {
                return CircuitStep {
                    controls: vec![],
                    action: CircuitAction::Monomial {
                        indices: vec![],
                        permutation: vec![0],
                        phases: vec![match phase {
                            ScalarPhase::MinusOne => 4,
                            ScalarPhase::EighthTurn => 1,
                        }],
                    },
                };
            }
        };
        CircuitStep {
            controls: controls
                .into_iter()
                .map(|index| BitControl {
                    index,
                    when_one: true,
                })
                .collect(),
            action: match gate {
                SingleGate::H => CircuitAction::Hadamard { target },
                _ => CircuitAction::Monomial {
                    indices: vec![target],
                    permutation: match gate {
                        SingleGate::X => vec![1, 0],
                        _ => vec![0, 1],
                    },
                    phases: vec![
                        0,
                        match gate {
                            SingleGate::Z => 4,
                            SingleGate::T => 1,
                            _ => 0,
                        },
                    ],
                },
            },
        }
    }
}
