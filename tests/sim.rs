use qleisli_core::ir::{
    BasisShape, ClassicalId, Control, Effect, ProtectedBit, ProtectedRegion, ProtectedUse,
    QuantumPhi, QuantumPort, RawOp, RawProgram, ScalarPhase, SingleGate, TokenId, UnitaryStep,
    WireId,
};
use qleisli_core::sim::{SimulationError, SimulationLimits, run_closed};
use qleisli_core::verify;

fn t(id: u32) -> TokenId {
    TokenId(id)
}

fn w(id: u32) -> WireId {
    WireId(id)
}

fn c(id: u32) -> ClassicalId {
    ClassicalId(id)
}

fn closed(
    operations: Vec<RawOp>,
    classical_outputs: Vec<ClassicalId>,
) -> qleisli_core::VerifiedProgram {
    verify(RawProgram {
        quantum_inputs: vec![],
        classical_inputs: vec![],
        operations,
        quantum_outputs: vec![],
        classical_outputs,
        declared_effect: Effect::Observe,
    })
    .expect("test program should verify")
}

fn run(program: &qleisli_core::VerifiedProgram) -> std::collections::BTreeMap<Vec<bool>, f64> {
    let distribution = run_closed(program, SimulationLimits::default()).unwrap();
    close(distribution.values().sum(), 1.0);
    distribution
}

fn close(actual: f64, expected: f64) {
    assert!(
        (actual - expected).abs() < 1e-12,
        "expected {expected}, got {actual}"
    );
}

#[test]
fn repeated_t_phase_can_leave_a_tiny_floating_point_outcome() {
    let mut operations = vec![
        RawOp::Init0 {
            output: t(0),
            wire: w(0),
        },
        RawOp::Gate {
            gate: SingleGate::H,
            input: t(0),
            output: t(1),
        },
    ];
    for index in 0..8 {
        operations.push(RawOp::Gate {
            gate: SingleGate::T,
            input: t(index + 1),
            output: t(index + 2),
        });
    }
    operations.extend([
        RawOp::Gate {
            gate: SingleGate::H,
            input: t(9),
            output: t(10),
        },
        RawOp::MeasureZ {
            input: t(10),
            output: c(0),
        },
    ]);
    let distribution = run(&closed(operations, vec![c(0)]));
    close(distribution[&vec![false]], 1.0);
    assert!(distribution.get(&vec![true]).copied().unwrap_or(0.0) < 1e-28);
}

#[test]
fn bell_lift_split_and_measure_has_only_matching_outcomes() {
    let program = closed(
        vec![
            RawOp::Init0 {
                output: t(0),
                wire: w(0),
            },
            RawOp::Gate {
                gate: SingleGate::H,
                input: t(0),
                output: t(1),
            },
            RawOp::LiftBasis {
                input: t(1),
                output: t(2),
                output_wires: vec![w(0), w(1)],
                table: vec![0, 3],
            },
            RawOp::Split {
                input: t(2),
                left: t(3),
                right: t(4),
                left_bits: 1,
            },
            RawOp::MeasureZ {
                input: t(3),
                output: c(0),
            },
            RawOp::MeasureZ {
                input: t(4),
                output: c(1),
            },
        ],
        vec![c(0), c(1)],
    );
    let distribution = run(&program);
    assert_eq!(distribution.len(), 2);
    close(distribution[&vec![false, false]], 0.5);
    close(distribution[&vec![true, true]], 0.5);
}

fn bell_cnot_prefix() -> Vec<RawOp> {
    vec![
        RawOp::Init0 {
            output: t(0),
            wire: w(0),
        },
        RawOp::Gate {
            gate: SingleGate::H,
            input: t(0),
            output: t(1),
        },
        RawOp::Init0 {
            output: t(2),
            wire: w(1),
        },
        RawOp::Cnot {
            control: t(1),
            target: t(2),
            control_out: t(3),
            target_out: t(4),
        },
    ]
}

#[test]
fn computed_phase_oracle_not_function_interferes_to_one() {
    let program = closed(
        vec![
            RawOp::Init0 {
                output: t(0),
                wire: w(0),
            },
            RawOp::Gate {
                gate: SingleGate::H,
                input: t(0),
                output: t(1),
            },
            RawOp::ComputeUseUncompute {
                source: t(1),
                source_out: t(2),
                targets: vec![],
                ancilla_wires: vec![w(1)],
                function: vec![1, 0],
                use_ops: vec![ProtectedUse::ProtectedGate {
                    bit: ProtectedBit {
                        region: ProtectedRegion::Ancilla,
                        index: 0,
                    },
                    gate: SingleGate::Z,
                }],
            },
            RawOp::Gate {
                gate: SingleGate::H,
                input: t(2),
                output: t(3),
            },
            RawOp::MeasureZ {
                input: t(3),
                output: c(0),
            },
        ],
        vec![c(0)],
    );
    let distribution = run(&program);
    assert_eq!(distribution.len(), 1);
    close(distribution[&vec![true]], 1.0);
}

#[test]
fn bell_half_measurement_and_feedback_corrects_other_half() {
    let mut ops = bell_cnot_prefix();
    ops.extend([
        RawOp::MeasureZ {
            input: t(3),
            output: c(0),
        },
        RawOp::ClassicalBranch {
            condition: c(0),
            then_ops: vec![RawOp::Gate {
                gate: SingleGate::X,
                input: t(4),
                output: t(5),
            }],
            else_ops: vec![],
            quantum_phis: vec![QuantumPhi {
                then_token: t(5),
                else_token: t(4),
                output: t(6),
                output_wires: vec![w(2)],
            }],
            classical_phis: vec![],
        },
        RawOp::MeasureZ {
            input: t(6),
            output: c(1),
        },
    ]);
    let distribution = run(&closed(ops, vec![c(1)]));
    assert_eq!(distribution.len(), 1);
    close(distribution[&vec![false]], 1.0);
}

#[test]
fn discarding_entangled_half_keeps_mixed_residual() {
    let mut ops = bell_cnot_prefix();
    ops.extend([
        RawOp::Discard { input: t(3) },
        RawOp::Gate {
            gate: SingleGate::H,
            input: t(4),
            output: t(5),
        },
        RawOp::MeasureZ {
            input: t(5),
            output: c(0),
        },
    ]);
    let distribution = run(&closed(ops, vec![c(0)]));
    assert_eq!(distribution.len(), 2);
    close(distribution[&vec![false]], 0.5);
    close(distribution[&vec![true]], 0.5);
}

#[test]
fn reset_breaks_bell_correlation_and_returns_new_zero_wire() {
    let mut ops = bell_cnot_prefix();
    ops.extend([
        RawOp::Reset {
            input: t(3),
            output: t(5),
            fresh_wire: w(2),
        },
        RawOp::MeasureZ {
            input: t(5),
            output: c(0),
        },
        RawOp::MeasureZ {
            input: t(4),
            output: c(1),
        },
    ]);
    let distribution = run(&closed(ops, vec![c(0), c(1)]));
    assert_eq!(distribution.len(), 2);
    close(distribution[&vec![false, false]], 0.5);
    close(distribution[&vec![false, true]], 0.5);
}

#[test]
fn scalar_phase_survives_even_without_target_wires() {
    let program = closed(
        vec![
            RawOp::Init0 {
                output: t(0),
                wire: w(0),
            },
            RawOp::Gate {
                gate: SingleGate::H,
                input: t(0),
                output: t(1),
            },
            RawOp::ComputeUseUncompute {
                source: t(1),
                source_out: t(2),
                targets: vec![],
                ancilla_wires: vec![w(1)],
                function: vec![0, 1],
                use_ops: vec![ProtectedUse::ControlledPhase {
                    controls: vec![Control {
                        bit: ProtectedBit {
                            region: ProtectedRegion::Ancilla,
                            index: 0,
                        },
                        when_one: true,
                    }],
                    phase: ScalarPhase::EighthTurn,
                }],
            },
            RawOp::Gate {
                gate: SingleGate::H,
                input: t(2),
                output: t(3),
            },
            RawOp::MeasureZ {
                input: t(3),
                output: c(0),
            },
        ],
        vec![c(0)],
    );
    let distribution = run(&program);
    close(
        distribution[&vec![false]],
        (1.0 + std::f64::consts::FRAC_1_SQRT_2) / 2.0,
    );
    close(
        distribution[&vec![true]],
        (1.0 - std::f64::consts::FRAC_1_SQRT_2) / 2.0,
    );
}

#[test]
fn computed_predicate_controls_target_without_measuring_source() {
    let program = closed(
        vec![
            RawOp::Init0 {
                output: t(0),
                wire: w(0),
            },
            RawOp::Gate {
                gate: SingleGate::H,
                input: t(0),
                output: t(1),
            },
            RawOp::Init0 {
                output: t(2),
                wire: w(1),
            },
            RawOp::ComputeUseUncompute {
                source: t(1),
                source_out: t(3),
                targets: vec![qleisli_core::ir::TargetTransition {
                    input: t(2),
                    output: t(4),
                }],
                ancilla_wires: vec![w(2)],
                function: vec![0, 1],
                use_ops: vec![ProtectedUse::ControlledTargetGate {
                    controls: vec![Control {
                        bit: ProtectedBit {
                            region: ProtectedRegion::Ancilla,
                            index: 0,
                        },
                        when_one: true,
                    }],
                    target_index: 0,
                    gate: SingleGate::X,
                }],
            },
            RawOp::MeasureZ {
                input: t(3),
                output: c(0),
            },
            RawOp::MeasureZ {
                input: t(4),
                output: c(1),
            },
        ],
        vec![c(0), c(1)],
    );
    let distribution = run(&program);
    assert_eq!(distribution.len(), 2);
    close(distribution[&vec![false, false]], 0.5);
    close(distribution[&vec![true, true]], 0.5);
}

#[test]
fn join_and_permutation_lift_use_register_bit_order() {
    let program = closed(
        vec![
            RawOp::Init0 {
                output: t(0),
                wire: w(0),
            },
            RawOp::Init0 {
                output: t(1),
                wire: w(1),
            },
            RawOp::Join {
                left: t(0),
                right: t(1),
                output: t(2),
            },
            RawOp::LiftBasis {
                input: t(2),
                output: t(3),
                output_wires: vec![w(0), w(1)],
                table: vec![3, 0, 1, 2],
            },
            RawOp::Split {
                input: t(3),
                left: t(4),
                right: t(5),
                left_bits: 1,
            },
            RawOp::MeasureZ {
                input: t(4),
                output: c(0),
            },
            RawOp::MeasureZ {
                input: t(5),
                output: c(1),
            },
        ],
        vec![c(0), c(1)],
    );
    let distribution = run(&program);
    assert_eq!(distribution.len(), 1);
    close(distribution[&vec![true, true]], 1.0);
}

#[test]
fn toffoli_and_classical_boolean_ops_execute() {
    let program = closed(
        vec![
            RawOp::Init0 {
                output: t(0),
                wire: w(0),
            },
            RawOp::Gate {
                gate: SingleGate::X,
                input: t(0),
                output: t(1),
            },
            RawOp::Init0 {
                output: t(2),
                wire: w(1),
            },
            RawOp::Gate {
                gate: SingleGate::X,
                input: t(2),
                output: t(3),
            },
            RawOp::Init0 {
                output: t(4),
                wire: w(2),
            },
            RawOp::Toffoli {
                control_a: t(1),
                control_b: t(3),
                target: t(4),
                control_a_out: t(5),
                control_b_out: t(6),
                target_out: t(7),
            },
            RawOp::Discard { input: t(5) },
            RawOp::Discard { input: t(6) },
            RawOp::MeasureZ {
                input: t(7),
                output: c(0),
            },
            RawOp::ClassicalNot {
                input: c(0),
                output: c(1),
            },
            RawOp::ClassicalXor {
                left: c(0),
                right: c(1),
                output: c(2),
            },
        ],
        vec![c(0), c(1), c(2)],
    );
    let distribution = run(&program);
    assert_eq!(distribution.len(), 1);
    close(distribution[&vec![true, false, true]], 1.0);
}

#[test]
fn nonclosed_input_and_dimension_limit_are_reported() {
    let open = verify(RawProgram {
        quantum_inputs: vec![QuantumPort {
            token: t(0),
            wires: vec![w(0)],
            shape: BasisShape::BIT,
        }],
        classical_inputs: vec![],
        operations: vec![RawOp::MeasureZ {
            input: t(0),
            output: c(0),
        }],
        quantum_outputs: vec![],
        classical_outputs: vec![c(0)],
        declared_effect: Effect::Observe,
    })
    .unwrap();
    assert!(matches!(
        run_closed(&open, SimulationLimits::default()),
        Err(SimulationError::NotClosed(_))
    ));

    let mut ops = bell_cnot_prefix();
    ops.extend([
        RawOp::MeasureZ {
            input: t(3),
            output: c(0),
        },
        RawOp::MeasureZ {
            input: t(4),
            output: c(1),
        },
    ]);
    let bell = closed(ops, vec![c(0), c(1)]);
    let err = run_closed(
        &bell,
        SimulationLimits {
            max_qubits: 1,
            max_components: 8,
            ..SimulationLimits::default()
        },
    );
    assert_eq!(
        err,
        Err(SimulationError::DimensionLimit {
            required: 2,
            max: 1
        })
    );

    let amplitude_error = run_closed(
        &bell,
        SimulationLimits {
            max_amplitude_cells: 1,
            ..SimulationLimits::default()
        },
    );
    assert_eq!(
        amplitude_error,
        Err(SimulationError::AmplitudeLimit {
            required: 2,
            max: 1
        })
    );
}

#[test]
fn coherent_qif_entangles_control_and_target() {
    let program = closed(
        vec![
            RawOp::Init0 {
                output: t(0),
                wire: w(0),
            },
            RawOp::Gate {
                gate: SingleGate::H,
                input: t(0),
                output: t(1),
            },
            RawOp::Init0 {
                output: t(2),
                wire: w(1),
            },
            RawOp::QuantumIf {
                control: t(1),
                target: t(2),
                control_out: t(3),
                target_out: t(4),
                zero_ops: vec![],
                one_ops: vec![UnitaryStep::Gate {
                    gate: SingleGate::X,
                    target_index: 0,
                }],
            },
            RawOp::MeasureZ {
                input: t(3),
                output: c(0),
            },
            RawOp::MeasureZ {
                input: t(4),
                output: c(1),
            },
        ],
        vec![c(0), c(1)],
    );
    let distribution = run(&program);
    assert_eq!(distribution.len(), 2);
    close(distribution[&vec![false, false]], 0.5);
    close(distribution[&vec![true, true]], 0.5);
}

#[test]
fn unit_target_scalar_phase_becomes_relative_control_phase() {
    let program = closed(
        vec![
            RawOp::Init0 {
                output: t(0),
                wire: w(0),
            },
            RawOp::Gate {
                gate: SingleGate::H,
                input: t(0),
                output: t(1),
            },
            RawOp::Split {
                input: t(1),
                left: t(2),
                right: t(3),
                left_bits: 0,
            },
            RawOp::QuantumIf {
                control: t(3),
                target: t(2),
                control_out: t(4),
                target_out: t(5),
                zero_ops: vec![],
                one_ops: vec![UnitaryStep::ScalarPhase(ScalarPhase::MinusOne)],
            },
            RawOp::Join {
                left: t(5),
                right: t(4),
                output: t(6),
            },
            RawOp::Gate {
                gate: SingleGate::H,
                input: t(6),
                output: t(7),
            },
            RawOp::MeasureZ {
                input: t(7),
                output: c(0),
            },
        ],
        vec![c(0)],
    );
    let distribution = run(&program);
    assert_eq!(distribution.len(), 1);
    close(distribution[&vec![true]], 1.0);
}
