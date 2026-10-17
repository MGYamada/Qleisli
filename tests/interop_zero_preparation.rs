//! Bounded terminal artifacts for an ordinary singleton zero preparation.
//! These tests do not establish a general source/export preservation theorem.
mod common;

use common::{SourceRoot, accept};
use qleisli::AcceptedProgram;
use qleisli::contract::exact::{Budget, Exact, Matrix};
use qleisli::contract::{
    BasisType, CheckedContract, Circuit, Contract, ContractError, DEFAULT_EXACT_WORK, Encoding,
};
use qleisli::interop::{InteropErrorKind, export_openqasm3, export_qir_base};
use qleisli::ir::*;

const ZERO: &str = "pub isometry fn init0()->Q<Bit>{basis unit(()) as () {0}}";

fn source(definition: &str, body: &str, result: &str) -> AcceptedProgram {
    let text = format!(
        "use std::gate::{{x,cnot}};
         {definition} pub observe fn main()->{result}{{{body}}}"
    );
    qleisli::frontend::compile::compile_project(&SourceRoot::new(&text).0).unwrap()
}

fn terminal(operations: Vec<RawOp>, outputs: Vec<ClassicalId>) -> AcceptedProgram {
    accept(RawProgram {
        quantum_inputs: vec![],
        classical_inputs: vec![],
        operations,
        quantum_outputs: vec![],
        classical_outputs: outputs,
        declared_effect: Effect::Observe,
    })
    .unwrap()
}

// This baseline is independent of the ordinary preparation body and its
// lowering. Init0 remains an admitted Raw operation; no source alias supplies
// it. Native X/Cnot words and the exact literal expectations remain explicit.
fn raw_init0_baseline(width: usize) -> AcceptedProgram {
    let operations = match width {
        0 => vec![],
        1 => vec![
            RawOp::Init0 {
                output: TokenId(0),
                wire: WireId(0),
            },
            RawOp::MeasureZ {
                input: TokenId(0),
                output: ClassicalId(0),
            },
        ],
        2 => vec![
            RawOp::Init0 {
                output: TokenId(0),
                wire: WireId(0),
            },
            RawOp::Gate {
                gate: SingleGate::H,
                input: TokenId(0),
                output: TokenId(1),
            },
            RawOp::Init0 {
                output: TokenId(2),
                wire: WireId(1),
            },
            RawOp::Cnot {
                control: TokenId(1),
                target: TokenId(2),
                control_out: TokenId(3),
                target_out: TokenId(4),
            },
            RawOp::MeasureZ {
                input: TokenId(4),
                output: ClassicalId(0),
            },
            RawOp::MeasureZ {
                input: TokenId(3),
                output: ClassicalId(1),
            },
        ],
        3 => vec![
            RawOp::Init0 {
                output: TokenId(0),
                wire: WireId(0),
            },
            RawOp::Gate {
                gate: SingleGate::X,
                input: TokenId(0),
                output: TokenId(1),
            },
            RawOp::Init0 {
                output: TokenId(2),
                wire: WireId(1),
            },
            RawOp::Gate {
                gate: SingleGate::H,
                input: TokenId(2),
                output: TokenId(3),
            },
            RawOp::Init0 {
                output: TokenId(4),
                wire: WireId(2),
            },
            RawOp::Cnot {
                control: TokenId(3),
                target: TokenId(4),
                control_out: TokenId(5),
                target_out: TokenId(6),
            },
            RawOp::MeasureZ {
                input: TokenId(6),
                output: ClassicalId(0),
            },
            RawOp::MeasureZ {
                input: TokenId(1),
                output: ClassicalId(1),
            },
            RawOp::MeasureZ {
                input: TokenId(5),
                output: ClassicalId(2),
            },
        ],
        _ => panic!("only the four bounded artifact baselines are defined"),
    };
    terminal(
        operations,
        (0..width).map(|index| ClassicalId(index as u32)).collect(),
    )
}

fn raw_sparse_init0_baseline() -> AcceptedProgram {
    terminal(
        vec![
            RawOp::Init0 {
                output: TokenId(0),
                wire: WireId(91),
            },
            RawOp::Gate {
                gate: SingleGate::H,
                input: TokenId(0),
                output: TokenId(1),
            },
            RawOp::Init0 {
                output: TokenId(2),
                wire: WireId(7),
            },
            RawOp::Cnot {
                control: TokenId(1),
                target: TokenId(2),
                control_out: TokenId(3),
                target_out: TokenId(4),
            },
            RawOp::Init0 {
                output: TokenId(5),
                wire: WireId(55),
            },
            RawOp::Gate {
                gate: SingleGate::X,
                input: TokenId(5),
                output: TokenId(6),
            },
            RawOp::MeasureZ {
                input: TokenId(3),
                output: ClassicalId(0),
            },
            RawOp::MeasureZ {
                input: TokenId(4),
                output: ClassicalId(1),
            },
            RawOp::MeasureZ {
                input: TokenId(6),
                output: ClassicalId(2),
            },
        ],
        vec![ClassicalId(2), ClassicalId(0), ClassicalId(1)],
    )
}

// Read the actual emitted words in this small profile, independently of the
// exporter. The encoding below models the target's explicit initial |0...0>.
fn literal_circuit(text: &str) -> (usize, Vec<CircuitStep>) {
    let mut width = 0;
    let mut steps = vec![];
    for line in text.lines() {
        if let Some(rest) = line.strip_prefix("qubit[") {
            width = rest.strip_suffix("] q;").unwrap().parse().unwrap();
        } else if !line.is_empty()
            && line != "OPENQASM 3.0;"
            && line != "include \"stdgates.inc\";"
            && line != "reset q;"
            && !line.starts_with("bit[")
            && !line.starts_with("c[")
        {
            let (gate, operands) = line.strip_suffix(';').unwrap().split_once(' ').unwrap();
            let axes: Vec<usize> = operands
                .split(", ")
                .map(|axis| {
                    axis.strip_prefix("q[")
                        .unwrap()
                        .strip_suffix(']')
                        .unwrap()
                        .parse()
                        .unwrap()
                })
                .collect();
            let step = match (gate, axes.as_slice()) {
                ("h", [target]) => CircuitStep {
                    controls: vec![],
                    action: CircuitAction::Hadamard { target: *target },
                },
                ("x", [target]) | ("cx", [_, target]) => CircuitStep {
                    controls: if gate == "cx" {
                        vec![BitControl {
                            index: axes[0],
                            when_one: true,
                        }]
                    } else {
                        vec![]
                    },
                    action: CircuitAction::Monomial {
                        indices: vec![*target],
                        permutation: vec![1, 0],
                        phases: vec![0, 0],
                    },
                },
                _ => panic!("unexpected word in bounded preparation artifact: {line}"),
            };
            steps.push(step);
        }
    }
    assert!(width <= 3, "only small exact artifact experiments");
    (width, steps)
}

fn exact_state(text: &str, amplitudes: &[Exact]) -> Result<(), ContractError> {
    let (width, steps) = literal_circuit(text);
    assert_eq!(amplitudes.len(), 1 << width);
    let physical = BasisType::Bits(u32::try_from(width).unwrap());
    let mut budget = Budget::new(DEFAULT_EXACT_WORK);
    let input = Encoding::new(
        BasisType::Unit,
        physical.clone(),
        Matrix::new(
            1 << width,
            1,
            (0..1 << width)
                .map(|row| {
                    if row == 0 {
                        Exact::one()
                    } else {
                        Exact::zero()
                    }
                })
                .collect(),
        )?,
        &mut budget,
    )?;
    let output = Encoding::new(
        BasisType::Unit,
        physical.clone(),
        Matrix::new(1 << width, 1, amplitudes.to_vec())?,
        &mut budget,
    )?;
    let contract = Contract::new(input, output, Matrix::identity(1)?, &mut budget)?;
    CheckedContract::check(Circuit::new(physical, steps)?, contract, &mut budget).map(|_| ())
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn ordinary_zero_preparation_exports_literal_artifacts_with_exact_phase() {
    let zero = Exact::zero();
    let half = Exact::inv_sqrt2();
    for (body, result, width, expected, amplitudes) in [
        (
            "()",
            "Unit",
            0,
            "OPENQASM 3.0;\ninclude \"stdgates.inc\";\n",
            vec![Exact::one()],
        ),
        (
            "measure_z(init0())",
            "Bit",
            1,
            "OPENQASM 3.0;\ninclude \"stdgates.inc\";\nqubit[1] q;\nbit[1] c;\nreset q;\nc[0] = measure q[0];\n",
            vec![Exact::one(), zero],
        ),
        (
            "let(a,b)=cnot(h(init0()),init0());(measure_z(b),measure_z(a))",
            "(Bit,Bit)",
            2,
            "OPENQASM 3.0;\ninclude \"stdgates.inc\";\nqubit[2] q;\nbit[2] c;\nreset q;\nh q[0];\ncx q[0], q[1];\nc[0] = measure q[1];\nc[1] = measure q[0];\n",
            vec![half, zero, zero, half],
        ),
        (
            "let a=x(init0());let(b,c)=cnot(h(init0()),init0());(measure_z(c),measure_z(a),measure_z(b))",
            "(Bit,Bit,Bit)",
            3,
            "OPENQASM 3.0;\ninclude \"stdgates.inc\";\nqubit[3] q;\nbit[3] c;\nreset q;\nx q[0];\nh q[1];\ncx q[1], q[2];\nc[0] = measure q[2];\nc[1] = measure q[0];\nc[2] = measure q[1];\n",
            vec![zero, half, zero, zero, zero, zero, zero, half],
        ),
    ] {
        let program = source(ZERO, body, result);
        assert_eq!(
            program
                .raw()
                .operations
                .iter()
                .filter(|op| matches!(op,
                    RawOp::LiftBasis { output_wires, table, .. }
                    if output_wires.len() == 1 && table.as_slice() == [0]
                ))
                .count(),
            width
        );
        assert!(
            !program
                .raw()
                .operations
                .iter()
                .any(|op| matches!(op, RawOp::Init0 { .. }))
        );
        let qasm = export_openqasm3(&program).unwrap();
        let qir = export_qir_base(&program).unwrap();
        assert_eq!(qasm, expected);
        let reference = raw_init0_baseline(width);
        assert_eq!(qasm, export_openqasm3(&reference).unwrap());
        assert_eq!(qir, export_qir_base(&reference).unwrap());
        assert!(qir.contains(&format!("\"required_num_qubits\"=\"{width}\"")));
        exact_state(&qasm, &amplitudes).unwrap();
        let wrong_phase: Vec<_> = amplitudes
            .iter()
            .map(|amplitude| amplitude.mul(Exact::phase(1)).unwrap())
            .collect();
        assert!(exact_state(&qasm, &wrong_phase).is_err());
        if width == 3 {
            let wrong_axis = qasm.replace("x q[0];", "x q[1];");
            assert!(exact_state(&wrong_axis, &amplitudes).is_err());
        }
    }
    let ordinary = source(
        &ZERO.replace("init0", "fresh_from_unit"),
        "measure_z(fresh_from_unit())",
        "Bit",
    );
    assert_eq!(
        export_openqasm3(&ordinary).unwrap(),
        export_openqasm3(&source(ZERO, "measure_z(init0())", "Bit")).unwrap()
    );
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn sparse_raw_wire_names_preserve_existing_entanglement_and_result_order() {
    let program = terminal(
        vec![
            RawOp::Init0 {
                output: TokenId(0),
                wire: WireId(91),
            },
            RawOp::Gate {
                gate: SingleGate::H,
                input: TokenId(0),
                output: TokenId(1),
            },
            RawOp::PackUnit { output: TokenId(2) },
            RawOp::LiftBasis {
                input: TokenId(2),
                output: TokenId(3),
                output_wires: vec![WireId(7)],
                table: vec![0],
            },
            RawOp::Cnot {
                control: TokenId(1),
                target: TokenId(3),
                control_out: TokenId(4),
                target_out: TokenId(5),
            },
            RawOp::PackUnit { output: TokenId(6) },
            RawOp::LiftBasis {
                input: TokenId(6),
                output: TokenId(7),
                output_wires: vec![WireId(55)],
                table: vec![0],
            },
            RawOp::Gate {
                gate: SingleGate::X,
                input: TokenId(7),
                output: TokenId(8),
            },
            RawOp::MeasureZ {
                input: TokenId(4),
                output: ClassicalId(0),
            },
            RawOp::MeasureZ {
                input: TokenId(5),
                output: ClassicalId(1),
            },
            RawOp::MeasureZ {
                input: TokenId(8),
                output: ClassicalId(2),
            },
        ],
        vec![ClassicalId(2), ClassicalId(0), ClassicalId(1)],
    );
    let qasm = export_openqasm3(&program).unwrap();
    assert_eq!(
        qasm,
        "OPENQASM 3.0;\ninclude \"stdgates.inc\";\nqubit[3] q;\nbit[3] c;\nreset q;\nh q[0];\ncx q[0], q[1];\nx q[2];\nc[0] = measure q[2];\nc[1] = measure q[0];\nc[2] = measure q[1];\n"
    );
    let z = Exact::zero();
    let half = Exact::inv_sqrt2();
    exact_state(&qasm, &[z, z, z, z, half, z, z, half]).unwrap();
    let reference = raw_sparse_init0_baseline();
    assert_eq!(qasm, export_openqasm3(&reference).unwrap());
    assert_eq!(
        export_qir_base(&program).unwrap(),
        export_qir_base(&reference).unwrap()
    );
}

fn refused(program: &AcceptedProgram, operation: usize) {
    for result in [export_openqasm3(program), export_qir_base(program)] {
        let error = result.unwrap_err();
        assert_eq!(error.kind, InteropErrorKind::Unsupported);
        assert_eq!(error.operation, Some(operation));
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn other_injective_lifts_do_not_gain_preparation_export() {
    for (before, output_wires, table) in [
        (
            RawOp::PackUnit { output: TokenId(0) },
            vec![WireId(17)],
            vec![1],
        ),
        (
            RawOp::PackUnit { output: TokenId(0) },
            vec![WireId(17), WireId(29)],
            vec![0],
        ),
        (
            RawOp::Init0 {
                output: TokenId(0),
                wire: WireId(17),
            },
            vec![WireId(17), WireId(29)],
            vec![0, 1],
        ),
        (
            RawOp::Init0 {
                output: TokenId(0),
                wire: WireId(17),
            },
            vec![WireId(17)],
            vec![1, 0],
        ),
    ] {
        let program = terminal(
            vec![
                before,
                RawOp::LiftBasis {
                    input: TokenId(0),
                    output: TokenId(1),
                    output_wires,
                    table,
                },
                RawOp::Discard { input: TokenId(1) },
            ],
            vec![],
        );
        refused(&program, 1);
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn zero_preparation_preserves_observation_and_scalar_phase_refusals() {
    let after_observation = terminal(
        vec![
            RawOp::Init0 {
                output: TokenId(0),
                wire: WireId(17),
            },
            RawOp::MeasureZ {
                input: TokenId(0),
                output: ClassicalId(0),
            },
            RawOp::PackUnit { output: TokenId(1) },
            RawOp::LiftBasis {
                input: TokenId(1),
                output: TokenId(2),
                output_wires: vec![WireId(29)],
                table: vec![0],
            },
            RawOp::Discard { input: TokenId(2) },
        ],
        vec![ClassicalId(0)],
    );
    refused(&after_observation, 3);
    let scalar = terminal(
        vec![
            RawOp::PackUnit { output: TokenId(0) },
            RawOp::ApplyUnitary {
                input: TokenId(0),
                output: TokenId(1),
                steps: vec![CircuitStep {
                    controls: vec![],
                    action: CircuitAction::Monomial {
                        indices: vec![],
                        permutation: vec![0],
                        phases: vec![1],
                    },
                }],
            },
            RawOp::LiftBasis {
                input: TokenId(1),
                output: TokenId(2),
                output_wires: vec![WireId(29)],
                table: vec![0],
            },
            RawOp::MeasureZ {
                input: TokenId(2),
                output: ClassicalId(0),
            },
        ],
        vec![ClassicalId(0)],
    );
    refused(&scalar, 1);
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn malformed_preparation_requires_native_rejection_before_export() {
    for table in [vec![], vec![0, 0], vec![2]] {
        assert!(
            accept(RawProgram {
                quantum_inputs: vec![],
                classical_inputs: vec![],
                operations: vec![
                    RawOp::PackUnit { output: TokenId(0) },
                    RawOp::LiftBasis {
                        input: TokenId(0),
                        output: TokenId(1),
                        output_wires: vec![WireId(17)],
                        table
                    },
                    RawOp::Discard { input: TokenId(1) },
                ],
                quantum_outputs: vec![],
                classical_outputs: vec![],
                declared_effect: Effect::Observe,
            })
            .is_err()
        );
    }
}
