use qleisli::interop::{
    InteropErrorKind, MAX_OPENQASM_BYTES, export_openqasm3, export_qir_base, import_openqasm3,
};
use qleisli::ir::*;
use qleisli::sim::{SimulationLimits, run_closed};
use qleisli::{VerifiedProgram, verify};

const BELL: &str = include_str!("fixtures/interop/bell.qasm");
const GATES: &str = include_str!("fixtures/interop/gates.qasm");
fn source(body: &str) -> String {
    format!("OPENQASM 3.0; include \"stdgates.inc\"; {body}")
}
fn probability(program: &VerifiedProgram, bits: &[bool]) -> f64 {
    run_closed(program, SimulationLimits::default())
        .unwrap()
        .get(bits)
        .copied()
        .unwrap_or(0.0)
}
fn close(actual: f64, expected: f64) {
    assert!((actual - expected).abs() < 1e-12, "{actual} != {expected}");
}
fn raw(ops: Vec<RawOp>, outputs: Vec<ClassicalId>) -> VerifiedProgram {
    verify(RawProgram {
        quantum_inputs: vec![],
        classical_inputs: vec![],
        operations: ops,
        quantum_outputs: vec![],
        classical_outputs: outputs,
        declared_effect: Effect::Observe,
    })
    .unwrap()
}

#[test]
fn independent_bell_and_gate_fixtures_are_verified() {
    let bell = import_openqasm3(BELL).unwrap();
    close(probability(&bell, &[false, false]), 0.5);
    close(probability(&bell, &[true, true]), 0.5);
    assert!(bell.raw().operations.iter().all(|op| matches!(
        op,
        RawOp::Init0 { .. }
            | RawOp::ApplyUnitary { .. }
            | RawOp::Join { .. }
            | RawOp::Split { .. }
            | RawOp::MeasureZ { .. }
            | RawOp::Discard { .. }
    )));
    let gates = import_openqasm3(GATES).unwrap();
    for program in [&bell, &gates] {
        let canonical = export_openqasm3(program).unwrap();
        assert!(canonical.contains("reset q;"));
        let roundtrip = import_openqasm3(&canonical).unwrap();
        assert_eq!(
            run_closed(program, SimulationLimits::default()).unwrap(),
            run_closed(&roundtrip, SimulationLimits::default()).unwrap()
        );
    }
}

#[test]
fn control_axes_and_classical_order_do_not_follow_measurement_order() {
    let p = import_openqasm3(&source("qubit[3] q; bit a; bit[2] b; reset q; x q[2]; cx q[2], q[0]; b[1] = measure q[0]; a = measure q[1]; b[0] = measure q[2];")).unwrap();
    close(probability(&p, &[false, true, true]), 1.0);
    let exported = export_openqasm3(&p).unwrap();
    assert!(exported.contains("c[0] = measure q[1];\nc[1] = measure q[2];\nc[2] = measure q[0];"));
    let qir = export_qir_base(&p).unwrap();
    assert!(qir.contains("@__quantum__qis__mz__body(ptr inttoptr (i64 1 to ptr), ptr null)"));
    assert!(qir.contains("@__quantum__qis__mz__body(ptr null, ptr inttoptr (i64 2 to ptr))"));
}

#[test]
fn exact_phase_interference_and_hidden_terminal_results() {
    let cr = import_openqasm3(&source(
        "// comment\rqubit q; bit c; reset q; x q; c = measure q;",
    ))
    .unwrap();
    close(probability(&cr, &[true]), 1.0);
    for gates in [
        "h q; z q; h q;",
        "h q; s q; s q; h q;",
        "h q; t q; t q; t q; t q; h q;",
        "y q;",
    ] {
        let p = import_openqasm3(&source(&format!(
            "qubit q; bit c; reset q; {gates} c = measure q;"
        )))
        .unwrap();
        close(probability(&p, &[true]), 1.0);
    }
    let p = import_openqasm3(&source(
        "qubit[2] q; bit c; reset q; h q[0]; cx q[0], q[1]; measure q[0]; c = measure q[1];",
    ))
    .unwrap();
    close(probability(&p, &[false]), 0.5);
    close(probability(&p, &[true]), 0.5);
    assert!(
        p.raw()
            .operations
            .iter()
            .any(|op| matches!(op, RawOp::Discard { .. }))
    );
    let p = import_openqasm3("OPENQASM 3.0;").unwrap();
    close(probability(&p, &[]), 1.0);
    assert!(
        export_qir_base(&p)
            .unwrap()
            .contains("array_record_output(i64 0, ptr @label.0)")
    );
}

#[test]
fn invalid_source_is_rejected_with_original_locations() {
    let cases = [
        "qubit q; h q;", // OpenQASM declarations do not initialize qubits.
        "qubit q;",
        "qubit[2] q; reset q[0]; h q[0];",
        "qubit q; reset q; reset q;",
        "qubit q; reset q; x q; reset q;",
        "qubit q; reset q; bit c;",
        "qubit[0] q;",
        "qubit[01] q;",
        "qubit q; qubit q;",
        "qubit h;",
        "qubit rx; reset rx;",
        "qubit U; reset U;",
        "qubit reset;",
        "qubit[1] q; reset q; h q;",
        "qubit q; reset q[0];",
        "qubit[1] q; reset q[1];",
        "qubit[2] q; reset q; cx q[0], q[0];",
        "qubit q; reset q; measure q; x q;",
        "qubit q; reset q; measure q; measure q;",
        "qubit[2] q; bit c; reset q; c = measure q[0]; c = measure q[1];",
        "qubit[2] q; bit[1] c; reset q; c = measure q;",
        "qubit q; bit[1] c; reset q; c = measure q;",
        "qubit q; bit c; reset q;",
        "qubit q; reset q; h missing;",
        "qubit q; reset q; rx(0.1) q;",
        "qubit q; reset q; inv @ h q;",
        "gate h a {}",
        "include \"stdgates.inc\";",
        "/* unterminated",
        "/* outer /* nested */ */",
        "extern magic();",
    ];
    for body in cases {
        let text = source(body);
        let err = import_openqasm3(&text).expect_err(body);
        let span = err.span.expect(body);
        assert!(span.start <= span.end && span.end <= text.len(), "{body}");
    }
    for text in [
        "",
        "OPENQASM 2.0;",
        "OPENQASM 3.2;",
        "OPENQASM 3 .0;",
        "OPENQASM 3. 0;",
        "OPENQASM 3.0; qubit pi; reset pi;",
        "OPENQASM 3.0;\u{b}qubit q; reset q;",
        "OPENQASM 3.0; include \"../../secret\";",
        "OPENQASM 3.0; qubit q; reset q; h q;",
    ] {
        assert!(import_openqasm3(text).is_err(), "{text}");
    }
    let text = source("// 日本語\r\nqubit q; reset q; mystery q;");
    let err = import_openqasm3(&text).unwrap_err();
    assert_eq!(err.span.unwrap().start, text.find("mystery").unwrap());
    // Every truncated prefix must return an error or a complete accepted program,
    // never panic or reinterpret an unfinished declaration as valid ownership.
    for (end, _) in BELL.char_indices() {
        let _ = import_openqasm3(&BELL[..end]);
    }
}

#[test]
fn import_limits_are_checked_before_expansion() {
    let err = import_openqasm3(&" ".repeat(MAX_OPENQASM_BYTES + 1)).unwrap_err();
    assert_eq!(err.kind, InteropErrorKind::Limit);
    for body in [
        "qubit[13] q;",
        "bit[13] c;",
        "qubit[99999999999999999999999999999] q;",
    ] {
        assert_eq!(
            import_openqasm3(&source(body)).unwrap_err().kind,
            InteropErrorKind::Limit
        );
    }
    let prefix = "qubit q; reset q; ";
    let allowed = source(&format!("{prefix}{}measure q;", "h q;".repeat(4096)));
    import_openqasm3(&allowed).unwrap();
    assert_eq!(
        import_openqasm3(&source(&format!(
            "{prefix}{}measure q;",
            "h q;".repeat(4097)
        )))
        .unwrap_err()
        .kind,
        InteropErrorKind::Limit
    );
    assert_eq!(
        import_openqasm3(&";".repeat(65_537)).unwrap_err().kind,
        InteropErrorKind::Limit
    );
}

#[test]
fn valid_ir_can_still_be_unrepresentable_in_the_target() {
    let p = import_openqasm3(BELL).unwrap();
    let mut duplicated = p.raw().clone();
    duplicated
        .classical_outputs
        .push(duplicated.classical_outputs[0]);
    assert_eq!(
        export_openqasm3(&verify(duplicated).unwrap())
            .unwrap_err()
            .kind,
        InteropErrorKind::Unsupported
    );
    let scalar = raw(
        vec![
            RawOp::Init0 {
                output: TokenId(0),
                wire: WireId(0),
            },
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
            RawOp::Discard { input: TokenId(1) },
        ],
        vec![],
    );
    for result in [export_openqasm3(&scalar), export_qir_base(&scalar)] {
        let err = result.unwrap_err();
        assert_eq!(err.operation, Some(1));
        assert_eq!(err.kind, InteropErrorKind::Unsupported);
    }
    let open = verify(RawProgram {
        quantum_inputs: vec![QuantumPort {
            token: TokenId(0),
            wires: vec![WireId(0)],
            shape: BasisShape::BIT,
        }],
        classical_inputs: vec![],
        operations: vec![],
        quantum_outputs: vec![TokenId(0)],
        classical_outputs: vec![],
        declared_effect: Effect::Unitary,
    })
    .unwrap();
    assert!(export_qir_base(&open).is_err());
    let observed = raw(
        vec![
            RawOp::Init0 {
                output: TokenId(0),
                wire: WireId(0),
            },
            RawOp::MeasureZ {
                input: TokenId(0),
                output: ClassicalId(0),
            },
            RawOp::Init0 {
                output: TokenId(1),
                wire: WireId(1),
            },
            RawOp::Discard { input: TokenId(1) },
        ],
        vec![ClassicalId(0)],
    );
    assert_eq!(export_qir_base(&observed).unwrap_err().operation, Some(2));
    let p =
        qleisli::frontend::compile::compile_project(std::path::Path::new("examples/bell")).unwrap();
    assert!(
        export_openqasm3(&p).is_err(),
        "arbitrary lifts are not silently rewritten"
    );
}

#[test]
fn qli_frontend_and_qir_profile_contract() {
    let p = qleisli::frontend::compile::compile_project(std::path::Path::new(
        "tests/fixtures/interop/terminal",
    ))
    .unwrap();
    let qasm = export_openqasm3(&p).unwrap();
    close(
        probability(&import_openqasm3(&qasm).unwrap(), &[true, true]),
        0.5,
    );
    let qir = export_qir_base(&import_openqasm3(GATES).unwrap()).unwrap();
    for expected in [
        "define i64 @main() #0",
        "\nentry:",
        "\nbody:",
        "\nmeasurements:",
        "\noutput:",
        "\"qir_profiles\"=\"base_profile\"",
        "\"required_num_qubits\"=\"3\"",
        "\"required_num_results\"=\"3\"",
        "ptr writeonly",
        "\"irreversible\"",
        "qleisli.bit-vector.v1",
        "!\"qir_major_version\", i32 2",
        "!\"dynamic_qubit_management\", i1 false",
        "!\"dynamic_result_management\", i1 false",
        "@__quantum__qis__s__adj",
        "@__quantum__qis__t__adj",
        "@__quantum__qis__ccx__body",
        "ret i64 0",
    ] {
        assert!(qir.contains(expected), "{expected}");
    }
    assert!(!qir.contains("result_record_output(ptr null, ptr null)"));
}

#[test]
fn export_tracks_reordered_owners_and_rejects_other_control_forms() {
    let mut p = raw(
        vec![
            RawOp::Init0 {
                output: TokenId(0),
                wire: WireId(80),
            },
            RawOp::Gate {
                gate: SingleGate::X,
                input: TokenId(0),
                output: TokenId(1),
            },
            RawOp::Init0 {
                output: TokenId(2),
                wire: WireId(2),
            },
            RawOp::Join {
                left: TokenId(2),
                right: TokenId(1),
                output: TokenId(3),
            },
            RawOp::ApplyUnitary {
                input: TokenId(3),
                output: TokenId(4),
                steps: vec![CircuitStep {
                    controls: vec![BitControl {
                        index: 1,
                        when_one: true,
                    }],
                    action: CircuitAction::Monomial {
                        indices: vec![0],
                        permutation: vec![1, 0],
                        phases: vec![0, 0],
                    },
                }],
            },
            RawOp::Split {
                input: TokenId(4),
                left: TokenId(5),
                right: TokenId(6),
                left_bits: 1,
            },
            RawOp::MeasureZ {
                input: TokenId(5),
                output: ClassicalId(20),
            },
            RawOp::MeasureZ {
                input: TokenId(6),
                output: ClassicalId(10),
            },
        ],
        vec![ClassicalId(20), ClassicalId(10)],
    )
    .raw()
    .clone();
    let text = export_openqasm3(&verify(p.clone()).unwrap()).unwrap();
    assert!(text.contains("cx q[0], q[1];"));
    assert!(text.contains("c[0] = measure q[1];"));
    close(
        probability(&import_openqasm3(&text).unwrap(), &[true, true]),
        1.0,
    );
    if let RawOp::ApplyUnitary { steps, .. } = &mut p.operations[4] {
        steps[0].controls[0].when_one = false;
    }
    assert_eq!(
        export_qir_base(&verify(p.clone()).unwrap())
            .unwrap_err()
            .operation,
        Some(4)
    );
    if let RawOp::ApplyUnitary { steps, .. } = &mut p.operations[4] {
        steps[0].controls[0].when_one = true;
        steps[0].action = CircuitAction::Monomial {
            indices: vec![],
            permutation: vec![0],
            phases: vec![1],
        };
    }
    assert_eq!(
        export_openqasm3(&verify(p).unwrap()).unwrap_err().operation,
        Some(4)
    );
}

#[test]
fn export_has_independent_capacity_checks() {
    let mut ops = vec![RawOp::Init0 {
        output: TokenId(0),
        wire: WireId(0),
    }];
    for id in 0..4097 {
        ops.push(RawOp::Gate {
            gate: SingleGate::H,
            input: TokenId(id),
            output: TokenId(id + 1),
        });
    }
    ops.push(RawOp::Discard {
        input: TokenId(4097),
    });
    assert_eq!(
        export_openqasm3(&raw(ops, vec![])).unwrap_err().kind,
        InteropErrorKind::Limit
    );
    let mut ops = (0..13)
        .map(|id| RawOp::Init0 {
            output: TokenId(id),
            wire: WireId(id),
        })
        .collect::<Vec<_>>();
    ops.extend((0..13).map(|id| RawOp::Discard { input: TokenId(id) }));
    assert_eq!(
        export_qir_base(&raw(ops, vec![])).unwrap_err().kind,
        InteropErrorKind::Limit
    );
}
