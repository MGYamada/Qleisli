mod common;
use common::accept;
use qleisli::AcceptedProgram;
use qleisli::interop::{
    InteropErrorKind, MAX_OPENQASM_BYTES, export_openqasm3, export_qir_base, import_openqasm3,
};
use qleisli::ir::*;
use qleisli::sim::{SimulationLimits, run_closed};

const BELL: &str = include_str!("fixtures/interop/bell.qasm");
const GATES: &str = include_str!("fixtures/interop/gates.qasm");
fn source(body: &str) -> String {
    format!("OPENQASM 3.0; include \"stdgates.inc\"; {body}")
}
fn probability(program: &AcceptedProgram, bits: &[bool]) -> f64 {
    run_closed(program, SimulationLimits::default())
        .unwrap()
        .get(bits)
        .copied()
        .unwrap_or(0.0)
}
fn close(actual: f64, expected: f64) {
    assert!((actual - expected).abs() < 1e-12, "{actual} != {expected}");
}
fn raw(ops: Vec<RawOp>, outputs: Vec<ClassicalId>) -> AcceptedProgram {
    accept(RawProgram {
        quantum_inputs: vec![],
        classical_inputs: vec![],
        operations: ops,
        quantum_outputs: vec![],
        classical_outputs: outputs,
        declared_effect: Effect::Observe,
    })
    .unwrap()
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
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
        let before = run_closed(program, SimulationLimits::default()).unwrap();
        let after = run_closed(&roundtrip, SimulationLimits::default()).unwrap();
        for (bits, p) in &before {
            close(after.get(bits).copied().unwrap_or(0.0), *p);
        }
        for (bits, p) in &after {
            close(before.get(bits).copied().unwrap_or(0.0), *p);
        }
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
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

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
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

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
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

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
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
    let allowed = source(&format!("{prefix}{}measure q;", "h q;".repeat(8)));
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

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn valid_ir_can_still_be_unrepresentable_in_the_target() {
    let p = import_openqasm3(BELL).unwrap();
    let mut duplicated = p.raw().clone();
    duplicated
        .classical_outputs
        .push(duplicated.classical_outputs[0]);
    assert_eq!(
        export_openqasm3(&accept(duplicated).unwrap())
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
    let open = accept(RawProgram {
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

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn qli_frontend_and_qir_profile_contract() {
    let p = qleisli::frontend::compile::compile_project(std::path::Path::new(
        "tests/fixtures/frontend_v030/ordinary-type-cutover/current/interop/terminal",
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
        "@__quantum__qis__z__body",
        "@__quantum__qis__ccx__body",
        "ret i64 0",
    ] {
        assert!(qir.contains(expected), "{expected}");
    }
    assert!(!qir.contains("result_record_output(ptr null, ptr null)"));
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn export_tracks_reordered_owners_and_control_phase() {
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
    let text = export_openqasm3(&accept(p.clone()).unwrap()).unwrap();
    assert!(text.contains("cx q[0], q[1];"));
    assert!(text.contains("c[0] = measure q[1];"));
    close(
        probability(&import_openqasm3(&text).unwrap(), &[true, true]),
        1.0,
    );
    if let RawOp::ApplyUnitary { steps, .. } = &mut p.operations[4] {
        steps[0].controls[0].when_one = false;
    }
    let negative = export_openqasm3(&accept(p.clone()).unwrap()).unwrap();
    close(
        probability(&import_openqasm3(&negative).unwrap(), &[false, true]),
        1.0,
    );
    assert!(export_qir_base(&accept(p.clone()).unwrap()).is_ok());
    if let RawOp::ApplyUnitary { steps, .. } = &mut p.operations[4] {
        steps[0].controls[0].when_one = true;
        steps[0].action = CircuitAction::Monomial {
            indices: vec![],
            permutation: vec![0],
            phases: vec![1],
        };
    }
    assert!(
        export_openqasm3(&accept(p).unwrap())
            .unwrap()
            .contains("t q[0];")
    );
}

#[test]
#[ignore = "historical maximum-size export stress; native acceptance has independent work/time limits"]
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

// These probes consume literal exported gate words, then ask the native encoded
// contract checker for independently specified all-column equations. Native
// re-import is a separate output-validity check, not an export theorem.
fn ordinary_terminal(body: &str, definitions: &str, result: &str) -> AcceptedProgram {
    let text = format!(
        "use std::quantum::{{init0,h,split,join,unit,finish,phase_eighth}};
         use std::gate::t;
         use std::observe::measure_z;
         unitary fn wrapper(q:Q<Bit>)->Q<Bit>{{t(q)}}
         unitary fn unchanged(q:Q<Bit>)->Q<Bit>{{q}}
         {definitions}
         pub observe fn main()->{result}{{{body}}}"
    );
    qleisli::frontend::compile::compile_project(&common::SourceRoot::new(&text).0).unwrap()
}

fn has_contract(program: &AcceptedProgram) -> bool {
    program.raw().operations.iter().any(|op| match op {
        RawOp::ApplyUnitary { steps, .. } => steps
            .iter()
            .any(|step| matches!(step.action, CircuitAction::Contract { .. })),
        _ => false,
    })
}

fn literal_target(text: &str) -> (usize, Vec<CircuitStep>) {
    let mut width = None;
    let mut steps = vec![];
    for line in text.lines() {
        if let Some(rest) = line.strip_prefix("qubit[") {
            width = Some(rest.strip_suffix("] q;").unwrap().parse::<usize>().unwrap());
            continue;
        }
        if line.is_empty()
            || line == "OPENQASM 3.0;"
            || line == "include \"stdgates.inc\";"
            || line == "reset q;"
            || line.starts_with("bit[")
            || line.starts_with("c[")
        {
            continue;
        }
        let (gate, operands) = line.strip_suffix(';').unwrap().split_once(' ').unwrap();
        let axes: Vec<usize> = operands
            .split(", ")
            .map(|arg| {
                arg.strip_prefix("q[")
                    .unwrap()
                    .strip_suffix(']')
                    .unwrap()
                    .parse()
                    .unwrap()
            })
            .collect();
        let (controls, action) = match gate {
            "h" => {
                assert_eq!(axes.len(), 1);
                (vec![], CircuitAction::Hadamard { target: axes[0] })
            }
            "x" | "cx" | "ccx" => {
                let arity = match gate {
                    "x" => 1,
                    "cx" => 2,
                    _ => 3,
                };
                assert_eq!(axes.len(), arity);
                (
                    axes[..arity - 1]
                        .iter()
                        .map(|&index| BitControl {
                            index,
                            when_one: true,
                        })
                        .collect(),
                    CircuitAction::Monomial {
                        indices: vec![axes[arity - 1]],
                        permutation: vec![1, 0],
                        phases: vec![0, 0],
                    },
                )
            }
            "t" | "tdg" | "s" | "sdg" | "z" => {
                assert_eq!(axes.len(), 1);
                let exponent = match gate {
                    "t" => 1,
                    "tdg" => 7,
                    "s" => 2,
                    "sdg" => 6,
                    _ => 4,
                };
                (
                    vec![],
                    CircuitAction::Monomial {
                        indices: axes,
                        permutation: vec![0, 1],
                        phases: vec![0, exponent],
                    },
                )
            }
            _ => panic!("unexpected target gate in bounded exact probe: {line}"),
        };
        steps.push(CircuitStep { controls, action });
    }
    let width = width.expect("physical target declaration");
    assert!(width <= 3, "only small target experiments");
    (width, steps)
}

fn exact_target(text: &str, logical_phases: &[u8]) -> Result<(), qleisli::contract::ContractError> {
    use qleisli::contract::exact::{Exact, Matrix};
    let logical_dim = logical_phases.len();
    let meaning = Matrix::new(
        logical_dim,
        logical_dim,
        (0..logical_dim * logical_dim)
            .map(|i| {
                if i / logical_dim == i % logical_dim {
                    Exact::phase(i32::from(logical_phases[i / logical_dim]))
                } else {
                    Exact::zero()
                }
            })
            .collect(),
    )?;
    exact_target_matrix(text, meaning)
}

fn exact_target_matrix(
    text: &str,
    meaning: qleisli::contract::exact::Matrix,
) -> Result<(), qleisli::contract::ContractError> {
    use qleisli::contract::exact::{Budget, Exact, Matrix};
    use qleisli::contract::{
        BasisType, CheckedContract, Circuit, Contract, DEFAULT_EXACT_WORK, Encoding,
    };
    let (width, steps) = literal_target(text);
    let logical_dim = meaning.cols();
    assert!(logical_dim.is_power_of_two());
    assert_eq!(meaning.rows(), logical_dim);
    let logical = BasisType::Bits(logical_dim.trailing_zeros());
    let physical = BasisType::Bits(u32::try_from(width).unwrap());
    let mut budget = Budget::new(DEFAULT_EXACT_WORK);
    let embedding = Matrix::new(
        1 << width,
        logical_dim,
        (0..(1 << width) * logical_dim)
            .map(|i| {
                if i / logical_dim == i % logical_dim {
                    Exact::one()
                } else {
                    Exact::zero()
                }
            })
            .collect(),
    )?;
    let encoding = Encoding::new(logical, physical.clone(), embedding, &mut budget)?;
    let contract = Contract::new(encoding.clone(), encoding, meaning, &mut budget)?;
    CheckedContract::check(Circuit::new(physical, steps)?, contract, &mut budget).map(|_| ())
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn ordinary_contract_export_preserves_t_phase_and_nested_adjoint() {
    for (operation, exponent, literal, qis) in [
        ("t", 1, "t", "t__body"),
        ("wrapper", 1, "t", "t__body"),
        ("adjoint(wrapper)", 7, "tdg", "t__adj"),
        ("adjoint(adjoint(wrapper))", 1, "t", "t__body"),
    ] {
        let program = ordinary_terminal(&format!("measure_z({operation}(init0()))"), "", "Bit");
        assert!(
            has_contract(&program),
            "actual retained ordinary body: {operation}"
        );
        let text = export_openqasm3(&program).unwrap();
        assert_eq!(literal_target(&text).1.len(), 1, "{text}");
        assert!(text.contains(&format!("{literal} q[0];")), "{text}");
        assert!(
            export_qir_base(&program)
                .unwrap()
                .contains(&format!("call void @__quantum__qis__{qis}("))
        );
        import_openqasm3(&text).unwrap();
        exact_target(&text, &[0, exponent]).unwrap();
        assert!(exact_target(&text, &[0, 0]).is_err());
        assert!(
            exact_target(&text, &[exponent, exponent]).is_err(),
            "global phase is not T"
        );
        assert!(
            exact_target(&text, &[0, (8 - exponent) % 8]).is_err(),
            "inverse direction"
        );
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn ordinary_contract_export_keeps_reference_axes_and_reordered_owners() {
    let program = ordinary_terminal(
        "let a=init0();let b=init0();let q=join(b,a);let(b,a)=split(q);let b=wrapper(b);(measure_z(a),measure_z(b))",
        "",
        "(Bit,Bit)",
    );
    let text = export_openqasm3(&program).unwrap();
    assert!(has_contract(&program));
    assert!(text.contains("t q[1];"), "{text}");
    import_openqasm3(&text).unwrap();
    exact_target(&text, &[0, 0, 1, 1]).unwrap();
    assert!(exact_target(&text.replace("t q[1];", "t q[0];"), &[0, 0, 1, 1]).is_err());

    let program = ordinary_terminal(
        "let a=init0();let b=init0();let c=init0();let q=apply_contract(on_last,on_last,join(b,join(c,a)));let(b,q)=split(q);let(c,a)=split(q);(measure_z(a),(measure_z(b),measure_z(c)))",
        "unitary fn on_last(q:Q<(Bit,(Bit,Bit))>)->Q<(Bit,(Bit,Bit))>{let(a,q)=split(q);let(b,c)=split(q);join(a,join(b,wrapper(c)))}",
        "(Bit,(Bit,Bit))",
    );
    let text = export_openqasm3(&program).unwrap();
    assert!(has_contract(&program));
    assert!(text.contains("t q[0];"), "{text}");
    import_openqasm3(&text).unwrap();
    exact_target(&text, &[0, 1, 0, 1, 0, 1, 0, 1]).unwrap();
    assert!(
        exact_target(
            &text.replace("t q[0];", "t q[2];"),
            &[0, 1, 0, 1, 0, 1, 0, 1]
        )
        .is_err()
    );
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn controlled_ordinary_contract_export_returns_scratch_exactly() {
    for (arms, expected) in [
        ("0=>unchanged,1=>wrapper", [0, 0, 0, 1]),
        ("0=>wrapper,1=>unchanged", [0, 0, 1, 0]),
    ] {
        let program = ordinary_terminal(
            &format!("let(a,b)=qif(init0(),init0()){{{arms}}};(measure_z(a),measure_z(b))"),
            "",
            "(Bit,Bit)",
        );
        let text = export_openqasm3(&program).unwrap();
        assert!(has_contract(&program));
        assert_eq!(literal_target(&text).0, 3, "one clean synthesis qubit");
        import_openqasm3(&text).unwrap();
        exact_target(&text, &expected).unwrap();
        assert!(exact_target(&text.replace("t q[2];\n", ""), &expected).is_err());
        let uncompute = text
            .lines()
            .rev()
            .find(|line| line.starts_with("ccx "))
            .unwrap();
        let last = text.rfind(uncompute).unwrap();
        let mut missing_uncompute = text.clone();
        missing_uncompute.replace_range(last..last + uncompute.len() + 1, "");
        assert!(
            exact_target(&missing_uncompute, &expected).is_err(),
            "scratch must return to zero for every input"
        );
        if arms.starts_with("0=>wrapper") {
            assert!(
                exact_target(&text.replace("x q[0];\n", ""), &expected).is_err(),
                "control polarity"
            );
        }
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn adjacent_contract_phases_merge_before_assigning_workspace() {
    let program = ordinary_terminal(
        "let(a,b)=qif(init0(),init0()){0=>unchanged,1=>twice};(measure_z(a),measure_z(b))",
        "unitary fn twice(q:Q<Bit>)->Q<Bit>{wrapper(wrapper(q))}",
        "(Bit,Bit)",
    );
    assert!(has_contract(&program));
    let text = export_openqasm3(&program).unwrap();
    assert_eq!(
        literal_target(&text).0,
        2,
        "adjacent even phase needs no synthesis qubit: {text}"
    );
    import_openqasm3(&text).unwrap();
    exact_target(&text, &[0, 0, 0, 2]).unwrap();
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn uncontrolled_unit_contract_phase_is_not_erased_by_export() {
    let program = ordinary_terminal(
        "let u=apply_contract(scalar,scalar,unit(()));finish(u);()",
        "unitary fn scalar(u:Q<Unit>)->Q<Unit>{phase_eighth(u)}",
        "Unit",
    );
    assert!(has_contract(&program));
    use qleisli::contract::exact::{Budget, Exact, Matrix};
    use qleisli::contract::{BasisType, DEFAULT_EXACT_WORK};
    use qleisli::interchange::finite_leaf::{UnitaryBoundary, check_unitary};
    use qleisli::interchange::native::Proposal;
    use qleisli::interchange::{RootInterface, Version};
    let implementation = program
        .raw()
        .operations
        .iter()
        .find_map(|op| {
            let RawOp::ApplyUnitary { steps, .. } = op else {
                return None;
            };
            steps.iter().find_map(|step| match &step.action {
                CircuitAction::Contract { evidence, .. } => Some(evidence.implementation()),
                _ => None,
            })
        })
        .unwrap();
    let boundary = UnitaryBoundary::new(
        BasisType::Unit,
        implementation.quantum_inputs[0].clone(),
        QuantumPort {
            token: implementation.quantum_outputs[0],
            wires: vec![],
            shape: BasisShape { bits: 0 },
        },
    )
    .unwrap();
    let interface = RootInterface {
        input: BasisType::Unit,
        output: BasisType::Unit,
    };
    let proposal = Proposal::from_raw(implementation, Some(&interface), Version::V2, None).unwrap();
    for (phase, accepted) in [(1, true), (0, false)] {
        let matrix = Matrix::new(1, 1, vec![Exact::phase(phase)]).unwrap();
        assert_eq!(
            check_unitary(
                proposal.artifact(),
                &boundary,
                &matrix,
                &mut Budget::new(DEFAULT_EXACT_WORK)
            )
            .is_ok(),
            accepted
        );
    }
    for result in [export_openqasm3(&program), export_qir_base(&program)] {
        let error = result.unwrap_err();
        assert_eq!(error.kind, InteropErrorKind::Unsupported);
        assert!(
            error.message.contains("uncontrolled scalar phase"),
            "{error}"
        );
        assert!(error.operation.is_some());
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn ordinary_contract_adjoint_reverses_noncommuting_body_order() {
    use qleisli::contract::exact::{Exact, Matrix};
    let program = ordinary_terminal(
        "measure_z(adjoint(mixed)(init0()))",
        "unitary fn mixed(q:Q<Bit>)->Q<Bit>{h(wrapper(q))}",
        "Bit",
    );
    assert!(has_contract(&program));
    let text = export_openqasm3(&program).unwrap();
    assert!(text.contains("h q[0];\ntdg q[0];"), "{text}");
    import_openqasm3(&text).unwrap();
    // (H T)^dagger = T^dagger H, including every complex coefficient.
    let scale = Exact::inv_sqrt2();
    let phase = Exact::phase(7).mul(scale).unwrap();
    let expected = Matrix::new(2, 2, vec![scale, scale, phase, phase.neg().unwrap()]).unwrap();
    exact_target_matrix(&text, expected.clone()).unwrap();
    let wrong_order = text.replace("h q[0];\ntdg q[0];", "tdg q[0];\nh q[0];");
    assert!(exact_target_matrix(&wrong_order, expected).is_err());
}
