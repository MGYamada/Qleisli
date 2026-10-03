mod common;
use common::accept;
use qleisli::contract::BasisType;
use qleisli::contract::exact::{Exact, Matrix};
use qleisli::interchange::hierarchical::Kernel;
use qleisli::interchange::{self, RootInterface, Version, finite_matrix};
use qleisli::ir::*;

fn quoted(text: &str) -> String {
    // Test payloads are ASCII JSON. Escape the outer string independently.
    format!(
        "\"{}\"",
        text.replace('\\', "\\\\")
            .replace('"', "\\\"")
            .replace('\n', "\\n")
    )
}

fn h_matrix(negative: bool) -> Matrix {
    let h = Exact::inv_sqrt2();
    let entries = vec![h, h, h, h.neg().unwrap()];
    Matrix::new(
        2,
        2,
        entries
            .into_iter()
            .map(|x| if negative { x.neg().unwrap() } else { x })
            .collect(),
    )
    .unwrap()
}

fn finite_program() -> Vec<u8> {
    finite_program_at(0, 7)
}

fn finite_program_at(owner: u32, wire: u32) -> Vec<u8> {
    let raw = RawProgram {
        quantum_inputs: vec![QuantumPort {
            token: TokenId(owner),
            wires: vec![WireId(wire)],
            shape: BasisShape { bits: 1 },
        }],
        classical_inputs: vec![],
        operations: vec![RawOp::Gate {
            gate: SingleGate::H,
            input: TokenId(owner),
            output: TokenId(owner + 1),
        }],
        quantum_outputs: vec![TokenId(owner + 1)],
        classical_outputs: vec![],
        declared_effect: Effect::Unitary,
    };
    interchange::export(
        &accept(raw).unwrap(),
        Some(&RootInterface {
            input: BasisType::Bit,
            output: BasisType::Bit,
        }),
        Version::V2,
    )
    .unwrap()
}

fn side(owner: u32, controlled: bool) -> String {
    let target = format!(r#"{{"owner":{owner},"basis":[{{"tag":"bit"}}],"axes":[7]}}"#);
    let ports = if controlled {
        format!(r#"{{"owner":99,"basis":[{{"tag":"bit"}}],"axes":[11]}},{target}"#)
    } else {
        target
    };
    format!(r#"{{"quantum":[{ports}],"classical":[]}}"#)
}

fn family(count: u32, logical_count: u32, negative: bool, controlled: bool) -> Vec<u8> {
    let program = quoted(std::str::from_utf8(&finite_program()).unwrap());
    let matrix =
        quoted(std::str::from_utf8(&finite_matrix::encode(&h_matrix(negative)).unwrap()).unwrap());
    let n = if controlled { 5 } else { 4 };
    let rev = |i| n - 1 - i;
    let permutation = r#"{"owners":[0],"axes":[0],"classical":[]}"#;
    let mut d = vec![
        format!(r#"{{"tag":"leaf","program":{program}}}"#),
        format!(r#"{{"tag":"rewire","permutation":{permutation}}}"#),
        r#"{"tag":"sequence","children":[0,1]}"#.to_string(),
        format!(r#"{{"tag":"repeat","count":{count},"definition":2}}"#),
    ];
    let mut m = vec![
        format!(r#"{{"tag":"finite","description":{matrix}}}"#),
        format!(r#"{{"tag":"rewire","permutation":{permutation}}}"#),
        format!(r#"{{"tag":"sequence","children":[{},{}]}}"#, rev(0), rev(1)),
        format!(
            r#"{{"tag":"power","child":{},"count":{logical_count}}}"#,
            rev(2)
        ),
    ];
    if controlled {
        d.push(r#"{"tag":"control","definition":3,"polarity":true}"#.into());
        m.push(format!(
            r#"{{"tag":"control","child":{},"polarity":true}}"#,
            rev(3)
        ));
    }
    let rules = ["finite", "rewire", "sequence", "repeat", "control"];
    let premises = ["[]", "[]", "[0,1]", "[2]", "[3]"];
    let mut definitions = vec![];
    let mut meanings = vec![];
    let mut encodings = vec![];
    let mut proofs = vec![];
    for i in 0..n {
        let a = side(if i == 1 { 1 } else { 0 }, i == 4);
        let b = side(if i == 0 { 1 } else { 0 }, i == 4);
        let header = format!(r#"{{"inputs":{a},"outputs":{b}}}"#);
        definitions.push(format!(
            r#"{{"interface":{header},"effect":"unitary","body":{}}}"#,
            d[i]
        ));
        meanings.push(format!(r#"{{"interface":{header},"body":{}}}"#, m[i]));
        for s in [&a, &b] {
            encodings.push(format!(
                r#"{{"logical":{s},"physical":{s},"body":{{"tag":"identity"}}}}"#
            ));
        }
        proofs.push(format!(r#"{{"kind":"equation","rule":{{"tag":"{}"}},"premises":{},"implementation":{i},"meaning":{},"input_encoding":{},"output_encoding":{},"witness":{{"template_version":1,"parameters":[],"references":[]}}}}"#,rules[i],premises[i],rev(i),2*i,2*i+1));
    }
    meanings.reverse();
    format!(r#"{{"format":"qleisli.hierarchical-ir","version":1,"profile":"qpe-dyadic8-v1","definitions":[{}],"meanings":[{}],"encodings":[{}],"proofs":[{}],"entry":{{"implementation":{},"proof":{}}}}}"#,definitions.join(","),meanings.join(","),encodings.join(","),proofs.join(","),n-1,n-1).into_bytes()
}

fn native() -> Kernel {
    let path = std::env::var_os("QLEISLI_HIERARCHY_KERNEL")
        .expect("set QLEISLI_HIERARCHY_KERNEL to the built audited executable");
    assert!(std::path::Path::new(&path).is_file());
    Kernel::new(path)
}

#[test]
#[ignore = "requires separately built and audited native Lean runtime"]
fn native_finite_pair_and_nested_tuple_boundaries_reconstruct_without_flattening() {
    use qleisli::interchange::hierarchical::execution::ExecutionLimits;
    let kernel = native();
    let bit = r#"{"tag":"bit"}"#;
    let unit = r#"{"tag":"unit"}"#;
    let pair = r#"{"tag":"tuple","arity":2}"#;
    let tuple = r#"{"tag":"tuple","arity":3}"#;
    for (ty, atoms) in [
        (
            BasisType::pair(BasisType::Bit, BasisType::Bit),
            format!("{pair},{bit},{bit}"),
        ),
        (
            BasisType::pair(BasisType::Unit, BasisType::Bit),
            format!("{pair},{unit},{bit}"),
        ),
        (
            BasisType::Tuple(vec![
                BasisType::Bit,
                BasisType::pair(BasisType::Unit, BasisType::Bit),
                BasisType::Bit,
            ]),
            format!("{tuple},{bit},{pair},{unit},{bit},{bit}"),
        ),
        (
            BasisType::pair(
                BasisType::Bit,
                BasisType::pair(BasisType::Unit, BasisType::Bit),
            ),
            format!("{pair},{bit},{pair},{unit},{bit}"),
        ),
    ] {
        let bits = ty.bits().unwrap();
        let axes = [11, 3, 7][..bits].to_vec();
        let port = QuantumPort {
            token: TokenId(5),
            wires: axes.iter().copied().map(WireId).collect(),
            shape: BasisShape { bits: bits as u8 },
        };
        let raw = RawProgram {
            quantum_inputs: vec![port],
            classical_inputs: vec![],
            operations: vec![],
            quantum_outputs: vec![TokenId(5)],
            classical_outputs: vec![],
            declared_effect: Effect::Unitary,
        };
        let dim = 1 << bits;
        let identity = Matrix::new(
            dim,
            dim,
            (0..dim * dim)
                .map(|i| {
                    if i / dim == i % dim {
                        Exact::one()
                    } else {
                        Exact::zero()
                    }
                })
                .collect(),
        )
        .unwrap();
        let description =
            quoted(std::str::from_utf8(&finite_matrix::encode(&identity).unwrap()).unwrap());
        let meaning = format!(r#"{{"tag":"finite","description":{description}}}"#);
        let axes_json = axes
            .iter()
            .map(u32::to_string)
            .collect::<Vec<_>>()
            .join(",");
        let side = format!(
            r#"{{"quantum":[{{"owner":5,"basis":[{atoms}],"axes":[{axes_json}]}}],"classical":[]}}"#
        );
        let request = request_from_meanings(vec![(side.clone(), side.clone(), meaning.clone())], 0);
        for version in [Version::V1, Version::V2] {
            let bytes = interchange::export(
                &accept(raw.clone()).unwrap(),
                Some(&RootInterface {
                    input: ty.clone(),
                    output: ty.clone(),
                }),
                version,
            )
            .unwrap();
            let program = quoted(std::str::from_utf8(&bytes).unwrap());
            let artifact = assemble(vec![(
                side.clone(),
                side.clone(),
                format!(r#"{{"tag":"leaf","program":{program}}}"#),
                meaning.clone(),
                "finite",
                "[]",
            )]);
            let native = kernel.inspect_native(&artifact).unwrap();
            assert_eq!(native.payload(), artifact);
            let checked = kernel.check_against(&artifact, &request).unwrap();
            let leaf = checked.reconstruction().leaves()[0].1.leaf();
            assert_eq!(leaf.boundary().signature(), &ty);
            assert_eq!(leaf.payload(), bytes);
            assert_eq!(
                leaf.boundary().input().wires,
                axes.iter().copied().map(WireId).collect::<Vec<_>>()
            );
            let input = (0..dim * 2)
                .map(|i| [i as f64 / 17.0, (2 * i + 1) as f64 / 23.0])
                .collect::<Vec<_>>();
            let result = checked
                .execute(
                    &input,
                    2,
                    ExecutionLimits {
                        max_amplitudes: 64,
                        max_steps: 1000,
                    },
                )
                .unwrap();
            assert_eq!(result.amplitudes, input);
            assert_eq!(result.reference_dimension, 2);
            if bits > 1 {
                let reversed = axes
                    .iter()
                    .rev()
                    .map(u32::to_string)
                    .collect::<Vec<_>>()
                    .join(",");
                let wrong = String::from_utf8(artifact.clone())
                    .unwrap()
                    .replace(&format!("[{axes_json}]"), &format!("[{reversed}]"));
                let renamed = kernel.inspect(wrong.as_bytes()).unwrap();
                assert_eq!(
                    renamed.leaves()[0].1.leaf().boundary().input().wires,
                    axes.iter().rev().copied().map(WireId).collect::<Vec<_>>()
                );
            }
            if atoms.contains(unit) {
                let swapped = atoms.replace(
                    &format!("{pair},{unit},{bit}"),
                    &format!("{pair},{bit},{unit}"),
                );
                let wrong_type = String::from_utf8(artifact.clone()).unwrap().replace(
                    &format!("\"basis\":[{atoms}]"),
                    &format!("\"basis\":[{swapped}]"),
                );
                assert!(kernel.inspect(wrong_type.as_bytes()).is_err());
            }
        }
    }
}

#[test]
#[ignore = "VM-22 optional comparison requires the separately built Lean runtime"]
fn vm22_frozen_hierarchy_requests_recheck_finite_premises_and_cycles() {
    let k = native();
    let frozen = |name: &str, bytes: Vec<u8>| {
        let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/verification_v022/hierarchy");
        if let Some(capture) = std::env::var_os("QLEISLI_VM22_HIERARCHY_CAPTURE") {
            let capture = std::path::PathBuf::from(capture);
            std::fs::create_dir_all(&capture).unwrap();
            std::fs::write(capture.join(name), &bytes).unwrap();
        } else {
            assert_eq!(std::fs::read(directory.join(name)).unwrap(), bytes);
        }
        bytes
    };
    let a = frozen("h.qirh", family(1, 1, false, false));
    let r = frozen("h.request.json", power_request(1, false, false, false));
    let checked = k.check_against(&a, &r).unwrap();
    assert_eq!(checked.request(), r);
    assert_eq!(checked.reconstruction().leaves().len(), 1);
    let wrong_request = frozen(
        "h.wrong-phase.request.json",
        power_request(1, true, false, false),
    );
    assert_eq!(
        k.check_against(&a, &wrong_request).unwrap_err().code,
        "contract"
    );
    let zero = frozen("zero-repeat.wrong-leaf.qirh", family(0, 0, true, false));
    let identity = frozen(
        "zero-repeat.request.json",
        power_request(0, false, false, false),
    );
    assert_eq!(
        k.check_against(&zero, &identity).unwrap_err().code,
        "contract"
    );
    let cycle =
        String::from_utf8(a)
            .unwrap()
            .replacen("\"children\":[0,1]", "\"children\":[0,2]", 1);
    let cycle = frozen("cycle.qirh", cycle.into_bytes());
    assert_eq!(k.check_against(&cycle, &r).unwrap_err().code, "invalid_ir");
}

#[test]
fn strict_json_rejects_before_starting_an_executable() {
    let k = Kernel::new("/nonexistent/qleisli-kernel");
    let good = String::from_utf8(family(3, 3, false, false)).unwrap();
    let malformed = [
        good.replacen("\"version\":1", "\"version\":1,\"version\":1", 1),
        good.replacen("\"version\":1", "\"version\":2", 1),
        good.replacen("\"effect\":\"unitary\"", "\"effect\":\"unknown\"", 1),
        good.replacen("\"owner\":0", "\"owner\":0,\"checked\":true", 1),
        good.replacen("\"polarity\":true", "\"polarity\":1", 1) + "null",
        good.replacen("\"tag\":\"repeat\"", "\"tag\":\"eval\"", 1),
    ];
    for bad in malformed {
        assert_eq!(k.inspect(bad.as_bytes()).unwrap_err().code, "format");
    }
    let big = good.replacen("\"owner\":0", "\"owner\":4294967296", 1);
    assert_eq!(k.inspect(big.as_bytes()).unwrap_err().code, "limit");
}

#[test]
fn schedule_producer_rejects_cycles_and_cross_table_aliases() {
    let k = Kernel::new("/nonexistent/qleisli-kernel");
    let good = String::from_utf8(family(3, 3, false, false)).unwrap();
    for bad in [
        good.replacen("\"children\":[0,1]", "\"children\":[0,2]", 1),
        good.replacen("\"definition\":2", "\"definition\":4", 1),
        good.replacen("\"input_encoding\":0", "\"input_encoding\":8", 1),
    ] {
        assert_eq!(k.inspect(bad.as_bytes()).unwrap_err().code, "invalid_ir");
    }
}

#[test]
fn external_schema_ids_cannot_enable_registry_entries() {
    let good = String::from_utf8(family(3, 3, false, false)).unwrap();
    let bad = good.replacen(
        "\"rule\":{\"tag\":\"finite\"}",
        "\"rule\":{\"tag\":\"schema\",\"id\":\"controlled-power/1\"}",
        1,
    );
    assert_eq!(
        Kernel::new("/nonexistent/qleisli-kernel")
            .inspect(bad.as_bytes())
            .unwrap_err()
            .code,
        "contract"
    );
}

#[test]
#[ignore = "requires separately built and audited native Lean runtime"]
fn native_shared_powers_reconstruct_one_bound_leaf_without_expansion() {
    let k = native();
    let payload = family(3, 3, false, false);
    let checked = k.inspect_native(&payload).unwrap();
    assert_eq!(checked.payload(), payload);
    assert!(checked.exact_work() > 0);
    assert!(checked.request().is_none());
    assert!(checked.candidate().is_none());
    assert_eq!(
        k.inspect_native(&family(0, 0, true, false))
            .unwrap_err()
            .code,
        "contract"
    );
    let mut costs = vec![];
    for count in [0, 1, 3, 4096] {
        let bytes = family(count, count, false, true);
        let result = k.inspect(&bytes).unwrap();
        assert_eq!(result.payload(), bytes);
        assert_eq!(result.leaves().len(), 1);
        assert_eq!(result.leaves()[0].0, 0);
        assert_eq!(result.leaves()[0].1.leaf().meaning(), &h_matrix(false));
        assert_eq!(result.leaves()[0].1.leaf().payload(), finite_program());
        costs.push((result.structural_work(), result.exact_work()));
    }
    assert!(costs.windows(2).all(|w| w[0] == w[1]));
    println!("shared power costs: {costs:?}");
}

#[test]
#[ignore = "requires separately built and audited native Lean runtime"]
fn native_phase_fault_remains_an_obligation_under_zero_repeat() {
    let k = native();
    for count in [0, 3, 4096] {
        let error = k.inspect(&family(count, count, true, true)).unwrap_err();
        assert_eq!(error.code, "contract");
        assert!(error.message.contains("Lean artifact inspection"));
    }
}

#[test]
#[ignore = "requires separately built and audited native Lean runtime"]
fn native_actual_counts_premises_and_encodings_are_checked() {
    let k = native();
    assert_eq!(
        k.inspect(&family(3, 4, false, true)).unwrap_err().code,
        "contract"
    );
    let good = String::from_utf8(family(3, 3, false, true)).unwrap();
    for bad in [
        good.replacen("\"premises\":[2]", "\"premises\":[]", 1),
        good.replacen("\"input_encoding\":6", "\"input_encoding\":1", 1),
        good.replacen("\"polarity\":true", "\"polarity\":false", 1),
    ] {
        assert!(matches!(
            k.inspect(bad.as_bytes()).unwrap_err().code,
            "contract" | "invalid_ir"
        ));
    }
}

#[test]
#[ignore = "requires separately built and audited native Lean runtime"]
fn native_leaf_type_and_owner_are_bound_to_the_embedded_program() {
    let k = native();
    let good = String::from_utf8(family(3, 3, false, false)).unwrap();
    let wrong_owner = good.replace("\"owner\":0", "\"owner\":8");
    assert_eq!(
        k.inspect(wrong_owner.as_bytes()).unwrap_err().code,
        "contract"
    );
    let wrong_type = good.replace(
        "\"basis\":[{\"tag\":\"bit\"}]",
        "\"basis\":[{\"tag\":\"bits\",\"width\":1}]",
    );
    assert!(matches!(
        k.inspect(wrong_type.as_bytes()).unwrap_err().code,
        "contract" | "invalid_ir"
    ));
}

// This fixture lists tables directly in the same order. The shared-power
// fixture above independently reverses the meaning table.
fn assemble(nodes: Vec<(String, String, String, String, &str, &str)>) -> Vec<u8> {
    let mut ds = vec![];
    let mut ms = vec![];
    let mut es = vec![];
    let mut ps = vec![];
    for (i, (a, b, d, m, rule, premises)) in nodes.iter().enumerate() {
        let header = format!(r#"{{"inputs":{a},"outputs":{b}}}"#);
        ds.push(format!(
            r#"{{"interface":{header},"effect":"unitary","body":{d}}}"#
        ));
        ms.push(format!(r#"{{"interface":{header},"body":{m}}}"#));
        for s in [a, b] {
            es.push(format!(
                r#"{{"logical":{s},"physical":{s},"body":{{"tag":"identity"}}}}"#
            ));
        }
        ps.push(format!(r#"{{"kind":"equation","rule":{{"tag":"{rule}"}},"premises":{premises},"implementation":{i},"meaning":{i},"input_encoding":{},"output_encoding":{},"witness":{{"template_version":1,"parameters":[],"references":[]}}}}"#,2*i,2*i+1));
    }
    let root = nodes.len() - 1;
    format!(r#"{{"format":"qleisli.hierarchical-ir","version":1,"profile":"qpe-dyadic8-v1","definitions":[{}],"meanings":[{}],"encodings":[{}],"proofs":[{}],"entry":{{"implementation":{root},"proof":{root}}}}}"#,ds.join(","),ms.join(","),es.join(","),ps.join(",")).into_bytes()
}

fn combined_side(left: u32, right: u32) -> String {
    format!(
        r#"{{"quantum":[{{"owner":{left},"basis":[{{"tag":"bit"}}],"axes":[7]}},{{"owner":{right},"basis":[{{"tag":"bit"}}],"axes":[17]}}],"classical":[]}}"#
    )
}

#[test]
#[ignore = "requires separately built and audited native Lean runtime"]
fn native_disjoint_tensor_reconstructs_both_leaves_in_one_budget() {
    let k = native();
    for negative in [false, true] {
        let mut nodes = vec![];
        for i in 0..2 {
            let (owner, wire) = if i == 0 { (0, 7) } else { (10, 17) };
            let a = side(owner, false).replace("[7]", &format!("[{wire}]"));
            let b = side(owner + 1, false).replace("[7]", &format!("[{wire}]"));
            let program = quoted(std::str::from_utf8(&finite_program_at(owner, wire)).unwrap());
            let matrix = quoted(
                std::str::from_utf8(&finite_matrix::encode(&h_matrix(negative && i == 1)).unwrap())
                    .unwrap(),
            );
            nodes.push((
                a,
                b,
                format!(r#"{{"tag":"leaf","program":{program}}}"#),
                format!(r#"{{"tag":"finite","description":{matrix}}}"#),
                "finite",
                "[]",
            ));
        }
        let body = r#"{"tag":"tensor","left":0,"right":1}"#.to_string();
        nodes.push((
            combined_side(0, 10),
            combined_side(1, 11),
            body.clone(),
            body,
            "tensor",
            "[0,1]",
        ));
        let result = k.inspect(&assemble(nodes));
        if negative {
            assert_eq!(result.unwrap_err().code, "contract");
        } else {
            let result = result.unwrap();
            assert_eq!(result.leaves().len(), 2);
            assert_eq!(
                result.exact_work(),
                result.leaves().iter().map(|(_, l)| l.exact_work()).sum()
            );
            assert!(result.exact_work() > 0);
        }
    }
}

#[test]
#[ignore = "requires separately built and audited native Lean runtime"]
fn native_phase_and_structural_inverse_need_no_dense_matrix_leaf() {
    let k = native();
    let a = side(0, false);
    let phase = assemble(vec![(
        a.clone(),
        a,
        r#"{"tag":"dyadic_phase","target":0,"j":1,"k":8}"#.into(),
        r#"{"tag":"phase","j":1,"k":8}"#.into(),
        "phase",
        "[]",
    )]);
    let result = k.inspect(&phase).unwrap();
    assert!(result.leaves().is_empty());
    assert_eq!(result.exact_work(), 0);
    let pair=r#"{"quantum":[{"owner":0,"basis":[{"tag":"tuple","arity":2},{"tag":"bit"},{"tag":"bit"}],"axes":[7,17]}],"classical":[]}"#.to_string();
    let split = combined_side(1, 2);
    let body = r#"{"tag":"structural","operation":{"tag":"split_tuple"}}"#.to_string();
    let artifact = assemble(vec![
        (
            pair.clone(),
            split.clone(),
            body.clone(),
            body,
            "structural",
            "[]",
        ),
        (
            split,
            pair,
            r#"{"tag":"inverse","definition":0}"#.into(),
            r#"{"tag":"inverse","child":0}"#.into(),
            "inverse",
            "[0]",
        ),
    ]);
    let result = k.inspect(&artifact).unwrap();
    assert!(result.leaves().is_empty());
    assert_eq!(result.exact_work(), 0);
}

// Independent request construction: no field is copied from the artifact.
fn request_from_meanings(meanings: Vec<(String, String, String)>, entry: usize) -> Vec<u8> {
    let (a, b, _) = &meanings[entry];
    let header = format!(r#"{{"inputs":{a},"outputs":{b}}}"#);
    let nodes = meanings
        .iter()
        .map(|(a, b, body)| {
            format!(r#"{{"interface":{{"inputs":{a},"outputs":{b}}},"body":{body}}}"#)
        })
        .collect::<Vec<_>>();
    format!(r#"{{"format":"qleisli.hierarchy-request","version":1,"profile":"qpe-dyadic8-v1","kind":"equation","effect":"unitary","interface":{header},"meanings":[{}],"entry":{entry}}}"#,nodes.join(",")).into_bytes()
}

fn power_request(count: u32, negative: bool, controlled: bool, pretty: bool) -> Vec<u8> {
    let mut matrix =
        String::from_utf8(finite_matrix::encode(&h_matrix(negative)).unwrap()).unwrap();
    if pretty {
        matrix = matrix.replace(',', ",\n ");
    }
    let matrix = quoted(&matrix);
    let a = side(0, false);
    let b = side(1, false);
    let mut nodes = vec![
        (
            a.clone(),
            b.clone(),
            format!(r#"{{"tag":"finite","description":{matrix}}}"#),
        ),
        (
            b,
            a.clone(),
            r#"{"tag":"rewire","permutation":{"owners":[0],"axes":[0],"classical":[]}}"#.into(),
        ),
        (
            a.clone(),
            a.clone(),
            r#"{"tag":"sequence","children":[0,1]}"#.into(),
        ),
        (
            a.clone(),
            a,
            format!(r#"{{"tag":"power","child":2,"count":{count}}}"#),
        ),
    ];
    if controlled {
        nodes.push((
            side(0, true),
            side(0, true),
            r#"{"tag":"control","child":3,"polarity":true}"#.into(),
        ));
    }
    let entry = nodes.len() - 1;
    request_from_meanings(nodes, entry)
}

#[test]
fn independent_request_transport_rejects_flags_and_invalid_references() {
    let k = Kernel::new("/nonexistent/qleisli-kernel");
    let a = family(3, 3, false, true);
    let request = String::from_utf8(power_request(3, false, true, false)).unwrap();
    for bad in [
        request.replacen("\"version\":1", "\"version\":1,\"checked\":true", 1),
        request.replacen("\"kind\":\"equation\"", "\"kind\":\"unchecked\"", 1),
        request.replacen("\"entry\":4", "\"entry\":4,\"entry\":4", 1),
    ] {
        assert_eq!(
            k.check_against(&a, bad.as_bytes()).unwrap_err().code,
            "format"
        );
    }
    for bad in [
        request.replacen("\"entry\":4", "\"entry\":5", 1),
        request.replacen("\"child\":2", "\"child\":99", 1),
        request.replacen("\"child\":3", "\"child\":4", 1),
    ] {
        assert_eq!(
            k.check_against(&a, bad.as_bytes()).unwrap_err().code,
            "invalid_ir"
        );
    }
}

#[test]
#[ignore = "requires separately built and audited native Lean runtime"]
fn native_request_binds_reindexed_shared_powers_and_exact_meaning_bytes() {
    let k = native();
    let mut costs = vec![];
    for count in [0, 1, 3, 4096] {
        let a = family(count, count, false, true);
        let r = power_request(count, false, true, true);
        let native = k.check_against_native(&a, &r).unwrap();
        assert_eq!(native.payload(), a);
        assert_eq!(native.request(), Some(r.as_slice()));
        let result = k.check_against(&a, &r).unwrap();
        assert_eq!(result.request(), r);
        assert_eq!(result.reconstruction().payload(), a);
        assert_eq!(result.reconstruction().leaves().len(), 1);
        costs.push((
            result.reconstruction().structural_work(),
            result.reconstruction().exact_work(),
            result.reconstruction().native_exact_work(),
        ));
        assert_eq!(
            native.exact_work(),
            result.reconstruction().native_exact_work()
        );
        assert_eq!(
            k.check_against(&a, &power_request(count, true, true, false))
                .unwrap_err()
                .code,
            "contract"
        );
        assert_eq!(
            k.check_against(&family(count, count, true, true), &r)
                .unwrap_err()
                .code,
            "contract"
        );
    }
    assert!(costs.windows(2).all(|w| w[0] == w[1]));
    // Compare with an independently invoked finite leaf, not the retired Rust
    // verifier's hard-coded 67-unit counter. Repeated DAG uses charge it once.
    use qleisli::contract::{DEFAULT_EXACT_WORK, exact::Budget};
    use qleisli::interchange::finite_leaf::{UnitaryBoundary, check_serialized_unitary};
    let port = |token| QuantumPort {
        token: TokenId(token),
        wires: vec![WireId(7)],
        shape: BasisShape::BIT,
    };
    let boundary = UnitaryBoundary::new(BasisType::Bit, port(0), port(1)).unwrap();
    let mut budget = Budget::new(DEFAULT_EXACT_WORK);
    let leaf = check_serialized_unitary(
        &finite_program(),
        &boundary,
        &finite_matrix::encode(&h_matrix(false)).unwrap(),
        &mut budget,
    )
    .unwrap();
    assert_eq!(costs[0].1, DEFAULT_EXACT_WORK - budget.remaining());
    assert_eq!(costs[0].1, leaf.exact_work());
    assert!(costs[0].2 > 0);
    println!("independent request shared-power costs: {costs:?}");
}

#[test]
#[ignore = "requires separately built and audited native Lean runtime"]
fn native_request_detects_coordinated_body_changes_and_wrong_headers() {
    let k = native();
    let a = family(3, 3, false, true);
    let r = power_request(3, false, true, false);
    let changed = family(4, 4, false, true);
    k.inspect(&changed).unwrap();
    assert_eq!(k.check_against(&changed, &r).unwrap_err().code, "contract");
    let text = String::from_utf8(r).unwrap();
    for bad in [
        text.replacen("\"kind\":\"equation\"", "\"kind\":\"instrument\"", 1),
        text.replacen("\"effect\":\"unitary\"", "\"effect\":\"iso\"", 1),
        text.replacen("\"owner\":99", "\"owner\":98", 1),
        text.replacen("\"axes\":[11]", "\"axes\":[12]", 1),
        text.replacen("\"tag\":\"bit\"", "\"tag\":\"bits\",\"width\":1", 1),
        text.replacen("\"polarity\":true", "\"polarity\":false", 1),
    ] {
        assert_eq!(
            k.check_against(&a, bad.as_bytes()).unwrap_err().code,
            "contract"
        );
    }
    let s = side(0, false);
    let req = request_from_meanings(
        vec![(
            s.clone(),
            s.clone(),
            r#"{"tag":"phase","j":1,"k":8}"#.into(),
        )],
        0,
    );
    let phase = assemble(vec![(
        s.clone(),
        s,
        r#"{"tag":"dyadic_phase","target":0,"j":2,"k":8}"#.into(),
        r#"{"tag":"phase","j":2,"k":8}"#.into(),
        "phase",
        "[]",
    )]);
    k.inspect(&phase).unwrap();
    assert_eq!(k.check_against(&phase, &req).unwrap_err().code, "contract");
}

#[test]
#[ignore = "requires separately built and audited native Lean runtime"]
fn native_request_permits_different_sharing_in_both_directions() {
    let k = native();
    let s = side(0, false);
    let d = r#"{"tag":"dyadic_phase","target":0,"j":1,"k":8}"#;
    let m = r#"{"tag":"phase","j":1,"k":8}"#;
    let shared = assemble(vec![
        (s.clone(), s.clone(), d.into(), m.into(), "phase", "[]"),
        (
            s.clone(),
            s.clone(),
            r#"{"tag":"sequence","children":[0,0]}"#.into(),
            r#"{"tag":"sequence","children":[0,0]}"#.into(),
            "sequence",
            "[0,0]",
        ),
    ]);
    let duplicated = assemble(vec![
        (s.clone(), s.clone(), d.into(), m.into(), "phase", "[]"),
        (s.clone(), s.clone(), d.into(), m.into(), "phase", "[]"),
        (
            s.clone(),
            s.clone(),
            r#"{"tag":"sequence","children":[0,1]}"#.into(),
            r#"{"tag":"sequence","children":[0,1]}"#.into(),
            "sequence",
            "[0,1]",
        ),
    ]);
    let req_shared = request_from_meanings(
        vec![
            (s.clone(), s.clone(), m.into()),
            (
                s.clone(),
                s.clone(),
                r#"{"tag":"sequence","children":[0,0]}"#.into(),
            ),
        ],
        1,
    );
    let req_duplicated = request_from_meanings(
        vec![
            (s.clone(), s.clone(), m.into()),
            (s.clone(), s.clone(), m.into()),
            (
                s.clone(),
                s.clone(),
                r#"{"tag":"sequence","children":[0,1]}"#.into(),
            ),
        ],
        2,
    );
    for (a, r) in [(&shared, &req_duplicated), (&duplicated, &req_shared)] {
        let result = k.check_against(a, r).unwrap();
        assert_eq!(result.reconstruction().exact_work(), 0);
    }
    let unused = request_from_meanings(
        vec![
            (s.clone(), s.clone(), m.into()),
            (s.clone(), s.clone(), m.into()),
        ],
        0,
    );
    let leaf = assemble(vec![(s.clone(), s, d.into(), m.into(), "phase", "[]")]);
    assert_eq!(
        k.check_against(&leaf, &unused).unwrap_err().code,
        "contract"
    );
}

// Independently authored initialization/readout request around an exact H
// circuit. The optional control is an arbitrary retained quantum input.
fn instrument_inputs(controlled: bool) -> String {
    let quantum = if controlled {
        r#"{"owner":99,"basis":[{"tag":"bit"}],"axes":[11]}"#
    } else {
        ""
    };
    format!(r#"{{"quantum":[{quantum}],"classical":[]}}"#)
}

fn instrument_outputs(controlled: bool) -> String {
    instrument_inputs(controlled).replace(
        r#""classical":[]"#,
        r#""classical":[{"value":900,"basis":[{"tag":"bits","width":1}]}]"#,
    )
}

fn instrument_payload(count: u32, negative: bool, controlled: bool) -> Vec<u8> {
    let before = instrument_inputs(controlled);
    let prepared = side(0, controlled);
    let observed = instrument_inputs(controlled).replace(
        r#""classical":[]"#,
        r#""classical":[{"value":20,"basis":[{"tag":"bit"}]}]"#,
    );
    let final_side = instrument_outputs(controlled);
    let circuit = String::from_utf8(family(count, count, negative, controlled)).unwrap();
    format!(r#"{{"format":"qleisli.instrument-ir","version":1,"profile":"initialize-unitary-readout-v1","preparation":{{"initializations":[{{"interface":{{"inputs":{before},"outputs":{prepared}}},"effect":"iso","body":{{"tag":"init0","output":0}}}}],"outputs":{prepared}}},"circuit":{circuit},"readout":{{"measurements":[{{"interface":{{"inputs":{prepared},"outputs":{observed}}},"effect":"observe","body":{{"tag":"observe_z","input":0,"output":20}}}}],"pack":[20],"outputs":{final_side}}}}}"#).into_bytes()
}

fn instrument_request(count: u32, negative: bool, controlled: bool) -> Vec<u8> {
    let input = instrument_inputs(controlled);
    let readout_input = side(0, controlled);
    let output = instrument_outputs(controlled);
    let circuit = String::from_utf8(power_request(count, negative, controlled, true)).unwrap();
    format!(r#"{{"format":"qleisli.instrument-request","version":1,"profile":"initialize-unitary-readout-v1","preparation":{{"inputs":{input},"fresh":[{{"owner":0,"basis":[{{"tag":"bit"}}],"axes":[7]}}]}},"circuit":{circuit},"readout":{{"inputs":{readout_input},"owners":[0],"result":900}},"outputs":{output}}}"#).into_bytes()
}

#[test]
fn instrument_codec_rejects_malformed_fields_before_execution() {
    let k = Kernel::new("/nonexistent/qleisli-kernel");
    let good = String::from_utf8(instrument_payload(1, false, true)).unwrap();
    let request = String::from_utf8(instrument_request(1, false, true)).unwrap();
    for bad in [
        good.replacen(r#""version":1"#, r#""version":2"#, 1),
        good.replacen(r#""version":1"#, r#""version":1,"checked":true"#, 1),
        good.replacen(r#""pack":[20]"#, r#""pack":[20],"pack":[20]"#, 1),
        good.replacen(
            r#""initializations":["#,
            r#""initializations":null,"unknown":["#,
            1,
        ),
    ] {
        assert_eq!(
            k.check_instrument(bad.as_bytes(), request.as_bytes())
                .unwrap_err()
                .code,
            "format"
        );
    }
    for bad in [
        request.replacen(r#""result":900"#, r#""result":900,"checked":true"#, 1),
        request.replacen(
            "initialize-unitary-readout-v1",
            "initialize-unitary-readout-v2",
            1,
        ),
        request.replacen(r#""outputs":{"#, r#""outputs":null,"outputs":{"#, 1),
    ] {
        assert_eq!(
            k.check_instrument(good.as_bytes(), bad.as_bytes())
                .unwrap_err()
                .code,
            "format"
        );
    }
    let too_large = request.replacen(r#""owners":[0]"#, r#""owners":[4294967296]"#, 1);
    assert_eq!(
        k.check_instrument(good.as_bytes(), too_large.as_bytes())
            .unwrap_err()
            .code,
        "limit"
    );
    // A well-formed message reaches the selected runtime instead of being
    // accepted locally or rejected by this negative-only harness.
    assert_eq!(
        k.check_instrument(good.as_bytes(), request.as_bytes())
            .unwrap_err()
            .code,
        "io"
    );
}

#[test]
#[ignore = "requires separately built and audited native Lean runtime"]
fn native_instrument_binds_all_stages_and_reconstructs_finite_obligations() {
    let k = native();
    let mut costs = Vec::new();
    for controlled in [false, true] {
        for count in [0, 1, 3] {
            let a = instrument_payload(count, false, controlled);
            let r = instrument_request(count, false, controlled);
            let native = k.check_instrument_native(&a, &r).unwrap();
            assert_eq!(native.payload(), a);
            assert_eq!(native.request(), Some(r.as_slice()));
            let checked = k.check_instrument(&a, &r).unwrap();
            assert_eq!(
                native.exact_work(),
                checked.reconstruction().native_exact_work()
            );
            assert_eq!(checked.request(), r);
            assert_eq!(checked.reconstruction().payload(), a);
            assert_eq!(checked.reconstruction().leaves().len(), 1);
            assert_eq!(
                checked.reconstruction().leaves()[0].1.leaf().meaning(),
                &h_matrix(false)
            );
            costs.push((
                controlled,
                count,
                checked.reconstruction().structural_work(),
                checked.reconstruction().exact_work(),
            ));
            // Zero repeat cannot hide an invalid actual leaf or requested
            // finite equation, even though its overall action is identity.
            let bad = instrument_payload(count, true, controlled);
            assert_eq!(k.check_instrument(&bad, &r).unwrap_err().code, "contract");
            let wrong = instrument_request(count, true, controlled);
            assert_eq!(k.check_instrument(&a, &wrong).unwrap_err().code, "contract");
        }
    }
    println!("composed instrument costs: {costs:?}");
    let a = String::from_utf8(instrument_payload(1, false, true)).unwrap();
    let r = String::from_utf8(instrument_request(1, false, true)).unwrap();
    for bad in [
        a.replacen(r#""effect":"iso""#, r#""effect":"unitary""#, 1),
        a.replacen(
            r#""tag":"init0","output":0"#,
            r#""tag":"init0","output":99"#,
            1,
        ),
        a.replacen(
            r#""tag":"observe_z","input":0"#,
            r#""tag":"observe_z","input":99"#,
            1,
        ),
        a.replacen(r#""pack":[20]"#, r#""pack":[21]"#, 1),
        a.replacen(r#""value":900"#, r#""value":901"#, 1),
    ] {
        assert_eq!(
            k.check_instrument(bad.as_bytes(), r.as_bytes())
                .unwrap_err()
                .code,
            "contract"
        );
    }
    for bad in [
        r.replacen(r#""owners":[0]"#, r#""owners":[99]"#, 1),
        r.replacen(r#""result":900"#, r#""result":901"#, 1),
        r.replacen(r#""axes":[7]"#, r#""axes":[8]"#, 1),
        r.replacen(r#""value":900"#, r#""value":901"#, 1),
    ] {
        assert_eq!(
            k.check_instrument(a.as_bytes(), bad.as_bytes())
                .unwrap_err()
                .code,
            "contract"
        );
    }
}

#[test]
#[cfg(unix)]
fn instrument_host_rejects_missing_duplicate_and_malformed_runtime_obligations() {
    use std::os::unix::fs::PermissionsExt;
    struct Scratch(std::path::PathBuf);
    impl Drop for Scratch {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }
    let stamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let scratch = Scratch(std::env::temp_dir().join(format!(
        "qleisli-instrument-response-{}-{stamp}",
        std::process::id()
    )));
    std::fs::create_dir(&scratch.0).unwrap();
    let executable = scratch.0.join("runtime");
    let payload = instrument_payload(1, false, false);
    let request = instrument_request(1, false, false);
    for body in [
        "pending\n0\n0\n0\n",              // omitted actual finite proof
        "pending\n0\n2\n0\n0\n0\n",        // duplicated actual proof
        "pending\n0\n1\n0\n0\n",           // omitted requested finite equation
        "pending\n0\n1\n0\n2\n2\n2\n",     // duplicated equation
        "pending\n0\n1\n0\n1\n99\n",       // unknown equation
        "pending\n0\n1\n0\n1\n2\nextra\n", // trailing response data
        "pending\n01\n0\n0\n",             // noncanonical counter
        "checked\n0\n0\n0\n",              // a claimed final result is not the protocol
    ] {
        let script = format!(
            "#!/bin/sh\ncat >/dev/null\nprintf '%s' 'qleisli.instrument-pending 3\n{}'\n",
            body.replacen("pending\n0\n", "pending\n0\n0\n", 1)
        );
        std::fs::write(&executable, script).unwrap();
        std::fs::set_permissions(&executable, std::fs::Permissions::from_mode(0o700)).unwrap();
        let error = Kernel::new(&executable)
            .check_instrument(&payload, &request)
            .unwrap_err();
        assert_eq!(error.code, "format", "{body}: {error}");
    }
}
