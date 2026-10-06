//! Bounded Q<Unit> owner, exact scalar, request and reference regressions.
//! Native request checking and numeric execution are distinct from source proofs.
//! Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
mod common;

use common::SourceRoot;
use qleisli::contract::exact::{Budget, Exact, Matrix};
use qleisli::contract::{BasisType, DEFAULT_EXACT_WORK};
use qleisli::frontend::compile::compile_project;
use qleisli::frontend::sized::{
    ElaboratedProgram, HierarchyEligibility, OperationBinding, ParsedProgram,
};
use qleisli::interchange::finite_leaf::check_unitary;
use qleisli::interchange::hierarchical::{Kernel, execution::ExecutionLimits};
use qleisli::interchange::{RootInterface, Version, finite_matrix, native};
use qleisli::ir::{CircuitAction, RawOp};
use qleisli::sim::{SimulationLimits, run_closed};
use std::collections::BTreeMap;
use std::fmt::Write;
use std::path::Path;

fn read(path: &str) -> String {
    std::fs::read_to_string(common::current_namespace_fixture(
        &Path::new(env!("CARGO_MANIFEST_DIR")).join(path),
    ))
    .unwrap()
}

fn study(name: &str) -> String {
    read(&format!(
        "tests/fixtures/authoring_sessions/quantum-unit-v030/attempt-01/{name}/main.qli"
    ))
}

fn source(name: &str) -> String {
    read(&format!(
        "tests/fixtures/frontend_v030/quantum-unit-source/current/{name}.qli"
    ))
}

fn parsed(text: &str) -> ParsedProgram {
    let original = ParsedProgram::parse(BTreeMap::from([("main".into(), text.into())])).unwrap();
    let cloned = original.clone();
    drop(original);
    assert_eq!(cloned.source("main"), Some(text));
    cloned
}

fn elaborate(text: &str, entry: &str, naturals: BTreeMap<String, u32>) -> ElaboratedProgram {
    parsed(text)
        .instantiate(entry, naturals, BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap()
}

fn kernel() -> Kernel {
    Kernel::new(std::env::var_os("QLEISLI_KERNEL").expect("explicit native checker"))
}

fn limits() -> ExecutionLimits {
    ExecutionLimits {
        max_amplitudes: 32,
        max_steps: 20_000,
    }
}

fn input(width: usize) -> Vec<[f64; 2]> {
    // Two reference coefficients for every system basis label. No normalization
    // or separability assumption is used; at most two system qubits are tested.
    (0..(2 << width))
        .map(|i| [(i + 1) as f64 / 13.0, (i as f64 - 2.0) / 17.0])
        .collect()
}

fn multiply([a, b]: [f64; 2], [c, d]: [f64; 2]) -> [f64; 2] {
    [a * c - b * d, a * d + b * c]
}

fn omega() -> [f64; 2] {
    [std::f64::consts::FRAC_1_SQRT_2; 2]
}

fn close(actual: &[[f64; 2]], expected: &[[f64; 2]]) {
    assert_eq!(actual.len(), expected.len());
    for (a, b) in actual.iter().flatten().zip(expected.iter().flatten()) {
        assert!(
            (a - b).abs() < 1e-12,
            "actual {actual:?}, expected {expected:?}"
        );
    }
}

fn quote(text: &str) -> String {
    let mut out = String::from("\"");
    for c in text.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            c if c < '\u{20}' => write!(out, "\\u{:04x}", c as u32).unwrap(),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn side(owner: u32, basis: &str, width: usize) -> String {
    let axes = (0..width)
        .map(|i| i.to_string())
        .collect::<Vec<_>>()
        .join(",");
    format!(
        r#"{{"quantum":[{{"owner":{owner},"basis":[{basis}],"axes":[{axes}]}}],"classical":[]}}"#
    )
}

fn header(before: &str, after: &str) -> String {
    format!(r#"{{"inputs":{before},"outputs":{after}}}"#)
}

fn meaning(before: &str, after: &str, body: &str) -> String {
    format!(r#"{{"interface":{},"body":{body}}}"#, header(before, after))
}

fn request(before: &str, after: &str, nodes: &[String], entry: usize) -> Vec<u8> {
    format!(
        r#"{{"format":"qleisli.hierarchy-request","version":1,"profile":"qpe-dyadic8-v1","kind":"equation","effect":"unitary","interface":{},"meanings":[{}],"entry":{entry}}}"#,
        header(before, after), nodes.join(",")
    ).into_bytes()
}

fn rename(width: usize) -> String {
    let axes = (0..width)
        .map(|i| i.to_string())
        .collect::<Vec<_>>()
        .join(",");
    format!(r#"{{"tag":"rewire","permutation":{{"owners":[0],"axes":[{axes}],"classical":[]}}}}"#)
}

fn scalar_request(basis: &str, width: usize) -> Vec<u8> {
    // Literal intended equation, not a copied producer comparison request:
    // S = pack Unit; [omega]; unpack Unit, then I_A tensor S and owner rename.
    // Interface labels 101..104 are inspected transport placement only. The
    // exact coefficient and all requested constructors are fixed independently.
    let nodes = scalar_meanings(basis, width, [101, 102, 103, 104]);
    let a = side(101, basis, width);
    let b = side(102, basis, width);
    request(&a, &b, &nodes, 8)
}

fn scalar_meanings(basis: &str, width: usize, owners: [u32; 4]) -> Vec<String> {
    let empty = r#"{"quantum":[],"classical":[]}"#;
    let a = side(owners[0], basis, width);
    let b = side(owners[1], basis, width);
    let u = side(owners[2], r#"{"tag":"unit"}"#, 0);
    let v = side(owners[3], r#"{"tag":"unit"}"#, 0);
    let matrix = Matrix::new(1, 1, vec![Exact::phase(1)]).unwrap();
    let description = String::from_utf8(finite_matrix::encode(&matrix).unwrap()).unwrap();
    vec![
        meaning(&a, &a, &rename(width)),
        meaning(
            empty,
            &u,
            r#"{"tag":"structural","operation":{"tag":"pack_unit"}}"#,
        ),
        meaning(
            &u,
            &v,
            &format!(
                r#"{{"tag":"finite","description":{}}}"#,
                quote(&description)
            ),
        ),
        meaning(
            &v,
            empty,
            r#"{"tag":"structural","operation":{"tag":"unpack_unit"}}"#,
        ),
        meaning(empty, empty, r#"{"tag":"sequence","children":[1,2,3]}"#),
        meaning(&a, &a, r#"{"tag":"tensor","left":0,"right":4}"#),
        meaning(&a, &b, &rename(width)),
        meaning(&a, &b, r#"{"tag":"sequence","children":[5,6]}"#),
        meaning(&a, &b, r#"{"tag":"sequence","children":[7]}"#),
    ]
}

fn append_meaning(nodes: &mut Vec<String>, before: &str, after: &str, body: &str) -> usize {
    let id = nodes.len();
    nodes.push(meaning(before, after, body));
    id
}

fn append_sequence(
    nodes: &mut Vec<String>,
    before: &str,
    after: &str,
    children: &[usize],
) -> usize {
    let children = children
        .iter()
        .map(usize::to_string)
        .collect::<Vec<_>>()
        .join(",");
    append_meaning(
        nodes,
        before,
        after,
        &format!(r#"{{"tag":"sequence","children":[{children}]}}"#),
    )
}

fn controlled_side(control: u32, target: u32) -> String {
    format!(
        r#"{{"quantum":[{{"owner":{control},"basis":[{{"tag":"bit"}}],"axes":[0]}},{{"owner":{target},"basis":[{{"tag":"unit"}}],"axes":[]}}],"classical":[]}}"#
    )
}

fn operation_request(entry: &str) -> Vec<u8> {
    // Fixed intended equations U=omega, U^-1, U^8, controlled(U), and
    // controlled(U^4). The coefficient and operators are authored here, never
    // obtained from a candidate or its producer comparison request. Literal
    // owner labels and the existing call/rename placement were inspected with
    // emit-proposal; these labels carry no semantic justification themselves.
    let unit = |owner| side(owner, r#"{"tag":"unit"}"#, 0);
    let first = match entry {
        "apply" | "inverse" => 102,
        "eight" | "controlled_once" | "controlled_four" => 103,
        _ => panic!("unlisted intended scalar operation"),
    };
    let mut nodes = scalar_meanings(
        r#"{"tag":"unit"}"#,
        0,
        [first, first + 1, first + 2, first + 3],
    );
    let canonical = unit(first);
    let restore = append_meaning(&mut nodes, &unit(first + 1), &canonical, &rename(0));
    let closed = append_sequence(&mut nodes, &canonical, &canonical, &[0, 8, restore]);
    let operation = match entry {
        "inverse" => append_meaning(
            &mut nodes,
            &canonical,
            &canonical,
            &format!(r#"{{"tag":"inverse","child":{closed}}}"#),
        ),
        "eight" | "controlled_four" => {
            let count = if entry == "eight" { 8 } else { 4 };
            append_meaning(
                &mut nodes,
                &canonical,
                &canonical,
                &format!(r#"{{"tag":"power","child":{closed},"count":{count}}}"#),
            )
        }
        _ => closed,
    };
    let (before, after, body) = match entry {
        "apply" | "inverse" => {
            let before = unit(101);
            let after = unit(106);
            let enter = append_meaning(&mut nodes, &before, &canonical, &rename(0));
            let exit = append_meaning(&mut nodes, &canonical, &after, &rename(0));
            let body = append_sequence(&mut nodes, &before, &after, &[enter, operation, exit]);
            (before, after, body)
        }
        "eight" => {
            // The source explicitly calls apply[repeat_op(8,U)], so preserve
            // the inner function boundary and the outer ordinary call.
            let inner_before = unit(102);
            let inner_after = unit(107);
            let enter = append_meaning(&mut nodes, &inner_before, &canonical, &rename(0));
            let exit = append_meaning(&mut nodes, &canonical, &inner_after, &rename(0));
            let step = append_sequence(
                &mut nodes,
                &inner_before,
                &inner_after,
                &[enter, operation, exit],
            );
            let inner = append_sequence(&mut nodes, &inner_before, &inner_after, &[step]);
            let before = unit(101);
            let after = unit(108);
            let enter = append_meaning(&mut nodes, &before, &inner_before, &rename(0));
            let exit = append_meaning(&mut nodes, &inner_after, &after, &rename(0));
            let body = append_sequence(&mut nodes, &before, &after, &[enter, inner, exit]);
            (before, after, body)
        }
        "controlled_once" | "controlled_four" => {
            let target = unit(102);
            let enter = append_meaning(&mut nodes, &target, &canonical, &rename(0));
            let exit = append_meaning(&mut nodes, &canonical, &target, &rename(0));
            let child = append_sequence(&mut nodes, &target, &target, &[enter, operation, exit]);
            let before = controlled_side(101, 102);
            let after = controlled_side(107, 108);
            let control = append_meaning(
                &mut nodes,
                &before,
                &before,
                &format!(r#"{{"tag":"control","child":{child},"polarity":true}}"#),
            );
            let exit = append_meaning(
                &mut nodes,
                &before,
                &after,
                r#"{"tag":"rewire","permutation":{"owners":[0,1],"axes":[0],"classical":[]}}"#,
            );
            let body = append_sequence(&mut nodes, &before, &after, &[control, exit]);
            (before, after, body)
        }
        _ => unreachable!(),
    };
    let root = append_sequence(&mut nodes, &before, &after, &[body]);
    request(&before, &after, &nodes, root)
}

fn identity_request(basis: &str) -> Vec<u8> {
    let a = side(101, basis, 0);
    request(&a, &a, &[meaning(&a, &a, &rename(0))], 0)
}

#[test]
fn retained_fourteen_sources_reach_type_and_owner_judgments() {
    for name in [
        "id",
        "helper-move",
        "ordered-unit-bit",
        "phase-eighth",
        "provider-apply",
        "provider-control",
        "ordinary-unit",
        "empty-bits",
    ] {
        let text = study(name);
        let bindings = if name.starts_with("provider-") {
            BTreeMap::from([(
                "U".into(),
                OperationBinding::new("main::identity", BTreeMap::new()),
            )])
        } else {
            BTreeMap::new()
        };
        parsed(&text)
            .instantiate("main::f", BTreeMap::new(), bindings)
            .unwrap()
            .elaborate()
            .unwrap();
    }
    for (name, code) in [
        ("unit-as-bits0", "type"),
        ("bits0-as-unit", "type"),
        ("duplicate-owner", "ownership"),
        ("lost-owner", "ownership"),
        ("wildcard-owner", "ownership"),
        ("zero-fold-invalid", "ownership"),
    ] {
        let error =
            ParsedProgram::parse(BTreeMap::from([("main".into(), study(name))])).unwrap_err();
        assert_eq!(error.code(), code, "{name}: {error}");
        assert_eq!(error.module(), Some("main"));
        assert!(error.span().end > error.span().start, "{error}");
    }
}

#[test]
fn source_types_keep_zero_axis_quantum_owners_distinct_from_ordinary_unit() {
    let unit = elaborate(&study("id"), "main::f", BTreeMap::new());
    let bits = elaborate(&study("empty-bits"), "main::f", BTreeMap::new());
    let ordinary = elaborate(&study("ordinary-unit"), "main::f", BTreeMap::new());
    let u = &unit.definitions()[unit.root()].inputs()[0];
    let b = &bits.definitions()[bits.root()].inputs()[0];
    let c = &ordinary.definitions()[ordinary.root()].inputs()[0];
    assert_eq!(
        (u.ty().kind(), u.ty().width(), u.ty().is_quantum()),
        ("unit", Some(0), true)
    );
    assert_eq!(
        (b.ty().kind(), b.ty().width(), b.ty().is_quantum()),
        ("bits", Some(0), true)
    );
    assert_eq!(
        (c.ty().kind(), c.ty().width(), c.ty().is_quantum()),
        ("unit", Some(0), false)
    );
    assert_ne!(u.ty(), b.ty());
    assert_ne!(u.ty(), c.ty());
    assert!(u.identity().is_some() && b.identity().is_some() && c.identity().is_none());
    assert!(u.fields().is_empty() && u.ty().fields().is_empty());
    let two = elaborate(&source("ordered-two-units"), "main::f", BTreeMap::new());
    let root = &two.definitions()[two.root()];
    assert_ne!(root.inputs()[0].identity(), root.inputs()[1].identity());
    assert_eq!(root.output().fields()[0], root.inputs()[1]);
    assert_eq!(root.output().fields()[1], root.inputs()[0]);
    let proposal = two.lower().unwrap();
    let checked = kernel()
        .check_against_native(proposal.payload(), proposal.comparison_request())
        .unwrap();
    close(
        &checked
            .execute_pure(&input(0), 2, limits())
            .unwrap()
            .amplitudes,
        &input(0),
    );
}

#[test]
fn fixed_scalar_requests_cover_unit_bit_and_small_registers_without_phase_erasure() {
    for (name, width, basis, naturals) in [
        (
            "scalar-unit",
            0,
            r#"{"tag":"unit"}"#.to_string(),
            BTreeMap::new(),
        ),
        (
            "scalar-bit",
            1,
            r#"{"tag":"bit"}"#.to_string(),
            BTreeMap::new(),
        ),
        (
            "scalar-bits",
            0,
            r#"{"tag":"bits","width":0}"#.to_string(),
            BTreeMap::from([("n".into(), 0)]),
        ),
        (
            "scalar-bits",
            1,
            r#"{"tag":"bits","width":1}"#.to_string(),
            BTreeMap::from([("n".into(), 1)]),
        ),
        (
            "scalar-bits",
            2,
            r#"{"tag":"bits","width":2}"#.to_string(),
            BTreeMap::from([("n".into(), 2)]),
        ),
    ] {
        let graph = elaborate(&source(name), "main::f", naturals);
        assert!(matches!(
            graph.hierarchy_eligibility().unwrap(),
            HierarchyEligibility::Eligible
        ));
        let definition = &graph.definitions()[graph.root()];
        assert_eq!(definition.steps().len(), 1);
        assert_eq!(
            definition.steps()[0].primitive(),
            Some("std::quantum::phase_eighth")
        );
        assert_ne!(
            definition.inputs()[0].identity(),
            definition.output().identity()
        );
        let proposal = graph.lower().unwrap();
        let required = scalar_request(&basis, width);
        let checked = kernel()
            .check_against_native(proposal.payload(), &required)
            .unwrap();
        assert_eq!(checked.request(), Some(required.as_slice()));
        let actual = checked.execute_pure(&input(width), 2, limits()).unwrap();
        assert_eq!(
            (actual.quantum_bits, actual.reference_dimension),
            (width, 2)
        );
        let expected = input(width)
            .into_iter()
            .map(|z| multiply(omega(), z))
            .collect::<Vec<_>>();
        close(&actual.amplitudes, &expected);
    }
}

#[test]
fn native_valid_zero_width_basis_substitutions_fail_the_fixed_typed_request() {
    let unit = elaborate(&study("id"), "main::f", BTreeMap::new())
        .lower()
        .unwrap();
    let bits = elaborate(&study("empty-bits"), "main::f", BTreeMap::new())
        .lower()
        .unwrap();
    let unit_request = identity_request(r#"{"tag":"unit"}"#);
    let bits_request = identity_request(r#"{"tag":"bits","width":0}"#);
    let k = kernel();
    k.inspect_native(unit.payload()).unwrap();
    k.inspect_native(bits.payload()).unwrap();
    k.check_against_native(unit.payload(), &unit_request)
        .unwrap();
    k.check_against_native(bits.payload(), &bits_request)
        .unwrap();
    assert!(
        k.check_against_native(unit.payload(), &bits_request)
            .is_err()
    );
    assert!(
        k.check_against_native(bits.payload(), &unit_request)
            .is_err()
    );
}

#[test]
fn native_valid_scalar_phase_substitution_fails_independent_exact_leaf_and_root_requests() {
    let proposal = elaborate(&source("scalar-unit"), "main::f", BTreeMap::new())
        .lower()
        .unwrap();
    let k = kernel();
    let reconstructed = k.inspect(proposal.payload()).unwrap();
    assert_eq!(reconstructed.leaves().len(), 1);
    let serialized = &reconstructed.leaves()[0].1;
    let leaf = serialized.leaf();
    assert_eq!(leaf.boundary().signature(), &BasisType::Unit);
    let required = Matrix::new(1, 1, vec![Exact::phase(1)]).unwrap();
    check_unitary(
        leaf.payload(),
        leaf.boundary(),
        &required,
        &mut Budget::new(DEFAULT_EXACT_WORK),
    )
    .unwrap();

    let mut wrong = leaf.program().raw().clone();
    let [RawOp::ApplyUnitary { steps, .. }] = wrong.operations.as_mut_slice() else {
        panic!("scalar leaf");
    };
    assert_eq!(steps.len(), 1);
    let CircuitAction::Monomial {
        indices,
        permutation,
        phases,
    } = &mut steps[0].action
    else {
        panic!("scalar monomial");
    };
    assert!(indices.is_empty());
    assert_eq!(permutation, &[0]);
    assert_eq!(phases, &[1]);
    phases[0] = 0;
    let wrong = native::Proposal::from_raw(
        &wrong,
        Some(&RootInterface {
            input: BasisType::Unit,
            output: BasisType::Unit,
        }),
        Version::V2,
        None,
    )
    .unwrap();
    native::Kernel::selected().unwrap().accept(&wrong).unwrap();
    assert!(
        check_unitary(
            wrong.artifact(),
            leaf.boundary(),
            &required,
            &mut Budget::new(DEFAULT_EXACT_WORK)
        )
        .is_err()
    );

    // Substitute both the actual leaf and its own producer-consistency meaning.
    // The whole wrong hierarchy is natively valid; the fixed external omega
    // request must still reject it. Neither request is read from this candidate.
    let old_program = quote(std::str::from_utf8(leaf.payload()).unwrap());
    let new_program = quote(std::str::from_utf8(wrong.artifact()).unwrap());
    let old_matrix = quote(std::str::from_utf8(serialized.description()).unwrap());
    let identity = finite_matrix::encode(&Matrix::new(1, 1, vec![Exact::one()]).unwrap()).unwrap();
    let new_matrix = quote(std::str::from_utf8(&identity).unwrap());
    let payload = std::str::from_utf8(proposal.payload()).unwrap();
    assert_eq!(payload.matches(&old_program).count(), 1);
    assert_eq!(payload.matches(&old_matrix).count(), 1);
    let replaced = payload
        .replace(&old_program, &new_program)
        .replace(&old_matrix, &new_matrix);
    k.inspect_native(replaced.as_bytes()).unwrap();
    assert!(
        k.check_against_native(replaced.as_bytes(), &scalar_request(r#"{"tag":"unit"}"#, 0))
            .is_err()
    );
}

#[test]
fn unit_provider_inverse_repeat_and_control_keep_exact_phase_on_reference_slices() {
    let text = source("operations");
    let p = parsed(&text);
    for (entry, width, factor) in [
        ("apply", 0, omega()),
        ("inverse", 0, [omega()[0], -omega()[1]]),
        ("eight", 0, [1.0, 0.0]),
        ("controlled_once", 1, omega()),
        ("controlled_four", 1, [-1.0, 0.0]),
    ] {
        let graph = p
            .instantiate(
                &format!("main::{entry}"),
                BTreeMap::new(),
                BTreeMap::from([(
                    "U".into(),
                    OperationBinding::new("main::scalar", BTreeMap::new()),
                )]),
            )
            .unwrap()
            .elaborate()
            .unwrap();
        let proposal = graph.lower().unwrap();
        let required = operation_request(entry);
        // The exact leaf and transformation operators are required separately
        // from the actual proposal. The numeric joint-state oracle additionally
        // tests execution; neither check is a universal source theorem.
        let accepted = kernel()
            .check_against_native(proposal.payload(), &required)
            .unwrap();
        assert_eq!(accepted.request(), Some(required.as_slice()));
        let actual = accepted.execute_pure(&input(width), 2, limits()).unwrap();
        let expected = input(width)
            .into_iter()
            .enumerate()
            .map(|(i, z)| {
                if width == 0 || i % 2 == 1 {
                    multiply(factor, z)
                } else {
                    z
                }
            })
            .collect::<Vec<_>>();
        close(&actual.amplitudes, &expected);
    }
}

#[test]
fn native_valid_changed_provider_fails_the_same_fixed_controlled_requests() {
    let p = parsed(&source("operations"));
    let k = kernel();
    for entry in ["controlled_once", "controlled_four"] {
        let graph = p
            .instantiate(
                &format!("main::{entry}"),
                BTreeMap::new(),
                BTreeMap::from([(
                    "U".into(),
                    OperationBinding::new("main::scalar", BTreeMap::new()),
                )]),
            )
            .unwrap()
            .elaborate()
            .unwrap();
        let proposal = graph.lower().unwrap();
        let reconstructed = k.inspect(proposal.payload()).unwrap();
        assert_eq!(reconstructed.leaves().len(), 1);
        let serialized = &reconstructed.leaves()[0].1;
        let leaf = serialized.leaf();
        assert_eq!(leaf.boundary().signature(), &BasisType::Unit);
        let mut raw = leaf.program().raw().clone();
        let [RawOp::ApplyUnitary { steps, .. }] = raw.operations.as_mut_slice() else {
            panic!("scalar provider leaf");
        };
        assert_eq!(steps.len(), 1);
        assert!(steps[0].controls.is_empty());
        let CircuitAction::Monomial {
            indices,
            permutation,
            phases,
        } = &mut steps[0].action
        else {
            panic!("scalar provider monomial");
        };
        assert!(indices.is_empty());
        assert_eq!(permutation, &[0]);
        assert_eq!(phases, &[1]);
        phases[0] = 0;
        let identity = native::Proposal::from_raw(
            &raw,
            Some(&RootInterface {
                input: BasisType::Unit,
                output: BasisType::Unit,
            }),
            Version::V2,
            None,
        )
        .unwrap();
        let old_program = quote(std::str::from_utf8(leaf.payload()).unwrap());
        let new_program = quote(std::str::from_utf8(identity.artifact()).unwrap());
        let old_matrix = quote(std::str::from_utf8(serialized.description()).unwrap());
        let matrix =
            finite_matrix::encode(&Matrix::new(1, 1, vec![Exact::one()]).unwrap()).unwrap();
        let new_matrix = quote(std::str::from_utf8(&matrix).unwrap());
        let payload = std::str::from_utf8(proposal.payload()).unwrap();
        let own_request = std::str::from_utf8(proposal.comparison_request()).unwrap();
        assert_eq!(payload.matches(&old_program).count(), 1);
        assert_eq!(payload.matches(&old_matrix).count(), 1);
        assert_eq!(own_request.matches(&old_matrix).count(), 1);
        let wrong = payload
            .replace(&old_program, &new_program)
            .replace(&old_matrix, &new_matrix);
        let own_request = own_request.replace(&old_matrix, &new_matrix);
        // Only the provider's exact scalar changed. All routes, controls and
        // repetition counts stay intact, and its own claimed equation changes
        // consistently. Native acceptance of that different equation is real.
        let changed = k
            .check_against_native(wrong.as_bytes(), own_request.as_bytes())
            .unwrap();
        close(
            &changed
                .execute_pure(&input(1), 2, limits())
                .unwrap()
                .amplitudes,
            &input(1),
        );
        let required = operation_request(entry);
        assert!(k.check_against_native(wrong.as_bytes(), &required).is_err());
    }
}

#[test]
fn scalar_work_precedes_readout_and_cannot_be_retimed_past_observation() {
    // The original Bit-returning first sources remain immutable. This explicit
    // derivative packs the ordinary result into the current Bits<1> readout
    // interface without changing the quantum work or its chronological order.
    let text = source("phase-then-measure-bits");
    let graph = elaborate(&text, "main::f", BTreeMap::new());
    let proposal = graph.lower().unwrap();
    assert!(proposal.is_instrument());
    assert_eq!(
        proposal
            .source_events()
            .iter()
            .map(|e| e.kind())
            .collect::<Vec<_>>(),
        ["pure", "observe", "empty_bits", "prepend_bit"]
    );
    let phase = &proposal.source_events()[0];
    assert!(phase.unitary_definition().is_some());
    let before = phase
        .input_frame()
        .find(|p| p.basis_kind() == "unit")
        .unwrap();
    let after = phase
        .output_frame()
        .find(|p| p.basis_kind() == "unit")
        .unwrap();
    assert_ne!(before.owner(), after.owner());
    assert!(before.axes().is_empty() && after.axes().is_empty());
    let accepted = kernel()
        .check_instrument_native(proposal.payload(), proposal.comparison_request())
        .unwrap();
    proposal
        .validate_initialization_moves_native(&accepted)
        .unwrap();
    let output = accepted.execute_instrument(&input(1), 2, limits()).unwrap();
    assert_eq!(
        (
            output.measured_bits,
            output.residual_quantum_bits,
            output.reference_dimension
        ),
        (1, 0, 2)
    );
    for outcome in 0..2 {
        let expected = (0..2)
            .map(|reference| multiply(omega(), input(1)[outcome + 2 * reference]))
            .collect::<Vec<_>>();
        close(&output.branches[outcome], &expected);
    }
    let text = source("measure-then-phase-bits");
    let after = elaborate(&text, "main::f", BTreeMap::new());
    assert!(matches!(
        after.hierarchy_eligibility().unwrap(),
        HierarchyEligibility::Eligible
    ));
    let error = after.lower().unwrap_err();
    assert_eq!(error.code(), "unsupported");
    assert_eq!(error.module(), Some("main"));
    assert!(error.message().contains("after observation"));
    assert!(error.span().end > error.span().start);
}

#[test]
fn scalar_signature_rejects_ordinary_values_tuples_and_incorrect_arities() {
    for (declaration, code, message) in [
        (
            "pub unitary fn f(u: Unit) -> Unit { phase_eighth(u) }",
            "type",
            "primitive requires one exact quantum owner",
        ),
        (
            "pub unitary fn f(b: Bit) -> Bit { phase_eighth(b) }",
            "type",
            "primitive requires one exact quantum owner",
        ),
        (
            "pub unitary fn f(q: Q<Unit>,r: Q<Bit>) -> (Q<Unit>,Q<Bit>) { phase_eighth((q,r)) }",
            "type",
            "primitive requires one exact quantum owner",
        ),
        (
            "pub unitary fn f(q: Q<Unit>) -> Q<Unit> { phase_eighth[0](not q) }",
            "static",
            "static argument arity mismatch",
        ),
        (
            "pub unitary fn f() -> Q<Unit> { phase_eighth() }",
            "arity",
            "runtime argument arity mismatch",
        ),
        (
            "pub unitary fn f(q: Q<Unit>) -> Q<Unit> { phase_eighth(q,q) }",
            "arity",
            "runtime argument arity mismatch",
        ),
    ] {
        let text = format!("use std::quantum::phase_eighth; {declaration}");
        let error =
            ParsedProgram::parse(BTreeMap::from([("main".into(), text.clone())])).unwrap_err();
        assert_eq!(error.code(), code, "{text}: {error}");
        assert!(error.message().contains(message), "{text}: {error}");
        assert_eq!(error.module(), Some("main"));
        assert!(error.span().end > error.span().start);
        assert!(text[error.span().start..error.span().end].starts_with("phase_eighth"));
    }
}

#[test]
fn nested_scalar_argument_is_evaluated_once_and_has_omega_squared_action() {
    let text = "use std::quantum::phase_eighth; pub unitary fn f(q: Q<Unit>) -> Q<Unit> { phase_eighth(phase_eighth(q)) }";
    let graph = elaborate(text, "main::f", BTreeMap::new());
    let definition = &graph.definitions()[graph.root()];
    assert_eq!(definition.steps().len(), 2);
    let first = &definition.steps()[0];
    let second = &definition.steps()[1];
    assert_eq!(first.inputs()[0], definition.inputs()[0]);
    assert_eq!(second.inputs()[0], *first.output());
    assert_eq!(definition.output(), second.output());
    assert_ne!(first.inputs()[0].identity(), first.output().identity());
    assert_ne!(first.output().identity(), second.output().identity());
    for step in definition.steps() {
        assert_eq!(step.primitive(), Some("std::quantum::phase_eighth"));
    }
    let proposal = graph.lower().unwrap();
    let reconstructed = kernel().inspect(proposal.payload()).unwrap();
    assert_eq!(reconstructed.leaves().len(), 2);
    let required = Matrix::new(1, 1, vec![Exact::phase(1)]).unwrap();
    for (_, serialized) in reconstructed.leaves() {
        let leaf = serialized.leaf();
        check_unitary(
            leaf.payload(),
            leaf.boundary(),
            &required,
            &mut Budget::new(DEFAULT_EXACT_WORK),
        )
        .unwrap();
    }
    // Producer consistency for the composition, independent exact requirements
    // for both leaves, and an independent numeric oracle i * reference state.
    let accepted = kernel()
        .check_against_native(proposal.payload(), proposal.comparison_request())
        .unwrap();
    let output = accepted.execute_pure(&input(0), 2, limits()).unwrap();
    let expected = input(0)
        .into_iter()
        .map(|z| multiply([0.0, 1.0], z))
        .collect::<Vec<_>>();
    close(&output.amplitudes, &expected);
}

#[test]
fn unused_and_zero_count_bodies_check_ownership_and_raw_bits_phase() {
    for name in ["unused-invalid", "unused-zero-provider"] {
        let error =
            ParsedProgram::parse(BTreeMap::from([("main".into(), source(name))])).unwrap_err();
        assert_eq!(error.code(), "ownership", "{name}: {error}");
        assert_eq!(error.module(), Some("main"));
        assert!(error.span().end > error.span().start);
    }
    {
        let text = source("scalar-bits");
        let graph = elaborate(&text, "main::f", BTreeMap::from([("n".into(), 1)]));
        assert!(matches!(
            graph.hierarchy_eligibility().unwrap(),
            HierarchyEligibility::Eligible
        ));
        let raw = graph.lower_raw().unwrap();
        let selected = native::Kernel::selected().unwrap();
        let accepted = selected.accept(raw.proposal()).unwrap();
        raw.validate_source_steps(&accepted).unwrap();
        let target =
            qleisli::contract::meaning::FiniteMeaning::phase(BasisType::Bits(1), vec![1, 1])
                .unwrap();
        raw.check_finite_meaning(&selected, &target, &mut Budget::new(DEFAULT_EXACT_WORK))
            .unwrap();
        let substituted =
            qleisli::contract::meaning::FiniteMeaning::phase(BasisType::Bit, vec![1, 1]).unwrap();
        assert_eq!(
            raw.check_finite_meaning(
                &selected,
                &substituted,
                &mut Budget::new(DEFAULT_EXACT_WORK)
            )
            .unwrap_err()
            .code(),
            "type",
        );
    }
}

#[test]
fn raw_unit_identity_retains_one_owner_and_independent_exact_scalar_request() {
    let graph = elaborate(&study("id"), "main::f", BTreeMap::new());
    let proposal = graph.lower_raw().unwrap();
    let accepted = native::Kernel::selected()
        .unwrap()
        .accept(proposal.proposal())
        .unwrap();
    proposal.validate_source_steps(&accepted).unwrap();
    let raw = accepted.raw();
    assert_eq!(raw.quantum_inputs.len(), 1);
    assert_eq!(raw.quantum_inputs[0].shape, qleisli::ir::BasisShape::UNIT);
    assert!(raw.quantum_inputs[0].wires.is_empty());
    assert_eq!(raw.quantum_outputs, [raw.quantum_inputs[0].token]);
    assert!(raw.operations.is_empty());
    let boundary = qleisli::interchange::finite_leaf::UnitaryBoundary::new(
        BasisType::Unit,
        raw.quantum_inputs[0].clone(),
        raw.quantum_inputs[0].clone(),
    )
    .unwrap();
    let identity = Matrix::new(1, 1, vec![Exact::one()]).unwrap();
    let leaf = check_unitary(
        proposal.payload(),
        &boundary,
        &identity,
        &mut Budget::new(DEFAULT_EXACT_WORK),
    )
    .unwrap();
    assert_eq!(leaf.payload(), proposal.payload());
    let minus = Matrix::new(1, 1, vec![Exact::phase(4)]).unwrap();
    assert!(
        check_unitary(
            proposal.payload(),
            &boundary,
            &minus,
            &mut Budget::new(DEFAULT_EXACT_WORK)
        )
        .is_err()
    );
}

#[test]
fn raw_scalar_keeps_exact_omega_on_unit_and_every_bit_label() {
    for (name, basis, dimension) in [
        ("scalar-unit", BasisType::Unit, 1),
        ("scalar-bit", BasisType::Bit, 2),
    ] {
        let graph = elaborate(&source(name), "main::f", BTreeMap::new());
        let proposal = graph.lower_raw().unwrap();
        let accepted = native::Kernel::selected()
            .unwrap()
            .accept(proposal.proposal())
            .unwrap();
        proposal.validate_source_steps(&accepted).unwrap();
        let raw = accepted.raw();
        let mut output = raw.quantum_inputs[0].clone();
        output.token = raw.quantum_outputs[0];
        let boundary = qleisli::interchange::finite_leaf::UnitaryBoundary::new(
            basis,
            raw.quantum_inputs[0].clone(),
            output,
        )
        .unwrap();
        // Independent full matrices distinguish a scalar on Bit from T.
        let entries = (0..dimension * dimension)
            .map(|index| {
                if index / dimension == index % dimension {
                    Exact::phase(1)
                } else {
                    Exact::zero()
                }
            })
            .collect();
        let required = Matrix::new(dimension, dimension, entries).unwrap();
        check_unitary(
            proposal.payload(),
            &boundary,
            &required,
            &mut Budget::new(DEFAULT_EXACT_WORK),
        )
        .unwrap();
        let mut wrong = Matrix::identity(dimension).unwrap();
        if dimension == 2 {
            wrong = Matrix::new(
                2,
                2,
                vec![Exact::one(), Exact::zero(), Exact::zero(), Exact::phase(1)],
            )
            .unwrap();
        }
        assert!(
            check_unitary(
                proposal.payload(),
                &boundary,
                &wrong,
                &mut Budget::new(DEFAULT_EXACT_WORK)
            )
            .is_err()
        );
        let mut changed = raw.clone();
        let RawOp::ApplyUnitary { steps, .. } = &mut changed.operations[0] else {
            panic!("scalar action");
        };
        let CircuitAction::Monomial { phases, .. } = &mut steps[0].action else {
            panic!("exact monomial");
        };
        phases[0] = 0;
        let wrong_accepted = native::Kernel::selected()
            .unwrap()
            .accept_raw(changed)
            .unwrap();
        assert!(proposal.validate_source_steps(&wrong_accepted).is_err());
    }
}

#[test]
fn raw_scalar_argument_work_is_ordered_and_matches_finite_emission() {
    let text = "use std::quantum::{init0,phase_eighth}; use std::observe::measure_z;\n\
        unitary fn twice(q: Q<Bit>) -> Q<Bit> { phase_eighth(phase_eighth(q)) }\n\
        pub observe fn main() -> Bit { measure_z(twice(init0())) }";
    let finite = compile_project(&SourceRoot::new(text).0).unwrap();
    let graph = elaborate(text, "main::main", BTreeMap::new());
    let proposal = graph.lower_raw().unwrap();
    let accepted = native::Kernel::selected()
        .unwrap()
        .accept(proposal.proposal())
        .unwrap();
    proposal.validate_source_steps(&accepted).unwrap();
    assert_eq!(accepted.raw(), finite.raw());
    let [
        RawOp::Init0 { .. },
        RawOp::ApplyUnitary { .. },
        RawOp::ApplyUnitary { .. },
        RawOp::MeasureZ { .. },
    ] = accepted.raw().operations.as_slice()
    else {
        panic!("both scalar calls must follow preparation and precede observation");
    };
}

#[test]
fn raw_nested_products_and_calls_keep_empty_owners_beside_a_live_bit() {
    let text = "unitary fn keep(q: Q<Unit>) -> Q<Unit> { q }\n\
        pub unitary fn f(a: Q<Unit>, b: Q<Unit>, c: Q<Bit>)\n\
        -> (Q<Unit>, (Q<Bit>, Q<Unit>)) { (keep(a), (c, keep(b))) }";
    let graph = elaborate(text, "main::f", BTreeMap::new());
    let proposal = graph.lower_raw().unwrap();
    let accepted = native::Kernel::selected()
        .unwrap()
        .accept(proposal.proposal())
        .unwrap();
    proposal.validate_source_steps(&accepted).unwrap();
    let raw = accepted.raw();
    assert_eq!(raw.quantum_inputs.len(), 3);
    assert_eq!(
        raw.quantum_inputs
            .iter()
            .map(|port| port.wires.len())
            .collect::<Vec<_>>(),
        [0, 0, 1]
    );
    assert_eq!(
        raw.quantum_outputs,
        [
            raw.quantum_inputs[0].token,
            raw.quantum_inputs[2].token,
            raw.quantum_inputs[1].token
        ]
    );
    assert!(raw.operations.is_empty());
}

#[test]
fn prior_finite_control_exposes_the_same_unit_scalar_without_using_sized_as_oracle() {
    let text = read(
        "tests/fixtures/authoring_sessions/finite-unit-pattern-v030/validation-sources/coherent-control/main.qli",
    );
    let accepted = compile_project(&SourceRoot::new(&text).0).unwrap();
    let distribution = run_closed(&accepted, SimulationLimits::default()).unwrap();
    let one = (2.0 - 2.0_f64.sqrt()) / 4.0;
    assert!((distribution[&vec![true]] - one).abs() < 1e-12);
    assert!((distribution[&vec![false]] - (1.0 - one)).abs() < 1e-12);
}
