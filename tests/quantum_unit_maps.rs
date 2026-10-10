//! Independent exact Unit introduction/elimination equations and owner regressions.
//! Native request checks and bounded execution do not prove source preservation.
//! Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
mod common;

use qleisli::contract::BasisType;
use qleisli::contract::DEFAULT_EXACT_WORK;
use qleisli::contract::exact::{Budget, Exact, Matrix};
use qleisli::frontend::compile::{ElaboratedProgram, Error, ParsedProgram};
use qleisli::interchange::finite_leaf::check_unitary;
use qleisli::interchange::hierarchical::{Kernel, execution::ExecutionLimits};
use qleisli::interchange::{RootInterface, Version, finite_matrix, native};
use qleisli::ir::{CircuitAction, RawOp};
use std::collections::BTreeMap;
use std::fmt::Write;

fn read(path: &str) -> String {
    common::current_source_text(path)
}
fn study(name: &str) -> String {
    read(&format!(
        "tests/fixtures/authoring_sessions/quantum-unit-maps-v030/attempt-01/{name}/main.qli"
    ))
}
fn source(name: &str) -> String {
    read(&format!(
        "tests/fixtures/frontend_v030/quantum-unit-maps/current/{name}.qli"
    ))
}
fn parsed(text: &str) -> ParsedProgram {
    let original = ParsedProgram::parse(BTreeMap::from([("main".into(), text.into())])).unwrap();
    let cloned = original.clone();
    drop(original);
    assert_eq!(cloned.source("main"), Some(text));
    cloned
}
fn elaborate(text: &str, entry: &str) -> ElaboratedProgram {
    parsed(text)
        .instantiate(entry, BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap()
}
fn check_raw_steps(graph: &ElaboratedProgram) {
    let raw = graph.lower_raw().unwrap();
    let accepted = native::Kernel::selected()
        .unwrap()
        .accept(raw.proposal())
        .unwrap();
    raw.validate_source_steps(&accepted).unwrap();
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
    // Actual joint vectors have reference dimension two, not a scalar-only
    // consequence of another comparison. No normalization/separability premise.
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
fn numbers(xs: &[usize]) -> String {
    xs.iter()
        .map(usize::to_string)
        .collect::<Vec<_>>()
        .join(",")
}
fn unit(owner: u32) -> String {
    format!(r#"{{"owner":{owner},"basis":[{{"tag":"unit"}}],"axes":[]}}"#)
}
fn bit(owner: u32, axis: u32) -> String {
    format!(r#"{{"owner":{owner},"basis":[{{"tag":"bit"}}],"axes":[{axis}]}}"#)
}
fn side(ports: &[String]) -> String {
    format!(r#"{{"quantum":[{}],"classical":[]}}"#, ports.join(","))
}
fn header(before: &[String], after: &[String]) -> String {
    format!(r#"{{"inputs":{},"outputs":{}}}"#, side(before), side(after))
}

// This small request serializer contains only independently intended equations.
// It never reads a candidate or its producer comparison request. Port labels
// implement the existing transport convention; see independent-expectations.json.
#[derive(Default)]
struct Equation {
    nodes: Vec<String>,
}
impl Equation {
    fn add(&mut self, before: &[String], after: &[String], body: &str) -> usize {
        let node = format!(r#"{{"interface":{},"body":{body}}}"#, header(before, after));
        if let Some(i) = self.nodes.iter().position(|n| *n == node) {
            return i;
        }
        let id = self.nodes.len();
        self.nodes.push(node);
        id
    }
    fn structural(&mut self, before: &[String], after: &[String], operation: &str) -> usize {
        self.add(
            before,
            after,
            &format!(r#"{{"tag":"structural","operation":{{"tag":"{operation}"}}}}"#),
        )
    }
    fn rewire(
        &mut self,
        before: &[String],
        after: &[String],
        owners: &[usize],
        axes: &[usize],
    ) -> usize {
        self.add(
            before,
            after,
            &format!(
                r#"{{"tag":"rewire","permutation":{{"owners":[{}],"axes":[{}],"classical":[]}}}}"#,
                numbers(owners),
                numbers(axes)
            ),
        )
    }
    fn sequence(&mut self, before: &[String], after: &[String], children: &[usize]) -> usize {
        self.add(
            before,
            after,
            &format!(r#"{{"tag":"sequence","children":[{}]}}"#, numbers(children)),
        )
    }
    fn tensor(&mut self, before: &[String], after: &[String], left: usize, right: usize) -> usize {
        self.add(
            before,
            after,
            &format!(r#"{{"tag":"tensor","left":{left},"right":{right}}}"#),
        )
    }
    fn scalar(&mut self, a: u32, b: u32, u: u32, v: u32) -> usize {
        // I_Unit tensor (eta ; [omega] ; epsilon), followed by owner renaming.
        // The complex coefficient is authored here; it is not reconstructed
        // from the generated program or supplied by its claimed meaning.
        let a = [unit(a)];
        let b = [unit(b)];
        let u = [unit(u)];
        let v = [unit(v)];
        let identity = self.rewire(&a, &a, &[0], &[]);
        let pack = self.structural(&[], &u, "pack_unit");
        let exact = Matrix::new(1, 1, vec![Exact::phase(1)]).unwrap();
        let description = String::from_utf8(finite_matrix::encode(&exact).unwrap()).unwrap();
        let finite = self.add(
            &u,
            &v,
            &format!(
                r#"{{"tag":"finite","description":{}}}"#,
                quote(&description)
            ),
        );
        let unpack = self.structural(&v, &[], "unpack_unit");
        let closed = self.sequence(&[], &[], &[pack, finite, unpack]);
        let tensor = self.tensor(&a, &a, identity, closed);
        let rename = self.rewire(&a, &b, &[0], &[]);
        self.sequence(&a, &b, &[tensor, rename])
    }
    fn request(&self, before: &[String], after: &[String], entry: usize) -> Vec<u8> {
        format!(r#"{{"format":"qleisli.hierarchy-request","version":1,"profile":"qpe-dyadic8-v1","kind":"equation","effect":"unitary","interface":{},"meanings":[{}],"entry":{entry}}}"#, header(before, after), self.nodes.join(",")).into_bytes()
    }
}

fn map_request(name: &str) -> Vec<u8> {
    let mut e = Equation::default();
    let u = [unit(101)];
    let v = [unit(102)];
    let (before, after, children) = match name {
        "introduce" => (vec![], u.to_vec(), vec![e.structural(&[], &u, "pack_unit")]),
        "eliminate" => (
            u.to_vec(),
            vec![],
            vec![e.structural(&u, &[], "unpack_unit")],
        ),
        "ordinary-roundtrip" => {
            let eta = e.structural(&[], &u, "pack_unit");
            let epsilon = e.structural(&u, &[], "unpack_unit");
            (vec![], vec![], vec![eta, epsilon])
        }
        "quantum-roundtrip" => {
            let epsilon = e.structural(&u, &[], "unpack_unit");
            let eta = e.structural(&[], &v, "pack_unit");
            (u.to_vec(), v.to_vec(), vec![epsilon, eta])
        }
        _ => panic!("unknown exact map"),
    };
    let root = e.sequence(&before, &after, &children);
    e.request(&before, &after, root)
}

fn scalar_request(count: usize, return_owner: bool) -> Vec<u8> {
    assert!((1..=2).contains(&count));
    let mut e = Equation::default();
    let eta = e.structural(&[], &[unit(101)], "pack_unit");
    let first = e.scalar(101, 102, 103, 104);
    let mut steps = vec![eta, first];
    let last = if count == 2 {
        steps.push(e.scalar(102, 105, 106, 107));
        105
    } else {
        102
    };
    steps.push(e.structural(&[unit(last)], &[], "unpack_unit"));
    let after = if return_owner {
        let fresh = if count == 2 { 108 } else { 105 };
        steps.push(e.structural(&[], &[unit(fresh)], "pack_unit"));
        vec![unit(fresh)]
    } else {
        vec![]
    };
    let root = e.sequence(&[], &after, &steps);
    e.request(&[], &after, root)
}

fn controlled_four_request() -> Vec<u8> {
    let mut e = Equation::default();
    let canonical = [unit(103)];
    let phase = e.scalar(103, 104, 105, 106);
    let epsilon = e.structural(&[unit(104)], &[], "unpack_unit");
    let eta = e.structural(&[], &[unit(107)], "pack_unit");
    let provider = e.sequence(&canonical, &[unit(107)], &[phase, epsilon, eta]);
    let enter = e.rewire(&canonical, &canonical, &[0], &[]);
    let restore = e.rewire(&[unit(107)], &canonical, &[0], &[]);
    let closed = e.sequence(&canonical, &canonical, &[enter, provider, restore]);
    let power = e.add(
        &canonical,
        &canonical,
        &format!(r#"{{"tag":"power","child":{closed},"count":4}}"#),
    );
    let target = [unit(102)];
    let a = e.rewire(&target, &canonical, &[0], &[]);
    let b = e.rewire(&canonical, &target, &[0], &[]);
    let body = e.sequence(&target, &target, &[a, power, b]);
    let before = [bit(101, 0), unit(102)];
    let after = [bit(108, 0), unit(109)];
    let control = e.add(
        &before,
        &before,
        &format!(r#"{{"tag":"control","child":{body},"polarity":true}}"#),
    );
    let rename = e.rewire(&before, &after, &[0, 1], &[0]);
    let step = e.sequence(&before, &after, &[control, rename]);
    let root = e.sequence(&before, &after, &[step]);
    e.request(&before, &after, root)
}

fn framed_request(left: bool, introduce: bool) -> Vec<u8> {
    let mut e = Equation::default();
    if introduce {
        let q = bit(101, 0);
        let u = unit(102);
        let eta = e.structural(&[], std::slice::from_ref(&u), "pack_unit");
        let identity = e.rewire(
            std::slice::from_ref(&q),
            std::slice::from_ref(&q),
            &[0],
            &[0],
        );
        let joined = [u.clone(), q.clone()];
        let tensor = e.tensor(std::slice::from_ref(&q), &joined, eta, identity);
        let after = if left {
            joined.to_vec()
        } else {
            vec![q.clone(), u]
        };
        let mut children = vec![tensor];
        if !left {
            children.push(e.rewire(&joined, &after, &[1, 0], &[0]));
        }
        let root = e.sequence(std::slice::from_ref(&q), &after, &children);
        e.request(&[q], &after, root)
    } else {
        let (u, q) = if left {
            (unit(101), bit(102, 0))
        } else {
            (unit(102), bit(101, 0))
        };
        let epsilon = e.structural(std::slice::from_ref(&u), &[], "unpack_unit");
        let before = if left {
            vec![u.clone(), q.clone()]
        } else {
            vec![q.clone(), u.clone()]
        };
        let arranged = [u, q.clone()];
        let route = if left {
            None
        } else {
            Some(e.rewire(&before, &arranged, &[1, 0], &[0]))
        };
        let identity = e.rewire(
            std::slice::from_ref(&q),
            std::slice::from_ref(&q),
            &[0],
            &[0],
        );
        let tensor = e.tensor(&arranged, std::slice::from_ref(&q), epsilon, identity);
        let mut children = route.into_iter().collect::<Vec<_>>();
        children.push(tensor);
        let root = e.sequence(&before, std::slice::from_ref(&q), &children);
        e.request(&before, &[q], root)
    }
}

fn located(error: &Error, text: &str, code: &str) {
    assert_eq!(error.code(), code, "{text}: {error}");
    assert_eq!(error.module(), Some("main"));
    assert!(error.span().end > error.span().start, "{text}: {error}");
    assert!(error.span().end <= text.len());
}

#[test]
fn first_positive_sources_retain_whole_signatures_and_reach_elaboration() {
    for name in [
        "introduce",
        "eliminate",
        "ordinary-roundtrip",
        "quantum-roundtrip",
        "scalar-argument",
        "controlled-four",
        "left-separate-owner",
        "right-separate-owner",
        "observing-argument",
        "existing-scalar-control",
        "existing-ordinary-control",
    ] {
        let text = study(name);
        let graph = elaborate(&text, "main::f");
        assert_eq!(
            graph.instantiation().program().source("main"),
            Some(text.as_str())
        );
    }
}

#[test]
fn exact_eta_epsilon_and_both_roundtrips_preserve_reference_coefficients() {
    for name in [
        "introduce",
        "eliminate",
        "ordinary-roundtrip",
        "quantum-roundtrip",
    ] {
        let graph = elaborate(&study(name), "main::f");
        let proposal = graph.lower().unwrap();
        assert!(!proposal.is_instrument());
        let required = map_request(name);
        let checked = kernel()
            .check_against_native(proposal.payload(), &required)
            .unwrap();
        assert_eq!(checked.request(), Some(required.as_slice()));
        close(
            &checked
                .execute_pure(&input(0), 2, limits())
                .unwrap()
                .amplitudes,
            &input(0),
        );
        let raw = graph.lower_raw().unwrap();
        let native = native::Kernel::selected().unwrap();
        let accepted = native.accept(raw.proposal()).unwrap();
        raw.validate_source_steps(&accepted).unwrap();
        let identity =
            qleisli::contract::meaning::FiniteMeaning::phase(BasisType::Unit, vec![0]).unwrap();
        let equation =
            raw.check_finite_meaning(&native, &identity, &mut Budget::new(DEFAULT_EXACT_WORK));
        if name == "quantum-roundtrip" {
            equation.unwrap();
        } else {
            // Ordinary Unit ports are not unary quantum endomorphisms. Raw
            // acceptance does not widen the source Meaning interface.
            assert_eq!(equation.unwrap_err().code(), "unsupported");
        }
    }
}

#[test]
fn ordinary_unit_copy_creates_fresh_owners_while_finish_returns_no_owner() {
    let graph = elaborate(&source("two-fresh-owners"), "main::f");
    let root = &graph.definitions()[graph.root()];
    assert_eq!(root.inputs()[0].identity(), None);
    assert_eq!(root.output().fields().len(), 2);
    let a = &root.output().fields()[0];
    let b = &root.output().fields()[1];
    assert_ne!(a.identity(), b.identity());
    assert!(a.identity().is_some() && b.identity().is_some());
    for value in [a, b] {
        assert_eq!(
            (
                value.ty().kind(),
                value.ty().width(),
                value.ty().is_quantum()
            ),
            ("unit", Some(0), true)
        );
    }
    let graph = elaborate(&study("quantum-roundtrip"), "main::f");
    let root = &graph.definitions()[graph.root()];
    assert_ne!(root.inputs()[0].identity(), root.output().identity());
    assert_eq!(root.steps().len(), 2);
    assert_eq!(root.steps()[0].primitive(), Some("std::quantum::finish"));
    assert_eq!(root.steps()[0].output().identity(), None);
    assert!(!root.steps()[0].output().ty().is_quantum());
    assert_eq!(root.steps()[1].primitive(), Some("std::quantum::unit"));
}

#[test]
fn scalar_arguments_execute_once_and_finish_does_not_erase_phase() {
    for (name, count, return_owner, factor) in [
        ("scalar-closed", 1, false, omega()),
        ("scalar-result", 1, true, omega()),
        ("double-scalar-result", 2, true, [0.0, 1.0]),
    ] {
        let graph = elaborate(&source(name), "main::f");
        check_raw_steps(&graph);
        let root = &graph.definitions()[graph.root()];
        let expected_steps = if count == 2 {
            vec![
                "std::quantum::unit",
                "std::quantum::phase_eighth",
                "std::quantum::phase_eighth",
                "std::quantum::finish",
                "std::quantum::unit",
            ]
        } else if return_owner {
            vec![
                "std::quantum::unit",
                "std::quantum::phase_eighth",
                "std::quantum::finish",
                "std::quantum::unit",
            ]
        } else {
            vec![
                "std::quantum::unit",
                "std::quantum::phase_eighth",
                "std::quantum::finish",
            ]
        };
        assert_eq!(
            root.steps()
                .iter()
                .map(|s| s.primitive().unwrap())
                .collect::<Vec<_>>(),
            expected_steps
        );
        let proposal = graph.lower().unwrap();
        let required = scalar_request(count, return_owner);
        let k = kernel();
        let checked = k
            .check_against_native(proposal.payload(), &required)
            .unwrap();
        let reconstruction = k.inspect(proposal.payload()).unwrap();
        assert_eq!(reconstruction.leaves().len(), count);
        for (_, serialized) in reconstruction.leaves() {
            let leaf = serialized.leaf();
            assert_eq!(leaf.boundary().signature(), &BasisType::Unit);
            check_unitary(
                leaf.payload(),
                leaf.boundary(),
                &Matrix::new(1, 1, vec![Exact::phase(1)]).unwrap(),
                &mut Budget::new(DEFAULT_EXACT_WORK),
            )
            .unwrap();
        }
        close(
            &checked
                .execute_pure(&input(0), 2, limits())
                .unwrap()
                .amplitudes,
            &input(0)
                .into_iter()
                .map(|z| multiply(factor, z))
                .collect::<Vec<_>>(),
        );
    }
}

#[test]
fn four_controlled_roundtrip_scalars_are_z_with_an_untouched_reference() {
    let graph = elaborate(&study("controlled-four"), "main::f");
    let proposal = graph.lower().unwrap();
    let required = controlled_four_request();
    let checked = kernel()
        .check_against_native(proposal.payload(), &required)
        .unwrap();
    let expected = input(1)
        .into_iter()
        .enumerate()
        .map(|(i, z)| if i % 2 == 0 { z } else { [-z[0], -z[1]] })
        .collect::<Vec<_>>();
    close(
        &checked
            .execute_pure(&input(1), 2, limits())
            .unwrap()
            .amplitudes,
        &expected,
    );
}

#[test]
fn left_and_right_owner_product_maps_preserve_order_and_entangled_references() {
    for (name, left, entry, introduce) in [
        ("left-separate-owner", true, "left", true),
        ("left-separate-owner", true, "remove", false),
        ("right-separate-owner", false, "right", true),
        ("right-separate-owner", false, "remove", false),
    ] {
        let graph = elaborate(&study(name), &format!("main::{entry}"));
        check_raw_steps(&graph);
        let proposal = graph.lower().unwrap();
        let required = framed_request(left, introduce);
        let checked = kernel()
            .check_against_native(proposal.payload(), &required)
            .unwrap();
        close(
            &checked
                .execute_pure(&input(1), 2, limits())
                .unwrap()
                .amplitudes,
            &input(1),
        );
    }
    // The additional two-bit case has a Unit owner between distinct physical
    // owners. Its independently fixed action is identity on system x reference.
    let graph = elaborate(&source("separate-middle-owner"), "main::f");
    check_raw_steps(&graph);
    let proposal = graph.lower().unwrap();
    let mut e = Equation::default();
    let before = [bit(101, 0), unit(102), bit(103, 1)];
    let arranged = [unit(102), bit(101, 0), bit(103, 1)];
    let after = [bit(101, 0), bit(103, 1)];
    let epsilon = e.structural(&[unit(102)], &[], "unpack_unit");
    let route = e.rewire(&before, &arranged, &[1, 0, 2], &[0, 1]);
    let identity = e.rewire(&after, &after, &[0, 1], &[0, 1]);
    let tensor = e.tensor(&arranged, &after, epsilon, identity);
    let root = e.sequence(&before, &after, &[route, tensor]);
    let checked = kernel()
        .check_against_native(proposal.payload(), &e.request(&before, &after, root))
        .unwrap();
    close(
        &checked
            .execute_pure(&input(2), 2, limits())
            .unwrap()
            .amplitudes,
        &input(2),
    );
}

#[test]
fn native_valid_wrong_scalar_and_matching_own_meaning_fail_the_unchanged_request() {
    let k = kernel();
    for (text, required, width) in [
        (source("scalar-result"), scalar_request(1, true), 0),
        (study("controlled-four"), controlled_four_request(), 1),
    ] {
        let graph = elaborate(&text, "main::f");
        let proposal = graph.lower().unwrap();
        let reconstruction = k.inspect(proposal.payload()).unwrap();
        assert_eq!(reconstruction.leaves().len(), 1);
        let serialized = &reconstruction.leaves()[0].1;
        let leaf = serialized.leaf();
        let mut raw = leaf.program().raw().clone();
        let [RawOp::ApplyUnitary { steps, .. }] = raw.operations.as_mut_slice() else {
            panic!("scalar leaf");
        };
        assert_eq!(steps.len(), 1);
        assert!(steps[0].controls.is_empty());
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
        let new_matrix = quote(
            std::str::from_utf8(
                &finite_matrix::encode(&Matrix::new(1, 1, vec![Exact::one()]).unwrap()).unwrap(),
            )
            .unwrap(),
        );
        let payload = std::str::from_utf8(proposal.payload()).unwrap();
        let own = std::str::from_utf8(proposal.comparison_request()).unwrap();
        assert_eq!(payload.matches(&old_program).count(), 1);
        assert_eq!(payload.matches(&old_matrix).count(), 1);
        assert_eq!(own.matches(&old_matrix).count(), 1);
        let changed = payload
            .replace(&old_program, &new_program)
            .replace(&old_matrix, &new_matrix);
        let changed_own = own.replace(&old_matrix, &new_matrix);
        let accepted = k
            .check_against_native(changed.as_bytes(), changed_own.as_bytes())
            .unwrap();
        close(
            &accepted
                .execute_pure(&input(width), 2, limits())
                .unwrap()
                .amplitudes,
            &input(width),
        );
        assert!(
            k.check_against_native(changed.as_bytes(), &required)
                .is_err()
        );
    }
}

#[test]
fn isolated_wrong_types_and_arities_reject_before_argument_evaluation() {
    for (declaration, code) in [
        ("pub unitary fn f(b: Bit) -> Q<Unit> { unit(b) }", "type"),
        (
            "pub unitary fn f(b: Bits<0>) -> Q<Unit> { unit(b) }",
            "type",
        ),
        (
            "pub unitary fn f(q: Q<Unit>) -> Q<Unit> { unit(q) }",
            "type",
        ),
        ("pub unitary fn f(u: Unit) -> Unit { finish(u) }", "type"),
        ("pub unitary fn f(b: Bit) -> Unit { finish(b) }", "type"),
        (
            "pub unitary fn f(q: Q<Bits<0>>) -> Unit { finish(q) }",
            "type",
        ),
        ("pub unitary fn f(q: Q<Bit>) -> Unit { finish(q) }", "type"),
        (
            "pub unitary fn f(q: Q<Unit>,r: Q<Unit>) -> Unit { finish((q,r)) }",
            "type",
        ),
        ("pub unitary fn f() -> Q<Unit> { unit() }", "arity"),
        ("pub unitary fn f() -> Q<Unit> { unit((),()) }", "arity"),
        ("pub unitary fn f() -> Unit { finish() }", "arity"),
        (
            "pub unitary fn f(q: Q<Unit>,r: Q<Unit>) -> Unit { finish(q,r) }",
            "arity",
        ),
        (
            "pub unitary fn f(u: Unit) -> Q<Unit> { unit[0](not u) }",
            "static",
        ),
        (
            "pub unitary fn f(q: Q<Unit>) -> Unit { finish[0](not q) }",
            "static",
        ),
    ] {
        let text = format!("use std::quantum::{{unit,finish}}; {declaration}");
        let error =
            ParsedProgram::parse(BTreeMap::from([("main".into(), text.clone())])).unwrap_err();
        located(&error, &text, code);
        if code == "static" {
            assert!(error.message().contains("static argument arity"));
        }
    }
}

#[test]
fn every_isolated_owner_and_unused_zero_iteration_body_is_checked() {
    for declaration in [
        "pub unitary fn f(q: Q<Unit>) -> (Q<Unit>,Q<Unit>) { let u=finish(q); (unit(u),q) }",
        "pub unitary fn f(u: Unit) -> (Q<Unit>,Q<Unit>) { let q=unit(u); (q,q) }",
        "pub unitary fn f(u: Unit) -> Unit { let q=unit(u); () }",
        "pub unitary fn f(u: Unit) -> Unit { let _=unit(u); () }",
        "pub unitary fn f(u: Unit) -> Unit { u } unitary fn unused(q:Q<Unit>)->Q<Unit>{let ()=finish(q);q}",
        "pub unitary fn f(q: Q<Unit>) -> Q<Unit> { qfor static k in 0..0 carry r=q { let ()=finish(r); yield r; } }",
    ] {
        let text = format!("use std::quantum::{{unit,finish}}; {declaration}");
        let error =
            ParsedProgram::parse(BTreeMap::from([("main".into(), text.clone())])).unwrap_err();
        located(&error, &text, "ownership");
    }
}

#[test]
fn effects_are_not_hidden_by_the_ordinary_unit_argument_or_result() {
    let text = study("effect-violation");
    let error = ParsedProgram::parse(BTreeMap::from([("main".into(), text.clone())])).unwrap_err();
    located(&error, &text, "effect");
    let graph = elaborate(&study("observing-argument"), "main::f");
    let root = &graph.definitions()[graph.root()];
    assert_eq!(root.effect(), "observe");
    assert_eq!(root.steps().len(), 3);
    assert!(root.steps()[0].called_definition().is_some());
    assert_eq!(root.steps()[1].primitive(), Some("std::quantum::unit"));
    assert_eq!(root.steps()[2].primitive(), Some("std::quantum::finish"));
    let helper = &graph.definitions()[root.steps()[0].called_definition().unwrap()];
    assert_eq!(helper.steps().len(), 1);
    assert_eq!(
        helper.steps()[0].primitive(),
        Some("std::observe::measure_z")
    );
    // This first desired source drops its readout. Preserve the separate current
    // readout limitation, rather than mislabeling generic checking as lowering.
    assert_eq!(graph.lower().unwrap_err().code(), "unsupported");
}

#[test]
fn unit_maps_after_observation_retain_actual_source_events_and_native_action() {
    let graph = elaborate(&source("maps-after-observation"), "main::f");
    check_raw_steps(&graph);
    let proposal = graph.lower().unwrap();
    assert!(proposal.is_instrument());
    assert_eq!(
        proposal
            .source_events()
            .iter()
            .map(|event| event.kind())
            .collect::<Vec<_>>(),
        ["observe", "pure", "pure", "empty_bits", "prepend_bit"]
    );
    let eta = &proposal.source_events()[1];
    let epsilon = &proposal.source_events()[2];
    let introduced = eta
        .output_frame()
        .find(|p| p.basis_kind() == "unit")
        .unwrap();
    assert!(introduced.axes().is_empty());
    assert_eq!(
        epsilon
            .input_frame()
            .find(|p| p.basis_kind() == "unit")
            .unwrap()
            .owner(),
        introduced.owner()
    );
    assert!(!epsilon.output_frame().any(|p| p.basis_kind() == "unit"));
    let checked = kernel()
        .check_instrument_native(proposal.payload(), proposal.comparison_request())
        .unwrap();
    proposal
        .validate_initialization_moves_native(&checked)
        .unwrap();
    let actual = checked.execute_instrument(&input(1), 2, limits()).unwrap();
    assert_eq!(
        (
            actual.measured_bits,
            actual.residual_quantum_bits,
            actual.reference_dimension
        ),
        (1, 0, 2)
    );
    for outcome in 0..2 {
        close(
            &actual.branches[outcome],
            &(0..2)
                .map(|reference| input(1)[outcome + 2 * reference])
                .collect::<Vec<_>>(),
        );
    }
}

#[test]
fn selected_coherent_lifts_remain_separate_from_explicit_packaged_maps() {
    for (input, pattern, output) in [
        ("Q<(Unit,Bit)>", "((),x)", "x"),
        ("Q<(Bit,Unit)>", "(x,())", "x"),
    ] {
        let identity = format!("pub unitary fn f(q:{input})->{input}{{q}}");
        let graph = ParsedProgram::parse(BTreeMap::from([("main".into(), identity)]))
            .unwrap()
            .instantiate("main::f", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap();
        let body = &graph.definitions()[graph.root()];
        assert_eq!(body.inputs()[0].identity(), body.output().identity());
        assert!(body.output().fields().is_empty());
        assert_eq!(
            body.output().ty().quantum_basis().unwrap().fields().len(),
            2
        );
        let text =
            format!("pub unitary fn f(q:{input})->Q<Bit>{{basis q as {pattern} {{ {output} }}}}");
        // The common source judgment checks the coherent pattern. The selected
        // concrete projection still cannot instantiate this source form.
        let error = ParsedProgram::parse(BTreeMap::from([("main".into(), text.clone())]))
            .unwrap()
            .instantiate("main::f", BTreeMap::new(), BTreeMap::new())
            .unwrap_err();
        located(&error, &text, "unsupported");
    }
}

#[test]
fn raw_unit_maps_keep_scalar_work_and_reject_changed_owner_histories() {
    use qleisli::contract::meaning::FiniteMeaning;
    use qleisli::frontend::compile::compile_project;
    use qleisli::ir::{Effect, TokenId};
    let text = "use std::quantum::{unit,finish,phase_eighth}; pub unitary fn main()->Q<Unit>{finish(phase_eighth(unit(())));unit(())}";
    let graph = elaborate(text, "main::main");
    let raw = graph.lower_raw().unwrap();
    let native = native::Kernel::selected().unwrap();
    let accepted = native.accept(raw.proposal()).unwrap();
    raw.validate_source_steps(&accepted).unwrap();
    assert_eq!(accepted.raw().declared_effect, Effect::Unitary);
    assert!(accepted.raw().quantum_inputs.is_empty());
    // Check the retained scalar on the supported unary quantum interface,
    // independently of the closed source and its separate finite adapter.
    let scalar = elaborate(
        "use std::quantum::{unit,finish,phase_eighth};pub unitary fn f(q:Q<Unit>)->Q<Unit>{finish(phase_eighth(q));unit(())}",
        "main::f",
    );
    let scalar = scalar.lower_raw().unwrap();
    let target = FiniteMeaning::phase(BasisType::Unit, vec![1]).unwrap();
    scalar
        .check_finite_meaning(&native, &target, &mut Budget::new(DEFAULT_EXACT_WORK))
        .unwrap();
    let identity = FiniteMeaning::phase(BasisType::Unit, vec![0]).unwrap();
    assert!(
        scalar
            .check_finite_meaning(&native, &identity, &mut Budget::new(DEFAULT_EXACT_WORK))
            .is_err()
    );
    // The finite source adapter invokes the same native boundary, separately.
    let finite_source = "use std::quantum::{unit,finish,phase_eighth};fn main()->Unit{finish(phase_eighth(unit(())));finish(unit(()))}";
    let finite = compile_project(&common::SourceRoot::new(finite_source).0).unwrap();
    assert_eq!(finite.raw().declared_effect, Effect::Unitary);
    let [
        RawOp::PackUnit { output: first },
        RawOp::ApplyUnitary { output: phased, .. },
        RawOp::UnpackUnit { input },
        RawOp::PackUnit { output: fresh },
    ] = accepted.raw().operations.as_slice()
    else {
        panic!("retained Unit/scalar transitions")
    };
    assert_eq!(input, phased);
    assert_ne!(first, fresh);
    let first = *first;
    let phased = *phased;
    let interface = RootInterface {
        input: BasisType::Unit,
        output: BasisType::Unit,
    };
    for wrong in [
        RawOp::PackUnit { output: first },
        RawOp::UnpackUnit { input: phased },
        RawOp::UnpackUnit {
            input: TokenId(u32::MAX),
        },
    ] {
        let mut changed = accepted.raw().clone();
        changed.operations.insert(3, wrong);
        let proposal =
            native::Proposal::from_raw(&changed, Some(&interface), Version::V2, None).unwrap();
        assert!(native.accept(&proposal).is_err());
    }
    // Physically indistinguishable empty owners are still different owners.
    let graph = elaborate(
        "use std::quantum::finish;pub unitary fn f(a:Q<Unit>,b:Q<Unit>)->Q<Unit>{finish(a);b}",
        "main::f",
    );
    let raw = graph.lower_raw().unwrap();
    let accepted = native.accept(raw.proposal()).unwrap();
    let mut changed = accepted.raw().clone();
    let a = changed.quantum_inputs[0].token;
    let b = changed.quantum_inputs[1].token;
    changed.operations[0] = RawOp::UnpackUnit { input: b };
    changed.quantum_outputs[0] = a;
    let proposal = native::Proposal::from_raw(&changed, None, Version::V2, None).unwrap();
    let different = native.accept(&proposal).unwrap();
    assert!(raw.validate_source_steps(&different).is_err());
}

#[test]
fn raw_unit_maps_preserve_controlled_scalar_interference_in_both_source_paths() {
    use qleisli::frontend::compile::compile_project;
    use qleisli::sim::{SimulationLimits, run_closed};
    let text = "use std::quantum::{unit,finish,phase_eighth,h,init0};use std::observe::measure_z;unitary fn scalar(q:Q<Unit>)->Q<Unit>{unit(finish(phase_eighth(q)))}pub observe fn main()->Bit{let(c,u)=controlled(power(scalar,4))(h(init0()),unit(()));finish(u);measure_z(h(c))}";
    let finite = compile_project(&common::SourceRoot::new(text).0).unwrap();
    let raw = elaborate(text, "main::main").lower_raw().unwrap();
    let accepted = native::Kernel::selected()
        .unwrap()
        .accept(raw.proposal())
        .unwrap();
    raw.validate_source_steps(&accepted).unwrap();
    // Four retained eighth phases give Z on the coherent control. Erasing the
    // scalar while consuming its Unit owner would instead return false.
    for program in [&finite, &accepted] {
        let distribution = run_closed(program, SimulationLimits::default()).unwrap();
        assert!((distribution[&vec![true]] - 1.0).abs() < 1e-12);
        assert!(distribution.get(&vec![false]).copied().unwrap_or(0.0) < 1e-12);
    }
}
