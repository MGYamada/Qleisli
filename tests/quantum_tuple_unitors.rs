//! Independent exact packaged-product equations, ownership and reference tests.
//! Bounded native requests are not a general source-preservation theorem.
//! Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.

mod common;
use common::SourceRoot;
use qleisli::contract::exact::{Exact, Matrix};
use qleisli::frontend::compile::{ElaboratedProgram, OperationBinding, ParsedProgram, SourceType};
use qleisli::frontend::compile::{ErrorCode, check_project};
use qleisli::interchange::finite_matrix;
use qleisli::interchange::hierarchical::{Kernel, execution::ExecutionLimits};
use std::collections::BTreeMap;
use std::fmt::Write;

fn read(path: &str) -> String {
    common::current_source_text(path)
}
fn study(name: &str) -> String {
    read(&format!(
        "tests/fixtures/authoring_sessions/quantum-tuple-unitors-v030/attempt-01/{name}/main.qli"
    ))
}
fn source(name: &str) -> String {
    read(&format!(
        "tests/fixtures/frontend_v030/quantum-tuple-unitors/independent-sources/{name}.qli"
    ))
}
fn parsed(text: &str) -> ParsedProgram {
    let first = ParsedProgram::parse(BTreeMap::from([("main".into(), text.into())])).unwrap();
    let cloned = first.clone();
    drop(first);
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
fn kernel() -> Kernel {
    Kernel::new(std::env::var_os("QLEISLI_KERNEL").expect("explicit native checker"))
}
fn limits() -> ExecutionLimits {
    ExecutionLimits {
        max_amplitudes: 32,
        max_steps: 30_000,
    }
}
fn input(width: usize) -> Vec<[f64; 2]> {
    (0..(2 << width))
        .map(|i| [(i + 1) as f64 / 13.0, (i as f64 - 2.0) / 17.0])
        .collect()
}
fn mul([a, b]: [f64; 2], [c, d]: [f64; 2]) -> [f64; 2] {
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
fn numbers(ns: &[usize]) -> String {
    ns.iter()
        .map(usize::to_string)
        .collect::<Vec<_>>()
        .join(",")
}

// Independent source/interface trees. They are never recovered from a candidate.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Basis {
    Unit,
    Bit,
    Bits(usize),
    Tuple(Vec<Self>),
}
impl Basis {
    fn pair(a: Self, b: Self) -> Self {
        Self::Tuple(vec![a, b])
    }
    fn width(&self) -> usize {
        match self {
            Self::Unit => 0,
            Self::Bit => 1,
            Self::Bits(n) => *n,
            Self::Tuple(xs) => xs.iter().map(Self::width).sum(),
        }
    }
    fn qli(&self) -> String {
        match self {
            Self::Unit => "Unit".into(),
            Self::Bit => "Bit".into(),
            Self::Bits(n) => format!("Bits<{n}>"),
            Self::Tuple(xs) => format!(
                "({})",
                xs.iter().map(Self::qli).collect::<Vec<_>>().join(",")
            ),
        }
    }
    fn atoms(&self) -> String {
        match self {
            Self::Unit => r#"{"tag":"unit"}"#.into(),
            Self::Bit => r#"{"tag":"bit"}"#.into(),
            Self::Bits(n) => format!(r#"{{"tag":"bits","width":{n}}}"#),
            Self::Tuple(xs) => format!(
                r#"{{"tag":"tuple","arity":{}}},{}"#,
                xs.len(),
                xs.iter().map(Self::atoms).collect::<Vec<_>>().join(",")
            ),
        }
    }
}
fn cases() -> Vec<(&'static str, Basis)> {
    vec![
        ("unit", Basis::Unit),
        ("bit", Basis::Bit),
        ("bits0", Basis::Bits(0)),
        ("bits1", Basis::Bits(1)),
        ("bits2", Basis::Bits(2)),
        (
            "nested-left",
            Basis::pair(Basis::pair(Basis::Unit, Basis::Bit), Basis::Unit),
        ),
        (
            "nested-right",
            Basis::pair(Basis::Unit, Basis::pair(Basis::Bit, Basis::Unit)),
        ),
    ]
}
fn basis_view(ty: &SourceType) -> String {
    assert!(!ty.is_quantum());
    match ty.kind() {
        "unit" => "Unit".into(),
        "bit" => "Bit".into(),
        "bits" => format!("Bits<{}>", ty.width().unwrap()),
        "tuple" => format!(
            "({})",
            ty.fields()
                .iter()
                .map(basis_view)
                .collect::<Vec<_>>()
                .join(",")
        ),
        other => panic!("unexpected basis {other}"),
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
struct Port {
    owner: u32,
    basis: Basis,
    axes: Vec<usize>,
}
impl Port {
    fn new(owner: u32, basis: Basis, offset: usize) -> Self {
        let axes = (offset..offset + basis.width()).collect();
        Self { owner, basis, axes }
    }
    fn json(&self) -> String {
        format!(
            r#"{{"owner":{},"basis":[{}],"axes":[{}]}}"#,
            self.owner,
            self.basis.atoms(),
            numbers(&self.axes)
        )
    }
}
fn side(ps: &[Port]) -> String {
    format!(
        r#"{{"quantum":[{}],"classical":[]}}"#,
        ps.iter().map(Port::json).collect::<Vec<_>>().join(",")
    )
}
fn header(a: &[Port], b: &[Port]) -> String {
    format!(r#"{{"inputs":{},"outputs":{}}}"#, side(a), side(b))
}
#[derive(Clone)]
struct Node {
    before: Vec<Port>,
    after: Vec<Port>,
    text: String,
}
#[derive(Default)]
struct Equation {
    nodes: Vec<Node>,
}
impl Equation {
    fn add(&mut self, a: &[Port], b: &[Port], body: &str) -> usize {
        let text = format!(r#"{{"interface":{},"body":{body}}}"#, header(a, b));
        if let Some(i) = self.nodes.iter().position(|n| n.text == text) {
            return i;
        }
        let i = self.nodes.len();
        self.nodes.push(Node {
            before: a.to_vec(),
            after: b.to_vec(),
            text,
        });
        i
    }
    fn structure(&mut self, a: &[Port], b: &[Port], tag: &str) -> usize {
        self.add(
            a,
            b,
            &format!(r#"{{"tag":"structural","operation":{{"tag":"{tag}"}}}}"#),
        )
    }
    fn rewire(&mut self, a: &[Port], b: &[Port], owners: &[usize], axes: &[usize]) -> usize {
        self.add(
            a,
            b,
            &format!(
                r#"{{"tag":"rewire","permutation":{{"owners":[{}],"axes":[{}],"classical":[]}}}}"#,
                numbers(owners),
                numbers(axes)
            ),
        )
    }
    fn rename(&mut self, a: &[Port], b: &[Port]) -> usize {
        assert_eq!(a.len(), b.len());
        assert!(a.iter().zip(b).all(|(x, y)| x.basis == y.basis));
        self.rewire(
            a,
            b,
            &(0..a.len()).collect::<Vec<_>>(),
            &(0..a.iter().map(|p| p.axes.len()).sum()).collect::<Vec<_>>(),
        )
    }
    fn route(&mut self, a: &[Port], b: &[Port]) -> usize {
        let old = a.iter().flat_map(|p| p.axes.iter()).collect::<Vec<_>>();
        self.rewire(
            a,
            b,
            &b.iter()
                .map(|p| a.iter().position(|q| p == q).unwrap())
                .collect::<Vec<_>>(),
            &b.iter()
                .flat_map(|p| p.axes.iter())
                .map(|w| old.iter().position(|x| *x == w).unwrap())
                .collect::<Vec<_>>(),
        )
    }
    fn sequence(&mut self, children: &[usize]) -> usize {
        let a = self.nodes[children[0]].before.clone();
        let b = self.nodes[*children.last().unwrap()].after.clone();
        for p in children.windows(2) {
            assert_eq!(self.nodes[p[0]].after, self.nodes[p[1]].before);
        }
        self.add(
            &a,
            &b,
            &format!(r#"{{"tag":"sequence","children":[{}]}}"#, numbers(children)),
        )
    }
    fn tensor(&mut self, l: usize, r: usize) -> usize {
        let a = [self.nodes[l].before.clone(), self.nodes[r].before.clone()].concat();
        let b = [self.nodes[l].after.clone(), self.nodes[r].after.clone()].concat();
        self.add(
            &a,
            &b,
            &format!(r#"{{"tag":"tensor","left":{l},"right":{r}}}"#),
        )
    }
    fn frame(&mut self, mut current: Vec<Port>, children: &[usize], outputs: &[Port]) -> usize {
        // Transport-only explicit frame placement. The primitive equations,
        // exact trees and +1/omega coefficients were authored before lowering.
        let mut steps = vec![];
        for &id in children {
            let n = self.nodes[id].clone();
            assert!(n.before.iter().all(|p| current.contains(p)));
            let rest = current
                .iter()
                .filter(|p| !n.before.iter().any(|q| p.owner == q.owner))
                .cloned()
                .collect::<Vec<_>>();
            let arranged = [n.before, rest.clone()].concat();
            if current != arranged {
                steps.push(self.route(&current, &arranged));
            }
            let node = if rest.is_empty() {
                id
            } else {
                let identity = self.rename(&rest, &rest);
                self.tensor(id, identity)
            };
            steps.push(node);
            current = [n.after, rest].concat();
        }
        if current != outputs {
            steps.push(self.route(&current, outputs));
        }
        if steps.is_empty() {
            self.rename(outputs, outputs)
        } else {
            self.sequence(&steps)
        }
    }
    fn scalar(&mut self, a: Port, b: Port, u: u32, v: u32) -> usize {
        self.scalar_phase(a, b, u, v, 1)
    }
    fn scalar_phase(&mut self, a: Port, b: Port, u: u32, v: u32, phase: i32) -> usize {
        assert_eq!(a.basis, b.basis);
        let identity = self.rename(std::slice::from_ref(&a), std::slice::from_ref(&a));
        let u = Port::new(u, Basis::Unit, 0);
        let v = Port::new(v, Basis::Unit, 0);
        let pack = self.structure(&[], std::slice::from_ref(&u), "pack_unit");
        let description = String::from_utf8(
            finite_matrix::encode(&Matrix::new(1, 1, vec![Exact::phase(phase)]).unwrap()).unwrap(),
        )
        .unwrap();
        let finite = self.add(
            &[u],
            std::slice::from_ref(&v),
            &format!(
                r#"{{"tag":"finite","description":{}}}"#,
                quote(&description)
            ),
        );
        let unpack = self.structure(&[v], &[], "unpack_unit");
        let closed = self.sequence(&[pack, finite, unpack]);
        let product = self.tensor(identity, closed);
        let rename = self.rename(&[a], &[b]);
        self.sequence(&[product, rename])
    }
    fn request(&self, root: usize) -> Vec<u8> {
        let n = &self.nodes[root];
        format!(r#"{{"format":"qleisli.hierarchy-request","version":1,"profile":"qpe-dyadic8-v1","kind":"equation","effect":"unitary","interface":{},"meanings":[{}],"entry":{root}}}"#,header(&n.before,&n.after),self.nodes.iter().map(|n|n.text.as_str()).collect::<Vec<_>>().join(",")).into_bytes()
    }
}

fn unitor_request(basis: Basis, left: bool, entry: &str) -> Vec<u8> {
    let mut e = Equation::default();
    let packed = if left {
        Basis::pair(Basis::Unit, basis.clone())
    } else {
        Basis::pair(basis.clone(), Basis::Unit)
    };
    if entry == "insert" {
        let a = Port::new(101, basis, 0);
        let u = Port::new(102, Basis::Unit, 0);
        let q = Port::new(103, packed, 0);
        let eta = e.structure(&[], std::slice::from_ref(&u), "pack_unit");
        let pair = if left {
            vec![u, a.clone()]
        } else {
            vec![a.clone(), u]
        };
        let join = e.structure(&pair, std::slice::from_ref(&q), "join_tuple");
        let root = e.frame(vec![a], &[eta, join], &[q]);
        return e.request(root);
    }
    let q = Port::new(101, packed.clone(), 0);
    let (mut u, a) = if left {
        (Port::new(102, Basis::Unit, 0), Port::new(103, basis, 0))
    } else {
        (Port::new(103, Basis::Unit, 0), Port::new(102, basis, 0))
    };
    let pair = if left {
        vec![u.clone(), a.clone()]
    } else {
        vec![a.clone(), u.clone()]
    };
    let split = e.structure(std::slice::from_ref(&q), &pair, "split_tuple");
    let mut steps = vec![split];
    if entry == "phase_remove" {
        let next = Port::new(104, Basis::Unit, 0);
        steps.push(e.scalar(u, next.clone(), 105, 106));
        u = next;
    }
    steps.push(e.structure(&[u], &[], "unpack_unit"));
    let output = if entry == "round" {
        let fresh = Port::new(104, Basis::Unit, 0);
        let packed = Port::new(105, packed, 0);
        steps.push(e.structure(&[], std::slice::from_ref(&fresh), "pack_unit"));
        let joined = if left { vec![fresh, a] } else { vec![a, fresh] };
        steps.push(e.structure(&joined, std::slice::from_ref(&packed), "join_tuple"));
        packed
    } else {
        a
    };
    let root = e.frame(vec![q], &steps, &[output]);
    e.request(root)
}

fn scalar_provider(e: &mut Equation, first: u32) -> usize {
    let packaged = Basis::pair(Basis::Unit, Basis::Bit);
    let q = Port::new(first, packaged.clone(), 0);
    let u = Port::new(first + 1, Basis::Unit, 0);
    let a = Port::new(first + 2, Basis::Bit, 0);
    let split = e.structure(
        std::slice::from_ref(&q),
        &[u.clone(), a.clone()],
        "split_tuple",
    );
    let phased = Port::new(first + 3, Basis::Unit, 0);
    let phase = e.scalar(u, phased.clone(), first + 4, first + 5);
    let finish = e.structure(&[phased], &[], "unpack_unit");
    let fresh = Port::new(first + 6, Basis::Unit, 0);
    let unit = e.structure(&[], std::slice::from_ref(&fresh), "pack_unit");
    let result = Port::new(first + 7, packaged, 0);
    let join = e.structure(&[fresh, a], std::slice::from_ref(&result), "join_tuple");
    e.frame(vec![q], &[split, phase, finish, unit, join], &[result])
}
fn operation_request(entry: &str) -> Vec<u8> {
    let mut e = Equation::default();
    let first = if entry == "apply" || entry == "inverse" {
        102
    } else {
        103
    };
    let provider = scalar_provider(&mut e, first);
    let canonical = e.nodes[provider].before.clone();
    let end = e.nodes[provider].after.clone();
    let enter = e.rename(&canonical, &canonical);
    let leave = e.rename(&end, &canonical);
    let mut operation = e.sequence(&[enter, provider, leave]);
    if entry == "inverse" {
        operation = e.add(
            &canonical,
            &canonical,
            &format!(r#"{{"tag":"inverse","child":{operation}}}"#),
        );
    }
    if entry == "eight" || entry == "controlled_four" {
        let count = if entry == "eight" { 8 } else { 4 };
        operation = e.add(
            &canonical,
            &canonical,
            &format!(r#"{{"tag":"power","child":{operation},"count":{count}}}"#),
        );
    }
    let ty = Basis::pair(Basis::Unit, Basis::Bit);
    let root = if entry == "controlled_four" {
        let target = [Port::new(102, ty.clone(), 1)];
        let a = e.rename(&target, &canonical);
        let b = e.rename(&canonical, &target);
        let child = e.sequence(&[a, operation, b]);
        let before = [Port::new(101, Basis::Bit, 0), target[0].clone()];
        let control = e.add(
            &before,
            &before,
            &format!(r#"{{"tag":"control","child":{child},"polarity":true}}"#),
        );
        let after = [
            Port::new(first + 8, Basis::Bit, 0),
            Port::new(first + 9, ty, 1),
        ];
        let rename = e.rename(&before, &after);
        let step = e.sequence(&[control, rename]);
        e.sequence(&[step])
    } else {
        let called = if entry == "eight" { 102 } else { 101 };
        let a = [Port::new(called, ty.clone(), 0)];
        let b = [Port::new(first + 8, ty.clone(), 0)];
        let enter = e.rename(&a, &canonical);
        let leave = e.rename(&canonical, &b);
        let call = e.sequence(&[enter, operation, leave]);
        let body = e.sequence(&[call]);
        if entry == "eight" {
            let input = [Port::new(101, ty.clone(), 0)];
            let output = [Port::new(first + 9, ty, 0)];
            let enter = e.rename(&input, &a);
            let leave = e.rename(&b, &output);
            let call = e.sequence(&[enter, body, leave]);
            e.sequence(&[call])
        } else {
            body
        }
    };
    e.request(root)
}

fn reject(text: &str, code: &str) {
    let error = ParsedProgram::parse(BTreeMap::from([("main".into(), text.into())])).unwrap_err();
    assert_eq!(error.code(), code, "{text}: {error}");
    assert_eq!(error.module(), Some("main"));
    assert!(
        error.span().start < error.span().end && error.span().end <= text.len(),
        "{error}"
    );
}

#[test]
fn exact_basis_view_never_unpacks_an_owner_and_preserves_nested_zero_width_fields() {
    for (_, basis) in cases() {
        let packaged = Basis::pair(Basis::Unit, basis.clone());
        let text = format!(
            "pub unitary fn f(q:Q<{}>)->Q<{}>{{q}}",
            packaged.qli(),
            packaged.qli()
        );
        let graph = elaborate(&text, "main::f");
        let root = &graph.definitions()[graph.root()];
        let q = &root.inputs()[0];
        assert!(q.identity().is_some() && q.ty().is_quantum());
        assert!(q.fields().is_empty() && q.ty().fields().is_empty());
        assert_eq!(q.ty().kind(), "tuple");
        assert_eq!(q.ty().width(), Some(basis.width() as u32));
        assert_eq!(basis_view(q.ty().quantum_basis().unwrap()), packaged.qli());
        assert_eq!(q.ty().quantum_basis().unwrap().fields().len(), 2);
        assert_eq!(q.identity(), root.output().identity());
    }
    let g = elaborate("pub unitary fn f(x:(Unit,Bit))->(Unit,Bit){x}", "main::f");
    let ordinary = g.definitions()[g.root()].inputs()[0].ty();
    assert!(!ordinary.is_quantum());
    assert!(ordinary.quantum_basis().is_none());
    assert_eq!(ordinary.fields().len(), 2);
}

#[test]
fn fixed_left_right_unitors_and_roundtrips_preserve_each_exact_tree_and_reference() {
    let k = kernel();
    for (name, basis) in cases() {
        for left in [true, false] {
            let label = if left { "left" } else { "right" };
            let text = source(&format!("{label}-{name}"));
            for entry in ["remove", "insert", "round"] {
                let graph = elaborate(&text, &format!("main::{entry}"));
                let proposal = graph.lower().unwrap();
                let required = unitor_request(basis.clone(), left, entry);
                let checked = k
                    .check_against_native(proposal.payload(), &required)
                    .unwrap();
                assert_eq!(checked.request(), Some(required.as_slice()));
                close(
                    &checked
                        .execute_pure(&input(basis.width()), 2, limits())
                        .unwrap()
                        .amplitudes,
                    &input(basis.width()),
                );
            }
        }
    }
}

#[test]
fn scalar_on_removed_unit_is_omega_on_every_retained_axis_and_reference() {
    let k = kernel();
    for (name, basis) in [
        ("unit", Basis::Unit),
        ("bit", Basis::Bit),
        ("bits2", Basis::Bits(2)),
    ] {
        for left in [true, false] {
            let label = if left { "left" } else { "right" };
            let graph = elaborate(&source(&format!("{label}-{name}")), "main::phase_remove");
            let proposal = graph.lower().unwrap();
            let fixed = unitor_request(basis.clone(), left, "phase_remove");
            let checked = k.check_against_native(proposal.payload(), &fixed).unwrap();
            let expected = input(basis.width())
                .into_iter()
                .map(|z| mul(omega(), z))
                .collect::<Vec<_>>();
            close(
                &checked
                    .execute_pure(&input(basis.width()), 2, limits())
                    .unwrap()
                    .amplitudes,
                &expected,
            );
        }
    }
}

#[test]
fn tuple_operation_binding_adjoint_repeat_and_control_have_independent_full_action() {
    let text = source("operations");
    let p = parsed(&text);
    let k = kernel();
    for (entry, width, factor) in [
        ("apply", 1, omega()),
        ("inverse", 1, [omega()[0], -omega()[1]]),
        ("eight", 1, [1.0, 0.0]),
        ("controlled_four", 2, [-1.0, 0.0]),
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
        let request = operation_request(entry);
        let checked = k
            .check_against_native(proposal.payload(), &request)
            .unwrap();
        let expected = input(width)
            .into_iter()
            .enumerate()
            .map(|(i, z)| {
                if entry != "controlled_four" || i % 2 == 1 {
                    mul(factor, z)
                } else {
                    z
                }
            })
            .collect::<Vec<_>>();
        close(
            &checked
                .execute_pure(&input(width), 2, limits())
                .unwrap()
                .amplitudes,
            &expected,
        );
    }
}

#[test]
fn ordered_axes_and_eager_helper_argument_do_not_erase_quantum_work() {
    let k = kernel();
    let graph = elaborate(&study("ordered-axes"), "main::f");
    let proposal = graph.lower().unwrap();
    let checked = k
        .check_against_native(proposal.payload(), proposal.comparison_request())
        .unwrap();
    let expected = (0..8).map(|i| input(2)[i ^ 1]).collect::<Vec<_>>();
    close(
        &checked
            .execute_pure(&input(2), 2, limits())
            .unwrap()
            .amplitudes,
        &expected,
    );
    let graph = elaborate(&source("argument-once"), "main::f");
    let root = &graph.definitions()[graph.root()];
    assert_eq!(root.steps().len(), 3);
    let callee = root.steps()[0].called_definition().unwrap();
    assert_eq!(root.steps()[1].primitive(), Some("std::quantum::split"));
    assert_eq!(root.steps()[2].primitive(), Some("std::quantum::finish"));
    assert_eq!(
        graph.definitions()[callee]
            .steps()
            .iter()
            .filter(|s| s.primitive() == Some("std::quantum::phase_eighth"))
            .count(),
        1
    );
    let proposal = graph.lower().unwrap();
    let checked = k
        .check_against_native(proposal.payload(), proposal.comparison_request())
        .unwrap();
    close(
        &checked
            .execute_pure(&input(1), 2, limits())
            .unwrap()
            .amplitudes,
        &input(1)
            .into_iter()
            .map(|z| mul(omega(), z))
            .collect::<Vec<_>>(),
    );
}

#[test]
fn split_and_join_create_fresh_distinct_linear_owners_without_flattening() {
    let graph = elaborate(&source("left-nested-right"), "main::round");
    let root = &graph.definitions()[graph.root()];
    let split = &root.steps()[0];
    assert_eq!(split.primitive(), Some("std::quantum::split"));
    let fields = split.output().fields();
    assert_eq!(fields.len(), 2);
    assert_ne!(fields[0].identity(), fields[1].identity());
    assert!(
        fields
            .iter()
            .all(|f| f.identity().is_some() && f.identity() != root.inputs()[0].identity())
    );
    assert!(fields[1].fields().is_empty());
    assert_eq!(
        basis_view(fields[1].ty().quantum_basis().unwrap()),
        "(Unit,(Bit,Unit))"
    );
    assert_ne!(root.output().identity(), root.inputs()[0].identity());
    assert_ne!(root.output().identity(), fields[0].identity());
    assert_ne!(root.output().identity(), fields[1].identity());
}

#[test]
fn same_width_substitutions_and_implicit_destructuring_remain_type_errors() {
    for (a, b) in [
        ("(Unit,Bit)", "(Bits<0>,Bit)"),
        ("(Unit,Bit)", "(Unit,Bits<1>)"),
        ("((Bit,Unit),Bit)", "(Bit,(Unit,Bit))"),
        ("(Bit,Unit,Bit)", "((Bit,Unit),Bit)"),
    ] {
        reject(&format!("pub unitary fn f(q:Q<{a}>)->Q<{b}>{{q}}"), "type");
    }
    reject(&study("implicit-destructure"), "type");
    reject(&study("bits0-is-not-unit"), "type");
    let text =
        source("operations") + "\npub unitary fn wrong(q:Q<(Bits<0>,Bit)>)->Q<(Bits<0>,Bit)>{q}\n";
    let error = parsed(&text)
        .instantiate(
            "main::apply",
            BTreeMap::new(),
            BTreeMap::from([(
                "U".into(),
                OperationBinding::new("main::wrong", BTreeMap::new()),
            )]),
        )
        .unwrap_err();
    assert_eq!(error.code(), "type");
    assert_eq!(error.module(), Some("main"));
    assert!(error.span().start < error.span().end && error.span().end <= text.len());
}

#[test]
fn binary_arity_static_arguments_and_tuple_scalar_remain_separate_rules() {
    for (decl, code) in [
        (
            "pub unitary fn f(q:Q<(Unit,Bit)>)->(Q<Unit>,Q<Bit>){split[0](q)}",
            "static",
        ),
        (
            "pub unitary fn f(a:Q<Unit>,b:Q<Bit>)->Q<(Unit,Bit)>{join[0](a,b)}",
            "static",
        ),
        ("pub unitary fn f()->Unit{split()}", "arity"),
        (
            "pub unitary fn f(q:Q<(Unit,Bit)>,r:Q<(Unit,Bit)>)->(Q<Unit>,Q<Bit>){split(q,r)}",
            "arity",
        ),
        ("pub unitary fn f()->Unit{join()}", "arity"),
        (
            "pub unitary fn f(q:Q<Unit>)->Q<(Unit,Unit)>{join(q)}",
            "arity",
        ),
        (
            "pub unitary fn f(a:Q<Unit>,b:Q<Unit>,c:Q<Unit>)->Q<(Unit,Unit,Unit)>{join(a,b,c)}",
            "arity",
        ),
        (
            "pub unitary fn f(q:Q<(Unit,Bit,Unit)>)->(Q<Unit>,Q<Bit>){split(q)}",
            "type",
        ),
        (
            "pub unitary fn f(a:Q<Unit>,b:Q<Bit>)->(Q<Unit>,Q<Bit>){split((a,b))}",
            "type",
        ),
        (
            "pub unitary fn f(a:Unit,b:Q<Bit>)->Q<(Unit,Bit)>{join(a,b)}",
            "type",
        ),
    ] {
        reject(
            &format!("use std::quantum::{{split,join,phase_eighth}};{decl}"),
            code,
        );
    }
    let text = "use std::quantum::phase_eighth; pub unitary fn f(q:Q<(Unit,Bit)>)->Q<(Unit,Bit)>{phase_eighth(q)}";
    let graph = elaborate(text, "main::f");
    assert_eq!(
        basis_view(
            graph.definitions()[graph.root()]
                .output()
                .ty()
                .quantum_basis()
                .unwrap()
        ),
        "(Unit,Bit)"
    );
    reject(
        "use std::quantum::phase_eighth;pub unitary fn f(a:Q<Unit>,b:Q<Bit>)->(Q<Unit>,Q<Bit>){phase_eighth((a,b))}",
        "type",
    );
}

#[test]
fn direct_packaged_scalar_keeps_exact_tree_axes_and_external_reference() {
    let first = include_str!(
        "fixtures/authoring_sessions/meaning-enforcement-v030/direct-scalar-attempt-01/main.qli"
    );
    for basis in [
        Basis::pair(Basis::Unit, Basis::pair(Basis::Bit, Basis::Bit)),
        Basis::pair(Basis::Unit, Basis::Unit),
        Basis::Tuple(vec![Basis::Unit, Basis::Bit, Basis::Unit]),
        Basis::pair(Basis::Bits(1), Basis::pair(Basis::Unit, Basis::Bit)),
        Basis::pair(Basis::Bits(0), Basis::Unit),
    ] {
        let text = first.replace("(Unit,(Bit,Bit))", &basis.qli());
        let graph = elaborate(&text, "main::client");
        assert_eq!(
            basis_view(
                graph.definitions()[graph.root()].inputs()[0]
                    .ty()
                    .quantum_basis()
                    .unwrap()
            ),
            basis.qli()
        );
        assert_eq!(
            graph.definitions()[graph.root()].inputs()[0].ty(),
            graph.definitions()[graph.root()].output().ty()
        );
        let proposal = graph.lower().unwrap();
        // Independently specified omega times identity: these ports and the
        // exact requested coefficient are not recovered from the candidate.
        let before = Port::new(101, basis.clone(), 0);
        let after = Port::new(102, basis.clone(), 0);
        let mut equation = Equation::default();
        let scalar = equation.scalar(before.clone(), after.clone(), 103, 104);
        let root = equation.sequence(&[scalar]);
        let accepted = kernel()
            .check_against_native(proposal.payload(), &equation.request(root))
            .unwrap();
        let joint = input(basis.width());
        let expected = joint.iter().map(|z| mul(omega(), *z)).collect::<Vec<_>>();
        close(
            &accepted
                .execute_pure(&joint, 2, limits())
                .unwrap()
                .amplitudes,
            &expected,
        );
        let mut wrong = Equation::default();
        let identity = wrong.scalar_phase(before, after, 103, 104, 0);
        let identity = wrong.sequence(&[identity]);
        assert!(
            kernel()
                .check_against_native(proposal.payload(), &wrong.request(identity))
                .is_err()
        );
    }
}

#[test]
fn isolated_zero_owner_loss_revival_alias_and_zero_iteration_bodies_reject() {
    for decl in [
        "pub unitary fn f(q:Q<Unit>)->Q<(Unit,Unit)>{join(q,q)}",
        "pub unitary fn f(q:Q<(Unit,Bit)>)->Q<Bit>{let(u,a)=split(q);a}",
        "pub unitary fn f(q:Q<(Unit,Bit)>)->Q<(Unit,Bit)>{let(u,a)=split(q);let()=finish(u);join(u,a)}",
        "pub unitary fn f(q:Q<(Unit,Bit)>)->Q<Bit>{let(_,a)=split(q);a}",
        "pub unitary fn f(q:Q<(Unit,Unit)>)->Q<(Unit,Unit)>{qfor static k in 0..0 carry r=q{let(a,b)=split(r);yield join(a,a);}}",
        "pub unitary fn f(q:Q<Bit>)->Q<Bit>{q} unitary fn unused(q:Q<(Unit,Bit)>)->Q<Bit>{let(u,a)=split(q);a}",
    ] {
        reject(
            &format!("use std::quantum::{{split,join,finish}};{decl}"),
            "ownership",
        );
    }
    reject(&study("effectful-argument"), "effect");
}

#[test]
fn structural_tuple_events_after_observation_retain_exact_basis_and_reference() {
    let graph = elaborate(&source("maps-after-observation"), "main::f");
    let proposal = graph.lower().unwrap();
    assert_eq!(
        proposal
            .source_events()
            .iter()
            .map(|e| e.kind())
            .collect::<Vec<_>>(),
        ["observe", "pure", "pure", "empty_bits", "prepend_bit"]
    );
    let split = &proposal.source_events()[1];
    let join = &proposal.source_events()[2];
    let packaged = split
        .input_frame()
        .find(|p| p.basis_kind() == "tuple")
        .unwrap();
    assert_eq!(basis_view(packaged.basis()), "(Unit,Bit)");
    assert_eq!(packaged.axes(), &[1]);
    let u = split
        .output_frame()
        .find(|p| p.basis_kind() == "unit")
        .unwrap();
    assert!(u.axes().is_empty());
    let joined = join
        .output_frame()
        .find(|p| p.basis_kind() == "tuple")
        .unwrap();
    assert_eq!(basis_view(joined.basis()), "(Unit,Bit)");
    assert_eq!(joined.axes(), &[1]);
    assert_ne!(packaged.owner(), joined.owner());
    let checked = kernel()
        .check_instrument_native(proposal.payload(), proposal.comparison_request())
        .unwrap();
    proposal
        .validate_initialization_moves_native(&checked)
        .unwrap();
    let actual = checked.execute_instrument(&input(2), 2, limits()).unwrap();
    assert_eq!(
        (
            actual.measured_bits,
            actual.residual_quantum_bits,
            actual.reference_dimension
        ),
        (1, 1, 2)
    );
    for outcome in 0..2 {
        let expected = (0..4)
            .map(|i| input(2)[outcome + 2 * (i % 2) + 4 * (i / 2)])
            .collect::<Vec<_>>();
        close(&actual.branches[outcome], &expected);
    }
}

#[test]
fn finite_controls_remain_checked_and_raw_tuple_limits_are_explicit() {
    use qleisli::contract::BasisType;
    // The first authoring source and observations retain retired do/pure.
    // Check a recorded three-body syntax derivative, never rewrite that history.
    let coherent = read(
        "tests/fixtures/review_v030alpha/hosted-ci-basis-repair-01/finite-coherent-unitors/main.qli",
    );
    for text in [study("finite-split-join"), coherent.clone()] {
        check_project(&SourceRoot::new(&text).0).unwrap();
    }
    let graph = elaborate(&study("finite-split-join"), "main::f");
    let raw = graph.lower_raw().unwrap();
    let target = qleisli::contract::meaning::FiniteMeaning::permutation(
        BasisType::pair(BasisType::Bit, BasisType::Bit),
        vec![0, 1, 2, 3],
    )
    .unwrap();
    // The new structural Raw adapter must establish exact identity, rather
    // than merely stop returning its historical unsupported diagnostic.
    raw.check_finite_meaning(
        &qleisli::interchange::native::Kernel::new(std::env::var_os("QLEISLI_KERNEL").unwrap()),
        &target,
        &mut qleisli::contract::exact::Budget::new(qleisli::contract::DEFAULT_EXACT_WORK),
    )
    .unwrap();
    // Coherent lifting is a separate selected-source capability even though
    // the same exact Q<tuple> now passes common source type classification.
    let error = parsed(&coherent)
        .instantiate("main::f", BTreeMap::new(), BTreeMap::new())
        .unwrap_err();
    assert_eq!(error.code(), "unsupported");
    assert_eq!(error.module(), Some("main"));
    assert!(error.span().end > error.span().start && error.span().end <= coherent.len());

    let historical = study("finite-coherent-unitors");
    let start = historical.find("do ((),x)").unwrap();
    let migration = "Haskell-style coherent `do ... pure ...` was removed in Qleisli 0.3.0. Write `basis q as p { e }`. This is a coherent basis map, not monadic bind or measurement; `pure` does not prepare a state.";
    let finite = check_project(&SourceRoot::new(&historical).0).unwrap_err();
    assert_eq!(finite.code, ErrorCode::Project);
    assert_eq!((finite.span.start, finite.span.end), (start, start + 2));
    assert_eq!(&historical[finite.span.start..finite.span.end], "do");
    assert_eq!(finite.message, format!("parse error: {migration}"));
    let selected = match ParsedProgram::parse(BTreeMap::from([("main".into(), historical.clone())]))
    {
        Err(error) => error,
        Ok(_) => panic!("historical do/pure must reject instead of becoming accepted syntax"),
    };
    assert_eq!(selected.code(), "parse");
    assert_eq!(selected.module(), Some("main"));
    assert_eq!(
        (selected.span().start, selected.span().end),
        (start, start + 2)
    );
    assert_eq!(
        &historical[selected.span().start..selected.span().end],
        "do"
    );
    assert_eq!(selected.message(), migration);
}
