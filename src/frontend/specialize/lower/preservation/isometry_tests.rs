//! Independently specified empty-readout equations and original-source mutants.
//! Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
use super::*;
use crate::contract::exact::{Exact, Matrix};
use crate::frontend::compile::ParsedProgram;
use crate::interchange::{finite_matrix, hierarchical};
use std::path::Path;

fn source(name: &str) -> String {
    if name == "multi-init-order" {
        return include_str!("../../../../../tests/fixtures/frontend_v030/isometry-preparation/supplemental-multi-init/main.qli").into();
    }
    std::fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/authoring_sessions/isometry-preparation-v030/attempt-01")
            .join(name)
            .join("main.qli"),
    )
    .unwrap()
}
fn lower(text: &str) -> HierarchyProposal {
    ParsedProgram::parse(BTreeMap::from([("main".into(), text.into())]))
        .unwrap()
        .instantiate("main::entry", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap()
        .lower()
        .unwrap()
}
fn kernel() -> hierarchical::Kernel {
    hierarchical::Kernel::new(std::env::var_os("QLEISLI_KERNEL").expect("explicit native checker"))
}
fn limits() -> hierarchical::execution::ExecutionLimits {
    hierarchical::execution::ExecutionLimits {
        max_amplitudes: 32,
        max_steps: 20_000,
    }
}

// The transport owner numbers below are explicitly reviewed placements, not
// mathematical evidence. Exact constructors, phase and control are authored
// independently; no candidate body, claimed Meaning or comparison is read.
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
    fn scalar(&mut self, a: u32, b: u32, u: u32, v: u32, phase: i32) -> usize {
        // I_Unit tensor (eta ; [omega] ; epsilon), followed by owner renaming.
        // The complex coefficient is authored here; it is not reconstructed
        // from the generated program or supplied by its claimed meaning.
        let a = [unit(a)];
        let b = [unit(b)];
        let u = [unit(u)];
        let v = [unit(v)];
        let identity = self.rewire(&a, &a, &[0], &[]);
        let pack = self.structural(&[], &u, "pack_unit");
        let exact = Matrix::new(1, 1, vec![Exact::phase(phase)]).unwrap();
        let description = String::from_utf8(finite_matrix::encode(&exact).unwrap()).unwrap();
        let finite = self.add(
            &u,
            &v,
            &format!(
                r#"{{"tag":"finite","description":{}}}"#,
                super::super::quote(&description)
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

fn circuit_request(name: &str, wrong: bool) -> Vec<u8> {
    let mut e = Equation::default();
    let phase = if wrong { 2 } else { 1 };
    let (before, after, entry) = match name {
        "multi-init-order" => {
            let rest = vec![bit(102, 0), bit(106, 1)];
            let before = [vec![unit(101)], rest.clone()].concat();
            let after_phase = [vec![unit(103)], rest.clone()].concat();
            let after_h = vec![bit(107, 0), bit(106, 1)];
            let after = vec![bit(106, 1), bit(107, 0)];
            let idle = e.rewire(&rest, &rest, &[0, 1], &[0, 1]);
            let scalar = e.scalar(101, 103, 104, 105, phase);
            let framed_scalar = e.tensor(&before, &after_phase, scalar, idle);
            let epsilon = e.structural(&[unit(103)], &[], "unpack_unit");
            let finish = e.tensor(&after_phase, &rest, epsilon, idle);
            let h = Matrix::new(
                2,
                2,
                [1, 1, 1, -1]
                    .into_iter()
                    .map(|n| Exact::new([0, n, 0, 0], 1).unwrap())
                    .collect(),
            )
            .unwrap();
            let description = String::from_utf8(finite_matrix::encode(&h).unwrap()).unwrap();
            let leaf = e.add(
                &[bit(102, 0)],
                &[bit(107, 0)],
                &format!(
                    r#"{{"tag":"finite","description":{}}}"#,
                    super::super::quote(&description)
                ),
            );
            let idle_b = e.rewire(&[bit(106, 1)], &[bit(106, 1)], &[0], &[0]);
            let framed_h = e.tensor(&rest, &after_h, leaf, idle_b);
            let route = e.rewire(&after_h, &after, &[1, 0], &[1, 0]);
            let root = e.sequence(&before, &after, &[framed_scalar, finish, framed_h, route]);
            (before, after, root)
        }
        "closed-zero" | "empty-classical" => {
            let ports = vec![bit(101, 0)];
            let root = e.rewire(&ports, &ports, &[0], &[0]);
            (ports.clone(), ports, root)
        }
        "retained-unit" => {
            let ports = vec![unit(101), bit(102, 0)];
            let root = e.rewire(&ports, &ports, &[0, 1], &[0]);
            (ports.clone(), ports, root)
        }
        "unit-zero" => {
            let before = vec![unit(101), bit(102, 0)];
            let after = vec![bit(102, 0)];
            let finish = e.structural(&[unit(101)], &[], "unpack_unit");
            let idle = e.rewire(&after, &after, &[0], &[0]);
            let framed = e.tensor(&before, &after, finish, idle);
            let root = e.sequence(&before, &after, &[framed]);
            (before, after, root)
        }
        "unit-phase" | "fresh-unit-phase" | "helper-phase" => {
            let helper = name == "helper-phase";
            let fresh = name == "fresh-unit-phase";
            let out_unit = if helper { 103 } else { 102 };
            let scalar_a = out_unit + 1;
            let scalar_b = scalar_a + 1;
            let zero = bit(scalar_b + 1, u32::from(helper));
            let rest = if helper {
                vec![bit(102, 0), zero]
            } else {
                vec![zero]
            };
            let after_intro = [vec![unit(101)], rest.clone()].concat();
            let before = if fresh {
                rest.clone()
            } else {
                after_intro.clone()
            };
            let after_phase = [vec![unit(out_unit)], rest.clone()].concat();
            let mut steps = vec![];
            let idle = e.rewire(
                &rest,
                &rest,
                &(0..rest.len()).collect::<Vec<_>>(),
                &(0..rest.len()).collect::<Vec<_>>(),
            );
            if fresh {
                let eta = e.structural(&[], &[unit(101)], "pack_unit");
                steps.push(e.tensor(&before, &after_intro, eta, idle));
            }
            let scalar = e.scalar(101, out_unit, scalar_a, scalar_b, phase);
            steps.push(e.tensor(&after_intro, &after_phase, scalar, idle));
            let epsilon = e.structural(&[unit(out_unit)], &[], "unpack_unit");
            steps.push(e.tensor(&after_phase, &rest, epsilon, idle));
            let root = e.sequence(&before, &rest, &steps);
            (before, rest, root)
        }
        "caller-frame" => {
            let before = vec![unit(101), bit(102, 0), bit(103, 1)];
            let pair = vec![bit(102, 0), bit(103, 1)];
            let after = vec![bit(105, 0), bit(106, 1)];
            let epsilon = e.structural(&[unit(101)], &[], "unpack_unit");
            let idle = e.rewire(&pair, &pair, &[0, 1], &[0, 1]);
            let finish = e.tensor(&before, &pair, epsilon, idle);
            // Exact X (or the deliberately wrong I) on the second, high axis.
            let matrix = Matrix::new(
                2,
                2,
                if wrong {
                    vec![Exact::one(), Exact::zero(), Exact::zero(), Exact::one()]
                } else {
                    vec![Exact::zero(), Exact::one(), Exact::one(), Exact::zero()]
                },
            )
            .unwrap();
            let description = String::from_utf8(finite_matrix::encode(&matrix).unwrap()).unwrap();
            let leaf = e.add(
                &[bit(1, 0)],
                &[bit(2, 0)],
                &format!(
                    r#"{{"tag":"finite","description":{}}}"#,
                    super::super::quote(&description)
                ),
            );
            let enter = e.rewire(&[bit(103, 1)], &[bit(1, 0)], &[0], &[0]);
            let leave = e.rewire(&[bit(2, 0)], &[bit(104, 1)], &[0], &[0]);
            let x = e.sequence(&[bit(103, 1)], &[bit(104, 1)], &[enter, leaf, leave]);
            let rename_x = e.rewire(&[bit(104, 1)], &[bit(103, 1)], &[0], &[0]);
            let closed = e.sequence(&[bit(103, 1)], &[bit(103, 1)], &[x, rename_x]);
            let controlled = e.add(
                &pair,
                &pair,
                &format!(r#"{{"tag":"control","child":{closed},"polarity":true}}"#),
            );
            let rename = e.rewire(&pair, &after, &[0, 1], &[0, 1]);
            let cnot = e.sequence(&pair, &after, &[controlled, rename]);
            let root = e.sequence(&before, &after, &[finish, cnot]);
            (before, after, root)
        }
        _ => panic!("unknown independently specified preparation"),
    };
    e.request(&before, &after, entry)
}

fn request(proposal: &HierarchyProposal, name: &str, wrong: bool) -> Vec<u8> {
    let circuit = json::parse(&circuit_request(name, wrong)).unwrap();
    let interface = circuit.field("interface").unwrap().clone();
    let actual = json::parse(proposal.payload()).unwrap();
    let graph = actual.field("circuit").unwrap();
    let index = graph
        .field("entry")
        .unwrap()
        .field("implementation")
        .unwrap()
        .number()
        .unwrap() as usize;
    assert_eq!(
        interface,
        *graph.field("definitions").unwrap().array().unwrap()[index]
            .field("interface")
            .unwrap(),
        "reviewed transport placement changed for {name}; do not infer new mathematics from the producer"
    );
    let preparation = actual.field("preparation").unwrap();
    let initial = preparation
        .field("initializations")
        .unwrap()
        .array()
        .unwrap()[0]
        .field("interface")
        .unwrap()
        .field("inputs")
        .unwrap()
        .clone();
    let initial_owners: BTreeSet<_> = initial
        .field("quantum")
        .unwrap()
        .array()
        .unwrap()
        .iter()
        .map(|p| p.field("owner").unwrap().number().unwrap())
        .collect();
    let fresh: Vec<_> = preparation
        .field("outputs")
        .unwrap()
        .field("quantum")
        .unwrap()
        .array()
        .unwrap()
        .iter()
        .filter(|p| !initial_owners.contains(&p.field("owner").unwrap().number().unwrap()))
        .cloned()
        .collect();
    let (expected_initial, expected_fresh) = match name {
        "closed-zero" | "empty-classical" => (vec![], vec![bit(101, 0)]),
        "fresh-unit-phase" => (vec![], vec![bit(105, 0)]),
        "unit-zero" | "retained-unit" => (vec![unit(101)], vec![bit(102, 0)]),
        "unit-phase" => (vec![unit(101)], vec![bit(105, 0)]),
        "caller-frame" => (vec![unit(101), bit(102, 0)], vec![bit(103, 1)]),
        "helper-phase" => (vec![unit(101), bit(102, 0)], vec![bit(106, 1)]),
        "multi-init-order" => (vec![unit(101)], vec![bit(102, 0), bit(106, 1)]),
        _ => panic!("unknown preparation interface"),
    };
    assert_eq!(
        initial,
        json::parse(side(&expected_initial).as_bytes()).unwrap()
    );
    assert_eq!(
        Value::Array(fresh.clone()),
        json::parse(format!("[{}]", expected_fresh.join(",")).as_bytes()).unwrap()
    );
    let outputs = actual
        .field("readout")
        .unwrap()
        .field("outputs")
        .unwrap()
        .clone();
    let classical = outputs.field("classical").unwrap().array().unwrap();
    assert_eq!(classical.len(), 1);
    assert_eq!(
        classical[0].field("basis").unwrap().array().unwrap()[0]
            .field("width")
            .unwrap()
            .number()
            .unwrap(),
        0
    );
    let result = classical[0].field("value").unwrap().clone();
    assert_eq!(
        outputs.field("quantum").unwrap(),
        interface
            .field("outputs")
            .unwrap()
            .field("quantum")
            .unwrap()
    );
    json::encode(&Value::object([
        ("format", Value::String("qleisli.instrument-request".into())),
        ("version", Value::Number(1)),
        (
            "profile",
            Value::String("initialize-unitary-readout-v1".into()),
        ),
        (
            "preparation",
            Value::object([("inputs", initial), ("fresh", Value::Array(fresh))]),
        ),
        ("circuit", circuit),
        (
            "readout",
            Value::object([
                ("inputs", interface.field("outputs").unwrap().clone()),
                ("owners", Value::Array(vec![])),
                ("result", result),
            ]),
        ),
        ("outputs", outputs),
    ]))
    .unwrap()
}

#[test]
fn isometry_roots_match_independently_authored_exact_composition_requests() {
    for name in [
        "closed-zero",
        "unit-zero",
        "unit-phase",
        "fresh-unit-phase",
        "caller-frame",
        "helper-phase",
        "retained-unit",
        "empty-classical",
        "multi-init-order",
    ] {
        let proposal = lower(&source(name));
        assert_eq!(
            proposal.source.definitions()[proposal.source.root()].effect(),
            "iso"
        );
        let expected = request(&proposal, name, false);
        let checked = kernel()
            .check_instrument_native(proposal.payload(), &expected)
            .unwrap_or_else(|e| panic!("{name}: {e}"));
        proposal
            .validate_initialization_moves_native(&checked)
            .unwrap();
        if matches!(
            name,
            "unit-phase"
                | "fresh-unit-phase"
                | "helper-phase"
                | "caller-frame"
                | "multi-init-order"
        ) {
            let wrong = request(&proposal, name, true);
            assert!(
                kernel()
                    .check_instrument_native(proposal.payload(), &wrong)
                    .is_err(),
                "{name}: wrong exact coefficient accepted"
            );
        }
    }
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
fn phase([a, b]: [f64; 2]) -> [f64; 2] {
    let s = std::f64::consts::FRAC_1_SQRT_2;
    [s * (a - b), s * (a + b)]
}

#[test]
fn isometry_empty_branch_preserves_complex_phase_and_external_reference() {
    for (name, omega) in [
        ("unit-zero", false),
        ("unit-phase", true),
        ("fresh-unit-phase", true),
        ("retained-unit", false),
    ] {
        let proposal = lower(&source(name));
        let input = [[0.2, 0.3], [-0.6, 0.4]];
        let checked = kernel()
            .check_instrument_native(proposal.payload(), &request(&proposal, name, false))
            .unwrap();
        let output = checked.execute_instrument(&input, 2, limits()).unwrap();
        assert_eq!(output.measured_bits, 0);
        assert_eq!(output.branches.len(), 1);
        assert_eq!(output.residual_quantum_bits, 1);
        let a = if omega { phase(input[0]) } else { input[0] };
        let b = if omega { phase(input[1]) } else { input[1] };
        close(&output.branches[0], &[a, [0.0; 2], b, [0.0; 2]]);
    }
}

#[test]
fn isometry_helper_retains_entangled_caller_frame_and_axis_order() {
    // Reference varies slowest. These are arbitrary unnormalized coefficients,
    // so neither independence of owners nor a sampled probability is assumed.
    let input = [[0.2, 0.3], [-0.4, 0.1], [0.6, -0.2], [-0.1, 0.7]];
    for (name, omega, copy) in [("helper-phase", true, false), ("caller-frame", false, true)] {
        let proposal = lower(&source(name));
        let checked = kernel()
            .check_instrument_native(proposal.payload(), &request(&proposal, name, false))
            .unwrap();
        let output = checked.execute_instrument(&input, 2, limits()).unwrap();
        let mut expected = vec![[0.0; 2]; 8];
        for reference in 0..2 {
            for bit in 0..2 {
                let coefficient = input[reference * 2 + bit];
                let row = if copy { bit * 3 } else { bit };
                expected[reference * 4 + row] = if omega {
                    phase(coefficient)
                } else {
                    coefficient
                };
            }
        }
        close(&output.branches[0], &expected);
    }
}

#[test]
fn isometry_native_valid_phased_finish_cannot_implement_original_source() {
    let valid = lower(&source("unit-zero"));
    let wrong = lower(
        "use std::quantum::finish; use std::quantum::phase_eighth;
         use std::quantum::init0;
         fn changed(q: Q<Unit>) -> Unit { finish(phase_eighth(q)) }
         pub fn entry(q: Q<Unit>) -> Q<Bit> { changed(q); init0() }",
    );
    let mut bad = wrong.clone();
    bad.source = valid.source.clone();
    assert_eq!(bad.events.len(), valid.events.len());
    for (event, original) in bad.events.iter_mut().zip(&valid.events) {
        event.definition = original.definition;
        event.step = original.step;
        event.call_path = original.call_path.clone();
        event.module = original.module.clone();
        event.span = original.span;
    }
    // The candidate has a valid, consistently phased native equation. Native
    // acceptance alone cannot grant correspondence to the original +1 finish.
    let accepted = kernel()
        .check_instrument_native(bad.payload(), bad.comparison_request())
        .unwrap();
    let output = accepted
        .execute_instrument(&[[1.0, 0.0]], 1, limits())
        .unwrap();
    close(&output.branches[0], &[phase([1.0, 0.0]), [0.0; 2]]);
    let error = bad
        .validate_initialization_moves_native(&accepted)
        .unwrap_err();
    assert_eq!(error.code(), "preservation");
    assert_eq!(
        error.message(),
        "actual Unit source map differs from its canonical structural node"
    );
}

#[test]
fn isometry_two_moved_initializations_keep_reversed_axes_and_reference() {
    let proposal = lower(&source("multi-init-order"));
    let checked = kernel()
        .check_instrument_native(
            proposal.payload(),
            &request(&proposal, "multi-init-order", false),
        )
        .unwrap();
    let movement = proposal
        .validate_initialization_moves_native(&checked)
        .unwrap();
    assert!(movement.movements() > 0);
    let input = [[0.2, 0.3], [-0.6, 0.4]];
    let output = checked.execute_instrument(&input, 2, limits()).unwrap();
    assert_eq!(output.measured_bits, 0);
    assert_eq!(output.branches.len(), 1);
    assert_eq!(output.residual_quantum_bits, 2);
    let mut expected = vec![[0.0; 2]; 8];
    for reference in 0..2 {
        let p = phase(input[reference]);
        let coefficient = [
            p[0] * std::f64::consts::FRAC_1_SQRT_2,
            p[1] * std::f64::consts::FRAC_1_SQRT_2,
        ];
        expected[reference * 4] = coefficient;
        expected[reference * 4 + 2] = coefficient;
    }
    close(&output.branches[0], &expected);
}
