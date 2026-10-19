//! Independently specified empty-readout equations and original-source mutants.
//! Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;
use crate::contract::exact::{Exact, Matrix};
use crate::frontend::compile::ParsedProgram;
use crate::interchange::{finite_matrix, hierarchical};
use std::path::Path;

fn source(name: &str) -> String {
    if name == "multi-init-order" {
        let original = current_source_text(
            "tests/fixtures/frontend_v030/isometry-preparation/supplemental-multi-init/main.qli",
        );
        let prefix = "pub fn entry(";
        assert_eq!(original.matches(prefix).count(), 1);
        // This current test adds an independently checked Isometry contract;
        // the preserved unannotated first program remains unchanged.
        let explicitly_annotated = original.replacen(prefix, "pub isometry fn entry(", 1);
        assert_eq!(
            explicitly_annotated
                .matches("pub isometry fn entry(")
                .count(),
            1
        );
        return explicitly_annotated;
    }
    let original = current_source_text(
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/authoring_sessions/isometry-preparation-v030/attempt-01")
            .join(name)
            .join("main.qli"),
    );
    if name == "empty-classical" {
        let prefix = "pub observe fn entry(";
        assert_eq!(original.matches(prefix).count(), 1);
        // This is a new, narrower public contract for the hierarchy experiment,
        // not a contract-preserving body edit. The original Observe API still
        // refuses this pure hierarchy profile in the public-source regressions.
        let hierarchy_isometry_contract = original.replacen(prefix, "pub isometry fn entry(", 1);
        assert_eq!(
            hierarchy_isometry_contract
                .matches("pub isometry fn entry(")
                .count(),
            1
        );
        hierarchy_isometry_contract
    } else {
        original
    }
}
fn lower(text: &str) -> HierarchyProposal {
    ParsedProgram::parse(
        crate::edition::Edition::E2026,
        BTreeMap::from([("main".into(), text.into())]),
    )
    .unwrap()
    .instantiate("main::entry", BTreeMap::new(), BTreeMap::new())
    .unwrap()
    .elaborate()
    .unwrap()
    .lower()
    .unwrap()
}
fn kernel() -> hierarchical::Kernel {
    hierarchical::Kernel::new(
        std::env::var_os("QLEISLI_KERNEL").expect("explicit native checker"),
        crate::edition::Edition::E2026,
    )
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
    /// The ordinary init0 body is eta_Unit followed by the singleton
    /// Unit-to-Bit map. Physical |0> is prepared separately; its pure interval
    /// consumes exactly the introduced Unit, preserves the fresh Bit, and
    /// renames that Bit result with coefficient +1.
    fn prepared_bit(&mut self, introduced: u32, fresh: u32, output: u32, axis: u32) -> usize {
        let before = vec![unit(introduced), bit(fresh, axis)];
        let zero = vec![bit(fresh, axis)];
        let after = vec![bit(output, axis)];
        let epsilon = self.structural(&[unit(introduced)], &[], "unpack_unit");
        let idle = self.rewire(&zero, &zero, &[0], &[0]);
        let consume = self.tensor(&before, &zero, epsilon, idle);
        let rename = self.rewire(&zero, &after, &[0], &[0]);
        self.sequence(&before, &after, &[consume, rename])
    }
    /// Both exact Hadamard columns are independent of the candidate/source IR.
    fn hadamard(&mut self, before: &[String], after: &[String]) -> usize {
        let matrix = Matrix::new(
            2,
            2,
            [1, 1, 1, -1]
                .into_iter()
                .map(|n| Exact::new([0, n, 0, 0], 1).unwrap())
                .collect(),
        )
        .unwrap();
        let description = String::from_utf8(finite_matrix::encode(&matrix).unwrap()).unwrap();
        self.add(
            before,
            after,
            &format!(
                r#"{{"tag":"finite","description":{}}}"#,
                super::super::quote(&description),
            ),
        )
    }
    fn request(&self, before: &[String], after: &[String], entry: usize) -> Vec<u8> {
        format!(r#"{{"format":"qleisli.hierarchy-request","version":1,"profile":"qpe-dyadic8-v1","kind":"equation","effect":"unitary","interface":{},"meanings":[{}],"entry":{entry}}}"#, header(before, after), self.nodes.join(",")).into_bytes()
    }
}

fn circuit_request(name: &str, wrong: bool) -> Vec<u8> {
    let mut e = Equation::default();
    let phase = if wrong { 2 } else { 1 };
    let (before, after, entry) = match name {
        "basis-zero" => {
            let before = vec![unit(101), bit(102, 0)];
            let after = vec![bit(103, 0)];
            let finish = e.structural(&[unit(101)], &[], "unpack_unit");
            let idle = e.rewire(&[bit(102, 0)], &[bit(102, 0)], &[0], &[0]);
            let framed = e.tensor(&before, &[bit(102, 0)], finish, idle);
            let rename = e.rewire(&[bit(102, 0)], &after, &[0], &[0]);
            let interval = e.sequence(&before, &after, &[framed, rename]);
            // One source basis step retains its own exact interval inside the
            // complete ordinary root frame; the native request compares both.
            let root = e.sequence(&before, &after, &[interval]);
            (before, after, root)
        }
        "basis-phase-reference" => {
            let before = vec![bit(101, 0), unit(102), bit(106, 1)];
            let arranged = vec![unit(102), bit(101, 0), bit(106, 1)];
            let phased = vec![unit(103), bit(101, 0), bit(106, 1)];
            let prepared = vec![unit(103), bit(106, 1), bit(101, 0)];
            let changed = vec![bit(107, 1), bit(101, 0)];
            let after = vec![bit(101, 0), bit(107, 1)];
            let enter = e.rewire(&before, &arranged, &[1, 0, 2], &[0, 1]);
            let scalar = e.scalar(102, 103, 104, 105, phase);
            let rest = vec![bit(101, 0), bit(106, 1)];
            let idle = e.rewire(&rest, &rest, &[0, 1], &[0, 1]);
            let scalar = e.tensor(&arranged, &phased, scalar, idle);
            let arrange = e.rewire(&phased, &prepared, &[0, 2, 1], &[1, 0]);
            let finish = e.structural(&[unit(103)], &[], "unpack_unit");
            let zero = vec![bit(106, 1)];
            let idle = e.rewire(&zero, &zero, &[0], &[0]);
            let finish = e.tensor(&[unit(103), bit(106, 1)], &zero, finish, idle);
            let rename = e.rewire(&zero, &[bit(107, 1)], &[0], &[0]);
            let finish = e.sequence(&[unit(103), bit(106, 1)], &[bit(107, 1)], &[finish, rename]);
            let retained = e.rewire(&[bit(101, 0)], &[bit(101, 0)], &[0], &[0]);
            let finish = e.tensor(&prepared, &changed, finish, retained);
            let leave = e.rewire(&changed, &after, &[1, 0], &[1, 0]);
            let root = e.sequence(&before, &after, &[enter, scalar, arrange, finish, leave]);
            (before, after, root)
        }
        "multi-init-order" => {
            // Source order fixes eta_a, phase(u), eta_b, epsilon(u), H(a).
            // Moving the two |0> preparations does not erase either Unit owner.
            let before = vec![unit(101), bit(103, 0), bit(109, 1)];
            let after_intro_a = vec![unit(102), unit(101), bit(103, 0), bit(109, 1)];
            let arranged_a = vec![unit(102), bit(103, 0), unit(101), bit(109, 1)];
            let after_a = vec![bit(104, 0), unit(101), bit(109, 1)];
            let phase_input = vec![unit(101), bit(104, 0), bit(109, 1)];
            let after_phase = vec![unit(105), bit(104, 0), bit(109, 1)];
            let after_intro_b = vec![unit(108), unit(105), bit(104, 0), bit(109, 1)];
            let arranged_b = vec![unit(108), bit(109, 1), unit(105), bit(104, 0)];
            let after_b = vec![bit(110, 1), unit(105), bit(104, 0)];
            let before_finish = vec![unit(105), bit(110, 1), bit(104, 0)];
            let before_h = vec![bit(104, 0), bit(110, 1)];
            let after_h = vec![bit(111, 0), bit(110, 1)];
            let after = vec![bit(110, 1), bit(111, 0)];
            let idle = e.rewire(&before, &before, &[0, 1, 2], &[0, 1]);
            let eta_a = e.structural(&[], &[unit(102)], "pack_unit");
            let eta_a = e.tensor(&before, &after_intro_a, eta_a, idle);
            let arrange_a = e.rewire(&after_intro_a, &arranged_a, &[0, 2, 1, 3], &[0, 1]);
            let prepare_a = e.prepared_bit(102, 103, 104, 0);
            let rest_a = vec![unit(101), bit(109, 1)];
            let idle_a = e.rewire(&rest_a, &rest_a, &[0, 1], &[0]);
            let prepare_a = e.tensor(&arranged_a, &after_a, prepare_a, idle_a);
            let arrange_phase = e.rewire(&after_a, &phase_input, &[1, 0, 2], &[0, 1]);
            let scalar = e.scalar(101, 105, 106, 107, phase);
            let rest = vec![bit(104, 0), bit(109, 1)];
            let idle = e.rewire(&rest, &rest, &[0, 1], &[0, 1]);
            let scalar = e.tensor(&phase_input, &after_phase, scalar, idle);
            let idle = e.rewire(&after_phase, &after_phase, &[0, 1, 2], &[0, 1]);
            let eta_b = e.structural(&[], &[unit(108)], "pack_unit");
            let eta_b = e.tensor(&after_phase, &after_intro_b, eta_b, idle);
            let arrange_b = e.rewire(&after_intro_b, &arranged_b, &[0, 3, 1, 2], &[1, 0]);
            let prepare_b = e.prepared_bit(108, 109, 110, 1);
            let rest_b = vec![unit(105), bit(104, 0)];
            let idle_b = e.rewire(&rest_b, &rest_b, &[0, 1], &[0]);
            let prepare_b = e.tensor(&arranged_b, &after_b, prepare_b, idle_b);
            let arrange_finish = e.rewire(&after_b, &before_finish, &[1, 0, 2], &[0, 1]);
            let epsilon = e.structural(&[unit(105)], &[], "unpack_unit");
            let rest = vec![bit(110, 1), bit(104, 0)];
            let idle = e.rewire(&rest, &rest, &[0, 1], &[0, 1]);
            let finish = e.tensor(&before_finish, &rest, epsilon, idle);
            let arrange_h = e.rewire(&rest, &before_h, &[1, 0], &[1, 0]);
            let h = e.hadamard(&[bit(104, 0)], &[bit(111, 0)]);
            let idle_b = e.rewire(&[bit(110, 1)], &[bit(110, 1)], &[0], &[0]);
            let h = e.tensor(&before_h, &after_h, h, idle_b);
            let route = e.rewire(&after_h, &after, &[1, 0], &[1, 0]);
            let root = e.sequence(
                &before,
                &after,
                &[
                    eta_a,
                    arrange_a,
                    prepare_a,
                    arrange_phase,
                    scalar,
                    eta_b,
                    arrange_b,
                    prepare_b,
                    arrange_finish,
                    finish,
                    arrange_h,
                    h,
                    route,
                ],
            );
            (before, after, root)
        }
        "closed-zero" | "empty-classical" => {
            let before = vec![bit(102, 0)];
            let after_intro = vec![unit(101), bit(102, 0)];
            let after = vec![bit(103, 0)];
            let eta = e.structural(&[], &[unit(101)], "pack_unit");
            let idle = e.rewire(&before, &before, &[0], &[0]);
            let eta = e.tensor(&before, &after_intro, eta, idle);
            let prepare = e.prepared_bit(101, 102, 103, 0);
            let root = e.sequence(&before, &after, &[eta, prepare]);
            (before, after, root)
        }
        "retained-unit" => {
            let before = vec![unit(101), bit(103, 0)];
            let after_intro = vec![unit(102), unit(101), bit(103, 0)];
            let arranged = vec![unit(102), bit(103, 0), unit(101)];
            let prepared = vec![bit(104, 0), unit(101)];
            let after = vec![unit(101), bit(104, 0)];
            let eta = e.structural(&[], &[unit(102)], "pack_unit");
            let idle = e.rewire(&before, &before, &[0, 1], &[0]);
            let eta = e.tensor(&before, &after_intro, eta, idle);
            let arrange = e.rewire(&after_intro, &arranged, &[0, 2, 1], &[0]);
            let prepare = e.prepared_bit(102, 103, 104, 0);
            let retained = e.rewire(&[unit(101)], &[unit(101)], &[0], &[]);
            let prepare = e.tensor(&arranged, &prepared, prepare, retained);
            let leave = e.rewire(&prepared, &after, &[1, 0], &[0]);
            let root = e.sequence(&before, &after, &[eta, arrange, prepare, leave]);
            (before, after, root)
        }
        "general-superposition" | "unit-zero" => {
            let before = vec![unit(101), bit(103, 0)];
            let zero = vec![bit(103, 0)];
            let introduced = vec![unit(102), bit(103, 0)];
            let prepared = vec![bit(104, 0)];
            let epsilon = e.structural(&[unit(101)], &[], "unpack_unit");
            let idle = e.rewire(&zero, &zero, &[0], &[0]);
            let finish = e.tensor(&before, &zero, epsilon, idle);
            let eta = e.structural(&[], &[unit(102)], "pack_unit");
            let eta = e.tensor(&zero, &introduced, eta, idle);
            let prepare = e.prepared_bit(102, 103, 104, 0);
            let mut steps = vec![finish, eta, prepare];
            let after = if name == "general-superposition" {
                let after = vec![bit(105, 0)];
                steps.push(e.hadamard(&prepared, &after));
                after
            } else {
                prepared
            };
            let root = e.sequence(&before, &after, &steps);
            (before, after, root)
        }
        "unit-phase" | "fresh-unit-phase" | "helper-phase" => {
            let helper = name == "helper-phase";
            let fresh = name == "fresh-unit-phase";
            let out_unit = if helper { 103 } else { 102 };
            let scalar_a = out_unit + 1;
            let scalar_b = scalar_a + 1;
            let init_unit = scalar_b + 1;
            let zero_owner = init_unit + 1;
            let output_owner = zero_owner + 1;
            let axis = u32::from(helper);
            let zero = bit(zero_owner, axis);
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
            let init_frame = [vec![unit(init_unit)], rest.clone()].concat();
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
            let eta = e.structural(&[], &[unit(init_unit)], "pack_unit");
            steps.push(e.tensor(&rest, &init_frame, eta, idle));
            let prepare = e.prepared_bit(init_unit, zero_owner, output_owner, axis);
            let after = if helper {
                let arranged = vec![unit(init_unit), bit(zero_owner, 1), bit(102, 0)];
                let prepared = vec![bit(output_owner, 1), bit(102, 0)];
                let after = vec![bit(102, 0), bit(output_owner, 1)];
                steps.push(e.rewire(&init_frame, &arranged, &[0, 2, 1], &[1, 0]));
                let retained = e.rewire(&[bit(102, 0)], &[bit(102, 0)], &[0], &[0]);
                steps.push(e.tensor(&arranged, &prepared, prepare, retained));
                steps.push(e.rewire(&prepared, &after, &[1, 0], &[1, 0]));
                after
            } else {
                steps.push(prepare);
                vec![bit(output_owner, 0)]
            };
            let root = e.sequence(&before, &after, &steps);
            (before, after, root)
        }
        "caller-frame" => {
            let before = vec![unit(101), bit(102, 0), bit(104, 1)];
            let rest = vec![bit(102, 0), bit(104, 1)];
            let introduced = vec![unit(103), bit(102, 0), bit(104, 1)];
            let arranged = vec![unit(103), bit(104, 1), bit(102, 0)];
            let prepared = vec![bit(105, 1), bit(102, 0)];
            let pair = vec![bit(102, 0), bit(105, 1)];
            let after = vec![bit(116, 0), bit(117, 1)];
            let epsilon = e.structural(&[unit(101)], &[], "unpack_unit");
            let idle = e.rewire(&rest, &rest, &[0, 1], &[0, 1]);
            let finish = e.tensor(&before, &rest, epsilon, idle);
            let eta = e.structural(&[], &[unit(103)], "pack_unit");
            let eta = e.tensor(&rest, &introduced, eta, idle);
            let arrange = e.rewire(&introduced, &arranged, &[0, 2, 1], &[1, 0]);
            let prepare = e.prepared_bit(103, 104, 105, 1);
            let retained = e.rewire(&[bit(102, 0)], &[bit(102, 0)], &[0], &[0]);
            let prepare = e.tensor(&arranged, &prepared, prepare, retained);
            let route = e.rewire(&prepared, &pair, &[1, 0], &[1, 0]);

            // Independently spell the actual ordinary X body H Z H. For the
            // negative equation Z is replaced by I, so H I H is exactly I.
            // All coefficients are phase-fixed and the same ordered context
            // is retained; no producer matrix or source name grants equality.
            let h_first = e.hadamard(&[bit(108, 0)], &[bit(109, 0)]);
            let z_before = vec![bit(110, 0)];
            let z_after = vec![bit(111, 0)];
            let z = e.add(
                &z_before,
                &z_before,
                &format!(
                    r#"{{"tag":"phase","j":{},"k":1}}"#,
                    if wrong { 0 } else { 1 },
                ),
            );
            let z_rename = e.rewire(&z_before, &z_after, &[0], &[0]);
            let z_step = e.sequence(&z_before, &z_after, &[z, z_rename]);
            let z_root = e.sequence(&z_before, &z_after, &[z_step]);
            let enter_z = e.rewire(&[bit(109, 0)], &z_before, &[0], &[0]);
            let leave_z = e.rewire(&z_after, &[bit(112, 0)], &[0], &[0]);
            let z_call = e.sequence(&[bit(109, 0)], &[bit(112, 0)], &[enter_z, z_root, leave_z]);
            let h_last = e.hadamard(&[bit(112, 0)], &[bit(113, 0)]);
            let x = e.sequence(&[bit(108, 0)], &[bit(113, 0)], &[h_first, z_call, h_last]);
            let x_identity = e.rewire(&[bit(108, 0)], &[bit(108, 0)], &[0], &[0]);
            let close_x = e.rewire(&[bit(113, 0)], &[bit(108, 0)], &[0], &[0]);
            let closed_x = e.sequence(&[bit(108, 0)], &[bit(108, 0)], &[x_identity, x, close_x]);
            let enter_x = e.rewire(&[bit(107, 1)], &[bit(108, 0)], &[0], &[0]);
            let leave_x = e.rewire(&[bit(108, 0)], &[bit(107, 1)], &[0], &[0]);
            let bound_x = e.sequence(
                &[bit(107, 1)],
                &[bit(107, 1)],
                &[enter_x, closed_x, leave_x],
            );
            let cnot_input = vec![bit(106, 0), bit(107, 1)];
            let cnot_output = vec![bit(114, 0), bit(115, 1)];
            let controlled = e.add(
                &cnot_input,
                &cnot_input,
                &format!(r#"{{"tag":"control","child":{bound_x},"polarity":true}}"#,),
            );
            let cnot_rename = e.rewire(&cnot_input, &cnot_output, &[0, 1], &[0, 1]);
            let cnot_step = e.sequence(&cnot_input, &cnot_output, &[controlled, cnot_rename]);
            let cnot = e.sequence(&cnot_input, &cnot_output, &[cnot_step]);
            let enter_cnot = e.rewire(&pair, &cnot_input, &[0, 1], &[0, 1]);
            let leave_cnot = e.rewire(&cnot_output, &after, &[0, 1], &[0, 1]);
            let cnot = e.sequence(&pair, &after, &[enter_cnot, cnot, leave_cnot]);
            let root = e.sequence(
                &before,
                &after,
                &[finish, eta, arrange, prepare, route, cnot],
            );
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
        "closed-zero" | "empty-classical" => (vec![], vec![bit(102, 0)]),
        "fresh-unit-phase" => (vec![], vec![bit(106, 0)]),
        "unit-zero" | "retained-unit" | "general-superposition" => {
            (vec![unit(101)], vec![bit(103, 0)])
        }
        "unit-phase" => (vec![unit(101)], vec![bit(106, 0)]),
        "caller-frame" => (vec![unit(101), bit(102, 0)], vec![bit(104, 1)]),
        "helper-phase" => (vec![unit(101), bit(102, 0)], vec![bit(107, 1)]),
        "basis-zero" => (vec![unit(101)], vec![bit(102, 0)]),
        "basis-phase-reference" => (vec![bit(101, 0), unit(102)], vec![bit(106, 1)]),
        "multi-init-order" => (vec![unit(101)], vec![bit(103, 0), bit(109, 1)]),
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

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn zero_basis_preparation_keeps_exact_phase_reference_and_physical_initialization() {
    for (name, text) in [
        (
            "basis-zero",
            "pub isometry fn entry(q:Q<Unit>)->Q<Bit>{basis q as () {0}}",
        ),
        (
            "basis-phase-reference",
            "pub isometry fn entry(r:Q<Bit>,u:Q<Unit>)->(Q<Bit>,Q<Bit>){(r,basis global_phase_eighth(u) as () {0})}",
        ),
    ] {
        let proposal = lower(text);
        let actual = json::parse(proposal.payload()).unwrap();
        assert_eq!(
            actual
                .field("preparation")
                .unwrap()
                .field("initializations")
                .unwrap()
                .array()
                .unwrap()
                .len(),
            1
        );
        let checked = kernel()
            .check_instrument_native(proposal.payload(), &request(&proposal, name, false))
            .unwrap();
        proposal
            .validate_initialization_moves_native(&checked)
            .unwrap();
        if name == "basis-phase-reference" {
            assert!(
                kernel()
                    .check_instrument_native(proposal.payload(), &request(&proposal, name, true))
                    .is_err(),
                "wrong exact phase must refuse"
            );
            let input = [[0.5, 0.0], [0.0, 0.5], [0.5, 0.0], [0.0, -0.5]];
            let output = checked.execute_instrument(&input, 2, limits()).unwrap();
            assert_eq!(output.branches.len(), 1);
            close(
                &output.branches[0],
                &[
                    phase(input[0]),
                    phase(input[1]),
                    [0.0; 2],
                    [0.0; 2],
                    phase(input[2]),
                    phase(input[3]),
                    [0.0; 2],
                    [0.0; 2],
                ],
            );
        } else {
            let output = checked
                .execute_instrument(&[[0.0, 1.0]], 1, limits())
                .unwrap();
            close(&output.branches[0], &[[0.0, 1.0], [0.0, 0.0]]);
        }
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
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

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn general_preparation_arrow_matches_independent_exact_request_and_reference() {
    let proposal = lower(
        "use std::state::init0;
        fn prepare(q:Q<Unit>)->Q<Bit>{finish(q);init0()}
        fn invoke[const U:Op<Unit -> Bit>](q:Q<Unit>)->Q<Bit> requires Applicable(U){U(q)}
        pub isometry fn entry(q:Q<Unit>)->Q<Bit>{invoke[prepare](q)}",
    );
    // Reuse the independently authored +1 Unit-elimination equation, with
    // fixed reviewed port placement; do not derive a target from this arrow.
    let checked = kernel()
        .check_instrument_native(proposal.payload(), &request(&proposal, "unit-zero", false))
        .unwrap();
    proposal
        .validate_initialization_moves_native(&checked)
        .unwrap();
    let input = [[0.2, 0.3], [-0.6, 0.4]];
    let output = checked.execute_instrument(&input, 2, limits()).unwrap();
    close(
        &output.branches[0],
        &[input[0], [0.0; 2], input[1], [0.0; 2]],
    );
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn general_arrow_native_valid_gate_substitution_fails_independent_exact_request() {
    let text = "use std::state::init0; use std::gate::x;
        fn prepare(q:Q<Unit>)->Q<Bit>{finish(q);h(init0())}
        fn invoke[const U:Op<Unit -> Bit>](q:Q<Unit>)->Q<Bit> requires Applicable(U){U(q)}
        pub isometry fn entry(q:Q<Unit>)->Q<Bit>{invoke[prepare](q)}";
    let valid = lower(text);
    let mut wrong = lower(&text.replace("h(init0())", "x(init0())"));
    assert_eq!(valid.events.len(), wrong.events.len());
    wrong.source = valid.source.clone();
    // The substituted X program is independently native-valid for its own
    // producer request; that fact cannot establish correspondence to H.
    let accepted = kernel()
        .check_instrument_native(wrong.payload(), wrong.comparison_request())
        .unwrap();
    // Ordinary init0 retains original basis intervals, activating complete
    // source replay. Native-valid X must now also fail that original H binding;
    // the independent exact H equation below remains a separate check.
    let error = wrong
        .validate_initialization_moves_native(&accepted)
        .unwrap_err();
    assert_eq!(error.code(), "preservation");
    let expected = request(&valid, "general-superposition", false);
    kernel()
        .check_instrument_native(valid.payload(), &expected)
        .unwrap();
    assert!(
        kernel()
            .check_instrument_native(wrong.payload(), &expected)
            .is_err()
    );
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

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
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

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
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

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn isometry_native_valid_phased_finish_cannot_implement_original_source() {
    let valid = lower(&source("unit-zero"));
    let wrong = lower(
        "\x20
         use std::state::init0;
         fn changed(q: Q<Unit>) -> Unit { finish(global_phase_eighth(q)) }
         pub isometry fn entry(q: Q<Unit>) -> Q<Bit> { changed(q); init0() }",
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
        // Ordinary init0 now retains its own exact source interval. The
        // substituted source collection fails that stronger binding first;
        // native validity and the independent omega amplitude remain above.
        "source event substitutes its original zero-basis interval"
    );
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
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

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn constructor_sequence_matches_independent_exact_equation_and_rejects_gate_substitution() {
    let original = current_source_text(
        "tests/fixtures/authoring_sessions/general-arrow-constructors-v030/attempt-01/sequence.qli",
    );
    // The current source uses bare language primitives; X is an ordinary gate
    // import required by the independently native-valid H-to-X counterexample.
    let source = format!("use std::gate::x;\n{original}");
    let valid = lower(&source);
    // The existing independently authored Unit elimination / H equation fixes
    // +1 structural action, both complex H columns and reviewed port placement.
    // No constructor-produced comparison request defines this expectation.
    let expected = request(&valid, "general-superposition", false);
    let checked = kernel()
        .check_instrument_native(valid.payload(), &expected)
        .unwrap();
    valid
        .validate_initialization_moves_native(&checked)
        .unwrap();
    let mut wrong = lower(&source.replace("{h(q)}", "{x(q)}"));
    wrong.source = valid.source.clone();
    let accepted = kernel()
        .check_instrument_native(wrong.payload(), wrong.comparison_request())
        .unwrap();
    // Complete source replay now retains this original constructor's H child.
    // Native acceptance of X cannot grant that correspondence; the independent
    // exact H request still supplies the separate mathematical counterexample.
    let error = wrong
        .validate_initialization_moves_native(&accepted)
        .unwrap_err();
    assert_eq!(error.code(), "preservation");
    assert!(
        kernel()
            .check_instrument_native(wrong.payload(), &expected)
            .is_err()
    );
}
