//! Selected nominal source executes through the existing typed native gate.
//! Exact request assertions and small runtime regressions are not preservation proofs.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
mod common;
use common::SourceRoot;
use qleisli::edition::Edition;
use qleisli::frontend::compile::{self, Instantiation, ParsedProgram};
use qleisli::interchange::native::Kernel;
use qleisli::sim::{SimulationLimits, run_closed};
use std::collections::BTreeMap;
use std::process::Command;

fn kernel() -> std::path::PathBuf {
    std::env::var_os("QLEISLI_KERNEL")
        .expect("explicit native test gate")
        .into()
}

fn instance(modules: &[(&str, &str)]) -> Instantiation {
    ParsedProgram::parse(
        Edition::E2026,
        modules
            .iter()
            .map(|(name, source)| (name.to_string(), source.to_string()))
            .collect(),
    )
    .unwrap()
    .instantiate_ordinary_with_types(
        "main::choose",
        Default::default(),
        Default::default(),
        Default::default(),
    )
    .unwrap()
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_ordinary_uses_actual_public_nominal_types_and_classical_bodies() {
    for (source, expected) in [
        (
            "pub enum Tri {A,B,C} pub classical fn choose()->Bit {match Tri::C {Tri::A=>0,Tri::B=>0,Tri::C=>1}}",
            vec![true],
        ),
        (
            "pub enum Tri {A,B,C} pub fn choose()->Tri {Tri::C}",
            vec![false, true],
        ),
        (
            "pub struct Empty {} pub fn choose()->Empty {Empty{}}",
            vec![],
        ),
        (
            "pub enum Tri {A,B,C} pub struct Empty {} pub struct Packet {pub flag:Bit,pub tag:Tri,pub empty:Empty} pub fn choose()->Packet {Packet{empty:Empty{},tag:Tri::C,flag:1}}",
            vec![true, false, true],
        ),
        (
            "pub enum Tri {A,B,C} classical fn flag()->Bit {match Tri::C {Tri::A=>0,Tri::B=>0,Tri::C=>1}} pub fn choose()->Bit {flag()}",
            vec![true],
        ),
        (
            "pub enum Tri {A,B,C} unitary fn unused(q:Q<Tri>)->Q<Tri>{q} pub fn choose()->Bit{1}",
            vec![true],
        ),
    ] {
        let original = instance(&[("main", source)]);
        let selected = original
            .compile_ordinary_with_kernel(&Kernel::new(kernel(), Edition::E2026))
            .unwrap();
        assert_eq!(selected.source().entry(), "main::choose");
        assert_eq!(selected.runtime_parameters(), 0);
        let request = selected
            .program()
            .ordinary_result()
            .expect("fresh native typed request");
        assert_eq!(request.declaration, "choose");
        assert!(request.parameters.is_empty());
        assert_eq!(request.input_rows, vec![Vec::<bool>::new()]);
        assert_eq!(
            run_closed(selected.program(), SimulationLimits::default()).unwrap(),
            BTreeMap::from([(expected, 1.0)])
        );
    }
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_ordinary_keeps_import_paths_and_every_nominal_input_row() {
    let classical = instance(&[("main","pub enum Tri{A,B,C} pub classical fn choose(value:Tri)->Tri {match value{Tri::A=>Tri::B,Tri::B=>Tri::C,Tri::C=>Tri::A}}")])
        .compile_ordinary_with_kernel(&Kernel::new(kernel(),Edition::E2026)).unwrap();
    assert_eq!(
        classical.program().ordinary_result().unwrap().input_rows,
        vec![vec![false, false], vec![true, false], vec![false, true]]
    );
    assert!(run_closed(classical.program(), SimulationLimits::default()).is_err());
    let selected = instance(&[
        ("main","use alias::Tri; pub fn choose(value:Tri)->Tri {match value {Tri::A=>Tri::B,Tri::B=>Tri::C,Tri::C=>Tri::A}}"),
        ("alias","pub use leaf::Tri;"),
        ("leaf","pub enum Tri {A,B,C}"),
    ]).compile_ordinary_with_kernel(&Kernel::new(kernel(), Edition::E2026)).unwrap();
    assert_eq!(selected.runtime_parameters(), 1);
    assert_eq!(
        selected.program().ordinary_result().unwrap().input_rows,
        vec![vec![false, false], vec![true, false], vec![false, true]]
    );
    assert!(run_closed(selected.program(), SimulationLimits::default()).is_err());
    for ty in ["Empty", "Unit", "Bits<0>", "(Unit,Empty)"] {
        let source = format!("pub struct Empty {{}} pub fn choose(value:{ty})->{ty} {{value}}");
        let empty = instance(&[("main", &source)])
            .compile_ordinary_with_kernel(&Kernel::new(kernel(), Edition::E2026))
            .unwrap();
        assert_eq!(empty.runtime_parameters(), 1);
        assert_eq!(
            empty.program().ordinary_result().unwrap().parameters.len(),
            1
        );
        assert!(run_closed(empty.program(), SimulationLimits::default()).is_err());
        assert!(
            qleisli::sim::sample_closed(
                empty.program(),
                &mut qleisli::sim::SplitMix64::new(0),
                qleisli::sim::SampleLimits::default()
            )
            .is_err()
        );
    }
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_ordinary_discharges_unused_function_equalities_in_both_effect_profiles() {
    let kernel = Kernel::new(kernel(), Edition::E2026);
    for observing in [false, true] {
        for honest in [false, true] {
            for dead_branch in [false, true] {
                let (kind, result, implementation, reference) = if observing {
                    (
                        "observe",
                        "Bit",
                        "measure_z(q)",
                        if honest {
                            "measure_z(q)"
                        } else {
                            "measure_z(h(q))"
                        },
                    )
                } else {
                    ("unitary", "Q<Bit>", "q", if honest { "q" } else { "h(q)" })
                };
                let contract = "apply_contract(implementation,reference,q)";
                let body = if dead_branch {
                    format!("if 0 {{{contract}}}else{{{implementation}}}")
                } else {
                    contract.into()
                };
                let source = format!(
                    "pub struct Empty{{}} pub fn choose()->Bit{{0}}
                    {kind} fn implementation(q:Q<Bit>)->{result}{{{implementation}}}
                    {kind} fn reference(q:Q<Bit>)->{result}{{{reference}}}
                    {kind} fn unused[const U:Op<Bit>](q:Q<Bit>)->{result}{{{body}}}"
                );
                let original = instance(&[("main", &source)]);
                let checked = original.compile_ordinary_with_kernel(&kernel);
                if honest {
                    assert_eq!(
                        run_closed(checked.unwrap().program(), SimulationLimits::default())
                            .unwrap(),
                        BTreeMap::from([(vec![false], 1.0)])
                    );
                } else {
                    assert_eq!(checked.unwrap_err().code, "contract");
                }
            }
        }
    }
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_ordinary_prepares_meanings_for_unused_refined_and_zero_repeat_operations() {
    let kernel = Kernel::new(kernel(), Edition::E2026);
    for mode in 0..4 {
        for honest in [false, true] {
            let parameter = if mode == 1 { "Op<Bit,Flip>" } else { "Op<Bit>" };
            let actual = match mode {
                0 | 3 => "checked_op(implementation,Flip)",
                1 => "implementation",
                _ => "power(checked_op(implementation,Flip),0)",
            };
            let meaning = if mode == 3 {
                "unitary fn reference(q:Q<Bit>)->Q<Bit>{x(q)} meaning Flip:Bit=reference(reference);"
            } else {
                "classical fn flip(b:Bit)->Bit{not b} meaning Flip:Bit=permutation_by(flip);"
            };
            let source = format!(
                "use std::gate::x; pub struct Empty{{}}
                {meaning}
                unitary fn implementation(q:Q<Bit>)->Q<Bit>{{{}}}
                unitary fn run[const U:{parameter}](q:Q<Bit>)->Q<Bit> requires Applicable(U){{U(q)}}
                unitary fn unused(q:Q<Bit>)->Q<Bit>{{run[{actual}](q)}}
                pub fn choose()->Bit{{0}}",
                if honest { "x(q)" } else { "q" }
            );
            let original = instance(&[("main", &source)]);
            let checked = original.compile_ordinary_with_kernel(&kernel);
            if honest {
                assert!(checked.is_ok(), "{checked:?}");
            } else {
                assert_eq!(checked.unwrap_err().code, "contract");
            }
        }
    }
    // Meaning preparation follows original import/declaration dependencies;
    // an alias spelling cannot replace the canonical Meaning definition.
    let original = instance(&[
        (
            "main",
            "use facade::Flip;use implementation::gate;pub struct Empty{} pub fn choose()->Bit{0}
         unitary fn run[const U:Op<Bit,Flip>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}
         unitary fn unused(q:Q<Bit>)->Q<Bit>{run[gate](q)}",
        ),
        ("facade", "pub use oracle::Flip;"),
        (
            "oracle",
            "classical fn flip(b:Bit)->Bit{not b}pub meaning Flip:Bit=permutation_by(flip);",
        ),
        (
            "implementation",
            "use std::gate::x;pub unitary fn gate(q:Q<Bit>)->Q<Bit>{x(q)}",
        ),
    ]);
    assert!(original.compile_ordinary_with_kernel(&kernel).is_ok());
    // The global dormant pass skips primitive-call plans. Such a site must
    // not make its unused owner's unrelated table a concrete selected root.
    let source = "pub struct Empty{} pub fn choose()->Bit{0}
        classical fn passthrough(value:Bits<13>)->Bits<13>{value}
        fn unused(head:Bit,tail:Bits<12>)->Bits<13>{passthrough(prepend_bit[12](head,tail))}";
    assert!(
        instance(&[("main", source)])
            .compile_ordinary_with_kernel(&kernel)
            .is_ok()
    );
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_main_uses_exported_eligibility_while_project_main_keeps_its_contract() {
    let kernel = Kernel::new(kernel(), Edition::E2026);
    for text in [
        "pub enum Tri{A,B,C}pub fn main(value:Tri)->Tri{value}",
        "pub enum Tri{A,B,C}pub classical fn main()->Bit{0}",
    ] {
        let parsed = ParsedProgram::parse(
            Edition::E2026,
            BTreeMap::from([("main".into(), text.into())]),
        )
        .unwrap();
        let source = parsed
            .instantiate_ordinary_with_types(
                "main::main",
                Default::default(),
                Default::default(),
                Default::default(),
            )
            .unwrap();
        let checked = source.compile_ordinary_with_kernel(&kernel).unwrap();
        assert_eq!(
            checked.program().ordinary_result().unwrap().selection,
            qleisli::interchange::ordinary_root::Selection::Exported
        );
        if checked.runtime_parameters() == 0 {
            assert_eq!(
                run_closed(checked.program(), SimulationLimits::default()).unwrap(),
                BTreeMap::from([(vec![false], 1.0)])
            );
        } else {
            assert_eq!(
                checked
                    .program()
                    .ordinary_result()
                    .unwrap()
                    .input_rows
                    .len(),
                3
            );
            assert!(run_closed(checked.program(), SimulationLimits::default()).is_err());
        }
        assert_eq!(
            compile::compile_project(&SourceRoot::new(text).0)
                .unwrap_err()
                .code,
            compile::ErrorCode::InvalidEntry
        );
    }
    let private = "pub struct Empty{}fn main()->Bit{0}";
    assert!(compile::compile_project(&SourceRoot::new(private).0).is_ok());
    let parsed = ParsedProgram::parse(
        Edition::E2026,
        BTreeMap::from([("main".into(), private.into())]),
    )
    .unwrap();
    assert!(
        parsed
            .instantiate_ordinary_with_types(
                "main::main",
                Default::default(),
                Default::default(),
                Default::default()
            )
            .is_err()
    );
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_ordinary_prepares_only_tables_demanded_by_dormant_operations() {
    let kernel = Kernel::new(kernel(), Edition::E2026);
    for predicate in [
        "classical fn predicate(b:Bit)->Bit{b}",
        "classical fn helper(b:Bit)->Bit{not b}classical fn predicate(b:Bit)->Bit{helper(b)}",
    ] {
        for controlled in [false, true] {
            let dormant = if controlled {
                "unitary fn keep(q:Q<Bit>)->Q<Bit>{q}
                 unitary fn unused(s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){qif(s,q){0=>keep,1=>oracle}}"
            } else {
                "unitary fn run[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}
                 unitary fn unused(q:Q<Bit>)->Q<Bit>{run[oracle](q)}"
            };
            let source = format!(
                "use std::gate::z;pub struct Empty{{}}pub fn choose()->Bit{{0}}
                 {predicate}
                 unitary fn oracle(q:Q<Bit>)->Q<Bit>{{with_computed(q,predicate){{|a|z(a)}}}}
                 {dormant}"
            );
            let checked = instance(&[("main", &source)])
                .compile_ordinary_with_kernel(&kernel)
                .unwrap();
            assert_eq!(
                run_closed(checked.program(), SimulationLimits::default()).unwrap(),
                BTreeMap::from([(vec![false], 1.0)])
            );
        }
    }
    let imported = instance(&[
        (
            "main",
            "use oracle::oracle;pub struct Empty{}pub fn choose()->Bit{0}
             unitary fn run[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}
             unitary fn unused(q:Q<Bit>)->Q<Bit>{run[oracle](q)}",
        ),
        (
            "oracle",
            "use std::gate::z;use predicate::predicate;
             pub unitary fn oracle(q:Q<Bit>)->Q<Bit>{with_computed(q,predicate){|a|z(a)}}",
        ),
        (
            "predicate",
            "classical fn helper(b:Bit)->Bit{not b}
             pub classical fn predicate(b:Bit)->Bit{helper(b)}",
        ),
    ]);
    assert!(imported.compile_ordinary_with_kernel(&kernel).is_ok());
    let nominal = instance(&[(
        "main",
        "use std::gate::z;pub struct Empty{}enum E{A}pub fn choose()->Bit{0}
         classical fn predicate(b:Bit)->Bit{match E::A{E::A=>b}}
         unitary fn oracle(q:Q<Bit>)->Q<Bit>{with_computed(q,predicate){|a|z(a)}}
         unitary fn run[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}
         unitary fn unused(q:Q<Bit>)->Q<Bit>{run[oracle](q)}",
    )]);
    let refused = nominal.compile_ordinary_with_kernel(&kernel).unwrap_err();
    assert_eq!(refused.code, "unsupported");
    assert!(
        refused
            .message
            .contains("finite tables require closed built-in")
    );
    let unrelated = instance(&[(
        "main",
        "pub struct Empty{}pub fn choose()->Bit{0}
         classical fn passthrough(value:Bits<13>)->Bits<13>{value}
         fn unused(head:Bit,tail:Bits<12>)->Bits<13>{passthrough(prepend_bit[12](head,tail))}",
    )]);
    assert!(unrelated.compile_ordinary_with_kernel(&kernel).is_ok());
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_ordinary_refuses_quantum_and_generic_routes_without_fallback() {
    let program = ParsedProgram::parse(
        Edition::E2026,
        BTreeMap::from([(
            "main".into(),
            "pub enum Tri{A,B,C} pub fn choose[const A:Basis](v:A)->A{v}".into(),
        )]),
    )
    .unwrap();
    let original = program
        .instantiate_ordinary_with_types(
            "main::choose",
            BTreeMap::from([("A".into(), program.basis_binding("main::Tri").unwrap())]),
            Default::default(),
            Default::default(),
        )
        .unwrap();
    let kernel = Kernel::new(kernel(), Edition::E2026);
    assert!(
        original
            .compile_ordinary_with_kernel(&kernel)
            .unwrap_err()
            .message
            .contains("static-binder")
    );
    let original = instance(&[(
        "main",
        "pub enum Tri {A,B,C} pub observe fn choose()->Tri {let b=measure_z(init0()); if b {Tri::A}else{Tri::C}}",
    )]);
    assert!(original.compile_ordinary_with_kernel(&kernel).is_err());
    let absent = Kernel::new("/nonexistent/qleisli-native-selected-test", Edition::E2026);
    assert!(
        instance(&[("main", "pub enum Tri {A,B,C} pub fn choose()->Tri{Tri::C}")])
            .compile_ordinary_with_kernel(&absent)
            .is_err()
    );
}

fn cli(root: &SourceRoot, action: &str) -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_qleisli"));
    command
        .arg(action)
        .arg("--entry=main::choose")
        .arg("--format=json")
        .arg("--ir-profile=raw")
        .arg(format!(
            "--module=main={}",
            root.0.join("main.qli").display()
        ));
    if action != "emit-proposal" {
        command.arg(format!("--lean-kernel={}", kernel().display()));
    }
    command
}

#[test]
fn selected_ordinary_preparation_preserves_visibility_bindings_and_unused_checks() {
    for source in [
        "pub enum Tri{A,B,C} fn broken()->Bit{()} pub fn choose()->Tri{Tri::C}",
        "pub enum Tri{A,B,C} pub unitary fn choose()->Tri{let b=measure_z(init0()); if b{Tri::A}else{Tri::C}}",
        "pub enum Tri{A,B,C} fn unused(v:Tri)->Bit{match v{Tri::A=>0}} pub fn choose()->Tri{Tri::C}",
    ] {
        assert!(
            ParsedProgram::parse(
                Edition::E2026,
                BTreeMap::from([("main".into(), source.into())])
            )
            .is_err()
        );
    }
    let private = ParsedProgram::parse(
        Edition::E2026,
        BTreeMap::from([(
            "main".into(),
            "pub enum Tri{A,B,C} fn choose()->Tri{Tri::C}".into(),
        )]),
    )
    .unwrap();
    assert!(
        private
            .instantiate_ordinary_with_types(
                "main::choose",
                Default::default(),
                Default::default(),
                Default::default()
            )
            .is_err()
    );
    let public = ParsedProgram::parse(
        Edition::E2026,
        BTreeMap::from([(
            "main".into(),
            "pub enum Tri{A,B,C} pub fn choose()->Tri{Tri::C}".into(),
        )]),
    )
    .unwrap();
    assert!(
        public
            .instantiate_ordinary_with_types(
                "main::choose",
                BTreeMap::from([("unused".into(), public.basis_binding("main::Tri").unwrap())]),
                Default::default(),
                Default::default()
            )
            .is_err()
    );
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_ordinary_preserves_word_and_call_depth_capacity() {
    let wide = ParsedProgram::parse(
        Edition::E2026,
        BTreeMap::from([(
            "main".into(),
            "pub enum Tri{A,B,C} pub fn choose(value:Bits<9>)->Bit{0}".into(),
        )]),
    )
    .unwrap();
    let error = wide
        .instantiate_ordinary_with_types(
            "main::choose",
            Default::default(),
            Default::default(),
            Default::default(),
        )
        .unwrap_err();
    assert_eq!(error.code(), "limit");
    let mut source = "pub enum Tri{A,B,C} pub fn choose()->Bit{f0()}\n".to_string();
    for i in 0..18 {
        source.push_str(&format!("fn f{i}()->Bit{{f{}()}}\n", i + 1));
    }
    source.push_str("fn f18()->Bit{1}\n");
    let deep = instance(&[("main", &source)]);
    assert_eq!(
        deep.compile_ordinary_with_kernel(&Kernel::new(kernel(), Edition::E2026))
            .unwrap_err()
            .code,
        "limit"
    );
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn selected_ordinary_cli_reports_actual_typed_scope_and_preserves_export_refusal() {
    let root = SourceRoot::new("pub enum Tri {A,B,C} pub fn choose()->Tri{Tri::C}");
    for action in ["check", "run"] {
        let result = cli(&root, action).output().unwrap();
        assert!(result.status.success(), "{result:?}");
        let text = String::from_utf8(result.stdout).unwrap();
        for fragment in [
            "\"scope\":\"finite-ordinary-root-v2\"",
            "\"ordinary_result_checked\":true",
            "\"source_meaning_verified\":false",
            "\"native_check_scope\":\"selected-specialization\"",
        ] {
            assert!(text.contains(fragment), "{text}");
        }
    }
    let output = root.0.join("proposal.qirf");
    let result = cli(&root, "emit-proposal")
        .arg(format!("--output={}", output.display()))
        .output()
        .unwrap();
    assert!(!result.status.success());
    assert!(!output.exists());
    assert!(
        String::from_utf8(result.stdout)
            .unwrap()
            .contains("complete typed request transport")
    );
    let root = SourceRoot::new("pub struct Empty {} pub fn choose(value:Empty)->Empty{value}");
    assert!(cli(&root, "check").output().unwrap().status.success());
    let result = cli(&root, "run").output().unwrap();
    assert!(!result.status.success());
    assert!(
        String::from_utf8(result.stdout)
            .unwrap()
            .contains("zero runtime parameters")
    );
}
