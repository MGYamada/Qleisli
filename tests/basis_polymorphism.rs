//! Exact opaque Basis substitutions and independent small-reference actions.
//! These bounded tests establish no generic/source-preservation theorem.
//! Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
use qleisli::frontend::compile::{BasisBinding, OperationBinding, ParsedProgram};
use qleisli::frontend::{
    ast::{StaticOpKind, StaticParamKind, TypeKind},
    parser::parse_module,
};
use qleisli::interchange::hierarchical::{Kernel, execution::ExecutionLimits};
use std::collections::BTreeMap;
mod common;

fn parsed(source: &str) -> ParsedProgram {
    ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap()
}
fn types(name: &str, ty: &str) -> BTreeMap<String, BasisBinding> {
    BTreeMap::from([(name.into(), BasisBinding::parse(ty).unwrap())])
}
fn study(name: &str) -> String {
    std::fs::read_to_string(common::current_namespace_fixture(
        &std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(format!(
            "tests/fixtures/authoring_sessions/basis-polymorphism-v030/attempt-02/{name}/main.qli"
        )),
    ))
    .unwrap()
}

#[test]
fn common_syntax_retains_basis_names_and_contextual_type_arguments() {
    let tree=parse_module("pub unitary fn f[static A:Basis](q:Q<A>)->Q<A>{q} pub unitary fn g(q:Q<Bit>)->Q<Bit>{f[type(Bit)](q)}").unwrap();
    assert!(matches!(
        tree.decls[0].static_params[0].kind,
        StaticParamKind::Basis
    ));
    assert!(
        matches!(&tree.decls[0].return_type.kind,TypeKind::Q(inner) if matches!(inner.kind,TypeKind::Named(_)))
    );
    let qleisli::frontend::ast::FnBody::Quantum(body) = &tree.decls[1].body else {
        panic!()
    };
    let qleisli::frontend::ast::ExprKind::Call { static_args, .. } = &body.result.kind else {
        panic!()
    };
    assert!(matches!(static_args[0].kind, StaticOpKind::Type(_)));
    // Ordinary runtime calls keep their original meaning and category.
    parsed("pub unitary fn type(q:Q<Bit>)->Q<Bit>{q} pub unitary fn f(q:Q<Bit>)->Q<Bit>{type(q)}");
    parsed("pub unitary fn f[static Bit:Nat](q:Q<Bits<Bit>>)->Q<Bits<Bit>>{q}");
}

#[test]
fn closed_bindings_preserve_tags_order_and_nesting_and_require_eof() {
    for (a, b) in [
        ("Bit", "Bits<1>"),
        ("Unit", "Bits<0>"),
        ("(Unit,Bit)", "(Bit,Unit)"),
        ("((Bit,Unit),Bit)", "(Bit,(Unit,Bit))"),
    ] {
        assert_ne!(
            BasisBinding::parse(a).unwrap(),
            BasisBinding::parse(b).unwrap()
        );
    }
    assert_eq!(
        BasisBinding::parse("Bits<1+1>").unwrap(),
        BasisBinding::parse("Bits<2>").unwrap()
    );
    for bad in [
        "Bit Bit",
        "Q<Bit>",
        "A",
        "Bits<n>",
        "Bits<1-2>",
        "Bits<4294967295+1>",
        "Bits<9>",
        "()",
        "(Bit,Q<Unit>)",
    ] {
        assert!(BasisBinding::parse(bad).is_err(), "{bad}");
    }
}

#[test]
fn unused_source_type_arguments_obey_the_same_closed_binding_capacity() {
    // Nine one-bit fields are a small type description, not an emitted or
    // executed maximum-size quantum case. An unused parameter cannot bypass
    // the closed Basis limit by avoiding Q and concrete interface checks.
    let p = parsed(
        "pub unitary fn unused[static A:Basis]()->Unit{()} pub unitary fn f()->Unit{unused[type((Bit,Bit,Bit,Bit,Bit,Bit,Bit,Bit,Bit))]()}",
    );
    let instance = p
        .instantiate("main::f", BTreeMap::new(), BTreeMap::new())
        .unwrap();
    let error = instance.elaborate().unwrap_err();
    assert_eq!(error.code(), "limit");
    assert!(error.message().contains("closed Basis binding"));
}

#[test]
fn all_first_opaque_rejections_reach_their_actual_rules_before_binding() {
    for (name, code) in [
        ("missing-access", "access"),
        ("abstract-split", "type"),
        ("duplicate-owner", "ownership"),
        ("assumed-unit", "ownership"),
        ("forward-kind", "type"),
        ("unknown-basis", "type"),
    ] {
        let error =
            ParsedProgram::parse(BTreeMap::from([("main".into(), study(name))])).unwrap_err();
        assert_eq!(error.code(), code, "{name}: {error}");
        assert_eq!(error.module(), Some("main"));
    }
    parsed(&study("opaque-repeat"));
    parsed(&study("opaque-forward"));
}

#[test]
fn unused_and_zero_iteration_bodies_do_not_gain_missing_access() {
    for body in [
        "U(q)",
        "qfor static i in 0..0 carry a=q {yield U(a)}",
        "if static 0 == 0 {q} else {U(q)}",
    ] {
        let source = format!(
            "pub unitary fn unused[static A:Basis,static U:Op<A>](q:Q<A>)->Q<A>{{{body}}} pub unitary fn good(q:Q<Bit>)->Q<Bit>{{q}}"
        );
        assert_eq!(
            ParsedProgram::parse(BTreeMap::from([("main".into(), source)]))
                .unwrap_err()
                .code(),
            "access"
        );
    }
    for source in [
        "pub unitary fn f[static U:Op<Bits<n>>,static n:Nat](q:Q<Bits<n>>)->Q<Bits<n>> requires Apply(U){U(q)}",
        "pub unitary fn f[static A:Basis](q:Q<A>)->Q<A>{let A=q;A}",
        "pub unitary fn f[static A:Basis,static B:Basis](q:Q<A>)->Q<B>{q}",
    ] {
        assert!(ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).is_err());
    }
}

#[test]
fn entry_and_provider_bindings_are_explicit_and_deterministic() {
    let source = "pub unitary fn id[static B:Basis](q:Q<B>)->Q<B>{q} pub unitary fn f[static A:Basis,static U:Op<A>](q:Q<A>)->Q<A> requires Apply(U){U(q)}";
    let p = parsed(source);
    let error = p
        .instantiate("main::f", BTreeMap::new(), BTreeMap::new())
        .unwrap_err();
    assert!(error.message().contains("Basis") && error.message().contains("missing [A]"));
    let extra = p
        .instantiate_with_types(
            "main::f",
            types("Z", "Bit"),
            BTreeMap::new(),
            BTreeMap::new(),
        )
        .unwrap_err();
    assert!(extra.message().contains("missing [A]") && extra.message().contains("unexpected [Z]"));
    let op = BTreeMap::from([(
        "U".into(),
        OperationBinding::new("main::id", BTreeMap::new()),
    )]);
    let missing = p
        .instantiate_with_types("main::f", types("A", "Bit"), BTreeMap::new(), op)
        .unwrap_err();
    assert!(
        missing.message().contains("provider main::id")
            && missing.message().contains("missing [B]")
    );
    for provider in ["Bits<1>", "(Unit,Bit)"] {
        let op = BTreeMap::from([(
            "U".into(),
            OperationBinding::with_types("main::id", types("B", provider), BTreeMap::new()),
        )]);
        assert_eq!(
            p.instantiate_with_types("main::f", types("A", "Bit"), BTreeMap::new(), op)
                .unwrap_err()
                .code(),
            "type"
        );
    }
    let op = BTreeMap::from([(
        "U".into(),
        OperationBinding::with_types("main::id", types("B", "Bit"), BTreeMap::new()),
    )]);
    p.instantiate_with_types("main::f", types("A", "Bit"), BTreeMap::new(), op)
        .unwrap()
        .elaborate()
        .unwrap();
}

#[test]
fn exact_type_substitutions_are_distinct_specialization_cache_keys() {
    let p = parsed(
        "pub unitary fn id[static A:Basis](q:Q<A>)->Q<A>{q} pub unitary fn f(a:Q<Bit>,b:Q<Bits<1>>)->(Q<Bit>,Q<Bits<1>>){(id[type(Bit)](a),id[type(Bits<1>)](b))}",
    );
    let e = p
        .instantiate("main::f", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap();
    let definitions = e
        .definitions()
        .iter()
        .filter(|d| d.path() == "main::id")
        .collect::<Vec<_>>();
    assert_eq!(definitions.len(), 2);
    assert_ne!(definitions[0].types(), definitions[1].types());
    assert_ne!(
        definitions[0].inputs()[0].ty(),
        definitions[1].inputs()[0].ty()
    );
}

#[test]
fn names_forward_the_resolved_type_without_width_coercion() {
    let p = parsed(&study("opaque-forward"));
    // Supply a source provider in the same retained source map.
    let text = format!(
        "{} pub unitary fn id[static B:Basis](q:Q<B>)->Q<B>{{q}}",
        p.source("main").unwrap()
    );
    let p = parsed(&text);
    for ty in ["Unit", "Bit", "Bits<1>", "(Unit,Bit)", "((Unit,Bit),Unit)"] {
        let op = BTreeMap::from([(
            "U".into(),
            OperationBinding::with_types("main::id", types("B", ty), BTreeMap::new()),
        )]);
        let e = p
            .instantiate_with_types("main::outer", types("A", ty), BTreeMap::new(), op)
            .unwrap()
            .elaborate()
            .unwrap();
        assert_eq!(
            e.definitions()[e.root()].types()["A"],
            BasisBinding::parse(ty).unwrap()
        );
        assert_eq!(
            e.definitions()[e.root()].inputs()[0].ty(),
            e.definitions()[e.root()].output().ty()
        );
    }
}

#[test]
fn selected_cli_type_and_provider_bindings_are_separate_from_runtime_basis() {
    let root = common::SourceRoot::new(
        "pub unitary fn id[static B:Basis](q:Q<B>)->Q<B>{q} pub unitary fn f[static A:Basis,static U:Op<A>](q:Q<A>)->Q<A> requires Apply(U){U(q)}",
    );
    let kernel = std::env::var_os("QLEISLI_KERNEL").expect("explicit audited native checker");
    for (ty, basis) in [("Unit", 0), ("Bit", 1), ("Bits<1>", 1), ("(Unit,Bit)", 1)] {
        for leading_format in [false, true] {
            let mut command = std::process::Command::new(env!("CARGO_BIN_EXE_qleisli"));
            if leading_format {
                command.arg("--format=json");
            } else {
                command.args(["run", "--format=json"]);
            }
            if leading_format {
                command.arg("run");
            }
            let output = command
                .arg("--entry=main::f")
                .arg(format!(
                    "--module=main={}",
                    root.0.join("main.qli").display()
                ))
                .arg(format!("--type=A={ty}"))
                .args(["--operation=U=main::id"])
                .arg(format!("--operation-type=U.B={ty}"))
                .arg(format!("--basis={basis}"))
                .arg(format!(
                    "--lean-kernel={}",
                    std::path::Path::new(&kernel).display()
                ))
                .output()
                .unwrap();
            assert!(output.status.success(), "{ty}: {output:?}");
            assert!(output.stderr.is_empty());
            let text = String::from_utf8(output.stdout).unwrap();
            assert!(text.contains("\"outcome\":\"ok\""), "{text}");
            assert!(text.contains("\"ir_profile\":\"hierarchy\""), "{text}");
            assert!(text.contains("\"source_meaning_verified\":false"), "{text}");
        }
    }
    for flags in [
        vec!["--type=A=Bit", "--type=A=Unit"],
        vec!["--operation-type=U.B=Bit"],
        vec!["--type=A="],
        vec!["--type=A=Bit", "--basis=0"],
    ] {
        let output = std::process::Command::new(env!("CARGO_BIN_EXE_qleisli"))
            .args(["check", "--format=json", "--entry=main::f"])
            .arg(format!(
                "--module=main={}",
                root.0.join("main.qli").display()
            ))
            .args(flags)
            .env_remove("QLEISLI_KERNEL")
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(2), "{output:?}");
        assert!(output.stderr.is_empty());
    }
}

#[test]
fn same_algorithm_retains_small_reference_action_and_unit_scalar_phase() {
    let kernel =
        Kernel::new(std::env::var_os("QLEISLI_KERNEL").expect("explicit audited native checker"));
    let source = "use std::quantum::{x,phase_eighth}; pub unitary fn flip(q:Q<Bit>)->Q<Bit>{x(q)} pub unitary fn scalar(q:Q<Unit>)->Q<Unit>{phase_eighth(q)} pub unitary fn repeat[static A:Basis,static k:Nat,static U:Op<A>](q:Q<A>)->Q<A> requires Apply(U),k<=4 {qfor static i in 0..k carry a=q {yield U(a)}}";
    let p = parsed(source);
    for (ty, provider, width) in [("Bit", "main::flip", 1), ("Unit", "main::scalar", 0)] {
        for n in 0..=4 {
            let e = p
                .instantiate_with_types(
                    "main::repeat",
                    types("A", ty),
                    BTreeMap::from([("k".into(), n)]),
                    BTreeMap::from([(
                        "U".into(),
                        OperationBinding::new(provider, BTreeMap::new()),
                    )]),
                )
                .unwrap()
                .elaborate()
                .unwrap();
            let proposal = e.lower().unwrap();
            let accepted = kernel
                .check_against_native(proposal.payload(), proposal.comparison_request())
                .unwrap();
            let input = (0..(2 << width))
                .map(|i| [(i + 1) as f64 / 7.0, (i as f64 - 2.0) / 11.0])
                .collect::<Vec<_>>();
            let actual = accepted
                .execute_pure(
                    &input,
                    2,
                    ExecutionLimits {
                        max_amplitudes: 16,
                        max_steps: 1000,
                    },
                )
                .unwrap()
                .amplitudes;
            let angle = f64::from(n) * std::f64::consts::FRAC_PI_4;
            let expected = if width == 0 {
                input
                    .iter()
                    .map(|[a, b]| {
                        [
                            a * angle.cos() - b * angle.sin(),
                            a * angle.sin() + b * angle.cos(),
                        ]
                    })
                    .collect::<Vec<_>>()
            } else {
                (0..input.len())
                    // Public execution layout: quantum basis varies fastest;
                    // each reference block has two system amplitudes.
                    .map(|i| input[i ^ (if n % 2 == 1 { 1 } else { 0 })])
                    .collect()
            };
            assert_eq!(actual.len(), expected.len());
            for (a, b) in actual.iter().flatten().zip(expected.iter().flatten()) {
                assert!(
                    (a - b).abs() < 1e-12,
                    "{ty}, k={n}: {actual:?} != {expected:?}"
                );
            }
        }
    }
}

#[test]
fn one_basis_nat_body_composes_with_original_refined_provider_requirements() {
    use qleisli::contract::{DEFAULT_EXACT_WORK, exact::Budget};
    let source = "use std::quantum::{x,phase_eighth};
        classical fn flip(b:Bit)->Bit{not b}
        classical fn angle(u:Unit)->(Bit,(Bit,Bit)){(1,(0,0))}
        meaning Flip:Bit=permutation_by(flip);
        meaning Eighth:Unit=phase_by(angle);
        pub unitary fn bit_provider(q:Q<Bit>)->Q<Bit>{x(q)}
        pub unitary fn unit_provider(q:Q<Unit>)->Q<Unit>{phase_eighth(q)}
        unitary fn run[static A:Basis,static n:Nat,static U:Op<A>](q:Q<A>)->Q<A>
            requires Apply(U),n<=2 {qfor static i in 0..n carry a=q {yield U(a)}}
        pub unitary fn bit[static n:Nat,static U:Op<Bit,Flip>](q:Q<Bit>)->Q<Bit>
            requires Apply(U),n<=2 {run[type(Bit),n,U](q)}
        pub unitary fn unit[static n:Nat,static U:Op<Unit,Eighth>](q:Q<Unit>)->Q<Unit>
            requires Apply(U),n<=2 {run[type(Unit),n,U](q)}";
    for honest in [false, true] {
        let text = if honest {
            source.into()
        } else {
            source
                .replace("{x(q)}", "{q}")
                .replace("{phase_eighth(q)}", "{q}")
        };
        let program = parsed(&text);
        for (entry, provider, width) in [("bit", "bit_provider", 1), ("unit", "unit_provider", 0)] {
            for n in 0..=2 {
                let elaborated = program
                    .instantiate(
                        &format!("main::{entry}"),
                        BTreeMap::from([("n".into(), n)]),
                        BTreeMap::from([(
                            "U".into(),
                            OperationBinding::new(format!("main::{provider}"), BTreeMap::new()),
                        )]),
                    )
                    .unwrap()
                    .elaborate()
                    .unwrap();
                let instances = elaborated
                    .definitions()
                    .iter()
                    .filter(|d| d.path() == "main::run")
                    .collect::<Vec<_>>();
                assert_eq!(instances.len(), 1);
                assert_eq!(instances[0].naturals()["n"], n);
                assert_eq!(
                    instances[0].types()["A"],
                    BasisBinding::parse(if entry == "bit" { "Bit" } else { "Unit" }).unwrap()
                );
                assert_eq!(
                    instances[0].inputs()[0].ty(),
                    elaborated.definitions()[elaborated.root()].inputs()[0].ty()
                );
                let checked = elaborated.check_operation_meanings(
                    &qleisli::interchange::native::Kernel::new(
                        std::env::var_os("QLEISLI_KERNEL").unwrap(),
                    ),
                    &mut Budget::new(DEFAULT_EXACT_WORK),
                );
                if !honest {
                    let e = checked.unwrap_err();
                    assert_eq!(e.code(), "contract", "{e}");
                    assert!(
                        e.message().contains(if entry == "bit" {
                            "main::Flip"
                        } else {
                            "main::Eighth"
                        }),
                        "{e}"
                    );
                    continue;
                }
                let graph = checked.unwrap().lower_hierarchy().unwrap();
                let accepted = Kernel::new(std::env::var_os("QLEISLI_KERNEL").unwrap())
                    .check_against_native(graph.payload(), graph.comparison_request())
                    .unwrap();
                let input = (0..(2 << width))
                    .map(|i| [(i + 1) as f64 / 7.0, (i as f64 - 2.0) / 11.0])
                    .collect::<Vec<_>>();
                let actual = accepted
                    .execute_pure(
                        &input,
                        2,
                        ExecutionLimits {
                            max_amplitudes: 16,
                            max_steps: 1000,
                        },
                    )
                    .unwrap()
                    .amplitudes;
                let angle = f64::from(n) * std::f64::consts::FRAC_PI_4;
                let expected = if width == 0 {
                    input
                        .iter()
                        .map(|[a, b]| {
                            [
                                a * angle.cos() - b * angle.sin(),
                                a * angle.sin() + b * angle.cos(),
                            ]
                        })
                        .collect::<Vec<_>>()
                } else {
                    (0..input.len())
                        .map(|i| input[i ^ (if n % 2 == 1 { 1 } else { 0 })])
                        .collect()
                };
                assert_eq!(actual.len(), expected.len());
                for (a, b) in actual.iter().flatten().zip(expected.iter().flatten()) {
                    assert!(
                        (a - b).abs() < 1e-12,
                        "{entry},n={n}: {actual:?} != {expected:?}"
                    );
                }
            }
        }
    }
}
