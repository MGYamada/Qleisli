//! Independent bounded contracts for ordinary/coherent reuse of classical functions.
//! These checks do not establish source preservation or a new guarantee.
//! Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
mod common;

use common::SourceRoot;
use qleisli::frontend::ast::{FnBody, FnKind};
use qleisli::frontend::compile::{check_project_with_kernel, compile_project_with_kernel};
use qleisli::frontend::parser::parse_module;
use qleisli::frontend::project::SourcePolicy;
use qleisli::frontend::sized::{ElaboratedProgram, ParsedProgram};
use qleisli::interchange::native::{AcceptedProgram, Kernel};
use qleisli::ir::{Effect, RawOp};
use qleisli::sim::{SimulationError, SimulationLimits, run_closed};
use std::collections::BTreeMap;

macro_rules! first_source {
    ($case:literal) => {
        include_str!(concat!(
            "fixtures/authoring_sessions/classical-runtime-v030/attempt-01/",
            $case,
            "/main.qli"
        ))
    };
}

fn kernel() -> Kernel {
    Kernel::new(std::env::var_os("QLEISLI_KERNEL").expect("explicit native checker"))
}

#[test]
fn explicit_checked_op_checks_unused_and_zero_repeat_children() {
    use qleisli::contract::{DEFAULT_EXACT_WORK, exact::Budget};
    use qleisli::interchange::hierarchical;
    let original = include_str!(
        "fixtures/authoring_sessions/meaning-enforcement-v030/explicit-attempt-01/main.qli"
    );
    for zero_repeat in [false, true] {
        for honest in [false, true] {
            let text = if zero_repeat {
                original.replace(
                    "unused[checked_op(implementation,Flip)]",
                    "unused[repeat_op(0,checked_op(implementation,Flip))]",
                )
            } else {
                original.to_owned()
            };
            let text = if honest {
                text
            } else {
                text.replace("{x(q)}", "{q}")
            };
            let source = ParsedProgram::parse(BTreeMap::from([("main".into(), text)]))
                .unwrap()
                .instantiate("main::client", BTreeMap::new(), BTreeMap::new())
                .unwrap()
                .elaborate()
                .unwrap();
            assert!(source.has_operation_meanings());
            assert_eq!(source.lower().unwrap_err().code(), "meaning");
            assert_eq!(source.lower_raw().unwrap_err().code(), "meaning");
            let checked =
                source.check_operation_meanings(&kernel(), &mut Budget::new(DEFAULT_EXACT_WORK));
            if !honest {
                let error = checked.unwrap_err();
                assert_eq!(error.code(), "contract", "{error}");
                assert!(error.message().contains("main::Flip"), "{error}");
                continue;
            }
            assert_eq!(checked.as_ref().unwrap().checked_bindings(), 1);
            let graph = checked.unwrap().lower_hierarchy().unwrap();
            let accepted = hierarchical::Kernel::new(std::env::var_os("QLEISLI_KERNEL").unwrap())
                .check_against_native(graph.payload(), graph.comparison_request())
                .unwrap();
            // The unused provider must be checked without executing it. Its
            // annotation also survives a zero-count wrapper.
            let input = vec![[0.1, -0.2], [0.3, 0.4], [-0.5, 0.6], [0.7, -0.8]];
            let actual = accepted
                .execute_pure(
                    &input,
                    2,
                    hierarchical::execution::ExecutionLimits {
                        max_amplitudes: 16,
                        max_steps: 1000,
                    },
                )
                .unwrap()
                .amplitudes;
            assert_eq!(actual, input);
        }
    }
}

#[test]
fn explicit_checked_op_direct_step_and_forwarded_requests_are_not_overwritten() {
    use qleisli::contract::{DEFAULT_EXACT_WORK, exact::Budget};
    use qleisli::interchange::hierarchical;
    let prelude = "use std::quantum::x;
        classical fn flip(b:Bit)->Bit{not b}
        classical fn ident(b:Bit)->Bit{b}
        meaning Flip:Bit=permutation_by(flip);
        meaning Identity:Bit=permutation_by(ident);
        unitary fn implementation(q:Q<Bit>)->Q<Bit>{x(q)}";
    for (body, honest) in [
        ("pub unitary fn client(q:Q<Bit>)->Q<Bit>{adjoint(checked_op(implementation,Flip),q)}", true),
        ("pub unitary fn client(q:Q<Bit>)->Q<Bit>{adjoint(checked_op(implementation,Identity),q)}", false),
        ("unitary fn inner[static U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Apply(U){q}
          unitary fn outer[static U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Apply(U){inner[checked_op(U,Identity)](q)}
          pub unitary fn client(q:Q<Bit>)->Q<Bit>{outer[checked_op(implementation,Flip)](q)}", false),
        ("unitary fn inner[static U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Apply(U){q}
          unitary fn outer[static U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Apply(U){inner[checked_op(U,Flip)](q)}
          pub unitary fn client(q:Q<Bit>)->Q<Bit>{outer[checked_op(implementation,Identity)](q)}", false),
    ] {
        let source = ParsedProgram::parse(BTreeMap::from([("main".into(),format!("{prelude}{body}"))]))
            .unwrap().instantiate("main::client",BTreeMap::new(),BTreeMap::new())
            .unwrap().elaborate().unwrap();
        assert!(source.has_operation_meanings());
        let checked = source.check_operation_meanings(&kernel(), &mut Budget::new(DEFAULT_EXACT_WORK));
        if !honest {
            let error = checked.unwrap_err();
            assert_eq!(error.code(), "contract", "{error}");
            assert!(error.message().contains("main::Identity"), "{error}");
            continue;
        }
        let graph = checked.unwrap().lower_hierarchy().unwrap();
        let accepted = hierarchical::Kernel::new(std::env::var_os("QLEISLI_KERNEL").unwrap())
            .check_against_native(graph.payload(), graph.comparison_request()).unwrap();
        let input = vec![[0.1,-0.2],[0.3,0.4],[-0.5,0.6],[0.7,-0.8]];
        let actual = accepted.execute_pure(&input,2,hierarchical::execution::ExecutionLimits {
            max_amplitudes:16,max_steps:1000,
        }).unwrap().amplitudes;
        assert_eq!(actual,(0..4).map(|i|input[i^1]).collect::<Vec<_>>());
    }
}

#[test]
fn selected_cli_checks_explicit_requests_without_a_refined_formal() {
    let original = include_str!(
        "fixtures/authoring_sessions/meaning-enforcement-v030/explicit-attempt-01/main.qli"
    );
    for honest in [true, false] {
        let root = SourceRoot::new(&if honest {
            original.into()
        } else {
            original.replace("{x(q)}", "{q}")
        });
        for legacy in [false, true] {
            for profile in ["auto", "hierarchy", "raw"] {
                let mut command = std::process::Command::new(env!("CARGO_BIN_EXE_qleisli"));
                if legacy {
                    command.arg("sized");
                }
                let result = command
                    .args(["check", "--entry=main::client"])
                    .arg(format!(
                        "--module=main={}",
                        root.0.join("main.qli").display()
                    ))
                    .arg(format!("--ir-profile={profile}"))
                    .env(
                        "QLEISLI_KERNEL",
                        std::env::var_os("QLEISLI_KERNEL").unwrap(),
                    )
                    .output()
                    .unwrap();
                assert_eq!(
                    result.status.success(),
                    honest && profile != "raw",
                    "{honest}/{legacy}/{profile}: {} {}",
                    String::from_utf8_lossy(&result.stdout),
                    String::from_utf8_lossy(&result.stderr)
                );
                if !honest && profile != "raw" {
                    assert!(String::from_utf8_lossy(&result.stderr).contains("original Meaning"));
                }
            }
        }
    }
}

#[test]
fn explicit_scalar_request_is_checked_before_adjoint_and_keeps_exact_phase() {
    use qleisli::contract::{DEFAULT_EXACT_WORK, exact::Budget};
    use qleisli::interchange::hierarchical;
    let text = "use std::quantum::phase_eighth;
        classical fn angle(u:Unit)->(Bit,(Bit,Bit)){(1,(0,0))}
        meaning Eighth:Unit=phase_by(angle);
        unitary fn implementation(q:Q<Unit>)->Q<Unit>{phase_eighth(q)}
        pub unitary fn client(q:Q<Unit>)->Q<Unit>{adjoint(checked_op(implementation,Eighth),q)}";
    let source = ParsedProgram::parse(BTreeMap::from([("main".into(), text.into())]))
        .unwrap()
        .instantiate("main::client", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap();
    let checked = source
        .check_operation_meanings(&kernel(), &mut Budget::new(DEFAULT_EXACT_WORK))
        .unwrap();
    assert_eq!(checked.checked_bindings(), 1);
    let graph = checked.lower_hierarchy().unwrap();
    let accepted = hierarchical::Kernel::new(std::env::var_os("QLEISLI_KERNEL").unwrap())
        .check_against_native(graph.payload(), graph.comparison_request())
        .unwrap();
    let input = vec![[0.3, 0.4], [-0.5, 0.6]];
    let actual = accepted
        .execute_pure(
            &input,
            2,
            hierarchical::execution::ExecutionLimits {
                max_amplitudes: 4,
                max_steps: 1000,
            },
        )
        .unwrap()
        .amplitudes;
    let s = std::f64::consts::FRAC_1_SQRT_2;
    for ([a, b], [x, y]) in input.into_iter().zip(actual) {
        assert!((x - s * (a + b)).abs() < 1e-12);
        assert!((y - s * (b - a)).abs() < 1e-12);
    }
}

#[test]
fn original_annotations_check_every_nested_and_unused_provider_before_lowering() {
    use qleisli::contract::{DEFAULT_EXACT_WORK, exact::Budget};
    use qleisli::frontend::sized::OperationBinding;
    use qleisli::interchange::hierarchical;
    let bit =
        include_str!("fixtures/authoring_sessions/meaning-enforcement-v030/attempt-01/bit.qli");
    let unit =
        include_str!("fixtures/authoring_sessions/meaning-enforcement-v030/attempt-01/unit.qli");
    for (text, nested) in [(bit, 2), (unit, 1)] {
        for (entry, count) in [("outer", nested), ("unused", 1)] {
            let parsed =
                ParsedProgram::parse(BTreeMap::from([("main".into(), text.into())])).unwrap();
            let source = parsed
                .instantiate(
                    &format!("main::{entry}"),
                    BTreeMap::new(),
                    BTreeMap::from([(
                        "U".into(),
                        OperationBinding::new("main::implementation", BTreeMap::new()),
                    )]),
                )
                .unwrap()
                .elaborate()
                .unwrap();
            assert!(source.has_operation_meanings());
            assert_eq!(source.lower().unwrap_err().code(), "meaning");
            assert_eq!(source.lower_raw().unwrap_err().code(), "meaning");
            let leaf = source.lower_raw_operation("U").unwrap();
            let target = parsed
                .finite_meaning_target(if nested == 2 {
                    "main::Flip"
                } else {
                    "main::Minus"
                })
                .unwrap();
            let mut one_budget = Budget::new(DEFAULT_EXACT_WORK);
            one_budget.charge(leaf.payload().len()).unwrap();
            let one = leaf
                .check_finite_meaning(&kernel(), &target, &mut one_budget)
                .unwrap();
            assert_eq!(one.lower_hierarchy().unwrap_err().code(), "meaning");
            if count == 2 {
                let first_cost = DEFAULT_EXACT_WORK - one_budget.remaining();
                assert_eq!(
                    source
                        .check_operation_meanings(&kernel(), &mut Budget::new(first_cost))
                        .unwrap_err()
                        .code(),
                    "limit",
                    "all bindings must share one budget"
                );
            }
            let all = source
                .check_operation_meanings(&kernel(), &mut Budget::new(DEFAULT_EXACT_WORK))
                .unwrap();
            assert_eq!(all.checked_bindings(), count);
            let graph = all.lower_hierarchy().unwrap();
            let actual = hierarchical::Kernel::new(std::env::var_os("QLEISLI_KERNEL").unwrap())
                .check_against_native(graph.payload(), graph.comparison_request())
                .unwrap();
            let input = if nested == 2 {
                vec![[0.1, -0.2], [0.3, 0.4], [-0.5, 0.6], [0.7, -0.8]]
            } else {
                vec![[0.1, -0.2], [0.3, 0.4]]
            };
            let expected = if entry == "unused" {
                input.clone()
            } else if nested == 2 {
                (0..4).map(|i| input[i ^ 1]).collect()
            } else {
                input.iter().map(|[a, b]| [-a, -b]).collect()
            };
            let output = actual
                .execute_pure(
                    &input,
                    2,
                    hierarchical::execution::ExecutionLimits {
                        max_amplitudes: 16,
                        max_steps: 1000,
                    },
                )
                .unwrap()
                .amplitudes;
            assert_eq!(output, expected, "{entry}, {nested}");
            assert_eq!(
                source
                    .check_operation_meanings(&kernel(), &mut Budget::new(1))
                    .unwrap_err()
                    .code(),
                "limit"
            );
            let missing = Kernel::new("/nonexistent/qleisli-native-checker");
            assert!(
                source
                    .check_operation_meanings(&missing, &mut Budget::new(DEFAULT_EXACT_WORK))
                    .is_err()
            );
        }
        let wrong = if nested == 2 {
            text.replace("{x(q)}", "{q}")
        } else {
            text.replace(
                "phase_eighth(phase_eighth(phase_eighth(phase_eighth(q))))",
                "q",
            )
        };
        for entry in ["outer", "unused"] {
            let source = ParsedProgram::parse(BTreeMap::from([("main".into(), wrong.clone())]))
                .unwrap()
                .instantiate(
                    &format!("main::{entry}"),
                    BTreeMap::new(),
                    BTreeMap::from([(
                        "U".into(),
                        OperationBinding::new("main::implementation", BTreeMap::new()),
                    )]),
                )
                .unwrap()
                .elaborate()
                .unwrap();
            let error = source
                .check_operation_meanings(&kernel(), &mut Budget::new(DEFAULT_EXACT_WORK))
                .unwrap_err();
            assert_eq!(error.code(), "contract", "{error}");
            assert!(error.message().contains("original Meaning"), "{error}");
        }
    }
}

#[test]
fn nested_repeated_binding_is_compared_with_its_own_original_annotation() {
    use qleisli::contract::{DEFAULT_EXACT_WORK, exact::Budget};
    use qleisli::frontend::sized::OperationBinding;
    let text = include_str!(
        "fixtures/authoring_sessions/meaning-enforcement-v030/attempt-01/repeated-bit.qli"
    );
    let source = ParsedProgram::parse(BTreeMap::from([("main".into(), text.into())]))
        .unwrap()
        .instantiate(
            "main::outer",
            BTreeMap::new(),
            BTreeMap::from([(
                "U".into(),
                OperationBinding::new("main::implementation", BTreeMap::new()),
            )]),
        )
        .unwrap()
        .elaborate()
        .unwrap();
    let error = source
        .check_operation_meanings(&kernel(), &mut Budget::new(DEFAULT_EXACT_WORK))
        .unwrap_err();
    assert_eq!(error.code(), "contract", "{error}");
    assert!(error.message().contains("main::inner::U"), "{error}");
    assert!(error.message().contains("main::Flip"), "{error}");
}

#[test]
fn original_meaning_ids_do_not_unify_same_named_targets_in_distinct_modules() {
    use qleisli::contract::{DEFAULT_EXACT_WORK, exact::Budget};
    use qleisli::frontend::sized::OperationBinding;
    let common = "use std::quantum::x; pub unitary fn implementation(q:Q<Bit>)->Q<Bit>{x(q)}";
    let declaration = "meaning M:Bit=permutation_by(f); pub unitary fn host[static U:Op<Bit,M>](q:Q<Bit>)->Q<Bit> requires Apply(U){q}";
    let parsed = ParsedProgram::parse(BTreeMap::from([
        (
            "flip".into(),
            format!("{common} classical fn f(b:Bit)->Bit{{not b}} {declaration}"),
        ),
        (
            "identity".into(),
            format!("{common} classical fn f(b:Bit)->Bit{{b}} {declaration}"),
        ),
    ]))
    .unwrap();
    for module in ["flip", "identity"] {
        let source = parsed
            .instantiate(
                &format!("{module}::host"),
                BTreeMap::new(),
                BTreeMap::from([(
                    "U".into(),
                    OperationBinding::new(format!("{module}::implementation"), BTreeMap::new()),
                )]),
            )
            .unwrap()
            .elaborate()
            .unwrap();
        let actual =
            source.check_operation_meanings(&kernel(), &mut Budget::new(DEFAULT_EXACT_WORK));
        if module == "flip" {
            assert_eq!(actual.unwrap().checked_bindings(), 1);
        } else {
            let e = actual.unwrap_err();
            assert_eq!(e.code(), "contract");
            assert!(e.message().contains("identity::M"), "{e}");
        }
    }
}

#[test]
fn selected_cli_checks_original_annotations_and_rejects_raw_bypass() {
    let text =
        include_str!("fixtures/authoring_sessions/meaning-enforcement-v030/attempt-01/bit.qli");
    for honest in [true, false] {
        let root = SourceRoot::new(&if honest {
            text.into()
        } else {
            text.replace("{x(q)}", "{q}")
        });
        for legacy in [false, true] {
            for profile in ["auto", "raw", "hierarchy"] {
                let mut cmd = std::process::Command::new(env!("CARGO_BIN_EXE_qleisli"));
                if legacy {
                    cmd.arg("sized");
                }
                let output = cmd
                    .args([
                        "check",
                        "--entry=main::unused",
                        "--operation=U=main::implementation",
                    ])
                    .arg(format!(
                        "--module=main={}",
                        root.0.join("main.qli").display()
                    ))
                    .arg(format!("--ir-profile={profile}"))
                    .env(
                        "QLEISLI_KERNEL",
                        std::env::var_os("QLEISLI_KERNEL").unwrap(),
                    )
                    .output()
                    .unwrap();
                assert_eq!(
                    output.status.success(),
                    honest && profile != "raw",
                    "{honest}, {legacy}, {profile}: {} {}",
                    String::from_utf8_lossy(&output.stdout),
                    String::from_utf8_lossy(&output.stderr)
                );
                if !honest && profile != "raw" {
                    assert!(String::from_utf8_lossy(&output.stderr).contains("original Meaning"));
                }
            }
        }
    }
}

#[test]
fn unused_provider_leaf_checks_its_body_without_replacing_caller_identity() {
    use qleisli::contract::{DEFAULT_EXACT_WORK, exact::Budget};
    use qleisli::frontend::sized::OperationBinding;
    let bit = "use std::quantum::x;\nclassical fn flip(b:Bit)->Bit{not b}\nmeaning Flip:Bit=permutation_by(flip);\nunitary fn helper(q:Q<Bit>)->Q<Bit>{x(q)}\npub unitary fn implementation(q:Q<Bit>)->Q<Bit>{helper(q)}\npub unitary fn host[static U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Apply(U){q}";
    let unit = "use std::quantum::phase_eighth;\nclassical fn scalar(u:Unit)->(Bit,(Bit,Bit)){(0,(0,1))}\nmeaning Minus:Unit=phase_by(scalar);\npub unitary fn implementation(q:Q<Unit>)->Q<Unit>{phase_eighth(phase_eighth(phase_eighth(phase_eighth(q))))}\npub unitary fn host[static U:Op<Unit>](q:Q<Unit>)->Q<Unit> requires Apply(U){q}";
    let wrong_bit = bit.replace("{helper(q)}", "{q}");
    let wrong_unit = unit.replace(
        "phase_eighth(phase_eighth(phase_eighth(phase_eighth(q))))",
        "phase_eighth(phase_eighth(phase_eighth(q)))",
    );
    for (text, meaning, correct) in [
        (bit, "Flip", true),
        (wrong_bit.as_str(), "Flip", false),
        (unit, "Minus", true),
        (wrong_unit.as_str(), "Minus", false),
    ] {
        let parsed = ParsedProgram::parse(BTreeMap::from([("main".into(), text.into())])).unwrap();
        let target = parsed
            .finite_meaning_target(&format!("main::{meaning}"))
            .unwrap();
        let source = parsed
            .instantiate(
                "main::host",
                BTreeMap::new(),
                BTreeMap::from([(
                    "U".into(),
                    OperationBinding::new("main::implementation", BTreeMap::new()),
                )]),
            )
            .unwrap()
            .elaborate()
            .unwrap();
        // This opt-in leaf check does not enable the caller's operation profile
        // or automatically discharge every unused binding.
        assert_eq!(source.lower_raw().unwrap_err().code(), "unsupported");
        assert_eq!(
            source.lower_raw_operation("missing").unwrap_err().code(),
            "unsupported"
        );
        let leaf = source.lower_raw_operation("U").unwrap();
        assert_eq!(leaf.source().instantiation().entry(), "main::host");
        assert_eq!(
            leaf.source().definitions()[leaf.source().root()].path(),
            "main::host"
        );
        assert_eq!(leaf.definition().path(), "main::implementation");
        assert_ne!(leaf.definition_index(), leaf.source().root());
        let accepted = kernel().accept(leaf.proposal()).unwrap();
        leaf.validate_source_steps(&accepted).unwrap();
        let checker = kernel();
        let checked =
            leaf.check_finite_meaning(&checker, &target, &mut Budget::new(DEFAULT_EXACT_WORK));
        if correct {
            checked.unwrap();
        } else {
            assert_eq!(checked.unwrap_err().code(), "contract");
        }
    }
}

#[test]
fn repeated_unused_binding_checks_composite_action_and_preserves_its_original_caller() {
    use qleisli::contract::{BasisType, DEFAULT_EXACT_WORK, exact::Budget, meaning::FiniteMeaning};
    use qleisli::frontend::sized::OperationBinding;
    let source = "use std::quantum::x;\nclassical fn flip(b:Bit)->Bit{not b}\nmeaning Flip:Bit=permutation_by(flip);\npub unitary fn implementation(q:Q<Bit>)->Q<Bit>{x(q)}\nunitary fn inner[static U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Apply(U){q}\npub unitary fn outer[static k:Nat,static U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Apply(U),k<=2 {inner[repeat_op(k,U)](q)}";
    let parsed = ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap();
    let flip = parsed.finite_meaning_target("main::Flip").unwrap();
    let identity = FiniteMeaning::permutation(BasisType::Bit, vec![0, 1]).unwrap();
    for count in 0..=2 {
        let source = parsed
            .instantiate(
                "main::outer",
                BTreeMap::from([("k".into(), count)]),
                BTreeMap::from([(
                    "U".into(),
                    OperationBinding::new("main::implementation", BTreeMap::new()),
                )]),
            )
            .unwrap()
            .elaborate()
            .unwrap();
        let caller = source
            .definitions()
            .iter()
            .position(|d| d.path() == "main::inner")
            .unwrap();
        let leaf = source.lower_raw_operation_at(caller, "U").unwrap();
        assert_eq!(leaf.source().instantiation().entry(), "main::outer");
        assert_eq!(leaf.operation_binding(), Some((caller, "U")));
        assert_eq!(leaf.operation().unwrap().repeat_count(), Some(count));
        assert_eq!(leaf.definition().path(), "main::implementation");
        let accepted = kernel().accept(leaf.proposal()).unwrap();
        leaf.validate_source_steps(&accepted).unwrap();
        assert_eq!(accepted.raw().operations.len(), count as usize);
        let checker = kernel();
        for (meaning, matches) in [(&flip, count == 1), (&identity, count != 1)] {
            let result =
                leaf.check_finite_meaning(&checker, meaning, &mut Budget::new(DEFAULT_EXACT_WORK));
            if matches {
                result.unwrap();
            } else {
                assert_eq!(result.unwrap_err().code(), "contract");
            }
        }
        assert_eq!(
            source
                .lower_raw_operation_at(usize::MAX, "U")
                .unwrap_err()
                .code(),
            "preservation"
        );
    }
}

#[test]
fn repeated_scalar_binding_keeps_exact_phase_and_zero_repeat_capability_preflight() {
    use qleisli::contract::{BasisType, DEFAULT_EXACT_WORK, exact::Budget, meaning::FiniteMeaning};
    use qleisli::frontend::sized::OperationBinding;
    let scalar = "use std::quantum::phase_eighth;\npub unitary fn implementation(q:Q<Unit>)->Q<Unit>{phase_eighth(phase_eighth(phase_eighth(phase_eighth(q))))}\nunitary fn inner[static U:Op<Unit>](q:Q<Unit>)->Q<Unit> requires Apply(U){q}\npub unitary fn outer[static k:Nat,static U:Op<Unit>](q:Q<Unit>)->Q<Unit> requires Apply(U),k<=2 {inner[repeat_op(k,U)](q)}";
    let parsed = ParsedProgram::parse(BTreeMap::from([("main".into(), scalar.into())])).unwrap();
    let minus = FiniteMeaning::phase(BasisType::Unit, vec![4]).unwrap();
    let identity = FiniteMeaning::phase(BasisType::Unit, vec![0]).unwrap();
    for count in 0..=2 {
        let source = parsed
            .instantiate(
                "main::outer",
                BTreeMap::from([("k".into(), count)]),
                BTreeMap::from([(
                    "U".into(),
                    OperationBinding::new("main::implementation", BTreeMap::new()),
                )]),
            )
            .unwrap()
            .elaborate()
            .unwrap();
        let caller = source
            .definitions()
            .iter()
            .position(|d| d.path() == "main::inner")
            .unwrap();
        let leaf = source.lower_raw_operation_at(caller, "U").unwrap();
        let checker = kernel();
        for (meaning, matches) in [(&minus, count == 1), (&identity, count != 1)] {
            let result =
                leaf.check_finite_meaning(&checker, meaning, &mut Budget::new(DEFAULT_EXACT_WORK));
            if matches {
                result.unwrap();
            } else {
                assert_eq!(result.unwrap_err().code(), "contract");
            }
        }
    }
    // A zero-count wrapper must not hide a provider capability unsupported by
    // the leaf profile. Its original body remains checked before emission.
    let unsupported = "use std::quantum::x;\nunitary fn turn(q:Q<Bit>)->Q<Bit>{x(q)}\npub unitary fn implementation(q:Q<Bit>)->Q<Bit>{adjoint(turn,q)}\nunitary fn inner[static U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Apply(U){q}\npub unitary fn outer[static U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Apply(U){inner[repeat_op(0,U)](q)}";
    let parsed =
        ParsedProgram::parse(BTreeMap::from([("main".into(), unsupported.into())])).unwrap();
    let source = parsed
        .instantiate(
            "main::outer",
            BTreeMap::new(),
            BTreeMap::from([(
                "U".into(),
                OperationBinding::new("main::implementation", BTreeMap::new()),
            )]),
        )
        .unwrap()
        .elaborate()
        .unwrap();
    let caller = source
        .definitions()
        .iter()
        .position(|d| d.path() == "main::inner")
        .unwrap();
    assert_eq!(
        source
            .lower_raw_operation_at(caller, "U")
            .unwrap_err()
            .code(),
        "unsupported"
    );
}

#[test]
fn original_meaning_request_checks_the_actual_provider_bytes_and_exact_phase() {
    use qleisli::contract::exact::{Budget, Exact};
    use qleisli::contract::{BasisType, DEFAULT_EXACT_WORK};
    use qleisli::interchange::finite_leaf::{UnitaryBoundary, check_unitary};
    use qleisli::ir::QuantumPort;
    let correct = include_str!(
        "fixtures/authoring_sessions/meaning-specialization-v030/attempt-01/correct-x/main.qli"
    );
    let wrong = include_str!(
        "fixtures/authoring_sessions/meaning-specialization-v030/attempt-01/wrong-x/main.qli"
    );
    let scalar = include_str!(
        "fixtures/authoring_sessions/meaning-specialization-v030/attempt-01/scalar-minus/main.qli"
    );
    let wrong_scalar = scalar.replace(
        "phase_eighth(phase_eighth(phase_eighth(phase_eighth(q))))",
        "phase_eighth(phase_eighth(phase_eighth(q)))",
    );
    assert_ne!(wrong_scalar, scalar);
    for (source, name, correct, signature) in [
        (correct, "Flip", true, BasisType::Bit),
        (wrong, "Flip", false, BasisType::Bit),
        (scalar, "Minus", true, BasisType::Unit),
        (wrong_scalar.as_str(), "Minus", false, BasisType::Unit),
    ] {
        let parsed =
            ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap();
        let target = parsed
            .finite_meaning_target(&format!("main::{name}"))
            .unwrap();
        assert_eq!(target.signature(), &signature);
        let required = target.matrix(&mut Budget::new(DEFAULT_EXACT_WORK)).unwrap();
        if name == "Minus" {
            assert_eq!(required.get(0, 0), Some(Exact::phase(4)));
        } else {
            assert_eq!(required.get(0, 1), Some(Exact::one()));
            assert_eq!(required.get(0, 0), Some(Exact::zero()));
        }
        let proposal = parsed
            .instantiate("main::implementation", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap()
            .lower_raw()
            .unwrap();
        let valid = kernel().accept(proposal.proposal()).unwrap();
        proposal.validate_source_steps(&valid).unwrap();
        let raw = valid.raw();
        assert_eq!(raw.quantum_inputs.len(), 1);
        assert_eq!(raw.quantum_outputs.len(), 1);
        let input = raw.quantum_inputs[0].clone();
        let boundary = UnitaryBoundary::new(
            signature,
            input.clone(),
            QuantumPort {
                token: raw.quantum_outputs[0],
                wires: input.wires,
                shape: input.shape,
            },
        )
        .unwrap();
        let result = check_unitary(
            proposal.payload(),
            &boundary,
            &required,
            &mut Budget::new(DEFAULT_EXACT_WORK),
        );
        let source_result =
            proposal.check_finite_meaning(&kernel(), &target, &mut Budget::new(DEFAULT_EXACT_WORK));
        if correct {
            assert!(
                result
                    .unwrap()
                    .matches(proposal.payload(), &boundary, &required)
            );
            let checked = source_result.unwrap();
            assert!(std::ptr::eq(checked.source(), &proposal));
            assert!(std::ptr::eq(checked.required(), &target));
            assert!(
                checked
                    .leaf()
                    .matches(proposal.payload(), &boundary, &required)
            );
        } else {
            assert_eq!(result.unwrap_err().code, "contract");
            assert_eq!(source_result.unwrap_err().code(), "contract");
        }
    }
}

#[test]
fn source_meaning_signature_effect_and_budget_guards_precede_native_io() {
    use qleisli::contract::{BasisType, DEFAULT_EXACT_WORK, exact::Budget, meaning::FiniteMeaning};
    let absent = std::path::Path::new("/private/tmp/qleisli-missing-source-meaning-test-checker");
    assert!(!absent.exists());
    let kernel = Kernel::new(absent);
    let source = "pub unitary fn identity(q:Q<Bit>)->Q<Bit>{q} pub observe fn main()->Unit{()}";
    let parsed = ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap();
    let raw = parsed
        .instantiate("main::identity", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap()
        .lower_raw()
        .unwrap();
    let same_width =
        FiniteMeaning::permutation(BasisType::pair(BasisType::Bit, BasisType::Unit), vec![0, 1])
            .unwrap();
    assert_eq!(
        raw.check_finite_meaning(&kernel, &same_width, &mut Budget::new(DEFAULT_EXACT_WORK))
            .unwrap_err()
            .code(),
        "type"
    );
    let bit = FiniteMeaning::permutation(BasisType::Bit, vec![0, 1]).unwrap();
    assert_eq!(
        raw.check_finite_meaning(&kernel, &bit, &mut Budget::new(DEFAULT_EXACT_WORK + 1))
            .unwrap_err()
            .code(),
        "limit"
    );
    assert_eq!(
        raw.check_finite_meaning(&kernel, &bit, &mut Budget::new(0))
            .unwrap_err()
            .code(),
        "limit"
    );
    let observe = parsed
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap()
        .lower_raw()
        .unwrap();
    let unit = FiniteMeaning::permutation(BasisType::Unit, vec![0]).unwrap();
    assert_eq!(
        observe
            .check_finite_meaning(&kernel, &unit, &mut Budget::new(DEFAULT_EXACT_WORK))
            .unwrap_err()
            .code(),
        "unsupported"
    );
}

#[test]
fn finite_source_targets_preserve_product_tree_and_refuse_width_substitution() {
    use qleisli::contract::BasisType;
    let parsed = ParsedProgram::parse(BTreeMap::from([(
        "main".into(),
        "classical fn identity(b:(Bit,(Unit,Bit)))->(Bit,(Unit,Bit)){b}
         classical fn bits(b:Bits<1>)->Bits<1>{b}
         meaning Product:(Bit,(Unit,Bit))=permutation_by(identity);
         meaning Sized:Bits<1> = permutation_by(bits);"
            .into(),
    )]))
    .unwrap();
    let target = parsed.finite_meaning_target("main::Product").unwrap();
    assert_eq!(
        target.signature(),
        &BasisType::pair(
            BasisType::Bit,
            BasisType::pair(BasisType::Unit, BasisType::Bit)
        )
    );
    assert_eq!(target.permutation_table(), &[0, 1, 2, 3]);
    let error = parsed.finite_meaning_target("main::Sized").unwrap_err();
    assert_eq!(error.code(), "unsupported");
    assert_eq!(error.module(), Some("main"));
    assert!(error.message().contains("Bits tags"));
    assert_eq!(
        parsed
            .finite_meaning_target("main::identity")
            .unwrap_err()
            .code(),
        "meaning"
    );
    assert!(parsed.finite_meaning_target("main::Missing").is_err());
}

#[test]
fn selected_preparation_rejects_unused_nonpermutation_meanings() {
    let source = "classical fn constant(b:Bit)->Bit{0}
        meaning Invalid:Bit=permutation_by(constant);
        pub observe fn main()->Unit{()}";
    let error = ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap_err();
    assert_eq!(error.code(), "meaning", "{error}");
    assert_eq!(error.module(), Some("main"));
    assert!(
        error.message().contains("inputs 0 and 1 both map to 0"),
        "{error}"
    );
    assert_eq!(
        &source[error.span().start..error.span().end],
        "meaning Invalid:Bit=permutation_by(constant);"
    );
    // An unused invalid target is a semantic failure in the finite route too.
    let finite = check_project_with_kernel(
        &SourceRoot::new(source).0,
        SourcePolicy::default(),
        &kernel(),
    )
    .unwrap_err();
    assert!(
        finite.message.contains("inputs 0 and 1 both map to 0"),
        "{finite:?}"
    );
}

#[test]
fn selected_meaning_checks_follow_original_imports_and_forward_calls() {
    let modules = BTreeMap::from([
        (
            "main".into(),
            "use functions::flip;
            meaning Flip:Bit=permutation_by(flip);
            pub observe fn main()->Unit{()}"
                .into(),
        ),
        (
            "functions".into(),
            "pub classical fn flip(b:Bit)->Bit{helper(b)}
            classical fn helper(b:Bit)->Bit{not b}"
                .into(),
        ),
    ]);
    let parsed = ParsedProgram::parse(modules).unwrap();
    parsed
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap();
    let modules = BTreeMap::from([
        (
            "main".into(),
            "use functions::constant;
            meaning Bad:Bit=permutation_by(constant);
            pub observe fn main()->Unit{()}"
                .into(),
        ),
        (
            "functions".into(),
            "pub classical fn constant(b:Bit)->Bit{helper(b)}
            classical fn helper(b:Bit)->Bit{b xor b}"
                .into(),
        ),
    ]);
    let error = ParsedProgram::parse(modules).unwrap_err();
    assert_eq!(error.code(), "meaning", "{error}");
    assert_eq!(error.module(), Some("main"));
    assert!(error.message().contains("inputs 0 and 1 both map to 0"));
}

#[test]
fn selected_meaning_preparation_keeps_zero_width_and_product_type_tags() {
    for (basis, body) in [
        ("Unit", "b"),
        ("Bits<0>", "b"),
        ("Bits<1>", "b"),
        ("(Bit,Unit)", "b"),
        ("(Unit,Bit)", "b"),
        ("(Bit,(Unit,Bit))", "b"),
    ] {
        let source = format!(
            "classical fn identity(b:{basis})->{basis}{{{body}}}
            meaning Id:{basis} = permutation_by(identity);
            pub observe fn main()->Unit{{()}}"
        );
        let parsed = ParsedProgram::parse(BTreeMap::from([("main".into(), source)])).unwrap();
        parsed
            .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap();
    }
    for (basis, domain) in [
        ("Unit", "Bits<0>"),
        ("Bit", "Bits<1>"),
        ("(Bit,Unit)", "(Unit,Bit)"),
    ] {
        let source = format!(
            "classical fn identity(b:{domain})->{domain}{{b}}
            meaning Bad:{basis} = permutation_by(identity);
            pub observe fn main()->Unit{{()}}"
        );
        let error = ParsedProgram::parse(BTreeMap::from([("main".into(), source)])).unwrap_err();
        assert_eq!(error.code(), "type", "{error}");
    }
}

#[test]
fn selected_meaning_preparation_handles_scalar_phase_and_pattern_leaf_order() {
    // Preparation validates the exact total phase function, not its provider.
    let source = "classical fn eighth(u:Unit)->(Bit,(Bit,Bit)){(0,(0,1))}
        meaning Minus:Unit=phase_by(eighth);
        classical fn swap((a,(u,b)):(Bit,(Unit,Bit)))->(Bit,(Unit,Bit)){(b,(u,a))}
        meaning Swap:(Bit,(Unit,Bit))=permutation_by(swap);
        pub observe fn main()->Unit{()}";
    ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap();
    let source = "classical fn duplicate((a,(u,b)):(Bit,(Unit,Bit)))->(Bit,(Unit,Bit)){(a,(u,a))}
        meaning Bad:(Bit,(Unit,Bit))=permutation_by(duplicate);
        pub observe fn main()->Unit{()}";
    let error = ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap_err();
    assert_eq!(error.code(), "meaning", "{error}");
    assert!(
        error.message().contains("inputs 0 and 2 both map to 0"),
        "{error}"
    );
}

fn finite(source: &str) -> AcceptedProgram {
    compile_project_with_kernel(
        &SourceRoot::new(source).0,
        SourcePolicy::default(),
        &kernel(),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
}

fn elaborate(source: &str, entry: &str) -> ElaboratedProgram {
    let parsed = ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap();
    let retained = parsed.clone();
    drop(parsed);
    assert_eq!(retained.source("main"), Some(source));
    retained
        .instantiate(entry, BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap()
}

fn accept(graph: &ElaboratedProgram) -> AcceptedProgram {
    let proposal = graph.lower_raw().unwrap();
    let accepted = kernel().accept(proposal.proposal()).unwrap();
    assert_eq!(accepted.artifact(), proposal.payload());
    assert!(accepted.request().is_none());
    proposal.validate_source_steps(&accepted).unwrap();
    accepted
}

fn closed(program: &AcceptedProgram, expected: &[bool]) {
    assert_eq!(
        run_closed(program, SimulationLimits::default()).unwrap(),
        BTreeMap::from([(expected.to_vec(), 1.0)])
    );
}

fn both_closed(source: &str, expected: &[bool]) -> ElaboratedProgram {
    closed(&finite(source), expected);
    let graph = elaborate(source, "main::main");
    closed(&accept(&graph), expected);
    graph
}

fn rejected_before_native(source: &str, selected: &str, finite: &str) {
    let error = ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap_err();
    assert_eq!(error.code(), selected, "{error}");
    assert_eq!(error.module(), Some("main"), "{error}");
    assert!(error.span().end > error.span().start, "{error}");
    assert!(error.span().end <= source.len(), "{error}");
    let root = SourceRoot::new(source);
    let absent = root.0.join("must-not-start-native");
    assert!(!absent.exists());
    let error = check_project_with_kernel(&root.0, SourcePolicy::default(), &Kernel::new(absent))
        .unwrap_err();
    assert_eq!(error.code, finite, "{error:?}");
    let location = error.primary.expect("located finite source diagnostic");
    assert!(location.path.ends_with("main.qli"));
    assert!(location.span.end > location.span.start);
    assert!(location.span.end <= source.len());
}

fn selected_coherent_unsupported(source: &str, entry: &str) {
    // The complete source judgment succeeds. Concrete projection has a narrower
    // profile: this is not evidence that the selected path verified injectivity.
    let parsed = ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap();
    // A selected root's projection is checked during instantiation; a helper's
    // unsupported projection is reached later while elaborating its caller.
    let error = match parsed.instantiate(entry, BTreeMap::new(), BTreeMap::new()) {
        Err(error) => error,
        Ok(instance) => match instance.elaborate() {
            Err(error) => error,
            Ok(_) => panic!("expected the explicitly unsupported coherent projection"),
        },
    };
    assert_eq!(error.code(), "unsupported", "{error}");
    assert!(error.span().end > error.span().start, "{error}");
    assert!(error.span().end <= source.len(), "{error}");
}

#[test]
fn canonical_declaration_retains_expression_ast_and_old_spelling_has_migration_error() {
    let source = "classical fn flip(x: Bit) -> Bit { not x }";
    let parsed = parse_module(source).unwrap();
    assert_eq!(parsed.decls[0].kind, FnKind::Classical);
    assert!(matches!(parsed.decls[0].body, FnBody::Basis(_)));
    let retired = "basis fn flip(x: Bit) -> Bit { not x }";
    let error = parse_module(retired).unwrap_err();
    assert!(error.message.contains("classical fn"), "{error}");
    assert!(error.span.end > error.span.start);
    assert!(error.span.end <= retired.len());
}

#[test]
fn frozen_flip_is_reused_coherently_and_ordinarily_with_explicit_profile_limit() {
    let source = first_source!("shared-flip");
    closed(&finite(source), &[true, false]);
    selected_coherent_unsupported(source, "main::main");
    both_closed(
        "classical fn flip(x: Bit) -> Bit { not x }
         pub fn main() -> (Bit,Bit) { let b = flip(0); (b,flip(b)) }",
        &[true, false],
    );
}

// Tiny exact evaluator of the accepted LiftBasis tag: |b> maps to |table[b]>
// with scalar phase exactly +1. The fixed oracle below is authored independently
// as X on the first owner and I on its external reference, not from this table.
fn act_on_two_axes(table: &[u16], state: [(i32, i32); 4]) -> [(i32, i32); 4] {
    assert_eq!(table.len(), 2);
    let mut output = [(0, 0); 4];
    for (column, coefficient) in state.into_iter().enumerate() {
        let mapped = usize::from(table[column & 1]);
        assert!(mapped < 2);
        let row = (column & 2) | mapped;
        output[row].0 += coefficient.0;
        output[row].1 += coefficient.1;
    }
    output
}

#[test]
fn coherent_flip_preserves_exact_phase_axis_and_entangled_external_reference() {
    let source = "use std::quantum::init0; use std::observe::measure_z;
        classical fn flip(x: Bit) -> Bit { not x }
        unitary fn lifted(q: Q<Bit>) -> Q<Bit> { basis q as b { flip(b) } }
        pub observe fn main() -> (Bit,Bit) {
            let q = init0(); let reference = init0(); let q = lifted(q);
            (measure_z(q),measure_z(reference))
        }";
    let accepted = finite(source);
    closed(&accepted, &[true, false]);
    let operations = &accepted.raw().operations;
    let initial: Vec<_> = operations
        .iter()
        .filter_map(|operation| match operation {
            RawOp::Init0 { output, wire } => Some((*output, *wire)),
            _ => None,
        })
        .collect();
    assert_eq!(initial.len(), 2);
    assert_ne!(initial[0].1, initial[1].1);
    let lifts: Vec<_> = operations
        .iter()
        .filter_map(|operation| match operation {
            RawOp::LiftBasis {
                input,
                output,
                output_wires,
                table,
            } => Some((*input, *output, output_wires, table)),
            _ => None,
        })
        .collect();
    assert_eq!(lifts.len(), 1);
    let (input, output, wires, table) = lifts[0];
    assert_eq!(input, initial[0].0);
    assert_eq!(wires.as_slice(), &[initial[0].1]);
    let measured: Vec<_> = operations
        .iter()
        .filter_map(|operation| match operation {
            RawOp::MeasureZ { input, .. } => Some(*input),
            _ => None,
        })
        .collect();
    assert_eq!(measured, [output, initial[1].0]);
    // Check every actual instruction, so an extra phase/gate cannot disappear
    // from the action being compared. This closed source needs no other action.
    assert!(operations.iter().all(|operation| matches!(
        operation,
        RawOp::Init0 { .. } | RawOp::LiftBasis { .. } | RawOp::MeasureZ { .. }
    )));
    for column in 0..4 {
        let mut input = [(0, 0); 4];
        input[column] = (1, 0);
        let mut expected = [(0, 0); 4];
        expected[column ^ 1] = (1, 0);
        assert_eq!(act_on_two_axes(table, input), expected);
    }
    // This rank-two complex coefficient matrix is entangled. Normalization is
    // unnecessary for equality of linear actions and cannot hide phase loss.
    assert_eq!(
        act_on_two_axes(table, [(1, 2), (3, -1), (-2, 4), (5, 0)]),
        [(3, -1), (1, 2), (5, 0), (-2, 4)]
    );
}

#[test]
fn noninjective_and_is_ordinary_total_but_is_not_a_coherent_isometry() {
    both_closed(first_source!("ordinary-and"), &[false]);
    for (a, b, expected) in [(0, 0, false), (0, 1, false), (1, 0, false), (1, 1, true)] {
        both_closed(
            &format!(
                "classical fn both((a,b): (Bit,Bit)) -> Bit {{ a and b }}
             pub fn main() -> Bit {{ both(({a},{b})) }}"
            ),
            &[expected],
        );
    }
    let source = "classical fn both((a,b): (Bit,Bit)) -> Bit { a and b }
        pub iso fn collapse(q: Q<(Bit,Bit)>) -> Q<Bit> { basis q as p { both(p) } }
        pub fn main() -> Bit { 0 }";
    let root = SourceRoot::new(source);
    let error = check_project_with_kernel(&root.0, SourcePolicy::default(), &kernel()).unwrap_err();
    assert_eq!(error.code, "ownership", "{error:?}");
    assert!(error.message.contains("not injective"), "{error:?}");
    selected_coherent_unsupported(source, "main::collapse");
}

#[test]
fn one_classical_body_remains_a_static_meaning_and_exact_computed_predicate() {
    let source = "use std::quantum::init0; use std::quantum::h; use std::quantum::z;
        use std::observe::measure_z;
        classical fn flip(x: Bit) -> Bit { not x }
        meaning Flip: Bit = permutation_by(flip);
        pub unitary fn oracle(q: Q<Bit>) -> Q<Bit> { with_computed(q,flip) { |a| z(a) } }
        pub observe fn main() -> (Bit,Bit) {
            let b = measure_z(h(oracle(h(init0())))); (b,flip(b))
        }";
    let accepted = finite(source);
    // Computing NOT, applying Z to the temporary and exactly uncomputing gives
    // diag(-1,+1). H diag(-1,+1) H|0> = -|1>, then ordinary NOT returns zero.
    let distribution = run_closed(&accepted, SimulationLimits::default()).unwrap();
    assert!((distribution.values().sum::<f64>() - 1.0).abs() < 1e-12);
    assert!((distribution.get(&vec![true, false]).copied().unwrap_or(0.0) - 1.0).abs() < 1e-12);
    for (outcome, probability) in distribution {
        if outcome != [true, false] {
            assert!(probability.abs() < 1e-12);
        }
    }
    assert!(
        accepted
            .raw()
            .operations
            .iter()
            .any(|operation| { matches!(operation, RawOp::ComputeUseUncompute { .. }) })
    );
    selected_coherent_unsupported(source, "main::oracle");
}

#[test]
fn unit_and_nested_products_retain_exact_trees_and_argument_list_arity() {
    both_closed(first_source!("nested-label"), &[false]);
    let source = "classical fn singleton((): Unit) -> Unit { () }
        classical fn pick(((),(b,())): (Unit,(Bit,Unit))) -> ((Bit,Unit),(Unit,Bit)) {
            ((b,()),((),not b))
        }
        pub fn main() -> ((Bit,Unit),(Unit,Bit)) { pick((singleton(()),(1,()))) }";
    let graph = both_closed(source, &[true, false]);
    let pick = graph
        .definitions()
        .iter()
        .find(|d| d.path() == "main::pick")
        .unwrap();
    assert_eq!(pick.inputs().len(), 1);
    assert_eq!(pick.inputs()[0].fields()[0].ty().kind(), "unit");
    assert_eq!(pick.inputs()[0].fields()[1].fields()[1].ty().kind(), "unit");
    assert_eq!(pick.output().fields()[0].fields()[1].ty().kind(), "unit");
    let prefix = "classical fn pick(((),(b,())): (Unit,(Bit,Unit))) -> Bit { b }";
    rejected_before_native(
        &format!("{prefix} pub fn main() -> Bit {{ pick((((),0),())) }}"),
        "type",
        "type_mismatch",
    );
    rejected_before_native(
        &format!("{prefix} pub fn main() -> Bit {{ pick((),(0,())) }}"),
        "arity",
        "arity",
    );
    rejected_before_native(
        "classical fn unary(_: Unit) -> Bit { 0 } pub fn main() -> Bit { unary() }",
        "arity",
        "arity",
    );
}

#[test]
fn eager_argument_effects_belong_to_the_caller_in_source_order() {
    let source = "use std::quantum::init0; use std::quantum::x; use std::observe::measure_z;
        classical fn left(a: Bit, b: Bit) -> Bit { a }
        pub observe fn main() -> Bit { left(measure_z(x(init0())),measure_z(init0())) }";
    let graph = both_closed(source, &[true]);
    for accepted in [finite(source), accept(&graph)] {
        assert_eq!(accepted.derived_effect(), Effect::Observe);
        let sequence: Vec<_> = accepted
            .raw()
            .operations
            .iter()
            .filter_map(|op| match op {
                RawOp::Init0 { .. } => Some("init"),
                RawOp::MeasureZ { .. } => Some("measure"),
                _ => None,
            })
            .collect();
        assert_eq!(sequence, ["init", "measure", "init", "measure"]);
    }
    let source = "use std::quantum::init0; use std::observe::measure_z;
        classical fn both(a: Bit, b: Bit) -> Bit { a and b }
        pub observe fn main() -> Bit { both(0,measure_z(init0())) }";
    let graph = both_closed(source, &[false]);
    for accepted in [finite(source), accept(&graph)] {
        let ops = &accepted.raw().operations;
        let measure = ops
            .iter()
            .position(|op| matches!(op, RawOp::MeasureZ { .. }))
            .unwrap();
        let and = ops
            .iter()
            .position(|op| matches!(op, RawOp::ClassicalAnd { .. }))
            .unwrap();
        assert!(measure < and);
        assert_eq!(accepted.derived_effect(), Effect::Observe);
    }
    rejected_before_native(
        "use std::observe::measure_z;
         classical fn left(a: Bit,b: Bit) -> Bit { a }
         unitary fn bad(q: Q<Bit>) -> Bit { left(0,measure_z(q)) }
         pub fn main() -> Bit { 0 }",
        "effect",
        "effect",
    );
}

#[test]
fn open_ordinary_inputs_are_explicit_ports_and_closed_wrappers_execute() {
    let source = "classical fn flip(x: Bit) -> Bit { not x }
        pub fn open(x: Bit) -> Bit { flip(x) }
        pub fn main() -> (Bit,Bit) { (open(0),open(1)) }";
    both_closed(source, &[true, false]);
    let graph = elaborate(source, "main::open");
    let definition = &graph.definitions()[graph.root()];
    assert_eq!(definition.inputs().len(), 1);
    assert_eq!(definition.inputs()[0].ty().kind(), "bit");
    assert!(!definition.inputs()[0].ty().is_quantum());
    let accepted = accept(&graph);
    assert!(matches!(
        run_closed(&accepted, SimulationLimits::default()),
        Err(SimulationError::NotClosed(_))
    ));
}

#[test]
fn quantum_arguments_and_invalid_unused_declarations_are_rejected_before_native() {
    rejected_before_native(first_source!("quantum-argument"), "type", "type_mismatch");
    for source in [
        "classical fn invalid(x: Bit) -> Unit { x } pub fn main() -> Bit { 0 }",
        "use std::quantum::init0; use std::observe::measure_z;
         classical fn invalid() -> Bit { measure_z(init0()) }
         pub fn main() -> Bit { 0 }",
    ] {
        rejected_before_native(source, "type", "type_mismatch");
    }
    // The declaration's grammar admits ordinary basis types only. Do not count
    // this earlier syntax rejection as the semantic Q-argument check above.
    rejected_before_native(
        "classical fn invalid(q: Q<Bit>) -> Bit { 0 } pub fn main() -> Bit { 0 }",
        "parse",
        "parse",
    );
    for call in ["adjoint(flip,q)", "controlled(flip)(c,q)"] {
        let signature = if call.starts_with("controlled") {
            "c: Q<Bit>, q: Q<Bit>"
        } else {
            "q: Q<Bit>"
        };
        rejected_before_native(
            &format!(
                "classical fn flip(x: Bit) -> Bit {{ not x }}
                unitary fn bad({signature}) -> Q<Bit> {{ {call} }}
                pub fn main() -> Bit {{ 0 }}"
            ),
            "type",
            "type_mismatch",
        );
    }
}

#[test]
fn private_classical_helpers_resolve_lexically_and_cycles_remain_illegal() {
    let main = "use helper::outer; pub fn main() -> Bit { outer(0) }";
    let helper = "classical fn private_flip(x: Bit) -> Bit { not x }
        pub classical fn outer(x: Bit) -> Bit { private_flip(x) }";
    let root = SourceRoot::new(main);
    root.write("helper.qli", helper);
    let accepted =
        compile_project_with_kernel(&root.0, SourcePolicy::default(), &kernel()).unwrap();
    closed(&accepted, &[true]);
    let parsed = ParsedProgram::parse(BTreeMap::from([
        ("main".into(), main.into()),
        ("helper".into(), helper.into()),
    ]))
    .unwrap();
    let graph = parsed
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap();
    closed(&accept(&graph), &[true]);
    let inaccessible = "use helper::private_flip; pub fn main() -> Bit { private_flip(0) }";
    root.write("main.qli", inaccessible);
    let selected = ParsedProgram::parse(BTreeMap::from([
        ("main".into(), inaccessible.into()),
        ("helper".into(), helper.into()),
    ]))
    .unwrap_err();
    assert!(selected.to_string().contains("private"), "{selected}");
    let absent = root.0.join("must-not-start-native");
    let error = check_project_with_kernel(&root.0, SourcePolicy::default(), &Kernel::new(absent))
        .unwrap_err();
    assert_eq!(error.code, "project", "{error:?}");
    assert!(error.message.contains("private"), "{error:?}");
    for source in [
        "classical fn a(x: Bit) -> Bit { a(x) } pub fn main() -> Bit { 0 }",
        "classical fn a(x: Bit) -> Bit { b(x) }
         classical fn b(x: Bit) -> Bit { a(x) } pub fn main() -> Bit { 0 }",
    ] {
        rejected_before_native(source, "cycle", "recursive_call");
    }
}

#[test]
fn meaning_is_still_a_static_target_and_not_an_ordinary_runtime_function() {
    let source = "classical fn identity(x: Bit) -> Bit { x }
        meaning Id: Bit = permutation_by(identity);
        pub fn main() -> Bit { Id(0) }";
    rejected_before_native(source, "type", "type_mismatch");
    let error = ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap_err();
    assert!(error.to_string().contains("Meaning"), "{error}");
}
