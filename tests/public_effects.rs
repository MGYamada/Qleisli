//! Bounded public effect contracts across finite and selected Raw source paths.
//! These regressions grant no new Meaning, cleanup or source-preservation proof.
//! Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
mod common;

use common::SourceRoot;
use qleisli::contract::{DEFAULT_EXACT_WORK, exact::Budget};
use qleisli::frontend::compile::{
    ErrorCode, OperationBinding, ParsedProgram, check_project, compile_project,
    project_effects_with_kernel,
};
use qleisli::frontend::project::SourcePolicy;
use qleisli::interchange::native::Kernel;
use qleisli::ir::Effect;
use std::collections::BTreeMap;

const IDENTITY: &str = "pub observe fn provider(q:Q<Bit>)->Q<Bit>{q}";
const RESET: &str = "use std::state::reset;pub observe fn provider(q:Q<Bit>)->Q<Bit>{reset(q)}";
const PUBLIC_QUANTUM_PERMISSION_BODIES: [(&str, bool); 2] = [
    ("x", false),
    ("finish(global_phase_eighth(unit(())));x", true),
];

fn classical_interface_with_public_quantum_permission(body: &str) -> String {
    format!(
        "
        pub unitary fn f(x:Bit)->Bit{{{body}}}
        fn local(x:Bit)->Bit{{f(x)}}"
    )
}

fn sources(main: &str, library: &str) -> BTreeMap<String, String> {
    BTreeMap::from([
        ("main".into(), main.into()),
        ("library".into(), library.into()),
    ])
}

fn project(modules: &BTreeMap<String, String>) -> SourceRoot {
    let root = SourceRoot::new(modules.get("main").map(String::as_str).unwrap_or(""));
    for (module, source) in modules {
        let path = root.0.join(format!("{}.qli", module.replace("::", "/")));
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, source).unwrap();
    }
    root
}

fn effect_refusal(modules: BTreeMap<String, String>) {
    let finite = check_project(&project(&modules).0).unwrap_err();
    assert_eq!(finite.code, ErrorCode::Effect, "{finite}");
    let selected = ParsedProgram::parse(qleisli::edition::Edition::E2026, modules).unwrap_err();
    assert_eq!(selected.code(), "effect", "{selected}");
}

#[test]
fn public_quantum_declarations_require_explicit_effects_even_without_quantum_ports() {
    for source in [
        "pub fn f(q:Q<Bit>)->Q<Bit>{q}",
        "pub fn f(q:Q<Bits<0>>)->Q<Bits<0>>{q}",
        "pub fn f(q:(Unit,Q<Unit>))->(Unit,Q<Unit>){q}",
        "pub fn f(q:Q<Bit>)->Q<Bit>{h(q)}",
        "pub fn f()->Unit{finish(unit(()))}",
        "fn helper()->Unit{finish(unit(()))}pub fn f()->Unit{helper()}",
        "use std::state::init0;pub fn f()->Unit{discard(init0())}",
        "pub fn f[const U:Op<Bit>](b:Bit)->Bit{b}",
    ] {
        let modules = BTreeMap::from([("main".into(), source.into())]);
        let selected =
            ParsedProgram::parse(qleisli::edition::Edition::E2026, modules.clone()).unwrap_err();
        assert_eq!(selected.code(), "effect", "{source}: {selected}");
        assert!(
            selected.message().contains("requires an explicit"),
            "{selected}"
        );
        let finite = check_project(&project(&modules).0).unwrap_err();
        assert_eq!(finite.code, ErrorCode::Effect, "{source}: {finite}");
        assert!(finite.message.contains("requires an explicit"), "{finite}");
    }
}

#[test]
fn public_bounds_refuse_external_tightening_before_and_after_a_body_only_reset_change() {
    for library in [IDENTITY, RESET] {
        for effect in ["unitary", "isometry"] {
            effect_refusal(sources(
                &format!(
                    "use library::provider;pub {effect} fn main(q:Q<Bit>)->Q<Bit>{{provider(q)}}"
                ),
                library,
            ));
        }
    }
}

#[test]
fn external_quantum_annotation_needs_are_fixed_by_the_public_contract() {
    for (body, internal_quantum) in PUBLIC_QUANTUM_PERMISSION_BODIES {
        let library = classical_interface_with_public_quantum_permission(body);
        // The same explicit public prefix permits closed quantum work in both
        // bodies. External callers cannot infer that permission from the body.
        effect_refusal(sources(
            "use library::f;pub fn g(x:Bit)->Bit{f(x)}fn main()->Bit{g(0)}",
            &library,
        ));
        let selected = ParsedProgram::parse(
            qleisli::edition::Edition::E2026,
            sources(
                "use library::f;pub unitary fn g(x:Bit)->Bit{f(x)}fn main()->Bit{g(0)}",
                &library,
            ),
        )
        .unwrap();
        for path in ["library::f", "library::local"] {
            assert_eq!(
                selected.function_effect(path).unwrap().uses_quantum(),
                internal_quantum,
                "{path}: {body}"
            );
        }
        let caller = selected.function_effect("main::g").unwrap();
        assert_eq!(caller.public_effect(), Some(Effect::Unitary));
        assert_eq!(caller.inferred(), Effect::Unitary);
        assert!(caller.uses_quantum());
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn classical_public_interface_body_replacement_keeps_both_source_paths_stable() {
    let kernel = Kernel::selected(qleisli::edition::Edition::E2026).unwrap();
    for (body, internal_quantum) in PUBLIC_QUANTUM_PERMISSION_BODIES {
        let modules = sources(
            "use library::f;pub unitary fn g(x:Bit)->Bit{f(x)}fn main()->Bit{g(0)}",
            &classical_interface_with_public_quantum_permission(body),
        );
        let root = project(&modules);
        let finite = project_effects_with_kernel(&root.0, SourcePolicy::Legacy, &kernel).unwrap();
        let selected = ParsedProgram::parse(qleisli::edition::Edition::E2026, modules).unwrap();
        for path in ["library::f", "library::local", "main::g"] {
            assert_eq!(
                finite.function_effect(path),
                selected.function_effect(path),
                "{path}"
            );
        }
        assert_eq!(
            finite.function_effect("library::f").unwrap().uses_quantum(),
            internal_quantum
        );
        assert!(finite.function_effect("main::g").unwrap().uses_quantum());
        assert_eq!(
            compile_project(&root.0).unwrap().derived_effect(),
            Effect::Unitary
        );
        let elaborated = selected
            .instantiate("main::g", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap();
        let proposal = elaborated.lower_raw().unwrap();
        let accepted = kernel.accept(proposal.proposal()).unwrap();
        assert_eq!(accepted.derived_effect(), Effect::Unitary);
        proposal.validate_source_steps(&accepted).unwrap();
    }
}

#[test]
fn internal_wrappers_keep_every_transitive_external_boundary() {
    for body in [
        "provider(q)",
        "if 0 {provider(q)} else {q}",
        "if static 0==0 {q} else {provider(q)}",
        "qfor static i in 0..0 carry a=q {yield provider(a)}",
    ] {
        for public_prefix in ["unitary", "isometry"] {
            effect_refusal(sources(
                &format!(
                    "use library::provider;fn wrapper(q:Q<Bit>)->Q<Bit>{{{body}}}
                    pub {public_prefix} fn main(q:Q<Bit>)->Q<Bit>{{wrapper(q)}}"
                ),
                IDENTITY,
            ));
        }
    }
    // An unused declaration is checked even when the selected entry is pure.
    effect_refusal(sources(
        "use library::provider;unitary fn unused(q:Q<Bit>)->Q<Bit>{provider(q)}
        pub unitary fn main(q:Q<Bit>)->Q<Bit>{q}",
        IDENTITY,
    ));
}

#[test]
fn imported_names_and_logical_module_maps_do_not_grant_internal_precision() {
    for module in ["library", "ordinary", "nested::ordinary"] {
        // The imported local name is resolved to its original declaration's
        // module; changing map keys or import grouping cannot make it local.
        let modules = BTreeMap::from([
            (
                "main".into(),
                format!(
                    "use {module}::{{provider}};pub unitary fn main(q:Q<Bit>)->Q<Bit>{{provider(q)}}"
                ),
            ),
            (module.into(), IDENTITY.into()),
        ]);
        effect_refusal(modules);
    }
}

#[test]
fn source_providers_meanings_and_transforms_use_the_public_effect() {
    for effect in ["observe", "isometry"] {
        let library = format!("pub {effect} fn provider(q:Q<Bit>)->Q<Bit>{{q}}");
        for body in [
            "apply[provider](q)",
            "adjoint(provider)(q)",
            "power(provider,0)(q)",
            "apply[then_op(provider,identity)](q)",
        ] {
            effect_refusal(sources(
                &format!(
                    "use library::provider;
                    fn identity(q:Q<Bit>)->Q<Bit>{{q}}
                    fn apply[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){{U(q)}}
                    pub observe fn main(q:Q<Bit>)->Q<Bit>{{{body}}}"
                ),
                &library,
            ));
        }
        effect_refusal(sources(
            "use library::provider;pub observe fn main(c:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){controlled(provider)(c,q)}",
            &library,
        ));
    }
    // Reference Meaning and equality obligations must not recover a sharper
    // effect by independently looking up the provider's fortunate pure body.
    effect_refusal(sources(
        "use library::provider;meaning Identity:Bit=reference(provider);
        pub unitary fn main(q:Q<Bit>)->Q<Bit>{q}",
        IDENTITY,
    ));
    effect_refusal(sources(
        "use library::provider;fn identity(q:Q<Bit>)->Q<Bit>{q}
        pub observe fn main(q:Q<Bit>)->Q<Bit>{apply_contract(provider,identity,q)}",
        IDENTITY,
    ));
}

#[test]
fn host_selected_public_providers_use_public_bounds_even_when_unused() {
    for effect in ["observe", "isometry"] {
        let source = format!(
            "pub {effect} fn provider(q:Q<Bit>)->Q<Bit>{{q}}
            pub unitary fn main[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){{q}}"
        );
        let program = ParsedProgram::parse(
            qleisli::edition::Edition::E2026,
            BTreeMap::from([("main".into(), source)]),
        )
        .unwrap();
        let fact = program.function_effect("main::provider").unwrap();
        assert_eq!(fact.inferred(), Effect::Unitary);
        assert_eq!(
            fact.public_effect(),
            Some(if effect == "observe" {
                Effect::Observe
            } else {
                Effect::Isometry
            })
        );
        let error = program
            .instantiate(
                "main::main",
                BTreeMap::new(),
                BTreeMap::from([(
                    "U".into(),
                    OperationBinding::new("main::provider", BTreeMap::new()),
                )]),
            )
            .unwrap_err();
        assert_eq!(error.code(), "effect", "{error}");
    }
    // Existing explicit private host bindings use the entry's module and do
    // not expose that provider as a public callable declaration.
    let source = "observe fn provider(q:Q<Bit>)->Q<Bit>{q}
        pub unitary fn main[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}";
    let program = ParsedProgram::parse(
        qleisli::edition::Edition::E2026,
        BTreeMap::from([("main".into(), source.into())]),
    )
    .unwrap();
    assert_eq!(program.public_function_effect("main::provider"), None);
    program
        .instantiate(
            "main::main",
            BTreeMap::new(),
            BTreeMap::from([(
                "U".into(),
                OperationBinding::new("main::provider", BTreeMap::new()),
            )]),
        )
        .unwrap();
}

#[test]
fn explicit_pure_labels_never_hide_observation_reset_or_discard() {
    for prefix in ["unitary", "isometry"] {
        for body in [
            "let b=measure_z(q);init0()",
            "reset(q)",
            "discard(q);init0()",
        ] {
            effect_refusal(BTreeMap::from([(
                "main".into(),
                format!(
                    "use std::state::init0;use std::state::reset;
                    fn hidden(q:Q<Bit>)->Q<Bit>{{{body}}}
                    pub {prefix} fn main(q:Q<Bit>)->Q<Bit>{{hidden(q)}}"
                ),
            )]));
        }
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn plain_classical_inference_and_private_quantum_precision_are_retained() {
    let source = "
        pub fn ordinary(b:Bit)->Bit{b}
        pub classical fn explicit(b:Bit)->Bit{b}
        pub observe fn broad(b:Bit)->Bit{b}
        fn private_quantum()->Unit{finish(unit(()))}
        pub fn main()->Unit{()}";
    let modules = BTreeMap::from([("main".into(), source.into())]);
    let selected = ParsedProgram::parse(qleisli::edition::Edition::E2026, modules.clone()).unwrap();
    let root = project(&modules);
    let finite = project_effects_with_kernel(
        &root.0,
        SourcePolicy::Legacy,
        &Kernel::selected(qleisli::edition::Edition::E2026).unwrap(),
    )
    .unwrap();
    for name in ["ordinary", "explicit", "main"] {
        let path = format!("main::{name}");
        let fact = selected.function_effect(&path).unwrap();
        assert_eq!(fact.inferred(), Effect::Unitary);
        assert_eq!(fact.public_effect(), Some(Effect::Unitary));
        assert!(!fact.uses_quantum());
        assert_eq!(finite.function_effect(&path), Some(fact));
        assert_eq!(finite.public_function_effect(&path), Some(Effect::Unitary));
    }
    let private = selected.function_effect("main::private_quantum").unwrap();
    assert_eq!(private.inferred(), Effect::Unitary);
    assert!(private.uses_quantum());
    assert_eq!(private.public_effect(), None);
    assert_eq!(
        finite.function_effect("main::private_quantum"),
        Some(private)
    );
    let broad = selected.function_effect("main::broad").unwrap();
    assert_eq!(broad.inferred(), Effect::Unitary);
    assert_eq!(broad.public_effect(), Some(Effect::Observe));
    assert_eq!(finite.function_effect("main::broad"), Some(broad));
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn public_observe_identity_retains_actual_unitary_raw_and_same_module_precision() {
    let modules = sources(
        "use library::{provider,internal};
        pub observe fn entry(q:Q<Bit>)->Q<Bit>{provider(internal(q))}",
        "pub observe fn provider(q:Q<Bit>)->Q<Bit>{q}
        pub unitary fn internal(q:Q<Bit>)->Q<Bit>{provider(q)}",
    );
    let root = project(&modules);
    let kernel = Kernel::selected(qleisli::edition::Edition::E2026).unwrap();
    let finite = project_effects_with_kernel(&root.0, SourcePolicy::Legacy, &kernel).unwrap();
    let selected = ParsedProgram::parse(qleisli::edition::Edition::E2026, modules).unwrap();
    for (path, internal, public) in [
        ("library::provider", Effect::Unitary, Effect::Observe),
        ("library::internal", Effect::Unitary, Effect::Unitary),
        ("main::entry", Effect::Observe, Effect::Observe),
    ] {
        let fact = selected.function_effect(path).unwrap();
        assert_eq!(fact.inferred(), internal, "{path}");
        assert_eq!(fact.public_effect(), Some(public), "{path}");
        assert_eq!(finite.function_effect(path), Some(fact), "{path}");
        assert_eq!(selected.public_function_effect(path), Some(public));
        assert_eq!(finite.public_function_effect(path), Some(public));
    }
    let elaborated = selected
        .instantiate("main::entry", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap();
    assert_eq!(
        elaborated.definitions()[elaborated.root()].effect(),
        "unitary"
    );
    let proposal = elaborated
        .lower_raw_with_kernel(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK))
        .unwrap();
    let accepted = kernel.accept(proposal.proposal()).unwrap();
    assert_eq!(accepted.derived_effect(), Effect::Unitary);
    assert_eq!(accepted.raw().declared_effect, Effect::Unitary);
    proposal.validate_source_steps(&accepted).unwrap();
    let documentation = selected.documentation("library").unwrap().unwrap();
    assert!(documentation.contains("Public quantum effect: `Observe`"));
    assert!(documentation.contains("Public quantum effect: `Unitary`"));
    assert!(!documentation.contains("Inferred quantum effect:"));

    // Ordinary project compilation has a closed classical entry. A separate
    // zero-width quantum example tests its actual Raw classification honestly.
    let closed = sources(
        "use library::scalar;pub observe fn main()->Unit{scalar()}",
        "pub observe fn scalar()->Unit{finish(unit(()))}",
    );
    let accepted = compile_project(&project(&closed).0).unwrap();
    assert_eq!(accepted.derived_effect(), Effect::Unitary);
    assert_eq!(accepted.raw().declared_effect, Effect::Unitary);
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn body_only_reset_keeps_the_public_contract_and_the_selected_unsupported_barrier() {
    let main = "use library::provider;pub observe fn entry(q:Q<Bit>)->Q<Bit>{provider(q)}";
    let kernel = Kernel::selected(qleisli::edition::Edition::E2026).unwrap();
    for (library, actual) in [(IDENTITY, Effect::Unitary), (RESET, Effect::Observe)] {
        let modules = sources(main, library);
        let root = project(&modules);
        let finite = project_effects_with_kernel(&root.0, SourcePolicy::Legacy, &kernel).unwrap();
        assert_eq!(
            finite.public_function_effect("library::provider"),
            Some(Effect::Observe)
        );
        assert_eq!(
            finite.public_function_effect("main::entry"),
            Some(Effect::Observe)
        );
        assert_eq!(
            finite
                .function_effect("library::provider")
                .unwrap()
                .inferred(),
            actual
        );
        let selected = ParsedProgram::parse(qleisli::edition::Edition::E2026, modules).unwrap();
        assert_eq!(
            selected.public_function_effect("library::provider"),
            Some(Effect::Observe)
        );
        assert_eq!(
            selected.function_effect("main::entry").unwrap().inferred(),
            Effect::Observe
        );
        let elaborated = selected
            .instantiate("main::entry", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate();
        if actual == Effect::Observe {
            let error = elaborated.unwrap_err();
            assert_eq!(error.code(), "unsupported", "{error}");
            assert!(
                error.message().contains("does not support discard"),
                "{error}"
            );
        } else {
            elaborated.unwrap().lower_raw().unwrap();
        }
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn provider_cache_order_keeps_external_isometry_bounds_and_actual_raw_separate() {
    // Identical arrow ports normalize to Op<A>'s Unitary ceiling. Distinct
    // exact trees retain the genuine apply-only general-arrow Isometry bound.
    let library = "
        pub isometry fn provider(q:Q<(Unit,Bit)>)->Q<Bit>{let(u,b)=split(q);finish(u);b}
        fn local_apply[const U:Op<(Unit,Bit) -> Bit>](q:Q<(Unit,Bit)>)->Q<Bit>
            requires Applicable(U),Adjointable(U){U(q)}
        pub unitary fn internal(q:Q<(Unit,Bit)>)->Q<Bit>{local_apply[provider](q)}";
    for body in [
        "apply[provider](join(unit(()),internal(q)))",
        "internal(join(unit(()),apply[provider](q)))",
    ] {
        let modules = sources(
            &format!(
                "use library::{{provider,internal}};
                fn apply[const U:Op<(Unit,Bit) -> Bit>](q:Q<(Unit,Bit)>)->Q<Bit> requires Applicable(U){{U(q)}}
                pub isometry fn entry(q:Q<(Unit,Bit)>)->Q<Bit>{{{body}}}"
            ),
            library,
        );
        let root = project(&modules);
        let selected = ParsedProgram::parse(qleisli::edition::Edition::E2026, modules).unwrap();
        assert_eq!(
            selected.function_effect("main::entry").unwrap().inferred(),
            Effect::Isometry
        );
        let finite = project_effects_with_kernel(
            &root.0,
            SourcePolicy::Legacy,
            &Kernel::selected(qleisli::edition::Edition::E2026).unwrap(),
        )
        .unwrap();
        assert_eq!(
            finite.function_effect("main::entry"),
            selected.function_effect("main::entry")
        );
        let elaborated = selected
            .instantiate("main::entry", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap();
        let proposal = elaborated.lower_raw().unwrap();
        let accepted = Kernel::selected(qleisli::edition::Edition::E2026)
            .unwrap()
            .accept(proposal.proposal())
            .unwrap();
        assert_eq!(accepted.derived_effect(), Effect::Unitary);
        proposal.validate_source_steps(&accepted).unwrap();
    }
}

#[test]
fn observing_contract_source_acceptance_does_not_promise_a_supported_native_profile() {
    let modules = sources(
        "use library::{provider,reference};
        pub observe fn main(q:Q<Bit>)->Q<Bit>{apply_contract(provider,reference,q)}",
        "pub observe fn provider(q:Q<Bit>)->Q<Bit>{q}
        pub observe fn reference(q:Q<Bit>)->Q<Bit>{q}",
    );
    let selected = ParsedProgram::parse(qleisli::edition::Edition::E2026, modules).unwrap();
    assert_eq!(
        selected.function_effect("main::main").unwrap().inferred(),
        Effect::Observe
    );
    let error = selected
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap_err();
    observing_profile_refusal(&error);
}

fn observing_profile_refusal(error: &qleisli::frontend::compile::Error) {
    assert_eq!(error.code(), "unsupported", "{error}");
    assert!(
        error
            .message()
            .contains("actual Observe bodies with observation history"),
        "{error}"
    );
    assert!(
        error
            .message()
            .contains("cannot reclassify Unitary/Isometry Raw artifacts"),
        "{error}"
    );
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn internal_pure_contract_remains_usable_under_broader_public_provider_bounds() {
    let modules = sources(
        "use library::internal;pub unitary fn entry(q:Q<Bit>)->Q<Bit>{internal(q)}",
        "pub observe fn provider(q:Q<Bit>)->Q<Bit>{q}
        pub observe fn reference(q:Q<Bit>)->Q<Bit>{q}
        pub unitary fn internal(q:Q<Bit>)->Q<Bit>{apply_contract(provider,reference,q)}",
    );
    let finite = project_effects_with_kernel(
        &project(&modules).0,
        SourcePolicy::Legacy,
        &Kernel::selected(qleisli::edition::Edition::E2026).unwrap(),
    )
    .unwrap();
    assert_eq!(
        finite.function_effect("main::entry").unwrap().inferred(),
        Effect::Unitary
    );
    let elaborated = ParsedProgram::parse(qleisli::edition::Edition::E2026, modules)
        .unwrap()
        .instantiate("main::entry", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap();
    let kernel = Kernel::selected(qleisli::edition::Edition::E2026).unwrap();
    let checked = elaborated
        .check_function_contracts(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK))
        .unwrap();
    let proposal = checked
        .lower_raw_with_kernel(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK))
        .unwrap();
    let accepted = kernel.accept(proposal.proposal()).unwrap();
    assert_eq!(accepted.derived_effect(), Effect::Unitary);
    proposal.validate_source_steps(&accepted).unwrap();
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn dormant_external_observe_obligations_cannot_reuse_an_internal_pure_pair() {
    let library = "pub observe fn provider(q:Q<Bit>)->Q<Bit>{q}
        pub observe fn reference(q:Q<Bit>)->Q<Bit>{q}
        pub unitary fn internal(q:Q<Bit>)->Q<Bit>{apply_contract(provider,reference,q)}";
    for main in [
        "use library::{provider,reference,internal};
        fn unused[const U:Op<Bit>](q:Q<Bit>)->Q<Bit>{apply_contract(provider,reference,q)}
        pub unitary fn main(q:Q<Bit>)->Q<Bit>{internal(q)}",
        "use library::{provider,reference};
        pub observe fn main(q:Q<Bit>)->Q<Bit>{qfor static i in 0..0 carry a=q {yield apply_contract(provider,reference,a)}}",
    ] {
        // Original library obligations precede consumer obligations, so fresh
        // checking first obtains the valid internal pure pair for these IDs.
        let elaborated = ParsedProgram::parse(qleisli::edition::Edition::E2026, sources(main, library))
            .unwrap()
            .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap();
        let error = elaborated
            .check_function_contracts(&Kernel::selected(qleisli::edition::Edition::E2026).unwrap(), &mut Budget::new(DEFAULT_EXACT_WORK))
            .unwrap_err();
        observing_profile_refusal(&error);
    }
}
