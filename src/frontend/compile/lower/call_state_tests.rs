//! Refused expansions preserve the suspended caller, without rewinding Raw state.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;
use crate::frontend::project::{ModuleOrigin, SourceModule};

pub(super) fn checked_compiler(project: &Project) -> Compiler<'_> {
    let PreparedSource {
        checked: source,
        occurrences,
        interface_naturals,
    } = prepare_original_source(Path::new("main.qli"), project)
        .expect("complete original source judgment");
    let declarations = source
        .resolution
        .declarations()
        .map(|(id, declaration)| {
            (
                id,
                &project.modules[&declaration.name.0].ast.decls[declaration.ast_index],
            )
        })
        .collect();
    Compiler {
        kernel: crate::interchange::native::Kernel::selected().expect("explicit test kernel"),
        project,
        source,
        interface_naturals,
        locals: Forest::from_occurrences(occurrences),
        declarations,
        basis: BTreeMap::new(),
        checked: BTreeMap::new(),
        function_evidence: BTreeMap::new(),
        instrument_evidence: BTreeMap::new(),
        source_rows: BTreeMap::new(),
        source_sets: BTreeMap::new(),
        pure_equations: Vec::new(),
        computed_normalizations: Vec::new(),
        meanings: BTreeMap::new(),
        providers: BTreeMap::new(),
        instances: Vec::new(),
        concrete_context: Default::default(),
        work: 0,
        checking: None,
        exact_work: crate::contract::exact::Budget::new(crate::contract::DEFAULT_EXACT_WORK),
        closed_meanings: BTreeMap::new(),
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn body_budget_refusal_restores_effect_context_but_keeps_raw_owners_and_work() {
    let text = " isometry fn make() -> Q<Unit> { let u = unit(()); u }";
    let project = Project {
        root: PathBuf::from("main.qli"),
        modules: BTreeMap::from([(
            "main".into(),
            SourceModule {
                name: "main".into(),
                path: PathBuf::from("main.qli"),
                source: text.into(),
                ast: crate::frontend::parser::parse_module(text).expect("first source"),
                imports: BTreeMap::new(),
                origin: ModuleOrigin::Local,
            },
        )]),
    };
    let mut compiler = checked_compiler(&project);
    let key = compiler.source.resolution.qualified("main::make").unwrap();
    let caller_span = Span { start: 0, end: 3 };
    let caller_origin = Some(("main".to_owned(), caller_span));
    let mut refusals_after_allocation = 0;
    let mut successes = 0;
    // Vary host work around one zero-qubit body. This is not a maximum-width
    // quantum case, and no rejected result is submitted for native acceptance.
    for remaining in 0..=4096 {
        let started = MAX_WORK - remaining;
        compiler.work = started;
        let mut lower = Lowerer {
            compiler: &mut compiler,
            raw: RawState::new(),
            operation_sources: BTreeMap::new(),
            instrument_calls: Vec::new(),
            tuple_binding_origins: vec![BTreeMap::new()],
            access_updates: vec![BTreeSet::new()],
            effect: Effect::Observe,
            contract_effect: Effect::Observe,
            effect_source: caller_origin.clone(),
            depth: 0,
            bindings: BTreeMap::new(),
        };
        // Keep an unrelated zero-width logical owner in the complete caller.
        let suspended = lower.raw.register(Ty::empty_bits(), Vec::new());
        let suspended_token = lower.raw.registers[&suspended].token;
        let result = lower.call_user(&key, Vec::new(), None);
        assert_eq!(lower.depth, 0);
        assert_eq!(lower.tuple_binding_origins.len(), 1);
        assert_eq!(lower.access_updates.len(), 1);
        assert_eq!(lower.effect, Effect::Observe);
        assert_eq!(lower.contract_effect, Effect::Observe);
        assert_eq!(lower.effect_source, caller_origin);
        assert_eq!(lower.compiler.checking, None);
        assert_eq!(lower.compiler.current_instance_owner(), None);
        assert!(lower.compiler.concrete_context.current.is_none());
        assert!(lower.compiler.concrete_context.naturals.is_empty());
        assert_eq!(lower.raw.registers[&suspended].token, suspended_token);
        assert_eq!(lower.raw.registers[&suspended].basis, Ty::empty_bits());
        assert!(lower.compiler.work >= started);
        match result {
            Err(error) => {
                assert_eq!(error.code, ErrorCode::Limit);
                if lower.raw.registers.len() > 1 {
                    refusals_after_allocation += 1;
                    // Work diagnostics are anchored to the active original
                    // declaration. A retained body allocation independently
                    // witnesses entry into the callee's private effect frame.
                    // A failed body retains its issued identity. The next
                    // token must be later than every still-retained owner.
                    let maximum = lower
                        .raw
                        .registers
                        .values()
                        .map(|r| r.token.0)
                        .max()
                        .unwrap();
                    assert!(lower.raw.token().0 > maximum);
                    assert!(lower.compiler.work > started);
                }
            }
            Ok(value) => {
                assert_eq!(value.ty(), Ty::quantum(Ty::unit()));
                successes += 1;
            }
        }
        if successes > 0 && refusals_after_allocation > 0 {
            break;
        }
    }
    assert!(
        refusals_after_allocation > 0,
        "must exercise a partially emitted body"
    );
    assert!(successes > 0, "must include an in-budget control");
}
