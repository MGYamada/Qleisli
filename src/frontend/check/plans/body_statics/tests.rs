use super::*;
use crate::frontend::resolve::locals::{Forest, OccurrencesForest};

fn checked(source: &str) -> CheckedProgram {
    let module = crate::frontend::parser::parse_module(source).unwrap();
    crate::frontend::check::program_with(
        BTreeMap::from([("main", &module)]),
        SourceLimits::selected(),
        |_, _, _, _, _, _, _| Ok(()),
    )
    .unwrap()
    .0
}

const BODY: &str = "
    unitary fn f[const n:Nat](q:Q<Unit>)->Q<Unit>{
        static let k=n-n;
        if static k==0 {qfor static i in 0..0 carry r=q {yield global_phase_eighth(r);}}
        else {q}
    }";

#[test]
fn identity_and_sealed_only_static_bodies_retain_all_original_plans() {
    let program = checked(BODY);
    assert!(program.static_calls.is_empty());
    let binding = program
        .body_statics
        .values()
        .find(|plan| matches!(plan.kind, BodyStaticKind::Binding { .. }))
        .unwrap();
    let BodyStaticKind::Binding { key, value } = &binding.kind else {
        unreachable!()
    };
    assert!(matches!(value.kind, ResolvedNaturalKind::Sub(..)));
    assert!(!binding.environment.naturals.contains_key(key));
    let predicate = program
        .body_statics
        .values()
        .find(|plan| matches!(plan.kind, BodyStaticKind::Predicate { .. }))
        .unwrap();
    assert!(matches!(
        predicate.environment.local_naturals.get(key),
        Some(NaturalBindingPlan::Initializer(_))
    ));
    let fold = program
        .body_statics
        .values()
        .find(|plan| matches!(plan.kind, BodyStaticKind::Fold { .. }))
        .unwrap();
    let BodyStaticKind::Fold {
        index, carry_type, ..
    } = &fold.kind
    else {
        unreachable!()
    };
    assert!(carry_type.linear());
    assert!(!fold.environment.naturals.contains_key(index));
    assert_eq!(fold.environment.regions.len(), 1);
    assert_eq!(
        program
            .body_statics
            .values()
            .filter(|plan| matches!(plan.kind, BodyStaticKind::Natural { .. }))
            .count(),
        4
    );
}

#[test]
fn zero_body_primitive_naturals_keep_ordered_categories_aliases_and_fold_scope() {
    let program = checked(
        "
        unitary fn f[const n:Nat](q:Q<Bit>)->Q<Bit>{
            static let k=n-n;
            qfor static i in 0..0 carry r=q {yield phase[k,i+1](r);}
        }",
    );
    assert!(program.static_calls.is_empty());
    let plan = program
        .body_statics
        .values()
        .find(|plan| matches!(plan.kind, BodyStaticKind::PrimitiveCall { .. }))
        .unwrap();
    let BodyStaticKind::PrimitiveCall { callee, arguments } = &plan.kind else {
        unreachable!()
    };
    assert!(matches!(
        callee.target,
        ResolvedUse::Global(resolve::Target::Primitive(_))
    ));
    assert_eq!(arguments.len(), 2);
    let ResolvedStaticKind::Name(alias) = &arguments[0].kind else {
        panic!("bare original Nat names must not be fabricated into Natural ASTs");
    };
    assert!(matches!(
        plan.environment
            .local_naturals
            .get(alias.local.as_ref().unwrap()),
        Some(NaturalBindingPlan::Initializer(_))
    ));
    let ResolvedStaticKind::Natural(value) = &arguments[1].kind else {
        panic!("original sum")
    };
    assert!(matches!(value.kind, ResolvedNaturalKind::Add(..)));
    assert!(
        plan.environment
            .local_naturals
            .values()
            .any(|value| matches!(value, NaturalBindingPlan::FoldIndex { .. }))
    );
    assert!(matches!(
        plan.environment.regions.as_slice(),
        [StaticRegion::Fold { .. }]
    ));
}

#[test]
fn pretransfer_validation_rejects_changed_predicates_and_missing_body_sites() {
    let program = checked(BODY);
    let module = crate::frontend::parser::parse_module(BODY).unwrap();
    crate::frontend::check::program_with(
        BTreeMap::from([("main", &module)]),
        SourceLimits::selected(),
        |resolution, interfaces, helpers, _, _, indices, budget| {
            let validation = Validation {
                indices,
                helpers,
                interfaces,
                resolution,
                budget,
            };
            validation.body_statics(&program.body_statics).unwrap();
            let mut changed = program.body_statics.clone();
            let predicate = changed
                .values_mut()
                .find(|plan| matches!(plan.kind, BodyStaticKind::Predicate { .. }))
                .unwrap();
            let BodyStaticKind::Predicate { left, .. } = &mut predicate.kind else {
                unreachable!()
            };
            Arc::make_mut(left).kind = ResolvedNaturalKind::Number(17);
            assert!(validation.body_statics(&changed).is_err());
            let mut missing = program.body_statics.clone();
            let node = *missing
                .iter()
                .find(|(_, plan)| matches!(plan.kind, BodyStaticKind::Fold { .. }))
                .unwrap()
                .0;
            missing.remove(&node);
            assert!(validation.body_statics(&missing).is_err());
            Ok(())
        },
    )
    .unwrap();
}

#[test]
fn posttransfer_borrowed_access_refuses_cloned_syntax_and_another_owner() {
    let source = "unitary fn guard(q:Q<Unit>)->Q<Unit>{q}
        unitary fn f[const n:Nat](q:Q<Unit>)->Q<Unit>{if static n==0 {q}else{q}}";
    let module = crate::frontend::parser::parse_module(source).unwrap();
    let (program, occurrences) = crate::frontend::check::program_with(
        BTreeMap::from([("main", &module)]),
        SourceLimits::selected(),
        |_, _, _, _, _, indices, budget| {
            let mut occurrences = OccurrencesForest::default();
            for index in indices.values_mut() {
                occurrences.insert_budgeted(
                    index.take_occurrences(),
                    Span::default(),
                    |span, cells| budget.charge(span, cells),
                )?;
            }
            Ok(occurrences)
        },
    )
    .unwrap();
    let forest = Forest::from_occurrences(occurrences);
    let locals = forest.lookup(&program.lexical);
    let owner = program.resolution.qualified("main::f").unwrap();
    let guard = program.resolution.qualified("main::guard").unwrap();
    let module_id = program.resolution.declaration(owner).module;
    let ast::FnBody::Quantum(body) = &module.decls[1].body else {
        unreachable!()
    };
    let original = &body.result;
    let copy = original.clone();
    let mut used = 0;
    let mut charge = |_: Span, cells| {
        used += cells;
        Ok::<_, SourceError>(())
    };
    let error = |span, message| SourceError::new("source", span, message);
    original_body_static(
        &program,
        &locals,
        owner,
        module_id,
        BodyStaticOriginal::Expression(original),
        &mut charge,
        &error,
    )
    .unwrap();
    assert!(
        original_body_static(
            &program,
            &locals,
            guard,
            module_id,
            BodyStaticOriginal::Expression(original),
            &mut charge,
            &error
        )
        .is_err()
    );
    assert!(
        original_body_static(
            &program,
            &locals,
            owner,
            module_id,
            BodyStaticOriginal::Expression(&copy),
            &mut charge,
            &error
        )
        .is_err()
    );
    assert!(used > 0);
}

#[test]
fn an_empty_static_fold_still_receives_complete_original_ownership_checking() {
    let source = "unitary fn f(q:Q<Unit>)->Q<Unit>{
        qfor static i in 0..0 carry r=q {let lost=r;yield r;}
    }";
    let module = crate::frontend::parser::parse_module(source).unwrap();
    let failure = crate::frontend::check::program_with(
        BTreeMap::from([("main", &module)]),
        SourceLimits::selected(),
        |_, _, _, _, _, _, _| Ok(()),
    )
    .unwrap_err();
    assert_eq!(failure.code, "ownership");
}

#[test]
fn posttransfer_access_rejects_a_different_checked_collection_with_identical_ids() {
    fn prepare(module: &ast::Module) -> (CheckedProgram, OccurrencesForest<'_>) {
        crate::frontend::check::program_with(
            BTreeMap::from([("main", module)]),
            SourceLimits::selected(),
            |_, _, _, _, _, indices, budget| {
                let mut occurrences = OccurrencesForest::default();
                for index in indices.values_mut() {
                    occurrences.insert_budgeted(
                        index.take_occurrences(),
                        Span::default(),
                        |span, cells| budget.charge(span, cells),
                    )?;
                }
                Ok(occurrences)
            },
        )
        .unwrap()
    }
    let source = "unitary fn f[const n:Nat](q:Q<Unit>)->Q<Unit>{if static n==0 {q}else{q}}";
    let module = crate::frontend::parser::parse_module(source).unwrap();
    let identical = crate::frontend::parser::parse_module(source).unwrap();
    let (program, occurrences) = prepare(&module);
    let (other, _) = prepare(&identical);
    // Even a second checking of the very same borrowed AST is a distinct
    // checked collection. Original source addresses alone cannot bind it.
    let (same_ast_other, _) = prepare(&module);
    let forest = Forest::from_occurrences(occurrences);
    let locals = forest.lookup(&program.lexical);
    let owner = program.resolution.qualified("main::f").unwrap();
    let module_id = program.resolution.declaration(owner).module;
    let ast::FnBody::Quantum(body) = &module.decls[0].body else {
        unreachable!()
    };
    let original = BodyStaticOriginal::Expression(&body.result);
    let error = |span, message| SourceError::new("source", span, message);
    original_body_static(
        &program,
        &locals,
        owner,
        module_id,
        original,
        &mut |_, _| Ok(()),
        &error,
    )
    .unwrap();
    for foreign in [&other, &same_ast_other] {
        assert_eq!(foreign.resolution.qualified("main::f"), Ok(owner));
        assert!(
            original_body_static(
                foreign,
                &locals,
                owner,
                module_id,
                original,
                &mut |_, _| Ok(()),
                &error
            )
            .is_err()
        );
    }
}

const OPERATIONS: &str = "unitary fn guard(q:Q<Bit>)->Q<Bit>{q}
    unitary fn f[const U:Op<Bit>](c:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>)
    requires Applicable(U),Adjointable(U),Controllable(U){
        let q=power(U,0)(q);
        let q=adjoint(U)(q);
        controlled(U)(c,q)
    }";

#[test]
fn every_runtime_operation_root_is_retained_without_an_incidental_call() {
    let program = checked(OPERATIONS);
    assert!(program.static_calls.is_empty());
    let roots: Vec<_> = program
        .body_statics
        .values()
        .filter_map(|plan| {
            let BodyStaticKind::Operation { operation, .. } = &plan.kind else {
                return None;
            };
            assert_eq!(operation.node, Some(plan.node));
            assert_eq!(plan.environment.owner, plan.owner);
            Some(operation)
        })
        .collect();
    assert_eq!(roots.len(), 3);
    assert_eq!(
        roots
            .iter()
            .filter(|operation| matches!(operation.kind, ResolvedStaticKind::Repeat { .. }))
            .count(),
        1
    );
    assert_eq!(
        roots
            .iter()
            .filter(|operation| matches!(operation.kind, ResolvedStaticKind::Name(_)))
            .count(),
        2
    );
    let demands: BTreeSet<_> = program
        .body_statics
        .values()
        .filter_map(|plan| {
            let BodyStaticKind::Operation {
                requested,
                expression,
                ..
            } = &plan.kind
            else {
                return None;
            };
            assert_eq!(
                program.lexical[&plan.owner]
                    .try_node(*expression)
                    .unwrap()
                    .kind,
                NodeKind::Expr
            );
            Some(*requested)
        })
        .collect();
    assert_eq!(
        demands,
        BTreeSet::from([
            [true, false, false],
            [false, true, false],
            [false, false, true]
        ])
    );

    let module = crate::frontend::parser::parse_module(OPERATIONS).unwrap();
    crate::frontend::check::program_with(
        BTreeMap::from([("main", &module)]),
        SourceLimits::selected(),
        |resolution, interfaces, helpers, _, _, indices, budget| {
            let validation = Validation {
                indices,
                helpers,
                interfaces,
                resolution,
                budget,
            };
            validation.body_statics(&program.body_statics).unwrap();
            let mut changed = program.body_statics.clone();
            let plan = changed
                .values_mut()
                .find(|plan| {
                    matches!(&plan.kind,
                BodyStaticKind::Operation { operation, .. }
                    if matches!(operation.kind, ResolvedStaticKind::Repeat { .. }))
                })
                .unwrap();
            let BodyStaticKind::Operation { operation, .. } = &mut plan.kind else {
                unreachable!()
            };
            let ResolvedStaticKind::Repeat { count, .. } = &mut Arc::make_mut(operation).kind
            else {
                unreachable!()
            };
            count.kind = ResolvedNaturalKind::Number(17);
            assert!(validation.body_statics(&changed).is_err());
            let mut missing = program.body_statics.clone();
            let node = *missing
                .iter()
                .find(|(_, plan)| matches!(plan.kind, BodyStaticKind::Operation { .. }))
                .unwrap()
                .0;
            missing.remove(&node);
            assert!(validation.body_statics(&missing).is_err());
            let mut changed_demand = program.body_statics.clone();
            let plan = changed_demand
                .values_mut()
                .find(|plan| matches!(plan.kind, BodyStaticKind::Operation { .. }))
                .unwrap();
            let BodyStaticKind::Operation { requested, .. } = &mut plan.kind else {
                unreachable!()
            };
            *requested = [false; 3];
            assert!(validation.body_statics(&changed_demand).is_err());
            Ok(())
        },
    )
    .unwrap();
}

#[test]
fn borrowed_operation_roots_refuse_clones_other_owners_and_other_collections() {
    let module = crate::frontend::parser::parse_module(OPERATIONS).unwrap();
    let (program, occurrences) = crate::frontend::check::program_with(
        BTreeMap::from([("main", &module)]),
        SourceLimits::selected(),
        |_, _, _, _, _, indices, budget| {
            let mut occurrences = OccurrencesForest::default();
            for index in indices.values_mut() {
                occurrences.insert_budgeted(
                    index.take_occurrences(),
                    Span::default(),
                    |span, cells| budget.charge(span, cells),
                )?;
            }
            Ok(occurrences)
        },
    )
    .unwrap();
    let (other, _) = crate::frontend::check::program_with(
        BTreeMap::from([("main", &module)]),
        SourceLimits::selected(),
        |_, _, _, _, _, _, _| Ok(()),
    )
    .unwrap();
    let forest = Forest::from_occurrences(occurrences);
    let locals = forest.lookup(&program.lexical);
    let owner = program.resolution.qualified("main::f").unwrap();
    let guard = program.resolution.qualified("main::guard").unwrap();
    let module_id = program.resolution.declaration(owner).module;
    let ast::FnBody::Quantum(body) = &module.decls[1].body else {
        unreachable!()
    };
    let ast::ExprKind::Controlled { operation, .. } = &body.result.kind else {
        unreachable!()
    };
    let copied = operation.clone();
    let error = |span, message| SourceError::new("source", span, message);
    let plan = original_body_static(
        &program,
        &locals,
        owner,
        module_id,
        BodyStaticOriginal::Operation(operation),
        &mut |_, _| Ok(()),
        &error,
    )
    .unwrap();
    assert!(matches!(plan.kind, BodyStaticKind::Operation { .. }));
    for (checked, expected_owner, original) in [
        (&program, guard, operation),
        (&program, owner, &copied),
        (&other, owner, operation),
    ] {
        assert!(
            original_body_static(
                checked,
                &locals,
                expected_owner,
                module_id,
                BodyStaticOriginal::Operation(original),
                &mut |_, _| Ok(()),
                &error
            )
            .is_err()
        );
    }
}
