use super::*;

const CONTROL_OWNERS: &str = "unitary fn zero(q:Q<Bits<0>>)->Q<Bits<0>>{q}
    unitary fn keep(a:Q<Bit>,b:Q<Unit>,c:Q<Bits<0>>)->(Q<Bit>,Q<Unit>,Q<Bits<0>>){(a,b,c)}
    unitary fn f[const U:Op<Bit>](z:Q<Bits<0>>,u:Q<Unit>,b:Q<Bit>)->(Q<Bits<0>>,Q<Unit>,Q<Bit>)
    requires Applicable(U){
        let alias=z;
        zero(ctrl alias);
        qfor static i in 0..0 carry (r_z,r_u,r_b)=(alias,u,b){
            keep(ctrl r_b,excl r_u,excl r_z);
            yield (r_z,r_u,r_b);
        }
    }";

fn checked(source: &str) -> CheckedProgram {
    use crate::frontend::source::{Builder, BundledRegistry, ParsePolicy, Source};
    crate::frontend::project::check_bundled_manifest().unwrap();
    let mut builder = Builder::default();
    builder
        .insert(
            Source::local("main".into(), None, source.into(), ParsePolicy::Project).unwrap_or_else(
                |failure| panic!("ordinary source {} at {:?}", failure.name, failure.span()),
            ),
        )
        .unwrap();
    for bundled in BundledRegistry::sources() {
        builder
            .insert(
                Source::bundled(bundled, ParsePolicy::Project).unwrap_or_else(|failure| {
                    panic!("ordinary source {} at {:?}", failure.name, failure.span())
                }),
            )
            .unwrap();
    }
    let sources = builder.finish();
    super::super::program_with(
        sources
            .iter()
            .map(|(name, source)| (name, source.syntax()))
            .collect(),
        SourceLimits::selected(),
        |_, _, _, _, _, _, _| Ok(()),
    )
    .unwrap()
    .0
}

#[test]
fn control_snapshots_retain_original_alias_carry_types_and_call_order() {
    let program = checked(CONTROL_OWNERS);
    let owner = program.resolution.qualified("main::f").unwrap();
    let snapshots: Vec<_> = program
        .obligations
        .iter()
        .filter(|obligation| {
            obligation.definition == owner
                && matches!(obligation.kind, ObligationKind::ControlSectors)
        })
        .collect();
    assert_eq!(snapshots.len(), 2);
    let alias = &snapshots[0].plan.runtime_owners;
    assert_eq!(alias.len(), 1);
    assert_eq!(alias[0].reference.local.as_ref().unwrap().name, "alias");
    assert_eq!(*alias[0].ty, Ty::quantum(Ty::bits(Linear::constant(0))));
    let carry = &snapshots[1].plan.runtime_owners;
    assert_eq!(
        carry
            .iter()
            .map(|binding| binding.reference.local.as_ref().unwrap().name.as_str())
            .collect::<Vec<_>>(),
        ["r_b", "r_u", "r_z"]
    );
    assert_eq!(*carry[0].ty, Ty::quantum(Ty::bit()));
    assert_eq!(*carry[1].ty, Ty::quantum(Ty::unit()));
    assert_eq!(*carry[2].ty, Ty::quantum(Ty::bits(Linear::constant(0))));
    assert_ne!(carry[1].ty, carry[2].ty);
    assert!(
        program
            .obligations
            .iter()
            .filter(|obligation| !matches!(obligation.kind, ObligationKind::ControlSectors))
            .all(|obligation| obligation.plan.runtime_owners.is_empty())
    );

    let module = crate::frontend::parser::parse_module(CONTROL_OWNERS).unwrap();
    super::super::program_with(
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
            let original = snapshots[1];
            let verify = |owners: &[RuntimeOwnerPlan]| {
                validation.runtime_owners(
                    owner,
                    original.plan.node,
                    &original.kind,
                    owners,
                    original.span,
                )
            };
            verify(carry).unwrap();
            let mut swapped = carry.clone();
            swapped.swap(0, 1);
            assert!(verify(&swapped).is_err());
            assert!(verify(&carry[..2]).is_err());
            let mut ordinary = carry.clone();
            ordinary[0].ty = Arc::new(Ty::bit());
            assert!(verify(&ordinary).is_err());
            let mut replaced = carry.clone();
            replaced[2].ty = Arc::new(Ty::quantum(Ty::unit()));
            assert!(verify(&replaced).is_err());
            Ok(())
        },
    )
    .unwrap();
}

#[test]
fn borrowed_control_snapshots_require_the_canonical_original_judgment() {
    use crate::frontend::resolve::locals::{Forest, OccurrencesForest, OriginalNode};
    let module = crate::frontend::parser::parse_module(CONTROL_OWNERS).unwrap();
    let (mut program, occurrences) = super::super::program_with(
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
    let (other, _) = super::super::program_with(
        BTreeMap::from([("main", &module)]),
        SourceLimits::selected(),
        |_, _, _, _, _, _, _| Ok(()),
    )
    .unwrap();
    let forest = Forest::from_occurrences(occurrences);
    let locals = forest.lookup(&program.lexical);
    let owner = program.resolution.qualified("main::f").unwrap();
    let module_id = program.resolution.declaration(owner).module;
    let obligation = program
        .obligations
        .iter()
        .find(|obligation| {
            obligation.definition == owner && obligation.plan.runtime_owners.len() == 3
        })
        .unwrap();
    let ordinal = obligation.id.ordinal;
    let Some(OriginalNode::Expression(original)) = locals
        .original_node_budgeted(obligation.plan.node, |_, _| Ok::<_, SourceError>(()))
        .unwrap()
    else {
        unreachable!()
    };
    let copied_expression = original.clone();
    let copied_judgment = obligation.clone();
    let error = |span, message| SourceError::new("source", span, message);
    let owners = original_runtime_owners(
        &program,
        &locals,
        owner,
        module_id,
        original,
        obligation,
        &mut |_, _| Ok(()),
        &error,
    )
    .unwrap();
    assert_eq!(owners.len(), 3);
    for (checked, expression, judgment) in [
        (&program, &copied_expression, obligation),
        (&program, original, &copied_judgment),
        (&other, original, &other.obligations[obligation.id.ordinal]),
    ] {
        assert!(
            original_runtime_owners(
                checked,
                &locals,
                owner,
                module_id,
                expression,
                judgment,
                &mut |_, _| Ok(()),
                &error
            )
            .is_err()
        );
    }
    let mut remaining = 0usize;
    let failure = original_runtime_owners(
        &program,
        &locals,
        owner,
        module_id,
        original,
        obligation,
        &mut |span, cells| {
            remaining = remaining
                .checked_sub(cells)
                .ok_or_else(|| SourceError::new("limit", span, "test snapshot budget exhausted"))?;
            Ok(())
        },
        &error,
    )
    .unwrap_err();
    assert_eq!(failure.code, "limit");
    // Canonical collection identity does not authorize replacing its captured
    // common type payload, even with another individually well-formed Q tree.
    program.obligations[ordinal].plan.runtime_owners[2].ty = Arc::new(Ty::quantum(Ty::unit()));
    let replaced = &program.obligations[ordinal];
    assert!(
        original_runtime_owners(
            &program,
            &locals,
            owner,
            module_id,
            original,
            replaced,
            &mut |_, _| Ok(()),
            &error
        )
        .is_err()
    );
}

fn call_in<'a>(program: &'a CheckedProgram, owner: &str, target: &str) -> &'a StaticCallPlan {
    let owner = program.resolution.qualified(owner).unwrap();
    let target = program.resolution.qualified(target).unwrap();
    let mut found = program
        .static_calls
        .values()
        .filter(|call| call.owner == owner && call.target == target);
    let call = found.next().expect("original call");
    assert!(found.next().is_none(), "one original source occurrence");
    call
}

#[test]
fn dormant_checked_operation_and_zero_repeat_keep_the_complete_original_tree() {
    let program = checked(
        "use std::gate::x;
         unitary fn candidate(q:Q<Bit>)->Q<Bit>{x(q)}
         classical fn phase_z(b:Bit)->(Bit,(Bit,Bit)){(0,(0,b))}
         meaning Z:Bit=phase_by(phase_z);
         unitary fn apply[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}
         unitary fn dormant[const A:Basis](q:Q<A>,r:Q<Bit>)->(Q<A>,Q<Bit>){
             let r=apply[power(checked_op(candidate,Z),0)](r);(q,r)
         }
         pub unitary fn main(q:Q<Bit>)->Q<Bit>{q}",
    );
    let call = call_in(&program, "main::dormant", "main::apply");
    assert_eq!(call.source_effect, Some(crate::ir::Effect::Unitary));
    assert_eq!(call.arguments.len(), 1);
    let ResolvedStaticKind::Repeat { count, child, .. } = &call.arguments[0].value.kind else {
        panic!("zero repetition remains a constructor");
    };
    assert!(matches!(count.kind, ResolvedNaturalKind::Number(0)));
    let ResolvedStaticKind::Bind(implementation, specification) = &child.kind else {
        panic!("original checked_op child remains present");
    };
    assert_ne!(implementation.site, specification.site);
    assert_eq!(implementation.site.definition(), call.owner);
    assert_eq!(specification.site.definition(), call.owner);
    let required = program.resolution.qualified("main::Z").unwrap();
    let evidence = program.obligations.iter().find(|obligation| {
        obligation.definition == call.owner
            && matches!(obligation.kind, ObligationKind::MeaningEquality { required: id, .. } if id == required)
    }).expect("unused original Meaning obligation");
    let EvidenceSubject::Operation {
        operation,
        required: Some(contract),
        ..
    } = &evidence.plan.subject
    else {
        panic!("Meaning obligation retains its actual operation subject");
    };
    assert_eq!(contract.meaning, Some(required));
    assert_eq!(operation.node, child.node);
    assert!(matches!(operation.kind, ResolvedStaticKind::Bind(..)));
    assert_eq!(evidence.plan.node, call.node);
}

#[test]
fn normalized_zero_does_not_erase_original_nat_dependencies() {
    let program = checked(
        "unitary fn keep[const m:Nat](q:Q<Bit>)->Q<Bit>{q}
         pub unitary fn f[const n:Nat](q:Q<Bit>)->Q<Bit>{
             static let k=n-n;keep[k](q)
         }",
    );
    let call = call_in(&program, "main::f", "main::keep");
    let ResolvedStaticKind::Name(reference) = &call.arguments[0].value.kind else {
        panic!("original named argument");
    };
    let key = reference.local.as_ref().unwrap();
    let normalized = &call.environment.naturals[key];
    assert_eq!(normalized.constant, 0);
    assert!(normalized.terms.is_empty());
    let NaturalBindingPlan::Initializer(original) = &call.environment.local_naturals[key] else {
        panic!("original local initializer");
    };
    let ResolvedNaturalKind::Sub(a, b) = &original.kind else {
        panic!("subtraction remains");
    };
    let (ResolvedNaturalKind::Name(a), ResolvedNaturalKind::Name(b)) = (&a.kind, &b.kind) else {
        panic!("both original operands remain");
    };
    assert_ne!(a.site, b.site);
    assert_eq!(a.local, b.local);
    let empty = BTreeSet::new();
    let classify = |bound| {
        call.arguments[0]
            .value
            .classify_budgeted(&call.environment, bound, &mut |_, _| Ok(()))
            .unwrap()
    };
    let PlanClosure::Deferred(free) = classify(&empty) else {
        panic!("unbound n cannot be cancelled");
    };
    assert_eq!(free, BTreeSet::from([a.local.clone().unwrap()]));
    assert!(matches!(classify(&free), PlanClosure::Closed));
}

#[test]
fn original_helper_and_intermediate_arithmetic_survive_affine_normalization() {
    let program = checked(
        "static fn next[const n:Nat]()->Nat{n+1}
         unitary fn keep[const m:Nat](q:Q<Bit>)->Q<Bit>{q}
         pub unitary fn f[const n:Nat](q:Q<Bit>)->Q<Bit>{
             static let k=(n+4294967295)-4294967295;
             let q=keep[next[4294967295]()](q);keep[k](q)
         }",
    );
    let owner = program.resolution.qualified("main::f").unwrap();
    let calls: Vec<_> = program
        .static_calls
        .values()
        .filter(|call| call.owner == owner)
        .collect();
    assert_eq!(calls.len(), 2);
    let helper_call = calls
        .iter()
        .find(|call| matches!(call.arguments[0].value.kind, ResolvedStaticKind::Natural(_)))
        .unwrap();
    let ResolvedStaticKind::Natural(value) = &helper_call.arguments[0].value.kind else {
        unreachable!();
    };
    let ResolvedNaturalKind::Helper {
        callee,
        template,
        arguments,
    } = &value.kind
    else {
        panic!("original helper call");
    };
    assert_eq!(
        callee.target,
        ResolvedUse::Global(resolve::Target::Declaration(
            program.resolution.qualified("main::next").unwrap()
        ))
    );
    assert_eq!(template.result.constant, 1);
    assert_eq!(template.parameters.len(), 1);
    assert_eq!(arguments.len(), 1);
    assert!(matches!(
        arguments[0].kind,
        ResolvedNaturalKind::Number(4294967295)
    ));
    let named_call = calls
        .iter()
        .find(|call| matches!(call.arguments[0].value.kind, ResolvedStaticKind::Name(_)))
        .unwrap();
    let ResolvedStaticKind::Name(reference) = &named_call.arguments[0].value.kind else {
        unreachable!();
    };
    let NaturalBindingPlan::Initializer(value) =
        &named_call.environment.local_naturals[reference.local.as_ref().unwrap()]
    else {
        unreachable!();
    };
    let ResolvedNaturalKind::Sub(a, b) = &value.kind else {
        panic!("outer subtraction");
    };
    assert!(matches!(a.kind, ResolvedNaturalKind::Add(..)));
    assert!(matches!(b.kind, ResolvedNaturalKind::Number(4294967295)));
}

#[test]
fn basis_arguments_keep_type_tags_and_original_same_spelling_binders() {
    let program = checked(
        "unitary fn identity[const A:Basis](q:Q<A>)->Q<A>{q}
         unitary fn first[const A:Basis](q:Q<A>)->Q<A>{identity[type(A)](q)}
         unitary fn second[const A:Basis](q:Q<A>)->Q<A>{identity[type(A)](q)}
         pub unitary fn f(q:Q<(Unit,Bits<0>)>)->Q<(Unit,Bits<0>)>{identity[type((Unit,Bits<0>))](q)}",
    );
    let a = call_in(&program, "main::first", "main::identity");
    let b = call_in(&program, "main::second", "main::identity");
    let (ResolvedStaticKind::Basis(a_ty), ResolvedStaticKind::Basis(b_ty)) =
        (&a.arguments[0].value.kind, &b.arguments[0].value.kind)
    else {
        panic!("Basis arguments");
    };
    let (Kind::Parameter(a_key), Kind::Parameter(b_key)) = (&a_ty.kind, &b_ty.kind) else {
        panic!("original opaque parameters");
    };
    assert_eq!(a_key.name, b_key.name);
    assert_ne!(a_key.key, b_key.key);
    assert_ne!(a.arguments[0].formal, a_key.key.clone().unwrap());
    assert_eq!(a.arguments[0].value.type_references.len(), 1);
    let call = call_in(&program, "main::f", "main::identity");
    let ResolvedStaticKind::Basis(ty) = &call.arguments[0].value.kind else {
        panic!("concrete product");
    };
    let Kind::Tuple(fields) = &ty.kind else {
        panic!("product tree");
    };
    assert!(matches!(fields[0].kind, Kind::Unit));
    assert!(matches!(fields[1].kind, Kind::Bits(_)));
}

#[test]
fn branch_and_fold_environments_keep_original_guards_and_index_bounds() {
    let program = checked(
        "unitary fn keep[const m:Nat](q:Q<Bit>)->Q<Bit>{q}
         pub unitary fn f[const n:Nat](q:Q<Bit>)->Q<Bit>{
             if static n>0 {qfor static i in 0..n carry r=q {yield keep[i](r);}}else{q}
         }",
    );
    let call = call_in(&program, "main::f", "main::keep");
    assert_eq!(call.environment.regions.len(), 2);
    assert!(matches!(
        call.environment.regions[0],
        StaticRegion::Predicate { truth: true, .. }
    ));
    let StaticRegion::Fold {
        index, start, end, ..
    } = &call.environment.regions[1]
    else {
        panic!("original fold");
    };
    let NaturalBindingPlan::FoldIndex {
        start: retained_start,
        end: retained_end,
    } = &call.environment.local_naturals[index]
    else {
        panic!("original index binding");
    };
    assert!(Arc::ptr_eq(start, retained_start));
    assert!(Arc::ptr_eq(end, retained_end));
    assert!(matches!(start.kind, ResolvedNaturalKind::Number(0)));
    assert!(matches!(end.kind, ResolvedNaturalKind::Name(_)));
}

fn with_validation(source: &str, inspect: impl FnOnce(&Validation<'_, '_>, &ast::Module)) {
    let module = crate::frontend::parser::parse_module(source).unwrap();
    super::super::program_with(
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
            inspect(&validation, &module);
            Ok(())
        },
    )
    .unwrap();
}

fn declaration<'a>(module: &'a ast::Module, name: &str) -> &'a ast::Decl {
    module
        .decls
        .iter()
        .find(|decl| decl.name.text == name)
        .unwrap()
}

fn quantum_body(declaration: &ast::Decl) -> &ast::Block {
    let ast::FnBody::Quantum(body) = &declaration.body else {
        panic!("quantum body");
    };
    body
}

fn static_arguments(body: &ast::Block) -> &[ast::StaticOp] {
    let ast::ExprKind::Call { static_args, .. } = &body.result.kind else {
        panic!("ordinary call");
    };
    static_args
}

#[test]
fn original_natural_literals_operators_and_order_cannot_be_mutated() {
    with_validation(
        "unitary fn f(q:Q<Bit>)->Q<Bit>{static let k=1+2;q}
         unitary fn g(q:Q<Bit>)->Q<Bit>{static let k=3;q}",
        |validation, module| {
            let owner = validation.resolution.qualified("main::f").unwrap();
            let other = validation.resolution.qualified("main::g").unwrap();
            let body = quantum_body(declaration(module, "f"));
            let ast::StmtKind::StaticLet {
                name,
                value: source,
            } = &body.statements[0].kind
            else {
                panic!("static initializer");
            };
            let capture = Capture {
                index: &validation.indices[&owner],
                helpers: validation.helpers,
                budget: validation.budget,
            };
            let original = capture.natural(source).unwrap();
            validation.natural(owner, &original).unwrap();
            let mut changed = original.clone();
            let ResolvedNaturalKind::Add(a, _) = &mut changed.kind else {
                panic!("addition");
            };
            a.kind = ResolvedNaturalKind::Number(9);
            assert!(validation.natural(owner, &changed).is_err());
            let mut changed = original.clone();
            let ResolvedNaturalKind::Add(a, b) = changed.kind else {
                unreachable!()
            };
            changed.kind = ResolvedNaturalKind::Sub(a, b);
            assert!(validation.natural(owner, &changed).is_err());
            let mut changed = original.clone();
            let ResolvedNaturalKind::Add(a, b) = &mut changed.kind else {
                unreachable!()
            };
            std::mem::swap(a, b);
            assert!(validation.natural(owner, &changed).is_err());
            let other_body = quantum_body(declaration(module, "g"));
            let ast::StmtKind::StaticLet {
                value: other_source,
                ..
            } = &other_body.statements[0].kind
            else {
                unreachable!();
            };
            let other_capture = Capture {
                index: &validation.indices[&other],
                ..capture
            };
            let mut changed = original.clone();
            changed.node = other_capture.natural(other_source).unwrap().node;
            assert!(validation.natural(owner, &changed).is_err());
            let key = capture.index.table.key(capture.index.binder(name));
            let mut changed = original.clone();
            changed.kind = ResolvedNaturalKind::Number(3);
            assert!(
                validation
                    .local_initializer(owner, key, &changed, source.span)
                    .is_err()
            );
        },
    );
}

#[test]
fn helper_arguments_keep_original_reference_and_child_sites() {
    with_validation(
        "static fn next[const n:Nat]()->Nat{n+1}
         unitary fn f(q:Q<Bit>)->Q<Bit>{static let k=next[1]()+next[2]();q}",
        |validation, module| {
            let owner = validation.resolution.qualified("main::f").unwrap();
            let body = quantum_body(declaration(module, "f"));
            let ast::StmtKind::StaticLet { value: source, .. } = &body.statements[0].kind else {
                unreachable!()
            };
            let original = Capture {
                index: &validation.indices[&owner],
                helpers: validation.helpers,
                budget: validation.budget,
            }
            .natural(source)
            .unwrap();
            validation.natural(owner, &original).unwrap();
            let mut changed = original.clone();
            let ResolvedNaturalKind::Add(a, b) = &mut changed.kind else {
                unreachable!()
            };
            let (
                ResolvedNaturalKind::Helper { callee: x, .. },
                ResolvedNaturalKind::Helper { callee: y, .. },
            ) = (&mut a.kind, &mut b.kind)
            else {
                unreachable!()
            };
            std::mem::swap(x, y);
            assert!(validation.natural(owner, &changed).is_err());
            let mut changed = original.clone();
            let ResolvedNaturalKind::Add(a, b) = &mut changed.kind else {
                unreachable!()
            };
            let (
                ResolvedNaturalKind::Helper { arguments: x, .. },
                ResolvedNaturalKind::Helper { arguments: y, .. },
            ) = (&mut a.kind, &mut b.kind)
            else {
                unreachable!()
            };
            std::mem::swap(&mut x[0], &mut y[0]);
            assert!(validation.natural(owner, &changed).is_err());
        },
    );
}

#[test]
fn static_constructor_sibling_reference_and_foreign_node_mutations_refuse() {
    with_validation(
        "unitary fn leaf(q:Q<Bit>)->Q<Bit>{q}
         unitary fn apply[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}
         pub unitary fn f(q:Q<Bit>)->Q<Bit>{apply[then_op(leaf,leaf)](q)}
         pub unitary fn g(q:Q<Bit>)->Q<Bit>{apply[leaf](q)}",
        |validation, module| {
            let owner = validation.resolution.qualified("main::f").unwrap();
            let other = validation.resolution.qualified("main::g").unwrap();
            let body = quantum_body(declaration(module, "f"));
            let source = &static_arguments(body)[0];
            let capture = Capture {
                index: &validation.indices[&owner],
                helpers: validation.helpers,
                budget: validation.budget,
            };
            let original = capture.operation(source).unwrap();
            validation.operation(owner, &original).unwrap();
            let mut changed = original.clone();
            let ResolvedStaticKind::Then(a, b) = changed.kind else {
                unreachable!()
            };
            changed.kind = ResolvedStaticKind::Tensor(a, b);
            assert!(validation.operation(owner, &changed).is_err());
            let mut changed = original.clone();
            let ResolvedStaticKind::Then(a, b) = &mut changed.kind else {
                unreachable!()
            };
            std::mem::swap(a, b);
            assert!(validation.operation(owner, &changed).is_err());
            let mut changed = original.clone();
            let ResolvedStaticKind::Then(a, b) = &mut changed.kind else {
                unreachable!()
            };
            let (ResolvedStaticKind::Name(x), ResolvedStaticKind::Name(y)) =
                (&mut a.kind, &mut b.kind)
            else {
                unreachable!()
            };
            std::mem::swap(x, y);
            assert!(validation.operation(owner, &changed).is_err());
            let other_source = &static_arguments(quantum_body(declaration(module, "g")))[0];
            let mut changed = original.clone();
            changed.node = Some(validation.indices[&other].node_id_static_op(other_source));
            assert!(validation.operation(owner, &changed).is_err());
            assert!(
                validation
                    .expression(
                        owner,
                        validation.indices[&other]
                            .node_id_expr(&quantum_body(declaration(module, "g")).result),
                        source.span
                    )
                    .is_err()
            );
            let mut changed = original.clone();
            changed.node = None;
            assert!(validation.operation(owner, &changed).is_err());
            let exhausted = Budget {
                remaining: Cell::new(0),
                limits: SourceLimits::selected(),
            };
            let bounded = Validation {
                indices: validation.indices,
                helpers: validation.helpers,
                interfaces: validation.interfaces,
                resolution: validation.resolution,
                budget: &exhausted,
            };
            assert_eq!(
                bounded.operation(owner, &original).unwrap_err().code,
                "limit"
            );
            assert_eq!(exhausted.remaining.get(), 0);
        },
    );
}

#[test]
fn zero_repeat_keeps_count_kind_and_exact_original_child() {
    with_validation(
        "unitary fn leaf(q:Q<Bit>)->Q<Bit>{q}
         unitary fn apply[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}
         pub unitary fn f(q:Q<Bit>)->Q<Bit>{apply[power(then_op(leaf,leaf),0)](q)}",
        |validation, module| {
            let owner = validation.resolution.qualified("main::f").unwrap();
            let source = &static_arguments(quantum_body(declaration(module, "f")))[0];
            let original = Capture {
                index: &validation.indices[&owner],
                helpers: validation.helpers,
                budget: validation.budget,
            }
            .operation(source)
            .unwrap();
            validation.operation(owner, &original).unwrap();
            let mut changed = original.clone();
            let ResolvedStaticKind::Repeat { power, .. } = &mut changed.kind else {
                unreachable!()
            };
            *power = !*power;
            assert!(validation.operation(owner, &changed).is_err());
            let mut changed = original.clone();
            let ResolvedStaticKind::Repeat { child, .. } = &mut changed.kind else {
                unreachable!()
            };
            let ResolvedStaticKind::Then(a, _) = &child.kind else {
                unreachable!()
            };
            *child = a.clone();
            assert!(validation.operation(owner, &changed).is_err());
        },
    );
}

#[test]
fn basis_type_tags_order_and_reference_sites_are_exact() {
    with_validation(
        "unitary fn identity[const A:Basis](q:Q<A>)->Q<A>{q}
         pub unitary fn f(q:Q<(Unit,Bits<0>)>)->Q<(Unit,Bits<0>)>{identity[type((Unit,Bits<0>))](q)}
         unitary fn g[const A:Basis,const B:Basis](q:Q<(A,B)>)->Q<(A,B)>{identity[type((A,B))](q)}",
        |validation, module| {
            for function in ["f", "g"] {
                let owner = validation
                    .resolution
                    .qualified(&format!("main::{function}"))
                    .unwrap();
                let source = &static_arguments(quantum_body(declaration(module, function)))[0];
                let original = Capture {
                    index: &validation.indices[&owner],
                    helpers: validation.helpers,
                    budget: validation.budget,
                }
                .operation(source)
                .unwrap();
                validation.operation(owner, &original).unwrap();
                let mut changed = original.clone();
                let ResolvedStaticKind::Basis(ty) = &mut changed.kind else {
                    unreachable!()
                };
                let Kind::Tuple(fields) = &mut ty.kind else {
                    unreachable!()
                };
                fields.swap(0, 1);
                assert!(validation.operation(owner, &changed).is_err());
                let mut changed = original.clone();
                changed.type_nodes.swap(1, 2);
                assert!(validation.operation(owner, &changed).is_err());
                let mut changed = original.clone();
                changed.type_nodes.push(changed.type_nodes[0]);
                assert!(validation.operation(owner, &changed).is_err());
                if function == "g" {
                    let mut changed = original.clone();
                    changed.type_references.swap(0, 1);
                    assert!(validation.operation(owner, &changed).is_err());
                }
            }
        },
    );
}

#[test]
fn rectangular_provider_plan_retains_actual_ports_and_effective_access_mask() {
    let program = checked(
        "use std::state::init0;
         pub isometry fn prepare(q:Q<Unit>)->Q<Bit>{finish(q);init0()}
         fn apply[const U:Op<Unit -> Bit>](q:Q<Unit>)->Q<Bit> requires Applicable(U){U(q)}
         pub isometry fn forward(q:Q<Unit>)->Q<Bit>{apply[prepare](q)}",
    );
    let call = call_in(&program, "main::forward", "main::prepare");
    assert!(!call.access[2]);
    assert!(matches!(
        call.parameters[0].quantum_basis().unwrap().kind,
        Kind::Unit
    ));
    assert!(matches!(
        call.result.quantum_basis().unwrap().kind,
        Kind::Bit
    ));
    assert_eq!(call.source_effect, Some(crate::ir::Effect::Isometry));
}

#[test]
fn ordinary_calls_keep_public_effect_boundary_after_complete_inference() {
    let library = crate::frontend::parser::parse_module(
        "
         pub observe fn opaque(q:Q<Bit>)->Q<Bit>{h(q)}
         pub isometry fn widened(q:Q<Bit>)->Q<Bit>{h(q)}
         unitary fn inside(q:Q<Bit>)->Q<Bit>{opaque(q)}
         unitary fn inside_iso(q:Q<Bit>)->Q<Bit>{widened(q)}",
    )
    .unwrap();
    let client = crate::frontend::parser::parse_module(
        "use lib::{opaque,widened};
         pub observe fn external(q:Q<Bit>)->Q<Bit>{opaque(q)}
         pub isometry fn external_iso(q:Q<Bit>)->Q<Bit>{widened(q)}",
    )
    .unwrap();
    let program = super::super::program_with(
        BTreeMap::from([("lib", &library), ("main", &client)]),
        SourceLimits::selected(),
        |_, _, _, _, _, _, _| Ok(()),
    )
    .unwrap()
    .0;
    for (owner, target, effect) in [
        ("lib::inside", "lib::opaque", crate::ir::Effect::Unitary),
        (
            "lib::inside_iso",
            "lib::widened",
            crate::ir::Effect::Unitary,
        ),
        ("main::external", "lib::opaque", crate::ir::Effect::Observe),
        (
            "main::external_iso",
            "lib::widened",
            crate::ir::Effect::Isometry,
        ),
    ] {
        assert_eq!(call_in(&program, owner, target).source_effect, Some(effect));
    }
}

#[test]
fn environment_regions_are_the_exact_ordered_original_ancestry() {
    let source = "unitary fn keep[const m:Nat](q:Q<Bit>)->Q<Bit>{q}
         pub unitary fn f[const n:Nat](q:Q<Bit>)->Q<Bit>{
             let q=if static n>0 {
                 qfor static i in 0..0 carry r=q {
                     yield if static i==0 {keep[0](r)}else{keep[1](r)};
                 }
             }else{keep[2](q)};
             let q=if static n>0 {keep[3](q)}else{q};
             keep[4](q)
         }";
    let program = checked(source);
    with_validation(source, |validation, _| {
        let owner = program.resolution.qualified("main::f").unwrap();
        let target = program.resolution.qualified("main::keep").unwrap();
        let call = |number| {
            program
                .static_calls
                .values()
                .find(|call| {
                    call.owner == owner
                        && call.target == target
                        && matches!(
                            &call.arguments[0].value.kind,
                            ResolvedStaticKind::Natural(ResolvedNatural {
                                kind: ResolvedNaturalKind::Number(value), ..
                            }) if *value == number
                        )
                })
                .unwrap()
        };
        let nested = call(0);
        assert_eq!(nested.environment.regions.len(), 3);
        validation
            .environment(&nested.environment, nested.node, Span::default())
            .unwrap();
        let opposite = call(1);
        assert!(matches!(
            opposite.environment.regions[2],
            StaticRegion::Predicate { truth: false, .. }
        ));
        validation
            .environment(&opposite.environment, opposite.node, Span::default())
            .unwrap();

        let mut changed = (*nested.environment).clone();
        let StaticRegion::Predicate { truth, .. } = &mut changed.regions[2] else {
            unreachable!()
        };
        *truth = !*truth;
        assert!(
            validation
                .environment(&changed, nested.node, Span::default())
                .is_err()
        );

        for omitted in 0..3 {
            let mut changed = (*nested.environment).clone();
            changed.regions.remove(omitted);
            assert!(
                validation
                    .environment(&changed, nested.node, Span::default())
                    .is_err()
            );
        }
        let mut changed = (*nested.environment).clone();
        changed.regions.swap(0, 1);
        assert!(
            validation
                .environment(&changed, nested.node, Span::default())
                .is_err()
        );
        let mut changed = (*nested.environment).clone();
        changed.regions.clear();
        assert!(
            validation
                .environment(&changed, nested.node, Span::default())
                .is_err()
        );
        let mut changed = (*nested.environment).clone();
        changed.regions.push(changed.regions[2].clone());
        assert!(
            validation
                .environment(&changed, nested.node, Span::default())
                .is_err()
        );

        // The sibling guard has the same owner, comparison and operands, but
        // is a different original occurrence and does not enclose this call.
        let sibling = call(3);
        let mut changed = (*nested.environment).clone();
        changed.regions[0] = sibling.environment.regions[0].clone();
        assert!(
            validation
                .environment(&changed, nested.node, Span::default())
                .is_err()
        );
        assert!(
            validation
                .environment(&nested.environment, opposite.node, Span::default())
                .is_err()
        );
        let outside = call(4);
        assert!(outside.environment.regions.is_empty());
        validation
            .environment(&outside.environment, outside.node, Span::default())
            .unwrap();
        assert!(
            validation
                .environment(&nested.environment, outside.node, Span::default())
                .is_err()
        );
    });
}

#[test]
fn fold_ancestry_keeps_original_index_and_bounds_even_with_shared_replacements() {
    let source = "unitary fn keep[const m:Nat](q:Q<Bit>)->Q<Bit>{q}
         pub unitary fn f(q:Q<Bit>)->Q<Bit>{
             qfor static i in 0..0 carry r=q {yield keep[i](r);}
         }";
    let program = checked(source);
    let call = call_in(&program, "main::f", "main::keep");
    with_validation(source, |validation, _| {
        validation
            .environment(&call.environment, call.node, Span::default())
            .unwrap();
        let mut changed = (*call.environment).clone();
        let StaticRegion::Fold { index, start, .. } = &mut changed.regions[0] else {
            unreachable!()
        };
        let mut replacement = (**start).clone();
        replacement.kind = ResolvedNaturalKind::Number(1);
        *start = Arc::new(replacement);
        let NaturalBindingPlan::FoldIndex {
            start: binding_start,
            ..
        } = changed.local_naturals.get_mut(index).unwrap()
        else {
            unreachable!()
        };
        *binding_start = Arc::clone(start);
        assert!(
            validation
                .environment(&changed, call.node, Span::default())
                .is_err()
        );

        let exhausted = Budget {
            remaining: Cell::new(0),
            limits: SourceLimits::selected(),
        };
        let bounded = Validation {
            indices: validation.indices,
            helpers: validation.helpers,
            interfaces: validation.interfaces,
            resolution: validation.resolution,
            budget: &exhausted,
        };
        assert_eq!(
            bounded
                .environment(&call.environment, call.node, Span::default())
                .unwrap_err()
                .code,
            "limit"
        );
    });
}

#[test]
fn dormant_provider_evidence_uses_its_original_region_chain() {
    let source = "unitary fn leaf(q:Q<Bit>)->Q<Bit>{q}
         unitary fn apply[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}
         pub unitary fn f[const n:Nat](q:Q<Bit>)->Q<Bit>{
             if static n>0 {
                 qfor static i in 0..0 carry r=q {yield apply[leaf](r);}
             }else{q}
         }";
    let program = checked(source);
    let owner = program.resolution.qualified("main::f").unwrap();
    let leaf = program.resolution.qualified("main::leaf").unwrap();
    let evidence = program
        .obligations
        .iter()
        .find(|obligation| {
            obligation.definition == owner
                && matches!(obligation.kind,
            ObligationKind::Provider { provider, .. } if provider == leaf)
        })
        .unwrap();
    assert_eq!(evidence.plan.environment.regions.len(), 2);
    with_validation(source, |validation, _| {
        validation
            .environment(
                &evidence.plan.environment,
                evidence.plan.node,
                evidence.span,
            )
            .unwrap();
        let mut changed = (*evidence.plan.environment).clone();
        let StaticRegion::Predicate { truth, .. } = &mut changed.regions[0] else {
            unreachable!()
        };
        *truth = false;
        assert!(
            validation
                .environment(&changed, evidence.plan.node, evidence.span)
                .is_err()
        );
    });
}
