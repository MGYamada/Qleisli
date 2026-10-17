//! Private full-key/transport controls; these issue no semantic feature claim.
use super::*;
use crate::frontend::project::{ModuleOrigin, SourceModule};

fn project(source: &str) -> Project {
    Project {
        root: PathBuf::from("main.qli"),
        modules: BTreeMap::from([(
            "main".into(),
            SourceModule {
                name: "main".into(),
                path: PathBuf::from("main.qli"),
                source: source.into(),
                ast: crate::frontend::parser::parse_module(source).expect("original source"),
                imports: BTreeMap::new(),
                origin: ModuleOrigin::Local,
            },
        )]),
    }
}

fn same(left: &Identity, right: &Identity) -> bool {
    left.same(right, &mut |_| Ok::<_, CompileError>(()))
        .unwrap()
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn complete_identity_preserves_order_basis_tags_naturals_and_effect() {
    let project = project(
        "unitary fn identity[const A:Basis,const n:Nat](q:Q<A>)->Q<A>{q}\nunitary fn other(q:Q<Unit>)->Q<Unit>{q}",
    );
    let compiler = super::super::snapshot_tests::compiler(&project);
    let key = compiler
        .source
        .resolution
        .qualified("main::identity")
        .unwrap();
    let other = compiler.source.resolution.qualified("main::other").unwrap();
    let identity = |definition, basis, n, source_effect| Identity {
        definition,
        arguments: vec![Argument::Basis(basis), Argument::Natural(n)],
        source_effect,
    };
    let base = identity(key, Ty::unit(), 0, Effect::Unitary);
    assert!(same(&base, &identity(key, Ty::unit(), 0, Effect::Unitary)));
    for changed in [
        identity(other, Ty::unit(), 0, Effect::Unitary),
        identity(key, Ty::empty_bits(), 0, Effect::Unitary),
        identity(key, Ty::unit(), 1, Effect::Unitary),
        identity(key, Ty::unit(), 0, Effect::Isometry),
    ] {
        assert!(!same(&base, &changed));
    }
    assert!(!same(
        &identity(key, Ty::bit(), 0, Effect::Unitary),
        &identity(key, Ty::bits(1), 0, Effect::Unitary)
    ));
    assert!(!same(
        &identity(key, Ty::pair(Ty::unit(), Ty::bit()), 0, Effect::Unitary),
        &identity(key, Ty::pair(Ty::bit(), Ty::unit()), 0, Effect::Unitary)
    ));
    let reversed = Identity {
        definition: key,
        arguments: vec![Argument::Natural(0), Argument::Basis(Ty::unit())],
        source_effect: Effect::Unitary,
    };
    assert!(!same(&base, &reversed));
    assert_eq!(
        base.same(&base, &mut |_| Err(compiler.error(
            "main",
            Span::default(),
            ErrorCode::Limit,
            "comparison exhausted"
        )))
        .err()
        .unwrap()
        .code,
        ErrorCode::Limit
    );
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn unused_basis_actuals_are_bounded_and_full_instances_remain_distinct() {
    let project = project("unitary fn hold[const A:Basis](q:Q<Unit>)->Q<Unit>{q}");
    let mut compiler = super::super::snapshot_tests::compiler(&project);
    let key = compiler.source.resolution.qualified("main::hold").unwrap();
    let span = compiler.declarations[&key].span;
    let formal = compiler.source.interfaces[&key].statics[0].key.clone();
    let mut records = Vec::new();
    for basis in [Ty::unit(), Ty::empty_bits(), Ty::bit(), Ty::bits(1)] {
        let closed = compiler
            .prepare_instance(
                key,
                BTreeMap::from([(formal.clone(), basis)]),
                BTreeMap::new(),
                BTreeMap::new(),
                "main",
                span,
            )
            .unwrap();
        assert_eq!(closed.interface.parameters, [Ty::quantum(Ty::unit())]);
        assert!(records.iter().all(|record| Some(*record) != closed.record));
        records.push(closed.record.unwrap());
    }
    let before = compiler.instances.len();
    let error = compiler
        .prepare_instance(
            key,
            BTreeMap::from([(formal.clone(), Ty::pair(Ty::bits(12), Ty::bit()))]),
            BTreeMap::new(),
            BTreeMap::new(),
            "main",
            span,
        )
        .err()
        .expect("unused actual capacity refusal");
    assert_eq!(error.code, ErrorCode::Limit);
    assert_eq!(compiler.instances.len(), before);
    compiler.work = MAX_WORK;
    let error = compiler
        .prepare_instance(
            key,
            BTreeMap::from([(formal, Ty::unit())]),
            BTreeMap::new(),
            BTreeMap::new(),
            "main",
            span,
        )
        .err()
        .expect("work refusal");
    assert_eq!(error.code, ErrorCode::Limit);
    assert_eq!(compiler.instances.len(), before);
    assert_eq!(compiler.work, MAX_WORK);
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn nested_context_and_fold_index_restore_without_refunding_work() {
    // This is the original zero-qubit fold form retained in the first study.
    let project = project(
        "unitary fn folded[const n:Nat](q:Q<Unit>)->Q<Unit>{qfor static i in 0..n carry r=q{yield r;}}",
    );
    let mut compiler = super::super::snapshot_tests::compiler(&project);
    let key = compiler
        .source
        .resolution
        .qualified("main::folded")
        .unwrap();
    let span = compiler.declarations[&key].span;
    let n = compiler.source.interfaces[&key].statics[0].key.clone();
    let index = compiler
        .source
        .body_statics
        .values()
        .find_map(|plan| match &plan.kind {
            check::plans::BodyStaticKind::Fold { index, .. } => Some(index.clone()),
            _ => None,
        })
        .unwrap();
    let (end, environment) = compiler
        .source
        .body_statics
        .values()
        .find_map(|plan| match &plan.kind {
            check::plans::BodyStaticKind::Fold { end, .. } => {
                Some((Arc::clone(end), Arc::clone(&plan.environment)))
            }
            _ => None,
        })
        .unwrap();
    let outer = compiler
        .prepare_instance(
            key,
            BTreeMap::new(),
            BTreeMap::from([(n.clone(), 2)]),
            BTreeMap::new(),
            "main",
            span,
        )
        .unwrap();
    let inner = compiler
        .prepare_instance(
            key,
            BTreeMap::new(),
            BTreeMap::from([(n.clone(), 0)]),
            BTreeMap::new(),
            "main",
            span,
        )
        .unwrap();
    let before = compiler.work;
    let frame = compiler
        .enter_instance(Arc::clone(&outer), "main", span)
        .unwrap();
    assert!(compiler.instance_is_active(&outer, "main", span).unwrap());
    assert!(!compiler.instance_is_active(&inner, "main", span).unwrap());
    assert_eq!(
        compiler
            .push_natural_binding(&n, 1, span)
            .err()
            .unwrap()
            .code,
        ErrorCode::TypeMismatch
    );
    assert_eq!(compiler.concrete_context.naturals[&n], 2);
    let fold = compiler.push_natural_binding(&index, 1, span).unwrap();
    assert_eq!(
        compiler
            .evaluate_plan_natural_partial(&end, &environment)
            .unwrap(),
        Some(2)
    );
    let inactive = compiler.enter_inactive_region(key, "main", span).unwrap();
    assert_eq!(compiler.concrete_context.naturals[&n], 2);
    assert!(Arc::ptr_eq(
        compiler.concrete_context.current.as_ref().unwrap(),
        &outer
    ));
    assert_eq!(
        compiler
            .evaluate_plan_natural_partial(&end, &environment)
            .unwrap(),
        None
    );
    let nested = compiler.enter_instance(inner, "main", span).unwrap();
    assert_eq!(compiler.concrete_context.naturals[&n], 0);
    assert_eq!(
        compiler
            .evaluate_plan_natural_partial(&end, &environment)
            .unwrap(),
        Some(0)
    );
    assert!(!compiler.concrete_context.naturals.contains_key(&index));
    compiler.leave_instance(nested);
    assert_eq!(
        compiler
            .evaluate_plan_natural_partial(&end, &environment)
            .unwrap(),
        None
    );
    compiler.leave_instance(inactive);
    assert_eq!(
        compiler
            .evaluate_plan_natural_partial(&end, &environment)
            .unwrap(),
        Some(2)
    );
    assert_eq!(compiler.concrete_context.naturals[&index], 1);
    compiler.restore_natural_binding(fold);
    assert!(!compiler.concrete_context.naturals.contains_key(&index));
    let error = compiler
        .enter_instance(outer, "main", span)
        .err()
        .expect("same complete active identity refusal");
    assert_eq!(error.code, ErrorCode::RecursiveCall);
    assert_eq!(compiler.concrete_context.naturals[&n], 2);
    compiler.leave_instance(frame);
    assert!(compiler.concrete_context.owner.is_none());
    assert!(compiler.concrete_context.current.is_none());
    assert!(compiler.concrete_context.naturals.is_empty());
    assert_eq!(compiler.concrete_context.depth, 0);
    assert!(compiler.work > before);
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn closed_provider_reuses_issued_identity_only_for_the_same_fresh_native_body() {
    let project = project("unitary fn identity(q:Q<Unit>)->Q<Unit>{q}");
    let mut compiler = super::super::snapshot_tests::compiler(&project);
    let key = compiler
        .source
        .resolution
        .qualified("main::identity")
        .unwrap();
    let span = compiler.declarations[&key].span;
    let instance = compiler
        .prepare_instance(
            key,
            BTreeMap::new(),
            BTreeMap::new(),
            BTreeMap::new(),
            "main",
            span,
        )
        .unwrap();
    let first = compiler
        .provider_instance(Arc::clone(&instance), None, "main", span)
        .unwrap();
    let (kernel, decisions) = compiler.kernel.recording();
    compiler.kernel = kernel;
    let second = compiler
        .provider_instance(Arc::clone(&instance), None, "main", span)
        .unwrap();
    assert!(
        first
            .same_descriptor_budgeted(&second, &mut |_| Ok::<_, CompileError>(()))
            .unwrap()
    );
    assert!(
        decisions.summary().decisions() > 0,
        "warm reuse still checks the actual native body"
    );
    assert!(
        compiler.instances.is_empty(),
        "nongeneric providers do not consume generic registry slots"
    );
    use crate::ir::*;
    let wrong = compiler
        .kernel
        .accept_raw(RawProgram {
            quantum_inputs: vec![QuantumPort {
                token: TokenId(0),
                wires: vec![],
                shape: BasisShape { bits: 0 },
            }],
            classical_inputs: vec![],
            operations: vec![RawOp::ApplyUnitary {
                input: TokenId(0),
                output: TokenId(1),
                steps: vec![CircuitStep {
                    controls: vec![],
                    action: CircuitAction::Monomial {
                        indices: vec![],
                        permutation: vec![0],
                        phases: vec![1],
                    },
                }],
            }],
            quantum_outputs: vec![TokenId(1)],
            classical_outputs: vec![],
            declared_effect: Effect::Unitary,
        })
        .unwrap();
    // This private corruption control is never accepted as source evidence.
    compiler
        .providers
        .get_mut(&(key, None, Effect::Unitary))
        .unwrap()
        .body = wrong;
    let error = compiler
        .provider_instance(instance, None, "main", span)
        .expect_err("mismatched actual cache body refusal");
    assert_eq!(error.code, ErrorCode::Contract);
    assert!(
        error
            .message
            .contains("different freshly checked Raw/source graph")
    );
}
