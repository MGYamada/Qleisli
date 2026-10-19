//! Closed primitive actions at original dormant Ctrl sites.
//!
//! This checks one original action on its retained common-checked owner types.
//! It neither executes a caller prefix nor certifies the surrounding function.
//! Common source ownership, liveness and frame checking remain mandatory.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.

use super::*;
use crate::frontend::check::plans::{
    BodyStaticKind, BodyStaticOriginal, StaticCategory, original_body_static,
    original_runtime_owners,
};
use crate::frontend::resolve::locals::{BindingKind, OriginalNode, ResolvedUse};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::frontend::compile) enum PrimitiveControlVisit {
    CheckedAction,
    NotCovered,
}

/// No accepted function handle or specialization-cache entry is created here.
/// Preserve charged work and exact work, including on an ordinary gate refusal.
pub(in crate::frontend::compile) fn check_dormant_primitive_control(
    compiler: &mut Compiler<'_>,
    owner: Key,
    original: &Expr,
) -> Result<PrimitiveControlVisit, CompileError> {
    let previous = compiler.checking;
    let result = (|| {
        if !compiler.declarations.contains_key(&owner) {
            // A malformed retained owner must not enter the diagnostic frame:
            // the shared work-limit formatter requires a present declaration.
            // Keep a valid previous frame, or temporarily clear a stale one.
            if compiler
                .checking
                .is_some_and(|key| !compiler.declarations.contains_key(&key))
            {
                compiler.checking = None;
            }
            let module = compiler
                .source
                .resolution
                .try_declaration(owner)
                .map(|declaration| declaration.name.0.as_str())
                .filter(|module| compiler.project.modules.contains_key(*module))
                .or_else(|| compiler.project.modules.keys().next().map(String::as_str))
                .expect("checked source compiler contains an original module");
            let message = "primitive control lacks its original owner declaration";
            let mut work = compiler.work;
            let charged = compiler.charge_at(&mut work, module, original.span, message.len() + 16);
            compiler.work = work;
            charged?;
            return Err(compiler.error(module, original.span, ErrorCode::TypeMismatch, message));
        }
        compiler.checking = Some(owner);
        let module = compiler.dormant_module(owner, original.span)?;
        let frame = if compiler.current_instance_owner() == Some(owner) {
            None
        } else {
            Some(compiler.enter_dormant_owner(owner, &module, original.span)?)
        };
        let result = check_action(compiler, owner, original);
        if let Some(frame) = frame {
            compiler.leave_instance(frame);
        }
        result
    })();
    compiler.checking = previous;
    result
}

fn refuse(
    compiler: &mut Compiler<'_>,
    module: &str,
    span: Span,
    message: &'static str,
) -> Result<CompileError, CompileError> {
    compiler.charge(module, span, message.len() + 1)?;
    Ok(compiler.error(module, span, ErrorCode::TypeMismatch, message))
}

fn check_action(
    compiler: &mut Compiler<'_>,
    owner: Key,
    original: &Expr,
) -> Result<PrimitiveControlVisit, CompileError> {
    // The caller obtains this owner from the common original obligation. Even
    // private malformed-association probes must not index a foreign expression.
    let module = compiler.dormant_module(owner, original.span)?;
    let node = compiler.locals().try_node_id_expr(original);
    let mut work = compiler.work;
    let associated = match node {
        Some(node) if node.definition() == owner => compiler
            .locals()
            .original_node_budgeted(node, |span, cells| {
                compiler.charge_at(&mut work, &module, span, cells)
            }),
        _ => Ok(None),
    };
    compiler.work = work;
    if !matches!(associated?, Some(OriginalNode::Expression(expression))
        if std::ptr::eq(expression, original))
    {
        return Err(refuse(
            compiler,
            &module,
            original.span,
            "primitive control lacks its original expression association",
        )?);
    }
    let ExprKind::AccessCall {
        callee,
        static_args,
        args,
    } = &original.kind
    else {
        return Ok(PrimitiveControlVisit::NotCovered);
    };
    compiler.charge(&module, original.span, args.len().saturating_mul(5) + 12)?;
    if args.is_empty()
        || args.len() > MAX_DEPTH
        || !args.iter().any(|arg| arg.access == QuantumAccess::Ctrl)
        || args.iter().any(|arg| arg.selection.is_some())
    {
        return Ok(PrimitiveControlVisit::NotCovered);
    }
    let locals = compiler.locals();
    let Some(site) = locals.try_reference_site(callee) else {
        return Err(refuse(
            compiler,
            &module,
            callee.span,
            "primitive control lacks its original callee association",
        )?);
    };
    if site.definition() != owner {
        return Err(refuse(
            compiler,
            &module,
            callee.span,
            "primitive control differs from its original resolved target",
        )?);
    }
    let primitive = match locals.usage(callee).target {
        ResolvedUse::Global(Target::Primitive(_)) => true,
        ResolvedUse::Local(id) => {
            compiler.charge(&module, callee.span, 8)?;
            let binder = compiler.source.lexical[&owner].try_binder(id);
            let Some(binder) = binder.filter(|binder| binder.kind == BindingKind::StaticOperation)
            else {
                return Err(refuse(
                    compiler,
                    &module,
                    callee.span,
                    "dormant action callee is not its original Op formal",
                )?);
            };
            compiler.charge(
                &module,
                callee.span,
                binder.key.name.len().saturating_mul(
                    compiler
                        .concrete_context
                        .current
                        .as_ref()
                        .map_or(1, |instance| instance.operations.len() + 1),
                ) + 1,
            )?;
            let binder = compiler.source.lexical[&owner]
                .try_binder(id)
                .expect("checked original Op binder");
            if compiler
                .concrete_context
                .current
                .as_ref()
                .is_none_or(|instance| !instance.operations.contains_key(&binder.key))
            {
                return Ok(PrimitiveControlVisit::NotCovered);
            }
            false
        }
        _ => {
            return Err(refuse(
                compiler,
                &module,
                callee.span,
                "primitive control differs from its original resolved target",
            )?);
        }
    };

    let mut work = compiler.work;
    let captured = (|| {
        let node = node.expect("original expression was associated above");
        compiler.charge_at(
            &mut work,
            &module,
            original.span,
            compiler.source.obligations.len() + 1,
        )?;
        let Some(obligation) = compiler.source.obligations.iter().find(|obligation| {
            obligation.definition == owner
                && obligation.plan.node == node
                && matches!(obligation.kind, check::ObligationKind::ControlSectors)
        }) else {
            let message = "dormant action lacks its canonical original control judgment";
            compiler.charge_at(&mut work, &module, original.span, message.len() + 1)?;
            return Err(compiler.error(&module, original.span, ErrorCode::TypeMismatch, message));
        };
        let retained = original_runtime_owners(
            &compiler.source,
            &compiler.locals(),
            owner,
            compiler.source.resolution.declaration(owner).module,
            original,
            obligation,
            &mut |span, cells| compiler.charge_at(&mut work, &module, span, cells),
            &|span, message| compiler.error(&module, span, ErrorCode::TypeMismatch, message),
        )?;
        compiler.charge_at(
            &mut work,
            &module,
            original.span,
            retained.len().saturating_mul(3) + 1,
        )?;
        let mut owners = Vec::with_capacity(retained.len());
        for retained in retained {
            let key = retained
                .reference
                .local
                .as_ref()
                .expect("original accessor checked runtime key");
            compiler.charge_at(&mut work, &module, original.span, key.name.len() + 1)?;
            owners.push((key.clone(), Arc::clone(&retained.ty)));
        }
        Ok::<_, CompileError>((owners, Arc::clone(&obligation.plan.environment)))
    })();
    compiler.work = work;
    let (owners, environment) = captured?;
    let bindings = compiler.dormant_operation_bindings(&module, original.span)?;
    // A normalized checked Bits size can cancel an intermediate subtraction.
    // Revisit the original interface Nat trees before using their owner types;
    // unrelated unbound roots remain conditional without hiding closed errors.
    let mut work = compiler.work;
    let interface = (|| {
        compiler.charge_at(&mut work, &module, original.span, 1)?;
        let Some(plans) = compiler.interface_naturals.get(&owner) else {
            let message = "dormant owner lacks its original interface natural plans";
            compiler.charge_at(&mut work, &module, original.span, message.len() + 1)?;
            return Err(compiler.error(&module, original.span, ErrorCode::TypeMismatch, message));
        };
        compiler.charge_at(&mut work, &module, original.span, plans.roots.len() + 1)?;
        let mut roots = Vec::with_capacity(plans.roots.len());
        for root in &plans.roots {
            let lookup = compiler.locals();
            let ty = lookup.original_node_budgeted(root.type_node, |at, cells| {
                compiler.charge_at(&mut work, &module, at, cells)
            })?;
            let natural = lookup.original_node_budgeted(root.natural.node, |at, cells| {
                compiler.charge_at(&mut work, &module, at, cells)
            })?;
            if root.owner != owner
                || plans.environment.owner != owner
                || !matches!((ty,natural), (Some(OriginalNode::Type(ty)),Some(OriginalNode::Natural(natural)))
                    if matches!(&ty.kind,TypeKind::Bits(child) if std::ptr::eq(child,natural)))
            {
                let message = "dormant interface natural differs from its original type child";
                compiler.charge_at(&mut work, &module, original.span, message.len() + 1)?;
                return Err(compiler.error(
                    &module,
                    original.span,
                    ErrorCode::TypeMismatch,
                    message,
                ));
            }
            roots.push(Arc::clone(&root.natural));
        }
        Ok::<_, CompileError>((roots, Arc::clone(&plans.environment)))
    })();
    compiler.work = work;
    let (interface_roots, interface_environment) = interface?;
    for root in interface_roots {
        compiler.evaluate_plan_natural_partial(&root, &interface_environment)?;
    }
    let mut complete = true;
    if primitive && !static_args.is_empty() {
        let mut work = compiler.work;
        let captured = (|| {
            let plan = original_body_static(
                &compiler.source,
                &compiler.locals(),
                owner,
                environment.module,
                BodyStaticOriginal::Expression(original),
                &mut |span, cells| compiler.charge_at(&mut work, &module, span, cells),
                &|span, message| compiler.error(&module, span, ErrorCode::TypeMismatch, message),
            )?;
            let BodyStaticKind::PrimitiveCall { arguments, .. } = &plan.kind else {
                let message = "dormant primitive lacks its original static operands";
                compiler.charge_at(&mut work, &module, original.span, message.len() + 1)?;
                return Err(compiler.error(
                    &module,
                    original.span,
                    ErrorCode::TypeMismatch,
                    message,
                ));
            };
            compiler.charge_at(&mut work, &module, original.span, arguments.len() + 1)?;
            Ok::<_, CompileError>((arguments.clone(), Arc::clone(&plan.environment)))
        })();
        compiler.work = work;
        let (arguments, static_environment) = captured?;
        for argument in &arguments {
            complete &= !matches!(
                compiler.evaluate_source_static(
                    argument,
                    &static_environment,
                    StaticCategory::Natural,
                    [false; 3],
                    &bindings,
                    &module
                )?,
                instances::StaticValue::Deferred
            );
        }
    }
    compiler.charge(&module, original.span, owners.len())?;
    let mut closed = Vec::with_capacity(owners.len());
    for (key, source_type) in owners {
        match compiler.close_source_type_partial(&source_type, &environment, original.span)? {
            Some(ty) => closed.push((key, ty)),
            None if compiler.concrete_context.current.is_some()
                && !compiler.in_inactive_region() =>
            {
                let message =
                    "closed dormant Ctrl action requires its exact original runtime owner type";
                compiler.charge(&module, original.span, message.len() + 1)?;
                return Err(compiler.error(
                    &module,
                    original.span,
                    ErrorCode::Unsupported,
                    message,
                ));
            }
            None => complete = false,
        }
    }
    if !complete {
        return Ok(PrimitiveControlVisit::NotCovered);
    }
    compiler.charge(&module, original.span, closed.len() + 1)?;
    let mut lower = Lowerer {
        compiler,
        raw: RawState::new(),
        operation_sources: BTreeMap::new(),
        instrument_calls: Vec::new(),
        tuple_binding_origins: Vec::new(),
        access_updates: vec![BTreeSet::new()],
        effect: Effect::Unitary,
        contract_effect: Effect::Unitary,
        effect_source: None,
        depth: 0,
        bindings,
    };
    let mut env = Env::new();
    let mut quantum = Vec::new();
    let mut classical = Vec::new();
    // The original common judgment supplies types and exact live BinderKeys,
    // including aliases, carry binders and zero-width owners, in CALL order.
    // It grants neither caller-prefix execution nor whole-body acceptance.
    for (key, ty) in closed {
        let mut work = lower.compiler.work;
        let charged = super::super::dormant::charge_port_copy(&ty, 8, &mut |cells| {
            lower
                .compiler
                .charge_at(&mut work, &module, original.span, cells)
        });
        lower.compiler.work = work;
        charged?;
        lower
            .compiler
            .charge(&module, original.span, key.name.len() + 16)?;
        let value = lower.input(&ty, &module, original.span, &mut quantum, &mut classical)?;
        if env.insert(key, Binding::Live(value)).is_some() {
            return Err(refuse(
                lower.compiler,
                &module,
                original.span,
                "primitive control requires distinct original runtime owners",
            )?);
        }
    }
    lower.compiler.charge(
        &module,
        original.span,
        module.len() + callee.text.len() + args.len().saturating_mul(8) + 16,
    )?;
    // The exact original AST reaches exclusive_call -> runtime_call -> the
    // existing native actual-Raw/ordered-owner sector request. AccessCall
    // restores its owners; do not finish an artificial surrounding function.
    lower.expr(&module, original, &mut env)?;
    Ok(PrimitiveControlVisit::CheckedAction)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::project::{ModuleOrigin, SourceModule};

    fn project(primitive: &str, basis: &str) -> Project {
        let source = format!(
            "             unitary fn guard(q:Q<Unit>)->Q<Unit>{{q}}
             unitary fn unused[const U:Op<{basis}>](q:Q<{basis}>)->Q<{basis}>
             requires Applicable(U){{{primitive}(ctrl q);U(q)}}"
        );
        Project {
            edition_context: crate::frontend::project::ProjectEdition::Explicit(
                crate::edition::Edition::E2026,
            ),
            root: PathBuf::from("main.qli"),
            modules: BTreeMap::from([(
                "main".into(),
                SourceModule {
                    name: "main".into(),
                    path: PathBuf::from("main.qli"),
                    ast: crate::frontend::parser::parse_module(&source).unwrap(),
                    source,
                    imports: BTreeMap::new(),
                    origin: ModuleOrigin::Local,
                },
            )]),
        }
    }

    fn expression(project: &Project) -> &Expr {
        let FnBody::Quantum(body) = &project.modules["main"].ast.decls[1].body else {
            panic!("original quantum body")
        };
        let StmtKind::Expr(expression) = &body.statements[0].kind else {
            panic!("original primitive action")
        };
        expression
    }

    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    #[test]
    fn primitive_control_refuses_a_foreign_expression_and_another_original_owner() {
        let project = project("global_phase_eighth", "Unit");
        let mut compiler = super::super::super::snapshot_tests::compiler(&project);
        let owner = compiler
            .source
            .resolution
            .qualified("main::unused")
            .unwrap();
        let guard = compiler.source.resolution.qualified("main::guard").unwrap();
        let original = expression(&project);
        let copied = original.clone();
        compiler.checking = Some(guard);
        for (owner, expression) in [(owner, &copied), (guard, original)] {
            let before = compiler.work;
            let failure =
                check_dormant_primitive_control(&mut compiler, owner, expression).unwrap_err();
            assert_eq!(failure.code, ErrorCode::TypeMismatch);
            assert_eq!(failure.span, original.span);
            assert_eq!(compiler.checking, Some(guard));
            assert!(compiler.work > before);
            assert!(compiler.instances.is_empty());
            assert!(compiler.checked.is_empty());
        }
        assert_eq!(
            check_dormant_primitive_control(&mut compiler, owner, original).unwrap(),
            PrimitiveControlVisit::CheckedAction
        );
        assert_eq!(compiler.checking, Some(guard));
        assert!(compiler.instances.is_empty());
        assert!(compiler.checked.is_empty());
    }

    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    #[test]
    fn primitive_control_success_and_budget_refusals_restore_the_previous_owner() {
        let project = project("global_phase_eighth", "Unit");
        let original = expression(&project);
        let mut limited = false;
        let mut successful = false;
        for allowance in [0, 1, 64, 256, 512, 1024, 2048, 4096] {
            let mut compiler = super::super::super::snapshot_tests::compiler(&project);
            let owner = compiler
                .source
                .resolution
                .qualified("main::unused")
                .unwrap();
            let guard = compiler.source.resolution.qualified("main::guard").unwrap();
            compiler.checking = Some(guard);
            compiler.work = MAX_WORK - allowance;
            let before = compiler.work;
            let exact_before = compiler.exact_work.remaining();
            let result = check_dormant_primitive_control(&mut compiler, owner, original);
            assert_eq!(compiler.checking, Some(guard));
            assert!(compiler.work >= before && compiler.work <= MAX_WORK);
            assert!(compiler.exact_work.remaining() <= exact_before);
            assert!(compiler.instances.is_empty());
            assert!(compiler.checked.is_empty());
            match result {
                Err(failure) => {
                    assert_eq!(failure.code, ErrorCode::Limit, "{failure}");
                    assert!(failure.message.contains("while checking main::unused"));
                    limited = true;
                }
                Ok(PrimitiveControlVisit::CheckedAction) => successful = true,
                Ok(PrimitiveControlVisit::NotCovered) => {
                    panic!("original direct action must be checked or limited")
                }
            }
        }
        assert!(limited && successful);
    }

    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    #[test]
    fn a_removed_original_owner_refuses_before_entering_its_diagnostic_frame() {
        let project = project("global_phase_eighth", "Unit");
        let original = expression(&project);
        for allowance in [0, 1, MAX_WORK] {
            let mut compiler = super::super::super::snapshot_tests::compiler(&project);
            let owner = compiler
                .source
                .resolution
                .qualified("main::unused")
                .unwrap();
            let guard = compiler.source.resolution.qualified("main::guard").unwrap();
            assert!(compiler.declarations.remove(&owner).is_some());
            compiler.checking = Some(guard);
            compiler.work = MAX_WORK - allowance;
            let before = compiler.work;
            let exact_before = compiler.exact_work.remaining();
            let (kernel, decisions) = compiler.kernel.recording();
            compiler.kernel = kernel;
            let failure =
                check_dormant_primitive_control(&mut compiler, owner, original).unwrap_err();
            assert_eq!(compiler.checking, Some(guard));
            assert_eq!(failure.path, PathBuf::from("main.qli"));
            assert!(compiler.work >= before && compiler.work <= MAX_WORK);
            assert_eq!(compiler.exact_work.remaining(), exact_before);
            assert_eq!(decisions.summary().requests_checked(), 0);
            assert!(compiler.instances.is_empty());
            assert!(compiler.checked.is_empty());
            if allowance == MAX_WORK {
                assert_eq!(failure.code, ErrorCode::TypeMismatch);
                assert_eq!(failure.span, original.span);
                assert!(failure.message.contains("original owner declaration"));
                assert!(compiler.work > before);
            } else {
                assert_eq!(failure.code, ErrorCode::Limit);
                assert!(failure.message.contains("while checking main::guard"));
            }
        }
    }

    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    #[test]
    fn primitive_native_refusal_keeps_charged_work_and_restores_the_previous_owner() {
        let project = project("h", "Bit");
        let mut compiler = super::super::super::snapshot_tests::compiler(&project);
        let owner = compiler
            .source
            .resolution
            .qualified("main::unused")
            .unwrap();
        let guard = compiler.source.resolution.qualified("main::guard").unwrap();
        compiler.checking = Some(guard);
        let before = compiler.work;
        let exact_before = compiler.exact_work.remaining();
        let failure = check_dormant_primitive_control(&mut compiler, owner, expression(&project))
            .unwrap_err();
        assert_eq!(failure.code, ErrorCode::Contract);
        assert_eq!(failure.span, expression(&project).span);
        assert_eq!(compiler.checking, Some(guard));
        assert!(compiler.work > before);
        assert!(compiler.exact_work.remaining() <= exact_before);
        assert!(compiler.instances.is_empty());
        assert!(compiler.checked.is_empty());
    }

    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    #[test]
    fn local_alias_and_zero_fold_carry_use_the_original_checked_owner_type() {
        for body in [
            "let renamed=q;h(ctrl renamed);renamed",
            "qfor static i in 0..0 carry renamed=q {h(ctrl renamed);yield renamed;}",
        ] {
            let mut project = project("h", "Bit");
            let source = format!(
                "unitary fn guard(q:Q<Unit>)->Q<Unit>{{q}}\n\
                unitary fn unused(q:Q<Bit>)->Q<Bit>{{{body}}}"
            );
            let module = project.modules.get_mut("main").unwrap();
            module.ast = crate::frontend::parser::parse_module(&source).unwrap();
            module.source = source;
            let mut compiler = super::super::super::snapshot_tests::compiler(&project);
            let owner = compiler
                .source
                .resolution
                .qualified("main::unused")
                .unwrap();
            let guard = compiler.source.resolution.qualified("main::guard").unwrap();
            let obligation = compiler
                .source
                .obligations
                .iter()
                .find(|obligation| matches!(obligation.kind, check::ObligationKind::ControlSectors))
                .unwrap();
            let node = obligation.plan.node;
            let Some(OriginalNode::Expression(original)) = compiler
                .locals()
                .original_node_budgeted(node, |_, _| Ok::<_, CompileError>(()))
                .unwrap()
            else {
                panic!("original control action")
            };
            let (kernel, decisions) = compiler.kernel.recording();
            compiler.kernel = kernel;
            compiler.checking = Some(guard);
            let before = compiler.work;
            let exact_before = compiler.exact_work.remaining();
            let failure =
                check_dormant_primitive_control(&mut compiler, owner, original).unwrap_err();
            assert_eq!(failure.code, ErrorCode::Contract);
            assert_eq!(failure.span, original.span);
            assert_eq!(compiler.checking, Some(guard));
            assert_eq!(compiler.current_instance_owner(), None);
            assert!(compiler.concrete_context.current.is_none());
            assert!(compiler.concrete_context.naturals.is_empty());
            assert!(compiler.work > before);
            assert!(compiler.exact_work.remaining() <= exact_before);
            assert!(failure.message.contains("sector preservation"));
            assert_eq!(
                decisions.summary().requests_checked(),
                0,
                "the refused native sector request is never recorded as successful"
            );
            assert!(compiler.instances.is_empty());
            assert!(compiler.checked.is_empty());
        }
    }
}
