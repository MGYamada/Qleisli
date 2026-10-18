//! Independently check closed declaration callees at original dormant Ctrl sites.
//! Conditional Ops and unsupported expression subjects acquire no evidence here.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.

use super::*;
use crate::contract::BasisType;
use crate::frontend::resolve::locals::{BindingKind, NodeId};
use crate::ir::Effect;

type ClosedControlInterface = (Vec<BasisType>, Vec<usize>);

impl<'a> Compiler<'a> {
    pub(in crate::frontend::compile) fn check_dormant_controls(
        &mut self,
    ) -> Result<(), CompileError> {
        let previous = self.checking;
        let result = self.check_dormant_controls_inner(None);
        self.checking = previous;
        result
    }

    pub(super) fn check_dormant_controls_inner(
        &mut self,
        owner_filter: Option<Key>,
    ) -> Result<(), CompileError> {
        let Some((&first, declaration)) = self.declarations.first_key_value() else {
            return Ok(());
        };
        let root_span = declaration.span;
        let root_module = self.dormant_module(first, root_span)?;
        for ordinal in 0..self.source.obligations.len() {
            self.charge(&root_module, root_span, 4)?;
            let obligation = &self.source.obligations[ordinal];
            if !matches!(obligation.kind, check::ObligationKind::ControlSectors)
                || owner_filter.is_some_and(|owner| owner != obligation.definition)
            {
                continue;
            }
            let (owner, node, span) =
                (obligation.definition, obligation.plan.node, obligation.span);
            let module = self.dormant_module(owner, span)?;
            self.charge(&module, span, 1)?;
            let environment = Arc::clone(&self.source.obligations[ordinal].plan.environment);
            self.visit_dormant_environment(&environment, &module, span, |compiler, inactive| {
                compiler.check_dormant_control_site(ordinal, owner, node, span, &module, inactive)
            })?;
        }
        Ok(())
    }

    fn check_dormant_control_site(
        &mut self,
        ordinal: usize,
        owner: Key,
        node: NodeId,
        span: Span,
        module: &str,
        inactive: bool,
    ) -> Result<(), CompileError> {
        let expression = self.original_control_expression(owner, node, module, span)?;
        self.charge(module, span, 5)?;
        let obligation = &self.source.obligations[ordinal];
        if !matches!(obligation.plan.subject, EvidenceSubject::Expression)
            || obligation.plan.environment.owner != owner
            || obligation.plan.environment.module
                != self.source.resolution.declaration(owner).module
        {
            return Err(self.dormant_error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "control obligation differs from its original owner or environment",
            )?);
        }
        let environment = Arc::clone(&obligation.plan.environment);
        let ExprKind::AccessCall { callee, args, .. } = &expression.kind else {
            return Err(self.dormant_error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "control obligation lacks its original access call",
            )?);
        };
        self.charge(module, span, args.len().saturating_mul(3) + 10)?;
        if args.is_empty()
            || args.len() > 64
            || !args
                .iter()
                .any(|argument| argument.access == QuantumAccess::Ctrl)
        {
            return Err(self.dormant_error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "control obligation lacks its original ordered Ctrl arguments",
            )?);
        }
        // Indexed places belong to their existing separate profile gate.
        // This pass neither materializes nor discharges that obligation.
        if args.iter().any(|argument| argument.selection.is_some()) {
            return Ok(());
        }
        let Some(callee_site) = self.locals().try_reference_site(callee) else {
            return Err(self.dormant_error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "control callee lacks its original reference association",
            )?);
        };
        if callee_site.definition() != owner {
            return Err(self.dormant_error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "control callee belongs to another original owner",
            )?);
        }
        let target = self.locals().usage(callee).target;
        match target {
            ResolvedUse::Local(_) => {
                // No dummy actual stands in for an unbound original Op.
                if !self.unbound_operation(module, callee, &environment)? {
                    lower::check_dormant_primitive_control(self, owner, expression)?;
                }
                return Ok(());
            }
            ResolvedUse::Global(Target::Primitive(_)) => {
                // Primitive calls have no StaticCallPlan. Reuse retained
                // original owner types and the ordinary action/native gate.
                match lower::check_dormant_primitive_control(self, owner, expression)? {
                    lower::PrimitiveControlVisit::CheckedAction => {}
                    lower::PrimitiveControlVisit::NotCovered => {}
                }
                return Ok(());
            }
            ResolvedUse::Global(Target::Declaration(_)) => {}
            ResolvedUse::Unresolved => {
                return Err(self.dormant_error(
                    module,
                    span,
                    ErrorCode::TypeMismatch,
                    "control callee is unresolved in its original collection",
                )?);
            }
        }
        let (site, _target) = self.original_control_call(owner, module, expression)?;
        if site != callee_site {
            return Err(self.dormant_error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "control call has a different original reference site",
            )?);
        }
        let Some(instance) = self.closed_call_instance(site, module, span)? else {
            // Closed siblings have still reached all ordinary actual gates.
            return Ok(());
        };
        let Some((signatures, axes)) =
            self.closed_control_interface(site, args, &instance, module, span)?
        else {
            return Ok(());
        };
        if inactive && self.instance_is_active(&instance, module, span)? {
            return Ok(());
        }
        let actual = self.materialize_instance(instance, module, span)?;
        // Fresh native reconstruction uses the actual ordered Raw ports and
        // complete body. No producer matrix or earlier decision replaces it.
        if let Err(failure) =
            self.kernel
                .check_control_owners(actual.raw(), &signatures, &axes, &mut self.exact_work)
        {
            self.charge(
                module,
                span,
                failure.code.len()
                    + failure.message.len()
                    + failure.json_pointer.len()
                    + crate::frontend::diagnostic::CONTROL_ACCESS_EXPLANATION.len()
                    + 16,
            )?;
            let code = match failure.code {
                "contract" => ErrorCode::Contract,
                "limit" => ErrorCode::Limit,
                "io" | "kernel" => ErrorCode::Project,
                _ => ErrorCode::InvalidIr,
            };
            return Err(self.error(
                module,
                span,
                code,
                format!(
                    "{failure}; {}",
                    crate::frontend::diagnostic::CONTROL_ACCESS_EXPLANATION
                ),
            ));
        }
        Ok(())
    }

    fn original_control_expression(
        &mut self,
        owner: Key,
        node: NodeId,
        module: &str,
        span: Span,
    ) -> Result<&'a Expr, CompileError> {
        let mut work = self.work;
        let original = if node.definition() == owner {
            self.locals().original_node_budgeted(node, |at, cells| {
                self.charge_at(&mut work, module, at, cells)
            })
        } else {
            Ok(None)
        };
        self.work = work;
        match original? {
            Some(OriginalNode::Expression(expression)) if expression.span == span => Ok(expression),
            _ => Err(self.dormant_error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "control obligation lacks its original expression association",
            )?),
        }
    }

    fn original_control_call(
        &mut self,
        owner: Key,
        module: &str,
        expression: &Expr,
    ) -> Result<(UseSiteId, Key), CompileError> {
        let ExprKind::AccessCall {
            callee,
            static_args,
            args,
        } = &expression.kind
        else {
            unreachable!("original access call checked before declaration selection")
        };
        let mut work = self.work;
        let result = (|| {
            let checked = calls::CheckedCall::original(
                &self.source,
                &self.locals(),
                calls::OriginalCall {
                    owner,
                    module: self.source.resolution.declaration(owner).module,
                    expression,
                    callee,
                    static_arguments: static_args,
                    runtime_arguments: RuntimeArguments::Accesses(args),
                },
                &mut |at, cells| self.charge_at(&mut work, module, at, cells),
                &|at, code, message| self.error(module, at, code, message),
            )?;
            let plan = checked.plan();
            self.charge_at(&mut work, module, expression.span, 1)?;
            if plan.source_effect != Some(Effect::Unitary) {
                let message = "control access requires an available Unitary source effect";
                self.charge_at(&mut work, module, expression.span, message.len() + 1)?;
                return Err(self.error(module, expression.span, ErrorCode::Effect, message));
            }
            self.charge_at(&mut work, module, expression.span, args.len() + 1)?;
            let mut owners = Vec::with_capacity(args.len());
            for argument in args {
                let ExprKind::Name(name) = &argument.value.kind else {
                    let message = "dormant control requires whole original lexical Q owners";
                    self.charge_at(&mut work, module, argument.value.span, message.len() + 1)?;
                    return Err(self.error(
                        module,
                        argument.value.span,
                        ErrorCode::Unsupported,
                        message,
                    ));
                };
                self.charge_at(&mut work, module, name.span, 12 + owners.len())?;
                let original = self.locals();
                let id = original.try_reference_site(name).and_then(|site| {
                    match original.usage(name).target {
                        ResolvedUse::Local(id)
                            if site.definition() == owner
                                && id.definition() == owner
                                && original.info(id).kind == BindingKind::Runtime =>
                        {
                            Some(id)
                        }
                        _ => None,
                    }
                });
                let Some(id) = id.filter(|id| !owners.contains(id)) else {
                    let message =
                        "control argument differs from its distinct original runtime owner";
                    self.charge_at(&mut work, module, name.span, message.len() + 1)?;
                    return Err(self.error(module, name.span, ErrorCode::Ownership, message));
                };
                owners.push(id);
            }
            Ok((plan.callee.site, plan.target))
        })();
        self.work = work;
        result
    }

    fn closed_control_interface(
        &mut self,
        site: UseSiteId,
        args: &[AccessArgument],
        instance: &instances::ClosedInstance,
        module: &str,
        span: Span,
    ) -> Result<Option<ClosedControlInterface>, CompileError> {
        self.tick(module, span)?;
        let mut work = self.work;
        let source = (|| {
            let plan = &self.source.static_calls[&site];
            self.charge_at(&mut work, module, span, plan.parameters.len() + 2)?;
            for ty in &plan.parameters {
                charge_source_type_copy(ty, &mut |cells| {
                    self.charge_at(&mut work, module, span, cells)
                })?;
            }
            charge_source_type_copy(&plan.result, &mut |cells| {
                self.charge_at(&mut work, module, span, cells)
            })?;
            Ok::<_, CompileError>((
                plan.parameters.clone(),
                plan.result.clone(),
                Arc::clone(&plan.environment),
            ))
        })();
        self.work = work;
        let (source_parameters, source_result, environment) = source?;
        // These source ports contain the original CALLER substitution. Closing
        // the target's formal keys here would confuse distinct lexical owners.
        self.charge(module, span, source_parameters.len())?;
        let mut parameters = Vec::with_capacity(source_parameters.len());
        let mut complete = true;
        for ty in &source_parameters {
            match self.close_source_type_partial(ty, &environment, span)? {
                Some(ty) => parameters.push(ty),
                None => complete = false,
            }
        }
        let result = self.close_source_type_partial(&source_result, &environment, span)?;
        let Some(result) = result.filter(|_| complete) else {
            return Ok(None);
        };
        let mut work = self.work;
        let same = (|| {
            let mut charge = |cells| self.charge_at(&mut work, module, span, cells);
            charge(parameters.len() + 1)?;
            if parameters.len() != instance.interface.parameters.len() {
                return Ok(false);
            }
            let mut same = true;
            for (parameter, actual) in parameters.iter().zip(&instance.interface.parameters) {
                same &= operations::same_port_budgeted(parameter, actual, &mut charge)?;
            }
            same &=
                operations::same_port_budgeted(&result, &instance.interface.result, &mut charge)?;
            Ok::<_, CompileError>(same)
        })();
        self.work = work;
        if !same? {
            return Err(self.dormant_error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "control call differs from its original closed interface",
            )?);
        }
        let outputs = if parameters.len() == 1 {
            std::slice::from_ref(&result)
        } else {
            result.tuple_fields().unwrap_or(&[])
        };
        self.charge(module, span, parameters.len() + 1)?;
        if parameters.len() != args.len() || outputs.len() != parameters.len() {
            return Err(self.dormant_error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "control call must return the same ordered owner forest",
            )?);
        }
        let mut work = self.work;
        let same = (|| {
            for (parameter, output) in parameters.iter().zip(outputs) {
                if parameter.quantum_basis().is_none()
                    || !operations::same_port_budgeted(parameter, output, &mut |cells| {
                        self.charge_at(&mut work, module, span, cells)
                    })?
                {
                    return Ok(false);
                }
            }
            Ok::<_, CompileError>(true)
        })();
        self.work = work;
        if !same? {
            return Err(self.dormant_error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "control call must preserve each exact Q owner type in order",
            )?);
        }
        self.charge(module, span, 2 * (parameters.len() + 1))?;
        let mut signatures = Vec::with_capacity(parameters.len());
        let mut widths = Vec::with_capacity(parameters.len());
        let mut requested = 0;
        for (parameter, argument) in parameters.iter().zip(args) {
            let basis = parameter
                .quantum_basis()
                .expect("exact Q owner checked above");
            let mut work = self.work;
            // Reserve the width traversal, copied Basis cells/slots and the
            // BasisType destructor's temporary traversal storage as well.
            let charged = charge_port_copy(basis, 4, &mut |cells| {
                self.charge_at(&mut work, module, span, cells)
            });
            self.work = work;
            charged?;
            let width = basis.basis_bits().expect("closed finite basis");
            widths.push(width);
            // A zero-width owner still contributes its complete signature.
            signatures.push(operations::contract_basis(basis));
            if argument.access == QuantumAccess::Ctrl {
                requested += width;
            }
        }
        self.charge(module, span, requested + widths.len() + 1)?;
        let mut axes = Vec::with_capacity(requested);
        let mut offset = 0;
        for (width, argument) in widths.into_iter().zip(args) {
            if argument.access == QuantumAccess::Ctrl {
                axes.extend(offset..offset + width);
            }
            offset += width;
        }
        Ok(Some((signatures, axes)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::project::{ModuleOrigin, SourceModule};

    fn project() -> Project {
        let source = "unitary fn guard(q:Q<Unit>)->Q<Unit>{q}
            unitary fn identity(q:Q<Unit>)->Q<Unit>{q}
            unitary fn unused[const U:Op<Unit>](q:Q<Unit>)->Q<Unit>
            requires Applicable(U){identity(ctrl q);U(q)}";
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
                    source: source.into(),
                    ast: crate::frontend::parser::parse_module(source).unwrap(),
                    imports: BTreeMap::new(),
                    origin: ModuleOrigin::Local,
                },
            )]),
        }
    }

    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    #[test]
    fn original_control_borrow_refuses_another_owner_and_another_expression() {
        let project = project();
        let mut compiler = super::super::super::snapshot_tests::compiler(&project);
        let guard = compiler.source.resolution.qualified("main::guard").unwrap();
        let obligation = compiler
            .source
            .obligations
            .iter()
            .find(|obligation| matches!(obligation.kind, check::ObligationKind::ControlSectors))
            .unwrap();
        let (owner, node, span) = (obligation.definition, obligation.plan.node, obligation.span);
        assert!(
            compiler
                .original_control_expression(owner, node, "main", span)
                .is_ok()
        );
        assert_eq!(
            compiler
                .original_control_expression(guard, node, "main", span)
                .unwrap_err()
                .code,
            ErrorCode::TypeMismatch
        );
        let FnBody::Quantum(body) = &project.modules["main"].ast.decls[2].body else {
            panic!("original quantum body")
        };
        let other = compiler.locals().try_node_id_expr(&body.result).unwrap();
        assert_eq!(
            compiler
                .original_control_expression(owner, other, "main", span)
                .unwrap_err()
                .code,
            ErrorCode::TypeMismatch
        );
        assert!(compiler.instances.is_empty());
        assert!(compiler.checked.is_empty());
    }

    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    #[test]
    fn a_control_revisit_requires_a_fresh_native_request_with_empty_axes() {
        let project = project();
        let mut compiler = super::super::super::snapshot_tests::compiler(&project);
        let (kernel, decisions) = compiler.kernel.recording();
        compiler.kernel = kernel;
        compiler.check_dormant_controls().unwrap();
        let before = decisions.summary().requests_checked();
        assert!(
            before > 0,
            "zero width retains an actual native control request"
        );
        compiler.check_dormant_controls().unwrap();
        assert!(decisions.summary().requests_checked() > before);
        assert!(compiler.instances.is_empty());
        assert!(compiler.checked.is_empty());
    }

    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    #[test]
    fn budget_failure_after_entering_the_callee_restores_the_previous_owner() {
        let project = project();
        let mut failed_in_callee = false;
        for allowance in (16..=2048).step_by(16) {
            let mut compiler = super::super::super::snapshot_tests::compiler(&project);
            let guard = compiler.source.resolution.qualified("main::guard").unwrap();
            compiler.checking = Some(guard);
            compiler.work = MAX_WORK - allowance;
            let before = compiler.work;
            let result = compiler.check_dormant_controls();
            assert_eq!(compiler.checking, Some(guard));
            assert!(compiler.work >= before && compiler.work <= MAX_WORK);
            assert!(compiler.instances.is_empty());
            assert!(compiler.checked.is_empty());
            if let Err(error) = result {
                if error.code == ErrorCode::Limit
                    && error.message.contains("while checking main::identity")
                {
                    failed_in_callee = true;
                    assert!(compiler.work > before);
                    break;
                }
            }
        }
        assert!(
            failed_in_callee,
            "exercise restoration after entering the real callee body"
        );
    }
}
