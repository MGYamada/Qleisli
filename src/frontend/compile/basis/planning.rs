//! Select original body recording before generating any Raw intervals.
//! The plan grants no table evidence or execution authority.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;
use crate::frontend::resolve::locals::OriginalNode;

impl Compiler<'_> {
    pub(in crate::frontend::compile) fn plan_original_tables(
        &mut self,
        selected: Option<&BTreeSet<Key>>,
    ) -> Result<(), CompileError> {
        let has_nominals = !self.source.nominals.is_empty();
        let word_predicates = self.word_coordinate_functions(selected)?;
        if !has_nominals
            && word_predicates.is_empty()
            && !self.source.obligations.iter().any(|obligation| {
                matches!(obligation.kind, check::ObligationKind::WorkspaceRestoration)
            })
        {
            return Ok(());
        }
        let mut work = self.work;
        let planned = (|| {
            let mut roots = BTreeSet::new();
            let mut meanings = BTreeSet::new();
            let locals = self.locals();
            for obligation in &self.source.obligations {
                let key = obligation.definition;
                let module = &self.source.resolution.declaration(key).name.0;
                let span = obligation.span;
                self.charge_at(&mut work, module, span, 2)?;
                let requires_plan = match obligation.kind {
                    check::ObligationKind::WorkspaceRestoration => true,
                    check::ObligationKind::Injectivity { .. }
                    | check::ObligationKind::CertifiedClean { .. } => has_nominals,
                    check::ObligationKind::ProtectedClean => {
                        has_nominals || !word_predicates.is_empty()
                    }
                    _ => false,
                };
                if !requires_plan {
                    continue;
                }
                if selected.is_some_and(|selected| !selected.contains(&key)) || roots.contains(&key)
                {
                    continue;
                }
                let original = locals
                    .original_node_budgeted(obligation.plan.node, |at, cells| {
                        self.charge_at(&mut work, module, at, cells)
                    })?;
                let required = match (&obligation.kind, original) {
                    (
                        check::ObligationKind::WorkspaceRestoration,
                        Some(OriginalNode::Expression(Expr {
                            kind: ExprKind::Workspace(_),
                            ..
                        })),
                    ) => true,
                    (
                        check::ObligationKind::Injectivity { typed_ports },
                        Some(OriginalNode::Expression(Expr {
                            kind: ExprKind::CoherentLift { basis, .. },
                            ..
                        })),
                    ) => *typed_ports || self.basis_uses_nominal(basis, module, &mut work)?,
                    (
                        check::ObligationKind::ProtectedClean
                        | check::ObligationKind::CertifiedClean { .. },
                        Some(OriginalNode::Expression(Expr {
                            kind:
                                ExprKind::WithComputed { function, .. }
                                | ExprKind::CertifiedComputed { function, .. },
                            ..
                        })),
                    ) => matches!(locals.usage(function).target,
                        ResolvedUse::Global(Target::Declaration(predicate))
                            if self.deferred_nominal_tables.contains(&predicate)
                                || matches!(obligation.kind, check::ObligationKind::ProtectedClean)
                                   && word_predicates.contains(&predicate)),
                    _ => {
                        return Err(self.error(
                            module,
                            span,
                            ErrorCode::InvalidIr,
                            "coherent table plan lacks its original expression",
                        ));
                    }
                };
                if required {
                    roots.insert(key);
                }
            }
            for key in &self.source.dependency_order {
                if selected.is_some_and(|selected| !selected.contains(key)) {
                    continue;
                }
                let module = &self.source.resolution.declaration(*key).name.0;
                let uses = self.source.lexical[key].resolved_uses();
                self.charge_at(
                    &mut work,
                    module,
                    self.declarations[key].span,
                    uses.len() + 1,
                )?;
                let declaration = self.declarations[key];
                let interface = &self.source.interfaces[key];
                if has_nominals
                    && interface.kind == FnKind::Meaning
                    && (self.has_nominal_port(
                        interface.meaning_input(),
                        module,
                        declaration.span,
                        &mut work,
                    )? || self.has_nominal_port(
                        &interface.result,
                        module,
                        declaration.span,
                        &mut work,
                    )?)
                {
                    meanings.insert(*key);
                }
                let meaning_leaf = matches!(declaration.body, FnBody::Meaning { .. });
                for usage in uses {
                    if let ResolvedUse::Global(Target::Declaration(callee)) = usage.target {
                        if roots.contains(&callee) {
                            roots.insert(*key);
                        }
                        if meanings.contains(&callee)
                            || meaning_leaf && self.deferred_nominal_tables.contains(&callee)
                        {
                            meanings.insert(*key);
                        }
                    }
                }
            }
            Ok::<_, CompileError>((roots, meanings))
        })();
        self.work = work;
        (self.nominal_basis_roots, self.nominal_meaning_roots) = planned?;
        Ok(())
    }

    fn word_coordinate_functions(
        &mut self,
        selected: Option<&BTreeSet<Key>>,
    ) -> Result<BTreeSet<Key>, CompileError> {
        let mut functions = BTreeSet::new();
        let mut work = self.work;
        for key in &self.source.dependency_order {
            let decl = self.declarations[key];
            if selected.is_some_and(|set| !set.contains(key)) || decl.kind != FnKind::Classical {
                continue;
            }
            let module = &self.source.resolution.declaration(*key).name.0;
            let table = &self.source.lexical[key];
            let uses = table.resolved_uses();
            self.charge_at(&mut work, module, decl.span, uses.len() + 1)?;
            if table.reads_word_coordinate() || uses.iter().any(|usage| {
                matches!(usage.target, ResolvedUse::Global(Target::Declaration(callee)) if functions.contains(&callee))
            }) {
                functions.insert(*key);
            }
        }
        self.work = work;
        Ok(functions)
    }

    fn has_nominal_port(
        &self,
        ty: &check::Ty,
        module: &str,
        span: Span,
        work: &mut usize,
    ) -> Result<bool, CompileError> {
        let mut pending = vec![ty];
        while let Some(ty) = pending.pop() {
            self.charge_at(work, module, span, 1)?;
            match &ty.kind {
                Kind::Nominal(_) => return Ok(true),
                Kind::Tuple(fields) => {
                    self.charge_at(work, module, span, fields.len())?;
                    pending.extend(fields);
                }
                _ => (),
            }
        }
        Ok(false)
    }

    fn basis_uses_nominal(
        &self,
        basis: &BasisExpr,
        module: &str,
        work: &mut usize,
    ) -> Result<bool, CompileError> {
        let mut pending = vec![basis];
        let locals = self.locals();
        while let Some(expression) = pending.pop() {
            self.charge_at(work, module, expression.span, 1)?;
            match &expression.kind {
                BasisExprKind::Variant(_)
                | BasisExprKind::Record(_)
                | BasisExprKind::Field { .. }
                | BasisExprKind::Match(_) => return Ok(true),
                BasisExprKind::Call { callee, args } => {
                    if matches!(locals.usage(callee).target,
                        ResolvedUse::Global(Target::Declaration(key)) if self.deferred_nominal_tables.contains(&key)
                    ) {
                        return Ok(true);
                    }
                    self.charge_at(work, module, expression.span, args.len())?;
                    pending.extend(args);
                }
                BasisExprKind::Tuple(fields) => {
                    self.charge_at(work, module, expression.span, fields.len())?;
                    pending.extend(fields);
                }
                BasisExprKind::Not(value)
                | BasisExprKind::BitIndex {
                    receiver: value, ..
                } => pending.push(value),
                BasisExprKind::And(a, b) | BasisExprKind::Xor(a, b) => {
                    pending.push(a);
                    pending.push(b);
                }
                BasisExprKind::Name(_) | BasisExprKind::Unit | BasisExprKind::Bit(_) => {}
            }
        }
        Ok(false)
    }
}
