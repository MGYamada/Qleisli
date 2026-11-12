//! Select original body recording before generating any Raw intervals.
//! The plan grants no table evidence or execution authority.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;
use crate::frontend::resolve::locals::OriginalNode;

impl Compiler<'_> {
    pub(in crate::frontend::compile) fn plan_nominal_basis(
        &mut self,
        selected: Option<&BTreeSet<Key>>,
    ) -> Result<(), CompileError> {
        if self.source.nominals.is_empty() {
            return Ok(());
        }
        let mut work = self.work;
        let planned = (|| {
            let mut roots = BTreeSet::new();
            let locals = self.locals();
            for obligation in &self.source.obligations {
                let key = obligation.definition;
                let module = &self.source.resolution.declaration(key).name.0;
                let span = obligation.span;
                self.charge_at(&mut work, module, span, 2)?;
                let check::ObligationKind::Injectivity { typed_ports } = obligation.kind else {
                    continue;
                };
                if selected.is_some_and(|selected| !selected.contains(&key)) || roots.contains(&key)
                {
                    continue;
                }
                let original = locals
                    .original_node_budgeted(obligation.plan.node, |at, cells| {
                        self.charge_at(&mut work, module, at, cells)
                    })?;
                let Some(OriginalNode::Expression(Expr {
                    kind: ExprKind::CoherentLift { basis, .. },
                    ..
                })) = original
                else {
                    return Err(self.error(
                        module,
                        span,
                        ErrorCode::InvalidIr,
                        "basis plan lacks its original lift",
                    ));
                };
                if typed_ports || self.basis_uses_nominal(basis, module, &mut work)? {
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
                if uses.iter().any(|usage| {
                    matches!(usage.target,
                        ResolvedUse::Global(Target::Declaration(callee)) if roots.contains(&callee)
                    )
                }) {
                    roots.insert(*key);
                }
            }
            Ok::<_, CompileError>(roots)
        })();
        self.work = work;
        self.nominal_basis_roots = planned?;
        Ok(())
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
                BasisExprKind::Not(value) => pending.push(value),
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
