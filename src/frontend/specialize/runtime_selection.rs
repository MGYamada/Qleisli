//! Choose the shared emitter from original AST occurrences, never diagnostics.
//! This metadata grants no execution, native acceptance or operation access.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use crate::frontend::{
    ast::ExprKind,
    check::{Budget, SourceError},
    resolve::{
        DefId, Target,
        locals::{Index, OriginalNode, ResolvedUse},
    },
};
use std::collections::{BTreeMap, BTreeSet};

pub(super) fn roots(
    dependency_order: &[DefId],
    indices: &BTreeMap<DefId, Index<'_>>,
    budget: &Budget,
) -> Result<BTreeSet<DefId>, SourceError> {
    let mut roots = BTreeSet::new();
    // The common judgment supplies a dependency-first acyclic order. Borrow
    // its original occurrence table while it still owns the same AST indices.
    for id in dependency_order {
        let index = &indices[id];
        let nodes = index.original_nodes();
        let uses = index.table.resolved_uses();
        budget.charge(Default::default(), nodes.len() + uses.len() + 2)?;
        let direct = nodes.iter().any(|node| {
            matches!(node,
            OriginalNode::Expression(expr) if matches!(expr.kind, ExprKind::QuantumMatch(_)))
        });
        let dependency = uses.iter().any(|usage| {
            matches!(usage.target,
            ResolvedUse::Global(Target::Declaration(callee)) if roots.contains(&callee))
        });
        if direct || dependency {
            roots.insert(*id);
        }
    }
    Ok(roots)
}
