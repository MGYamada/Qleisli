//! Complete original-source judgments, before concrete adapter eligibility.
//!
//! These are untrusted frontend facts. They authorize neither native acceptance
//! nor source preservation, exact cleanup, provider correspondence or a guarantee.
// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.

mod body;
mod declarations;
mod normalize;
pub(super) mod primitive;
mod static_helpers;

use super::ast::{self, FnKind, Span};
use super::effects::{BodyEffects, FunctionEffect};
pub(super) use super::linear::{Context, Linear};
use super::resolve::locals::{BinderKey, Index, Table};
use super::resolve::{self, DefId, Resolution};
use super::types::{Kind, Type};
use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;
use std::sync::Arc;

pub(super) type Ty = Type<Linear>;
pub(super) type StaticHelpers = Rc<BTreeMap<DefId, Arc<StaticHelper>>>;
#[derive(Debug)]
pub(super) struct StaticHelper {
    pub parameters: Vec<BinderKey>,
    pub result: Linear,
    pub requirements: Vec<(Linear, ast::Compare, Linear)>,
}
pub(super) type Result<T> = std::result::Result<T, SourceError>;

fn runtime_quantum_group(ty: &Ty, span: Span, budget: &Budget) -> Result<bool> {
    budget.charge(span, 1)?;
    let mut pending = vec![ty];
    while let Some(node) = pending.pop() {
        budget.charge(span, 1)?;
        match &node.kind {
            Kind::Q(_) => {}
            Kind::Tuple(fields) if !fields.is_empty() => {
                budget.charge(span, fields.len())?;
                pending.extend(fields);
            }
            _ => return Ok(false),
        }
    }
    Ok(true)
}

/// Borrowed bounded preflight: Q is transparent in retained storage, while
/// its actual visit and stack entry are charged before traversal.
pub(super) fn type_size_budgeted<N>(
    ty: &Type<N>,
    nodes: usize,
    depth: usize,
    basis_only: bool,
    span: Span,
    charge: &mut impl FnMut(Span, usize) -> Result<()>,
) -> Result<super::types::TreeSize> {
    charge(span, 1)?;
    let mut pending = vec![(ty, 1usize)];
    let mut size = super::types::TreeSize::default();
    while let Some((node, level)) = pending.pop() {
        charge(span, 1)?;
        if level > depth {
            return Err(SourceError::new(
                "limit",
                span,
                "type exceeds depth capacity",
            ));
        }
        if let Kind::Q(child) = &node.kind {
            if basis_only {
                return Err(SourceError::new(
                    "type",
                    span,
                    "a Basis binding cannot contain quantum ownership",
                ));
            }
            charge(span, 1)?;
            pending.push((child, level));
            continue;
        }
        size.nodes = size
            .nodes
            .checked_add(1)
            .ok_or_else(|| SourceError::new("limit", span, "type cell count overflow"))?;
        size.depth = size.depth.max(level);
        if size.nodes > nodes {
            return Err(SourceError::new(
                "limit",
                span,
                "type exceeds storage capacity",
            ));
        }
        if let Kind::Tuple(fields) = &node.kind {
            if fields.len() > 64 {
                return Err(SourceError::new(
                    "limit",
                    span,
                    "type tuple exceeds 64 fields",
                ));
            }
            charge(span, fields.len())?;
            pending.extend(fields.iter().rev().map(|field| (field, level + 1)));
        }
    }
    Ok(size)
}

#[derive(Clone, Debug)]
pub(super) struct SourceError {
    pub code: &'static str,
    pub module: Option<String>,
    pub span: Span,
    pub message: String,
    // Diagnostic provenance only; outer primitive calls must not move an
    // already located inner argument failure to their own call span.
    pub(super) primitive_argument_located: bool,
}
impl SourceError {
    pub fn new(code: &'static str, span: Span, message: impl Into<String>) -> Self {
        Self {
            code,
            module: None,
            span,
            message: message.into(),
            primitive_argument_located: false,
        }
    }
    pub fn in_module(mut self, module: &str) -> Self {
        if self.module.is_none() {
            self.module = Some(module.into());
        }
        self
    }
}
impl From<super::error::Error> for SourceError {
    fn from(error: super::error::Error) -> Self {
        let code = match error.code() {
            "limit" => "limit",
            "size" => "size",
            "type" => "type",
            "name" => "name",
            "static" => "static",
            "access" => "access",
            "ownership" => "ownership",
            "effect" => "effect",
            "cycle" => "cycle",
            "contract" => "contract",
            "unsupported" => "unsupported",
            "module" => "module",
            "visibility" => "visibility",
            "arity" => "arity",
            _ => "source",
        };
        Self {
            code,
            module: error.module().map(str::to_owned),
            span: error.span(),
            message: error.message().into(),
            primitive_argument_located: false,
        }
    }
}

/// Capacity options select limits, never another source semantics.
#[derive(Clone, Copy, Debug)]
pub(super) struct SourceLimits {
    pub work: usize,
    pub retained_scope_cells: Option<usize>,
}
impl SourceLimits {
    pub fn finite() -> Self {
        Self {
            work: 1_000_000,
            retained_scope_cells: None,
        }
    }
    pub fn selected() -> Self {
        Self {
            work: 1_000_000,
            retained_scope_cells: Some(16_384),
        }
    }
}

pub(in crate::frontend) struct Budget {
    remaining: Cell<usize>,
    limits: SourceLimits,
}
impl Budget {
    pub fn charge(&self, span: Span, cells: usize) -> Result<()> {
        let remaining = self.remaining.get().checked_sub(cells).ok_or_else(|| {
            SourceError::new(
                "limit",
                span,
                "common source judgment exceeds its 1000000 work capacity",
            )
        })?;
        self.remaining.set(remaining);
        Ok(())
    }
    pub fn preparation_charge(&self, span: Span, cells: usize) -> super::error::Result<()> {
        self.charge(span, cells)
            .map_err(|e| super::error::Error::new(e.code, e.span, e.message))
    }
    fn ty(&self, span: Span, ty: &Ty) -> Result<usize> {
        self.charge(span, 1)?;
        let mut pending = vec![(ty, 1usize)];
        let mut cells = 0usize;
        while let Some((node, depth)) = pending.pop() {
            self.charge(span, 1)?;
            if depth > 64 {
                return Err(SourceError::new("limit", span, "type exceeds depth 64"));
            }
            if !matches!(node.kind, Kind::Q(_)) {
                cells = cells
                    .checked_add(1)
                    .ok_or_else(|| SourceError::new("limit", span, "type cell count overflow"))?;
            }
            if cells > 4096 {
                return Err(SourceError::new("limit", span, "type exceeds 4096 cells"));
            }
            match &node.kind {
                Kind::Bits(size) => self.charge(span, size.storage_cells()?)?,
                Kind::Parameter(parameter) => self.charge(
                    span,
                    parameter.name.len()
                        + parameter.key.as_ref().map_or(0, |key| key.name.len())
                        + 1,
                )?,
                Kind::Q(child) => {
                    self.charge(span, 1)?;
                    pending.push((child, depth));
                }
                Kind::Tuple(fields) => {
                    if fields.len() > 64 {
                        return Err(SourceError::new(
                            "limit",
                            span,
                            "type tuple exceeds 64 fields",
                        ));
                    }
                    self.charge(span, fields.len())?;
                    pending.extend(fields.iter().rev().map(|field| (field, depth + 1)));
                }
                _ => {}
            }
        }
        Ok(cells)
    }
    fn copy_ty(&self, span: Span, ty: &Ty) -> Result<Ty> {
        self.ty(span, ty)?;
        Ok(ty.clone())
    }
    fn key(&self, span: Span, key: &BinderKey) -> Result<BinderKey> {
        self.charge(span, key.name.len() + 1)?;
        Ok(key.clone())
    }
    fn values(
        &self,
        span: Span,
        values: &BTreeMap<BinderKey, Binding>,
    ) -> Result<BTreeMap<BinderKey, Binding>> {
        let mut copied = BTreeMap::new();
        for (key, value) in values {
            let key = self.key(span, key)?;
            let ty = self.copy_ty(span, &value.ty)?;
            self.charge(span, 1)?;
            copied.insert(
                key,
                Binding {
                    identity: value.identity,
                    ty,
                },
            );
        }
        Ok(copied)
    }
    fn copy_context(&self, span: Span, context: &Context) -> Result<Context> {
        Ok(context.copy_budgeted(span, &mut |span, cells| {
            self.preparation_charge(span, cells)
        })?)
    }
}

#[derive(Clone, Debug)]
pub(super) enum StaticKind {
    Natural,
    Basis,
    Operation {
        basis: Ty,
        codomain: Option<Ty>,
        meaning: Option<DefId>,
        access: [bool; 3],
    },
}
#[derive(Clone, Debug)]
pub(super) struct StaticFormal {
    pub key: BinderKey,
    pub kind: StaticKind,
}
#[derive(Clone, Debug)]
pub(super) struct Interface {
    pub module: String,
    pub ast_index: usize,
    pub kind: FnKind,
    pub statics: Vec<StaticFormal>,
    pub params: Vec<Ty>,
    pub result: Ty,
    pub premises: Context,
}

#[derive(Clone, Debug)]
pub(super) enum ObligationKind {
    ControlSectors,
    Injectivity,
    ProtectedClean,
    CertifiedClean {
        logical: OperationIdentity,
    },
    Provider {
        provider: DefId,
        ceiling: crate::ir::Effect,
        meaning: Option<DefId>,
    },
    RuntimeGroupProvider {
        provider: DefId,
    },
    MeaningEquality {
        required: DefId,
        supplied: Option<DefId>,
    },
    FunctionEquality {
        implementation: DefId,
        specification: DefId,
    },
    TransformedMeaning,
}
#[derive(Clone, Debug)]
pub(super) enum OperationIdentity {
    Global(resolve::Target),
    Formal(BinderKey),
}
#[derive(Clone, Debug)]
pub(super) struct Obligation {
    pub definition: DefId,
    pub span: Span,
    pub kind: ObligationKind,
}

/// Immutable identities and checked facts from one current original collection.
#[derive(Debug)]
pub(super) struct CheckedProgram {
    pub resolution: Resolution,
    pub interfaces: BTreeMap<DefId, Interface>,
    pub effects: BTreeMap<DefId, FunctionEffect>,
    pub lexical: BTreeMap<DefId, Arc<Table>>,
    pub obligations: Vec<Obligation>,
    pub dependency_order: Vec<DefId>,
}
impl CheckedProgram {
    pub fn interface(&self, id: DefId) -> &Interface {
        &self.interfaces[&id]
    }
}

#[derive(Clone)]
struct Operation {
    basis: Ty,
    codomain: Option<Ty>,
    effect: crate::ir::Effect,
    meaning: Option<DefId>,
    access: [bool; 3],
}
impl Operation {
    fn output(&self) -> &Ty {
        self.codomain.as_ref().unwrap_or(&self.basis)
    }
}
#[derive(Clone, Copy)]
struct OperationMode {
    arrows: bool,
    ceiling: crate::ir::Effect,
}
impl OperationMode {
    const ENDO: Self = Self {
        arrows: false,
        ceiling: crate::ir::Effect::Unitary,
    };
    fn unitary(self) -> Self {
        Self {
            ceiling: crate::ir::Effect::Unitary,
            ..self
        }
    }
}
fn formal_effect(codomain: &Option<Ty>, access: &[bool; 3]) -> crate::ir::Effect {
    if codomain.is_some() && !access[1] && !access[2] {
        crate::ir::Effect::Iso
    } else {
        crate::ir::Effect::Unitary
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
struct Binding {
    identity: usize,
    ty: Ty,
}
struct Scope {
    helpers: StaticHelpers,
    naturals: BTreeMap<BinderKey, Linear>,
    bases: BTreeMap<BinderKey, Ty>,
    operations: BTreeMap<BinderKey, Operation>,
    context: Context,
    values: BTreeMap<BinderKey, Binding>,
    moved: BTreeSet<usize>,
    next_binding: Rc<Cell<usize>>,
}
impl Scope {
    fn copy(&self, budget: &Budget, span: Span) -> Result<Self> {
        let mut copied = self.basis_scope(budget, span)?;
        budget.charge(span, self.moved.len())?;
        copied.values = budget.values(span, &self.values)?;
        copied.moved = self.moved.clone();
        Ok(copied)
    }
    /// Coherent labels have a closed ordinary-value context. Retain static
    /// facts without cloning runtime values which cannot be observed there.
    fn basis_scope(&self, budget: &Budget, span: Span) -> Result<Self> {
        let mut naturals = BTreeMap::new();
        for (key, value) in &self.naturals {
            naturals.insert(
                budget.key(span, key)?,
                value.copy_budgeted(span, &mut |span, cells| {
                    budget.preparation_charge(span, cells)
                })?,
            );
        }
        let mut bases = BTreeMap::new();
        for (key, value) in &self.bases {
            bases.insert(budget.key(span, key)?, budget.copy_ty(span, value)?);
        }
        let mut operations = BTreeMap::new();
        for (key, value) in &self.operations {
            operations.insert(
                budget.key(span, key)?,
                Operation {
                    basis: budget.copy_ty(span, &value.basis)?,
                    codomain: value
                        .codomain
                        .as_ref()
                        .map(|ty| budget.copy_ty(span, ty))
                        .transpose()?,
                    effect: value.effect,
                    meaning: value.meaning,
                    access: value.access,
                },
            );
        }
        budget.charge(span, 1)?;
        Ok(Self {
            helpers: Rc::clone(&self.helpers),
            naturals,
            bases,
            operations,
            context: budget.copy_context(span, &self.context)?,
            values: BTreeMap::new(),
            moved: BTreeSet::new(),
            next_binding: Rc::clone(&self.next_binding),
        })
    }
}

struct Program<'a> {
    helpers: StaticHelpers,
    modules: BTreeMap<&'a str, &'a ast::Module>,
    resolution: Resolution,
    indices: BTreeMap<DefId, Index<'a>>,
    interfaces: BTreeMap<DefId, Interface>,
    obligations: Vec<Obligation>,
    unitary_regions: Vec<(DefId, Span, BodyEffects)>,
    budget: Rc<Budget>,
}
impl<'a> Program<'a> {
    fn decl(&self, id: DefId) -> &'a ast::Decl {
        let d = self.resolution.declaration(id);
        &self.modules[d.name.0.as_str()].decls[d.ast_index]
    }
    fn module(&self, id: DefId) -> &str {
        &self.resolution.declaration(id).name.0
    }

    /// Check collection-local binding integrity before a consumer receives the
    /// pending ledger. This never discharges its physical or matrix evidence.
    fn validate_pending_bindings(&self, effects: &BTreeMap<DefId, FunctionEffect>) -> Result<()> {
        for obligation in &self.obligations {
            let span = obligation.span;
            self.budget.charge(span, 1)?;
            let failure = || {
                SourceError::new(
                    "source",
                    span,
                    "pending evidence binding does not match the current original source",
                )
            };
            let interface = self
                .interfaces
                .get(&obligation.definition)
                .ok_or_else(failure)?;
            let declaration = self.decl(obligation.definition);
            let index = self
                .indices
                .get(&obligation.definition)
                .ok_or_else(failure)?;
            let resolved = self.resolution.declaration(obligation.definition);
            self.budget
                .charge(span, interface.module.len() + resolved.name.0.len() + 1)?;
            if interface.ast_index != resolved.ast_index
                || interface.module != resolved.name.0
                || interface.kind != declaration.kind
                || span.start > span.end
                || span.start < declaration.span.start
                || span.end > declaration.span.end
                || matches!(interface.kind, FnKind::Classical | FnKind::Meaning)
            {
                return Err(failure().in_module(&interface.module));
            }
            // Ordinal association uses the original identifiers and Index,
            // never a span/name search or a reconstructed lexical table.
            if interface.statics.len() != declaration.static_params.len() {
                return Err(failure().in_module(&interface.module));
            }
            for (formal, original) in interface.statics.iter().zip(&declaration.static_params) {
                self.budget.charge(
                    original.name.span,
                    formal.key.name.len() + original.name.text.len() + 1,
                )?;
                if &formal.key != index.table.key(index.binder(&original.name)) {
                    return Err(failure().in_module(&interface.module));
                }
            }
            let meaning = |id: DefId| -> Result<()> {
                self.budget.charge(span, 1)?;
                let target = self.interfaces.get(&id).ok_or_else(failure)?;
                if target.kind != FnKind::Meaning
                    || !matches!(
                        self.decl(id).body,
                        ast::FnBody::Meaning { .. }
                            | ast::FnBody::MeaningCompose { .. }
                            | ast::FnBody::MeaningTensor { .. }
                    )
                {
                    return Err(failure().in_module(&interface.module));
                }
                Ok(())
            };
            let provider = |id: DefId, ceiling: crate::ir::Effect| -> Result<()> {
                self.budget.charge(span, 1)?;
                let target = self.interfaces.get(&id).ok_or_else(failure)?;
                if matches!(target.kind, FnKind::Classical | FnKind::Meaning)
                    || target.params.len() != 1
                    || !target.params[0].is_quantum_owner()
                    || !target.result.is_quantum_owner()
                    || effects
                        .get(&id)
                        .is_none_or(|fact| fact.inferred() > ceiling)
                {
                    return Err(failure().in_module(&interface.module));
                }
                Ok(())
            };
            match &obligation.kind {
                ObligationKind::Provider {
                    provider: id,
                    ceiling,
                    meaning: required,
                } => {
                    provider(*id, *ceiling)?;
                    if let Some(id) = required {
                        meaning(*id)?;
                    }
                }
                ObligationKind::RuntimeGroupProvider { provider: id } => {
                    self.budget.charge(span, 1)?;
                    let target = self.interfaces.get(id).ok_or_else(failure)?;
                    let original = self.decl(*id);
                    let registered = self.resolution.declaration(*id);
                    self.budget
                        .charge(span, target.module.len() + registered.name.0.len() + 1)?;
                    if matches!(target.kind, FnKind::Classical | FnKind::Meaning)
                        || target.ast_index != registered.ast_index
                        || target.module != registered.name.0
                        || target.kind != original.kind
                        || target.params.len() != original.params.len()
                        || target.params.is_empty()
                        || effects.get(id).map(|fact| fact.inferred())
                            != Some(crate::ir::Effect::Unitary)
                        || !runtime_quantum_group(&target.result, span, &self.budget)?
                    {
                        return Err(failure().in_module(&interface.module));
                    }
                    for parameter in &target.params {
                        self.budget.charge(span, 1)?;
                        if !runtime_quantum_group(parameter, span, &self.budget)? {
                            return Err(failure().in_module(&interface.module));
                        }
                    }
                    // Actual substituted input-group/result/target equality
                    // was checked at the call. This verifies source binding,
                    // never transformation evidence or source preservation.
                }
                ObligationKind::MeaningEquality { required, supplied } => {
                    meaning(*required)?;
                    if let Some(id) = supplied {
                        meaning(*id)?;
                    }
                    // Distinct identities may denote equal matrices; neither
                    // identity equality nor this guard is evidence of that.
                }
                ObligationKind::FunctionEquality {
                    implementation,
                    specification,
                } => {
                    provider(*implementation, crate::ir::Effect::Unitary)?;
                    self.budget.charge(span, 1)?;
                    if !self.interfaces[implementation].statics.is_empty() {
                        return Err(failure().in_module(&interface.module));
                    }
                    if self.interfaces[specification].kind == FnKind::Meaning {
                        meaning(*specification)?;
                    } else {
                        provider(*specification, crate::ir::Effect::Unitary)?;
                        self.budget.charge(span, 1)?;
                        if !self.interfaces[specification].statics.is_empty() {
                            return Err(failure().in_module(&interface.module));
                        }
                    }
                    // Both identities are bound, but their denotations still
                    // require independent exact semantic evidence.
                }
                ObligationKind::CertifiedClean { logical } => match logical {
                    OperationIdentity::Global(resolve::Target::Declaration(id)) => {
                        provider(*id, crate::ir::Effect::Unitary)?
                    }
                    OperationIdentity::Global(resolve::Target::Primitive(id)) => {
                        self.budget
                            .charge(span, id.module.len() + id.name.len() + 2)?;
                        let path = format!("{}::{}", id.module, id.name);
                        use primitive::Primitive::*;
                        if !matches!(
                            primitive::Primitive::lookup(&path),
                            Some(H | X | Z | T | S | Sdg | Tdg | Id | PhaseEighth)
                        ) {
                            return Err(failure().in_module(&interface.module));
                        }
                    }
                    OperationIdentity::Formal(key) => {
                        let mut found = false;
                        for formal in &interface.statics {
                            self.budget
                                .charge(span, formal.key.name.len() + key.name.len() + 1)?;
                            if &formal.key == key {
                                found = matches!(&formal.kind,StaticKind::Operation {access,..} if access[super::formals::access_index(ast::Access::Apply)]);
                                break;
                            }
                        }
                        if !found {
                            return Err(failure().in_module(&interface.module));
                        }
                    }
                },
                ObligationKind::Injectivity
                | ObligationKind::ControlSectors
                | ObligationKind::ProtectedClean
                | ObligationKind::TransformedMeaning => {}
            }
        }
        Ok(())
    }
}

pub(super) fn program_with<'a, R>(
    modules: BTreeMap<&'a str, &'a ast::Module>,
    limits: SourceLimits,
    finish: impl FnOnce(
        &Resolution,
        &BTreeMap<DefId, Interface>,
        &StaticHelpers,
        &BTreeMap<DefId, FunctionEffect>,
        &[DefId],
        &mut BTreeMap<DefId, Index<'a>>,
        &Budget,
    ) -> Result<R>,
) -> Result<(CheckedProgram, R)> {
    let budget = Rc::new(Budget {
        remaining: Cell::new(limits.work),
        limits,
    });
    let resolution = Resolution::new_budgeted(
        modules.iter().map(|(name, module)| (*name, *module)),
        |span, cells| budget.charge(span, cells),
    )?;
    let mut program = Program {
        helpers: Rc::new(BTreeMap::new()),
        modules,
        resolution,
        indices: BTreeMap::new(),
        interfaces: BTreeMap::new(),
        obligations: Vec::new(),
        unitary_regions: Vec::new(),
        budget,
    };
    declarations::prepare(&mut program)?;
    let mut bodies = BTreeMap::new();
    let mut edges = BTreeMap::new();
    // Canonical DefId order deliberately does not choose declaration diagnostics.
    let mut order = Vec::new();
    for (name, module) in &program.modules {
        let owner = program
            .resolution
            .module(name)
            .expect("registered original module");
        program.budget.charge(module.span, module.decls.len())?;
        for decl in &module.decls {
            if decl.kind == FnKind::Static {
                continue;
            }
            order.push(
                program
                    .resolution
                    .local(owner, &decl.name.text)
                    .expect("registered original declaration"),
            );
        }
    }
    for id in &order {
        let (body, dependencies) =
            body::check(&mut program, *id).map_err(|e| e.in_module(program.module(*id)))?;
        program.budget.charge(program.decl(*id).span, 2)?;
        bodies.insert(*id, body);
        edges.insert(*id, dependencies);
    }
    if let Some((owner, span, _)) =
        resolve::cycle_budgeted(order.iter().copied(), &edges, false, |span, cells| {
            program.budget.charge(span, cells)
        })?
    {
        return Err(SourceError::new(
            "cycle",
            span,
            "recursive source dependency cycle is unsupported",
        )
        .in_module(program.module(owner)));
    }
    program.budget.charge(
        Span::default(),
        edges.len() + edges.values().map(Vec::len).sum::<usize>(),
    )?;
    let dependency_order = resolve::order_budgeted(
        edges
            .iter()
            .map(|(id, targets)| (*id, targets.iter().map(|(target, _)| *target).collect()))
            .collect(),
        |span, cells| program.budget.charge(span, cells),
    )?
    .map_err(|id| {
        SourceError::new(
            "cycle",
            program.decl(id).name.span,
            "recursive source dependency cycle is unsupported",
        )
        .in_module(program.module(id))
    })?;
    let inferred =
        super::effects::infer_with(&bodies, |span, cells| program.budget.charge(span, cells))?
            .ok_or_else(|| {
                SourceError::new(
                    "effect",
                    Span::default(),
                    "unresolved checked effect dependency",
                )
            })?;
    let mut effects = BTreeMap::new();
    for id in &order {
        let decl = program.decl(*id);
        if decl.kind == FnKind::Meaning {
            continue;
        }
        let fact = FunctionEffect::checked(decl.kind, inferred[id]).ok_or_else(|| {
            SourceError::new(
                "effect",
                bodies[id].origin(&inferred),
                super::effects::assertion_error(&decl.name.text, decl.kind, inferred[id]),
            )
            .in_module(program.module(*id))
        })?;
        if let Some((ceiling, span)) = bodies[id].first_violation(&inferred) {
            let message = if ceiling == crate::ir::Effect::Unitary {
                super::effects::unitary_required(
                    "operation provider's inferred body effect must be Unitary",
                )
            } else {
                format!(
                    "operation provider's inferred body effect exceeds required {ceiling:?} ceiling"
                )
            };
            return Err(SourceError::new("effect", span, message).in_module(program.module(*id)));
        }
        program.budget.charge(decl.span, 1)?;
        effects.insert(*id, fact);
    }
    for (owner, span, region) in &program.unitary_regions {
        if region.inferred_with(&inferred) != Some(crate::ir::Effect::Unitary) {
            return Err(SourceError::new(
                "effect",
                *span,
                super::effects::unitary_required("with_computed body must be unitary"),
            )
            .in_module(program.module(*owner)));
        }
    }
    program.validate_pending_bindings(&effects)?;
    let output = finish(
        &program.resolution,
        &program.interfaces,
        &program.helpers,
        &effects,
        &dependency_order,
        &mut program.indices,
        &program.budget,
    )?;
    program
        .budget
        .charge(Span::default(), program.indices.len() * 2)?;
    let lexical = program
        .indices
        .into_iter()
        .map(|(id, index)| (id, Arc::new(index.table)))
        .collect();
    Ok((
        CheckedProgram {
            resolution: program.resolution,
            interfaces: program.interfaces,
            effects,
            lexical,
            obligations: program.obligations,
            dependency_order,
        },
        output,
    ))
}

pub(super) fn close_type_budgeted(
    ty: &Ty,
    naturals: &BTreeMap<BinderKey, u32>,
    bases: &BTreeMap<BinderKey, Type<u32>>,
    span: Span,
    mut charge: impl FnMut(Span, usize) -> Result<()>,
) -> Result<Type<u32>> {
    let mut pending = Vec::new();
    charge(span, 1)?;
    pending.push((ty, 1usize));
    let mut cells = 0usize;
    while let Some((node, depth)) = pending.pop() {
        charge(span, 1)?;
        if depth > 64 {
            return Err(SourceError::new(
                "limit",
                span,
                "closed type exceeds depth 64",
            ));
        }
        let n = match &node.kind {
            Kind::Parameter(parameter) => {
                let replacement = parameter
                    .key
                    .as_ref()
                    .and_then(|key| bases.get(key))
                    .ok_or_else(|| {
                        SourceError::new(
                            "static",
                            span,
                            format!("missing Basis binding {}", parameter.name),
                        )
                    })?;
                let size =
                    type_size_budgeted(replacement, 4096, 65 - depth, true, span, &mut charge)?;
                charge(span, size.nodes)?;
                size.nodes
            }
            Kind::Tuple(fields) => {
                if fields.len() > 64 {
                    return Err(SourceError::new(
                        "limit",
                        span,
                        "closed tuple exceeds 64 fields",
                    ));
                }
                charge(span, fields.len())?;
                pending.extend(fields.iter().rev().map(|field| (field, depth + 1)));
                1
            }
            Kind::Q(child) => {
                charge(span, 1)?;
                pending.push((child, depth));
                0
            }
            _ => 1,
        };
        cells = cells
            .checked_add(n)
            .ok_or_else(|| SourceError::new("limit", span, "closed type cell count overflow"))?;
        if cells > 4096 {
            return Err(SourceError::new(
                "limit",
                span,
                "closed type exceeds 4096 expanded cells",
            ));
        }
    }
    charge(span, cells)?;
    ty.map_parts(
        &mut |linear| {
            let mut value = linear.constant;
            for (key, coefficient) in &linear.terms {
                charge(span, 1)?;
                let n = naturals.get(key).ok_or_else(|| {
                    SourceError::new(
                        "static",
                        span,
                        format!("missing natural binding {}", key.name),
                    )
                })?;
                value = value
                    .checked_add(coefficient.checked_mul(i128::from(*n)).ok_or_else(|| {
                        SourceError::new("limit", span, "closed size multiplication overflow")
                    })?)
                    .ok_or_else(|| {
                        SourceError::new("limit", span, "closed size addition overflow")
                    })?;
            }
            u32::try_from(value).map_err(|_| {
                SourceError::new("size", span, "closed size must fit a nonnegative u32")
            })
        },
        &mut |parameter| {
            parameter
                .key
                .as_ref()
                .and_then(|key| bases.get(key))
                .cloned()
                .ok_or_else(|| {
                    SourceError::new(
                        "static",
                        span,
                        format!("missing Basis binding {}", parameter.name),
                    )
                })
        },
    )
}
