//! Original resolved static/evidence templates, never checking evidence.
//!
//! Ordinary natural expression and helper-argument trees accompany normalized
//! facts, retaining their checked u32 nodes and helper work. A helper call uses
//! its shared checked affine template, whose signed i128 intermediates and final
//! u32 contract are unchanged; this metadata does not replay its source body.
//! Source occurrence IDs belong to the one original lexical collection.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;
use crate::frontend::resolve::ModuleId;
use crate::frontend::resolve::locals::{
    BindingKind, NodeId, NodeKind, OriginalNode, OriginalRegion, ResolvedUse, UseSiteId,
};

mod body_statics;
mod interface_naturals;
mod runtime_owners;
pub(super) use body_statics::expression_natural_roots;
pub(in crate::frontend) use body_statics::{
    BodyStaticKind, BodyStaticOriginal, BodyStaticPlan, original_body_static,
};
pub(in crate::frontend) use interface_naturals::{
    InterfaceNaturalContext, InterfaceNaturals, InterfaceSlot, TypeChild,
    capture_interface_naturals_budgeted,
};
pub(in crate::frontend) use runtime_owners::{RuntimeOwnerPlan, original_runtime_owners};

#[derive(Clone, Debug)]
pub(in crate::frontend) struct ResolvedReference {
    pub site: UseSiteId,
    pub target: ResolvedUse,
    pub local: Option<BinderKey>,
}

#[derive(Clone, Debug)]
pub(in crate::frontend) struct ResolvedNatural {
    pub node: NodeId,
    pub span: Span,
    pub kind: ResolvedNaturalKind,
}
#[derive(Clone, Debug)]
pub(in crate::frontend) enum ResolvedNaturalKind {
    Number(i128),
    Name(ResolvedReference),
    Helper {
        callee: ResolvedReference,
        template: Arc<StaticHelper>,
        arguments: Vec<ResolvedNatural>,
    },
    Add(Box<ResolvedNatural>, Box<ResolvedNatural>),
    Sub(Box<ResolvedNatural>, Box<ResolvedNatural>),
    Mul(Box<ResolvedNatural>, Box<ResolvedNatural>),
}
pub(in crate::frontend) type ResolvedType = Type<ResolvedNatural>;

#[derive(Clone, Debug)]
pub(in crate::frontend) struct ResolvedStatic {
    pub node: Option<NodeId>,
    pub span: Span,
    pub kind: ResolvedStaticKind,
    pub type_references: Vec<ResolvedReference>,
    pub type_nodes: Vec<NodeId>,
}
#[derive(Clone, Debug)]
pub(in crate::frontend) enum ResolvedStaticKind {
    Basis(ResolvedType),
    Natural(ResolvedNatural),
    Name(ResolvedReference),
    Specialize(ResolvedReference, Vec<ResolvedStatic>),
    Bind(ResolvedReference, ResolvedReference),
    Then(Box<ResolvedStatic>, Box<ResolvedStatic>),
    Tensor(Box<ResolvedStatic>, Box<ResolvedStatic>),
    Inverse(Box<ResolvedStatic>),
    Controlled(Box<ResolvedStatic>),
    Repeat {
        power: bool,
        count: ResolvedNatural,
        child: Box<ResolvedStatic>,
    },
    Conjugate(Box<ResolvedStatic>, Box<ResolvedStatic>),
}

#[derive(Clone, Debug)]
pub(in crate::frontend) enum NaturalBindingPlan {
    Initializer(Arc<ResolvedNatural>),
    FoldIndex {
        start: Arc<ResolvedNatural>,
        end: Arc<ResolvedNatural>,
    },
}
#[derive(Clone, Debug)]
pub(in crate::frontend) enum StaticRegion {
    Predicate {
        node: NodeId,
        left: Arc<ResolvedNatural>,
        comparison: ast::Compare,
        right: Arc<ResolvedNatural>,
        truth: bool,
    },
    Fold {
        node: NodeId,
        index: BinderKey,
        start: Arc<ResolvedNatural>,
        end: Arc<ResolvedNatural>,
    },
}

#[derive(Clone, Debug)]
pub(in crate::frontend) struct OperationContract {
    pub input: Ty,
    pub codomain: Option<Ty>,
    pub effect: crate::ir::Effect,
    pub access: [bool; 3],
    pub meaning: Option<DefId>,
}
impl OperationContract {
    pub fn output(&self) -> &Ty {
        self.codomain.as_ref().unwrap_or(&self.input)
    }
}

/// Only original static bindings/facts; runtime values and owners are absent.
/// An operation key denotes the declaring formal. A concrete instance must
/// substitute its complete actual operation plan, never this summary alone.
#[derive(Clone, Debug)]
pub(in crate::frontend) struct StaticEnvironment {
    pub owner: DefId,
    pub module: ModuleId,
    pub naturals: BTreeMap<BinderKey, Linear>,
    pub local_naturals: BTreeMap<BinderKey, NaturalBindingPlan>,
    pub bases: BTreeMap<BinderKey, Ty>,
    pub operations: BTreeMap<BinderKey, OperationContract>,
    pub context: Context,
    pub regions: Vec<StaticRegion>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::frontend) enum StaticCategory {
    Basis,
    Natural,
    Operation,
}
#[derive(Clone, Debug)]
pub(in crate::frontend) struct StaticActual {
    pub formal: BinderKey,
    pub category: StaticCategory,
    pub value: Arc<ResolvedStatic>,
}
#[derive(Clone, Debug)]
pub(in crate::frontend) struct StaticCallPlan {
    pub owner: DefId,
    pub module: ModuleId,
    pub node: NodeId,
    pub callee: ResolvedReference,
    pub target: DefId,
    pub arguments: Vec<StaticActual>,
    pub parameters: Vec<Ty>,
    pub result: Ty,
    pub access: [bool; 3],
    /// Filled only after complete source effect inference/bound checking.
    pub source_effect: Option<crate::ir::Effect>,
    pub environment: Arc<StaticEnvironment>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(in crate::frontend) struct ObligationId {
    pub definition: DefId,
    pub ordinal: usize,
}
#[derive(Clone, Debug)]
pub(in crate::frontend) enum EvidenceSubject {
    /// The actual original expression remains in the immutable source owner.
    Expression,
    Operation {
        operation: Arc<ResolvedStatic>,
        required: Option<OperationContract>,
        actual: Option<Box<OperationContract>>,
    },
    Call {
        site: UseSiteId,
        requested: ast::Access,
    },
    FunctionPair {
        implementation: ResolvedReference,
        specification: ResolvedReference,
    },
}
#[derive(Clone, Debug)]
pub(in crate::frontend) struct EvidencePlan {
    pub node: NodeId,
    pub environment: Arc<StaticEnvironment>,
    pub subject: EvidenceSubject,
    /// Ordered common-judgment owner types for this original Ctrl action only.
    /// This is untrusted action metadata, not caller-prefix/frame evidence.
    pub runtime_owners: Vec<RuntimeOwnerPlan>,
}

pub(super) struct Capture<'a, 'ast> {
    pub index: &'a Index<'ast>,
    pub helpers: &'a StaticHelpers,
    pub budget: &'a Budget,
}
impl Capture<'_, '_> {
    pub fn reference(&self, name: &ast::Ident) -> Result<ResolvedReference> {
        self.reference_at(self.index.usage(name), name.span)
    }
    fn reference_at(&self, site: UseSiteId, span: Span) -> Result<ResolvedReference> {
        self.budget.charge(span, 2)?;
        let target = self.index.table.usage(site).target;
        let local = match target {
            ResolvedUse::Local(id) => Some(self.budget.key(span, self.index.table.key(id))?),
            ResolvedUse::Global(_) => None,
            ResolvedUse::Unresolved => {
                return Err(SourceError::new(
                    "source",
                    span,
                    "unresolved static plan occurrence",
                ));
            }
        };
        Ok(ResolvedReference {
            site,
            target,
            local,
        })
    }
    pub fn natural(&self, source: &ast::Natural) -> Result<ResolvedNatural> {
        self.natural_at(source, 1)
    }
    fn natural_at(&self, source: &ast::Natural, depth: usize) -> Result<ResolvedNatural> {
        self.budget.charge(source.span, 2)?;
        if depth > 128 {
            return Err(SourceError::new(
                "limit",
                source.span,
                "retained natural plan exceeds depth 128",
            ));
        }
        use ast::NatKind;
        let kind = match &source.kind {
            NatKind::Number(n) => ResolvedNaturalKind::Number(*n),
            NatKind::Name(_) => ResolvedNaturalKind::Name(
                self.reference_at(self.index.natural_usage(source), source.span)?,
            ),
            NatKind::Call { callee, arguments } => {
                let reference = self.reference(callee)?;
                let ResolvedUse::Global(resolve::Target::Declaration(id)) = reference.target else {
                    return Err(SourceError::new(
                        "source",
                        callee.span,
                        "natural plan does not name its checked helper",
                    ));
                };
                let helper = self.helpers.get(&id).ok_or_else(|| {
                    SourceError::new(
                        "source",
                        callee.span,
                        "missing original checked helper template",
                    )
                })?;
                if helper.parameters.len() != arguments.len() {
                    return Err(SourceError::new(
                        "source",
                        source.span,
                        "retained helper argument arity differs",
                    ));
                }
                self.budget.charge(source.span, 1 + arguments.len())?;
                ResolvedNaturalKind::Helper {
                    callee: reference,
                    template: Arc::clone(helper),
                    arguments: arguments
                        .iter()
                        .map(|n| self.natural_at(n, depth + 1))
                        .collect::<Result<_>>()?,
                }
            }
            NatKind::Add(a, b) | NatKind::Sub(a, b) | NatKind::Mul(a, b) => {
                self.budget.charge(source.span, 2)?;
                let a = Box::new(self.natural_at(a, depth + 1)?);
                let b = Box::new(self.natural_at(b, depth + 1)?);
                match source.kind {
                    NatKind::Add(..) => ResolvedNaturalKind::Add(a, b),
                    NatKind::Sub(..) => ResolvedNaturalKind::Sub(a, b),
                    _ => ResolvedNaturalKind::Mul(a, b),
                }
            }
        };
        Ok(ResolvedNatural {
            node: self.index.node_id_natural(source),
            span: source.span,
            kind,
        })
    }
    fn basis_at(
        &self,
        source: &ast::Type,
        depth: usize,
        references: &mut Vec<ResolvedReference>,
        nodes: &mut Vec<NodeId>,
    ) -> Result<ResolvedType> {
        self.budget.charge(source.span, 3)?;
        nodes.push(self.index.node_id_ty(source));
        if depth > 64 {
            return Err(SourceError::new(
                "limit",
                source.span,
                "retained Basis plan exceeds depth 64",
            ));
        }
        use ast::TypeKind;
        Ok(match &source.kind {
            TypeKind::Unit => Type::unit(),
            TypeKind::Bit => Type::bit(),
            TypeKind::Bits(n) => Type::bits(self.natural(n)?),
            TypeKind::Named(name) => {
                let reference = self.reference(name)?;
                let key = self.budget.key(
                    name.span,
                    reference.local.as_ref().ok_or_else(|| {
                        SourceError::new(
                            "source",
                            name.span,
                            "Basis plan requires its original static binder",
                        )
                    })?,
                )?;
                if self.index.table.binder(key.id).kind != BindingKind::StaticBasis {
                    return Err(SourceError::new(
                        "source",
                        name.span,
                        "Basis plan has a non-Basis binder",
                    ));
                }
                self.budget.charge(name.span, name.text.len() + 1)?;
                self.budget.charge(name.span, 1)?;
                references.push(reference);
                Type::parameter(super::super::types::TypeParameter {
                    key: Some(key),
                    name: name.text.clone(),
                    span: name.span,
                })
            }
            TypeKind::Tuple(fields) => {
                if fields.len() > 64 {
                    return Err(SourceError::new(
                        "limit",
                        source.span,
                        "retained Basis tuple exceeds 64 fields",
                    ));
                }
                self.budget.charge(source.span, fields.len())?;
                Type::tuple(
                    fields
                        .iter()
                        .map(|ty| self.basis_at(ty, depth + 1, references, nodes))
                        .collect::<Result<_>>()?,
                )
            }
            TypeKind::Q(_) => {
                return Err(SourceError::new(
                    "source",
                    source.span,
                    "retained Basis argument contains quantum ownership",
                ));
            }
        })
    }
    pub fn operation(&self, source: &ast::StaticOp) -> Result<ResolvedStatic> {
        self.operation_at(source, 1)
    }
    fn operation_at(&self, source: &ast::StaticOp, depth: usize) -> Result<ResolvedStatic> {
        self.budget.charge(source.span, 2)?;
        if depth > 64 {
            return Err(SourceError::new(
                "limit",
                source.span,
                "retained static plan exceeds depth 64",
            ));
        }
        use ast::StaticOpKind;
        let mut type_references = Vec::new();
        let mut type_nodes = Vec::new();
        let kind = match &source.kind {
            StaticOpKind::Type(ty) => ResolvedStaticKind::Basis(self.basis_at(
                ty,
                1,
                &mut type_references,
                &mut type_nodes,
            )?),
            StaticOpKind::Natural(n) => ResolvedStaticKind::Natural(self.natural(n)?),
            StaticOpKind::Name(name) => ResolvedStaticKind::Name(self.reference(name)?),
            StaticOpKind::Specialize { name, arguments } => {
                self.budget.charge(source.span, arguments.len())?;
                ResolvedStaticKind::Specialize(
                    self.reference(name)?,
                    arguments
                        .iter()
                        .map(|op| self.operation_at(op, depth + 1))
                        .collect::<Result<_>>()?,
                )
            }
            StaticOpKind::Bind {
                implementation,
                meaning,
            } => {
                ResolvedStaticKind::Bind(self.reference(implementation)?, self.reference(meaning)?)
            }
            StaticOpKind::Inverse(child) | StaticOpKind::Controlled(child) => {
                self.budget.charge(source.span, 1)?;
                let child = Box::new(self.operation_at(child, depth + 1)?);
                if matches!(source.kind, StaticOpKind::Inverse(_)) {
                    ResolvedStaticKind::Inverse(child)
                } else {
                    ResolvedStaticKind::Controlled(child)
                }
            }
            StaticOpKind::Then(a, b)
            | StaticOpKind::Tensor(a, b)
            | StaticOpKind::Conjugate(a, b) => {
                self.budget.charge(source.span, 2)?;
                let a = Box::new(self.operation_at(a, depth + 1)?);
                let b = Box::new(self.operation_at(b, depth + 1)?);
                match source.kind {
                    StaticOpKind::Then(..) => ResolvedStaticKind::Then(a, b),
                    StaticOpKind::Tensor(..) => ResolvedStaticKind::Tensor(a, b),
                    _ => ResolvedStaticKind::Conjugate(a, b),
                }
            }
            StaticOpKind::Repeat(count, child) => {
                self.budget.charge(source.span, 1)?;
                let (ast::Count::Natural(n) | ast::Count::Power(n)) = count;
                ResolvedStaticKind::Repeat {
                    power: matches!(count, ast::Count::Power(_)),
                    count: self.natural(n)?,
                    child: Box::new(self.operation_at(child, depth + 1)?),
                }
            }
        };
        Ok(ResolvedStatic {
            node: Some(self.index.node_id_static_op(source)),
            span: source.span,
            kind,
            type_references,
            type_nodes,
        })
    }
    pub fn named(&self, name: &ast::Ident, arguments: &[ast::StaticOp]) -> Result<ResolvedStatic> {
        self.budget.charge(name.span, 2 + arguments.len())?;
        let reference = self.reference(name)?;
        let kind = if arguments.is_empty() {
            ResolvedStaticKind::Name(reference)
        } else {
            ResolvedStaticKind::Specialize(
                reference,
                arguments
                    .iter()
                    .map(|arg| self.operation(arg))
                    .collect::<Result<_>>()?,
            )
        };
        Ok(ResolvedStatic {
            node: None,
            span: name.span,
            kind,
            type_references: Vec::new(),
            type_nodes: Vec::new(),
        })
    }
}

pub(super) fn operation_contract(
    operation: &Operation,
    span: Span,
    budget: &Budget,
) -> Result<OperationContract> {
    budget.charge(span, 4)?;
    Ok(OperationContract {
        input: budget.copy_ty(span, &operation.basis)?,
        codomain: operation
            .codomain
            .as_ref()
            .map(|ty| budget.copy_ty(span, ty))
            .transpose()?,
        effect: operation.effect,
        access: operation.access,
        meaning: operation.meaning,
    })
}

pub(super) fn environment(
    owner: DefId,
    module: ModuleId,
    scope: &Scope,
    local_plans: &BTreeMap<BinderKey, NaturalBindingPlan>,
    regions: &[StaticRegion],
    span: Span,
    budget: &Budget,
) -> Result<Arc<StaticEnvironment>> {
    budget.charge(span, 2 + regions.len())?;
    let mut naturals = BTreeMap::new();
    let mut local_naturals = BTreeMap::new();
    for (key, value) in &scope.naturals {
        budget.charge(span, 1)?;
        naturals.insert(
            budget.key(span, key)?,
            value.copy_budgeted(span, &mut |s, n| budget.preparation_charge(s, n))?,
        );
        if let Some(plan) = local_plans.get(key) {
            budget.charge(span, 3)?;
            local_naturals.insert(budget.key(span, key)?, plan.clone());
        }
    }
    let mut bases = BTreeMap::new();
    for (key, ty) in &scope.bases {
        budget.charge(span, 1)?;
        bases.insert(budget.key(span, key)?, budget.copy_ty(span, ty)?);
    }
    let mut operations = BTreeMap::new();
    for (key, operation) in &scope.operations {
        budget.charge(span, 1)?;
        operations.insert(
            budget.key(span, key)?,
            operation_contract(operation, span, budget)?,
        );
    }
    let mut copied_regions = Vec::with_capacity(regions.len());
    for region in regions {
        budget.charge(span, 4)?;
        copied_regions.push(match region {
            StaticRegion::Predicate {
                node,
                left,
                comparison,
                right,
                truth,
            } => StaticRegion::Predicate {
                node: *node,
                left: Arc::clone(left),
                comparison: *comparison,
                right: Arc::clone(right),
                truth: *truth,
            },
            StaticRegion::Fold {
                node,
                index,
                start,
                end,
            } => StaticRegion::Fold {
                node: *node,
                index: budget.key(span, index)?,
                start: Arc::clone(start),
                end: Arc::clone(end),
            },
        });
    }
    Ok(Arc::new(StaticEnvironment {
        owner,
        module,
        naturals,
        local_naturals,
        bases,
        operations,
        context: budget.copy_context(span, &scope.context)?,
        regions: copied_regions,
    }))
}

/// Unbound original keys, never textual-name guesses or erased affine terms.
#[derive(Debug)]
pub(in crate::frontend) enum PlanClosure {
    Closed,
    Deferred(BTreeSet<BinderKey>),
}
impl ResolvedStatic {
    pub fn classify_budgeted(
        &self,
        environment: &StaticEnvironment,
        bound: &BTreeSet<BinderKey>,
        charge: &mut impl FnMut(Span, usize) -> Result<()>,
    ) -> Result<PlanClosure> {
        let mut keys = BTreeSet::new();
        let mut active = BTreeSet::new();
        free_static(self, environment, bound, &mut keys, &mut active, charge)?;
        Ok(if keys.is_empty() {
            PlanClosure::Closed
        } else {
            PlanClosure::Deferred(keys)
        })
    }
}
enum FreeTask<'a> {
    Static(&'a ResolvedStatic),
    Natural(&'a ResolvedNatural),
    Type(&'a ResolvedType, Span),
    Reference(&'a ResolvedReference, Span),
    Key(&'a BinderKey, Span),
    Leave(BinderKey),
}
fn free_static(
    value: &ResolvedStatic,
    environment: &StaticEnvironment,
    bound: &BTreeSet<BinderKey>,
    keys: &mut BTreeSet<BinderKey>,
    active: &mut BTreeSet<BinderKey>,
    charge: &mut impl FnMut(Span, usize) -> Result<()>,
) -> Result<()> {
    charge(value.span, 1)?;
    let mut pending = vec![FreeTask::Static(value)];
    while let Some(task) = pending.pop() {
        match task {
            FreeTask::Key(key, span) => {
                charge(span, key.name.len() + 2)?;
                if bound.contains(key) {
                    continue;
                }
                if let Some(NaturalBindingPlan::Initializer(value)) =
                    environment.local_naturals.get(key)
                {
                    // Both retained keys and both stack cells are charged first.
                    charge(span, 2 * key.name.len() + 4)?;
                    if !active.insert(key.clone()) {
                        return Err(SourceError::new(
                            "source",
                            span,
                            "cyclic retained static binding",
                        ));
                    }
                    pending.push(FreeTask::Leave(key.clone()));
                    pending.push(FreeTask::Natural(value));
                } else {
                    charge(span, key.name.len() + 1)?;
                    keys.insert(key.clone());
                }
            }
            FreeTask::Leave(key) => {
                active.remove(&key);
            }
            FreeTask::Reference(reference, span) => {
                charge(span, 1)?;
                if let Some(key) = &reference.local {
                    charge(span, 1)?;
                    pending.push(FreeTask::Key(key, span));
                }
            }
            FreeTask::Natural(value) => {
                charge(value.span, 1)?;
                match &value.kind {
                    ResolvedNaturalKind::Number(_) => {}
                    ResolvedNaturalKind::Name(reference) => {
                        charge(value.span, 1)?;
                        pending.push(FreeTask::Reference(reference, value.span));
                    }
                    ResolvedNaturalKind::Helper {
                        callee, arguments, ..
                    } => {
                        charge(value.span, 1 + arguments.len())?;
                        pending.extend(arguments.iter().rev().map(FreeTask::Natural));
                        pending.push(FreeTask::Reference(callee, value.span));
                    }
                    ResolvedNaturalKind::Add(a, b)
                    | ResolvedNaturalKind::Sub(a, b)
                    | ResolvedNaturalKind::Mul(a, b) => {
                        charge(value.span, 2)?;
                        pending.extend([FreeTask::Natural(b), FreeTask::Natural(a)]);
                    }
                }
            }
            FreeTask::Type(value, span) => {
                charge(span, 1)?;
                match &value.kind {
                    Kind::Bits(n) => {
                        charge(span, 1)?;
                        pending.push(FreeTask::Natural(n));
                    }
                    Kind::Parameter(parameter) => {
                        let key = parameter.key.as_ref().ok_or_else(|| {
                            SourceError::new("source", span, "unbound retained Basis identity")
                        })?;
                        charge(span, 1)?;
                        pending.push(FreeTask::Key(key, span));
                    }
                    Kind::Tuple(fields) => {
                        charge(span, fields.len())?;
                        pending.extend(fields.iter().rev().map(|ty| FreeTask::Type(ty, span)));
                    }
                    Kind::Q(_) => {
                        return Err(SourceError::new(
                            "source",
                            span,
                            "retained Basis plan contains ownership",
                        ));
                    }
                    _ => {}
                }
            }
            FreeTask::Static(value) => {
                charge(value.span, 1)?;
                match &value.kind {
                    ResolvedStaticKind::Basis(ty) => {
                        charge(value.span, 1)?;
                        pending.push(FreeTask::Type(ty, value.span));
                    }
                    ResolvedStaticKind::Natural(n) => {
                        charge(value.span, 1)?;
                        pending.push(FreeTask::Natural(n));
                    }
                    ResolvedStaticKind::Name(reference) => {
                        charge(value.span, 1)?;
                        pending.push(FreeTask::Reference(reference, value.span));
                    }
                    ResolvedStaticKind::Specialize(reference, args) => {
                        charge(value.span, 1 + args.len())?;
                        pending.extend(args.iter().rev().map(FreeTask::Static));
                        pending.push(FreeTask::Reference(reference, value.span));
                    }
                    ResolvedStaticKind::Bind(a, b) => {
                        charge(value.span, 2)?;
                        pending.extend([
                            FreeTask::Reference(b, value.span),
                            FreeTask::Reference(a, value.span),
                        ]);
                    }
                    ResolvedStaticKind::Then(a, b)
                    | ResolvedStaticKind::Tensor(a, b)
                    | ResolvedStaticKind::Conjugate(a, b) => {
                        charge(value.span, 2)?;
                        pending.extend([FreeTask::Static(b), FreeTask::Static(a)]);
                    }
                    ResolvedStaticKind::Inverse(child) | ResolvedStaticKind::Controlled(child) => {
                        charge(value.span, 1)?;
                        pending.push(FreeTask::Static(child));
                    }
                    ResolvedStaticKind::Repeat { count, child, .. } => {
                        charge(value.span, 2)?;
                        pending.extend([FreeTask::Static(child), FreeTask::Natural(count)]);
                    }
                }
            }
        }
    }
    Ok(())
}

struct Validation<'a, 'ast> {
    indices: &'a BTreeMap<DefId, Index<'ast>>,
    helpers: &'a StaticHelpers,
    interfaces: &'a BTreeMap<DefId, Interface>,
    resolution: &'a Resolution,
    budget: &'a Budget,
}
impl<'ast> Validation<'_, 'ast> {
    fn failure(&self, span: Span) -> SourceError {
        SourceError::new(
            "source",
            span,
            "retained static/evidence plan differs from its original collection",
        )
    }
    fn node(
        &self,
        owner: DefId,
        node: NodeId,
        kind: crate::frontend::resolve::locals::NodeKind,
        span: Span,
    ) -> Result<()> {
        self.original(owner, node, kind, span).map(|_| ())
    }
    fn original(
        &self,
        owner: DefId,
        node: NodeId,
        kind: NodeKind,
        span: Span,
    ) -> Result<OriginalNode<'ast>> {
        self.budget.charge(span, 1)?;
        if node.definition() != owner {
            return Err(self.failure(span));
        }
        let original = self
            .indices
            .get(&owner)
            .and_then(|index| index.original_node(node))
            .ok_or_else(|| self.failure(span))?;
        if original.kind() != kind {
            return Err(self.failure(span));
        }
        Ok(original)
    }
    fn expression(&self, owner: DefId, node: NodeId, span: Span) -> Result<&'ast ast::Expr> {
        let OriginalNode::Expression(source) = self.original(owner, node, NodeKind::Expr, span)?
        else {
            return Err(self.failure(span));
        };
        Ok(source)
    }
    fn key(&self, owner: DefId, key: &BinderKey, span: Span) -> Result<BindingKind> {
        self.budget.charge(span, key.name.len() + 1)?;
        if key.id.definition() != owner {
            return Err(self.failure(span));
        }
        let info = self
            .indices
            .get(&owner)
            .and_then(|index| index.table.try_binder(key.id))
            .ok_or_else(|| self.failure(span))?;
        if &info.key != key {
            return Err(self.failure(span));
        }
        Ok(info.kind)
    }
    fn reference(&self, owner: DefId, reference: &ResolvedReference, span: Span) -> Result<()> {
        self.budget.charge(span, 1)?;
        if reference.site.definition() != owner {
            return Err(self.failure(span));
        }
        let usage = self
            .indices
            .get(&owner)
            .and_then(|index| index.table.try_usage(reference.site))
            .ok_or_else(|| self.failure(span))?;
        if usage.target != reference.target {
            return Err(self.failure(span));
        }
        match (reference.target, &reference.local) {
            (ResolvedUse::Local(id), Some(key)) if id == key.id => {
                self.key(owner, key, span)?;
            }
            (ResolvedUse::Global(_), None) => {}
            _ => return Err(self.failure(span)),
        }
        Ok(())
    }
    fn named_reference(
        &self,
        owner: DefId,
        reference: &ResolvedReference,
        name: &ast::Ident,
    ) -> Result<()> {
        self.reference(owner, reference, name.span)?;
        if reference.site != self.indices[&owner].usage(name) {
            return Err(self.failure(name.span));
        }
        Ok(())
    }
    #[cfg(test)]
    fn natural(&self, owner: DefId, value: &ResolvedNatural) -> Result<()> {
        let OriginalNode::Natural(source) =
            self.original(owner, value.node, NodeKind::Natural, value.span)?
        else {
            return Err(self.failure(value.span));
        };
        self.natural_at(owner, source, value, 1)
    }
    fn natural_at(
        &self,
        owner: DefId,
        source: &ast::Natural,
        value: &ResolvedNatural,
        depth: usize,
    ) -> Result<()> {
        self.budget.charge(value.span, 1)?;
        if depth > 128
            || value.node != self.indices[&owner].node_id_natural(source)
            || value.span != source.span
        {
            return Err(self.failure(value.span));
        }
        match (&source.kind, &value.kind) {
            (ast::NatKind::Number(original), ResolvedNaturalKind::Number(number)) => {
                if original != number || *number < 0 {
                    return Err(self.failure(value.span));
                }
            }
            (ast::NatKind::Name(_), ResolvedNaturalKind::Name(reference)) => {
                self.reference(owner, reference, value.span)?;
                if reference.site != self.indices[&owner].natural_usage(source) {
                    return Err(self.failure(value.span));
                }
                let key = reference
                    .local
                    .as_ref()
                    .ok_or_else(|| self.failure(value.span))?;
                if !matches!(
                    self.key(owner, key, value.span)?,
                    BindingKind::StaticNatural | BindingKind::FoldIndex
                ) {
                    return Err(self.failure(value.span));
                }
            }
            (
                ast::NatKind::Call {
                    callee: name,
                    arguments: original_arguments,
                },
                ResolvedNaturalKind::Helper {
                    callee,
                    template,
                    arguments,
                },
            ) => {
                self.named_reference(owner, callee, name)?;
                let ResolvedUse::Global(resolve::Target::Declaration(id)) = callee.target else {
                    return Err(self.failure(value.span));
                };
                let original = self
                    .helpers
                    .get(&id)
                    .ok_or_else(|| self.failure(value.span))?;
                if !Arc::ptr_eq(original, template)
                    || arguments.len() != template.parameters.len()
                    || arguments.len() != original_arguments.len()
                {
                    return Err(self.failure(value.span));
                }
                for (original, argument) in original_arguments.iter().zip(arguments) {
                    self.natural_at(owner, original, argument, depth + 1)?;
                }
            }
            (ast::NatKind::Add(a, b), ResolvedNaturalKind::Add(x, y))
            | (ast::NatKind::Sub(a, b), ResolvedNaturalKind::Sub(x, y))
            | (ast::NatKind::Mul(a, b), ResolvedNaturalKind::Mul(x, y)) => {
                self.natural_at(owner, a, x, depth + 1)?;
                self.natural_at(owner, b, y, depth + 1)?;
            }
            _ => return Err(self.failure(value.span)),
        }
        Ok(())
    }
    fn basis_at(
        &self,
        owner: DefId,
        source: &ast::Type,
        ty: &ResolvedType,
        nodes: &mut &[NodeId],
        references: &mut &[ResolvedReference],
        depth: usize,
    ) -> Result<()> {
        self.budget.charge(source.span, 1)?;
        let Some((node, remaining)) = nodes.split_first() else {
            return Err(self.failure(source.span));
        };
        if depth > 64 || *node != self.indices[&owner].node_id_ty(source) {
            return Err(self.failure(source.span));
        }
        *nodes = remaining;
        match (&source.kind, &ty.kind) {
            (ast::TypeKind::Unit, Kind::Unit) | (ast::TypeKind::Bit, Kind::Bit) => {}
            (ast::TypeKind::Bits(n), Kind::Bits(value)) => {
                self.natural_at(owner, n, value, 1)?;
            }
            (ast::TypeKind::Named(name), Kind::Parameter(parameter)) => {
                let Some((reference, remaining)) = references.split_first() else {
                    return Err(self.failure(source.span));
                };
                self.named_reference(owner, reference, name)?;
                self.budget
                    .charge(name.span, name.text.len() + parameter.name.len() + 1)?;
                let key = parameter
                    .key
                    .as_ref()
                    .ok_or_else(|| self.failure(name.span))?;
                if reference.local.as_ref() != Some(key)
                    || parameter.name != name.text
                    || parameter.span != name.span
                    || self.key(owner, key, name.span)? != BindingKind::StaticBasis
                {
                    return Err(self.failure(name.span));
                }
                *references = remaining;
            }
            (ast::TypeKind::Tuple(original), Kind::Tuple(fields)) => {
                if original.len() != fields.len() || fields.len() > 64 {
                    return Err(self.failure(source.span));
                }
                for (source, field) in original.iter().zip(fields) {
                    self.basis_at(owner, source, field, nodes, references, depth + 1)?;
                }
            }
            _ => return Err(self.failure(source.span)),
        }
        Ok(())
    }
    fn operation(&self, owner: DefId, value: &ResolvedStatic) -> Result<()> {
        let node = value.node.ok_or_else(|| self.failure(value.span))?;
        let OriginalNode::Operation(source) =
            self.original(owner, node, NodeKind::StaticOp, value.span)?
        else {
            return Err(self.failure(value.span));
        };
        self.operation_at(owner, source, value, 1)
    }
    fn operation_at(
        &self,
        owner: DefId,
        source: &ast::StaticOp,
        value: &ResolvedStatic,
        depth: usize,
    ) -> Result<()> {
        self.budget.charge(value.span, 1)?;
        if depth > 64
            || value.node != Some(self.indices[&owner].node_id_static_op(source))
            || value.span != source.span
            || (!matches!(source.kind, ast::StaticOpKind::Type(_))
                && (!value.type_nodes.is_empty() || !value.type_references.is_empty()))
        {
            return Err(self.failure(value.span));
        }
        match (&source.kind, &value.kind) {
            (ast::StaticOpKind::Type(source), ResolvedStaticKind::Basis(ty)) => {
                let mut nodes = value.type_nodes.as_slice();
                let mut references = value.type_references.as_slice();
                self.basis_at(owner, source, ty, &mut nodes, &mut references, 1)?;
                if !nodes.is_empty() || !references.is_empty() {
                    return Err(self.failure(value.span));
                }
            }
            (ast::StaticOpKind::Natural(source), ResolvedStaticKind::Natural(value)) => {
                self.natural_at(owner, source, value, 1)?;
            }
            (ast::StaticOpKind::Name(name), ResolvedStaticKind::Name(reference)) => {
                self.named_reference(owner, reference, name)?;
            }
            (
                ast::StaticOpKind::Specialize { name, arguments },
                ResolvedStaticKind::Specialize(reference, args),
            ) => {
                self.named_reference(owner, reference, name)?;
                if arguments.len() != args.len() {
                    return Err(self.failure(value.span));
                }
                for (source, arg) in arguments.iter().zip(args) {
                    self.operation_at(owner, source, arg, depth + 1)?;
                }
            }
            (
                ast::StaticOpKind::Bind {
                    implementation,
                    meaning,
                },
                ResolvedStaticKind::Bind(a, b),
            ) => {
                self.named_reference(owner, a, implementation)?;
                self.named_reference(owner, b, meaning)?;
            }
            (ast::StaticOpKind::Then(a, b), ResolvedStaticKind::Then(x, y))
            | (ast::StaticOpKind::Tensor(a, b), ResolvedStaticKind::Tensor(x, y))
            | (ast::StaticOpKind::Conjugate(a, b), ResolvedStaticKind::Conjugate(x, y)) => {
                self.operation_at(owner, a, x, depth + 1)?;
                self.operation_at(owner, b, y, depth + 1)?;
            }
            (ast::StaticOpKind::Inverse(source), ResolvedStaticKind::Inverse(child))
            | (ast::StaticOpKind::Controlled(source), ResolvedStaticKind::Controlled(child)) => {
                self.operation_at(owner, source, child, depth + 1)?;
            }
            (
                ast::StaticOpKind::Repeat(original_count, original_child),
                ResolvedStaticKind::Repeat {
                    power,
                    count,
                    child,
                },
            ) => {
                if *power != matches!(original_count, ast::Count::Power(_)) {
                    return Err(self.failure(value.span));
                }
                let (ast::Count::Natural(source) | ast::Count::Power(source)) = original_count;
                self.natural_at(owner, source, count, 1)?;
                // A zero count never suppresses association of its original child.
                self.operation_at(owner, original_child, child, depth + 1)?;
            }
            _ => return Err(self.failure(value.span)),
        }
        Ok(())
    }
    fn named_operation(
        &self,
        owner: DefId,
        value: &ResolvedStatic,
        name: &ast::Ident,
    ) -> Result<()> {
        self.budget.charge(value.span, 1)?;
        let ResolvedStaticKind::Name(reference) = &value.kind else {
            return Err(self.failure(value.span));
        };
        if value.node.is_some()
            || value.span != name.span
            || !value.type_nodes.is_empty()
            || !value.type_references.is_empty()
        {
            return Err(self.failure(value.span));
        }
        self.named_reference(owner, reference, name)
    }
    fn call_in_operation(
        &self,
        owner: DefId,
        source: &'ast ast::StaticOp,
        site: UseSiteId,
        depth: usize,
    ) -> Result<Option<&'ast [ast::StaticOp]>> {
        self.budget.charge(source.span, 1)?;
        if depth > 64 {
            return Err(self.failure(source.span));
        }
        let index = &self.indices[&owner];
        match &source.kind {
            ast::StaticOpKind::Name(name) => Ok((index.usage(name) == site).then_some(&[])),
            ast::StaticOpKind::Bind { implementation, .. } => {
                Ok((index.usage(implementation) == site).then_some(&[]))
            }
            ast::StaticOpKind::Specialize { name, arguments } => {
                if index.usage(name) == site {
                    return Ok(Some(arguments));
                }
                for argument in arguments {
                    if let Some(found) = self.call_in_operation(owner, argument, site, depth + 1)? {
                        return Ok(Some(found));
                    }
                }
                Ok(None)
            }
            ast::StaticOpKind::Inverse(child)
            | ast::StaticOpKind::Controlled(child)
            | ast::StaticOpKind::Repeat(_, child) => {
                self.call_in_operation(owner, child, site, depth + 1)
            }
            ast::StaticOpKind::Then(a, b)
            | ast::StaticOpKind::Tensor(a, b)
            | ast::StaticOpKind::Conjugate(a, b) => {
                if let Some(found) = self.call_in_operation(owner, a, site, depth + 1)? {
                    Ok(Some(found))
                } else {
                    self.call_in_operation(owner, b, site, depth + 1)
                }
            }
            ast::StaticOpKind::Type(_) | ast::StaticOpKind::Natural(_) => Ok(None),
        }
    }
    fn call_arguments(
        &self,
        owner: DefId,
        node: NodeId,
        site: UseSiteId,
        span: Span,
    ) -> Result<&'ast [ast::StaticOp]> {
        let source = self.expression(owner, node, span)?;
        let index = &self.indices[&owner];
        let found = match &source.kind {
            ast::ExprKind::Call {
                callee,
                static_args,
                ..
            }
            | ast::ExprKind::AccessCall {
                callee,
                static_args,
                ..
            } => {
                if index.usage(callee) == site {
                    return Ok(static_args);
                }
                let mut found = None;
                for argument in static_args {
                    if let Some(arguments) = self.call_in_operation(owner, argument, site, 1)? {
                        found = Some(arguments);
                        break;
                    }
                }
                found
            }
            ast::ExprKind::ApplyStatic { operation, .. }
            | ast::ExprKind::Adjoint { operation, .. }
            | ast::ExprKind::Controlled { operation, .. } => {
                self.call_in_operation(owner, operation, site, 1)?
            }
            ast::ExprKind::WithComputed { function, .. }
            | ast::ExprKind::RepeatStatic { function, .. } => {
                (index.usage(function) == site).then_some(&[][..])
            }
            ast::ExprKind::CertifiedComputed {
                function, logical, ..
            } => (index.usage(function) == site || index.usage(logical) == site).then_some(&[][..]),
            ast::ExprKind::ApplyContract {
                implementation,
                specification,
                ..
            } => (index.usage(implementation) == site || index.usage(specification) == site)
                .then_some(&[][..]),
            ast::ExprKind::QuantumIf { zero, one, .. } => {
                (index.usage(zero) == site || index.usage(one) == site).then_some(&[][..])
            }
            _ => None,
        };
        found.ok_or_else(|| self.failure(span))
    }
    fn operation_in_tree(
        &self,
        owner: DefId,
        source: &ast::StaticOp,
        wanted: NodeId,
        depth: usize,
    ) -> Result<bool> {
        self.budget.charge(source.span, 1)?;
        if depth > 64 {
            return Err(self.failure(source.span));
        }
        if self.indices[&owner].node_id_static_op(source) == wanted {
            return Ok(true);
        }
        match &source.kind {
            ast::StaticOpKind::Inverse(child)
            | ast::StaticOpKind::Controlled(child)
            | ast::StaticOpKind::Repeat(_, child) => {
                self.operation_in_tree(owner, child, wanted, depth + 1)
            }
            ast::StaticOpKind::Then(a, b)
            | ast::StaticOpKind::Tensor(a, b)
            | ast::StaticOpKind::Conjugate(a, b) => {
                Ok(self.operation_in_tree(owner, a, wanted, depth + 1)?
                    || self.operation_in_tree(owner, b, wanted, depth + 1)?)
            }
            ast::StaticOpKind::Specialize { arguments, .. } => {
                for argument in arguments {
                    if self.operation_in_tree(owner, argument, wanted, depth + 1)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            _ => Ok(false),
        }
    }
    fn operation_in_expression(
        &self,
        owner: DefId,
        node: NodeId,
        value: &ResolvedStatic,
        span: Span,
    ) -> Result<()> {
        let wanted = value.node.ok_or_else(|| self.failure(span))?;
        let source = self.expression(owner, node, span)?;
        let found = match &source.kind {
            ast::ExprKind::Call { static_args, .. }
            | ast::ExprKind::AccessCall { static_args, .. } => {
                let mut found = false;
                for argument in static_args {
                    if self.operation_in_tree(owner, argument, wanted, 1)? {
                        found = true;
                        break;
                    }
                }
                found
            }
            ast::ExprKind::ApplyStatic { operation, .. }
            | ast::ExprKind::Adjoint { operation, .. }
            | ast::ExprKind::Controlled { operation, .. } => {
                self.operation_in_tree(owner, operation, wanted, 1)?
            }
            _ => false,
        };
        if !found {
            return Err(self.failure(span));
        }
        self.operation(owner, value)
    }
    fn local_initializer(
        &self,
        owner: DefId,
        key: &BinderKey,
        value: &ResolvedNatural,
        span: Span,
    ) -> Result<()> {
        let index = &self.indices[&owner];
        // Only borrow existing blocks; do not clone syntax or rebuild names.
        for original in index.original_nodes() {
            self.budget.charge(span, 1)?;
            let OriginalNode::Block(block) = original else {
                continue;
            };
            for statement in &block.statements {
                self.budget.charge(statement.span, 1)?;
                if let ast::StmtKind::StaticLet {
                    name,
                    value: source,
                } = &statement.kind
                {
                    if index.binder(name) == key.id {
                        return self.natural_at(owner, source, value, 1);
                    }
                }
            }
        }
        Err(self.failure(span))
    }
    fn fold_bounds(
        &self,
        owner: DefId,
        key: &BinderKey,
        start: &ResolvedNatural,
        end: &ResolvedNatural,
        span: Span,
    ) -> Result<()> {
        let index = &self.indices[&owner];
        for original in index.original_nodes() {
            self.budget.charge(span, 1)?;
            let OriginalNode::Expression(ast::Expr {
                kind:
                    ast::ExprKind::StaticFold {
                        index: name,
                        start: a,
                        end: b,
                        ..
                    },
                ..
            }) = original
            else {
                continue;
            };
            if index.binder(name) == key.id {
                self.natural_at(owner, a, start, 1)?;
                return self.natural_at(owner, b, end, 1);
            }
        }
        Err(self.failure(span))
    }
    fn linear(&self, owner: DefId, value: &Linear, span: Span) -> Result<()> {
        self.budget.charge(span, 1)?;
        for key in value.terms.keys() {
            if !matches!(
                self.key(owner, key, span)?,
                BindingKind::StaticNatural | BindingKind::FoldIndex
            ) {
                return Err(self.failure(span));
            }
        }
        Ok(())
    }
    fn ty(&self, owner: DefId, ty: &Ty, span: Span) -> Result<()> {
        self.budget.ty(span, ty)?;
        self.budget.charge(span, 1)?;
        let mut pending = vec![ty];
        while let Some(ty) = pending.pop() {
            self.budget.charge(span, 1)?;
            match &ty.kind {
                Kind::Bits(n) => self.linear(owner, n, span)?,
                Kind::Parameter(parameter) => {
                    let key = parameter.key.as_ref().ok_or_else(|| self.failure(span))?;
                    if self.key(owner, key, span)? != BindingKind::StaticBasis {
                        return Err(self.failure(span));
                    }
                }
                Kind::Q(child) => {
                    self.budget.charge(span, 1)?;
                    pending.push(child);
                }
                Kind::Tuple(fields) => {
                    self.budget.charge(span, fields.len())?;
                    pending.extend(fields);
                }
                _ => {}
            }
        }
        Ok(())
    }
    fn contract(&self, owner: DefId, contract: &OperationContract, span: Span) -> Result<()> {
        self.ty(owner, &contract.input, span)?;
        if contract.codomain.is_some() {
            self.ty(owner, contract.output(), span)?;
        }
        if let Some(id) = contract.meaning {
            self.budget.charge(span, 1)?;
            if self
                .interfaces
                .get(&id)
                .is_none_or(|interface| interface.kind != FnKind::Meaning)
            {
                return Err(self.failure(span));
            }
        }
        Ok(())
    }
    fn environment(&self, environment: &StaticEnvironment, node: NodeId, span: Span) -> Result<()> {
        self.environment_kind(environment, node, span, NodeKind::Expr)
    }
    fn environment_kind(
        &self,
        environment: &StaticEnvironment,
        node: NodeId,
        span: Span,
        kind: NodeKind,
    ) -> Result<()> {
        let owner = environment.owner;
        self.budget.charge(span, 1)?;
        self.original(owner, node, kind, span)?;
        if self.resolution.declaration(owner).module != environment.module {
            return Err(self.failure(span));
        }
        let interface = &self.interfaces[&owner];
        for (key, value) in &environment.naturals {
            let kind = self.key(owner, key, span)?;
            if !matches!(kind, BindingKind::StaticNatural | BindingKind::FoldIndex) {
                return Err(self.failure(span));
            }
            self.linear(owner, value, span)?;
            self.budget.charge(span, interface.statics.len())?;
            let formal = interface
                .statics
                .iter()
                .any(|formal| &formal.key == key && matches!(formal.kind, StaticKind::Natural));
            if !formal && !environment.local_naturals.contains_key(key) {
                return Err(self.failure(span));
            }
        }
        for (key, value) in &environment.local_naturals {
            if !environment.naturals.contains_key(key) {
                return Err(self.failure(span));
            }
            match value {
                NaturalBindingPlan::Initializer(value) => {
                    self.budget.charge(span, interface.statics.len())?;
                    if self.key(owner, key, span)? != BindingKind::StaticNatural
                        || interface.statics.iter().any(|formal| &formal.key == key)
                    {
                        return Err(self.failure(span));
                    }
                    self.local_initializer(owner, key, value, span)?;
                }
                NaturalBindingPlan::FoldIndex { start, end } => {
                    if self.key(owner, key, span)? != BindingKind::FoldIndex {
                        return Err(self.failure(span));
                    }
                    self.fold_bounds(owner, key, start, end, span)?;
                }
            }
        }
        for (key, ty) in &environment.bases {
            if self.key(owner, key, span)? != BindingKind::StaticBasis {
                return Err(self.failure(span));
            }
            self.ty(owner, ty, span)?;
        }
        for (key, contract) in &environment.operations {
            if self.key(owner, key, span)? != BindingKind::StaticOperation {
                return Err(self.failure(span));
            }
            self.contract(owner, contract, span)?;
        }
        for alternative in &environment.context.alternatives {
            self.budget.charge(span, 1)?;
            for constraint in alternative {
                self.linear(owner, constraint, span)?;
            }
        }
        let mut original = self.indices[&owner]
            .enclosing_regions(node)
            .ok_or_else(|| self.failure(span))?;
        let mut retained = environment.regions.iter().rev();
        loop {
            // Both chains are borrowed. Charge each step before inspecting a
            // link, including the final exact-length check; allocate no stack.
            self.budget.charge(span, 1)?;
            let ancestor = original
                .next()
                .transpose()
                .map_err(|()| self.failure(span))?;
            match (ancestor, retained.next()) {
                (None, None) => break,
                (
                    Some(OriginalRegion::Predicate {
                        node: original_node,
                        truth: original_truth,
                    }),
                    Some(StaticRegion::Predicate {
                        node,
                        left,
                        comparison,
                        right,
                        truth,
                    }),
                ) => {
                    if *node != original_node || *truth != original_truth {
                        return Err(self.failure(span));
                    }
                    let source = self.expression(owner, *node, span)?;
                    let ast::ExprKind::StaticIf { predicate, .. } = &source.kind else {
                        return Err(self.failure(span));
                    };
                    if *comparison != predicate.comparison {
                        return Err(self.failure(span));
                    }
                    self.natural_at(owner, &predicate.left, left, 1)?;
                    self.natural_at(owner, &predicate.right, right, 1)?;
                }
                (
                    Some(OriginalRegion::Fold {
                        node: original_node,
                    }),
                    Some(StaticRegion::Fold {
                        node,
                        index,
                        start,
                        end,
                    }),
                ) => {
                    if *node != original_node {
                        return Err(self.failure(span));
                    }
                    let source = self.expression(owner, *node, span)?;
                    let ast::ExprKind::StaticFold {
                        index: original_index,
                        start: original_start,
                        end: original_end,
                        ..
                    } = &source.kind
                    else {
                        return Err(self.failure(span));
                    };
                    if self.key(owner, index, span)? != BindingKind::FoldIndex {
                        return Err(self.failure(span));
                    }
                    if self.indices[&owner].binder(original_index) != index.id {
                        return Err(self.failure(span));
                    }
                    let Some(NaturalBindingPlan::FoldIndex {
                        start: retained_start,
                        end: retained_end,
                    }) = environment.local_naturals.get(index)
                    else {
                        return Err(self.failure(span));
                    };
                    if !Arc::ptr_eq(start, retained_start) || !Arc::ptr_eq(end, retained_end) {
                        return Err(self.failure(span));
                    }
                    self.natural_at(owner, original_start, start, 1)?;
                    self.natural_at(owner, original_end, end, 1)?;
                }
                _ => return Err(self.failure(span)),
            }
        }
        Ok(())
    }
}

pub(super) fn validate_and_finish(
    program: &mut Program<'_>,
    effects: &BTreeMap<DefId, FunctionEffect>,
) -> Result<()> {
    let validation = Validation {
        indices: &program.indices,
        helpers: &program.helpers,
        interfaces: &program.interfaces,
        resolution: &program.resolution,
        budget: &program.budget,
    };
    validation.body_statics(&program.body_statics)?;
    for (site, plan) in &mut program.static_calls {
        let span = validation
            .original(plan.owner, plan.node, NodeKind::Expr, Span::default())?
            .span();
        validation.node(
            plan.owner,
            plan.node,
            crate::frontend::resolve::locals::NodeKind::Expr,
            span,
        )?;
        validation.reference(plan.owner, &plan.callee, span)?;
        if *site != plan.callee.site
            || plan.callee.target != ResolvedUse::Global(resolve::Target::Declaration(plan.target))
            || plan.module != validation.resolution.declaration(plan.owner).module
            || plan.environment.owner != plan.owner
            || plan.environment.module != plan.module
        {
            return Err(validation.failure(span));
        }
        let interface = &validation.interfaces[&plan.target];
        let original_arguments =
            validation.call_arguments(plan.owner, plan.node, plan.callee.site, span)?;
        if interface.statics.len() != plan.arguments.len()
            || interface.params.len() != plan.parameters.len()
            || original_arguments.len() != plan.arguments.len()
        {
            return Err(validation.failure(span));
        }
        for ((actual, formal), original) in plan
            .arguments
            .iter()
            .zip(&interface.statics)
            .zip(original_arguments)
        {
            validation
                .budget
                .charge(span, 1 + actual.formal.name.len() + formal.key.name.len())?;
            let category = match formal.kind {
                StaticKind::Basis => StaticCategory::Basis,
                StaticKind::Natural => StaticCategory::Natural,
                StaticKind::Operation { .. } => StaticCategory::Operation,
            };
            if actual.formal != formal.key || actual.category != category {
                return Err(validation.failure(span));
            }
            validation.operation_at(plan.owner, original, &actual.value, 1)?;
            let closure = actual.value.classify_budgeted(
                &plan.environment,
                &BTreeSet::new(),
                &mut |at, cells| validation.budget.charge(at, cells),
            )?;
            if let PlanClosure::Deferred(keys) = closure {
                for key in keys {
                    validation.budget.charge(span, 1 + key.name.len())?;
                    if !plan.environment.naturals.contains_key(&key)
                        && !plan.environment.bases.contains_key(&key)
                        && !plan.environment.operations.contains_key(&key)
                    {
                        return Err(validation.failure(span));
                    }
                }
            }
        }
        validation.environment(&plan.environment, plan.node, span)?;
        for parameter in &plan.parameters {
            validation.ty(plan.owner, parameter, span)?;
        }
        validation.ty(plan.owner, &plan.result, span)?;
        if plan.source_effect.is_some() {
            return Err(validation.failure(span));
        }
        plan.source_effect = Some(
            effect_at(
                validation.resolution,
                effects,
                EffectContext::Module(plan.module),
                plan.target,
            )
            .ok_or_else(|| validation.failure(span))?,
        );
    }
    for (ordinal, obligation) in program.obligations.iter().enumerate() {
        let owner = obligation.definition;
        let span = obligation.span;
        let plan = &obligation.plan;
        if obligation.id
            != (ObligationId {
                definition: owner,
                ordinal,
            })
            || plan.environment.owner != owner
        {
            return Err(validation.failure(span));
        }
        validation.node(
            owner,
            plan.node,
            crate::frontend::resolve::locals::NodeKind::Expr,
            span,
        )?;
        validation.environment(&plan.environment, plan.node, span)?;
        validation.runtime_owners(
            owner,
            plan.node,
            &obligation.kind,
            &plan.runtime_owners,
            span,
        )?;
        match (&obligation.kind, &plan.subject) {
            (
                ObligationKind::Provider { provider, .. }
                | ObligationKind::RuntimeGroupProvider { provider },
                EvidenceSubject::Call { site, requested },
            ) => {
                let call = program
                    .static_calls
                    .get(site)
                    .ok_or_else(|| validation.failure(span))?;
                if call.owner != owner
                    || call.node != plan.node
                    || call.target != *provider
                    || !call.access[crate::frontend::formals::access_index(*requested)]
                    || (matches!(obligation.kind, ObligationKind::Provider { .. })
                        && *requested != ast::Access::Apply)
                {
                    return Err(validation.failure(span));
                }
            }
            (
                ObligationKind::MeaningEquality {
                    required: original_required,
                    supplied,
                },
                EvidenceSubject::Operation {
                    operation,
                    required: Some(required),
                    actual: Some(actual),
                },
            ) => {
                if required.meaning != Some(*original_required) || actual.meaning != *supplied {
                    return Err(validation.failure(span));
                }
                if actual.effect > required.effect
                    || required
                        .access
                        .iter()
                        .zip(actual.access)
                        .any(|(needed, available)| *needed && !available)
                {
                    return Err(validation.failure(span));
                }
                validation.operation_in_expression(owner, plan.node, operation, span)?;
                validation.contract(owner, required, span)?;
                validation.contract(owner, actual, span)?;
            }
            (
                ObligationKind::CertifiedClean { .. },
                EvidenceSubject::Operation {
                    operation,
                    required,
                    actual,
                },
            ) => {
                let source = validation.expression(owner, plan.node, span)?;
                let ast::ExprKind::CertifiedComputed { logical, .. } = &source.kind else {
                    return Err(validation.failure(span));
                };
                validation.named_operation(owner, operation, logical)?;
                for contract in required.iter().chain(actual.as_deref()) {
                    validation.contract(owner, contract, span)?;
                }
            }
            (
                ObligationKind::FunctionEquality {
                    implementation,
                    specification,
                },
                EvidenceSubject::FunctionPair {
                    implementation: actual,
                    specification: expected,
                },
            ) => {
                let source = validation.expression(owner, plan.node, span)?;
                let ast::ExprKind::ApplyContract {
                    implementation: original_actual,
                    specification: original_expected,
                    ..
                } = &source.kind
                else {
                    return Err(validation.failure(span));
                };
                validation.named_reference(owner, actual, original_actual)?;
                validation.named_reference(owner, expected, original_expected)?;
                if actual.target
                    != ResolvedUse::Global(resolve::Target::Declaration(*implementation))
                    || expected.target
                        != ResolvedUse::Global(resolve::Target::Declaration(*specification))
                {
                    return Err(validation.failure(span));
                }
            }
            (
                ObligationKind::ControlSectors
                | ObligationKind::Injectivity
                | ObligationKind::ProtectedClean
                | ObligationKind::TransformedMeaning,
                EvidenceSubject::Expression,
            ) => {}
            _ => return Err(validation.failure(span)),
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests;
