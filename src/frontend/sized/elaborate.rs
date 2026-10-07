//! Untrusted concrete, source-order ownership proposal. No verified IR is made.
use super::ast::{self, *};
use super::primitive::{Primitive, Size, TypeRule, TypeShape, dependent_output};
use super::{BasisBinding, Error, Instantiation, ParsedProgram, Result, Span};
use std::collections::{BTreeMap, BTreeSet};

const MAX_CALLS: usize = 1_024;
const MAX_FOLDS: usize = 1_024;
const MAX_DEPTH: usize = 16;
const MAX_STEPS: usize = 10_000;
const MAX_CELLS: usize = 100_000;

use crate::frontend::resolve::{DefId, Target};
use crate::frontend::types::Kind as TypeKind;
use std::sync::Arc;

/// Concrete exact source tree. Unit/Bit/Bits kind tags are shared by ordinary and
/// quantum leaves; `is_quantum` retains their distinct ownership category.
/// Its private shared representation makes Q explicit; no constructor is public.
pub type SourceType = crate::frontend::types::Type<u32>;
impl SourceType {
    fn value_cells(&self) -> usize {
        self.cells() + 1 + self.fields().iter().map(Self::value_cells).sum::<usize>()
    }
    pub fn kind(&self) -> &'static str {
        match &self.kind {
            TypeKind::Q(basis) => match basis.kind {
                TypeKind::Unit => "unit",
                TypeKind::Bit => "bit",
                TypeKind::Bits(_) => "bits",
                TypeKind::Tuple(_) => "tuple",
                TypeKind::Q(_) => unreachable!("nested Q is not a basis"),
                TypeKind::Parameter(_) => "unresolved",
            },
            TypeKind::Bit => "bit",
            TypeKind::Bits(_) => "bits",
            TypeKind::Tuple(_) => "tuple",
            TypeKind::Unit => "unit",
            TypeKind::Parameter(_) => "unresolved",
        }
    }
    pub fn width(&self) -> Option<u32> {
        match &self.kind {
            TypeKind::Bit => Some(1),
            TypeKind::Bits(n) => Some(*n),
            TypeKind::Q(basis) => basis.basis_width(),
            TypeKind::Tuple(_) => None,
            TypeKind::Unit => Some(0),
            TypeKind::Parameter(_) => None,
        }
    }
    pub fn fields(&self) -> &[SourceType] {
        self.tuple_fields().unwrap_or(&[])
    }
    pub fn is_quantum(&self) -> bool {
        self.is_quantum_owner()
    }
    fn quantum_width(&self) -> usize {
        if self.is_quantum() {
            self.width().unwrap() as usize
        } else {
            self.fields().iter().map(Self::quantum_width).sum()
        }
    }
    fn cells(&self) -> usize {
        self.owner_shape_size()
            .nodes
            .max(self.storage_size(4096, 64).map_or(4097, |size| size.nodes))
    }
}
fn bit() -> SourceType {
    SourceType::quantum(SourceType::bit())
}
fn tuple(fields: Vec<SourceType>) -> SourceType {
    SourceType::tuple(fields)
}

/// Quantum owner or copyable classical value in one definition's local namespace.
/// Tuples retain ordered fields and do not introduce a further owner identity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceValue {
    ty: SourceType,
    identity: Option<u32>,
    fields: Vec<SourceValue>,
}
impl SourceValue {
    fn cells(&self) -> usize {
        self.ty.cells() + 1 + self.fields.iter().map(Self::cells).sum::<usize>()
    }
    pub fn ty(&self) -> &SourceType {
        &self.ty
    }
    pub fn identity(&self) -> Option<u32> {
        self.identity
    }
    pub fn fields(&self) -> &[SourceValue] {
        &self.fields
    }
    fn unit() -> Self {
        Self {
            ty: SourceType::unit(),
            identity: None,
            fields: Vec::new(),
        }
    }
    fn tuple(fields: Vec<Self>) -> Self {
        Self {
            ty: tuple(fields.iter().map(|v| v.ty.clone()).collect()),
            identity: None,
            fields,
        }
    }
}

/// A shared transparent provider, optionally wrapped in retained repetitions.
#[derive(Clone, Debug)]
pub struct SourceOperation {
    kind: OperationKind,
    pub(super) meanings: Arc<[ExplicitMeaning]>,
    module: String,
    span: Span,
    repetitions: u32,
}
#[derive(Clone, Debug)]
pub(super) struct ExplicitMeaning {
    pub id: DefId,
    pub span: Span,
    pub module: String,
}
#[derive(Clone, Debug)]
enum OperationKind {
    Definition(usize),
    Repeat(u32, Box<SourceOperation>),
}
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum OperationKey {
    Definition(usize),
    Repeat(u32, Box<OperationKey>),
    Requested(Vec<DefId>, Box<OperationKey>),
}
impl SourceOperation {
    pub fn definition(&self) -> Option<usize> {
        match self.kind {
            OperationKind::Definition(id) => Some(id),
            _ => None,
        }
    }
    pub fn repeat_count(&self) -> Option<u32> {
        match self.kind {
            OperationKind::Repeat(n, _) => Some(n),
            _ => None,
        }
    }
    pub fn child(&self) -> Option<&Self> {
        match &self.kind {
            OperationKind::Repeat(_, child) => Some(child),
            _ => None,
        }
    }
    pub fn module(&self) -> &str {
        &self.module
    }
    pub fn span(&self) -> Span {
        self.span
    }
    fn target(&self) -> usize {
        match &self.kind {
            OperationKind::Definition(id) => *id,
            OperationKind::Repeat(_, child) => child.target(),
        }
    }
    pub(super) fn key(&self) -> OperationKey {
        let action = match &self.kind {
            OperationKind::Definition(id) => OperationKey::Definition(*id),
            OperationKind::Repeat(n, child) => OperationKey::Repeat(*n, Box::new(child.key())),
        };
        if self.meanings.is_empty() {
            action
        } else {
            OperationKey::Requested(
                self.meanings.iter().map(|m| m.id).collect(),
                Box::new(action),
            )
        }
    }
    fn has_meanings(&self) -> bool {
        !self.meanings.is_empty() || self.child().is_some_and(Self::has_meanings)
    }
}

/// One ordered source operation. Names are exact primitive identities or step
/// categories; call/provider references always select retained actual definitions.
#[derive(Clone, Debug)]
pub struct SourceStep {
    module: String,
    span: Span,
    kind: StepKind,
    inputs: Vec<SourceValue>,
    output: SourceValue,
    effect: Effect,
}
#[derive(Clone, Debug)]
enum StepKind {
    Boolean(Boolean),
    Primitive(Primitive, Vec<u32>),
    Call {
        definition: usize,
        operations: BTreeMap<String, SourceOperation>,
    },
    Apply(SourceOperation),
    Adjoint(SourceOperation),
    Controlled(SourceOperation),
}
impl SourceStep {
    pub fn kind(&self) -> &'static str {
        match self.kind {
            StepKind::Boolean(_) => "boolean",
            StepKind::Primitive(..) => "primitive",
            StepKind::Call { .. } => "call",
            StepKind::Apply(_) => "apply",
            StepKind::Adjoint(_) => "adjoint",
            StepKind::Controlled(_) => "controlled",
        }
    }
    pub fn primitive(&self) -> Option<&str> {
        match &self.kind {
            StepKind::Primitive(name, _) => Some(name.signature().path),
            _ => None,
        }
    }
    pub(super) fn boolean(&self) -> Option<Boolean> {
        match self.kind {
            StepKind::Boolean(operation) => Some(operation),
            _ => None,
        }
    }
    /// Ordinary Boolean source operation, without exposing internal SSA IDs.
    pub fn boolean_operator(&self) -> Option<&'static str> {
        self.boolean().map(Boolean::operator)
    }
    /// Source literal value, present only for a Boolean constant step.
    pub fn boolean_literal(&self) -> Option<bool> {
        match self.boolean() {
            Some(Boolean::Constant(value)) => Some(value),
            _ => None,
        }
    }
    pub(super) fn primitive_kind(&self) -> Option<Primitive> {
        match self.kind {
            StepKind::Primitive(name, _) => Some(name),
            _ => None,
        }
    }
    pub fn natural_arguments(&self) -> &[u32] {
        match &self.kind {
            StepKind::Primitive(_, ns) => ns,
            _ => &[],
        }
    }
    pub fn called_definition(&self) -> Option<usize> {
        match self.kind {
            StepKind::Call { definition, .. } => Some(definition),
            _ => None,
        }
    }
    pub fn operation(&self) -> Option<&SourceOperation> {
        match &self.kind {
            StepKind::Apply(op) | StepKind::Adjoint(op) | StepKind::Controlled(op) => Some(op),
            _ => None,
        }
    }
    pub fn operation_bindings(&self) -> Option<&BTreeMap<String, SourceOperation>> {
        match &self.kind {
            StepKind::Call { operations, .. } => Some(operations),
            _ => None,
        }
    }
    pub fn inputs(&self) -> &[SourceValue] {
        &self.inputs
    }
    pub fn output(&self) -> &SourceValue {
        &self.output
    }
    pub fn module(&self) -> &str {
        &self.module
    }
    pub fn span(&self) -> Span {
        self.span
    }
    pub fn effect(&self) -> &'static str {
        effect_name(self.effect)
    }
}

/// One specialized source function, with a sequential body and local identities.
#[derive(Clone, Debug)]
pub struct SourceDefinition {
    pub(super) original: DefId,
    path: String,
    types: BTreeMap<String, BasisBinding>,
    naturals: BTreeMap<String, u32>,
    operations: BTreeMap<String, SourceOperation>,
    inputs: Vec<SourceValue>,
    output: SourceValue,
    steps: Vec<SourceStep>,
    effect: Effect,
    span: Span,
    peak_quantum: usize,
}
impl SourceDefinition {
    pub fn path(&self) -> &str {
        &self.path
    }
    pub fn naturals(&self) -> &BTreeMap<String, u32> {
        &self.naturals
    }
    pub fn types(&self) -> &BTreeMap<String, BasisBinding> {
        &self.types
    }
    pub fn operations(&self) -> &BTreeMap<String, SourceOperation> {
        &self.operations
    }
    pub fn inputs(&self) -> &[SourceValue] {
        &self.inputs
    }
    pub fn output(&self) -> &SourceValue {
        &self.output
    }
    pub fn steps(&self) -> &[SourceStep] {
        &self.steps
    }
    pub fn effect(&self) -> &'static str {
        effect_name(self.effect)
    }
    pub fn span(&self) -> Span {
        self.span
    }
    /// Diagnostic peak for this bounded source-order proposal, not a proved
    /// runtime/resource-safety certificate.
    pub fn peak_quantum_width(&self) -> usize {
        self.peak_quantum
    }
}

/// Opaque concrete source proposal. Neither this type nor its inspection views
/// authorizes execution or claims a source-preservation theorem.
#[derive(Clone, Debug)]
pub struct ElaboratedProgram {
    instance: Instantiation,
    definitions: Arc<[SourceDefinition]>,
    root: usize,
    calls: usize,
    folds: usize,
}

/// Preflight admission to the hierarchical transport profile, not acceptance
/// evidence or a promise that body lowering and native checking will succeed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HierarchyEligibility {
    Eligible,
    /// An explicit root signature, effect or ordinary Boolean-step mismatch.
    Ineligible(Error),
}

impl ElaboratedProgram {
    /// Whether any retained actual specialization has an original Meaning
    /// obligation, including unused operation bindings.
    pub fn has_operation_meanings(&self) -> bool {
        self.definitions.iter().any(|definition| {
            definition
                .operations
                .values()
                .any(SourceOperation::has_meanings)
                || definition
                    .steps
                    .iter()
                    .filter_map(SourceStep::operation)
                    .any(SourceOperation::has_meanings)
                || self
                    .instance
                    .program
                    .checked
                    .interface(definition.original)
                    .statics
                    .iter()
                    .any(|formal| {
                        matches!(
                            formal.kind,
                            crate::frontend::check::StaticKind::Operation {
                                meaning: Some(_),
                                ..
                            }
                        )
                    })
        })
    }
    pub(super) fn require_unrefined(&self) -> Result<()> {
        if self.has_operation_meanings() {
            return Err(error(
                "meaning",
                self.definitions[self.root].span,
                "original operation Meanings require checking every binding before hierarchy lowering; Raw lowering is unsupported",
            ));
        }
        Ok(())
    }
    /// Check every original Meaning against its actual closed provider, using
    /// fresh native finite equations and one aggregate exact-work budget.
    pub fn check_operation_meanings<'a>(
        &'a self,
        kernel: &crate::interchange::native::Kernel,
        budget: &mut crate::contract::exact::Budget,
    ) -> Result<super::CheckedSourceMeanings<'a>> {
        super::raw::check_operation_meanings(self, kernel, budget)
    }
    /// Classify explicit hierarchical profile mismatches without treating other
    /// failures as a reason to select another target. Any checking error is
    /// returned separately; eligible bodies still require full lowering checks.
    pub fn hierarchy_eligibility(&self) -> Result<HierarchyEligibility> {
        super::lower::hierarchy_eligibility(self)
    }
    /// Preflight the root signature and declared effect against the selected
    /// hierarchical transport profile, including ordinary Boolean steps.
    /// Generic source checking is separate;
    /// `lower` performs body and operation-specific capability checks before
    /// generating a proposal. This preflight issues no acceptance evidence.
    pub fn check_lowering_profile(&self) -> Result<()> {
        super::lower::check_profile(self)
    }
    /// Check the root profile, body and operation capabilities, then produce
    /// bounded untrusted hierarchical transport. This performs no native
    /// acceptance and retains this source-order program for preservation checks.
    pub fn lower(&self) -> Result<super::HierarchyProposal> {
        super::lower::lower(self)
    }
    /// Produce a bounded Raw proposal from this retained specialization.
    /// This performs no native acceptance or source-preservation proof.
    pub fn lower_raw(&self) -> Result<super::RawSourceProposal> {
        super::raw::lower(self)
    }
    /// Propose the actual closed definition bound to an entry operation.
    /// Keep the original caller instance and an explicit leaf subject. This
    /// neither accepts the caller nor automatically checks every binding.
    pub fn lower_raw_operation(&self, name: &str) -> Result<super::RawSourceProposal> {
        self.lower_raw_operation_at(self.root, name)
    }
    /// Select an original binding in any retained instantiated definition.
    /// Repetition is part of the subject, never replaced by its base provider.
    /// This is preparation only, not mandatory generic Meaning enforcement.
    pub fn lower_raw_operation_at(
        &self,
        caller: usize,
        name: &str,
    ) -> Result<super::RawSourceProposal> {
        super::raw::lower_operation(self, caller, name)
    }
    pub fn instantiation(&self) -> &Instantiation {
        &self.instance
    }
    pub fn definitions(&self) -> &[SourceDefinition] {
        &self.definitions
    }
    pub fn root(&self) -> usize {
        self.root
    }
    pub fn call_instances(&self) -> usize {
        self.calls
    }
    pub fn fold_iterations(&self) -> usize {
        self.folds
    }
}
fn effect_name(effect: Effect) -> &'static str {
    match effect {
        Effect::Unitary => "unitary",
        Effect::Iso => "iso",
        Effect::Observe => "observe",
    }
}
fn error(code: &'static str, span: Span, message: impl Into<String>) -> Error {
    Error::new(code, span, message)
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Key {
    definition: DefId,
    types: BTreeMap<String, String>,
    naturals: BTreeMap<String, u32>,
    operations: BTreeMap<String, OperationKey>,
}
struct Builder<'a> {
    program: &'a ParsedProgram,
    definitions: Vec<SourceDefinition>,
    cache: BTreeMap<Key, usize>,
    active: BTreeSet<Key>,
    calls: usize,
    folds: usize,
    steps: usize,
    cells: usize,
    active_frames: usize,
}
#[derive(Clone)]
struct Binding {
    identity: usize,
    value: SourceValue,
}
#[derive(Clone)]
struct Scope {
    naturals: BTreeMap<BinderKey, u32>,
    bases: BTreeMap<BinderKey, SourceType>,
    operations: BTreeMap<BinderKey, SourceOperation>,
    values: BTreeMap<BinderKey, Binding>,
    moved: BTreeSet<usize>,
}
type ClosedArguments = (
    BTreeMap<String, BasisBinding>,
    BTreeMap<String, u32>,
    BTreeMap<String, SourceOperation>,
);
struct Frame {
    module: String,
    lexical: Arc<Table>,
    effect: Effect,
    steps: Vec<SourceStep>,
    next_value: u32,
    next_binding: usize,
    live_quantum: BTreeMap<u32, usize>,
    peak: usize,
}

pub(super) fn elaborate(instance: &Instantiation) -> Result<ElaboratedProgram> {
    let mut builder = Builder {
        program: &instance.program,
        definitions: Vec::new(),
        cache: BTreeMap::new(),
        active: BTreeSet::new(),
        calls: 0,
        folds: 0,
        steps: 0,
        cells: 0,
        active_frames: 0,
    };
    let mut operations = BTreeMap::new();
    // Eager validation prevents an unused entry operation from concealing an
    // invalid concrete source body, even if no executable step invokes it.
    for (name, binding) in &instance.operations {
        let id = builder.function(
            instance.operation_ids[name],
            binding.types.clone(),
            binding.naturals.clone(),
            BTreeMap::new(),
            0,
        )?;
        builder.provider_type(id, Span::default())?;
        operations.insert(
            name.clone(),
            SourceOperation {
                kind: OperationKind::Definition(id),
                meanings: Arc::from([]),
                module: instance
                    .program
                    .checked
                    .resolution
                    .declaration(instance.entry_id)
                    .name
                    .0
                    .clone(),
                span: Span::default(),
                repetitions: 1,
            },
        );
    }
    let root = builder.function(
        instance.entry_id,
        instance.types.clone(),
        instance.naturals.clone(),
        operations,
        0,
    )?;
    Ok(ElaboratedProgram {
        instance: instance.clone(),
        definitions: builder.definitions.into(),
        root,
        calls: builder.calls,
        folds: builder.folds,
    })
}

fn natural(
    n: &Natural,
    values: &BTreeMap<BinderKey, u32>,
    cells: &mut usize,
    calls: &mut usize,
) -> Result<u32> {
    charge_retained_cells(cells, 1, n.span)?;
    let fail = || {
        error(
            "limit",
            n.span,
            "concrete natural arithmetic exceeds u32 or has negative subtraction",
        )
    };
    match &n.kind {
        NatKind::Helper {
            template,
            arguments,
        } => {
            *calls = calls
                .checked_add(1)
                .ok_or_else(|| error("limit", n.span, "static helper call accounting overflow"))?;
            if *calls > MAX_CALLS {
                return Err(error(
                    "limit",
                    n.span,
                    "concrete source exceeds 1024 combined runtime and Nat helper calls",
                ));
            }
            let mut actual = BTreeMap::new();
            for (key, argument) in template.parameters.iter().zip(arguments) {
                let value = natural(argument, values, cells, calls)?;
                charge_retained_cells(cells, 2 + key.name.len(), n.span)?;
                actual.insert(key, value);
            }
            let mut result = template.result.constant;
            for (key, coefficient) in &template.result.terms {
                charge_retained_cells(cells, 1, n.span)?;
                let value = actual.get(key).ok_or_else(|| {
                    error("static", n.span, "missing original Nat helper binding")
                })?;
                let scaled = coefficient
                    .checked_mul(i128::from(*value))
                    .ok_or_else(fail)?;
                result = result.checked_add(scaled).ok_or_else(fail)?;
            }
            u32::try_from(result).map_err(|_| fail())
        }
        NatKind::Number(n) => u32::try_from(*n).map_err(|_| fail()),
        NatKind::Name(name) => name
            .get(values)
            .copied()
            .ok_or_else(|| error("static", n.span, format!("missing concrete natural {name}"))),
        NatKind::Add(a, b) => natural(a, values, cells, calls)?
            .checked_add(natural(b, values, cells, calls)?)
            .ok_or_else(fail),
        NatKind::Sub(a, b) => natural(a, values, cells, calls)?
            .checked_sub(natural(b, values, cells, calls)?)
            .ok_or_else(fail),
        NatKind::Mul(a, b) => natural(a, values, cells, calls)?
            .checked_mul(natural(b, values, cells, calls)?)
            .ok_or_else(fail),
    }
}

fn predicate(
    p: &Predicate,
    values: &BTreeMap<BinderKey, u32>,
    cells: &mut usize,
    calls: &mut usize,
) -> Result<bool> {
    let a = natural(&p.left, values, cells, calls)?;
    let b = natural(&p.right, values, cells, calls)?;
    Ok(match p.comparison {
        Compare::Eq => a == b,
        Compare::Ne => a != b,
        Compare::Lt => a < b,
        Compare::Le => a <= b,
        Compare::Gt => a > b,
        Compare::Ge => a >= b,
    })
}
fn concrete_type(
    t: &ast::Type,
    values: &BTreeMap<BinderKey, u32>,
    bases: &BTreeMap<BinderKey, SourceType>,
    span: Span,
    cells: &mut usize,
    calls: &mut usize,
) -> Result<SourceType> {
    t.storage_size(4096, 64).ok_or_else(|| {
        error(
            "limit",
            span,
            "concrete type exceeds 4096 cells or depth 64",
        )
    })?;
    // Resolve opaque bases before allocation and check the expanded exact tree.
    // Each referenced binding is already bounded, but repeated substitutions
    // must also respect the aggregate shape and quantum width limits.
    let mut expanded_nodes = 0usize;
    let mut pending = vec![(t, 1usize)];
    while let Some((node, depth)) = pending.pop() {
        match &node.kind {
            TypeKind::Parameter(parameter) => {
                let replacement = parameter
                    .key
                    .as_ref()
                    .and_then(|key| bases.get(key))
                    .ok_or_else(|| {
                        error("static", parameter.span, "missing concrete Basis binding")
                    })?;
                let size = replacement.storage_size(4096, 64).ok_or_else(|| {
                    error("limit", span, "concrete Basis exceeds storage capacity")
                })?;
                expanded_nodes = expanded_nodes.saturating_add(size.nodes);
                if depth.saturating_add(size.depth).saturating_sub(1) > 64 {
                    return Err(error("limit", span, "substituted Basis exceeds depth 64"));
                }
            }
            TypeKind::Q(child) => pending.push((child, depth)),
            TypeKind::Tuple(fields) => {
                expanded_nodes = expanded_nodes.saturating_add(1);
                pending.extend(fields.iter().rev().map(|child| (child, depth + 1)));
            }
            _ => expanded_nodes = expanded_nodes.saturating_add(1),
        }
        if expanded_nodes > 4096 {
            return Err(error(
                "limit",
                span,
                "substituted Basis exceeds 4096 type nodes",
            ));
        }
    }
    let mut sizes = Vec::new();
    let mut pending = vec![t];
    while let Some(node) = pending.pop() {
        match &node.kind {
            TypeKind::Bits(n) => {
                let value = natural(n, values, cells, calls)?;
                if value > 8 {
                    return Err(error(
                        "limit",
                        span,
                        "concrete register/classical sequence exceeds eight bits",
                    ));
                }
                sizes.push(value);
            }
            TypeKind::Q(basis) => pending.push(basis),
            TypeKind::Tuple(fields) => pending.extend(fields.iter().rev()),
            _ => {}
        }
    }
    // Width sums are checked on borrowed symbolic trees before allocating the
    // concrete representation. Each ordinary tuple remains a value product.
    fn widths(
        t: &ast::Type,
        sizes: &mut impl Iterator<Item = u32>,
        bases: &BTreeMap<BinderKey, SourceType>,
        span: Span,
    ) -> Result<u32> {
        match &t.kind {
            TypeKind::Unit => Ok(0),
            TypeKind::Bit => Ok(1),
            TypeKind::Bits(_) => Ok(sizes.next().expect("one resolved size per occurrence")),
            TypeKind::Parameter(parameter) => parameter
                .key
                .as_ref()
                .and_then(|key| bases.get(key))
                .and_then(SourceType::basis_width)
                .ok_or_else(|| error("static", parameter.span, "missing closed ordinary Basis")),
            TypeKind::Tuple(fields) => fields.iter().try_fold(0u32, |n, field| {
                n.checked_add(widths(field, sizes, bases, span)?)
                    .ok_or_else(|| error("limit", span, "concrete basis width overflow"))
            }),
            TypeKind::Q(basis) => {
                let width = widths(basis, sizes, bases, span)?;
                if width > 8 {
                    return Err(error(
                        "limit",
                        span,
                        "concrete quantum owner exceeds eight bits",
                    ));
                }
                Ok(0)
            }
        }
    }
    widths(t, &mut sizes.iter().copied(), bases, span)?;
    let mut sizes = sizes.into_iter();
    let closed = t.map_parts(
        &mut |_| Ok::<_, Error>(sizes.next().expect("resolved source size")),
        &mut |parameter| {
            parameter
                .key
                .as_ref()
                .and_then(|key| bases.get(key))
                .cloned()
                .ok_or_else(|| error("static", parameter.span, "missing concrete Basis"))
        },
    )?;
    concrete_capacity(&closed, span)?;
    Ok(closed)
}
pub(super) fn concrete_capacity(ty: &SourceType, span: Span) -> Result<()> {
    ty.storage_size(4096, 64).ok_or_else(|| {
        error(
            "limit",
            span,
            "concrete type exceeds 4096 cells or depth 64",
        )
    })?;
    let mut pending = vec![(ty, false)];
    while let Some((node, in_basis)) = pending.pop() {
        match &node.kind {
            TypeKind::Q(basis) => {
                if basis.basis_width().is_none_or(|width| width > 8) {
                    return Err(error(
                        "limit",
                        span,
                        "concrete quantum owner exceeds eight bits",
                    ));
                }
                pending.push((basis, true));
            }
            TypeKind::Bits(n) if *n > 8 => {
                return Err(error(
                    "limit",
                    span,
                    "concrete register/classical sequence exceeds eight bits",
                ));
            }
            TypeKind::Tuple(fields) => {
                if in_basis && fields.len() < 2 {
                    return Err(error(
                        "unsupported",
                        span,
                        "concrete quantum Basis tuples require at least two fields",
                    ));
                }
                pending.extend(fields.iter().map(|field| (field, in_basis)));
            }
            TypeKind::Parameter(parameter) => {
                return Err(error(
                    "static",
                    parameter.span,
                    "unresolved Basis in concrete type",
                ));
            }
            _ => {}
        }
    }
    Ok(())
}
fn expected(value: &SourceValue, ty: &SourceType, span: Span) -> Result<()> {
    if &value.ty == ty {
        Ok(())
    } else {
        Err(error(
            "type",
            span,
            "concrete type/size or tuple shape mismatch",
        ))
    }
}

fn charge_retained_cells(cells: &mut usize, n: usize, span: Span) -> Result<()> {
    *cells = cells
        .checked_add(n)
        .ok_or_else(|| error("limit", span, "source value accounting overflow"))?;
    if *cells > MAX_CELLS {
        return Err(error(
            "limit",
            span,
            "source proposal exceeds 100000 retained value cells",
        ));
    }
    Ok(())
}

impl Builder<'_> {
    fn enter(&mut self, span: Span) -> Result<()> {
        if self.active_frames >= 64 {
            return Err(error(
                "limit",
                span,
                "combined concrete traversal depth exceeds 64",
            ));
        }
        self.active_frames += 1;
        Ok(())
    }
    fn charge_cells(&mut self, n: usize, span: Span) -> Result<()> {
        charge_retained_cells(&mut self.cells, n, span)
    }
    fn declaration(&self, id: DefId) -> Result<(String, Arc<Function>)> {
        let (module, function) = self.program.definition(id)?;
        Ok((module.into(), Arc::clone(function)))
    }
    fn function(
        &mut self,
        definition: DefId,
        types: BTreeMap<String, BasisBinding>,
        naturals: BTreeMap<String, u32>,
        operations: BTreeMap<String, SourceOperation>,
        depth: usize,
    ) -> Result<usize> {
        self.enter(Span::default())?;
        let result = self.function_inner(definition, types, naturals, operations, depth);
        self.active_frames -= 1;
        result
    }
    fn function_inner(
        &mut self,
        definition: DefId,
        types: BTreeMap<String, BasisBinding>,
        naturals: BTreeMap<String, u32>,
        operations: BTreeMap<String, SourceOperation>,
        depth: usize,
    ) -> Result<usize> {
        self.calls = self
            .calls
            .checked_add(1)
            .ok_or_else(|| error("limit", Span::default(), "call accounting overflow"))?;
        if self.calls > MAX_CALLS || depth > MAX_DEPTH {
            return Err(error(
                "limit",
                Span::default(),
                "concrete source exceeds 1024 calls or depth 16",
            ));
        }
        let type_cells = types.values().try_fold(0usize, |total, basis| {
            let size = basis.ty.storage_size(4096, 64).ok_or_else(|| {
                error(
                    "limit",
                    Span::default(),
                    "closed Basis exceeds type storage capacity",
                )
            })?;
            total
                .checked_add(size.nodes)
                .ok_or_else(|| error("limit", Span::default(), "type binding accounting overflow"))
        })?;
        // Include keys, retained definition substitutions and lexical scope
        // copies in the existing aggregate budget, even for unused parameters.
        self.charge_cells(type_cells.saturating_mul(4), Span::default())?;
        let key = Key {
            definition,
            types: types
                .iter()
                .map(|(name, ty)| (name.clone(), ty.key()))
                .collect(),
            naturals: naturals.clone(),
            operations: operations
                .iter()
                .map(|(name, op)| (name.clone(), op.key()))
                .collect(),
        };
        if let Some(id) = self.cache.get(&key) {
            return Ok(*id);
        }
        if !self.active.insert(key.clone()) {
            return Err(error(
                "cycle",
                Span::default(),
                "concrete source recursion does not decrease",
            ));
        }
        let (module, function) = self.declaration(definition)?;
        let path = self.program.checked.resolution.path(definition);
        let result = (|| {
            let interface = self.program.checked.interface(definition);
            let expected_operations: BTreeSet<_> = interface
                .statics
                .iter()
                .filter_map(|formal| {
                    matches!(
                        formal.kind,
                        crate::frontend::check::StaticKind::Operation { .. }
                    )
                    .then_some(&formal.key.name)
                })
                .collect();
            if operations.keys().collect::<BTreeSet<_>>() != expected_operations {
                return Err(error(
                    "static",
                    function.span,
                    "concrete operation bindings do not match declaration",
                ));
            }
            let program = self.program;
            let closed = super::bindings::closed_interface_budgeted(
                program,
                definition,
                &types,
                &naturals,
                &format!("function {path}"),
                function.span,
                |span, cells| self.charge_cells(cells, span),
            )?;
            let resolved_naturals = closed.naturals;
            let resolved_bases = closed.bases;
            for (key, required) in &closed.operations {
                let target_type =
                    self.provider_type(operations[&key.name].target(), function.span)?;
                if &target_type != required {
                    return Err(error(
                        "type",
                        function.span,
                        "concrete provider width/type mismatch",
                    ));
                }
                self.charge_cells(interface.statics.len(), function.span)?;
                let formal = interface
                    .statics
                    .iter()
                    .find(|formal| formal.key == *key)
                    .expect("closed operation retains original formal");
                if let crate::frontend::check::StaticKind::Operation {
                    meaning: Some(id), ..
                } = &formal.kind
                {
                    let target = &program.meaning_targets[id];
                    self.charge_cells(target.cells(), function.span)?;
                    if target_type.quantum_basis() != Some(&target.basis) {
                        return Err(error(
                            "type",
                            function.span,
                            "provider and original Meaning have different exact basis trees",
                        ));
                    }
                }
            }
            let mut frame = Frame {
                module: module.clone(),
                lexical: Arc::clone(&function.lexical),
                effect: function.effect,
                steps: Vec::new(),
                next_value: 0,
                next_binding: 0,
                live_quantum: BTreeMap::new(),
                peak: 0,
            };
            let mut scope = Scope {
                naturals: resolved_naturals,
                bases: resolved_bases,
                operations: interface
                    .statics
                    .iter()
                    .filter(|formal| {
                        matches!(
                            formal.kind,
                            crate::frontend::check::StaticKind::Operation { .. }
                        )
                    })
                    .map(|formal| (formal.key.clone(), operations[&formal.key.name].clone()))
                    .collect(),
                values: BTreeMap::new(),
                moved: BTreeSet::new(),
            };
            let mut inputs = Vec::new();
            assert_eq!(
                function.arguments.len(),
                closed.parameters.len(),
                "post-judgment projection retains every original parameter"
            );
            for ((pattern, span), ty) in function.arguments.iter().zip(&closed.parameters) {
                let value = frame.fresh(ty, *span)?;
                // Destructuring binds the value's fields, but the declared
                // argument and its exact input interface remain whole.
                bind(pattern, value.clone(), &mut scope, &mut frame)?;
                inputs.push(value);
            }
            self.charge_cells(inputs.iter().map(SourceValue::cells).sum(), function.span)?;
            let output = self.block(&function.body, &mut scope, &mut frame, depth)?;
            expected(&output, &closed.result, function.body.span)?;
            if scope.values.values().any(|b| b.value.ty.linear()) {
                return Err(error(
                    "ownership",
                    function.body.span,
                    "concrete function leaves live quantum bindings",
                ));
            }
            let output_owners = quantum_ids(&output);
            if frame.live_quantum.keys().copied().collect::<BTreeSet<_>>() != output_owners {
                return Err(error(
                    "ownership",
                    function.body.span,
                    "concrete function output does not contain every live owner",
                ));
            }
            self.charge_cells(output.cells(), function.span)?;
            let definition = SourceDefinition {
                original: definition,
                path,
                types,
                naturals,
                operations,
                inputs,
                output,
                steps: frame.steps,
                effect: function.effect,
                span: function.span,
                peak_quantum: frame.peak,
            };
            let id = self.definitions.len();
            self.definitions.push(definition);
            self.cache.insert(key.clone(), id);
            Ok(id)
        })();
        self.active.remove(&key);
        result.map_err(|e| e.in_module(&module))
    }
    fn provider_type(&self, id: usize, span: Span) -> Result<SourceType> {
        let definition = &self.definitions[id];
        if definition.effect != Effect::Unitary
            || definition.inputs.len() != 1
            || !definition.inputs[0].ty.is_quantum_owner()
            || definition.inputs[0].ty != definition.output.ty
        {
            return Err(error(
                "type",
                span,
                "provider must be unitary and preserve one exact quantum input owner",
            ));
        }
        Ok(definition.output.ty.clone())
    }
    fn runtime_provider_type(&mut self, id: usize, span: Span) -> Result<SourceType> {
        fn preflight(ty: &SourceType, cells: &mut usize, span: Span) -> Result<(usize, usize)> {
            let before = *cells;
            let size = crate::frontend::check::type_size_budgeted(
                ty,
                4096,
                64,
                false,
                span,
                &mut |span, n| {
                    charge_retained_cells(cells, n, span)
                        .map_err(crate::frontend::check::SourceError::from)
                },
            )
            .map_err(Error::from)?;
            // This charged work includes every original node, including Q,
            // and stack entries; it bounds later comparison and copy work.
            Ok((size.nodes, *cells - before))
        }
        let definition = &self.definitions[id];
        let cells = &mut self.cells;
        let (output_nodes, output_work) = preflight(&definition.output.ty, cells, span)?;
        for input in &definition.inputs {
            let (_, input_work) = preflight(&input.ty, cells, span)?;
            charge_retained_cells(cells, input_work, span)?;
        }
        let mut charge = |span, n| charge_retained_cells(cells, n, span);
        // Preflight above charges stack entries and visits before allocation.
        // Compare borrowed types; no aggregate type or packed owner is made.
        charge(span, output_work + 1)?;
        let preserves_group = match definition.inputs.as_slice() {
            [input] => input.ty == definition.output.ty,
            inputs if !inputs.is_empty() => match &definition.output.ty.kind {
                TypeKind::Tuple(fields) if fields.len() == inputs.len() => inputs
                    .iter()
                    .zip(fields)
                    .all(|(input, field)| &input.ty == field),
                _ => false,
            },
            _ => false,
        };
        charge(span, output_nodes)?;
        let mut pending = Vec::with_capacity(output_nodes);
        pending.push(&definition.output.ty);
        let mut quantum_group = true;
        while let Some(ty) = pending.pop() {
            charge(span, 1)?;
            match &ty.kind {
                TypeKind::Q(_) => {}
                TypeKind::Tuple(fields) if !fields.is_empty() => pending.extend(fields),
                _ => {
                    quantum_group = false;
                    break;
                }
            }
        }
        if definition.effect != Effect::Unitary || !preserves_group || !quantum_group {
            return Err(error(
                "type",
                span,
                "provider must be unitary and preserve its complete quantum input group",
            ));
        }
        charge(span, output_work)?;
        Ok(definition.output.ty.clone())
    }
    fn resolve(
        &self,
        name: &Reference,
        _scope: &Scope,
        frame: &Frame,
        span: Span,
    ) -> Result<Target> {
        match name.target(&frame.lexical) {
            ResolvedUse::Local(_) => Err(error(
                "name",
                span,
                "concrete function name is lexically shadowed",
            )),
            ResolvedUse::Global(target) => Ok(target),
            ResolvedUse::Unresolved => Err(error("name", span, "unresolved concrete function")),
        }
    }
    fn arguments(
        &mut self,
        definition: DefId,
        arguments: &[Argument],
        scope: &Scope,
        frame: &Frame,
        depth: usize,
        span: Span,
    ) -> Result<ClosedArguments> {
        self.enter(span)?;
        let result = self.arguments_inner(definition, arguments, scope, frame, depth, span);
        self.active_frames -= 1;
        result
    }
    fn arguments_inner(
        &mut self,
        definition: DefId,
        arguments: &[Argument],
        scope: &Scope,
        frame: &Frame,
        depth: usize,
        span: Span,
    ) -> Result<ClosedArguments> {
        let interface = self.program.checked.interface(definition);
        if arguments.len() != interface.statics.len() {
            return Err(error(
                "static",
                span,
                "concrete static argument arity mismatch",
            ));
        }
        let mut naturals = BTreeMap::new();
        let mut types = BTreeMap::new();
        let mut operations = BTreeMap::new();
        for (formal, a) in interface.statics.iter().zip(arguments) {
            let name = &formal.key.name;
            match &formal.kind {
                crate::frontend::check::StaticKind::Basis => {
                    let ty = match a {
                        Argument::Basis(basis, at) => concrete_type(
                            basis,
                            &scope.naturals,
                            &scope.bases,
                            *at,
                            &mut self.cells,
                            &mut self.calls,
                        )?,
                        Argument::Natural(Natural {
                            kind: NatKind::Name(reference),
                            ..
                        }) => reference.get(&scope.bases).cloned().ok_or_else(|| {
                            error("static", span, "expected a concrete Basis argument")
                        })?,
                        _ => {
                            return Err(error(
                                "static",
                                span,
                                "expected a concrete Basis argument",
                            ));
                        }
                    };
                    types.insert(name.clone(), BasisBinding::checked(ty, span)?);
                }
                crate::frontend::check::StaticKind::Natural => {
                    let Argument::Natural(n) = a else {
                        return Err(error("static", span, "expected concrete natural"));
                    };
                    naturals.insert(
                        name.clone(),
                        natural(n, &scope.naturals, &mut self.cells, &mut self.calls)?,
                    );
                }
                crate::frontend::check::StaticKind::Operation { .. } => {
                    operations.insert(name.clone(), self.operation(a, scope, frame, depth, span)?);
                }
            }
        }
        Ok((types, naturals, operations))
    }
    fn operation(
        &mut self,
        argument: &Argument,
        scope: &Scope,
        frame: &Frame,
        depth: usize,
        span: Span,
    ) -> Result<SourceOperation> {
        self.enter(span)?;
        let result = self.operation_inner(argument, scope, frame, depth, span);
        self.active_frames -= 1;
        result
    }
    fn operation_inner(
        &mut self,
        argument: &Argument,
        scope: &Scope,
        frame: &Frame,
        depth: usize,
        span: Span,
    ) -> Result<SourceOperation> {
        match argument {
            Argument::Natural(Natural {
                kind: NatKind::Name(name),
                ..
            }) if name.get(&scope.operations).is_some() => {
                Ok(name.get(&scope.operations).unwrap().clone())
            }
            Argument::Natural(Natural {
                kind: NatKind::Name(name),
                span,
                ..
            }) => self.provider(name, &[], scope, frame, depth, *span),
            Argument::Definition(name, arguments, span) => {
                self.provider(name, arguments, scope, frame, depth, *span)
            }
            Argument::Checked(implementation, meaning, span) => {
                let argument = Argument::Natural(Natural {
                    kind: NatKind::Name(implementation.clone()),
                    span: *span,
                });
                let mut operation = self.operation(&argument, scope, frame, depth, *span)?;
                let Target::Declaration(id) = self.resolve(meaning, scope, frame, *span)? else {
                    return Err(error(
                        "meaning",
                        *span,
                        "checked_op requires an original Meaning declaration",
                    ));
                };
                let target = self.program.meaning_targets.get(&id).ok_or_else(|| {
                    error(
                        "meaning",
                        *span,
                        "checked_op requires an original finite Meaning",
                    )
                })?;
                if self
                    .provider_type(operation.target(), *span)?
                    .quantum_basis()
                    != Some(&target.basis)
                {
                    return Err(error(
                        "type",
                        *span,
                        "checked_op provider and Meaning have different exact basis trees",
                    ));
                }
                self.charge_cells(
                    target.cells() + operation.meanings.len() + frame.module.len() + 1,
                    *span,
                )?;
                let mut meanings = operation.meanings.to_vec();
                meanings.push(ExplicitMeaning {
                    id,
                    span: *span,
                    module: frame.module.clone(),
                });
                operation.meanings = meanings.into();
                Ok(operation)
            }
            Argument::Repeat(count, child, span) => {
                let child = self.operation(child, scope, frame, depth, *span)?;
                let count = match count {
                    Count::Natural(n) => {
                        natural(n, &scope.naturals, &mut self.cells, &mut self.calls)?
                    }
                    Count::Power(n) => {
                        let e = natural(n, &scope.naturals, &mut self.cells, &mut self.calls)?;
                        if e > 8 {
                            return Err(error("limit", *span, "repeat exponent exceeds eight"));
                        }
                        1u32 << e
                    }
                };
                let repetitions = count
                    .checked_mul(child.repetitions)
                    .ok_or_else(|| error("limit", *span, "repeat multiplicity overflow"))?;
                if count > 256 || repetitions > 256 {
                    return Err(error("limit", *span, "repeat count/product exceeds 256"));
                }
                Ok(SourceOperation {
                    kind: OperationKind::Repeat(count, Box::new(child)),
                    meanings: Arc::from([]),
                    module: frame.module.clone(),
                    span: *span,
                    repetitions,
                })
            }
            _ => Err(error(
                "static",
                span,
                "expected concrete operation provider",
            )),
        }
    }
    fn provider(
        &mut self,
        name: &Reference,
        arguments: &[Argument],
        scope: &Scope,
        frame: &Frame,
        depth: usize,
        span: Span,
    ) -> Result<SourceOperation> {
        self.enter(span)?;
        let result = self.provider_inner(name, arguments, scope, frame, depth, span);
        self.active_frames -= 1;
        result
    }
    fn provider_inner(
        &mut self,
        name: &Reference,
        arguments: &[Argument],
        scope: &Scope,
        frame: &Frame,
        depth: usize,
        span: Span,
    ) -> Result<SourceOperation> {
        let Target::Declaration(definition) = self.resolve(name, scope, frame, span)? else {
            return Err(error(
                "unsupported",
                span,
                "primitive operation references are outside this preparation profile",
            ));
        };
        let (types, naturals, operations) =
            self.arguments(definition, arguments, scope, frame, depth, span)?;
        let id = self.function(definition, types, naturals, operations, depth + 1)?;
        self.runtime_provider_type(id, span)?;
        Ok(SourceOperation {
            kind: OperationKind::Definition(id),
            meanings: Arc::from([]),
            module: frame.module.clone(),
            span,
            repetitions: 1,
        })
    }
    fn block(
        &mut self,
        block: &Block,
        scope: &mut Scope,
        frame: &mut Frame,
        depth: usize,
    ) -> Result<SourceValue> {
        self.enter(block.span)?;
        let result = self.block_inner(block, scope, frame, depth);
        self.active_frames -= 1;
        result
    }
    fn block_inner(
        &mut self,
        block: &Block,
        scope: &mut Scope,
        frame: &mut Frame,
        depth: usize,
    ) -> Result<SourceValue> {
        let initial = scope.values.clone();
        let initial_ids: BTreeSet<_> = initial.values().map(|b| b.identity).collect();
        let mut local_naturals = Vec::new();
        for statement in &block.statements {
            match statement {
                Statement::StaticLet(name, value) => {
                    self.charge_cells(4 + 2 * name.name.len(), value.span)?;
                    let value = natural(value, &scope.naturals, &mut self.cells, &mut self.calls)?;
                    let key = name.key.clone();
                    scope.naturals.insert(key.clone(), value);
                    local_naturals.push(key);
                }
                Statement::Let(pattern, expr) => {
                    let value = self.expr(expr, scope, frame, depth)?;
                    bind(pattern, value, scope, frame)?;
                }
                Statement::Drop(expr) => {
                    if self.expr(expr, scope, frame, depth)?.ty.linear() {
                        return Err(error(
                            "ownership",
                            expr.span,
                            "concrete expression discards quantum owner",
                        ));
                    }
                }
            }
        }
        let result = self.expr(&block.result, scope, frame, depth)?;
        for key in local_naturals {
            scope.naturals.remove(&key);
        }
        if scope
            .values
            .values()
            .any(|b| !initial_ids.contains(&b.identity) && b.value.ty.linear())
        {
            return Err(error(
                "ownership",
                block.span,
                "concrete local quantum owner escapes its lexical block",
            ));
        }
        scope.values = initial
            .into_iter()
            .filter(|(_, b)| !scope.moved.contains(&b.identity))
            .collect();
        Ok(result)
    }
    fn expr(
        &mut self,
        expr: &Expr,
        scope: &mut Scope,
        frame: &mut Frame,
        depth: usize,
    ) -> Result<SourceValue> {
        self.enter(expr.span)?;
        let result = self.expr_inner(expr, scope, frame, depth);
        self.active_frames -= 1;
        result
    }
    fn expr_inner(
        &mut self,
        expr: &Expr,
        scope: &mut Scope,
        frame: &mut Frame,
        depth: usize,
    ) -> Result<SourceValue> {
        let span = expr.span;
        match &expr.kind {
            ExprKind::Unit => Ok(SourceValue::unit()),
            ExprKind::Boolean(operation, operands) => {
                use crate::frontend::ordinary::{self, OperandFailure};
                let values = ordinary::evaluate(
                    *operation,
                    operands.iter(),
                    &mut (&mut *self, &mut *scope, &mut *frame),
                    |(builder, scope, frame), operand| builder.expr(operand, scope, frame, depth),
                    |value| value.ty.clone(),
                    |_, failure| match failure {
                        OperandFailure::Arity { expected, actual } => error(
                            "type",
                            span,
                            format!(
                                "Boolean operation requires {expected} operands, found {actual}"
                            ),
                        ),
                        OperandFailure::Type(ty) => error(
                            "type",
                            span,
                            format!(
                                "{} requires ordinary Bit operands, found {:?}",
                                operation.operator(),
                                ty.sized_debug()
                            ),
                        ),
                    },
                )?;
                self.step(
                    StepKind::Boolean(*operation),
                    vec![SourceType::bit(); operation.arity()],
                    operation.result_type(),
                    Effect::Unitary,
                    values,
                    frame,
                    span,
                    0,
                )
            }
            ExprKind::Name(name) => {
                let b = name.get(&scope.values).cloned().ok_or_else(|| {
                    error(
                        "ownership",
                        span,
                        "concrete binding is unavailable or moved",
                    )
                })?;
                if b.value.ty.linear() {
                    scope
                        .values
                        .remove(name.local.as_ref().expect("resolved runtime binding"));
                    scope.moved.insert(b.identity);
                }
                Ok(b.value)
            }
            ExprKind::Tuple(fields) => {
                let mut values = Vec::new();
                let mut cells = 2usize;
                for field in fields {
                    let value = self.expr(field, scope, frame, depth)?;
                    cells = cells
                        .saturating_add(value.cells())
                        .saturating_add(value.ty.cells());
                    if cells > 4096 {
                        return Err(error(
                            "limit",
                            span,
                            "inferred concrete value exceeds 4096 cells",
                        ));
                    }
                    values.push(value);
                }
                Ok(SourceValue::tuple(values))
            }
            ExprKind::Call(name, arguments, inputs) => {
                if let Some(op) = name.get(&scope.operations).cloned() {
                    let values = inputs
                        .iter()
                        .map(|e| self.expr(e, scope, frame, depth))
                        .collect::<Result<_>>()?;
                    return self.operation_step(StepKind::Apply(op), values, frame, span);
                }
                let target = self.resolve(name, scope, frame, span)?;
                if let Target::Primitive(_) = target {
                    let path = self.program.checked.resolution.target_path(target);
                    let kind = Primitive::lookup(&path).ok_or_else(|| {
                        error(
                            "unsupported",
                            span,
                            format!("selected concrete preparation does not support {path}"),
                        )
                    })?;
                    let signature = kind.signature();
                    // These contracts reject arity before evaluating the sole
                    // argument; its complete work is then retained exactly once.
                    if signature.types.dependent()
                        || matches!(kind, Primitive::Unit | Primitive::Finish)
                    {
                        if arguments.len() != signature.natural_arity {
                            return Err(error(
                                "static",
                                span,
                                "concrete primitive natural arity mismatch",
                            ));
                        }
                        if inputs.len() != signature.types.runtime_arity() {
                            return Err(error("type", span, "concrete operation arity mismatch"));
                        }
                    }
                    let naturals = arguments
                        .iter()
                        .map(|a| {
                            let Argument::Natural(n) = a else {
                                return Err(error(
                                    "static",
                                    span,
                                    "primitive requires natural arguments",
                                ));
                            };
                            natural(n, &scope.naturals, &mut self.cells, &mut self.calls)
                        })
                        .collect::<Result<Vec<_>>>()?;
                    let values: Vec<SourceValue> = inputs
                        .iter()
                        .map(|e| self.expr(e, scope, frame, depth))
                        .collect::<Result<_>>()?;
                    let (types, output, effect) = primitive(
                        kind,
                        &naturals,
                        &values.iter().map(|value| &value.ty).collect::<Vec<_>>(),
                        span,
                    )?;
                    self.step(
                        StepKind::Primitive(kind, naturals),
                        types,
                        output,
                        effect,
                        values,
                        frame,
                        span,
                        0,
                    )
                } else {
                    let Target::Declaration(definition) = target else {
                        unreachable!("primitive handled above")
                    };
                    let (types, naturals, operations) =
                        self.arguments(definition, arguments, scope, frame, depth, span)?;
                    let id =
                        self.function(definition, types, naturals, operations.clone(), depth + 1)?;
                    let definition = &self.definitions[id];
                    let types = definition.inputs.iter().map(|v| v.ty.clone()).collect();
                    let output = definition.output.ty.clone();
                    let effect = definition.effect;
                    let peak = definition.peak_quantum;
                    let values = inputs
                        .iter()
                        .map(|e| self.expr(e, scope, frame, depth))
                        .collect::<Result<_>>()?;
                    self.step(
                        StepKind::Call {
                            definition: id,
                            operations,
                        },
                        types,
                        output,
                        effect,
                        values,
                        frame,
                        span,
                        peak,
                    )
                }
            }
            ExprKind::Apply(argument, input) => {
                let op = self.operation(argument, scope, frame, depth, span)?;
                let value = self.expr(input, scope, frame, depth)?;
                self.operation_step(StepKind::Apply(op), vec![value], frame, span)
            }
            ExprKind::Adjoint(argument, input) => {
                let op = self.operation(argument, scope, frame, depth, span)?;
                let value = self.expr(input, scope, frame, depth)?;
                self.operation_step(StepKind::Adjoint(op), vec![value], frame, span)
            }
            ExprKind::Controlled(argument, inputs) => {
                let op = self.operation(argument, scope, frame, depth, span)?;
                let values = inputs
                    .iter()
                    .map(|e| self.expr(e, scope, frame, depth))
                    .collect::<Result<_>>()?;
                self.operation_step(StepKind::Controlled(op), values, frame, span)
            }
            ExprKind::If(condition, yes, no) => {
                let branch =
                    if predicate(condition, &scope.naturals, &mut self.cells, &mut self.calls)? {
                        yes
                    } else {
                        no
                    };
                self.block(branch, scope, frame, depth)
            }
            ExprKind::Fold {
                index,
                start,
                end,
                carry,
                initial,
                body,
            } => {
                let start = natural(start, &scope.naturals, &mut self.cells, &mut self.calls)?;
                let end = natural(end, &scope.naturals, &mut self.cells, &mut self.calls)?;
                let count = end
                    .checked_sub(start)
                    .ok_or_else(|| error("size", span, "negative concrete fold range"))?;
                self.folds = self
                    .folds
                    .checked_add(count as usize)
                    .ok_or_else(|| error("limit", span, "fold accounting overflow"))?;
                if self.folds > MAX_FOLDS {
                    return Err(error(
                        "limit",
                        span,
                        "concrete source exceeds 1024 aggregate fold iterations",
                    ));
                }
                let mut value = self.expr(initial, scope, frame, depth)?;
                let carry_type = value.ty.clone();
                for index_value in start..end {
                    let mut inner = scope.clone();
                    inner.values.retain(|_, b| !b.value.ty.linear());
                    inner.naturals.insert(index.key().clone(), index_value);
                    bind(carry, value, &mut inner, frame)?;
                    value = self.block(body, &mut inner, frame, depth)?;
                    expected(&value, &carry_type, body.span)?;
                    if inner.values.values().any(|b| b.value.ty.linear()) {
                        return Err(error(
                            "ownership",
                            body.span,
                            "concrete fold leaves carry owner live",
                        ));
                    }
                }
                Ok(value)
            }
        }
    }
    fn operation_step(
        &mut self,
        kind: StepKind,
        inputs: Vec<SourceValue>,
        frame: &mut Frame,
        span: Span,
    ) -> Result<SourceValue> {
        let (op, controlled) = match &kind {
            StepKind::Apply(op) | StepKind::Adjoint(op) => (op, false),
            StepKind::Controlled(op) => (op, true),
            _ => unreachable!(),
        };
        let target = self.runtime_provider_type(op.target(), span)?;
        let (types, output) = if controlled {
            (vec![bit(), target.clone()], tuple(vec![bit(), target]))
        } else {
            (vec![target.clone()], target)
        };
        let peak = self.definitions[op.target()].peak_quantum + usize::from(controlled);
        self.step(
            kind,
            types,
            output,
            Effect::Unitary,
            inputs,
            frame,
            span,
            peak,
        )
    }
    #[allow(clippy::too_many_arguments)]
    fn step(
        &mut self,
        kind: StepKind,
        types: Vec<SourceType>,
        output_type: SourceType,
        effect: Effect,
        inputs: Vec<SourceValue>,
        frame: &mut Frame,
        span: Span,
        child_peak: usize,
    ) -> Result<SourceValue> {
        if effect > frame.effect {
            return Err(error(
                "effect",
                span,
                "concrete operation exceeds declared effect",
            ));
        }
        if inputs.len() != types.len() {
            return Err(error("type", span, "concrete operation arity mismatch"));
        }
        for (v, ty) in inputs.iter().zip(types) {
            expected(v, &ty, span)?;
        }
        let before: usize = frame.live_quantum.values().sum();
        let input_width: usize = inputs.iter().map(|v| v.ty.quantum_width()).sum();
        if child_peak > 0 {
            frame.observe_width(
                before
                    .checked_sub(input_width)
                    .and_then(|n| n.checked_add(child_peak))
                    .ok_or_else(|| error("limit", span, "concrete width accounting overflow"))?,
                span,
            )?;
        }
        let mut consumed = BTreeSet::new();
        for input in &inputs {
            for id in quantum_ids(input) {
                if !consumed.insert(id) || frame.live_quantum.remove(&id).is_none() {
                    return Err(error(
                        "ownership",
                        span,
                        "concrete source step aliases or consumes an unavailable owner",
                    ));
                }
            }
        }
        self.steps = self
            .steps
            .checked_add(1)
            .ok_or_else(|| error("limit", span, "source step count overflow"))?;
        if self.steps > MAX_STEPS {
            return Err(error(
                "limit",
                span,
                "source proposal exceeds 10000 ordered steps",
            ));
        }
        self.charge_cells(
            inputs
                .iter()
                .map(SourceValue::cells)
                .sum::<usize>()
                .checked_add(output_type.value_cells())
                .ok_or_else(|| error("limit", span, "value cell accounting overflow"))?,
            span,
        )?;
        let output = frame.fresh(&output_type, span)?;
        frame.steps.push(SourceStep {
            module: frame.module.clone(),
            span,
            kind,
            inputs,
            output: output.clone(),
            effect,
        });
        Ok(output)
    }
}
impl Frame {
    fn observe_width(&mut self, width: usize, span: Span) -> Result<()> {
        if width > 16 {
            return Err(error(
                "limit",
                span,
                "concrete source exceeds 16 live quantum wires",
            ));
        }
        self.peak = self.peak.max(width);
        Ok(())
    }
    fn fresh(&mut self, ty: &SourceType, span: Span) -> Result<SourceValue> {
        concrete_capacity(ty, span)?;
        if ty.value_cells() > 4096 {
            return Err(error("limit", span, "concrete value exceeds 4096 cells"));
        }
        if matches!(ty.kind, TypeKind::Unit) {
            return Ok(SourceValue::unit());
        }
        if let TypeKind::Tuple(fields) = &ty.kind {
            return Ok(SourceValue::tuple(
                fields
                    .iter()
                    .map(|t| self.fresh(t, span))
                    .collect::<Result<_>>()?,
            ));
        }
        let identity = self.next_value;
        self.next_value = identity
            .checked_add(1)
            .ok_or_else(|| error("limit", span, "source value identity exhausted"))?;
        if ty.is_quantum() {
            self.live_quantum.insert(identity, ty.quantum_width());
            self.observe_width(self.live_quantum.values().sum(), span)?;
        }
        Ok(SourceValue {
            ty: ty.clone(),
            identity: Some(identity),
            fields: Vec::new(),
        })
    }
}
fn quantum_ids(value: &SourceValue) -> BTreeSet<u32> {
    if value.ty.is_quantum() {
        BTreeSet::from([value.identity.unwrap()])
    } else {
        value.fields.iter().flat_map(quantum_ids).collect()
    }
}
fn bind_name(
    name: &BindingName,
    value: SourceValue,
    span: Span,
    scope: &mut Scope,
    frame: &mut Frame,
) -> Result<()> {
    let retained: usize = scope
        .values
        .iter()
        .filter(|(key, _)| name.shadowed.as_ref() != Some(*key))
        .map(|(_, b)| b.value.cells())
        .sum();
    if retained.saturating_add(value.cells()) > 16_384 {
        return Err(error(
            "limit",
            span,
            "concrete scope exceeds 16384 retained value cells",
        ));
    }
    if name.shadowed.as_ref().is_some_and(|key| {
        scope.naturals.contains_key(key)
            || scope.operations.contains_key(key)
            || scope.values.get(key).is_some_and(|b| b.value.ty.linear())
    }) {
        return Err(error(
            "ownership",
            span,
            "concrete binding shadows a static name or live quantum owner",
        ));
    }
    let identity = frame.next_binding;
    frame.next_binding = identity
        .checked_add(1)
        .ok_or_else(|| error("limit", span, "binding identity exhausted"))?;
    if let Some(previous) = &name.shadowed {
        scope.values.remove(previous);
    }
    scope
        .values
        .insert(name.key().clone(), Binding { identity, value });
    Ok(())
}
fn bind(pattern: &Pattern, value: SourceValue, scope: &mut Scope, frame: &mut Frame) -> Result<()> {
    match pattern {
        Pattern::Wildcard(span) => {
            if value.ty.linear() {
                return Err(error(
                    "ownership",
                    *span,
                    "wildcard would discard quantum ownership",
                ));
            }
            Ok(())
        }
        Pattern::Name(name, span) => bind_name(name, value, *span, scope, frame),
        Pattern::Tuple(patterns, span) => {
            if value.ty.pattern_fields(patterns.len()).is_none()
                || patterns.len() != value.fields.len()
            {
                return Err(error(
                    "type",
                    *span,
                    "concrete pattern does not preserve tuple shape",
                ));
            }
            for (p, v) in patterns.iter().zip(value.fields) {
                bind(p, v, scope, frame)?;
            }
            Ok(())
        }
    }
}
fn primitive(
    kind: Primitive,
    ns: &[u32],
    inputs: &[&SourceType],
    span: Span,
) -> Result<(Vec<SourceType>, SourceType, Effect)> {
    let signature = kind.signature();
    if ns.len() != signature.natural_arity {
        return Err(error(
            "static",
            span,
            "concrete primitive natural arity mismatch",
        ));
    }
    if matches!(signature.guard, super::primitive::Guard::RegisterIndex) && ns[1] >= ns[0] {
        return Err(error("size", span, "concrete register requires k < n <= 8"));
    }
    let (inputs, output) = match signature.types {
        TypeRule::Fixed(inputs, output) => (inputs, output),
        rule @ (TypeRule::QuantumEndomorphism | TypeRule::Split | TypeRule::Join) => {
            // Reject an oversized joined owner before cloning its basis tree.
            if matches!(rule, TypeRule::Join) && inputs.len() == 2 {
                if let (Some(a), Some(b)) = (inputs[0].quantum_basis(), inputs[1].quantum_basis()) {
                    if a.basis_width()
                        .and_then(|a| b.basis_width().and_then(|b| a.checked_add(b)))
                        .is_none_or(|width| width > 8)
                    {
                        return Err(error(
                            "limit",
                            span,
                            "concrete joined owner exceeds eight bits",
                        ));
                    }
                }
            }
            let output = dependent_output(rule, inputs, span)?;
            concrete_capacity(&output, span)?;
            return Ok((
                inputs.iter().map(|ty| (**ty).clone()).collect(),
                output,
                signature.effect,
            ));
        }
    };
    // These are concrete preparation capacities, not generic source premises.
    match kind {
        Primitive::Phase | Primitive::ControlledPhase => {
            if ns[1] > 8 || ns[0] >= (1u32 << ns[1]) {
                return Err(error(
                    "limit",
                    span,
                    "dyadic phase requires k <= 8 and j < 2^k",
                ));
            }
        }
        Primitive::TakeBit | Primitive::PutBit => {
            if ns[0] > 8 || ns[1] >= ns[0] {
                return Err(error("size", span, "concrete register requires k < n <= 8"));
            }
        }
        Primitive::PrependBit => {
            if ns[0] >= 8 {
                return Err(error("limit", span, "classical pack exceeds eight bits"));
            }
        }
        Primitive::Unit
        | Primitive::Split
        | Primitive::Join
        | Primitive::Finish
        | Primitive::H
        | Primitive::X
        | Primitive::Z
        | Primitive::PhaseEighth
        | Primitive::Cnot
        | Primitive::Init0
        | Primitive::MeasureZ
        | Primitive::Empty
        | Primitive::ConsumeEmpty
        | Primitive::EmptyBits => {}
    }
    fn size(size: Size, ns: &[u32], span: Span) -> Result<u32> {
        match size {
            Size::Constant(n) => Ok(n),
            Size::Argument(index, offset) => ns[index]
                .checked_add_signed(i32::from(offset))
                .ok_or_else(|| error("limit", span, "concrete primitive register size overflow")),
        }
    }
    fn shape(t: TypeShape, ns: &[u32], span: Span) -> Result<SourceType> {
        Ok(SourceType {
            kind: match t {
                TypeShape::Unit => TypeKind::Unit,
                TypeShape::QUnit => TypeKind::Q(Box::new(SourceType::unit())),
                TypeShape::Bit => TypeKind::Q(Box::new(SourceType::bit())),
                TypeShape::CBit => TypeKind::Bit,
                TypeShape::Bits(n) => TypeKind::Q(Box::new(SourceType::bits(size(n, ns, span)?))),
                TypeShape::CBits(n) => TypeKind::Bits(size(n, ns, span)?),
                TypeShape::Tuple(fields) => TypeKind::Tuple(
                    fields
                        .iter()
                        .map(|t| shape(*t, ns, span))
                        .collect::<Result<_>>()?,
                ),
            },
        })
    }
    Ok((
        inputs
            .iter()
            .map(|t| shape(*t, ns, span))
            .collect::<Result<_>>()?,
        shape(output, ns, span)?,
        signature.effect,
    ))
}

#[cfg(test)]
mod natural_budget_tests {
    use super::*;
    #[test]
    fn helper_calls_and_natural_visits_share_existing_aggregate_budgets() {
        let span = Span::new(31, 42);
        let helper = Natural {
            span,
            kind: NatKind::Helper {
                template: Arc::new(crate::frontend::check::StaticHelper {
                    parameters: vec![],
                    result: crate::frontend::check::Linear::constant(1),
                    requirements: vec![],
                }),
                arguments: vec![],
            },
        };
        let mut cells = 0;
        let mut calls = MAX_CALLS;
        let error = natural(&helper, &BTreeMap::new(), &mut cells, &mut calls).unwrap_err();
        assert_eq!(error.code(), "limit");
        assert_eq!(error.span(), span);
        let mut cells = MAX_CELLS;
        let mut calls = 0;
        let error = natural(&helper, &BTreeMap::new(), &mut cells, &mut calls).unwrap_err();
        assert_eq!(error.code(), "limit");
        assert_eq!(error.span(), span);
        assert_eq!(calls, 0, "work must stop before calling the helper");
    }
}
