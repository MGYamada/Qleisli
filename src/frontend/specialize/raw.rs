//! Source-bound finite proposals. This adapter supplies no acceptance decision.
//! Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
use super::ast::OperationConstructor;
use super::elaborate::operation_signature;
use super::primitive::Primitive;
use super::{ElaboratedProgram, Error, Result, SourceType, SourceValue, Span};
use crate::contract::{BasisType, DEFAULT_EXACT_WORK, exact::Budget, meaning::FiniteMeaning};
use crate::frontend::raw_state::{RawState, Slot};
use crate::frontend::types::Kind;
use crate::interchange::finite_leaf::{self, CheckedUnitaryLeaf, UnitaryBoundary};
use crate::interchange::{RootInterface, Version, native};
use crate::ir::{BasisShape, ClassicalId, Effect, QuantumPort, RawProgram, SingleGate};
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

mod circuit;
pub(super) mod contracts;
mod preservation;

const MAX_OPERATIONS: usize = 10_000;
const MAX_CALLS: usize = 1_024;
const MAX_DEPTH: usize = 16;
const MAX_CELLS: usize = 100_000;
const MAX_LIVE_QUBITS: usize = 16;

pub(super) type CheckedMeaning = (
    super::elaborate::OperationKey,
    CheckedUnitaryLeaf,
    Option<Arc<crate::contract::FunctionEvidence>>,
);

#[derive(Clone, Debug)]
enum OperationSite {
    Binding(usize, String),
    Step(usize, usize),
    Descendant(Box<OperationSite>, Vec<usize>),
}
impl OperationSite {
    fn origin(&self) -> &Self {
        match self {
            Self::Descendant(site, _) => site.origin(),
            _ => self,
        }
    }
    fn caller(&self) -> usize {
        match self {
            Self::Binding(id, _) | Self::Step(id, _) => *id,
            Self::Descendant(site, _) => site.caller(),
        }
    }
    fn select<'a>(
        &self,
        source: &'a ElaboratedProgram,
        depth: usize,
    ) -> Option<&'a super::SourceOperation> {
        let definition = source.definitions().get(self.caller())?;
        let mut operation = match self {
            Self::Binding(_, name) => definition.operations().get(name)?,
            Self::Step(_, step) => definition.steps().get(*step)?.operation()?,
            Self::Descendant(site, path) => {
                let mut operation = site.select(source, 0)?;
                for index in path {
                    operation = operation.children().get(*index)?;
                }
                operation
            }
        };
        for _ in 0..depth {
            operation = operation.child()?;
        }
        Some(operation)
    }
}

/// Native finite equations for every original Meaning binding in this immutable
/// concrete source graph. No constructor or mutable evidence view is public.
#[derive(Debug)]
pub struct CheckedSourceMeanings<'a> {
    source: &'a ElaboratedProgram,
    pub(super) leaves: Arc<Vec<CheckedMeaning>>,
}
impl CheckedSourceMeanings<'_> {
    pub fn checked_bindings(&self) -> usize {
        self.leaves.len()
    }
    pub fn source(&self) -> &ElaboratedProgram {
        self.source
    }
    /// Emit actual checked finite nodes. The final hierarchy still needs a
    /// fresh native decision; this is not an AST preservation theorem.
    pub fn lower_hierarchy(&self) -> Result<super::HierarchyProposal> {
        super::lower::lower_with_checked_meanings(self)
    }
    /// Emit Raw only after independently checking the actual instruction
    /// intervals against the original finite requests. No accepted root is
    /// returned; the caller must still obtain a fresh whole-artifact decision.
    pub fn lower_raw(
        &self,
        kernel: &native::Kernel,
        budget: &mut Budget,
    ) -> Result<RawSourceProposal> {
        if self.source.has_control_obligations() {
            return lower_refined_with_control(self.source, kernel, budget);
        }
        self.source.require_control_evidence()?;
        if budget.remaining() > DEFAULT_EXACT_WORK {
            return Err(Error::new(
                "limit",
                Span::default(),
                "source Meaning budget exceeds the shared exact-work ceiling",
            ));
        }
        let mut proposal = lower_inner(
            self.source,
            self.source.root(),
            None,
            None,
            Some((kernel, budget, &self.leaves)),
        )?;
        // lower_inner freshly accepts and independently replays these exact
        // emitted intervals once, using the same original requests and budget.
        proposal.meanings = Some(self.leaves.clone());
        Ok(proposal)
    }
}

pub(super) fn check_operation_meanings<'a>(
    source: &'a ElaboratedProgram,
    kernel: &native::Kernel,
    budget: &mut Budget,
) -> Result<CheckedSourceMeanings<'a>> {
    source.require_function_contracts()?;
    check_operation_meanings_selected(source, kernel, budget, None)
}

fn check_operation_meanings_selected<'a>(
    source: &'a ElaboratedProgram,
    kernel: &native::Kernel,
    budget: &mut Budget,
    selected: Option<&BTreeSet<usize>>,
) -> Result<CheckedSourceMeanings<'a>> {
    if budget.remaining() > DEFAULT_EXACT_WORK {
        return Err(Error::new(
            "limit",
            Span::default(),
            "source Meaning budget exceeds the shared exact-work ceiling",
        ));
    }
    let program = &source.instantiation().program;
    let mut collector = MeaningCollector {
        source,
        kernel,
        budget,
        leaves: Vec::new(),
        bytes: 0,
    };
    for (caller, definition) in source.definitions().iter().enumerate() {
        if selected.is_some_and(|selected| !selected.contains(&caller)) {
            continue;
        }
        for formal in &program.checked.interface(definition.original).statics {
            let crate::frontend::check::StaticKind::Operation { meaning, .. } = &formal.kind else {
                continue;
            };
            let site = OperationSite::Binding(caller, formal.key.name.clone());
            if let Some(id) = meaning {
                collector.check(&site, 0, *id)?;
            }
            collector.annotated(&site)?;
        }
        for (step, operation) in definition.steps().iter().enumerate() {
            if operation.operation().is_some() {
                collector.annotated(&OperationSite::Step(caller, step))?;
            }
        }
    }
    Ok(CheckedSourceMeanings {
        source,
        leaves: Arc::new(collector.leaves),
    })
}

struct MeaningCollector<'a, 'b> {
    source: &'a ElaboratedProgram,
    kernel: &'b native::Kernel,
    budget: &'b mut Budget,
    leaves: Vec<CheckedMeaning>,
    bytes: usize,
}
impl MeaningCollector<'_, '_> {
    fn annotated(&mut self, site: &OperationSite) -> Result<()> {
        let source = self.source;
        let root = site.select(source, 0).expect("original operation site");
        let mut pending = vec![(root, Vec::new())];
        let mut visited = 0;
        while let Some((operation, path)) = pending.pop() {
            visited += 1;
            if path.len() > MAX_DEPTH || visited > MAX_CELLS {
                return Err(Error::new(
                    "limit",
                    operation.span(),
                    "Raw operation exceeds existing depth bound",
                ));
            }
            let descendant = OperationSite::Descendant(Box::new(site.clone()), path.clone());
            for required in operation.meanings.iter() {
                let (selected, depth) = if root.has_constructed() {
                    (&descendant, 0)
                } else {
                    (site, path.len())
                };
                self.check(selected, depth, required.id)
                    .map_err(|mut error| {
                        error.span = required.span;
                        error.module = Some(required.module.clone());
                        error
                    })?;
            }
            for (index, child) in operation.children().iter().enumerate().rev() {
                let mut child_path = path.clone();
                child_path.push(index);
                pending.push((child, child_path));
            }
        }
        Ok(())
    }
    fn check(
        &mut self,
        site: &OperationSite,
        depth: usize,
        id: crate::frontend::resolve::DefId,
    ) -> Result<()> {
        let source = self.source;
        let definition = &source.definitions()[site.caller()];
        let operation = site
            .select(source, depth)
            .expect("original operation descendant");
        let program = &source.instantiation().program;
        let span = operation.span();
        if self.leaves.len() >= MAX_CALLS {
            return Err(Error::new(
                "limit",
                span,
                "source Meaning checking exceeds 1024 bindings",
            ));
        }
        // Fix the original request before producing or checking its actual body.
        let target = program.meaning_targets[&id].expression(span)?;
        let checking =
            source
                .has_control_obligations()
                .then_some((self.kernel, &mut *self.budget, &[][..]));
        let proposal = lower_operation_site(source, site.clone(), depth, checking)?;
        self.bytes = self
            .bytes
            .checked_add(proposal.payload().len())
            .ok_or_else(|| Error::new("limit", span, "provider byte accounting overflow"))?;
        if self.bytes > MAX_CELLS {
            return Err(Error::new(
                "limit",
                span,
                "source Meaning checking exceeds 100000 aggregate provider bytes",
            ));
        }
        self.budget
            .charge(proposal.payload().len())
            .map_err(|e| Error::new("limit", span, e.to_string()))?;
        let check = (|| -> Result<(CheckedUnitaryLeaf, Option<Arc<crate::contract::FunctionEvidence>>)> {
            if target.references().is_empty() {
                let required = target.finite().map_err(|e| invalid(span, &e.to_string()))?;
                let check = proposal.check_finite_meaning(self.kernel, required, self.budget)?;
                return Ok((check.leaf, None));
            }
            let required = source.meaning_artifacts.get(&id)
                .ok_or_else(|| invalid(span, "original reference target has no fresh native artifact"))?;
            if proposal.finite_boundary.as_ref().map(|boundary| boundary.signature()) != Some(target.signature()) {
                return Err(invalid(span, "reference Meaning changes its exact unary Unitary basis tree"));
            }
            let accepted = self.kernel.accept(proposal.proposal())
                .map_err(|e| Error::new(e.code, span, e.to_string()))?;
            self.budget.charge(accepted.native_exact_work())
                .map_err(|e| Error::new("limit", span, e.to_string()))?;
            proposal.replay_with_work(&accepted, self.budget)?;
            let receipt = Arc::new(crate::contract::FunctionEvidence::check_retained_with_kernel(
                self.kernel, target.signature().clone(), accepted.raw().clone(), required.raw.clone(),
                crate::contract::function::RetainedIdentity::shared(definition.path().to_owned(),
                    program.checked.resolution.path(id), required.sources.clone()), self.budget)
                .map_err(|e| Error::new(if e.error.is_capacity() {"limit"} else {"contract"}, span, e.to_string()))?);
            let leaf = contracts::leaf(self.kernel, &receipt, self.budget, span)?;
            self.bytes = self.bytes.saturating_add(leaf.payload().len());
            if self.bytes > MAX_CELLS {
                return Err(Error::new("limit", span, "source Meaning checking exceeds 100000 aggregate provider bytes"));
            }
            Ok((leaf, Some(receipt)))
        })()
            .map_err(|mut error| {
                let location = match site.origin() {
                    OperationSite::Binding(_, name) => name.clone(),
                    OperationSite::Step(_, step) => format!("step {step}"),
                    OperationSite::Descendant(..) => unreachable!("original operation site"),
                };
                error.message = format!(
                    "operation binding {}::{location} must satisfy original Meaning {}: {}",
                    definition.path(),
                    program.checked.resolution.path(id),
                    error.message()
                );
                error
            })?;
        self.leaves.push((operation.key(), check.0, check.1));
        Ok(())
    }
}

/// An immutable finite transport proposal alongside its exact source instance.
///
/// The adapter supports ordinary Unit/Bit/Bits products and packaged quantum
/// Unit/Bit/Bits/product bases, specialized ordinary calls and the explicitly
/// supported finite primitives. Native Raw validity
/// and source-step correspondence are distinct checks; neither proves source
/// elaboration preserves meaning. Whole argument/result trees remain beside
/// the separate classical SSA and quantum-owner transport interfaces.
#[derive(Clone, Debug)]
pub struct RawSourceProposal {
    source: ElaboratedProgram,
    subject: usize,
    binding: Option<OperationSite>,
    operation_depth: usize,
    proposal: native::Proposal,
    finite_boundary: Option<UnitaryBoundary>,
    meanings: Option<Arc<Vec<CheckedMeaning>>>,
}

/// A fresh native finite equation with replay of these retained source steps.
/// The borrowed immutable source/target identities cannot be substituted.
/// This does not prove original AST-to-step preservation or generic binding.
#[derive(Debug)]
pub struct SourceMeaningCheck<'a> {
    source: &'a RawSourceProposal,
    required: &'a FiniteMeaning,
    leaf: CheckedUnitaryLeaf,
}
impl SourceMeaningCheck<'_> {
    pub fn source(&self) -> &RawSourceProposal {
        self.source
    }
    pub fn required(&self) -> &FiniteMeaning {
        self.required
    }
    pub fn leaf(&self) -> &CheckedUnitaryLeaf {
        &self.leaf
    }
    /// Emit a hierarchy whose actual use of this original binding embeds the
    /// same checked provider bytes and required matrix. The returned artifact
    /// is an untrusted proposal and still requires fresh native checking.
    /// This neither checks all bindings nor enables Meaning-refined admission.
    pub fn lower_hierarchy(&self) -> Result<super::HierarchyProposal> {
        super::lower::lower_with_checked_operation(self)
    }
}
impl RawSourceProposal {
    /// Check the requested exact operator on this actual source-bound artifact,
    /// then independently replay its ordered steps. Only Lean issues the leaf.
    /// Unsupported interfaces reject before any native invocation. This gate
    /// neither enables generic providers nor proves source elaboration sound.
    pub fn check_finite_meaning<'a>(
        &'a self,
        kernel: &native::Kernel,
        required: &'a FiniteMeaning,
        budget: &mut Budget,
    ) -> Result<SourceMeaningCheck<'a>> {
        let root = self.definition();
        let error = |code, message: String| {
            let path = root.path();
            Error::new(code, root.span(), message)
                .in_module(path.rsplit_once("::").map_or(path, |(module, _)| module))
        };
        let boundary = self.finite_boundary.as_ref().ok_or_else(|| {
            error("unsupported", "source Meaning checking requires a unary exact Unit/Bit/Bits/product quantum endomorphism with Unitary effect".into())
        })?;
        if required.signature() != boundary.signature() {
            return Err(error(
                "type",
                "source and requested Meaning have different exact basis trees".into(),
            ));
        }
        if budget.remaining() > DEFAULT_EXACT_WORK {
            return Err(error(
                "limit",
                "source Meaning budget exceeds the shared exact-work ceiling".into(),
            ));
        }
        let matrix = required.matrix(budget).map_err(|e| {
            error(
                if e.is_capacity() { "limit" } else { "meaning" },
                e.to_string(),
            )
        })?;
        let leaf =
            finite_leaf::check_with_kernel(kernel, self.payload(), boundary, &matrix, budget)
                .map_err(|e| error(e.code, e.to_string()))?;
        if leaf.payload() != self.payload() {
            return Err(error(
                "preservation",
                "checked leaf differs from actual source artifact".into(),
            ));
        }
        self.replay_with_work(leaf.program(), budget)?;
        Ok(SourceMeaningCheck {
            source: self,
            required,
            leaf,
        })
    }
    pub fn source(&self) -> &ElaboratedProgram {
        &self.source
    }
    pub fn proposal(&self) -> &native::Proposal {
        &self.proposal
    }
    pub fn payload(&self) -> &[u8] {
        self.proposal.artifact()
    }
    /// Original leaf definition, or original caller for a constructed operation.
    /// `operation()` retains the exact selected tree and both of its ports.
    /// The caller's instantiation metadata is never rewritten as leaf metadata.
    pub fn definition(&self) -> &super::SourceDefinition {
        &self.source.definitions()[self.subject]
    }
    pub fn definition_index(&self) -> usize {
        self.subject
    }
    pub fn operation_binding(&self) -> Option<(usize, &str)> {
        match self.binding.as_ref()?.origin() {
            OperationSite::Binding(id, name) => Some((*id, name)),
            OperationSite::Step(_, _) => None,
            OperationSite::Descendant(..) => unreachable!("original operation site"),
        }
    }
    /// Original source-step locator for a direct operation expression.
    pub fn operation_step(&self) -> Option<(usize, usize)> {
        match self.binding.as_ref()?.origin() {
            OperationSite::Step(id, step) => Some((*id, *step)),
            OperationSite::Binding(_, _) => None,
            OperationSite::Descendant(..) => unreachable!("original operation site"),
        }
    }
    /// Legacy repetition depth after selecting the original operation subtree.
    /// Constructor descendants are selected by their retained ordered path.
    pub fn operation_depth(&self) -> usize {
        self.operation_depth
    }
    pub fn operation(&self) -> Option<&super::SourceOperation> {
        self.binding
            .as_ref()?
            .select(&self.source, self.operation_depth)
    }
    fn replay(&self, accepted: &native::AcceptedProgram) -> Result<()> {
        self.replay_with_work(accepted, &mut Budget::new(DEFAULT_EXACT_WORK))
    }
    fn replay_with_work(
        &self,
        accepted: &native::AcceptedProgram,
        budget: &mut Budget,
    ) -> Result<()> {
        let operation = if self.binding.is_some() {
            Some(self.operation().ok_or_else(|| {
                invalid(
                    Span::default(),
                    "original operation binding is absent during replay",
                )
            })?)
        } else {
            None
        };
        preservation::validate_subject_with_meanings(
            &self.source,
            self.subject,
            operation,
            accepted.raw(),
            Some(&accepted.kernel()),
            budget,
            self.meanings.as_deref().map_or(&[], Vec::as_slice),
        )
    }

    /// Compare the actual native-accepted artifact with retained ordered source
    /// steps. This issues no execution handle and proves no AST-to-step theorem.
    /// No independent general source meaning is requested by Raw validity.
    pub fn validate_source_steps(&self, accepted: &native::AcceptedProgram) -> Result<()> {
        if accepted.artifact() != self.payload() || accepted.request().is_some() {
            return Err(Error::new(
                "preservation",
                Span::default(),
                "native accepted artifact differs from the source-bound Raw proposal",
            ));
        }
        self.replay(accepted)
    }
}

#[cfg(test)]
pub(super) fn validate_source_with_kernel(
    source: &ElaboratedProgram,
    subject: usize,
    operation: Option<&super::SourceOperation>,
    raw: &RawProgram,
    kernel: &native::Kernel,
) -> Result<()> {
    preservation::validate_subject_with_kernel(source, subject, operation, raw, Some(kernel))
}

fn located(source: &ElaboratedProgram, id: usize, span: Span, message: &str) -> Error {
    let path = source.definitions()[id].path();
    Error::new("unsupported", span, message)
        .in_module(path.rsplit_once("::").map_or(path, |(module, _)| module))
}
fn supported(ty: &SourceType) -> bool {
    match &ty.kind {
        Kind::Unit | Kind::Bit | Kind::Bits(_) => true,
        Kind::Q(basis) => basis_supported(basis),
        Kind::Tuple(fields) => fields.iter().all(supported),
        Kind::Parameter(_) => false,
    }
}
fn basis_supported(basis: &SourceType) -> bool {
    match &basis.kind {
        Kind::Unit | Kind::Bit | Kind::Bits(_) => true,
        Kind::Tuple(fields) => fields.iter().all(basis_supported),
        _ => false,
    }
}
fn finite_basis(basis: &SourceType) -> Option<BasisType> {
    match &basis.kind {
        Kind::Unit => Some(BasisType::Unit),
        Kind::Bit => Some(BasisType::Bit),
        Kind::Bits(width) => Some(BasisType::Bits(*width)),
        Kind::Tuple(fields) => {
            let mut fields = fields
                .iter()
                .map(finite_basis)
                .collect::<Option<Vec<_>>>()?;
            if fields.len() == 2 {
                let right = fields.pop()?;
                Some(BasisType::pair(fields.pop()?, right))
            } else {
                Some(BasisType::Tuple(fields))
            }
        }
        _ => None,
    }
}
fn atom_count(ty: &SourceType) -> usize {
    match &ty.kind {
        Kind::Unit => 0,
        Kind::Bit | Kind::Bits(_) | Kind::Q(_) => 1,
        Kind::Tuple(fields) => fields.iter().map(atom_count).sum(),
        Kind::Parameter(_) => unreachable!("preflighted closed finite source type"),
    }
}
fn effect(source: &ElaboratedProgram, subject: usize) -> Effect {
    match source.definitions()[subject].effect() {
        "unitary" => Effect::Unitary,
        "iso" => Effect::Isometry,
        "observe" => Effect::Observe,
        _ => unreachable!("private source effect"),
    }
}
// Exact existing dyadic phase exp(2*pi*i*j/2^k). The source already requires
// canonical j and k <= 8. Raw T realizes only integral multiples of pi/4;
// never round a smaller angle or obtain it by retrying another native request.
fn eighths(ns: &[u32]) -> Option<usize> {
    let [j, k] = ns else {
        return None;
    };
    if *k > 8 {
        return None;
    }
    let denominator = 1u32 << k;
    if *j >= denominator || (j * 8) % denominator != 0 {
        return None;
    }
    Some((j * 8 / denominator) as usize)
}
// Capability selection precedes every emission and native decision.
fn check_profile(
    source: &ElaboratedProgram,
    selected: Option<&BTreeSet<usize>>,
    checking_control: bool,
) -> Result<()> {
    if !checking_control {
        source.require_control_evidence()?;
    }
    for (id, definition) in source.definitions().iter().enumerate() {
        if selected.is_some_and(|selected| !selected.contains(&id)) {
            continue;
        }
        for value in definition.inputs().iter().chain([definition.output()]) {
            if !supported(value.ty()) {
                return Err(located(
                    source,
                    id,
                    definition.span(),
                    "finite source lowering requires closed ordinary finite products or exact packaged quantum bases",
                ));
            }
        }
        for step in definition.steps() {
            if checking_control {
                step.check_access_shape()?;
            } else {
                step.check_access_contract()?;
            }
            if step
                .inputs()
                .iter()
                .chain([step.output()])
                .any(|v| !supported(v.ty()))
            {
                return Err(located(
                    source,
                    id,
                    step.span(),
                    "finite source lowering requires supported intermediate value types",
                ));
            }
            if step.boolean().is_some() || step.partition().is_some() {
                continue;
            }
            if step.called_definition().is_some()
                || step.contract().is_some()
                || (matches!(step.kind(), "apply" | "adjoint" | "controlled")
                    && step.operation().is_some())
            {
                continue;
            }
            match step.primitive_kind() {
                Some(
                    Primitive::H
                    | Primitive::X
                    | Primitive::Z
                    | Primitive::Cnot
                    | Primitive::Init0
                    | Primitive::Unit
                    | Primitive::Finish
                    | Primitive::MeasureZ
                    | Primitive::PhaseEighth
                    | Primitive::Split
                    | Primitive::Join
                    | Primitive::TakeBit
                    | Primitive::PutBit
                    | Primitive::EmptyBits
                    | Primitive::PrependBit,
                ) => {}
                Some(Primitive::Phase) if eighths(step.natural_arguments()).is_some() => {}
                Some(Primitive::Phase) => {
                    return Err(located(
                        source,
                        id,
                        step.span(),
                        "finite source lowering requires an exact integral eighth-turn phase; this dyadic phase needs its explicit target support",
                    ));
                }
                _ => {
                    return Err(located(
                        source,
                        id,
                        step.span(),
                        "finite source lowering does not yet support this primitive or operation capability",
                    ));
                }
            }
        }
    }
    Ok(())
}

#[derive(Clone)]
enum Atom {
    Classical(ClassicalId),
    Register(Arc<[ClassicalId]>),
    Quantum(Slot),
}
type Values = BTreeMap<u32, Atom>;

fn invalid(span: Span, message: &str) -> Error {
    Error::new("preservation", span, message)
}
fn read(value: &SourceValue, values: &mut Values, span: Span) -> Result<Vec<Atom>> {
    match &value.ty().kind {
        Kind::Unit => Ok(vec![]),
        Kind::Bit | Kind::Bits(_) | Kind::Q(_) => {
            let id = value.identity().expect("source atom identity");
            let atom = if value.ty().is_quantum() {
                values.remove(&id)
            } else {
                values.get(&id).cloned()
            }
            .ok_or_else(|| {
                invalid(
                    span,
                    "source atom is absent or its quantum owner was consumed",
                )
            })?;
            Ok(vec![atom])
        }
        Kind::Tuple(_) => {
            let mut atoms = Vec::new();
            for field in value.fields() {
                atoms.extend(read(field, values, span)?);
            }
            Ok(atoms)
        }
        _ => unreachable!("preflighted finite source type"),
    }
}
fn bind(value: &SourceValue, atoms: &[Atom], values: &mut Values, span: Span) -> Result<()> {
    if atoms.len() != atom_count(value.ty()) {
        return Err(invalid(span, "source value changes its exact leaf count"));
    }
    match &value.ty().kind {
        Kind::Unit => {}
        Kind::Bit | Kind::Bits(_) | Kind::Q(_) => {
            if !matches!(
                (&value.ty().kind, &atoms[0]),
                (Kind::Bit, Atom::Classical(_))
                    | (Kind::Bits(_), Atom::Register(_))
                    | (Kind::Q(_), Atom::Quantum(_))
            ) {
                return Err(invalid(span, "source atom changes its ownership category"));
            }
            if let (Kind::Bits(width), Atom::Register(ids)) = (&value.ty().kind, &atoms[0]) {
                if ids.len() != *width as usize {
                    return Err(invalid(span, "source register changes its exact width"));
                }
            }
            if values
                .insert(
                    value.identity().expect("source atom identity"),
                    atoms[0].clone(),
                )
                .is_some()
            {
                return Err(invalid(span, "source step redefines a live value identity"));
            }
        }
        Kind::Tuple(_) => {
            let mut offset = 0;
            for field in value.fields() {
                let count = atom_count(field.ty());
                bind(field, &atoms[offset..offset + count], values, span)?;
                offset += count;
            }
        }
        _ => unreachable!("preflighted finite source type"),
    }
    Ok(())
}
fn quantum(atoms: &[Atom], span: Span) -> Result<Slot> {
    match atoms {
        [Atom::Quantum(slot)] => Ok(*slot),
        _ => Err(invalid(span, "quantum primitive requires one owned Q<Bit>")),
    }
}
struct Emitter<'a> {
    source: &'a ElaboratedProgram,
    meanings: &'a [CheckedMeaning],
    raw: RawState<u32>,
    calls: usize,
    cells: usize,
}
impl Emitter<'_> {
    fn access(
        &mut self,
        op: &super::SourceOperation,
        arguments: Vec<Vec<Atom>>,
        depth: usize,
        controlled: bool,
    ) -> Result<Vec<Atom>> {
        let span = op.span();
        if arguments.len() != 1 + usize::from(controlled) {
            return Err(invalid(span, "source access changes whole-argument arity"));
        }
        let target = quantum(&arguments[usize::from(controlled)], span)?;
        let control = if controlled {
            Some(quantum(&arguments[0], span)?)
        } else {
            None
        };
        if control == Some(target) {
            return Err(invalid(span, "controlled source operands alias"));
        }
        let mut pending = vec![(op, 0)];
        while let Some((operation, level)) = pending.pop() {
            if level > MAX_DEPTH {
                return Err(Error::new(
                    "limit",
                    span,
                    "Raw access exceeds operation depth bounds",
                ));
            }
            if !operation.children().is_empty() {
                self.cells = self.cells.saturating_add(1);
                if self.cells > MAX_CELLS {
                    return Err(Error::new(
                        "limit",
                        span,
                        "Raw access exceeds operation cell bounds",
                    ));
                }
                pending.extend(operation.children().iter().map(|child| (child, level + 1)));
            }
        }
        let (ports, effect, _) = operation_signature(op, self.source.definitions(), span)?;
        let basis = &self.raw.registers[&target].basis;
        let actual_input = if controlled {
            ports.input
        } else {
            ports.output
        };
        if actual_input.quantum_basis() != Some(basis)
            || (controlled && ports.input != ports.output)
            || effect != Effect::Unitary
        {
            return Err(invalid(
                span,
                "source access changes its exact endomorphism interface",
            ));
        }
        // Compile the actual retained provider in an isolated canonical frame.
        // The shared counters carry through nested transforms, never resetting
        // the work/depth budget for a new temporary state.
        let mut child = Emitter {
            source: self.source,
            meanings: self.meanings,
            raw: RawState::new(),
            calls: self.calls,
            cells: self.cells,
        };
        let input = child.input_type(ports.input, span)?;
        let input_slot = quantum(&input, span)?;
        let input_token = child.raw.registers[&input_slot].token;
        let input_wires = child.raw.registers[&input_slot].wires.clone();
        let output = child.operation(op, vec![input], depth)?;
        let output_slot = quantum(&output, span)?;
        if Some(&child.raw.registers[&output_slot].basis) != ports.output.quantum_basis() {
            return Err(invalid(
                span,
                "source access changes its exact returned basis tree",
            ));
        }
        let mut steps = circuit::flatten(
            &child.raw.operations,
            input_token,
            &input_wires,
            child.raw.registers[&output_slot].token,
            &mut child.cells,
            span,
        )?;
        self.calls = child.calls;
        self.cells = child.cells;
        if controlled {
            steps = circuit::controlled(steps);
        } else {
            crate::contract::invert_steps(&mut steps);
        }
        circuit::charge(&steps, &mut self.cells, span)?;
        self.reserve_operations(if controlled { 3 } else { 1 }, span)?;
        let target_register = self
            .raw
            .registers
            .remove(&target)
            .ok_or_else(|| invalid(span, "source access owner is absent"))?;
        if let Some(control) = control {
            let control_register = self
                .raw
                .registers
                .remove(&control)
                .ok_or_else(|| invalid(span, "source control owner is absent"))?;
            if control_register.basis != SourceType::bit() || control_register.wires.len() != 1 {
                return Err(invalid(span, "source control is not exact Q<Bit>"));
            }
            let joined = self.raw.token();
            let transformed = self.raw.token();
            let control_out = self.raw.token();
            let target_out = self.raw.token();
            self.raw.operations.extend([
                crate::ir::RawOp::Join {
                    left: control_register.token,
                    right: target_register.token,
                    output: joined,
                },
                crate::ir::RawOp::ApplyUnitary {
                    input: joined,
                    output: transformed,
                    steps,
                },
                crate::ir::RawOp::Split {
                    input: transformed,
                    left: control_out,
                    right: target_out,
                    left_bits: 1,
                },
            ]);
            self.raw.registers.insert(
                control,
                crate::frontend::raw_state::Register {
                    token: control_out,
                    ..control_register
                },
            );
            self.raw.registers.insert(
                target,
                crate::frontend::raw_state::Register {
                    token: target_out,
                    ..target_register
                },
            );
            Ok(vec![Atom::Quantum(control), Atom::Quantum(target)])
        } else {
            let output = self.raw.token();
            self.raw.operations.push(crate::ir::RawOp::ApplyUnitary {
                input: target_register.token,
                output,
                steps,
            });
            let basis = ports
                .input
                .quantum_basis()
                .ok_or_else(|| invalid(span, "inverse output is not a quantum owner"))?;
            self.cells = self.cells.saturating_add(basis.tree_size().nodes);
            if self.cells > MAX_CELLS {
                return Err(Error::new(
                    "limit",
                    span,
                    "Raw inverse basis exceeds cell bounds",
                ));
            }
            self.raw.registers.insert(
                target,
                crate::frontend::raw_state::Register {
                    token: output,
                    basis: basis.clone(),
                    ..target_register
                },
            );
            Ok(vec![Atom::Quantum(target)])
        }
    }
    fn operation(
        &mut self,
        op: &super::SourceOperation,
        arguments: Vec<Vec<Atom>>,
        depth: usize,
    ) -> Result<Vec<Atom>> {
        if let Some(receipt) = self
            .meanings
            .iter()
            .find_map(|(key, _, receipt)| (*key == op.key()).then_some(receipt.as_ref()).flatten())
        {
            let [input] = arguments.as_slice() else {
                return Err(invalid(
                    op.span(),
                    "reference Meaning operation requires one whole owner",
                ));
            };
            let slot = quantum(input, op.span())?;
            let register = &self.raw.registers[&slot];
            if finite_basis(&register.basis).as_ref() != Some(receipt.signature()) {
                return Err(invalid(
                    op.span(),
                    "reference Meaning operation changes its exact basis",
                ));
            }
            let input = register.token;
            let bits = register.wires.len();
            self.reserve_operations(1, op.span())?;
            let output = self.raw.token();
            self.raw.operations.push(crate::ir::RawOp::ApplyUnitary {
                input,
                output,
                steps: vec![crate::ir::CircuitStep {
                    controls: vec![],
                    action: crate::ir::CircuitAction::Contract {
                        indices: (0..bits).collect(),
                        evidence: receipt.clone(),
                        adjoint: false,
                    },
                }],
            });
            self.raw
                .registers
                .get_mut(&slot)
                .expect("original operation owner")
                .token = output;
            return Ok(vec![Atom::Quantum(slot)]);
        }
        if let Some(id) = op.definition() {
            return self.invoke(id, arguments, depth, op.span());
        }
        self.calls += 1;
        if self.calls > MAX_CALLS || depth > MAX_DEPTH {
            return Err(Error::new(
                "limit",
                op.span(),
                "Raw operation exceeds existing call/depth bounds",
            ));
        }
        if let Some((kind, children, _)) = op.constructed() {
            return match kind {
                OperationConstructor::Then => {
                    let middle = self.operation(&children[0], arguments, depth + 1)?;
                    self.operation(&children[1], vec![middle], depth + 1)
                }
                OperationConstructor::Adjoint => {
                    self.access(&children[0], arguments, depth + 1, false)
                }
                OperationConstructor::Conjugate => {
                    let first = self.access(&children[0], arguments, depth + 1, false)?;
                    let middle = self.operation(&children[1], vec![first], depth + 1)?;
                    self.operation(&children[0], vec![middle], depth + 1)
                }
                OperationConstructor::Tensor | OperationConstructor::Controlled => {
                    let [input]: [Vec<Atom>; 1] = arguments.try_into().map_err(|_| {
                        invalid(op.span(), "packed constructor requires one whole argument")
                    })?;
                    let (left, right) = self.split_owner(quantum(&input, op.span())?, op.span())?;
                    let (left, right) = if kind == OperationConstructor::Tensor {
                        let left = self.operation(
                            &children[0],
                            vec![vec![Atom::Quantum(left)]],
                            depth + 1,
                        )?;
                        let right = self.operation(
                            &children[1],
                            vec![vec![Atom::Quantum(right)]],
                            depth + 1,
                        )?;
                        (quantum(&left, op.span())?, quantum(&right, op.span())?)
                    } else {
                        let result = self.access(
                            &children[0],
                            vec![vec![Atom::Quantum(left)], vec![Atom::Quantum(right)]],
                            depth + 1,
                            true,
                        )?;
                        let [Atom::Quantum(left), Atom::Quantum(right)] = result.as_slice() else {
                            return Err(invalid(
                                op.span(),
                                "packed control changes its owner frame",
                            ));
                        };
                        (*left, *right)
                    };
                    Ok(vec![Atom::Quantum(self.join_owners(
                        left,
                        right,
                        op.span(),
                    )?)])
                }
            };
        }
        let child = op.child().expect("retained repeat child");
        let [mut value]: [Vec<Atom>; 1] = arguments
            .try_into()
            .map_err(|_| invalid(op.span(), "repeated operation requires one whole argument"))?;
        for _ in 0..op.repeat_count().expect("retained repeat count") {
            value = self.operation(child, vec![value], depth + 1)?;
        }
        Ok(value)
    }
    fn split_owner(&mut self, input: Slot, span: Span) -> Result<(Slot, Slot)> {
        self.reserve_operations(1, span)?;
        let register = self
            .raw
            .registers
            .remove(&input)
            .ok_or_else(|| invalid(span, "constructor split owner is absent"))?;
        let fields = register
            .basis
            .tuple_fields()
            .filter(|fields| fields.len() == 2)
            .ok_or_else(|| invalid(span, "constructor requires a binary packed basis"))?;
        self.cells = self
            .cells
            .saturating_add(register.basis.tree_size().nodes + register.wires.len() + 2);
        if self.cells > MAX_CELLS {
            return Err(Error::new(
                "limit",
                span,
                "Raw constructor split exceeds value-cell bounds",
            ));
        }
        let width = fields[0]
            .basis_width()
            .ok_or_else(|| invalid(span, "constructor field is not finite"))?
            as usize;
        if width > register.wires.len() {
            return Err(invalid(span, "constructor field exceeds actual wires"));
        }
        let left = self
            .raw
            .register(fields[0].clone(), register.wires[..width].to_vec());
        let right = self
            .raw
            .register(fields[1].clone(), register.wires[width..].to_vec());
        self.raw.operations.push(crate::ir::RawOp::Split {
            input: register.token,
            left: self.raw.registers[&left].token,
            right: self.raw.registers[&right].token,
            left_bits: width as u8,
        });
        Ok((left, right))
    }
    fn join_owners(&mut self, left: Slot, right: Slot, span: Span) -> Result<Slot> {
        self.reserve_operations(1, span)?;
        if left == right {
            return Err(invalid(span, "constructor aliases its tensor owners"));
        }
        let left = self
            .raw
            .registers
            .remove(&left)
            .ok_or_else(|| invalid(span, "constructor left owner is absent"))?;
        let right = self
            .raw
            .registers
            .remove(&right)
            .ok_or_else(|| invalid(span, "constructor right owner is absent"))?;
        self.cells = self
            .cells
            .saturating_add(1 + left.wires.len() + right.wires.len());
        if self.cells > MAX_CELLS {
            return Err(Error::new(
                "limit",
                span,
                "Raw constructor join exceeds value-cell bounds",
            ));
        }
        let (l, r) = (left.token, right.token);
        let mut wires = left.wires;
        wires.extend(right.wires);
        let output = self
            .raw
            .register(SourceType::pair(left.basis, right.basis), wires);
        self.raw.operations.push(crate::ir::RawOp::Join {
            left: l,
            right: r,
            output: self.raw.registers[&output].token,
        });
        Ok(output)
    }
    fn charge_value(&mut self, value: &SourceValue, span: Span) -> Result<()> {
        self.charge_type(value.ty(), span)
    }
    fn charge_type(&mut self, ty: &SourceType, span: Span) -> Result<()> {
        // Ordinary register elements occupy transport storage even when the
        // type has only one node. Bound every allocation before emission.
        let mut pending = vec![ty];
        while let Some(ty) = pending.pop() {
            match &ty.kind {
                Kind::Bits(width) => self.cells = self.cells.saturating_add(*width as usize),
                Kind::Tuple(fields) => pending.extend(fields),
                _ => {}
            }
        }
        self.cells = self.cells.saturating_add(ty.owner_shape_size().nodes);
        if self.cells > MAX_CELLS {
            return Err(Error::new(
                "limit",
                span,
                "finite source lowering exceeds 100000 value cells",
            ));
        }
        Ok(())
    }
    fn reserve_operations(&self, n: usize, span: Span) -> Result<()> {
        if self.raw.operations.len().saturating_add(n) > MAX_OPERATIONS {
            return Err(Error::new(
                "limit",
                span,
                "finite source lowering exceeds 10000 operations",
            ));
        }
        Ok(())
    }
    fn reserve_qubit(&self, span: Span) -> Result<()> {
        if self
            .raw
            .registers
            .values()
            .map(|r| r.wires.len())
            .sum::<usize>()
            >= MAX_LIVE_QUBITS
        {
            return Err(Error::new(
                "limit",
                span,
                "finite source lowering exceeds 16 globally live quantum wires",
            ));
        }
        Ok(())
    }

    /// Repartition the original ordered wires with existing structural IR.
    /// The temporary prefix/suffix owners exist even at width zero; none is
    /// prepared, discarded or represented by a physical permutation gate.
    fn register_bit(
        &mut self,
        take: bool,
        step: &super::SourceStep,
        inputs: &[Vec<Atom>],
    ) -> Result<Vec<Atom>> {
        let [n, k] = step.natural_arguments() else {
            return Err(invalid(
                step.span(),
                "register repartition loses its exact Nat arguments",
            ));
        };
        if *n > 8 || k >= n {
            return Err(invalid(
                step.span(),
                "register repartition requires k < n <= 8",
            ));
        }
        self.partition_register(
            super::elaborate::PlacePartition {
                taking: take,
                width: *n,
                start: *k,
                end: k + 1,
                bit: true,
            },
            step,
            inputs,
        )
    }
    fn partition_register(
        &mut self,
        p: super::elaborate::PlacePartition,
        step: &super::SourceStep,
        inputs: &[Vec<Atom>],
    ) -> Result<Vec<Atom>> {
        use crate::ir::RawOp;
        let span = step.span();
        if p.start > p.end || p.end > p.width || p.width > 8 || (p.bit && p.end - p.start != 1) {
            return Err(invalid(
                span,
                "place repartition loses its exact ordered bounds",
            ));
        }
        let n = p.width;
        let selected_width = p.end - p.start;
        let selected_basis = if p.bit {
            SourceType::bit()
        } else {
            SourceType::bits(selected_width)
        };
        let width = n as usize;
        let position = p.start as usize;
        self.reserve_operations(3, span)?;
        self.cells = self.cells.saturating_add(12 + width * 3);
        if self.cells > MAX_CELLS {
            return Err(Error::new(
                "limit",
                span,
                "register repartition exceeds value-cell bounds",
            ));
        }
        if p.taking {
            let [input] = inputs else {
                return Err(invalid(span, "take_bit requires one original owner"));
            };
            let slot = quantum(input, span)?;
            let register = self
                .raw
                .registers
                .remove(&slot)
                .ok_or_else(|| invalid(span, "take_bit source owner is absent"))?;
            if register.basis != SourceType::bits(n) || register.wires.len() != width {
                return Err(invalid(span, "take_bit changes its original register type"));
            }
            let prefix = self.raw.token();
            let tail = self.raw.token();
            let suffix = self.raw.token();
            let bit = self.raw.register(
                selected_basis.clone(),
                register.wires[position..p.end as usize].to_vec(),
            );
            let rest = self.raw.register(
                SourceType::bits(n - selected_width),
                register
                    .wires
                    .iter()
                    .enumerate()
                    .filter_map(|(i, w)| (i < position || i >= p.end as usize).then_some(*w))
                    .collect(),
            );
            self.raw.operations.extend([
                RawOp::Split {
                    input: register.token,
                    left: prefix,
                    right: tail,
                    left_bits: p.start as u8,
                },
                RawOp::Split {
                    input: tail,
                    left: self.raw.registers[&bit].token,
                    right: suffix,
                    left_bits: selected_width as u8,
                },
                RawOp::Join {
                    left: prefix,
                    right: suffix,
                    output: self.raw.registers[&rest].token,
                },
            ]);
            Ok(vec![Atom::Quantum(bit), Atom::Quantum(rest)])
        } else {
            let [bit, rest] = inputs else {
                return Err(invalid(span, "put_bit requires two original owners"));
            };
            let bit = quantum(bit, span)?;
            let rest = quantum(rest, span)?;
            if bit == rest {
                return Err(invalid(span, "put_bit owners alias"));
            }
            let bit = self
                .raw
                .registers
                .remove(&bit)
                .ok_or_else(|| invalid(span, "put_bit bit owner is absent"))?;
            let rest = self
                .raw
                .registers
                .remove(&rest)
                .ok_or_else(|| invalid(span, "put_bit register owner is absent"))?;
            if bit.basis != selected_basis
                || bit.wires.len() != selected_width as usize
                || rest.basis != SourceType::bits(n - selected_width)
                || rest.wires.len() != width - selected_width as usize
            {
                return Err(invalid(span, "put_bit changes its original owner types"));
            }
            let mut wires = rest.wires;
            wires.splice(position..position, bit.wires);
            let output = self.raw.register(SourceType::bits(n), wires);
            let prefix = self.raw.token();
            let suffix = self.raw.token();
            let head = self.raw.token();
            self.raw.operations.extend([
                RawOp::Split {
                    input: rest.token,
                    left: prefix,
                    right: suffix,
                    left_bits: p.start as u8,
                },
                RawOp::Join {
                    left: prefix,
                    right: bit.token,
                    output: head,
                },
                RawOp::Join {
                    left: head,
                    right: suffix,
                    output: self.raw.registers[&output].token,
                },
            ]);
            Ok(vec![Atom::Quantum(output)])
        }
    }
    fn input(&mut self, value: &SourceValue, span: Span) -> Result<Vec<Atom>> {
        self.input_type(value.ty(), span)
    }
    fn input_type(&mut self, ty: &SourceType, span: Span) -> Result<Vec<Atom>> {
        match &ty.kind {
            Kind::Unit => Ok(vec![]),
            Kind::Bit => Ok(vec![Atom::Classical(self.raw.classical())]),
            Kind::Bits(width) => Ok(vec![Atom::Register(
                (0..*width).map(|_| self.raw.classical()).collect(),
            )]),
            Kind::Q(basis) => {
                let width = basis.basis_width().expect("preflighted finite basis") as usize;
                self.cells = self.cells.saturating_add(basis.tree_size().nodes + width);
                if self.cells > MAX_CELLS {
                    return Err(Error::new(
                        "limit",
                        span,
                        "finite source lowering exceeds 100000 value cells",
                    ));
                }
                let mut wires = Vec::new();
                for _ in 0..width {
                    // Pending input wires are not registered until allocation
                    // ends, so account for them in the existing global bound.
                    if self
                        .raw
                        .registers
                        .values()
                        .map(|r| r.wires.len())
                        .sum::<usize>()
                        + wires.len()
                        >= MAX_LIVE_QUBITS
                    {
                        return Err(Error::new(
                            "limit",
                            span,
                            "finite source lowering exceeds 16 globally live quantum wires",
                        ));
                    }
                    wires.push(self.raw.wire());
                }
                Ok(vec![Atom::Quantum(
                    self.raw.register((**basis).clone(), wires),
                )])
            }
            Kind::Tuple(fields) => {
                let mut atoms = Vec::new();
                for field in fields {
                    atoms.extend(self.input_type(field, span)?);
                }
                Ok(atoms)
            }
            _ => unreachable!("preflighted finite source type"),
        }
    }
    fn invoke(
        &mut self,
        id: usize,
        arguments: Vec<Vec<Atom>>,
        depth: usize,
        call_span: Span,
    ) -> Result<Vec<Atom>> {
        self.calls += 1;
        if self.calls > MAX_CALLS || depth > MAX_DEPTH {
            return Err(Error::new(
                "limit",
                call_span,
                "finite source lowering exceeds call/depth capacity",
            ));
        }
        let definition = &self.source.definitions()[id];
        let module = definition
            .path()
            .rsplit_once("::")
            .map_or(definition.path(), |(module, _)| module);
        (|| -> Result<Vec<Atom>> {
            // A source-ID environment is local to this activation. Physical owners,
            // pending caller arguments and all fresh supplies stay in shared RawState.
            let mut values = Values::new();
            debug_assert_eq!(arguments.len(), definition.inputs().len());
            for (value, atoms) in definition.inputs().iter().zip(arguments) {
                self.charge_value(value, definition.span())?;
                bind(value, &atoms, &mut values, definition.span())?;
            }
            for step in definition.steps() {
                (|| -> Result<()> {
                    let span = step.span();
                    let mut inputs = vec![];
                    for value in step.inputs() {
                        self.charge_value(value, span)?;
                        inputs.push(read(value, &mut values, span)?);
                    }
                    let state_error = |error: crate::frontend::raw_state::StateError| {
                        invalid(span, &error.to_string()).in_module(step.module())
                    };
                    self.charge_value(step.output(), span)?;
                    let output = if let Some(operation) = step.boolean() {
                        let operands = inputs
                            .iter()
                            .map(|atoms| match atoms.as_slice() {
                                [Atom::Classical(id)] => Ok(*id),
                                _ => Err(invalid(
                                    span,
                                    "Boolean source operand is not one ordinary Bit",
                                )),
                            })
                            .collect::<Result<Vec<_>>>()?;
                        self.reserve_operations(1, span)?;
                        vec![Atom::Classical(
                            self.raw
                                .boolean(operation, &operands)
                                .map_err(state_error)?,
                        )]
                    } else if let Some(partition) = step.partition() {
                        self.partition_register(partition, step, &inputs)?
                    } else if let Some(key) = step.contract() {
                        let checked = self.source.contracts.get(&key).ok_or_else(|| {
                            invalid(span, "source contract has no freshly checked original pair")
                        })?;
                        let [input] = inputs.as_slice() else {
                            return Err(invalid(span, "contract requires one owner"));
                        };
                        let slot = quantum(input, span)?;
                        let register = &self.raw.registers[&slot];
                        if finite_basis(&register.basis).as_ref()
                            != Some(checked.receipt.signature())
                        {
                            return Err(invalid(span, "contract changes its exact quantum basis"));
                        }
                        let input = register.token;
                        let bits = register.wires.len();
                        self.reserve_operations(1, span)?;
                        let output = self.raw.token();
                        self.raw.operations.push(crate::ir::RawOp::ApplyUnitary {
                            input,
                            output,
                            steps: vec![crate::ir::CircuitStep {
                                controls: vec![],
                                action: crate::ir::CircuitAction::Contract {
                                    indices: (0..bits).collect(),
                                    evidence: checked.receipt.clone(),
                                    adjoint: false,
                                },
                            }],
                        });
                        self.raw
                            .registers
                            .get_mut(&slot)
                            .expect("retained contract owner")
                            .token = output;
                        vec![Atom::Quantum(slot)]
                    } else if let Some(child) = step.called_definition() {
                        self.invoke(child, inputs, depth + 1, span)?
                    } else if let Some(operation) = step.operation() {
                        if step.kind() == "apply" {
                            self.operation(operation, inputs, depth + 1)?
                        } else {
                            self.access(operation, inputs, depth + 1, step.kind() == "controlled")?
                        }
                    } else {
                        use Primitive::*;
                        match step.primitive_kind().expect("preflighted finite primitive") {
                            Unit => {
                                if inputs.len() != 1 || !inputs[0].is_empty() {
                                    return Err(invalid(
                                        span,
                                        "Unit map requires one ordinary Unit argument",
                                    ));
                                }
                                self.reserve_operations(1, span)?;
                                let slot = self.raw.register(SourceType::unit(), vec![]);
                                self.raw.operations.push(crate::ir::RawOp::PackUnit {
                                    output: self.raw.registers[&slot].token,
                                });
                                vec![Atom::Quantum(slot)]
                            }
                            Finish => {
                                let [input] = inputs.as_slice() else {
                                    return Err(invalid(
                                        span,
                                        "finish requires one zero-axis owner",
                                    ));
                                };
                                let slot = quantum(input, span)?;
                                self.reserve_operations(1, span)?;
                                let owner = self
                                    .raw
                                    .registers
                                    .remove(&slot)
                                    .ok_or_else(|| invalid(span, "finish owner is absent"))?;
                                if owner.basis != SourceType::unit() || !owner.wires.is_empty() {
                                    return Err(invalid(
                                        span,
                                        "finish changes the exact Unit basis",
                                    ));
                                }
                                self.raw
                                    .operations
                                    .push(crate::ir::RawOp::UnpackUnit { input: owner.token });
                                vec![]
                            }
                            TakeBit | PutBit => self.register_bit(
                                step.primitive_kind() == Some(TakeBit),
                                step,
                                &inputs,
                            )?,
                            EmptyBits => vec![Atom::Register(Arc::from([]))],
                            PrependBit => {
                                let ([Atom::Classical(head)], [Atom::Register(tail)]) =
                                    (inputs[0].as_slice(), inputs[1].as_slice())
                                else {
                                    return Err(invalid(
                                        span,
                                        "packing requires a Bit and ordinary register",
                                    ));
                                };
                                vec![Atom::Register(
                                    std::iter::once(*head).chain(tail.iter().copied()).collect(),
                                )]
                            }
                            Init0 => {
                                self.reserve_operations(1, span)?;
                                self.reserve_qubit(span)?;
                                vec![Atom::Quantum(self.raw.init0())]
                            }
                            H | X | Z => {
                                let slot = quantum(&inputs[0], span)?;
                                self.reserve_operations(1, span)?;
                                let gate = match step.primitive_kind() {
                                    Some(H) => SingleGate::H,
                                    Some(X) => SingleGate::X,
                                    Some(Z) => SingleGate::Z,
                                    _ => unreachable!("matched single gate"),
                                };
                                self.raw.gate_bit(gate, slot).map_err(state_error)?;
                                vec![Atom::Quantum(slot)]
                            }
                            Phase => {
                                let slot = quantum(&inputs[0], span)?;
                                let turns = eighths(step.natural_arguments())
                                    .expect("preflighted exact phase");
                                self.reserve_operations(turns, span)?;
                                for _ in 0..turns {
                                    self.raw
                                        .gate_bit(SingleGate::T, slot)
                                        .map_err(state_error)?;
                                }
                                vec![Atom::Quantum(slot)]
                            }
                            PhaseEighth => {
                                let slot = quantum(&inputs[0], span)?;
                                self.reserve_operations(1, span)?;
                                self.raw.scalar_eighth(slot).map_err(state_error)?;
                                vec![Atom::Quantum(slot)]
                            }
                            Split => {
                                let slot = quantum(&inputs[0], span)?;
                                let fields = step.inputs()[0]
                                    .ty()
                                    .quantum_basis()
                                    .and_then(SourceType::tuple_fields)
                                    .expect("checked exact split basis");
                                let left_bits =
                                    fields[0].basis_width().expect("finite split basis") as usize;
                                self.reserve_operations(1, span)?;
                                self.cells = self.cells.saturating_add(
                                    fields.iter().map(|f| f.tree_size().nodes).sum::<usize>(),
                                );
                                if self.cells > MAX_CELLS {
                                    return Err(Error::new(
                                        "limit",
                                        span,
                                        "finite source lowering exceeds 100000 value cells",
                                    ));
                                }
                                let register =
                                    self.raw.registers.remove(&slot).ok_or_else(|| {
                                        invalid(span, "split source owner is absent")
                                    })?;
                                let left = self.raw.register(
                                    fields[0].clone(),
                                    register.wires[..left_bits].to_vec(),
                                );
                                let right = self.raw.register(
                                    fields[1].clone(),
                                    register.wires[left_bits..].to_vec(),
                                );
                                self.raw.operations.push(crate::ir::RawOp::Split {
                                    input: register.token,
                                    left: self.raw.registers[&left].token,
                                    right: self.raw.registers[&right].token,
                                    left_bits: left_bits as u8,
                                });
                                vec![Atom::Quantum(left), Atom::Quantum(right)]
                            }
                            Join => {
                                let left = quantum(&inputs[0], span)?;
                                let right = quantum(&inputs[1], span)?;
                                if left == right {
                                    return Err(invalid(span, "join source operands alias"));
                                }
                                self.reserve_operations(1, span)?;
                                let left =
                                    self.raw.registers.remove(&left).ok_or_else(|| {
                                        invalid(span, "join left owner is absent")
                                    })?;
                                let right =
                                    self.raw.registers.remove(&right).ok_or_else(|| {
                                        invalid(span, "join right owner is absent")
                                    })?;
                                let basis = step
                                    .output()
                                    .ty()
                                    .quantum_basis()
                                    .expect("checked exact join result");
                                self.cells = self.cells.saturating_add(
                                    basis.tree_size().nodes + left.wires.len() + right.wires.len(),
                                );
                                if self.cells > MAX_CELLS {
                                    return Err(Error::new(
                                        "limit",
                                        span,
                                        "finite source lowering exceeds 100000 value cells",
                                    ));
                                }
                                let wires =
                                    left.wires.iter().chain(&right.wires).copied().collect();
                                let output = self.raw.register(basis.clone(), wires);
                                self.raw.operations.push(crate::ir::RawOp::Join {
                                    left: left.token,
                                    right: right.token,
                                    output: self.raw.registers[&output].token,
                                });
                                vec![Atom::Quantum(output)]
                            }
                            Cnot => {
                                let control = quantum(&inputs[0], span)?;
                                let target = quantum(&inputs[1], span)?;
                                self.reserve_operations(1, span)?;
                                self.raw.cnot(control, target).map_err(state_error)?;
                                vec![Atom::Quantum(control), Atom::Quantum(target)]
                            }
                            MeasureZ => {
                                let slot = quantum(&inputs[0], span)?;
                                self.reserve_operations(1, span)?;
                                vec![Atom::Classical(
                                    self.raw.measure_z(slot).map_err(state_error)?,
                                )]
                            }
                            _ => unreachable!("preflighted finite primitive"),
                        }
                    };
                    bind(step.output(), &output, &mut values, span)?;
                    Ok(())
                })()
                .map_err(|error| error.in_module(step.module()))?;
            }
            self.charge_value(definition.output(), definition.span())?;
            let output = read(definition.output(), &mut values, definition.span())?;
            if values
                .values()
                .any(|value| matches!(value, Atom::Quantum(_)))
            {
                return Err(invalid(
                    definition.span(),
                    "source call drops a quantum owner",
                ));
            }
            Ok(output)
        })()
        .map_err(|error| error.in_module(module))
    }
}

pub(super) fn lower(source: &ElaboratedProgram) -> Result<RawSourceProposal> {
    source.require_unrefined()?;
    let root = &source.definitions()[source.root()];
    let module = root
        .path()
        .rsplit_once("::")
        .map_or(root.path(), |(module, _)| module);
    lower_inner(source, source.root(), None, None, None).map_err(|error| error.in_module(module))
}

/// The only control-enabled emission entry. Append closed original audit roots,
/// require coverage of every original obligation, check all retained concrete
/// control-bearing bodies, then independently check the unchanged selected root.
/// No role is rewritten and no native result is reused as acceptance authority.
pub(super) fn lower_with_kernel(
    source: &ElaboratedProgram,
    kernel: &native::Kernel,
    budget: &mut Budget,
) -> Result<RawSourceProposal> {
    let checked;
    let source = if source.has_function_contracts() && source.require_function_contracts().is_err()
    {
        checked = source.check_function_contracts(kernel, budget)?;
        &checked
    } else {
        source
    };
    source.require_unrefined()?;
    if !source.has_control_obligations() {
        return lower(source);
    }
    lower_refined_with_control(source, kernel, budget)
}

fn lower_refined_with_control(
    source: &ElaboratedProgram,
    kernel: &native::Kernel,
    budget: &mut Budget,
) -> Result<RawSourceProposal> {
    let span = source.definitions()[source.root()].span();
    if budget.remaining() > DEFAULT_EXACT_WORK {
        return Err(Error::new(
            "limit",
            span,
            "source control budget exceeds the shared exact-work ceiling",
        ));
    }
    let audited = super::elaborate::with_control_roots(source, budget)?;
    let checked;
    let source = if let Some(audited) = audited.as_ref() {
        checked = audited.check_function_contracts(kernel, budget)?;
        &checked
    } else {
        source
    };
    // Audit roots can add concrete bindings absent from the selected graph.
    // Check all original requests again in this exact expanded graph; earlier
    // leaf keys are not transplanted across re-elaboration or reused as acceptance.
    let meanings = check_operation_meanings(source, kernel, budget)?.leaves;
    lower_controlled_source(source, kernel, budget, meanings)
}

fn lower_controlled_source(
    source: &ElaboratedProgram,
    kernel: &native::Kernel,
    budget: &mut Budget,
    meanings: Arc<Vec<CheckedMeaning>>,
) -> Result<RawSourceProposal> {
    use crate::frontend::{ast::QuantumAccess, check::ObligationKind};
    let span = source.definitions()[source.root()].span();
    let checked = &source.instantiation().program.checked;
    // The elaborator already bounds this immutable graph. Also bound the
    // number of additional body checks; never create a budget per definition.
    if source.definitions().len() > MAX_CALLS {
        return Err(Error::new(
            "limit",
            span,
            "source control checking exceeds 1024 concrete definitions",
        ));
    }
    let mut retained = BTreeMap::<_, Vec<BTreeSet<_>>>::new();
    let mut subjects = Vec::new();
    for (id, definition) in source.definitions().iter().enumerate() {
        let mut calls = BTreeSet::new();
        for step in definition.steps() {
            budget
                .charge(1)
                .map_err(|e| Error::new("limit", step.span(), e.to_string()))?;
            if step.access_roles().contains(&QuantumAccess::Ctrl) {
                let span = step.span();
                calls.insert((span.start, span.end));
            }
        }
        if !calls.is_empty() {
            subjects.push(id);
        }
        retained.entry(definition.original).or_default().push(calls);
    }
    for obligation in &checked.obligations {
        if !matches!(obligation.kind, ObligationKind::ControlSectors) {
            continue;
        }
        let instances = retained.get(&obligation.definition);
        let mut covered = instances.is_some();
        for calls in instances.into_iter().flatten() {
            budget
                .charge(1)
                .map_err(|e| Error::new("limit", obligation.span, e.to_string()))?;
            covered &= calls.contains(&(obligation.span.start, obligation.span.end));
        }
        if !covered {
            let original = checked.resolution.declaration(obligation.definition);
            return Err(Error::new(
                "unsupported", obligation.span,
                "ctrl source access has no retained concrete call interval; independent sector checking is not yet supported for this original obligation",
            ).in_module(&original.name.0));
        }
    }
    for subject in subjects {
        // Check each specialization, not just one representative per source
        // declaration. Zero-count providers still retain their original body.
        let definition = &source.definitions()[subject];
        let module = definition
            .path()
            .rsplit_once("::")
            .map_or(definition.path(), |(module, _)| module);
        lower_inner(
            source,
            subject,
            None,
            None,
            Some((kernel, budget, &meanings)),
        )
        .map_err(|error| error.in_module(module))?;
    }
    let root = &source.definitions()[source.root()];
    let module = root
        .path()
        .rsplit_once("::")
        .map_or(root.path(), |(module, _)| module);
    let mut proposal = lower_inner(
        source,
        source.root(),
        None,
        None,
        Some((kernel, budget, &meanings)),
    )
    .map_err(|error| error.in_module(module))?;
    if !meanings.is_empty() {
        proposal.meanings = Some(meanings);
    }
    Ok(proposal)
}

pub(super) fn lower_operation(
    source: &ElaboratedProgram,
    caller_id: usize,
    name: &str,
) -> Result<RawSourceProposal> {
    source.require_function_contracts()?;
    lower_operation_site(
        source,
        OperationSite::Binding(caller_id, name.into()),
        0,
        None,
    )
}

fn lower_operation_site(
    source: &ElaboratedProgram,
    site: OperationSite,
    operation_depth: usize,
    checking: Option<(&native::Kernel, &mut Budget, &[CheckedMeaning])>,
) -> Result<RawSourceProposal> {
    let caller_id = site.caller();
    let caller = source.definitions().get(caller_id).ok_or_else(|| {
        invalid(
            Span::default(),
            "operation caller is absent from its original source graph",
        )
    })?;
    if operation_depth > MAX_DEPTH {
        return Err(Error::new(
            "limit",
            caller.span(),
            "Raw operation exceeds existing depth bound",
        ));
    }
    let op = site.select(source, operation_depth).ok_or_else(|| {
        located(
            source,
            caller_id,
            caller.span(),
            "unknown original operation site or descendant",
        )
    })?;
    let mut base = op;
    let mut depth = 0;
    while let Some(child) = base.child() {
        depth += 1;
        if depth > MAX_DEPTH {
            return Err(Error::new(
                "limit",
                op.span(),
                "Raw operation exceeds existing depth bound",
            ));
        }
        base = child;
    }
    let subject = base.definition().unwrap_or(caller_id);
    let (ports, operation_effect, _) = operation_signature(op, source.definitions(), op.span())?;
    if !supported(ports.input) || !supported(ports.output) {
        return Err(located(
            source,
            caller_id,
            op.span(),
            "Raw operation requires closed finite quantum ports",
        ));
    }
    let mut selected = BTreeSet::new();
    let mut pending = Vec::new();
    let mut cells = 0usize;
    let mut operations = vec![(op, 0usize)];
    while let Some((operation, depth)) = operations.pop() {
        cells = cells.saturating_add(1);
        if depth > MAX_DEPTH || cells > MAX_CELLS {
            return Err(Error::new(
                "limit",
                operation.span(),
                "Raw operation dependency depth/cells exceeded",
            ));
        }
        if let Some(id) = operation.definition() {
            pending.push(id);
        }
        for child in operation.children().iter().rev() {
            operations.push((child, depth + 1));
        }
    }
    while let Some(id) = pending.pop() {
        if !selected.insert(id) {
            continue;
        }
        let definition = source.definitions().get(id).ok_or_else(|| {
            invalid(
                caller.span(),
                "operation subject is absent from its original source graph",
            )
        })?;
        cells = cells.saturating_add(1 + definition.steps().len());
        if cells > MAX_CELLS || selected.len() > MAX_CALLS {
            return Err(Error::new(
                "limit",
                caller.span(),
                "Raw operation dependency selection exceeds existing source budgets",
            ));
        }
        for step in definition.steps() {
            if let Some(child) = step.called_definition() {
                pending.push(child);
            }
        }
        // Actual operation arguments are part of the immutable dependency
        // closure even when the body or a repetition never invokes them.
        for operation in definition
            .operations()
            .values()
            .chain(definition.steps().iter().flat_map(|step| {
                step.operation().into_iter().chain(
                    step.operation_bindings()
                        .into_iter()
                        .flat_map(|bindings| bindings.values()),
                )
            }))
        {
            let mut pending_operations = vec![(operation, 0usize)];
            while let Some((operation, depth)) = pending_operations.pop() {
                cells = cells.saturating_add(1);
                if cells > MAX_CELLS || depth > MAX_DEPTH {
                    return Err(Error::new(
                        "limit",
                        operation.span(),
                        "Raw operation dependency selection exceeds existing work/depth bounds",
                    ));
                }
                if let Some(id) = operation.definition() {
                    pending.push(id);
                }
                for child in operation.children().iter().rev() {
                    pending_operations.push((child, depth + 1));
                }
            }
        }
    }
    let definition = &source.definitions()[subject];
    if operation_effect > Effect::Isometry {
        return Err(invalid(
            op.span(),
            "Raw pure operation exceeds its principal effect ceiling",
        ));
    }
    let module = definition
        .path()
        .rsplit_once("::")
        .map_or(definition.path(), |(module, _)| module);
    lower_inner(
        source,
        subject,
        Some(&selected),
        Some((site, operation_depth)),
        checking,
    )
    .map_err(|error| error.in_module(module))
}

fn lower_inner(
    source: &ElaboratedProgram,
    subject: usize,
    selected: Option<&BTreeSet<usize>>,
    binding: Option<(OperationSite, usize)>,
    checking: Option<(&native::Kernel, &mut Budget, &[CheckedMeaning])>,
) -> Result<RawSourceProposal> {
    check_profile(source, selected, checking.is_some())?;
    let root = &source.definitions()[subject];
    let mut emitter = Emitter {
        source,
        meanings: checking.as_ref().map_or(&[], |(_, _, meanings)| *meanings),
        raw: RawState::new(),
        calls: 0,
        cells: 0,
    };
    let operation = binding.as_ref().map(|(site, depth)| {
        site.select(source, *depth)
            .expect("retained original operation site")
    });
    let signature = operation
        .map(|op| operation_signature(op, source.definitions(), op.span()))
        .transpose()?;
    let mut arguments = vec![];
    if let Some((ports, _, _)) = &signature {
        emitter.charge_type(ports.input, root.span())?;
        arguments.push(emitter.input_type(ports.input, root.span())?);
    } else {
        for value in root.inputs() {
            emitter.charge_value(value, root.span())?;
            arguments.push(emitter.input(value, root.span())?);
        }
    }
    let mut quantum_inputs = Vec::new();
    let mut classical_inputs = Vec::new();
    for atom in arguments.iter().flatten() {
        match atom {
            Atom::Classical(id) => classical_inputs.push(*id),
            Atom::Register(ids) => classical_inputs.extend(ids.iter().copied()),
            Atom::Quantum(slot) => {
                let register = &emitter.raw.registers[slot];
                quantum_inputs.push(QuantumPort {
                    token: register.token,
                    wires: register.wires.clone(),
                    shape: BasisShape {
                        bits: register.wires.len() as u8,
                    },
                });
            }
        }
    }
    let outputs = if let Some(op) = operation {
        emitter.operation(op, arguments, 0)?
    } else {
        emitter.invoke(subject, arguments, 0, root.span())?
    };
    let mut quantum_outputs = Vec::new();
    let mut classical_outputs = Vec::new();
    let mut retained = BTreeSet::new();
    for atom in outputs {
        match atom {
            Atom::Classical(id) => classical_outputs.push(id),
            Atom::Register(ids) => classical_outputs.extend(ids.iter().copied()),
            Atom::Quantum(slot) => {
                if !retained.insert(slot) {
                    return Err(invalid(
                        root.span(),
                        "source result duplicates a quantum owner",
                    ));
                }
                let register = emitter.raw.registers.get(&slot).ok_or_else(|| {
                    invalid(
                        root.span(),
                        "source result contains a consumed quantum owner",
                    )
                })?;
                quantum_outputs.push(register.token);
            }
        }
    }
    if retained.len() != emitter.raw.registers.len() {
        return Err(invalid(
            root.span(),
            "source result drops a globally live quantum owner",
        ));
    }
    let raw = RawProgram {
        quantum_inputs,
        classical_inputs,
        operations: emitter.raw.operations,
        quantum_outputs,
        classical_outputs,
        declared_effect: signature
            .as_ref()
            .map_or_else(|| effect(source, subject), |(_, effect, _)| *effect),
    };
    if checking.is_none() {
        preservation::validate_subject(source, subject, operation, &raw)?;
    }
    // A finite request binds the actual artifact's declared type as well as
    // its ports. Retain a unary quantum boundary only for an exact matching
    // source tree; zero width alone never establishes a Unit signature.
    let interface = if let Some((ports, _, _)) = &signature {
        if ports.input == ports.output {
            ports.input.quantum_basis().and_then(finite_basis)
        } else {
            None
        }
    } else {
        match root.inputs() {
            [input] if input.ty() == root.output().ty() => match &input.ty().kind {
                Kind::Q(basis) => finite_basis(basis),
                _ => None,
            },
            _ => None,
        }
    }
    .map(|basis| RootInterface {
        input: basis.clone(),
        output: basis,
    });
    let proposal = native::Proposal::from_raw(&raw, interface.as_ref(), Version::V2, None)
        .map_err(|error| Error::new("transport", root.span(), error.to_string()))?;
    if let Some((kernel, budget, meanings)) = checking {
        // These checks bind the original source roles to decoded, freshly
        // accepted bytes. A valid whole body alone is not sector evidence.
        budget
            .charge(proposal.artifact().len())
            .map_err(|e| Error::new("limit", root.span(), e.to_string()))?;
        let accepted = kernel
            .accept(&proposal)
            .map_err(|e| Error::new(e.code, root.span(), e.to_string()))?;
        budget
            .charge(accepted.native_exact_work())
            .map_err(|e| Error::new("limit", root.span(), e.to_string()))?;
        preservation::validate_subject_with_meanings(
            source,
            subject,
            operation,
            accepted.raw(),
            Some(kernel),
            budget,
            meanings,
        )?;
    }
    let finite_boundary =
        if raw.declared_effect == Effect::Unitary {
            if let Some(interface) = interface {
                // This exact unary source result has one globally live register.
                // Use its actual returned wire order, never just the input width.
                if raw.quantum_inputs.len() != 1
                    || raw.quantum_outputs.len() != 1
                    || emitter.raw.registers.len() != 1
                {
                    return Err(invalid(
                        root.span(),
                        "unary source boundary has a different owner frame",
                    ));
                }
                let output =
                    emitter.raw.registers.values().next().ok_or_else(|| {
                        invalid(root.span(), "missing unary source output register")
                    })?;
                Some(
                    UnitaryBoundary::new(
                        interface.input,
                        raw.quantum_inputs[0].clone(),
                        QuantumPort {
                            token: output.token,
                            wires: output.wires.clone(),
                            shape: BasisShape {
                                bits: output.wires.len() as u8,
                            },
                        },
                    )
                    .map_err(|e| invalid(root.span(), &e.to_string()))?,
                )
            } else {
                None
            }
        } else {
            None
        };
    Ok(RawSourceProposal {
        source: source.clone(),
        subject,
        operation_depth: binding.as_ref().map_or(0, |(_, depth)| *depth),
        binding: binding.map(|(site, _)| site),
        proposal,
        finite_boundary,
        meanings: None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::compile::ParsedProgram;
    use crate::ir::RawOp;

    #[test]
    fn control_audit_collects_new_meanings_in_the_expanded_original_graph() {
        let text = include_str!(
            "../../../tests/fixtures/authoring_sessions/refined-source-control-v030/attempt-01/unused-valid.qli"
        );
        let source = ParsedProgram::parse(BTreeMap::from([("main".into(), text.into())]))
            .unwrap()
            .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap();
        let kernel = native::Kernel::new(std::env::var_os("QLEISLI_KERNEL").unwrap());
        let mut budget = Budget::new(DEFAULT_EXACT_WORK);
        let checked = source
            .check_operation_meanings(&kernel, &mut budget)
            .unwrap();
        assert_eq!(checked.checked_bindings(), 0);
        let raw = checked.lower_raw(&kernel, &mut budget).unwrap();
        assert!(raw.source.definitions().len() > source.definitions().len());
        assert!(!raw.meanings.as_ref().unwrap().is_empty());
        assert_eq!(
            raw.definition().original,
            source.definitions()[source.root()].original
        );
        raw.validate_source_steps(&kernel.accept(raw.proposal()).unwrap())
            .unwrap();
    }

    #[test]
    fn finite_meaning_replay_charges_control_sectors_to_the_callers_budget() {
        let text = "use std::quantum::z;pub fn main(q:Q<Bit>)->Q<Bit>{z(ctrl q);q}";
        let source = ParsedProgram::parse(BTreeMap::from([("main".into(), text.into())]))
            .unwrap()
            .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap();
        let kernel = native::Kernel::new(std::env::var_os("QLEISLI_KERNEL").unwrap());
        let raw = source
            .lower_raw_with_kernel(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK))
            .unwrap();
        let required = FiniteMeaning::phase(BasisType::Bit, vec![0, 4]).unwrap();
        let mut finite_only = Budget::new(DEFAULT_EXACT_WORK);
        let matrix = required.matrix(&mut finite_only).unwrap();
        finite_leaf::check_with_kernel(
            &kernel,
            raw.payload(),
            raw.finite_boundary.as_ref().unwrap(),
            &matrix,
            &mut finite_only,
        )
        .unwrap();
        let cost = DEFAULT_EXACT_WORK - finite_only.remaining();
        // This covers the finite equation, but not the additional fresh sector
        // check during source replay. A hidden default budget would wrongly pass.
        let error = raw
            .check_finite_meaning(&kernel, &required, &mut Budget::new(cost))
            .unwrap_err();
        assert_eq!(error.code(), "limit", "{error}");
        assert!(error.message().contains("ctrl requires"), "{error}");
        raw.check_finite_meaning(&kernel, &required, &mut Budget::new(DEFAULT_EXACT_WORK))
            .unwrap();
    }

    #[test]
    fn raw_meaning_intervals_reject_a_fresh_valid_leaf_for_another_action() {
        let elaborate = |text: &str| {
            ParsedProgram::parse(BTreeMap::from([("main".into(), text.into())]))
                .unwrap()
                .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
                .unwrap()
                .elaborate()
                .unwrap()
        };
        let source = elaborate(
            "use std::quantum::x; classical fn flip(b:Bit)->Bit{not b}
            meaning X:Bit=permutation_by(flip); fn direct(q:Q<Bit>)->Q<Bit>{x(q)}
            fn apply[const U:Op<Bit,X>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}
            pub fn main(q:Q<Bit>)->Q<Bit>{apply[checked_op(direct,X)](q)}",
        );
        let checker = native::Kernel::new(std::env::var_os("QLEISLI_KERNEL").unwrap());
        let checked = source
            .check_operation_meanings(&checker, &mut Budget::new(DEFAULT_EXACT_WORK))
            .unwrap();
        let raw = lower_inner(&source, source.root(), None, None, None).unwrap();
        let accepted = checker.accept(raw.proposal()).unwrap();
        // Both source replay and ordinary native validity succeed for the X
        // artifact. The substituted identity leaves also have genuine fresh
        // native equations, but cannot establish the actual X intervals.
        raw.validate_source_steps(&accepted).unwrap();
        let identity = elaborate("pub fn main(q:Q<Bit>)->Q<Bit>{q}")
            .lower_raw()
            .unwrap();
        let required = FiniteMeaning::permutation(BasisType::Bit, vec![0, 1]).unwrap();
        let foreign = checked
            .leaves
            .iter()
            .map(|(key, _, _)| {
                let check = identity
                    .check_finite_meaning(&checker, &required, &mut Budget::new(DEFAULT_EXACT_WORK))
                    .unwrap();
                (key.clone(), check.leaf, None)
            })
            .collect::<Vec<_>>();
        assert!(!foreign.is_empty());
        let error = preservation::validate_subject_with_meanings(
            &source,
            source.root(),
            None,
            accepted.raw(),
            Some(&checker),
            &mut Budget::new(DEFAULT_EXACT_WORK),
            &foreign,
        )
        .unwrap_err();
        assert_eq!(error.code(), "contract", "{error}");
        assert!(error.message().contains("actual Raw operation interval"));
    }

    #[test]
    fn transformed_raw_meanings_reject_genuine_identity_evidence_for_other_substeps() {
        let checker = native::Kernel::new(std::env::var_os("QLEISLI_KERNEL").unwrap());
        let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/authoring_sessions/refined-raw-access-v030/attempt-01");
        for name in [
            "hidden-inverse",
            "nested-control-inverse",
            "controlled-scalar",
            "reordered-tensor-inverse",
            "hidden-controlled-swap",
        ] {
            let text = std::fs::read_to_string(
                directory
                    .with_file_name(if name == "hidden-controlled-swap" {
                        "attempt-02"
                    } else {
                        "attempt-01"
                    })
                    .join(format!("{name}.qli")),
            )
            .unwrap();
            let source = ParsedProgram::parse(BTreeMap::from([("main".into(), text)]))
                .unwrap()
                .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
                .unwrap()
                .elaborate()
                .unwrap();
            let checked = source
                .check_operation_meanings(&checker, &mut Budget::new(DEFAULT_EXACT_WORK))
                .unwrap();
            let raw = lower_inner(&source, source.root(), None, None, None).unwrap();
            let accepted = checker.accept(raw.proposal()).unwrap();
            raw.validate_source_steps(&accepted).unwrap();
            // Each replacement is a real fresh native equation with the same
            // exact type tree. Only its action differs from the required one.
            let foreign = checked
                .leaves
                .iter()
                .map(|(key, leaf, _)| {
                    let signature = leaf.boundary().signature().clone();
                    let dim = 1usize << signature.bits().unwrap();
                    let identity =
                        FiniteMeaning::permutation(signature.clone(), (0..dim as u16).collect())
                            .unwrap();
                    let target = identity.target_ir().unwrap();
                    let interface = RootInterface {
                        input: signature.clone(),
                        output: signature.clone(),
                    };
                    let proposal =
                        native::Proposal::from_raw(&target, Some(&interface), Version::V2, None)
                            .unwrap();
                    let accepted = checker.accept(&proposal).unwrap();
                    let boundary = UnitaryBoundary::new(
                        signature,
                        target.quantum_inputs[0].clone(),
                        accepted.output_ports()[0].clone(),
                    )
                    .unwrap();
                    let leaf = finite_leaf::check_with_kernel(
                        &checker,
                        proposal.artifact(),
                        &boundary,
                        &identity
                            .matrix(&mut Budget::new(DEFAULT_EXACT_WORK))
                            .unwrap(),
                        &mut Budget::new(DEFAULT_EXACT_WORK),
                    )
                    .unwrap();
                    (key.clone(), leaf, None)
                })
                .collect::<Vec<_>>();
            assert!(!foreign.is_empty());
            let error = preservation::validate_subject_with_meanings(
                &source,
                source.root(),
                None,
                accepted.raw(),
                Some(&checker),
                &mut Budget::new(DEFAULT_EXACT_WORK),
                &foreign,
            )
            .unwrap_err();
            assert_eq!(error.code(), "contract", "{name}: {error}");
            assert!(
                error.message().contains("actual transformed Raw substeps"),
                "{name}: {error}"
            );
        }
    }

    #[test]
    fn checked_operation_bytes_are_used_by_the_actual_emitted_hierarchy() {
        use crate::frontend::compile::{BasisBinding, OperationBinding};
        use crate::interchange::{hierarchical, json};
        use hierarchical::execution::ExecutionLimits;
        let parsed = ParsedProgram::parse(BTreeMap::from([("main".into(),
            "use std::quantum::{x,phase_eighth}; pub unitary fn flip(q:Q<Bit>)->Q<Bit>{x(q)} pub unitary fn scalar(q:Q<Unit>)->Q<Unit>{phase_eighth(phase_eighth(phase_eighth(phase_eighth(q))))} unitary fn inner[const A:Basis,const U:Op<A>](q:Q<A>)->Q<A> requires Applicable(U){U(q)} pub unitary fn outer[const A:Basis,const k:Nat,const U:Op<A>](q:Q<A>)->Q<A> requires Applicable(U),k<=2{inner[A,power(U,k)](q)}".into())])).unwrap();
        let executable = std::env::var_os("QLEISLI_KERNEL").expect("matching native checker");
        let checker = native::Kernel::new(executable.clone());
        let hierarchy_checker = hierarchical::Kernel::new(executable);
        for (basis, provider) in [("Bit", "main::flip"), ("Unit", "main::scalar")] {
            for count in 0..=2 {
                let source = parsed
                    .instantiate_with_types(
                        "main::outer",
                        BTreeMap::from([("A".into(), BasisBinding::parse(basis).unwrap())]),
                        BTreeMap::from([("k".into(), count)]),
                        BTreeMap::from([(
                            "U".into(),
                            OperationBinding::new(provider, BTreeMap::new()),
                        )]),
                    )
                    .unwrap()
                    .elaborate()
                    .unwrap();
                let caller = source
                    .definitions()
                    .iter()
                    .position(|d| d.path() == "main::inner")
                    .unwrap();
                let leaf = source.lower_raw_operation_at(caller, "U").unwrap();
                let required = if basis == "Bit" {
                    FiniteMeaning::permutation(
                        BasisType::Bit,
                        if count == 1 { vec![1, 0] } else { vec![0, 1] },
                    )
                    .unwrap()
                } else {
                    FiniteMeaning::phase(BasisType::Unit, vec![if count == 1 { 4 } else { 0 }])
                        .unwrap()
                };
                let checked = leaf
                    .check_finite_meaning(&checker, &required, &mut Budget::new(DEFAULT_EXACT_WORK))
                    .unwrap();
                let proposal = checked.lower_hierarchy().unwrap();
                let graph = json::parse(proposal.payload()).unwrap();
                let definitions = graph.field("definitions").unwrap().array().unwrap();
                assert!(
                    definitions.iter().any(|d| {
                        let body = d.field("body").unwrap();
                        body.field("tag").unwrap().text().unwrap() == "leaf"
                            && body.field("program").unwrap().text().unwrap().as_bytes()
                                == checked.leaf().payload()
                    }),
                    "actual provider bytes must be in the emitted artifact"
                );
                let actual = hierarchy_checker
                    .check_against_native(proposal.payload(), proposal.comparison_request())
                    .unwrap();
                let input = if basis == "Bit" {
                    vec![[0.1, -0.2], [0.3, 0.4], [-0.5, 0.6], [0.7, -0.8]]
                } else {
                    vec![[0.1, -0.2], [0.3, 0.4]]
                };
                let output = actual
                    .execute_pure(
                        &input,
                        2,
                        ExecutionLimits {
                            max_amplitudes: 16,
                            max_steps: 1000,
                        },
                    )
                    .unwrap()
                    .amplitudes;
                let expected = if basis == "Bit" {
                    (0..input.len())
                        .map(|i| input[i ^ (if count == 1 { 1 } else { 0 })])
                        .collect::<Vec<_>>()
                } else {
                    input
                        .iter()
                        .map(|[a, b]| if count == 1 { [-a, -b] } else { [*a, *b] })
                        .collect()
                };
                for (a, b) in output.iter().flatten().zip(expected.iter().flatten()) {
                    assert!((a - b).abs() < 1e-12, "{basis}, {count}");
                }
                assert_eq!(output.len(), expected.len());
                if basis == "Bit" && count == 2 {
                    // Keep the actual input/output frame, but substitute a
                    // native-valid single X for the checked X^2 body. The
                    // emitted matrix request must reject the new artifact.
                    let mut wrong = checked.leaf().program().raw().clone();
                    wrong.operations.remove(0);
                    let RawOp::Gate { input, .. } = &mut wrong.operations[0] else {
                        panic!("X gate")
                    };
                    *input = wrong.quantum_inputs[0].token;
                    let wrong = native::Proposal::from_raw(
                        &wrong,
                        Some(&RootInterface {
                            input: BasisType::Bit,
                            output: BasisType::Bit,
                        }),
                        Version::V2,
                        None,
                    )
                    .unwrap();
                    checker.accept(&wrong).unwrap();
                    let mut changed = json::parse(proposal.payload()).unwrap();
                    let json::Value::Object(root) = &mut changed else {
                        panic!("graph")
                    };
                    let json::Value::Array(definitions) = root.get_mut("definitions").unwrap()
                    else {
                        panic!("definitions")
                    };
                    let mut replaced = 0;
                    for definition in definitions {
                        let json::Value::Object(fields) = definition else {
                            panic!("definition")
                        };
                        let json::Value::Object(body) = fields.get_mut("body").unwrap() else {
                            panic!("body")
                        };
                        if body.get("program")
                            == Some(&json::Value::String(
                                std::str::from_utf8(checked.leaf().payload())
                                    .unwrap()
                                    .into(),
                            ))
                        {
                            body.insert(
                                "program".into(),
                                json::Value::String(
                                    std::str::from_utf8(wrong.artifact()).unwrap().into(),
                                ),
                            );
                            replaced += 1;
                        }
                    }
                    assert_eq!(replaced, 1);
                    let error = hierarchy_checker
                        .check_against_native(
                            &json::encode(&changed).unwrap(),
                            proposal.comparison_request(),
                        )
                        .unwrap_err();
                    assert_eq!(error.code, "contract", "{error}");
                }
            }
        }
    }

    #[test]
    fn repeated_subject_replay_rejects_its_native_valid_base_artifact() {
        use crate::frontend::compile::OperationBinding;
        let source = ParsedProgram::parse(BTreeMap::from([("main".into(),
            "use std::quantum::x; pub unitary fn flip(q:Q<Bit>)->Q<Bit>{x(q)} unitary fn inner[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){q} pub unitary fn outer[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){inner[power(U,2)](q)}".into())]))
            .unwrap().instantiate("main::outer", BTreeMap::new(), BTreeMap::from([("U".into(), OperationBinding::new("main::flip", BTreeMap::new()))])).unwrap().elaborate().unwrap();
        let caller = source
            .definitions()
            .iter()
            .position(|d| d.path() == "main::inner")
            .unwrap();
        let mut repeated = source.lower_raw_operation_at(caller, "U").unwrap();
        let base = source.lower_raw_operation("U").unwrap();
        // Model a producer substituting both valid bytes and a matching port
        // boundary. Its claim still must replay the retained X^2 subject.
        repeated.proposal = base.proposal;
        repeated.finite_boundary = base.finite_boundary;
        let required = FiniteMeaning::permutation(BasisType::Bit, vec![1, 0]).unwrap();
        let checker = native::Kernel::new(
            std::env::var_os("QLEISLI_KERNEL").expect("matching native checker"),
        );
        finite_leaf::check_with_kernel(
            &checker,
            repeated.payload(),
            repeated.finite_boundary.as_ref().unwrap(),
            &required
                .matrix(&mut Budget::new(DEFAULT_EXACT_WORK))
                .unwrap(),
            &mut Budget::new(DEFAULT_EXACT_WORK),
        )
        .unwrap();
        let error = repeated
            .check_finite_meaning(&checker, &required, &mut Budget::new(DEFAULT_EXACT_WORK))
            .unwrap_err();
        assert_eq!(error.code(), "preservation", "{error}");
    }

    #[test]
    fn source_meaning_gate_rejects_a_native_valid_replaced_provider() {
        let source = ParsedProgram::parse(BTreeMap::from([(
            "main".into(),
            "use std::quantum::x; pub unitary fn implementation(q:Q<Bit>)->Q<Bit>{x(q)}".into(),
        )]))
        .unwrap()
        .instantiate("main::implementation", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap();
        let mut proposal = source.lower_raw().unwrap();
        let required = FiniteMeaning::permutation(BasisType::Bit, vec![0, 1]).unwrap();
        proposal.proposal = native::Proposal::from_raw(
            &required.target_ir().unwrap(),
            Some(&RootInterface {
                input: BasisType::Bit,
                output: BasisType::Bit,
            }),
            Version::V2,
            None,
        )
        .unwrap();
        let kernel = native::Kernel::new(
            std::env::var_os("QLEISLI_KERNEL").expect("matching native checker"),
        );
        let matrix = required
            .matrix(&mut Budget::new(DEFAULT_EXACT_WORK))
            .unwrap();
        // The replacement even satisfies its own requested equation. This
        // cannot establish correspondence to the retained X source steps.
        finite_leaf::check_with_kernel(
            &kernel,
            proposal.payload(),
            proposal.finite_boundary.as_ref().unwrap(),
            &matrix,
            &mut Budget::new(DEFAULT_EXACT_WORK),
        )
        .unwrap();
        let error = proposal
            .check_finite_meaning(&kernel, &required, &mut Budget::new(DEFAULT_EXACT_WORK))
            .unwrap_err();
        assert_eq!(error.code(), "preservation", "{error}");
    }

    #[test]
    fn raw_source_replay_rejects_noncommuting_gate_reordering() {
        use crate::ir::SingleGate;
        let text =
            "use std::quantum::{h,z};pub unitary fn main(q:Q<Bit>)->Q<Bit>{h(excl q);z(excl q);q}";
        let source = ParsedProgram::parse(BTreeMap::from([("main".into(), text.into())]))
            .unwrap()
            .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap();
        let proposal = source.lower_raw().unwrap();
        let kernel = native::Kernel::selected().unwrap();
        let accepted = kernel.accept(proposal.proposal()).unwrap();
        preservation::validate(&source, accepted.raw()).unwrap();
        let mut wrong = accepted.raw().clone();
        assert_eq!(wrong.operations.len(), 2);
        // Keep every token edge and the exact type/effect interface valid,
        // while exchanging only the gate actions on that ordered chain.
        for (op, replacement) in wrong
            .operations
            .iter_mut()
            .zip([SingleGate::Z, SingleGate::H])
        {
            let RawOp::Gate { gate, .. } = op else {
                panic!("gate chain")
            };
            *gate = replacement;
        }
        let wrong = kernel.accept_raw(wrong).unwrap();
        // Direct opcode replay must reject, independently of the enclosing
        // proposal's artifact-identity comparison and ordinary native validity.
        assert_eq!(
            preservation::validate(&source, wrong.raw())
                .unwrap_err()
                .code(),
            "preservation"
        );
    }

    fn example() -> ElaboratedProgram {
        ParsedProgram::parse(BTreeMap::from([(
            "main".into(),
            "unitary fn f((a,b): (Bit,Bit)) -> (Bit,Bit,Bit) { (not a, a and b, a xor b) }\n\
             pub observe fn main() -> (Bit,Bit,Bit) { f((1,1)) }"
                .into(),
        )]))
        .unwrap()
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap()
    }

    #[test]
    fn raw_source_replay_rejects_native_valid_semantic_and_structural_mutations() {
        let source = example();
        let proposal = source.lower_raw().unwrap();
        let kernel = native::Kernel::new(
            std::env::var_os("QLEISLI_KERNEL").expect("select the matching native checker"),
        );
        let accepted = kernel.accept(proposal.proposal()).unwrap();
        proposal.validate_source_steps(&accepted).unwrap();
        let original = accepted.raw();
        let mut mutations = vec![];
        let mut changed = original.clone();
        let index = changed
            .operations
            .iter()
            .position(|op| matches!(op, RawOp::ClassicalAnd { .. }))
            .unwrap();
        let RawOp::ClassicalAnd {
            left,
            right,
            output,
        } = &changed.operations[index]
        else {
            unreachable!()
        };
        changed.operations[index] = RawOp::ClassicalXor {
            left: *left,
            right: *right,
            output: *output,
        };
        mutations.push(("and changed to xor", changed));

        let mut changed = original.clone();
        let RawOp::ClassicalConst { value, .. } = &mut changed.operations[0] else {
            unreachable!()
        };
        *value = !*value;
        mutations.push(("literal substituted", changed));

        let mut changed = original.clone();
        changed.operations.push(RawOp::ClassicalConst {
            value: true,
            output: ClassicalId(900),
        });
        mutations.push(("extra unused operation", changed));

        let mut changed = original.clone();
        changed.classical_outputs.reverse();
        mutations.push(("output order reversed", changed));

        for (name, raw) in mutations {
            let accepted_mutation = kernel.accept_raw(raw).expect(name);
            // Exercise the direct opcode/tree matcher, not just the proposal's
            // outer byte-identity check. These programs remain native-valid.
            let error = preservation::validate(&source, accepted_mutation.raw()).expect_err(name);
            assert_eq!(error.code(), "preservation", "{name}: {error}");
            assert!(
                proposal.validate_source_steps(&accepted_mutation).is_err(),
                "{name}"
            );
        }
    }
}
