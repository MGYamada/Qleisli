//! Independently checked meanings for concrete unary unitary functions.
//!
//! This module extracts circuit semantics from independently verified raw IR.
//! It deliberately does not call the frontend's flattening implementation.
//! Source snapshots identify the compiler input; they do not establish the
//! still separate theorem that Rust lowering implements that source.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::sync::{Arc, OnceLock};

use super::exact::{Budget, Matrix};
use super::{
    BasisType, Circuit, ContractDiagnostic, ContractError, MAX_CONTRACT_BITS, MAX_CONTRACT_STEPS,
};
use crate::ir::*;

pub const MAX_FUNCTION_DEPTH: usize = 32;
pub const MAX_FUNCTION_SOURCES: usize = 128;
pub const MAX_FUNCTION_SOURCE_BYTES: usize = 1_048_576;
pub const MAX_FUNCTION_EXPANDED_STEPS: usize = 1_000_000;
pub(crate) const MAX_IDENTITY_NAME_BYTES: usize = 4096;

/// Exact source metadata attached to an implementation/specification pair.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionIdentity {
    pub implementation: String,
    pub specification: String,
    pub sources: Vec<(String, String)>,
}

/// Untrusted metadata storage; every evidence constructor still validates it.
/// The frontend shares one frozen project without changing the public owned API.
pub(crate) enum RetainedIdentity {
    Owned(FunctionIdentity),
    Shared {
        implementation: String,
        specification: String,
        sources: Arc<Vec<(String, String)>>,
        exposed: OnceLock<FunctionIdentity>,
    },
}

impl RetainedIdentity {
    pub(crate) fn shared(
        implementation: String,
        specification: String,
        sources: Arc<Vec<(String, String)>>,
    ) -> Self {
        Self::Shared {
            implementation,
            specification,
            sources,
            exposed: OnceLock::new(),
        }
    }

    pub(crate) fn parts(&self) -> (&str, &str, &[(String, String)]) {
        match self {
            Self::Owned(identity) => (
                &identity.implementation,
                &identity.specification,
                &identity.sources,
            ),
            Self::Shared {
                implementation,
                specification,
                sources,
                ..
            } => (implementation, specification, sources),
        }
    }

    fn exposed(&self) -> &FunctionIdentity {
        match self {
            Self::Owned(identity) => identity,
            Self::Shared {
                implementation,
                specification,
                sources,
                exposed,
            } => exposed.get_or_init(|| FunctionIdentity {
                implementation: implementation.clone(),
                specification: specification.clone(),
                sources: sources.as_ref().clone(),
            }),
        }
    }

    fn matches(&self, identity: &FunctionIdentity) -> bool {
        let (implementation, specification, sources) = self.parts();
        identity.implementation == implementation
            && identity.specification == specification
            && identity.sources == sources
    }
}

/// Native acceptance of two concrete raw functions with equal exact meaning.
///
/// All fields are private. Cloning evidence preserves its checked raw snapshots
/// and dependency graph. A function call may reuse `meaning` without evaluating
/// the function body again. Identity includes global phase and output ordering.
/// `Eq` compares issued proof identities: clones are equal, independently
/// checked receipts are distinct even when their snapshots are identical.
#[derive(Clone)]
pub struct FunctionEvidence {
    signature: BasisType,
    implementation: RawProgram,
    specification: RawProgram,
    identity: Arc<RetainedIdentity>,
    circuit: Circuit,
    meaning: Matrix,
    depth: usize,
    expanded_steps: usize,
    proof_identity: Arc<()>,
    native: Arc<crate::interchange::native::NativeChecked>,
    snapshot_key: Arc<[u8]>,
}

// Proof dependencies are issued identities, not recursively expanded trees.
// A clone keeps its identity; a separately checked proof is a new dependency.
// This makes raw snapshot comparison bounded even for highly shared DAGs.
impl PartialEq for FunctionEvidence {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.proof_identity, &other.proof_identity)
    }
}

impl Eq for FunctionEvidence {}

impl fmt::Debug for FunctionEvidence {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (implementation, specification, _) = self.identity.parts();
        f.debug_struct("FunctionEvidence")
            .field("signature", &self.signature)
            .field("implementation", &implementation)
            .field("specification", &specification)
            .field("depth", &self.depth)
            .field("expanded_steps", &self.expanded_steps)
            .finish_non_exhaustive()
    }
}

impl FunctionEvidence {
    pub fn check(
        signature: BasisType,
        implementation: RawProgram,
        specification: RawProgram,
        identity: FunctionIdentity,
        budget: &mut Budget,
    ) -> Result<Self, ContractError> {
        Self::check_diagnostic(signature, implementation, specification, identity, budget)
            .map_err(|diagnostic| diagnostic.error)
    }

    pub(crate) fn check_diagnostic(
        signature: BasisType,
        implementation: RawProgram,
        specification: RawProgram,
        identity: FunctionIdentity,
        budget: &mut Budget,
    ) -> Result<Self, ContractDiagnostic> {
        Self::check_retained_diagnostic(
            signature,
            implementation,
            specification,
            RetainedIdentity::Owned(identity),
            budget,
        )
    }

    pub(crate) fn check_retained_diagnostic(
        signature: BasisType,
        implementation: RawProgram,
        specification: RawProgram,
        identity: RetainedIdentity,
        budget: &mut Budget,
    ) -> Result<Self, ContractDiagnostic> {
        let kernel = crate::interchange::native::Kernel::selected().map_err(native_error)?;
        Self::check_retained_with_kernel(
            &kernel,
            signature,
            implementation,
            specification,
            identity,
            budget,
        )
    }

    pub(crate) fn check_retained_with_kernel(
        kernel: &crate::interchange::native::Kernel,
        signature: BasisType,
        implementation: RawProgram,
        specification: RawProgram,
        identity: RetainedIdentity,
        budget: &mut Budget,
    ) -> Result<Self, ContractDiagnostic> {
        validate_identity(&identity, budget)?;
        // Keep the untrusted trees borrowed until transport has checked their
        // capacity. Cloning here would recurse before its depth checks run.
        kernel
            .function_evidence(
                &signature,
                &implementation,
                &specification,
                identity,
                budget,
            )
            .map_err(|failure| {
                let error = native_error(failure);
                let detail = if error == ContractError::EquationMismatch {
                    (|| {
                        let bits = signature.bits()?;
                        preflight(&implementation, bits, budget)?;
                        preflight(&specification, bits, budget)?;
                        let a = extract(&implementation, &signature, budget)?.matrix(budget)?;
                        let b = extract(&specification, &signature, budget)?.matrix(budget)?;
                        Ok::<_, ContractError>(super::equation_counterexample(&a, &b))
                    })()
                    .ok()
                    .flatten()
                } else {
                    None
                };
                ContractDiagnostic { error, detail }
            })
    }

    /// Decode a view of an entry in a freshly accepted artifact. This constructor
    /// is internal; only the native artifact decoder supplies its bound fields.
    pub(crate) fn decode_native(
        ticket: &crate::interchange::native::NativeChecked,
        signature: BasisType,
        implementation: RawProgram,
        specification: RawProgram,
        identity: RetainedIdentity,
        budget: &mut Budget,
    ) -> Result<Self, ContractDiagnostic> {
        let bits = signature.bits()?;
        validate_identity(&identity, budget)?;
        let depth =
            preflight(&implementation, bits, budget)?.max(preflight(&specification, bits, budget)?);
        let circuit = extract(&implementation, &signature, budget)?;
        let specified = extract(&specification, &signature, budget)?;
        let expanded_steps = expanded_steps(&circuit)?;
        // Execution cache, never a Rust equation/isometry acceptance decision.
        let meaning = specified.matrix(budget)?;
        let snapshot_key = crate::interchange::function_snapshot_key(
            &signature,
            &implementation,
            &specification,
            identity.parts(),
        )
        .map_err(native_error)?;
        Ok(Self {
            signature,
            implementation,
            specification,
            identity: Arc::new(identity),
            circuit,
            meaning,
            depth,
            expanded_steps,
            proof_identity: Arc::new(()),
            native: Arc::new(ticket.clone()),
            snapshot_key,
        })
    }

    /// Reuse producer source storage only after matching native-decoded metadata.
    pub(crate) fn retain_identity(
        mut self,
        identity: RetainedIdentity,
    ) -> Result<Self, ContractError> {
        if self.identity.parts() != identity.parts() {
            return Err(ContractError::EvidenceMismatch);
        }
        self.identity = Arc::new(identity);
        Ok(self)
    }

    pub(crate) fn snapshot_key(&self) -> &Arc<[u8]> {
        &self.snapshot_key
    }

    pub fn checker(&self) -> &std::path::Path {
        self.native.checker()
    }

    pub fn signature(&self) -> &BasisType {
        &self.signature
    }
    pub fn implementation(&self) -> &RawProgram {
        &self.implementation
    }
    pub fn specification(&self) -> &RawProgram {
        &self.specification
    }
    /// Inspect exact source metadata. Frontend receipts lazily materialize this
    /// owned compatibility view once; normal checking, cloning and execution
    /// share the frozen snapshot without this copy. Evidence clones share the
    /// same view, and the original metadata limits bound its allocation.
    pub fn identity(&self) -> &FunctionIdentity {
        self.identity.exposed()
    }
    /// Borrow transport metadata without materializing the owned public view.
    pub(crate) fn identity_parts(&self) -> (&str, &str, &[(String, String)]) {
        self.identity.parts()
    }
    pub fn circuit(&self) -> &Circuit {
        &self.circuit
    }
    pub fn meaning(&self) -> &Matrix {
        &self.meaning
    }
    pub fn depth(&self) -> usize {
        self.depth
    }
    pub fn expanded_steps(&self) -> usize {
        self.expanded_steps
    }

    /// Check exact attachment of the basis tree, both raw functions and source bytes.
    /// Equal bit widths do not identify different tuple trees or Unit factors.
    pub fn check_binding(
        &self,
        signature: &BasisType,
        identity: &FunctionIdentity,
        implementation: &RawProgram,
        specification: &RawProgram,
    ) -> Result<(), ContractError> {
        if signature != &self.signature
            || !self.identity.matches(identity)
            || !same_snapshot(implementation, &self.implementation)?
            || !same_snapshot(specification, &self.specification)?
        {
            return Err(ContractError::EvidenceMismatch);
        }
        Ok(())
    }
}

// Fresh native decoding assigns fresh receipt identities. Bind complete canonical
// graph bytes rather than treating host Arc identity as semantic/source evidence.
fn same_snapshot(a: &RawProgram, b: &RawProgram) -> Result<bool, ContractError> {
    use crate::interchange::{Version, native::Proposal};
    Ok(Proposal::from_raw(a, None, Version::V2, None)
        .map_err(native_error)?
        .artifact()
        == Proposal::from_raw(b, None, Version::V2, None)
            .map_err(native_error)?
            .artifact())
}

fn native_error(error: crate::interchange::Error) -> ContractError {
    if error.code == "limit" {
        ContractError::Limit("native function checking exceeded its bounded profile")
    } else if error.code == "contract" {
        ContractError::EquationMismatch
    } else {
        ContractError::InvalidCircuit(error.to_string())
    }
}

fn expanded_steps(circuit: &Circuit) -> Result<usize, ContractError> {
    let mut total = 0usize;
    for step in circuit.steps() {
        let cost = match &step.action {
            CircuitAction::Contract { evidence, .. } => evidence.expanded_steps(),
            _ => 1,
        };
        total = total
            .checked_add(cost)
            .ok_or(ContractError::Limit("function expansion size overflow"))?;
        bounded(total, MAX_FUNCTION_EXPANDED_STEPS)?;
    }
    Ok(total.max(1))
}

fn validate_identity(
    identity: &RetainedIdentity,
    budget: &mut Budget,
) -> Result<(), ContractError> {
    let (implementation, specification, sources) = identity.parts();
    if implementation.is_empty()
        || specification.is_empty()
        || implementation.len() > MAX_IDENTITY_NAME_BYTES
        || specification.len() > MAX_IDENTITY_NAME_BYTES
        || sources.len() > MAX_FUNCTION_SOURCES
    {
        return Err(ContractError::Limit(
            "function identity exceeds its metadata profile",
        ));
    }
    let mut bytes = implementation.len() + specification.len();
    let mut names = BTreeSet::new();
    for (name, source) in sources {
        if name.len() > MAX_IDENTITY_NAME_BYTES || !names.insert(name) {
            return Err(ContractError::Type(
                "source identity paths must be bounded and unique",
            ));
        }
        bytes = bytes
            .checked_add(name.len())
            .and_then(|n| n.checked_add(source.len()))
            .ok_or(ContractError::Limit("source identity size overflow"))?;
        if bytes > MAX_FUNCTION_SOURCE_BYTES {
            return Err(ContractError::Limit(
                "function source identity exceeds 1 MiB",
            ));
        }
    }
    match identity {
        RetainedIdentity::Owned(_) => budget.charge(bytes)?,
        RetainedIdentity::Shared { sources, .. } => {
            let names = implementation.len() + specification.len();
            budget.charge_source_storage(sources, bytes - names)?;
            // Recheck every identity's bounds and path uniqueness above. The
            // immutable source bytes are retained, not copied for each receipt.
            budget.charge(
                names
                    + sources
                        .iter()
                        .map(|(name, _)| name.len() + 1)
                        .sum::<usize>(),
            )?;
        }
    }
    Ok(())
}

fn bounded(len: usize, limit: usize) -> Result<(), ContractError> {
    if len > limit {
        Err(ContractError::Limit(
            "function evidence exceeds its finite IR profile",
        ))
    } else {
        Ok(())
    }
}

/// Check all owned inputs before a clone, recursion, or evidence comparison.
fn preflight(raw: &RawProgram, bits: usize, budget: &mut Budget) -> Result<usize, ContractError> {
    if raw.declared_effect != Effect::Unitary
        || raw.quantum_inputs.len() != 1
        || raw.quantum_outputs.len() != 1
        || !raw.classical_inputs.is_empty()
        || !raw.classical_outputs.is_empty()
        || raw.quantum_inputs[0].wires.len() != bits
        || usize::from(raw.quantum_inputs[0].shape.bits) != bits
    {
        return Err(ContractError::Type(
            "function evidence requires one quantum input/output of the signature width and no classical ports",
        ));
    }
    let mut pending = vec![(raw.operations.as_slice(), 0usize)];
    let mut count = 0usize;
    let mut circuit_steps = 0usize;
    let mut depth = 1;
    while let Some((operations, nesting)) = pending.pop() {
        bounded(nesting, MAX_FUNCTION_DEPTH)?;
        count = count
            .checked_add(operations.len())
            .ok_or(ContractError::Limit("function operation count overflow"))?;
        bounded(count, MAX_CONTRACT_STEPS)?;
        budget.charge(operations.len())?;
        for op in operations {
            match op {
                RawOp::ApplyUnitary { steps, .. } => {
                    inspect_steps(steps, &mut circuit_steps, &mut depth, budget)?;
                }
                RawOp::CertifiedCompute {
                    ancilla_wires,
                    function,
                    use_steps,
                    logical_steps,
                    ..
                } => {
                    bounded(ancilla_wires.len(), MAX_CONTRACT_BITS)?;
                    bounded(function.len(), 1 << MAX_CONTRACT_BITS)?;
                    inspect_steps(use_steps, &mut circuit_steps, &mut depth, budget)?;
                    inspect_steps(logical_steps, &mut circuit_steps, &mut depth, budget)?;
                    budget.charge(ancilla_wires.len() + function.len())?;
                }
                RawOp::QuantumIf {
                    zero_ops, one_ops, ..
                } => {
                    circuit_steps = circuit_steps
                        .checked_add(zero_ops.len())
                        .and_then(|n| n.checked_add(one_ops.len()))
                        .ok_or(ContractError::Limit("function circuit size overflow"))?;
                    bounded(circuit_steps, MAX_CONTRACT_STEPS)?;
                    budget.charge(zero_ops.len() + one_ops.len())?;
                }
                RawOp::LiftBasis {
                    output_wires,
                    table,
                    ..
                } => {
                    bounded(output_wires.len(), MAX_CONTRACT_BITS)?;
                    bounded(table.len(), 1 << MAX_CONTRACT_BITS)?;
                    budget.charge(output_wires.len() + table.len())?;
                }
                RawOp::ClassicalBranch {
                    then_ops,
                    else_ops,
                    quantum_phis,
                    classical_phis,
                    ..
                } => {
                    bounded(quantum_phis.len(), MAX_CONTRACT_STEPS)?;
                    bounded(classical_phis.len(), MAX_CONTRACT_STEPS)?;
                    for phi in quantum_phis {
                        bounded(phi.output_wires.len(), MAX_CONTRACT_BITS)?;
                        budget.charge(phi.output_wires.len())?;
                    }
                    budget.charge(quantum_phis.len() + classical_phis.len())?;
                    pending.extend([
                        (then_ops.as_slice(), nesting + 1),
                        (else_ops.as_slice(), nesting + 1),
                    ]);
                }
                RawOp::ComputeUseUncompute {
                    targets,
                    ancilla_wires,
                    function,
                    use_ops,
                    ..
                } => {
                    bounded(targets.len(), MAX_CONTRACT_BITS)?;
                    bounded(ancilla_wires.len(), MAX_CONTRACT_BITS)?;
                    bounded(function.len(), 1 << MAX_CONTRACT_BITS)?;
                    bounded(use_ops.len(), MAX_CONTRACT_STEPS)?;
                    for usage in use_ops {
                        match usage {
                            ProtectedUse::ControlledTargetGate { controls, .. }
                            | ProtectedUse::ControlledPhase { controls, .. } => {
                                bounded(controls.len(), 2 * MAX_CONTRACT_BITS)?;
                                budget.charge(controls.len())?;
                            }
                            ProtectedUse::ProtectedGate { .. } => (),
                        }
                    }
                    budget.charge(
                        targets.len() + ancilla_wires.len() + function.len() + use_ops.len(),
                    )?;
                }
                RawOp::Init0 { .. }
                | RawOp::MeasureZ { .. }
                | RawOp::Reset { .. }
                | RawOp::Discard { .. } => {
                    return Err(ContractError::Type(
                        "function evidence does not admit preparation or observation",
                    ));
                }
                _ => (),
            }
        }
    }
    Ok(depth)
}

fn inspect_steps(
    steps: &[CircuitStep],
    count: &mut usize,
    depth: &mut usize,
    budget: &mut Budget,
) -> Result<(), ContractError> {
    *count = count
        .checked_add(steps.len())
        .ok_or(ContractError::Limit("function circuit size overflow"))?;
    bounded(*count, MAX_CONTRACT_STEPS)?;
    for step in steps {
        bounded(step.controls.len(), MAX_CONTRACT_BITS)?;
        budget.charge(1 + step.controls.len())?;
        match &step.action {
            CircuitAction::Hadamard { .. } => (),
            CircuitAction::Monomial {
                indices,
                permutation,
                phases,
            } => {
                bounded(indices.len(), MAX_CONTRACT_BITS)?;
                bounded(permutation.len(), 1 << MAX_CONTRACT_BITS)?;
                bounded(phases.len(), 1 << MAX_CONTRACT_BITS)?;
                budget.charge(indices.len() + permutation.len() + phases.len())?;
            }
            CircuitAction::Contract {
                indices, evidence, ..
            } => {
                bounded(indices.len(), MAX_CONTRACT_BITS)?;
                *depth = (*depth).max(evidence.depth() + 1);
                bounded(*depth, MAX_FUNCTION_DEPTH)?;
                budget.charge(indices.len())?;
            }
        }
    }
    Ok(())
}

/// Independent finite denotation of a verified unary unitary. This exposes no
/// evidence constructor and does not trust frontend circuit flattening.
pub(crate) fn verified_meaning(
    verified: &crate::AcceptedProgram,
    signature: &BasisType,
    budget: &mut Budget,
) -> Result<Matrix, ContractError> {
    let bits = signature.bits()?;
    preflight(verified.raw(), bits, budget)?;
    let circuit = extract(verified.raw(), signature, budget)?;
    expanded_steps(&circuit)?;
    circuit.matrix(budget)
}

fn extract(
    raw: &RawProgram,
    signature: &BasisType,
    budget: &mut Budget,
) -> Result<Circuit, ContractError> {
    let bits = signature.bits()?;
    let mut state = Extraction {
        registers: BTreeMap::from([(raw.quantum_inputs[0].token, (0..bits).collect())]),
        classical: BTreeMap::new(),
        steps: vec![],
        budget,
    };
    state.operations(&raw.operations)?;
    let axes = state.take(raw.quantum_outputs[0])?;
    if !state.registers.is_empty() || axes.len() != bits {
        return Err(ContractError::Type(
            "function output does not preserve the complete quantum interface",
        ));
    }
    if axes.iter().copied().ne(0..bits) {
        // The result's coordinate order is semantic, even for an otherwise
        // empty split/join body. Reindex the final amplitudes explicitly.
        let dimension = 1usize << bits;
        state.budget.charge(dimension * (bits + 1))?;
        let permutation = (0..dimension)
            .map(|label| {
                axes.iter().enumerate().fold(0u16, |out, (place, axis)| {
                    out | ((((label >> axis) & 1) as u16) << place)
                })
            })
            .collect();
        state.push(CircuitStep {
            controls: vec![],
            action: CircuitAction::Monomial {
                indices: (0..bits).collect(),
                permutation,
                phases: vec![0; dimension],
            },
        })?;
    }
    Circuit::new(signature.clone(), state.steps)
}

struct Extraction<'a> {
    registers: BTreeMap<TokenId, Vec<usize>>,
    classical: BTreeMap<ClassicalId, bool>,
    steps: Vec<CircuitStep>,
    budget: &'a mut Budget,
}

fn invalid(message: &'static str) -> ContractError {
    ContractError::InvalidCircuit(message.into())
}

impl Extraction<'_> {
    fn take(&mut self, token: TokenId) -> Result<Vec<usize>, ContractError> {
        self.registers
            .remove(&token)
            .ok_or_else(|| invalid("missing live register during independent extraction"))
    }

    fn bit(&self, id: ClassicalId) -> Result<bool, ContractError> {
        self.classical
            .get(&id)
            .copied()
            .ok_or_else(|| invalid("non-closed classical value during independent extraction"))
    }

    fn push(&mut self, step: CircuitStep) -> Result<(), ContractError> {
        bounded(self.steps.len() + 1, MAX_CONTRACT_STEPS)?;
        self.budget.charge(1 + step.controls.len())?;
        self.steps.push(step);
        Ok(())
    }

    fn operations(&mut self, operations: &[RawOp]) -> Result<(), ContractError> {
        for op in operations {
            self.budget.charge(1)?;
            match op {
                RawOp::PackUnit { output } => {
                    if self.registers.insert(*output, vec![]).is_some() {
                        return Err(invalid("Unit map reuses a live owner"));
                    }
                }
                RawOp::UnpackUnit { input } => {
                    if !self.take(*input)?.is_empty() {
                        return Err(invalid("Unit map consumes a nonempty owner"));
                    }
                }
                RawOp::Gate {
                    gate,
                    input,
                    output,
                } => {
                    let axes = self.take(*input)?;
                    self.push(gate_step(*gate, axis(&axes, 0)?))?;
                    self.registers.insert(*output, axes);
                }
                RawOp::Cnot {
                    control,
                    target,
                    control_out,
                    target_out,
                } => {
                    let controls = self.take(*control)?;
                    let targets = self.take(*target)?;
                    let mut step = gate_step(SingleGate::X, axis(&targets, 0)?);
                    step.controls.push(BitControl {
                        index: axis(&controls, 0)?,
                        when_one: true,
                    });
                    self.push(step)?;
                    self.registers.insert(*control_out, controls);
                    self.registers.insert(*target_out, targets);
                }
                RawOp::Toffoli {
                    control_a,
                    control_b,
                    target,
                    control_a_out,
                    control_b_out,
                    target_out,
                } => {
                    let a = self.take(*control_a)?;
                    let b = self.take(*control_b)?;
                    let t = self.take(*target)?;
                    let mut step = gate_step(SingleGate::X, axis(&t, 0)?);
                    step.controls = vec![
                        BitControl {
                            index: axis(&a, 0)?,
                            when_one: true,
                        },
                        BitControl {
                            index: axis(&b, 0)?,
                            when_one: true,
                        },
                    ];
                    self.push(step)?;
                    self.registers.insert(*control_a_out, a);
                    self.registers.insert(*control_b_out, b);
                    self.registers.insert(*target_out, t);
                }
                RawOp::Split {
                    input,
                    left,
                    right,
                    left_bits,
                } => {
                    let axes = self.take(*input)?;
                    let middle = usize::from(*left_bits);
                    if middle > axes.len() {
                        return Err(invalid("split exceeds its input"));
                    }
                    self.registers.insert(*left, axes[..middle].to_vec());
                    self.registers.insert(*right, axes[middle..].to_vec());
                }
                RawOp::Join {
                    left,
                    right,
                    output,
                } => {
                    let mut axes = self.take(*left)?;
                    axes.extend(self.take(*right)?);
                    self.registers.insert(*output, axes);
                }
                RawOp::LiftBasis {
                    input,
                    output,
                    output_wires,
                    table,
                } => {
                    let axes = self.take(*input)?;
                    if output_wires.len() != axes.len() {
                        return Err(ContractError::Type(
                            "function evidence requires width-preserving lifts",
                        ));
                    }
                    self.push(CircuitStep {
                        controls: vec![],
                        action: CircuitAction::Monomial {
                            indices: axes.clone(),
                            permutation: table.clone(),
                            phases: vec![0; table.len()],
                        },
                    })?;
                    self.registers.insert(*output, axes);
                }
                RawOp::ApplyUnitary {
                    input,
                    output,
                    steps,
                } => {
                    let axes = self.take(*input)?;
                    for step in steps {
                        self.push(remap(step, &axes)?)?;
                    }
                    self.registers.insert(*output, axes);
                }
                RawOp::CertifiedCompute {
                    source,
                    source_out,
                    logical_steps,
                    ..
                } => {
                    // The independent verifier just checked this exact retained
                    // body, predicate, and logical circuit with the same budget.
                    let axes = self.take(*source)?;
                    for step in logical_steps {
                        self.push(remap(step, &axes)?)?;
                    }
                    self.registers.insert(*source_out, axes);
                }
                RawOp::QuantumIf {
                    control,
                    target,
                    control_out,
                    target_out,
                    zero_ops,
                    one_ops,
                } => {
                    let controls = self.take(*control)?;
                    let targets = self.take(*target)?;
                    for (when_one, arm) in [(false, zero_ops), (true, one_ops)] {
                        for unitary in arm {
                            let mut step = unitary_step(*unitary, &targets)?;
                            step.controls.push(BitControl {
                                index: axis(&controls, 0)?,
                                when_one,
                            });
                            self.push(step)?;
                        }
                    }
                    self.registers.insert(*control_out, controls);
                    self.registers.insert(*target_out, targets);
                }
                RawOp::ComputeUseUncompute {
                    source,
                    source_out,
                    targets,
                    function,
                    use_ops,
                    ..
                } => {
                    self.computed(*source, *source_out, targets, function, use_ops)?;
                }
                RawOp::ClassicalConst { value, output } => {
                    self.classical.insert(*output, *value);
                }
                RawOp::ClassicalNot { input, output } => {
                    self.classical.insert(*output, !self.bit(*input)?);
                }
                RawOp::ClassicalXor {
                    left,
                    right,
                    output,
                } => {
                    self.classical
                        .insert(*output, self.bit(*left)? ^ self.bit(*right)?);
                }
                RawOp::ClassicalAnd {
                    left,
                    right,
                    output,
                } => {
                    self.classical
                        .insert(*output, self.bit(*left)? & self.bit(*right)?);
                }
                RawOp::ClassicalBranch {
                    condition,
                    then_ops,
                    else_ops,
                    quantum_phis,
                    classical_phis,
                } => {
                    let then_arm = self.bit(*condition)?;
                    let outer = self.classical.clone();
                    self.budget.charge(outer.len())?;
                    self.operations(if then_arm { then_ops } else { else_ops })?;
                    let mut quantum = BTreeMap::new();
                    for phi in quantum_phis {
                        let token = if then_arm {
                            phi.then_token
                        } else {
                            phi.else_token
                        };
                        quantum.insert(phi.output, self.take(token)?);
                    }
                    if !self.registers.is_empty() {
                        return Err(invalid("branch omitted a quantum frame output"));
                    }
                    self.registers = quantum;
                    let mut classical = outer;
                    for phi in classical_phis {
                        classical.insert(
                            phi.output,
                            self.bit(if then_arm { phi.then_id } else { phi.else_id })?,
                        );
                    }
                    self.classical = classical;
                }
                _ => {
                    return Err(ContractError::Type(
                        "operation is outside the finite unitary function evidence profile",
                    ));
                }
            }
        }
        Ok(())
    }

    fn computed(
        &mut self,
        source: TokenId,
        source_out: TokenId,
        targets: &[TargetTransition],
        function: &[u16],
        uses: &[ProtectedUse],
    ) -> Result<(), ContractError> {
        let source_axes = self.take(source)?;
        let mut target_axes = Vec::with_capacity(targets.len());
        for target in targets {
            target_axes.push(self.take(target.input)?);
        }
        for usage in uses {
            self.budget
                .charge(function.len() * (source_axes.len() + 1))?;
            match usage {
                ProtectedUse::ProtectedGate { bit, gate } => {
                    let exponent = if *gate == SingleGate::Z {
                        4
                    } else if *gate == SingleGate::T {
                        1
                    } else {
                        return Err(invalid("non-diagonal protected gate"));
                    };
                    let phases = function
                        .iter()
                        .copied()
                        .enumerate()
                        .map(|(label, value)| {
                            if protected_value(*bit, label, value) {
                                exponent
                            } else {
                                0
                            }
                        })
                        .collect();
                    self.push(diagonal_step(&source_axes, phases))?;
                }
                ProtectedUse::ControlledPhase { controls, phase } => {
                    let exponent = phase_exponent(*phase);
                    let phases = function
                        .iter()
                        .copied()
                        .enumerate()
                        .map(|(label, value)| {
                            if protected_controls(controls, label, value) {
                                exponent
                            } else {
                                0
                            }
                        })
                        .collect();
                    self.push(diagonal_step(&source_axes, phases))?;
                }
                ProtectedUse::ControlledTargetGate {
                    controls,
                    target_index,
                    gate,
                } => {
                    let target = target_axes
                        .get(*target_index)
                        .ok_or_else(|| invalid("missing protected target"))?;
                    let target = axis(target, 0)?;
                    for (label, value) in function.iter().copied().enumerate() {
                        if !protected_controls(controls, label, value) {
                            continue;
                        }
                        let mut step = gate_step(*gate, target);
                        step.controls = source_axes
                            .iter()
                            .enumerate()
                            .map(|(place, index)| BitControl {
                                index: *index,
                                when_one: label & (1 << place) != 0,
                            })
                            .collect();
                        self.push(step)?;
                    }
                }
            }
        }
        self.registers.insert(source_out, source_axes);
        for (target, axes) in targets.iter().zip(target_axes) {
            self.registers.insert(target.output, axes);
        }
        Ok(())
    }
}

fn axis(axes: &[usize], position: usize) -> Result<usize, ContractError> {
    axes.get(position)
        .copied()
        .ok_or_else(|| invalid("circuit axis is outside the independent extraction interface"))
}

fn gate_step(gate: SingleGate, target: usize) -> CircuitStep {
    let action = match gate {
        SingleGate::H => CircuitAction::Hadamard { target },
        SingleGate::X => CircuitAction::Monomial {
            indices: vec![target],
            permutation: vec![1, 0],
            phases: vec![0, 0],
        },
        SingleGate::Z | SingleGate::T => CircuitAction::Monomial {
            indices: vec![target],
            permutation: vec![0, 1],
            phases: vec![0, if gate == SingleGate::Z { 4 } else { 1 }],
        },
    };
    CircuitStep {
        controls: vec![],
        action,
    }
}

fn phase_exponent(phase: ScalarPhase) -> u8 {
    match phase {
        ScalarPhase::MinusOne => 4,
        ScalarPhase::EighthTurn => 1,
    }
}

fn unitary_step(step: UnitaryStep, axes: &[usize]) -> Result<CircuitStep, ContractError> {
    Ok(match step {
        UnitaryStep::Gate { gate, target_index } => gate_step(gate, axis(axes, target_index)?),
        UnitaryStep::Cnot {
            control_index,
            target_index,
        } => {
            let mut step = gate_step(SingleGate::X, axis(axes, target_index)?);
            step.controls.push(BitControl {
                index: axis(axes, control_index)?,
                when_one: true,
            });
            step
        }
        UnitaryStep::Toffoli {
            control_a_index,
            control_b_index,
            target_index,
        } => {
            let mut step = gate_step(SingleGate::X, axis(axes, target_index)?);
            step.controls = vec![
                BitControl {
                    index: axis(axes, control_a_index)?,
                    when_one: true,
                },
                BitControl {
                    index: axis(axes, control_b_index)?,
                    when_one: true,
                },
            ];
            step
        }
        UnitaryStep::ScalarPhase(phase) => CircuitStep {
            controls: vec![],
            action: CircuitAction::Monomial {
                indices: vec![],
                permutation: vec![0],
                phases: vec![phase_exponent(phase)],
            },
        },
    })
}

fn remap(step: &CircuitStep, axes: &[usize]) -> Result<CircuitStep, ContractError> {
    let mut step = step.clone();
    for control in &mut step.controls {
        control.index = axis(axes, control.index)?;
    }
    match &mut step.action {
        CircuitAction::Hadamard { target } => *target = axis(axes, *target)?,
        CircuitAction::Monomial { indices, .. } | CircuitAction::Contract { indices, .. } => {
            for index in indices {
                *index = axis(axes, *index)?;
            }
        }
    }
    Ok(step)
}

fn protected_value(bit: ProtectedBit, label: usize, computed: u16) -> bool {
    let value = match bit.region {
        ProtectedRegion::Source => label,
        ProtectedRegion::Ancilla => usize::from(computed),
    };
    value & (1 << bit.index) != 0
}

fn protected_controls(controls: &[Control], label: usize, computed: u16) -> bool {
    controls
        .iter()
        .all(|control| protected_value(control.bit, label, computed) == control.when_one)
}

fn diagonal_step(indices: &[usize], phases: Vec<u8>) -> CircuitStep {
    CircuitStep {
        controls: vec![],
        action: CircuitAction::Monomial {
            indices: indices.to_vec(),
            permutation: (0..phases.len() as u16).collect(),
            phases,
        },
    }
}

#[cfg(test)]
mod snapshot_tests {
    use super::*;
    use crate::contract::DEFAULT_EXACT_WORK;

    fn raw() -> RawProgram {
        RawProgram {
            quantum_inputs: vec![QuantumPort {
                token: TokenId(0),
                wires: vec![],
                shape: BasisShape { bits: 0 },
            }],
            classical_inputs: vec![],
            operations: vec![],
            quantum_outputs: vec![TokenId(0)],
            classical_outputs: vec![],
            declared_effect: Effect::Unitary,
        }
    }

    fn check(sources: Arc<Vec<(String, String)>>) -> Result<FunctionEvidence, ContractDiagnostic> {
        FunctionEvidence::check_retained_diagnostic(
            BasisType::Unit,
            raw(),
            raw(),
            RetainedIdentity::shared("implementation".into(), "specification".into(), sources),
            &mut Budget::new(DEFAULT_EXACT_WORK),
        )
    }

    #[test]
    fn shared_receipt_clones_and_binding_checks_do_not_materialize_legacy_source_copies() {
        let sources = Arc::new(vec![("main".into(), "p".repeat(100_000))]);
        let first = check(Arc::clone(&sources)).unwrap();
        let second = check(Arc::clone(&sources)).unwrap();
        let cloned = first.clone();
        assert!(Arc::ptr_eq(&first.identity, &cloned.identity));
        assert!(!Arc::ptr_eq(&first.identity, &second.identity));
        assert_eq!(Arc::strong_count(&sources), 3);
        let expected = FunctionIdentity {
            implementation: "implementation".into(),
            specification: "specification".into(),
            sources: sources.as_ref().clone(),
        };
        first
            .check_binding(&BasisType::Unit, &expected, &raw(), &raw())
            .unwrap();
        let (implementation, specification, borrowed) = first.identity_parts();
        assert_eq!(implementation, expected.implementation);
        assert_eq!(specification, expected.specification);
        assert!(std::ptr::eq(borrowed.as_ptr(), sources.as_ptr()));
        assert!(format!("{first:?}").contains("implementation"));
        for receipt in [&first, &second, &cloned] {
            let RetainedIdentity::Shared {
                sources: retained,
                exposed,
                ..
            } = receipt.identity.as_ref()
            else {
                panic!("expected shared storage")
            };
            assert!(Arc::ptr_eq(retained, &sources));
            assert!(exposed.get().is_none());
        }
        // An explicit public inspection owns one bounded compatibility copy.
        assert_eq!(first.identity(), &expected);
        assert!(std::ptr::eq(first.identity(), cloned.identity()));
        assert!(std::ptr::eq(first.identity(), first.identity()));
        assert_ne!(
            first.identity().sources[0].1.as_ptr(),
            sources[0].1.as_ptr()
        );
        let RetainedIdentity::Shared { exposed, .. } = second.identity.as_ref() else {
            unreachable!()
        };
        assert!(exposed.get().is_none());
    }

    #[test]
    fn shared_storage_cannot_bypass_metadata_limits_budget_or_raw_verification() {
        for sources in [
            vec![("main".into(), "p".repeat(MAX_FUNCTION_SOURCE_BYTES))],
            vec![
                ("main".into(), String::new()),
                ("main".into(), String::new()),
            ],
            (0..=MAX_FUNCTION_SOURCES)
                .map(|i| (i.to_string(), String::new()))
                .collect(),
            vec![("n".repeat(MAX_IDENTITY_NAME_BYTES + 1), String::new())],
        ] {
            assert!(check(Arc::new(sources)).is_err());
        }
        let sources = Arc::new(vec![("main".into(), "p".repeat(100_000))]);
        for work in [0, 99_999] {
            assert!(
                FunctionEvidence::check_retained_diagnostic(
                    BasisType::Unit,
                    raw(),
                    raw(),
                    RetainedIdentity::shared("i".into(), "s".into(), Arc::clone(&sources)),
                    &mut Budget::new(work),
                )
                .is_err()
            );
        }
        let mut invalid = raw();
        invalid
            .operations
            .push(RawOp::Discard { input: TokenId(0) });
        assert!(
            FunctionEvidence::check_retained_diagnostic(
                BasisType::Unit,
                invalid,
                raw(),
                RetainedIdentity::shared("i".into(), "s".into(), Arc::clone(&sources)),
                &mut Budget::new(DEFAULT_EXACT_WORK),
            )
            .is_err()
        );
        // Even a shared source handle does not establish equality of meanings.
        let mut phase = raw();
        phase.operations.push(RawOp::ApplyUnitary {
            input: TokenId(0),
            output: TokenId(1),
            steps: vec![diagonal_step(&[], vec![4])],
        });
        phase.quantum_outputs = vec![TokenId(1)];
        assert_eq!(
            FunctionEvidence::check_retained_diagnostic(
                BasisType::Unit,
                phase,
                raw(),
                RetainedIdentity::shared("i".into(), "s".into(), sources),
                &mut Budget::new(DEFAULT_EXACT_WORK),
            )
            .unwrap_err()
            .error,
            ContractError::EquationMismatch
        );
    }

    #[test]
    fn aggregate_budget_charges_each_fresh_native_decision() {
        let sources = Arc::new(vec![("main".into(), "p".repeat(1000))]);
        let mut budget = Budget::new(DEFAULT_EXACT_WORK);
        let before = budget.remaining();
        for _ in 0..2 {
            FunctionEvidence::check_retained_diagnostic(
                BasisType::Unit,
                raw(),
                raw(),
                RetainedIdentity::shared("i".into(), "s".into(), Arc::clone(&sources)),
                &mut budget,
            )
            .unwrap();
        }
        assert!(budget.remaining() < before - 2000);
        let mut exhausted = Budget::new(0);
        assert!(
            FunctionEvidence::check_retained_diagnostic(
                BasisType::Unit,
                raw(),
                raw(),
                RetainedIdentity::shared("i".into(), "s".into(), sources),
                &mut exhausted
            )
            .is_err()
        );
        assert_eq!(exhausted.remaining(), 0);
    }
}
