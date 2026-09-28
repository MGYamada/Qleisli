//! Bounded, exact semantic evidence for finite pure circuit implementations.
//!
//! Checked values have private fields. Their constructors validate the
//! operator equation or derive it using a qualified composition rule. They
//! describe encoded inputs; possession of a theorem is not ownership of, or
//! preparation evidence for, a quantum state. Raw IR always rechecks evidence.

pub mod exact;
pub mod function;
pub mod meaning;
pub use function::{FunctionEvidence, FunctionIdentity};

use std::fmt;

use crate::ir::{BitControl, CircuitAction, CircuitStep};
use exact::{Budget, Exact, ExactError, Matrix};

pub const MAX_CONTRACT_BITS: usize = 6;
pub const MAX_CONTRACT_STEPS: usize = 1024;
pub const DEFAULT_EXACT_WORK: usize = 10_000_000;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ContractError {
    Limit(&'static str),
    Type(&'static str),
    InvalidCircuit(String),
    NotIsometric,
    EquationMismatch,
    EvidenceMismatch,
    Arithmetic(ExactError),
}

impl fmt::Display for ContractError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Limit(message) | Self::Type(message) => f.write_str(message),
            Self::InvalidCircuit(message) => write!(f, "invalid circuit: {message}"),
            Self::NotIsometric => f.write_str("encoding or logical operator is not an isometry"),
            Self::EquationMismatch => f.write_str("exact equation U E_in = E_out u does not hold"),
            Self::EvidenceMismatch => {
                f.write_str("evidence does not match the circuit, contract, or entry encoding")
            }
            Self::Arithmetic(error) => write!(f, "{error}"),
        }
    }
}

impl std::error::Error for ContractError {}

impl From<ExactError> for ContractError {
    fn from(error: ExactError) -> Self {
        Self::Arithmetic(error)
    }
}

/// Internal diagnostic detail; the public error variants remain unchanged.
#[derive(Debug)]
pub(crate) struct ContractDiagnostic {
    pub(crate) error: ContractError,
    detail: Option<String>,
}

impl From<ContractError> for ContractDiagnostic {
    fn from(error: ContractError) -> Self {
        Self {
            error,
            detail: None,
        }
    }
}

impl From<ExactError> for ContractDiagnostic {
    fn from(error: ExactError) -> Self {
        ContractError::Arithmetic(error).into()
    }
}

impl fmt::Display for ContractDiagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.error)?;
        if let Some(detail) = &self.detail {
            write!(f, "; {detail}")?;
        }
        Ok(())
    }
}

fn check_equation(actual: &Matrix, expected: &Matrix) -> Result<(), ContractDiagnostic> {
    if actual.rows() != expected.rows() || actual.cols() != expected.cols() {
        return Err(ContractError::EquationMismatch.into());
    }
    // Retain a counterexample from the matrices already computed under the
    // caller's budget. The first column is a logical input basis state.
    for column in 0..actual.cols() {
        for row in 0..actual.rows() {
            let index = row * actual.cols() + column;
            let actual = actual.entries()[index];
            let expected = expected.entries()[index];
            if actual != expected {
                return Err(ContractDiagnostic {
                    error: ContractError::EquationMismatch,
                    detail: Some(format!(
                        "input column {column}, output row {row} (zero-based): actual {}, expected {}",
                        actual.diagnostic(),
                        expected.diagnostic()
                    )),
                });
            }
        }
    }
    Ok(())
}

/// The exact basis tree of one owned quantum register, including Unit nodes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BasisType {
    Unit,
    Bit,
    Pair(Box<BasisType>, Box<BasisType>),
}

// A rejected public tree can be much deeper than our accepted type profile.
// Rejection must not recurse again while destroying that untrusted input.
impl Drop for BasisType {
    fn drop(&mut self) {
        let mut pending = Vec::new();
        if let Self::Pair(a, b) = self {
            pending.push(std::mem::replace(a.as_mut(), Self::Unit));
            pending.push(std::mem::replace(b.as_mut(), Self::Unit));
        }
        while let Some(mut node) = pending.pop() {
            if let Self::Pair(a, b) = &mut node {
                pending.push(std::mem::replace(a.as_mut(), Self::Unit));
                pending.push(std::mem::replace(b.as_mut(), Self::Unit));
            }
            // The children now are leaves, so this node's drop is bounded.
        }
    }
}

impl BasisType {
    pub fn pair(left: Self, right: Self) -> Self {
        Self::Pair(Box::new(left), Box::new(right))
    }

    /// Validate type-tree capacity before any recursive transformation.
    pub fn bits(&self) -> Result<usize, ContractError> {
        let mut pending = vec![(self, 0)];
        let mut nodes = 0;
        let mut bits = 0;
        while let Some((ty, depth)) = pending.pop() {
            nodes += 1;
            if nodes > 128 || depth > 32 {
                return Err(ContractError::Limit(
                    "contract type exceeds 128 nodes or depth 32",
                ));
            }
            match ty {
                Self::Unit => (),
                Self::Bit => bits += 1,
                Self::Pair(a, b) => {
                    pending.extend([(a.as_ref(), depth + 1), (b.as_ref(), depth + 1)])
                }
            }
        }
        if bits > MAX_CONTRACT_BITS {
            return Err(ContractError::Limit(
                "exact contracts support at most 6 physical/logical bits",
            ));
        }
        Ok(bits)
    }

    fn register(bits: usize) -> Result<Self, ContractError> {
        if bits > MAX_CONTRACT_BITS {
            return Err(ContractError::Limit(
                "exact contracts support at most 6 bits",
            ));
        }
        Ok((0..bits)
            .fold(None, |tree, _| {
                Some(match tree {
                    None => Self::Bit,
                    Some(tree) => Self::pair(tree, Self::Bit),
                })
            })
            .unwrap_or(Self::Unit))
    }
}

/// A checked flat circuit. Its basis fixes tensor order and type identity.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Circuit {
    basis: BasisType,
    steps: Vec<CircuitStep>,
}

impl Circuit {
    pub fn new(basis: BasisType, steps: Vec<CircuitStep>) -> Result<Self, ContractError> {
        Self::validate(&basis, &steps)?;
        Ok(Self { basis, steps })
    }

    fn validate(basis: &BasisType, steps: &[CircuitStep]) -> Result<(), ContractError> {
        let bits = basis.bits()?;
        if steps.len() > MAX_CONTRACT_STEPS {
            return Err(ContractError::Limit("contract circuit exceeds 1024 steps"));
        }
        // Bound untrusted vectors before traversing their contents.
        for step in steps {
            if step.controls.len() > bits {
                return Err(ContractError::Limit("too many circuit controls"));
            }
            if let CircuitAction::Contract { indices, .. } = &step.action {
                if indices.len() > bits {
                    return Err(ContractError::Limit("too many contract axes"));
                }
            }
            if let CircuitAction::Monomial {
                indices,
                permutation,
                phases,
            } = &step.action
            {
                if indices.len() > bits
                    || permutation.len() > (1 << bits)
                    || phases.len() > (1 << bits)
                {
                    return Err(ContractError::Limit(
                        "contract circuit table exceeds its register",
                    ));
                }
            }
        }
        crate::verify::check_circuit(steps, bits, &[])
            .map_err(|e| ContractError::InvalidCircuit(e.message))?;
        Ok(())
    }

    pub fn basis(&self) -> &BasisType {
        &self.basis
    }
    pub fn steps(&self) -> &[CircuitStep] {
        &self.steps
    }

    /// Direct exact column evaluation, independent of the frontend and simulator.
    pub fn matrix(&self, budget: &mut Budget) -> Result<Matrix, ContractError> {
        let dimension = 1usize << self.basis.bits()?;
        for step in &self.steps {
            let cost = match &step.action {
                CircuitAction::Contract { evidence, .. } => 3 * evidence.meaning().rows(),
                _ => 6,
            };
            budget.charge(dimension * dimension * cost)?;
        }
        let mut matrix = vec![Exact::zero(); dimension * dimension];
        for column in 0..dimension {
            let mut values = vec![Exact::zero(); dimension];
            values[column] = Exact::one();
            for step in &self.steps {
                let mut next = vec![Exact::zero(); dimension];
                for (label, value) in values.iter().copied().enumerate() {
                    if value == Exact::zero() {
                        continue;
                    }
                    let enabled = step
                        .controls
                        .iter()
                        .all(|c| ((label >> c.index) & 1 != 0) == c.when_one);
                    if !enabled {
                        next[label] = next[label].add(value)?;
                        continue;
                    }
                    match &step.action {
                        CircuitAction::Contract {
                            indices,
                            evidence,
                            adjoint,
                        } => {
                            let input =
                                indices.iter().enumerate().fold(0usize, |n, (place, axis)| {
                                    n | (((label >> axis) & 1) << place)
                                });
                            let meaning = evidence.meaning();
                            let local_dim = meaning.rows();
                            for output in 0..local_dim {
                                let entry = if *adjoint {
                                    meaning.entries()[input * local_dim + output].conjugate()?
                                } else {
                                    meaning.entries()[output * local_dim + input]
                                };
                                if entry == Exact::zero() {
                                    continue;
                                }
                                let mut target = label;
                                for (place, axis) in indices.iter().enumerate() {
                                    target =
                                        (target & !(1 << axis)) | (((output >> place) & 1) << axis);
                                }
                                next[target] = next[target].add(value.mul(entry)?)?;
                            }
                        }
                        CircuitAction::Hadamard { target } => {
                            let low = label & !(1 << target);
                            let high = low | (1 << target);
                            let scaled = value.mul(Exact::inv_sqrt2())?;
                            next[low] = next[low].add(scaled)?;
                            let signed = if label == high { scaled.neg()? } else { scaled };
                            next[high] = next[high].add(signed)?;
                        }
                        CircuitAction::Monomial {
                            indices,
                            permutation,
                            phases,
                        } => {
                            let input =
                                indices.iter().enumerate().fold(0usize, |n, (place, axis)| {
                                    n | (((label >> axis) & 1) << place)
                                });
                            let output = usize::from(permutation[input]);
                            let mut target = label;
                            for (place, axis) in indices.iter().enumerate() {
                                target =
                                    (target & !(1 << axis)) | (((output >> place) & 1) << axis);
                            }
                            next[target] = next[target]
                                .add(value.mul(Exact::phase(i32::from(phases[input])))?)?;
                        }
                    }
                }
                values = next;
            }
            for (row, value) in values.into_iter().enumerate() {
                matrix[row * dimension + column] = value;
            }
        }
        Ok(Matrix::new(dimension, dimension, matrix)?)
    }
}

/// A checked isometric map with fixed logical coordinates and physical layout.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Encoding {
    logical: BasisType,
    physical: BasisType,
    map: Matrix,
}

impl Encoding {
    pub fn new(
        logical: BasisType,
        physical: BasisType,
        map: Matrix,
        budget: &mut Budget,
    ) -> Result<Self, ContractError> {
        if map.cols() != 1usize << logical.bits()? || map.rows() != 1usize << physical.bits()? {
            return Err(ContractError::Type(
                "encoding dimensions do not match its exact types",
            ));
        }
        if !map.is_isometry(budget)? {
            return Err(ContractError::NotIsometric);
        }
        Ok(Self {
            logical,
            physical,
            map,
        })
    }

    pub fn identity(basis: BasisType) -> Result<Self, ContractError> {
        let map = Matrix::identity(1usize << basis.bits()?)?;
        Ok(Self {
            logical: basis.clone(),
            physical: basis,
            map,
        })
    }

    pub fn logical(&self) -> &BasisType {
        &self.logical
    }
    pub fn physical(&self) -> &BasisType {
        &self.physical
    }
    pub fn map(&self) -> &Matrix {
        &self.map
    }
}

/// An independently specified meaning. Equality includes encodings and phase.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Contract {
    input: Encoding,
    output: Encoding,
    logical: Matrix,
}

impl Contract {
    pub fn new(
        input: Encoding,
        output: Encoding,
        logical: Matrix,
        budget: &mut Budget,
    ) -> Result<Self, ContractError> {
        if logical.cols() != input.map.cols() || logical.rows() != output.map.cols() {
            return Err(ContractError::Type(
                "logical operator does not match the encoding domains",
            ));
        }
        if !logical.is_isometry(budget)? {
            return Err(ContractError::NotIsometric);
        }
        Ok(Self {
            input,
            output,
            logical,
        })
    }
    pub fn input(&self) -> &Encoding {
        &self.input
    }
    pub fn output(&self) -> &Encoding {
        &self.output
    }
    pub fn logical(&self) -> &Matrix {
        &self.logical
    }
}

/// Immutable evidence bound to the complete circuit and contract, not a name.
#[derive(Clone, Debug)]
pub struct CheckedContract {
    circuit: Circuit,
    contract: Contract,
}

impl CheckedContract {
    pub fn circuit(&self) -> &Circuit {
        &self.circuit
    }
    pub fn contract(&self) -> &Contract {
        &self.contract
    }

    /// Exact matrix leaf: all input columns and physical output rows are checked.
    pub fn check(
        circuit: Circuit,
        contract: Contract,
        budget: &mut Budget,
    ) -> Result<Self, ContractError> {
        Self::check_diagnostic(circuit, contract, budget).map_err(|diagnostic| diagnostic.error)
    }

    pub(crate) fn check_diagnostic(
        circuit: Circuit,
        contract: Contract,
        budget: &mut Budget,
    ) -> Result<Self, ContractDiagnostic> {
        if circuit.basis != contract.input.physical || circuit.basis != contract.output.physical {
            return Err(
                ContractError::Type("circuit type does not match the physical encodings").into(),
            );
        }
        let lhs = circuit
            .matrix(budget)?
            .compose(&contract.input.map, budget)?;
        let rhs = contract.output.map.compose(&contract.logical, budget)?;
        check_equation(&lhs, &rhs)?;
        Ok(Self { circuit, contract })
    }

    /// Identity primitive; no simulation is needed for this known equality.
    pub fn identity(encoding: Encoding) -> Result<Self, ContractError> {
        Ok(Self {
            circuit: Circuit::new(encoding.physical.clone(), vec![])?,
            contract: Contract {
                logical: Matrix::identity(encoding.map.cols())?,
                input: encoding.clone(),
                output: encoding,
            },
        })
    }

    pub fn check_binding(
        &self,
        circuit: &Circuit,
        contract: &Contract,
    ) -> Result<(), ContractError> {
        if &self.circuit != circuit || &self.contract != contract {
            return Err(ContractError::EvidenceMismatch);
        }
        Ok(())
    }

    /// A caller must establish this exact encoding, not merely its image.
    /// This checks theorem compatibility; runtime ownership is checked by IR.
    pub fn check_entry(&self, entry: Option<&Encoding>) -> Result<&Encoding, ContractError> {
        if entry != Some(&self.contract.input) {
            return Err(ContractError::EvidenceMismatch);
        }
        Ok(&self.contract.output)
    }

    /// Derive next ∘ self without re-evaluating either physical circuit.
    pub fn then(&self, next: &Self, budget: &mut Budget) -> Result<Self, ContractError> {
        // Checked constructors bind both physical interfaces to the circuit's
        // exact basis tree. Matching middle encodings therefore also fixes the
        // basis on which the concatenated steps operate.
        for evidence in [self, next] {
            debug_assert_eq!(evidence.circuit.basis, evidence.contract.input.physical);
            debug_assert_eq!(evidence.circuit.basis, evidence.contract.output.physical);
        }
        if self.contract.output != next.contract.input {
            return Err(ContractError::Type(
                "sequential contracts require exactly matching middle encoding",
            ));
        }
        let steps = self
            .circuit
            .steps
            .iter()
            .chain(&next.circuit.steps)
            .cloned()
            .collect();
        Ok(Self {
            circuit: Circuit::new(self.circuit.basis.clone(), steps)?,
            contract: Contract {
                input: self.contract.input.clone(),
                output: next.contract.output.clone(),
                logical: next
                    .contract
                    .logical
                    .compose(&self.contract.logical, budget)?,
            },
        })
    }

    /// First operand occupies the low tensor axes. This does not assert separability.
    pub fn tensor(&self, other: &Self, budget: &mut Budget) -> Result<Self, ContractError> {
        let physical = BasisType::pair(self.circuit.basis.clone(), other.circuit.basis.clone());
        physical.bits()?;
        let mut steps = self.circuit.steps.clone();
        steps.extend(remapped(&other.circuit.steps, self.circuit.basis.bits()?));
        let encoding =
            |a: &Encoding, b: &Encoding, budget: &mut Budget| -> Result<Encoding, ContractError> {
                let logical = BasisType::pair(a.logical.clone(), b.logical.clone());
                logical.bits()?;
                Ok(Encoding {
                    logical,
                    physical: physical.clone(),
                    map: a.map.tensor(&b.map, budget)?,
                })
            };
        Ok(Self {
            circuit: Circuit::new(physical.clone(), steps)?,
            contract: Contract {
                input: encoding(&self.contract.input, &other.contract.input, budget)?,
                output: encoding(&self.contract.output, &other.contract.output, budget)?,
                logical: self
                    .contract
                    .logical
                    .tensor(&other.contract.logical, budget)?,
            },
        })
    }

    /// The physical circuit is unitary by construction. The logical map must
    /// also be square (it is already checked isometric) before reversing E.
    pub fn adjoint(&self, budget: &mut Budget) -> Result<Self, ContractError> {
        if self.contract.logical.rows() != self.contract.logical.cols() {
            return Err(ContractError::Type(
                "adjoint contract requires logical unitarity",
            ));
        }
        let mut steps = self.circuit.steps.clone();
        invert_steps(&mut steps);
        Ok(Self {
            circuit: Circuit::new(self.circuit.basis.clone(), steps)?,
            contract: Contract {
                input: self.contract.output.clone(),
                output: self.contract.input.clone(),
                logical: self.contract.logical.adjoint(budget)?,
            },
        })
    }

    /// Construct control of a known circuit, with identical input/output E.
    /// This is not an ability to control an unknown external device.
    pub fn controlled(&self, budget: &mut Budget) -> Result<Self, ContractError> {
        if self.contract.input != self.contract.output {
            return Err(ContractError::Type(
                "controlled contract requires identical input and output encodings",
            ));
        }
        let physical = BasisType::pair(BasisType::Bit, self.circuit.basis.clone());
        let logical_type = BasisType::pair(BasisType::Bit, self.contract.input.logical.clone());
        physical.bits()?;
        logical_type.bits()?;
        let mut steps = remapped(&self.circuit.steps, 1);
        for step in &mut steps {
            step.controls.push(BitControl {
                index: 0,
                when_one: true,
            });
        }
        let identity = Matrix::identity(2)?;
        let encoding = Encoding {
            logical: logical_type,
            physical: physical.clone(),
            map: identity.tensor(&self.contract.input.map, budget)?,
        };
        let old_dim = self.contract.logical.cols();
        let dimension = old_dim * 2;
        budget.charge(dimension * dimension)?;
        let mut entries = vec![Exact::zero(); dimension * dimension];
        for row in 0..old_dim {
            entries[(2 * row) * dimension + 2 * row] = Exact::one();
            for col in 0..old_dim {
                entries[(2 * row + 1) * dimension + 2 * col + 1] =
                    self.contract.logical.entries()[row * old_dim + col];
            }
        }
        Ok(Self {
            circuit: Circuit::new(physical, steps)?,
            contract: Contract {
                input: encoding.clone(),
                output: encoding,
                logical: Matrix::new(dimension, dimension, entries)?,
            },
        })
    }
}

fn remapped(steps: &[CircuitStep], offset: usize) -> Vec<CircuitStep> {
    steps
        .iter()
        .cloned()
        .map(|mut step| {
            for control in &mut step.controls {
                control.index += offset;
            }
            match &mut step.action {
                CircuitAction::Hadamard { target } => *target += offset,
                CircuitAction::Monomial { indices, .. }
                | CircuitAction::Contract { indices, .. } => {
                    for index in indices {
                        *index += offset;
                    }
                }
            }
            step
        })
        .collect()
}

/// Recheck the evidence carried by a raw certified compute/use/uncompute scope.
/// This IR-level boundary knows widths; the source checker additionally checks
/// exact source type trees and the two body ownerships, including Q<Unit>.
pub fn check_computed(
    source_bits: usize,
    function: &[u16],
    use_steps: &[CircuitStep],
    logical_steps: &[CircuitStep],
) -> Result<(), ContractError> {
    let mut budget = Budget::new(DEFAULT_EXACT_WORK);
    check_computed_with_budget(source_bits, function, use_steps, logical_steps, &mut budget)
}

pub(crate) fn check_computed_with_budget(
    source_bits: usize,
    function: &[u16],
    use_steps: &[CircuitStep],
    logical_steps: &[CircuitStep],
    budget: &mut Budget,
) -> Result<(), ContractError> {
    check_computed_diagnostic_with_budget(source_bits, function, use_steps, logical_steps, budget)
        .map_err(|diagnostic| diagnostic.error)
}

pub(crate) fn check_computed_diagnostic_with_budget(
    source_bits: usize,
    function: &[u16],
    use_steps: &[CircuitStep],
    logical_steps: &[CircuitStep],
    budget: &mut Budget,
) -> Result<(), ContractDiagnostic> {
    let available = budget.remaining().min(DEFAULT_EXACT_WORK);
    let mut local = Budget::new(available);
    let result = check_computed_inner(source_bits, function, use_steps, logical_steps, &mut local);
    budget.charge(available - local.remaining())?;
    result
}

fn check_computed_inner(
    source_bits: usize,
    function: &[u16],
    use_steps: &[CircuitStep],
    logical_steps: &[CircuitStep],
    budget: &mut Budget,
) -> Result<(), ContractDiagnostic> {
    if source_bits >= MAX_CONTRACT_BITS {
        return Err(ContractError::Limit(
            "certified computation supports at most 5 data bits plus one auxiliary",
        )
        .into());
    }
    let dim = 1usize << source_bits;
    if function.len() != dim || function.iter().any(|x| *x > 1) {
        return Err(
            ContractError::Type("computed predicate must be a total Bit-valued table").into(),
        );
    }
    // Validate capacities before cloning untrusted circuit vectors.
    if use_steps.len() > MAX_CONTRACT_STEPS || logical_steps.len() > MAX_CONTRACT_STEPS {
        return Err(ContractError::Limit("contract circuit exceeds 1024 steps").into());
    }
    let data = BasisType::register(source_bits)?;
    let physical = BasisType::pair(data.clone(), BasisType::Bit);
    Circuit::validate(&physical, use_steps)?;
    Circuit::validate(&data, logical_steps)?;
    let implementation = Circuit::new(physical.clone(), use_steps.to_vec())?;
    let logical = Circuit::new(data.clone(), logical_steps.to_vec())?;
    let mut entries = vec![Exact::zero(); 2 * dim * dim];
    for (x, fx) in function.iter().copied().enumerate() {
        entries[(x + usize::from(fx) * dim) * dim + x] = Exact::one();
    }
    let encoding = Encoding::new(data, physical, Matrix::new(2 * dim, dim, entries)?, budget)?;
    let meaning = logical.matrix(budget)?;
    let contract = Contract::new(encoding.clone(), encoding, meaning, budget)?;
    CheckedContract::check_diagnostic(implementation, contract, budget)?;
    Ok(())
}

/// Reverse a checked circuit without losing phase or nested evidence.
pub(crate) fn invert_steps(steps: &mut [CircuitStep]) {
    steps.reverse();
    for step in steps {
        match &mut step.action {
            CircuitAction::Contract { adjoint, .. } => *adjoint = !*adjoint,
            CircuitAction::Hadamard { .. } => (),
            CircuitAction::Monomial {
                permutation,
                phases,
                ..
            } => {
                let mut inverse = vec![0; permutation.len()];
                let mut inverse_phases = vec![0; phases.len()];
                for (x, y) in permutation.iter().copied().enumerate() {
                    inverse[usize::from(y)] = x as u16;
                    inverse_phases[usize::from(y)] = (8 - phases[x]) % 8;
                }
                *permutation = inverse;
                *phases = inverse_phases;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn counterexample_diagnostic_preserves_the_shared_work_budget() {
        let use_steps = [CircuitStep {
            controls: vec![],
            action: CircuitAction::Hadamard { target: 1 },
        }];
        let mut public_budget = Budget::new(DEFAULT_EXACT_WORK);
        let mut diagnostic_budget = Budget::new(DEFAULT_EXACT_WORK);
        let error = check_computed_with_budget(1, &[0, 1], &use_steps, &[], &mut public_budget)
            .unwrap_err();
        let diagnostic = check_computed_diagnostic_with_budget(
            1,
            &[0, 1],
            &use_steps,
            &[],
            &mut diagnostic_budget,
        )
        .unwrap_err();
        assert_eq!(error, ContractError::EquationMismatch);
        assert_eq!(diagnostic.error, error);
        assert_eq!(public_budget.remaining(), diagnostic_budget.remaining());
        assert!(
            diagnostic
                .to_string()
                .contains("input column 0, output row 0")
        );

        let mut exhausted = Budget::new(0);
        let diagnostic =
            check_computed_diagnostic_with_budget(1, &[0, 1], &use_steps, &[], &mut exhausted)
                .unwrap_err();
        assert_eq!(
            diagnostic.error,
            ContractError::Arithmetic(ExactError::WorkLimit)
        );
        assert!(diagnostic.detail.is_none());
        assert_eq!(exhausted.remaining(), 0);
    }
}
