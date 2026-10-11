//! Native finite equations bound to complete QIRF bytes and independent requests.
//! Rust describes and decodes data; only a fresh Lean decision authorizes a leaf.

use std::collections::BTreeSet;
use std::sync::Arc;

use super::{Error, Result, contract_error};
use crate::AcceptedProgram;
use crate::contract::exact::{Budget, Matrix};
use crate::contract::{BasisType, ContractError, DEFAULT_EXACT_WORK};
use crate::ir::QuantumPort;

/// Independently required whole-space boundary of a unary unitary leaf.
/// The exact legacy type tree is retained even when its width is zero.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UnitaryBoundary {
    signature: BasisType,
    input: QuantumPort,
    output: QuantumPort,
}

impl UnitaryBoundary {
    pub fn new(signature: BasisType, input: QuantumPort, output: QuantumPort) -> Result<Self> {
        let bits = signature.bits().map_err(contract_error)?;
        for port in [&input, &output] {
            if usize::from(port.shape.bits) != bits
                || port.wires.len() != bits
                || port.wires.iter().collect::<BTreeSet<_>>().len() != bits
            {
                return Err(Error::new(
                    "invalid_ir",
                    "finite leaf boundary disagrees with its exact type or repeats a wire",
                ));
            }
        }
        Ok(Self {
            signature,
            input,
            output,
        })
    }

    pub fn signature(&self) -> &BasisType {
        &self.signature
    }

    pub fn input(&self) -> &QuantumPort {
        &self.input
    }

    pub fn output(&self) -> &QuantumPort {
        &self.output
    }
}

/// A native-checked finite equation bound to complete bytes and required ports.
/// Private fields prevent producer construction. This value must never be
/// serialized as an authority flag or imported into Lean as a theorem.
#[derive(Debug)]
pub struct CheckedUnitaryLeaf {
    payload: Arc<[u8]>,
    boundary: UnitaryBoundary,
    program: AcceptedProgram,
    meaning: Matrix,
    exact_work: usize,
}

impl CheckedUnitaryLeaf {
    pub fn payload(&self) -> &[u8] {
        &self.payload
    }

    pub fn boundary(&self) -> &UnitaryBoundary {
        &self.boundary
    }

    pub fn program(&self) -> &AcceptedProgram {
        &self.program
    }

    pub fn meaning(&self) -> &Matrix {
        &self.meaning
    }

    /// Exact work spent by this reconstruction/equation, excluding tokenization.
    pub fn exact_work(&self) -> usize {
        self.exact_work
    }

    /// Full structural binding, never pointer identity or a producer hash.
    pub fn matches(&self, payload: &[u8], boundary: &UnitaryBoundary, meaning: &Matrix) -> bool {
        self.payload.as_ref() == payload && &self.boundary == boundary && &self.meaning == meaning
    }
}

/// Reconstructed equation bound to both complete transported byte strings.
/// No public constructor or serialized success flag can create this value.
#[derive(Debug)]
pub struct CheckedSerializedUnitaryLeaf {
    leaf: CheckedUnitaryLeaf,
    description: Arc<[u8]>,
    exact_work: usize,
}

impl CheckedSerializedUnitaryLeaf {
    pub fn leaf(&self) -> &CheckedUnitaryLeaf {
        &self.leaf
    }

    pub fn description(&self) -> &[u8] {
        &self.description
    }

    /// Shared exact work including description decoding and QIRF reconstruction.
    pub fn exact_work(&self) -> usize {
        self.exact_work
    }

    pub fn matches(&self, payload: &[u8], boundary: &UnitaryBoundary, description: &[u8]) -> bool {
        self.leaf.payload() == payload
            && self.leaf.boundary() == boundary
            && self.description.as_ref() == description
    }
}

/// Freshly decode both transported sides of a finite equation. The hierarchy
/// host must additionally bind this result to its actual pending request and
/// share payload/work limits across all requests in that artifact.
pub fn check_serialized_unitary(
    payload: &[u8],
    boundary: &UnitaryBoundary,
    description: &[u8],
    budget: &mut Budget,
) -> Result<CheckedSerializedUnitaryLeaf> {
    check_serialized_with_kernel(
        &super::native::Kernel::selected()?,
        payload,
        boundary,
        description,
        budget,
    )
}

pub(super) fn check_serialized_with_kernel(
    kernel: &super::native::Kernel,
    payload: &[u8],
    boundary: &UnitaryBoundary,
    description: &[u8],
    budget: &mut Budget,
) -> Result<CheckedSerializedUnitaryLeaf> {
    if payload.len().saturating_add(description.len()) > super::json::MAX_BYTES {
        return Err(Error::limit("combined finite leaf payload exceeds 16 MiB"));
    }
    let before = budget.remaining();
    let meaning = super::finite_matrix::decode(description, budget)?;
    let leaf = check_with_kernel(kernel, payload, boundary, &meaning, budget)?;
    Ok(CheckedSerializedUnitaryLeaf {
        leaf,
        description: Arc::from(description),
        exact_work: before - budget.remaining(),
    })
}

/// Reconstruct an implementation and compare it with an independently required
/// exact whole-space matrix. The caller shares one bounded budget across leaves.
/// Neither the expected matrix nor the declared effect alone is evidence.
pub fn check_unitary(
    payload: &[u8],
    boundary: &UnitaryBoundary,
    meaning: &Matrix,
    budget: &mut Budget,
) -> Result<CheckedUnitaryLeaf> {
    check_with_kernel(
        &super::native::Kernel::selected()?,
        payload,
        boundary,
        meaning,
        budget,
    )
}

pub(crate) fn check_with_kernel(
    kernel: &super::native::Kernel,
    payload: &[u8],
    boundary: &UnitaryBoundary,
    meaning: &Matrix,
    budget: &mut Budget,
) -> Result<CheckedUnitaryLeaf> {
    if budget.remaining() > DEFAULT_EXACT_WORK {
        return Err(Error::limit(
            "finite leaf budget exceeds the shared exact-work ceiling",
        ));
    }
    let before = budget.remaining();
    let bits = boundary.signature.bits().map_err(contract_error)?;
    let dimension = 1usize << bits;
    if meaning.rows() != dimension || meaning.cols() != dimension {
        return Err(contract_error(ContractError::Type(
            "finite leaf meaning dimensions differ from the required type",
        )));
    }
    let program = kernel.check_leaf(payload, boundary, meaning)?;
    budget
        .charge(program.native_exact_work())
        .map_err(ContractError::from)
        .map_err(contract_error)?;
    Ok(CheckedUnitaryLeaf {
        payload: Arc::from(payload),
        boundary: boundary.clone(),
        program,
        meaning: meaning.clone(),
        exact_work: before - budget.remaining(),
    })
}
