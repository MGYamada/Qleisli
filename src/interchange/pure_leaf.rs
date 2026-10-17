//! Native rectangular equations over complete original QIRF artifacts.
//! Producers describe obligations; only fresh Lean checking grants a receipt.

use std::collections::BTreeSet;
use std::sync::Arc;

use super::{Error, Result, contract_error};
use crate::AcceptedProgram;
use crate::contract::exact::{Budget, Matrix};
use crate::contract::{BasisType, ContractError, DEFAULT_EXACT_WORK};
use crate::ir::QuantumPort;

/// Independently requested exact domain, codomain and ordered owner ports.
/// Construction validates data shape only; it grants no semantic evidence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PureBoundary {
    domain: BasisType,
    codomain: BasisType,
    input: QuantumPort,
    output: QuantumPort,
}

impl PureBoundary {
    pub fn new(
        domain: BasisType,
        codomain: BasisType,
        input: QuantumPort,
        output: QuantumPort,
    ) -> Result<Self> {
        for (ty, port) in [(&domain, &input), (&codomain, &output)] {
            let bits = ty.bits().map_err(contract_error)?;
            if usize::from(port.shape.bits) != bits
                || port.wires.len() != bits
                || port.wires.iter().collect::<BTreeSet<_>>().len() != bits
            {
                return Err(Error::new(
                    "invalid_ir",
                    "pure leaf boundary disagrees with its exact type or repeats a wire",
                ));
            }
        }
        Ok(Self {
            domain,
            codomain,
            input,
            output,
        })
    }

    pub fn domain(&self) -> &BasisType {
        &self.domain
    }

    pub fn codomain(&self) -> &BasisType {
        &self.codomain
    }

    pub fn input(&self) -> &QuantumPort {
        &self.input
    }

    pub fn output(&self) -> &QuantumPort {
        &self.output
    }
}

/// A native-created exact isometry equation bound to original bytes and ports.
/// It grants no inverse/control capability, target realization or resource bound.
///
/// ```compile_fail
/// use qleisli::interchange::pure_leaf::{CheckedPureLeaf, PureBoundary};
/// fn bypass(boundary: PureBoundary) -> CheckedPureLeaf {
///     CheckedPureLeaf { boundary }
/// }
/// ```
#[derive(Debug)]
pub struct CheckedPureLeaf {
    payload: Arc<[u8]>,
    boundary: PureBoundary,
    program: AcceptedProgram,
    meaning: Matrix,
    exact_work: usize,
}

/// Two independently checked bodies with the same requested two-port meaning.
/// Source snapshots are provenance, not a source-preservation proof. This
/// sidecar does not make the enclosing program's ordinary request a pure one.
#[derive(Debug)]
pub struct SourcePureEquation {
    implementation: Arc<CheckedPureLeaf>,
    specification: Arc<CheckedPureLeaf>,
    names: (String, String),
    sources: crate::contract::function::SourceSnapshot,
}
impl SourcePureEquation {
    pub fn implementation(&self) -> &CheckedPureLeaf {
        &self.implementation
    }
    pub fn specification(&self) -> &CheckedPureLeaf {
        &self.specification
    }
    pub fn names(&self) -> (&str, &str) {
        (&self.names.0, &self.names.1)
    }
    pub fn sources(&self) -> &[(String, String)] {
        self.sources.exposed()
    }
    pub(crate) fn source_view(&self) -> crate::contract::function::SourceView<'_> {
        self.sources.view()
    }
    pub(crate) fn bind(
        implementation: Arc<CheckedPureLeaf>,
        specification: Arc<CheckedPureLeaf>,
        names: (String, String),
        sources: crate::contract::function::SourceRows,
    ) -> Result<Self> {
        if implementation.boundary().domain() != specification.boundary().domain()
            || implementation.boundary().codomain() != specification.boundary().codomain()
            || implementation.meaning() != specification.meaning()
        {
            return Err(contract_error(ContractError::EquationMismatch));
        }
        Ok(Self {
            implementation,
            specification,
            names,
            sources: crate::contract::function::SourceSnapshot::new(sources),
        })
    }
}

impl CheckedPureLeaf {
    pub fn payload(&self) -> &[u8] {
        &self.payload
    }

    pub fn boundary(&self) -> &PureBoundary {
        &self.boundary
    }

    pub fn program(&self) -> &AcceptedProgram {
        &self.program
    }

    pub fn meaning(&self) -> &Matrix {
        &self.meaning
    }

    pub fn exact_work(&self) -> usize {
        self.exact_work
    }

    /// Compare complete values, never a producer hash or pointer identity.
    pub fn matches(&self, payload: &[u8], boundary: &PureBoundary, meaning: &Matrix) -> bool {
        self.payload.as_ref() == payload && &self.boundary == boundary && &self.meaning == meaning
    }
}

/// Freshly check the whole graph, original pure body and exact rectangular
/// equation, including its Gram identity. The caller shares a bounded budget.
pub fn check_pure(
    payload: &[u8],
    boundary: &PureBoundary,
    meaning: &Matrix,
    budget: &mut Budget,
) -> Result<CheckedPureLeaf> {
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
    boundary: &PureBoundary,
    meaning: &Matrix,
    budget: &mut Budget,
) -> Result<CheckedPureLeaf> {
    if budget.remaining() > DEFAULT_EXACT_WORK {
        return Err(Error::limit(
            "pure leaf budget exceeds the shared exact-work ceiling",
        ));
    }
    let before = budget.remaining();
    let rows = 1usize << boundary.codomain.bits().map_err(contract_error)?;
    let cols = 1usize << boundary.domain.bits().map_err(contract_error)?;
    if meaning.rows() != rows || meaning.cols() != cols {
        return Err(contract_error(ContractError::Type(
            "pure leaf meaning dimensions differ from the required types",
        )));
    }
    let program = kernel.check_pure_leaf(payload, boundary, meaning)?;
    budget
        .charge(program.native_exact_work())
        .map_err(ContractError::from)
        .map_err(contract_error)?;
    Ok(CheckedPureLeaf {
        payload: Arc::from(payload),
        boundary: boundary.clone(),
        program,
        meaning: meaning.clone(),
        exact_work: before - budget.remaining(),
    })
}
