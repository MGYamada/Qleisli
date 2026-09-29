//! Experimental exact operator contracts with bounded matrix leaves.
//!
//! All supplied graphs are untrusted. References must point backwards, and the
//! checker derives types and proof conclusions. Structural interning preserves
//! exact type trees and phases; it performs no algebraic simplification.
//! Matrices occur only in leaves whose every interface has at most three bits.
//! Encodings describe mathematical subspaces, not runtime ownership or entry
//! permissions. In particular, a checked contract does not grant pure release.

use std::collections::BTreeMap;
use std::fmt;

use qleisli::contract::exact::{Budget, Exact, ExactError, Matrix};

pub const MAX_LEAF_BITS: usize = 3;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct TypeId(pub usize);
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct TermId(pub usize);
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct ProofId(pub usize);

/// Products retain their tree, including zero-bit `Unit` factors.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum TypeNode {
    Unit,
    Bit,
    Pair { low: TypeId, high: TypeId },
}

/// Typed isometries. The low tensor operand occupies the least significant axes.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum Term {
    Identity {
        space: TypeId,
    },
    H,
    X,
    Z,
    T,
    /// Control is the low bit, target the high bit of `Pair(Bit, Bit)`.
    Cnot,
    /// Exact exp(i*pi*eighths/4) times identity, including on `Unit`.
    Phase {
        space: TypeId,
        eighths: u8,
    },
    Init0,
    /// |x> -> |x,0_scratch>; this is a semantic encoding, not a release API.
    ZeroExtend {
        logical: TypeId,
        scratch: TypeId,
    },
    /// Execute `first`, then `second`.
    Sequence {
        first: TermId,
        second: TermId,
    },
    Tensor {
        low: TermId,
        high: TermId,
    },
    Adjoint {
        operand: TermId,
    },
    /// A fresh low control axis, selecting identity at zero and operand at one.
    Controlled {
        operand: TermId,
    },
    Repeat {
        operand: TermId,
        count: u64,
    },
    /// Output bit j receives input bit output_axes[j]. Also records retyping.
    Rewire {
        input: TypeId,
        output: TypeId,
        output_axes: Vec<usize>,
    },
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct TermGraph {
    pub types: Vec<TypeNode>,
    pub terms: Vec<Term>,
}

/// U E_in = E_out u, with exact operator phase and ordered type interfaces.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Contract {
    pub implementation: TermId,
    pub input_encoding: TermId,
    pub output_encoding: TermId,
    pub logical: TermId,
}

/// A caller-owned requirement frozen before asking an untrusted producer for a
/// proof. IDs alone are insufficient: their complete defining graph is retained.
/// Creating a snapshot does not validate it or issue semantic evidence. `check`
/// rejects malformed or open requirements, changed prefixes, and false claims.
/// A producer may append nodes but cannot edit the frozen definitions.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RequiredContract {
    graph: TermGraph,
    contract: Contract,
}

impl RequiredContract {
    pub fn new(graph: TermGraph, contract: Contract) -> Self {
        Self { graph, contract }
    }

    pub fn graph(&self) -> &TermGraph {
        &self.graph
    }

    pub fn contract(&self) -> &Contract {
        &self.contract
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProofRule {
    ExactLeaf { contract: Contract },
    Identity { encoding: TermId },
    Sequence { first: ProofId, second: ProofId },
    Tensor { low: ProofId, high: ProofId },
    Adjoint { premise: ProofId },
    Control { premise: ProofId },
    Repeat { premise: ProofId, count: u64 },
}

#[derive(Clone, Copy, Debug)]
pub struct Limits {
    pub max_types: usize,
    pub max_terms: usize,
    pub max_proofs: usize,
    pub max_width: usize,
    pub work: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            max_types: 8192,
            max_terms: 65_536,
            max_proofs: 65_536,
            max_width: 4096,
            work: 20_000_000,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum KernelError {
    InvalidGraph(&'static str),
    TypeMismatch(&'static str),
    RuleMismatch(&'static str),
    Limit(&'static str),
    LeafTooWide,
    EquationMismatch,
    ExpectedContractMismatch,
    RequirementMismatch,
    BindingMismatch,
    Exact(ExactError),
}

impl fmt::Display for KernelError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidGraph(message)
            | Self::TypeMismatch(message)
            | Self::RuleMismatch(message)
            | Self::Limit(message) => f.write_str(message),
            Self::LeafTooWide => write!(
                f,
                "exact leaves support at most {MAX_LEAF_BITS} bits per interface"
            ),
            Self::EquationMismatch => f.write_str("exact leaf does not satisfy U E_in = E_out u"),
            Self::ExpectedContractMismatch => {
                f.write_str("derived root differs from the expected implementation or contract")
            }
            Self::RequirementMismatch => {
                f.write_str("submitted graph changes the frozen required contract definitions")
            }
            Self::BindingMismatch => {
                f.write_str("evidence is attached to a different graph or contract")
            }
            Self::Exact(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for KernelError {}
impl From<ExactError> for KernelError {
    fn from(error: ExactError) -> Self {
        Self::Exact(error)
    }
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Statistics {
    pub term_nodes: usize,
    pub proof_nodes: usize,
    pub exact_leaves: usize,
    pub leaf_operator_evaluations: usize,
    pub largest_matrix_dimension: usize,
    /// Work charged while evaluating and comparing bounded exact leaves.
    pub exact_work_used: usize,
    pub work_used: usize,
}

/// Opaque checked evidence retains complete immutable input and proof graphs.
#[derive(Clone, Debug)]
pub struct CheckedEvidence {
    graph: TermGraph,
    proofs: Vec<ProofRule>,
    root: ProofId,
    requirement: RequiredContract,
    statistics: Statistics,
}

impl CheckedEvidence {
    pub fn contract(&self) -> &Contract {
        self.requirement.contract()
    }
    pub fn requirement(&self) -> &RequiredContract {
        &self.requirement
    }
    pub fn graph(&self) -> &TermGraph {
        &self.graph
    }
    pub fn proofs(&self) -> &[ProofRule] {
        &self.proofs
    }
    pub fn root(&self) -> ProofId {
        self.root
    }
    pub fn stats(&self) -> &Statistics {
        &self.statistics
    }

    /// Compare concrete contents, not names, hashes, or a caller's explanation.
    pub fn check_binding(
        &self,
        graph: &TermGraph,
        requirement: &RequiredContract,
    ) -> Result<(), KernelError> {
        if graph != &self.graph || requirement != &self.requirement {
            return Err(KernelError::BindingMismatch);
        }
        Ok(())
    }
}

#[derive(Clone, Copy)]
struct Signature {
    input: usize,
    output: usize,
    unitary: bool,
}

struct Checker {
    limits: Limits,
    budget: Budget,
    types: Vec<TypeNode>,
    widths: Vec<usize>,
    type_intern: BTreeMap<TypeNode, usize>,
    terms: Vec<Term>,
    signatures: Vec<Signature>,
    term_intern: BTreeMap<Term, usize>,
    matrices: Vec<Option<Matrix>>,
    raw_types: Vec<usize>,
    raw_terms: Vec<usize>,
    statistics: Statistics,
}

impl Checker {
    fn new(limits: Limits) -> Self {
        Self {
            limits,
            budget: Budget::new(limits.work),
            types: vec![],
            widths: vec![],
            type_intern: BTreeMap::new(),
            terms: vec![],
            signatures: vec![],
            term_intern: BTreeMap::new(),
            matrices: vec![],
            raw_types: vec![],
            raw_terms: vec![],
            statistics: Statistics::default(),
        }
    }

    fn ty(&mut self, node: TypeNode) -> Result<usize, KernelError> {
        self.budget.charge(1)?;
        if let Some(id) = self.type_intern.get(&node) {
            return Ok(*id);
        }
        if self.types.len() >= self.limits.max_types {
            return Err(KernelError::Limit("type-node limit exceeded"));
        }
        let width = match node {
            TypeNode::Unit => 0,
            TypeNode::Bit => 1,
            TypeNode::Pair { low, high } => self.widths[low.0]
                .checked_add(self.widths[high.0])
                .ok_or(KernelError::Limit("type width overflow"))?,
        };
        if width > self.limits.max_width {
            return Err(KernelError::Limit("symbolic type width limit exceeded"));
        }
        let id = self.types.len();
        self.type_intern.insert(node.clone(), id);
        self.types.push(node);
        self.widths.push(width);
        Ok(id)
    }

    fn pair(&mut self, low: usize, high: usize) -> Result<usize, KernelError> {
        self.ty(TypeNode::Pair {
            low: TypeId(low),
            high: TypeId(high),
        })
    }

    fn term(&mut self, node: Term) -> Result<usize, KernelError> {
        self.budget.charge(1)?;
        if let Some(id) = self.term_intern.get(&node) {
            return Ok(*id);
        }
        if self.terms.len() >= self.limits.max_terms {
            return Err(KernelError::Limit("term-node limit exceeded"));
        }
        let unit = self.ty(TypeNode::Unit)?;
        let bit = self.ty(TypeNode::Bit)?;
        let signature = match &node {
            Term::Identity { space } | Term::Phase { space, .. } => {
                if matches!(node, Term::Phase { eighths: 8.., .. }) {
                    return Err(KernelError::InvalidGraph("phase exponent must be in 0..8"));
                }
                Signature {
                    input: space.0,
                    output: space.0,
                    unitary: true,
                }
            }
            Term::H | Term::X | Term::Z | Term::T => Signature {
                input: bit,
                output: bit,
                unitary: true,
            },
            Term::Cnot => {
                let pair = self.pair(bit, bit)?;
                Signature {
                    input: pair,
                    output: pair,
                    unitary: true,
                }
            }
            Term::Init0 => Signature {
                input: unit,
                output: bit,
                unitary: false,
            },
            Term::ZeroExtend { logical, scratch } => Signature {
                input: logical.0,
                output: self.pair(logical.0, scratch.0)?,
                unitary: self.widths[scratch.0] == 0,
            },
            Term::Sequence { first, second } => {
                let a = self.signatures[first.0];
                let b = self.signatures[second.0];
                if a.output != b.input {
                    return Err(KernelError::TypeMismatch(
                        "sequence interfaces differ in exact type",
                    ));
                }
                Signature {
                    input: a.input,
                    output: b.output,
                    unitary: a.unitary && b.unitary,
                }
            }
            Term::Tensor { low, high } => {
                let a = self.signatures[low.0];
                let b = self.signatures[high.0];
                Signature {
                    input: self.pair(a.input, b.input)?,
                    output: self.pair(a.output, b.output)?,
                    unitary: a.unitary && b.unitary,
                }
            }
            Term::Adjoint { operand } => {
                let a = self.signatures[operand.0];
                if !a.unitary {
                    return Err(KernelError::TypeMismatch(
                        "adjoint requires a known unitary operand",
                    ));
                }
                Signature {
                    input: a.output,
                    output: a.input,
                    unitary: true,
                }
            }
            Term::Controlled { operand } => {
                let a = self.signatures[operand.0];
                if !a.unitary || a.input != a.output {
                    return Err(KernelError::TypeMismatch(
                        "control requires a unitary on the same exact type",
                    ));
                }
                let pair = self.pair(bit, a.input)?;
                Signature {
                    input: pair,
                    output: pair,
                    unitary: true,
                }
            }
            Term::Repeat { operand, .. } => {
                let a = self.signatures[operand.0];
                if !a.unitary || a.input != a.output {
                    return Err(KernelError::TypeMismatch(
                        "repetition requires a unitary on the same exact type, even at count zero",
                    ));
                }
                a
            }
            Term::Rewire {
                input,
                output,
                output_axes,
            } => {
                let width = self.widths[input.0];
                if width != self.widths[output.0] || output_axes.len() != width {
                    return Err(KernelError::TypeMismatch(
                        "rewire must preserve width and specify every axis",
                    ));
                }
                self.budget.charge(width)?;
                let mut seen = vec![false; width];
                for axis in output_axes {
                    if *axis >= width || seen[*axis] {
                        return Err(KernelError::InvalidGraph("rewire axes must be a bijection"));
                    }
                    seen[*axis] = true;
                }
                Signature {
                    input: input.0,
                    output: output.0,
                    unitary: true,
                }
            }
        };
        let id = self.terms.len();
        self.term_intern.insert(node.clone(), id);
        self.terms.push(node);
        self.signatures.push(signature);
        self.matrices.push(None);
        Ok(id)
    }

    fn load(&mut self, graph: &TermGraph) -> Result<(), KernelError> {
        if graph.types.len() > self.limits.max_types || graph.terms.len() > self.limits.max_terms {
            return Err(KernelError::Limit("input graph exceeds node limits"));
        }
        for node in &graph.types {
            let mapped = match node {
                TypeNode::Unit => TypeNode::Unit,
                TypeNode::Bit => TypeNode::Bit,
                TypeNode::Pair { low, high } => TypeNode::Pair {
                    low: TypeId(self.raw_type(*low)?),
                    high: TypeId(self.raw_type(*high)?),
                },
            };
            let id = self.ty(mapped)?;
            self.raw_types.push(id);
        }
        for node in &graph.terms {
            // Mapping before insertion rejects cyclic and forward references.
            let mapped = match node {
                Term::Identity { space } => Term::Identity {
                    space: TypeId(self.raw_type(*space)?),
                },
                Term::Phase { space, eighths } => Term::Phase {
                    space: TypeId(self.raw_type(*space)?),
                    eighths: *eighths,
                },
                Term::ZeroExtend { logical, scratch } => Term::ZeroExtend {
                    logical: TypeId(self.raw_type(*logical)?),
                    scratch: TypeId(self.raw_type(*scratch)?),
                },
                Term::Sequence { first, second } => Term::Sequence {
                    first: TermId(self.raw_term(*first)?),
                    second: TermId(self.raw_term(*second)?),
                },
                Term::Tensor { low, high } => Term::Tensor {
                    low: TermId(self.raw_term(*low)?),
                    high: TermId(self.raw_term(*high)?),
                },
                Term::Adjoint { operand } => Term::Adjoint {
                    operand: TermId(self.raw_term(*operand)?),
                },
                Term::Controlled { operand } => Term::Controlled {
                    operand: TermId(self.raw_term(*operand)?),
                },
                Term::Repeat { operand, count } => Term::Repeat {
                    operand: TermId(self.raw_term(*operand)?),
                    count: *count,
                },
                Term::Rewire {
                    input,
                    output,
                    output_axes,
                } => {
                    if output_axes.len() > self.limits.max_width {
                        return Err(KernelError::Limit("rewire axis limit exceeded"));
                    }
                    self.budget.charge(output_axes.len())?;
                    Term::Rewire {
                        input: TypeId(self.raw_type(*input)?),
                        output: TypeId(self.raw_type(*output)?),
                        output_axes: output_axes.clone(),
                    }
                }
                Term::H | Term::X | Term::Z | Term::T | Term::Cnot | Term::Init0 => node.clone(),
            };
            let id = self.term(mapped)?;
            self.raw_terms.push(id);
        }
        Ok(())
    }

    fn raw_type(&self, id: TypeId) -> Result<usize, KernelError> {
        self.raw_types
            .get(id.0)
            .copied()
            .ok_or(KernelError::InvalidGraph(
                "invalid or forward type reference",
            ))
    }
    fn raw_term(&self, id: TermId) -> Result<usize, KernelError> {
        self.raw_terms
            .get(id.0)
            .copied()
            .ok_or(KernelError::InvalidGraph(
                "invalid or forward term reference",
            ))
    }
    fn contract(&self, contract: Contract) -> Result<Contract, KernelError> {
        let mapped = Contract {
            implementation: TermId(self.raw_term(contract.implementation)?),
            input_encoding: TermId(self.raw_term(contract.input_encoding)?),
            output_encoding: TermId(self.raw_term(contract.output_encoding)?),
            logical: TermId(self.raw_term(contract.logical)?),
        };
        self.validate_contract(mapped)?;
        Ok(mapped)
    }
    fn validate_contract(&self, c: Contract) -> Result<(), KernelError> {
        let u = self.signatures[c.implementation.0];
        let ein = self.signatures[c.input_encoding.0];
        let eout = self.signatures[c.output_encoding.0];
        let logical = self.signatures[c.logical.0];
        if ein.output != u.input
            || u.output != eout.output
            || ein.input != logical.input
            || logical.output != eout.input
        {
            return Err(KernelError::TypeMismatch(
                "contract's logical and physical interfaces do not match exactly",
            ));
        }
        Ok(())
    }

    fn exact_leaf(&mut self, c: Contract) -> Result<(), KernelError> {
        let initial_work = self.budget.remaining();
        for id in [
            c.implementation,
            c.input_encoding,
            c.output_encoding,
            c.logical,
        ] {
            let signature = self.signatures[id.0];
            if self.widths[signature.input] > MAX_LEAF_BITS
                || self.widths[signature.output] > MAX_LEAF_BITS
            {
                return Err(KernelError::LeafTooWide);
            }
        }
        let u = self.matrix(c.implementation.0)?;
        let ein = self.matrix(c.input_encoding.0)?;
        let eout = self.matrix(c.output_encoding.0)?;
        let logical = self.matrix(c.logical.0)?;
        if u.compose(&ein, &mut self.budget)? != eout.compose(&logical, &mut self.budget)? {
            return Err(KernelError::EquationMismatch);
        }
        self.statistics.exact_leaves += 1;
        self.statistics.exact_work_used += initial_work - self.budget.remaining();
        Ok(())
    }

    fn matrix(&mut self, root: usize) -> Result<Matrix, KernelError> {
        if let Some(matrix) = &self.matrices[root] {
            self.budget.charge(matrix.rows() * matrix.cols())?;
            return Ok(matrix.clone());
        }
        // Mark only dependencies of this bounded leaf; never evaluate unrelated
        // global expressions. Canonical IDs are topologically ordered.
        self.budget.charge(self.terms.len())?;
        let mut needed = vec![false; self.terms.len()];
        let mut pending = vec![root];
        while let Some(id) = pending.pop() {
            self.budget.charge(1)?;
            if needed[id] || self.matrices[id].is_some() {
                continue;
            }
            needed[id] = true;
            match self.terms[id] {
                Term::Sequence { first, second } => pending.extend([first.0, second.0]),
                Term::Tensor { low, high } => pending.extend([low.0, high.0]),
                Term::Adjoint { operand }
                | Term::Controlled { operand }
                | Term::Repeat { operand, .. } => pending.push(operand.0),
                _ => (),
            }
        }
        for (id, evaluate) in needed.into_iter().enumerate() {
            if !evaluate {
                continue;
            }
            let signature = self.signatures[id];
            let input_bits = self.widths[signature.input];
            let output_bits = self.widths[signature.output];
            if input_bits > MAX_LEAF_BITS || output_bits > MAX_LEAF_BITS {
                return Err(KernelError::LeafTooWide);
            }
            let cols = 1 << input_bits;
            let rows = 1 << output_bits;
            self.budget.charge(rows * cols)?;
            let operand = |child: TermId| {
                self.matrices[child.0]
                    .as_ref()
                    .expect("topological bounded matrix dependency")
            };
            let result = match &self.terms[id] {
                Term::Identity { .. } => Matrix::identity(rows)?,
                Term::H => {
                    let a = Exact::inv_sqrt2();
                    Matrix::new(2, 2, vec![a, a, a, a.neg()?])?
                }
                Term::X => Matrix::new(
                    2,
                    2,
                    vec![Exact::zero(), Exact::one(), Exact::one(), Exact::zero()],
                )?,
                Term::Z | Term::T => Matrix::new(
                    2,
                    2,
                    vec![
                        Exact::one(),
                        Exact::zero(),
                        Exact::zero(),
                        Exact::phase(if matches!(self.terms[id], Term::Z) {
                            4
                        } else {
                            1
                        }),
                    ],
                )?,
                Term::Cnot => {
                    let mut entries = vec![Exact::zero(); 16];
                    for label in 0..4 {
                        let target = label ^ ((label & 1) << 1);
                        entries[target * 4 + label] = Exact::one();
                    }
                    Matrix::new(4, 4, entries)?
                }
                Term::Phase { eighths, .. } => {
                    let mut entries = vec![Exact::zero(); rows * cols];
                    for i in 0..rows {
                        entries[i * cols + i] = Exact::phase(i32::from(*eighths));
                    }
                    Matrix::new(rows, cols, entries)?
                }
                Term::Init0 | Term::ZeroExtend { .. } => {
                    let mut entries = vec![Exact::zero(); rows * cols];
                    for i in 0..cols {
                        entries[i * cols + i] = Exact::one();
                    }
                    Matrix::new(rows, cols, entries)?
                }
                Term::Sequence { first, second } => {
                    operand(*second).compose(operand(*first), &mut self.budget)?
                }
                Term::Tensor { low, high } => {
                    operand(*low).tensor(operand(*high), &mut self.budget)?
                }
                Term::Adjoint { operand: child } => operand(*child).adjoint(&mut self.budget)?,
                Term::Controlled { operand: child } => {
                    let inner = operand(*child);
                    let mut entries = vec![Exact::zero(); rows * cols];
                    for row in 0..inner.rows() {
                        entries[(2 * row) * cols + 2 * row] = Exact::one();
                        for col in 0..inner.cols() {
                            entries[(2 * row + 1) * cols + 2 * col + 1] =
                                inner.entries()[row * inner.cols() + col];
                        }
                    }
                    Matrix::new(rows, cols, entries)?
                }
                Term::Repeat {
                    operand: child,
                    count,
                } => {
                    let mut factor = operand(*child).clone();
                    let mut count = *count;
                    let mut result = Matrix::identity(rows)?;
                    while count != 0 {
                        if count & 1 != 0 {
                            result = factor.compose(&result, &mut self.budget)?;
                        }
                        count >>= 1;
                        if count != 0 {
                            factor = factor.compose(&factor, &mut self.budget)?;
                        }
                    }
                    result
                }
                Term::Rewire { output_axes, .. } => {
                    let mut entries = vec![Exact::zero(); rows * cols];
                    for source in 0..cols {
                        let target = output_axes
                            .iter()
                            .enumerate()
                            .fold(0, |label, (out, input)| {
                                label | (((source >> input) & 1) << out)
                            });
                        entries[target * cols + source] = Exact::one();
                    }
                    Matrix::new(rows, cols, entries)?
                }
            };
            self.statistics.leaf_operator_evaluations += 1;
            self.statistics.largest_matrix_dimension =
                self.statistics.largest_matrix_dimension.max(rows).max(cols);
            self.matrices[id] = Some(result);
        }
        let matrix = self.matrices[root].as_ref().expect("evaluated leaf root");
        self.budget.charge(matrix.rows() * matrix.cols())?;
        Ok(matrix.clone())
    }

    fn derive(&mut self, rule: &ProofRule, previous: &[Contract]) -> Result<Contract, KernelError> {
        self.budget.charge(1)?;
        let premise = |id: ProofId| {
            previous.get(id.0).copied().ok_or(KernelError::InvalidGraph(
                "invalid or forward proof reference",
            ))
        };
        let contract = match rule {
            ProofRule::ExactLeaf { contract } => {
                let c = self.contract(*contract)?;
                self.exact_leaf(c)?;
                c
            }
            ProofRule::Identity { encoding } => {
                let encoding = self.raw_term(*encoding)?;
                let e = self.signatures[encoding];
                Contract {
                    implementation: TermId(self.term(Term::Identity {
                        space: TypeId(e.output),
                    })?),
                    input_encoding: TermId(encoding),
                    output_encoding: TermId(encoding),
                    logical: TermId(self.term(Term::Identity {
                        space: TypeId(e.input),
                    })?),
                }
            }
            ProofRule::Sequence { first, second } => {
                let a = premise(*first)?;
                let b = premise(*second)?;
                if a.output_encoding != b.input_encoding {
                    return Err(KernelError::RuleMismatch(
                        "sequential contracts require the exact same middle encoding",
                    ));
                }
                Contract {
                    implementation: TermId(self.term(Term::Sequence {
                        first: a.implementation,
                        second: b.implementation,
                    })?),
                    input_encoding: a.input_encoding,
                    output_encoding: b.output_encoding,
                    logical: TermId(self.term(Term::Sequence {
                        first: a.logical,
                        second: b.logical,
                    })?),
                }
            }
            ProofRule::Tensor { low, high } => {
                let a = premise(*low)?;
                let b = premise(*high)?;
                Contract {
                    implementation: TermId(self.term(Term::Tensor {
                        low: a.implementation,
                        high: b.implementation,
                    })?),
                    input_encoding: TermId(self.term(Term::Tensor {
                        low: a.input_encoding,
                        high: b.input_encoding,
                    })?),
                    output_encoding: TermId(self.term(Term::Tensor {
                        low: a.output_encoding,
                        high: b.output_encoding,
                    })?),
                    logical: TermId(self.term(Term::Tensor {
                        low: a.logical,
                        high: b.logical,
                    })?),
                }
            }
            ProofRule::Adjoint { premise: id } => {
                let a = premise(*id)?;
                Contract {
                    implementation: TermId(self.term(Term::Adjoint {
                        operand: a.implementation,
                    })?),
                    input_encoding: a.output_encoding,
                    output_encoding: a.input_encoding,
                    logical: TermId(self.term(Term::Adjoint { operand: a.logical })?),
                }
            }
            ProofRule::Control { premise: id } => {
                let a = premise(*id)?;
                if a.input_encoding != a.output_encoding {
                    return Err(KernelError::RuleMismatch(
                        "control requires identical input and output encodings",
                    ));
                }
                let bit = self.ty(TypeNode::Bit)?;
                let control = TermId(self.term(Term::Identity { space: TypeId(bit) })?);
                let encoding = TermId(self.term(Term::Tensor {
                    low: control,
                    high: a.input_encoding,
                })?);
                Contract {
                    implementation: TermId(self.term(Term::Controlled {
                        operand: a.implementation,
                    })?),
                    input_encoding: encoding,
                    output_encoding: encoding,
                    logical: TermId(self.term(Term::Controlled { operand: a.logical })?),
                }
            }
            ProofRule::Repeat { premise: id, count } => {
                let a = premise(*id)?;
                if a.input_encoding != a.output_encoding {
                    return Err(KernelError::RuleMismatch(
                        "repetition requires identical input and output encodings, even at count zero",
                    ));
                }
                Contract {
                    implementation: TermId(self.term(Term::Repeat {
                        operand: a.implementation,
                        count: *count,
                    })?),
                    input_encoding: a.input_encoding,
                    output_encoding: a.output_encoding,
                    logical: TermId(self.term(Term::Repeat {
                        operand: a.logical,
                        count: *count,
                    })?),
                }
            }
        };
        self.validate_contract(contract)?;
        Ok(contract)
    }
}

/// Preserve the caller's frozen requirement, check every submitted node, derive
/// the root, and compare all four expected terms.
/// A zero repetition does not skip its operand or premise. No proof rule adds
/// assumptions, quotients phase, samples inputs, or evaluates a global matrix.
pub fn check(
    graph: &TermGraph,
    proofs: &[ProofRule],
    root: ProofId,
    required: &RequiredContract,
    limits: Limits,
) -> Result<CheckedEvidence, KernelError> {
    if proofs.len() > limits.max_proofs {
        return Err(KernelError::Limit("proof-node limit exceeded"));
    }
    if root.0 >= proofs.len() {
        return Err(KernelError::InvalidGraph("invalid root proof reference"));
    }
    let mut checker = Checker::new(limits);
    checker.load(graph)?;
    // Validate submitted sizes/references before traversing the frozen prefix.
    if required.graph.types.len() > graph.types.len()
        || required.graph.terms.len() > graph.terms.len()
    {
        return Err(KernelError::RequirementMismatch);
    }
    checker
        .budget
        .charge(required.graph.types.len() + required.graph.terms.len())?;
    for term in &required.graph.terms {
        if let Term::Rewire { output_axes, .. } = term {
            checker.budget.charge(output_axes.len())?;
        }
    }
    if graph.types[..required.graph.types.len()] != required.graph.types
        || graph.terms[..required.graph.terms.len()] != required.graph.terms
    {
        return Err(KernelError::RequirementMismatch);
    }
    // Term children already point backwards after load, but type references can
    // point to any submitted type. Appending types must not fill holes in a
    // malformed frozen requirement, nor may the four roots refer to new terms.
    let frozen_type = |id: TypeId| {
        if id.0 < required.graph.types.len() {
            Ok(())
        } else {
            Err(KernelError::InvalidGraph(
                "required contract refers outside its frozen type graph",
            ))
        }
    };
    for term in &required.graph.terms {
        match term {
            Term::Identity { space } | Term::Phase { space, .. } => frozen_type(*space)?,
            Term::ZeroExtend { logical, scratch } => {
                frozen_type(*logical)?;
                frozen_type(*scratch)?;
            }
            Term::Rewire { input, output, .. } => {
                frozen_type(*input)?;
                frozen_type(*output)?;
            }
            _ => (),
        }
    }
    for root in [
        required.contract.implementation,
        required.contract.input_encoding,
        required.contract.output_encoding,
        required.contract.logical,
    ] {
        if root.0 >= required.graph.terms.len() {
            return Err(KernelError::InvalidGraph(
                "required contract root is outside its frozen term graph",
            ));
        }
    }
    let expected_canonical = checker.contract(required.contract)?;
    let mut conclusions = Vec::with_capacity(proofs.len());
    for rule in proofs {
        conclusions.push(checker.derive(rule, &conclusions)?);
    }
    if conclusions[root.0] != expected_canonical {
        return Err(KernelError::ExpectedContractMismatch);
    }
    // Charge retained concrete snapshots before cloning them.
    checker.budget.charge(
        graph.types.len()
            + graph.terms.len()
            + proofs.len()
            + required.graph.types.len()
            + required.graph.terms.len(),
    )?;
    for term in graph.terms.iter().chain(&required.graph.terms) {
        if let Term::Rewire { output_axes, .. } = term {
            checker.budget.charge(output_axes.len())?;
        }
    }
    checker.statistics.term_nodes = checker.terms.len();
    checker.statistics.proof_nodes = proofs.len();
    checker.statistics.work_used = limits.work - checker.budget.remaining();
    Ok(CheckedEvidence {
        graph: graph.clone(),
        proofs: proofs.to_vec(),
        root,
        requirement: required.clone(),
        statistics: checker.statistics,
    })
}

#[cfg(test)]
#[path = "kernel_tests.rs"]
mod tests;
