//! Fixed-width descriptions are untrusted elaboration objects. Only retained
//! finite contract receipts can authorize an executable operation.
use super::*;
use crate::contract::{
    BasisType, Circuit, ContractError, FunctionEvidence, MAX_CONTRACT_BITS, MAX_CONTRACT_STEPS,
    exact::{Budget, Exact, Matrix},
    function::RetainedIdentity,
    meaning::{FiniteMeaning, MeaningEvidence},
};
use crate::ir::*;

#[derive(Clone)]
pub(super) struct DeclaredMeaning {
    pub basis: Ty,
    pub target: FiniteMeaning,
    pub matrix: Matrix,
}
#[derive(Clone, Debug, PartialEq)]
pub(super) struct Operation {
    pub basis: Ty,
    pub access: [bool; 3],
    pub meaning: Option<Matrix>,
    node: Arc<Node>,
    depth: usize,
    nodes: usize,
    pub abstract_value: bool,
}
#[derive(Debug, PartialEq)]
enum Node {
    Abstract(String),
    Provider(Arc<FunctionEvidence>),
    Inverse(Operation),
    Then(Operation, Operation),
    Tensor(Operation, Operation),
    Controlled(Operation),
    Repeat(u16, Operation),
    Conjugate(Operation, Operation),
}
pub(super) type Bindings = BTreeMap<String, Operation>;
pub(super) fn access_index(access: Access) -> usize {
    match access {
        Access::Apply => 0,
        Access::Adjoint => 1,
        Access::Controlled => 2,
    }
}
pub(super) fn contract_basis(ty: &Ty) -> BasisType {
    match ty {
        Ty::Unit => BasisType::Unit,
        Ty::Bit => BasisType::Bit,
        Ty::Pair(a, b) => BasisType::pair(contract_basis(a), contract_basis(b)),
        Ty::Tuple(fields) => BasisType::Tuple(fields.iter().map(contract_basis).collect()),
        _ => unreachable!("checked basis"),
    }
}
fn inverse(mut steps: Vec<CircuitStep>) -> Vec<CircuitStep> {
    circuit::invert(&mut steps);
    steps
}

fn remapped(mut steps: Vec<CircuitStep>, axes: &[usize]) -> Vec<CircuitStep> {
    for s in &mut steps {
        circuit::remap(s, axes);
    }
    steps
}
fn controlled(steps: Vec<CircuitStep>, bits: usize) -> Vec<CircuitStep> {
    let mut steps = remapped(steps, &(1..=bits).collect::<Vec<_>>());
    for s in &mut steps {
        s.controls.push(BitControl {
            index: 0,
            when_one: true,
        });
    }
    steps
}
pub(super) fn control_matrix(m: &Matrix, budget: &mut Budget) -> Result<Matrix, ContractError> {
    let d = m.rows();
    budget.charge(4 * d * d)?;
    let mut entries = vec![Exact::zero(); 4 * d * d];
    for x in 0..d {
        entries[(2 * x) * 2 * d + 2 * x] = Exact::one();
        for y in 0..d {
            entries[(2 * y + 1) * 2 * d + 2 * x + 1] = m.get(y, x).expect("square");
        }
    }
    Ok(Matrix::new(2 * d, 2 * d, entries)?)
}
impl Compiler<'_> {
    pub(super) fn op_error(&self, module: &str, span: Span, error: ContractError) -> CompileError {
        let code = match &error {
            ContractError::Limit(_) | ContractError::Arithmetic(_) => ErrorCode::Limit,
            _ => ErrorCode::Contract,
        };
        let mut message = error.to_string();
        if matches!(
            error,
            ContractError::Arithmetic(crate::contract::exact::ExactError::ArithmeticCapacity)
        ) {
            message.push_str(
                " (bounded i128 coefficients or dyadic denominator exponent above 126); \
                reduce exact composition/repetition; no approximate fallback is used",
            );
        }
        self.error(module, span, code, message)
    }
    pub(super) fn compile_meaning(&mut self, key: &Key) -> Result<(), CompileError> {
        let decl = self.declarations[key];
        let basis = self.ty(&key.0, &decl.return_type, true)?;
        contract_basis(&basis)
            .bits()
            .map_err(|e| self.op_error(&key.0, decl.span, e))?;
        let FnBody::Meaning {
            permutation,
            function,
        } = &decl.body
        else {
            unreachable!()
        };
        let Callee::User(fkey) = self.resolve(&key.0, function)? else {
            return Err(self.error(
                &key.0,
                function.span,
                ErrorCode::TypeMismatch,
                "meaning requires an ordinary total basis function",
            ));
        };
        let f = self.basis.get(&fkey).ok_or_else(|| {
            self.error(
                &key.0,
                function.span,
                ErrorCode::TypeMismatch,
                "meaning requires an ordinary total basis function",
            )
        })?;
        let result = if *permutation {
            basis.clone()
        } else {
            Ty::pair(Ty::Bit, Ty::pair(Ty::Bit, Ty::Bit))
        };
        if f.params != [basis.clone()] || f.result != result {
            return Err(self.error(
                &key.0,
                function.span,
                ErrorCode::TypeMismatch,
                "meaning function has the wrong exact basis signature",
            ));
        }
        let target = if *permutation {
            FiniteMeaning::permutation(contract_basis(&basis), f.table.clone())
        } else {
            FiniteMeaning::phase(
                contract_basis(&basis),
                f.table.iter().map(|x| *x as u8).collect(),
            )
        }
        .map_err(|e| self.op_error(&key.0, decl.span, e))?;
        let matrix = target
            .matrix(&mut self.exact_work)
            .map_err(|e| self.op_error(&key.0, decl.span, e))?;
        self.meanings.insert(
            key.clone(),
            DeclaredMeaning {
                basis,
                target,
                matrix,
            },
        );
        Ok(())
    }
    pub(super) fn meaning_key(&self, module: &str, name: &Ident) -> Result<Key, CompileError> {
        match self.resolve(module, name)? {
            Callee::User(k) if self.meanings.contains_key(&k) => Ok(k),
            _ => Err(self.error(
                module,
                name.span,
                ErrorCode::TypeMismatch,
                "expected a declared finite meaning",
            )),
        }
    }
    pub(super) fn abstract_bindings(&mut self, key: &Key) -> Result<Bindings, CompileError> {
        let decl = self.declarations[key];
        self.signature(key)?;
        let mut bindings = Bindings::new();
        for p in &decl.static_params {
            let basis = self.ty(&key.0, &p.basis, true)?;
            contract_basis(&basis)
                .bits()
                .map_err(|e| self.op_error(&key.0, p.basis.span, e))?;
            let meaning = if let Some(m) = &p.meaning {
                let k = self.meaning_key(&key.0, m)?;
                let target = &self.meanings[&k];
                if target.basis != basis {
                    return Err(self.error(
                        &key.0,
                        m.span,
                        ErrorCode::TypeMismatch,
                        "parameter and meaning basis trees differ",
                    ));
                }
                let cost = target.matrix.entries().len();
                self.charge(&key.0, m.span, cost)?;
                Some(self.meanings[&k].matrix.clone())
            } else {
                None
            };
            bindings.insert(
                p.name.text.clone(),
                Operation {
                    basis,
                    access: [false; 3],
                    meaning,
                    node: Arc::new(Node::Abstract(format!(
                        "{}::{}::{}",
                        key.0, key.1, p.name.text
                    ))),
                    depth: 1,
                    nodes: 1,
                    abstract_value: true,
                },
            );
        }
        for constraint in &decl.requires {
            let Some(op) = bindings.get_mut(&constraint.name.text) else {
                return Err(self.error(
                    &key.0,
                    constraint.name.span,
                    ErrorCode::UnknownName,
                    "access constraint must name a static parameter",
                ));
            };
            let index = access_index(constraint.access);
            if op.access[index] {
                return Err(self.error(
                    &key.0,
                    constraint.name.span,
                    ErrorCode::Capability,
                    "duplicate access constraint",
                ));
            }
            op.access[index] = true;
        }
        Ok(bindings)
    }
    pub(super) fn provider(
        &mut self,
        module: &str,
        name: &Ident,
        meaning: Option<&Ident>,
    ) -> Result<Operation, CompileError> {
        let key = match self.resolve(module, name)? {
            Callee::User(key) => key,
            Callee::Sealed(namespace, gate) => {
                let mut message =
                    "static provider requires an ordinary declared unitary function".to_owned();
                if namespace == "std::quantum" && matches!(gate.as_str(), "h" | "x" | "z" | "t") {
                    message.push_str(&format!(
                        "; wrap the gate as `unitary fn wrapped_gate(q: Q<Bit>) -> Q<Bit> {{ {}(q) }}` and pass `[wrapped_gate]`",
                        name.text
                    ));
                }
                return Err(self.error(module, name.span, ErrorCode::TypeMismatch, message));
            }
        };
        let decl = self.declarations[&key];
        if decl.kind != FnKind::Unitary {
            return Err(self.error(
                module,
                name.span,
                ErrorCode::Effect,
                "static provider must be declared unitary",
            ));
        }
        if !decl.static_params.is_empty() {
            return Err(self.error(
                module,
                name.span,
                ErrorCode::TypeMismatch,
                "static provider must be closed; instantiate it in an ordinary wrapper",
            ));
        }
        let (params, result) = self.signature(&key)?;
        let Ty::Q(basis) = &result else {
            return Err(self.error(
                module,
                name.span,
                ErrorCode::TypeMismatch,
                "static provider requires Q<A> -> Q<A>",
            ));
        };
        if params != [result.clone()] {
            return Err(self.error(
                module,
                name.span,
                ErrorCode::TypeMismatch,
                "static provider requires one input with the exact output type",
            ));
        }
        contract_basis(basis)
            .bits()
            .map_err(|e| self.op_error(module, name.span, e))?;
        let mkey = meaning.map(|m| self.meaning_key(module, m)).transpose()?;
        if let Some(mkey) = &mkey {
            if self.meanings[mkey].basis != **basis {
                return Err(self.error(
                    module,
                    name.span,
                    ErrorCode::TypeMismatch,
                    "provider and meaning basis trees differ",
                ));
            }
        }
        let cache = (key.clone(), mkey.clone());
        if let Some(op) = self.providers.get(&cache) {
            let cost = op.copy_size();
            self.charge(module, name.span, cost)?;
            return Ok(self.providers[&cache].clone());
        }
        let sources = self.retained_sources(module, name.span)?;
        let program = self.checked.get(&key).ok_or_else(|| {
            self.error(
                module,
                name.span,
                ErrorCode::InvalidIr,
                "provider has not been independently checked",
            )
        })?;
        let implementation = program.program().clone();
        let identity = RetainedIdentity::shared(
            format!("{}::{}", key.0, key.1),
            mkey.as_ref().map_or_else(
                || format!("{}::{}", key.0, key.1),
                |m| format!("meaning {}::{}", m.0, m.1),
            ),
            sources,
        );
        let budget = &mut self.exact_work;
        let evidence = if let Some(mkey) = &mkey {
            MeaningEvidence::check_retained(
                implementation,
                self.meanings[mkey].target.clone(),
                identity,
                budget,
            )
            .map(|e| e.receipt())
        } else {
            FunctionEvidence::check_retained_diagnostic(
                contract_basis(basis),
                implementation.clone(),
                implementation,
                identity,
                budget,
            )
            .map(Arc::new)
            .map_err(|diagnostic| diagnostic.error)
        }
        .map_err(|e| self.op_error(module, name.span, e))?;
        let op = Operation {
            basis: (**basis).clone(),
            access: [true; 3],
            meaning: Some(evidence.meaning().clone()),
            node: Arc::new(Node::Provider(evidence)),
            depth: 1,
            nodes: 1,
            abstract_value: false,
        };
        self.charge(module, name.span, op.copy_size())?;
        self.providers.insert(cache, op.clone());
        Ok(op)
    }
    pub(super) fn construct(
        &mut self,
        module: &str,
        span: Span,
        kind: &StaticOpKind,
        a: Operation,
        b: Option<Operation>,
    ) -> Result<Operation, CompileError> {
        let nodes = 1 + a.nodes + b.as_ref().map_or(0, |b| b.nodes);
        let depth = 1 + a.depth.max(b.as_ref().map_or(0, |b| b.depth));
        if nodes > MAX_TREE_NODES || depth > MAX_DEPTH {
            return Err(self.error(
                module,
                span,
                ErrorCode::Limit,
                "static description exceeds its node/depth limit",
            ));
        }
        self.charge(module, span, nodes)?;
        let abstract_value = a.abstract_value || b.as_ref().is_some_and(|b| b.abstract_value);
        let mut basis = a.basis.clone();
        let caps = a.access;
        if let Some(b) = &b {
            if !matches!(kind, StaticOpKind::Tensor(..)) && a.basis != b.basis {
                return Err(self.error(
                    module,
                    span,
                    ErrorCode::TypeMismatch,
                    format!("static composition requires identical basis trees: expected `Op<{}>`, found `Op<{}>`", a.basis, b.basis),
                ));
            }
        }
        let (access, node) = match kind {
            StaticOpKind::Inverse(..) => ([caps[1], caps[0], caps[2]], Node::Inverse(a)),
            StaticOpKind::Controlled(..) => {
                basis = Ty::pair(Ty::Bit, basis);
                ([caps[2]; 3], Node::Controlled(a))
            }
            StaticOpKind::Repeat(n, ..) => (caps, Node::Repeat(*n, a)),
            StaticOpKind::Then(..) | StaticOpKind::Tensor(..) | StaticOpKind::Conjugate(..) => {
                let b = b.expect("binary constructor");
                let mut access = std::array::from_fn(|i| caps[i] && b.access[i]);
                let node = match kind {
                    StaticOpKind::Then(..) => Node::Then(a, b),
                    StaticOpKind::Tensor(..) => {
                        basis = Ty::pair(basis, b.basis.clone());
                        Node::Tensor(a, b)
                    }
                    _ => {
                        access = std::array::from_fn(|i| caps[0] && caps[1] && b.access[i]);
                        Node::Conjugate(a, b)
                    }
                };
                (access, node)
            }
            _ => unreachable!("constructor"),
        };
        self.check_tree(module, span, basis.tree_size())?;
        contract_basis(&basis)
            .bits()
            .map_err(|e| self.op_error(module, span, e))?;
        let meaning = node
            .meaning(&mut self.exact_work)
            .map_err(|e| self.op_error(module, span, e))?;
        Ok(Operation {
            basis,
            access,
            meaning,
            node: Arc::new(node),
            depth,
            nodes,
            abstract_value,
        })
    }
}
pub(super) fn matrix_power(
    m: &Matrix,
    mut n: u16,
    budget: &mut Budget,
) -> Result<Matrix, ContractError> {
    budget.charge(2 * m.entries().len())?;
    let mut result = Matrix::identity(m.rows())?;
    let mut power = m.clone();
    while n != 0 {
        if n & 1 != 0 {
            result = power.compose(&result, budget)?;
        }
        n >>= 1;
        if n != 0 {
            power = power.compose(&power, budget)?;
        }
    }
    Ok(result)
}

/// Check the emitted circuit against an independently obtained expectation.
/// Chunking preserves the existing finite per-circuit bound without requiring
/// a dense matrix beyond six bits or limiting a flat repeat to 1024 steps.
pub(super) fn check_steps_meaning(
    signature: &BasisType,
    steps: &[CircuitStep],
    expected: &Matrix,
    budget: &mut Budget,
) -> Result<(), ContractError> {
    let dimension = 1 << signature.bits()?;
    let mut chunks = steps.chunks(MAX_CONTRACT_STEPS);
    let mut actual = match chunks.next() {
        Some(first) => Circuit::new(signature.clone(), first.to_vec())?.matrix(budget)?,
        None => {
            budget.charge(dimension * dimension)?;
            Matrix::identity(dimension)?
        }
    };
    for chunk in chunks {
        let matrix = Circuit::new(signature.clone(), chunk.to_vec())?.matrix(budget)?;
        actual = matrix.compose(&actual, budget)?;
    }
    if actual != *expected {
        return Err(ContractError::EquationMismatch);
    }
    Ok(())
}

impl Node {
    fn meaning(&self, budget: &mut Budget) -> Result<Option<Matrix>, ContractError> {
        fn binary<'a>(a: &'a Operation, b: &'a Operation) -> Option<(&'a Matrix, &'a Matrix)> {
            a.meaning.as_ref().zip(b.meaning.as_ref())
        }
        Ok(match self {
            Self::Abstract(_) => None,
            Self::Provider(e) => Some(e.meaning().clone()),
            Self::Inverse(a) => a.meaning.as_ref().map(|m| m.adjoint(budget)).transpose()?,
            Self::Controlled(a) => a
                .meaning
                .as_ref()
                .map(|m| control_matrix(m, budget))
                .transpose()?,
            Self::Then(a, b) => binary(a, b)
                .map(|(a, b)| b.compose(a, budget))
                .transpose()?,
            Self::Tensor(a, b) => binary(a, b).map(|(a, b)| a.tensor(b, budget)).transpose()?,
            Self::Conjugate(a, b) => {
                if let Some((a, b)) = binary(a, b) {
                    Some(a.compose(&b.compose(&a.adjoint(budget)?, budget)?, budget)?)
                } else {
                    None
                }
            }
            Self::Repeat(n, a) => {
                if *n == 0 {
                    let dimension = 1 << a.basis.basis_bits().expect("basis");
                    budget.charge(dimension * dimension)?;
                    Some(Matrix::identity(dimension)?)
                } else if let Some(m) = &a.meaning {
                    Some(matrix_power(m, *n, budget)?)
                } else {
                    None
                }
            }
        })
    }
}
impl Operation {
    /// Cloning shares the description DAG/receipt, but copies its root matrix
    /// and exact type tree. Charge these before populating binding caches.
    pub(super) fn copy_size(&self) -> usize {
        self.basis.tree_size().nodes + self.meaning.as_ref().map_or(0, |m| m.entries().len()) + 1
    }
    pub(super) fn require(
        &self,
        module: &str,
        span: Span,
        access: Access,
        compiler: &Compiler<'_>,
    ) -> Result<(), CompileError> {
        if !self.access[access_index(access)] {
            return Err(compiler.error(
                module,
                span,
                ErrorCode::Capability,
                format!("missing {access:?} access in the generic declaration"),
            ));
        }
        let bits =
            self.basis.basis_bits().expect("basis") + usize::from(access == Access::Controlled);
        if bits > MAX_CONTRACT_BITS {
            return Err(compiler.error(
                module,
                span,
                ErrorCode::Limit,
                "requested operation exceeds the six-bit contract profile",
            ));
        }
        Ok(())
    }
    pub(super) fn steps(
        &self,
        module: &str,
        span: Span,
        access: Access,
        compiler: &mut Compiler<'_>,
    ) -> Result<Vec<CircuitStep>, CompileError> {
        self.require(module, span, access, compiler)?;
        compiler.charge(module, span, self.nodes)?;
        if self.abstract_value {
            return Ok(vec![]);
        }
        let steps = self
            .materialize(access)
            .map_err(|e| compiler.op_error(module, span, e))?;
        compiler.charge(module, span, total_size(steps.iter().map(circuit::size)))?;
        let basis = if access == Access::Controlled {
            Ty::pair(Ty::Bit, self.basis.clone())
        } else {
            self.basis.clone()
        };
        let budget = &mut compiler.exact_work;
        let actual = Circuit::new(contract_basis(&basis), steps.clone())
            .and_then(|c| c.matrix(budget))
            .map_err(|e| compiler.op_error(module, span, e))?;
        let m = self.meaning.as_ref().expect("concrete meaning");
        let expected = match access {
            Access::Apply => Ok(m.clone()),
            Access::Adjoint => m
                .adjoint(&mut compiler.exact_work)
                .map_err(ContractError::from),
            Access::Controlled => control_matrix(m, &mut compiler.exact_work),
        }
        .map_err(|e| compiler.op_error(module, span, e))?;
        if actual != expected {
            return Err(compiler.error(
                module,
                span,
                ErrorCode::Contract,
                "derived operation does not preserve its phase-fixed meaning",
            ));
        }
        Ok(steps)
    }
    fn materialize(&self, access: Access) -> Result<Vec<CircuitStep>, ContractError> {
        let bits = self.basis.basis_bits().expect("basis");
        let cat = |mut a: Vec<CircuitStep>,
                   b: Vec<CircuitStep>|
         -> Result<Vec<CircuitStep>, ContractError> {
            if a.len() + b.len() > MAX_CONTRACT_STEPS {
                return Err(ContractError::Limit("static circuit exceeds 1024 steps"));
            }
            a.extend(b);
            Ok(a)
        };
        let steps = match self.node.as_ref() {
            Node::Abstract(_) => {
                return Err(ContractError::Type("abstract operation is not executable"));
            }
            Node::Provider(e) => {
                let s = vec![CircuitStep {
                    controls: vec![],
                    action: CircuitAction::Contract {
                        indices: (0..bits).collect(),
                        evidence: Arc::clone(e),
                        adjoint: access == Access::Adjoint,
                    },
                }];
                if access == Access::Controlled {
                    controlled(s, bits)
                } else {
                    s
                }
            }
            Node::Inverse(a) => match access {
                Access::Apply => a.materialize(Access::Adjoint)?,
                Access::Adjoint => a.materialize(Access::Apply)?,
                Access::Controlled => inverse(a.materialize(Access::Controlled)?),
            },
            Node::Controlled(a) => {
                let s = a.materialize(Access::Controlled)?;
                match access {
                    Access::Apply => s,
                    Access::Adjoint => inverse(s),
                    Access::Controlled => controlled(s, bits),
                }
            }
            Node::Then(a, b) => {
                if access == Access::Adjoint {
                    cat(b.materialize(access)?, a.materialize(access)?)?
                } else {
                    cat(a.materialize(access)?, b.materialize(access)?)?
                }
            }
            Node::Tensor(a, b) => {
                let shift = usize::from(access == Access::Controlled);
                let abits = a.basis.basis_bits().expect("basis");
                let bbits = b.basis.basis_bits().expect("basis");
                let axes: Vec<_> = (0..shift)
                    .chain((shift + abits)..(shift + abits + bbits))
                    .collect();
                cat(
                    a.materialize(access)?,
                    remapped(b.materialize(access)?, &axes),
                )?
            }
            Node::Repeat(n, a) => {
                let s = a.materialize(access)?;
                if s.len().saturating_mul(*n as usize) > MAX_CONTRACT_STEPS {
                    return Err(ContractError::Limit("static repetition exceeds 1024 steps"));
                }
                (0..*n).flat_map(|_| s.iter().cloned()).collect()
            }
            Node::Conjugate(a, b) => {
                let mut before = a.materialize(Access::Adjoint)?;
                let mut after = a.materialize(Access::Apply)?;
                if access == Access::Controlled {
                    let axes = (1..=bits).collect::<Vec<_>>();
                    before = remapped(before, &axes);
                    after = remapped(after, &axes);
                }
                cat(cat(before, b.materialize(access)?)?, after)?
            }
        };
        if steps.len() > MAX_CONTRACT_STEPS {
            return Err(ContractError::Limit("static circuit exceeds 1024 steps"));
        }
        Ok(steps)
    }
}
pub(super) fn called_static_names<'a>(op: &'a StaticOp, names: &mut Vec<&'a Ident>) {
    match &op.kind {
        StaticOpKind::Name(n) => names.push(n),
        StaticOpKind::Bind {
            implementation,
            meaning,
        } => names.extend([implementation, meaning]),
        StaticOpKind::Inverse(a) | StaticOpKind::Controlled(a) | StaticOpKind::Repeat(_, a) => {
            called_static_names(a, names)
        }
        StaticOpKind::Then(a, b) | StaticOpKind::Tensor(a, b) | StaticOpKind::Conjugate(a, b) => {
            called_static_names(a, names);
            called_static_names(b, names);
        }
    }
}

#[cfg(test)]
mod review_tests {
    use super::*;

    #[test]
    fn powers_preserve_exact_phase_with_logarithmic_matrix_work() {
        let t = Matrix::new(
            2,
            2,
            vec![Exact::one(), Exact::zero(), Exact::zero(), Exact::phase(1)],
        )
        .unwrap();
        for n in [0, 1, 2, 7, 8, 150, 4095, 4096] {
            // Independent root-of-unity expectation, not repeated multiplication.
            let expected = Matrix::new(
                2,
                2,
                vec![
                    Exact::one(),
                    Exact::zero(),
                    Exact::zero(),
                    Exact::phase(i32::from(n)),
                ],
            )
            .unwrap();
            let mut budget = Budget::new(8 + 24 * 16);
            assert_eq!(matrix_power(&t, n, &mut budget).unwrap(), expected);
        }
    }

    #[test]
    fn transformed_circuit_check_rejects_phase_control_and_axis_mutations() {
        let signature = BasisType::pair(BasisType::Bit, BasisType::Bit);
        let correct = CircuitStep {
            controls: vec![BitControl {
                index: 0,
                when_one: true,
            }],
            action: CircuitAction::Monomial {
                indices: vec![1],
                permutation: vec![0, 1],
                phases: vec![0, 7],
            },
        };
        // Adjoint(T) on the high bit controlled by the low bit: diag(1,1,1,zeta8^-1).
        let mut entries = vec![Exact::zero(); 16];
        for i in 0..4 {
            entries[5 * i] = Exact::one();
        }
        entries[15] = Exact::phase(-1);
        let expected = Matrix::new(4, 4, entries).unwrap();
        check_steps_meaning(
            &signature,
            std::slice::from_ref(&correct),
            &expected,
            &mut Budget::new(10_000),
        )
        .unwrap();
        let mut wrong_phase = correct.clone();
        let CircuitAction::Monomial { phases, .. } = &mut wrong_phase.action else {
            unreachable!()
        };
        phases[1] = 1;
        let mut wrong_control = correct.clone();
        wrong_control.controls[0].when_one = false;
        let mut wrong_axis = correct.clone();
        // A valid unconditional phase on the other axis is still the wrong operation.
        wrong_axis.controls.clear();
        let CircuitAction::Monomial { indices, .. } = &mut wrong_axis.action else {
            unreachable!()
        };
        indices[0] = 0;
        for candidate in [wrong_phase, wrong_control, wrong_axis] {
            // These are structurally admissible circuits, not malformed evidence.
            Circuit::new(signature.clone(), vec![candidate.clone()]).unwrap();
            assert_eq!(
                check_steps_meaning(
                    &signature,
                    &[candidate],
                    &expected,
                    &mut Budget::new(10_000)
                ),
                Err(ContractError::EquationMismatch)
            );
        }
    }
}
