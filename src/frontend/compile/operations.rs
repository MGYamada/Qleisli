//! Fixed-width descriptions are untrusted elaboration objects. Only retained
//! finite contract receipts can authorize an executable operation.
use super::*;
use crate::contract::{
    BasisType, Circuit, ContractError, FunctionEvidence, MAX_CONTRACT_BITS, MAX_CONTRACT_STEPS,
    exact::{Budget, Exact, Matrix},
    function::RetainedIdentity,
    meaning::{FiniteMeaning, MeaningEvidence},
};
use crate::frontend::formals;
use crate::frontend::resolve::locals::BindingKind;
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
}
#[derive(Debug, PartialEq)]
enum Node {
    Provider(Arc<FunctionEvidence>),
    Inverse(Operation),
    Then(Operation, Operation),
    Tensor(Operation, Operation),
    Controlled(Operation),
    Repeat(u16, Operation),
    Conjugate(Operation, Operation),
}
pub(super) type Bindings = BTreeMap<BinderKey, Operation>;

/// Required metadata from the complete checked declaration; never executable.
pub(super) struct RequiredOperation {
    pub(super) basis: Ty,
    pub(super) access: [bool; 3],
    pub(super) meaning: Option<Matrix>,
}
pub(super) fn access_index(access: Access) -> usize {
    formals::access_index(access)
}
pub(super) fn contract_basis(ty: &Ty) -> BasisType {
    match &ty.kind {
        Kind::Unit => BasisType::Unit,
        Kind::Bit => BasisType::Bit,
        Kind::Tuple(fields) if fields.len() == 2 => {
            BasisType::pair(contract_basis(&fields[0]), contract_basis(&fields[1]))
        }
        Kind::Tuple(fields) => BasisType::Tuple(fields.iter().map(contract_basis).collect()),
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
    pub(super) fn narrow_u8(
        &self,
        module: &str,
        span: Span,
        value: usize,
        field: &str,
    ) -> Result<u8, CompileError> {
        u8::try_from(value).map_err(|_| {
            self.error(
                module,
                span,
                ErrorCode::Limit,
                format!(
                    "{field} {value} exceeds the IR's u8 representation; no truncation is permitted"
                ),
            )
        })
    }
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
        let key_name = self.resolution.declaration(*key).name.clone();
        let (_, basis) = self.signature(key)?;
        contract_basis(&basis)
            .bits()
            .map_err(|e| self.op_error(&key_name.0, decl.span, e))?;
        if let FnBody::MeaningCompose { first, second }
        | FnBody::MeaningTensor {
            left: first,
            right: second,
        } = &decl.body
        {
            let left = self.meaning_key(&key_name.0, first)?;
            let right = self.meaning_key(&key_name.0, second)?;
            let dimension = 1usize
                << contract_basis(&basis)
                    .bits()
                    .map_err(|e| self.op_error(&key_name.0, decl.span, e))?;
            self.charge(&key_name.0, decl.span, dimension * 2)?;
            let left = &self.meanings[&left].target;
            let right = &self.meanings[&right].target;
            let target = if matches!(&decl.body, FnBody::MeaningTensor { .. }) {
                left.tensor(right)
            } else {
                left.compose(right)
            }
            .map_err(|e| self.op_error(&key_name.0, decl.span, e))?;
            let matrix = target
                .matrix(&mut self.exact_work)
                .map_err(|e| self.op_error(&key_name.0, decl.span, e))?;
            self.meanings.insert(
                *key,
                DeclaredMeaning {
                    basis,
                    target,
                    matrix,
                },
            );
            return Ok(());
        }
        let FnBody::Meaning {
            permutation,
            function,
        } = &decl.body
        else {
            unreachable!()
        };
        let Callee::User(fkey) = self.resolve(&key_name.0, function)? else {
            return Err(self.error(
                &key_name.0,
                function.span,
                ErrorCode::TypeMismatch,
                "meaning requires an ordinary total classical function",
            ));
        };
        let f = self.basis.get(&fkey).ok_or_else(|| {
            self.error(
                &key_name.0,
                function.span,
                ErrorCode::TypeMismatch,
                "meaning requires an ordinary total classical function",
            )
        })?;
        let result = if *permutation {
            basis.clone()
        } else {
            Ty::pair(Ty::bit(), Ty::pair(Ty::bit(), Ty::bit()))
        };
        if f.params != [basis.clone()] || f.result != result {
            return Err(self.error(
                &key_name.0,
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
                f.table
                    .iter()
                    .map(|x| {
                        self.narrow_u8(&key_name.0, function.span, usize::from(*x), "phase label")
                    })
                    .collect::<Result<_, _>>()?,
            )
        }
        .map_err(|e| self.op_error(&key_name.0, decl.span, e))?;
        let matrix = target
            .matrix(&mut self.exact_work)
            .map_err(|e| self.op_error(&key_name.0, decl.span, e))?;
        self.meanings.insert(
            *key,
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
    pub(super) fn required_bindings(
        &mut self,
        key: &Key,
    ) -> Result<BTreeMap<BinderKey, RequiredOperation>, CompileError> {
        let decl = self.declarations[key];
        let key_name = self.resolution.declaration(*key).name.clone();
        self.signature(key)?;
        let mut bindings = BTreeMap::new();
        for (ordinal, parameter) in decl.static_params.iter().enumerate() {
            let StaticParamKind::Operation {
                basis: original_basis,
                meaning: original_meaning,
            } = &parameter.kind
            else {
                return Err(self.error(
                    &key_name.0,
                    parameter.name.span,
                    ErrorCode::Unsupported,
                    "finite profile does not support Nat or Basis parameters",
                ));
            };
            let formal = &self.interfaces[key].statics[ordinal];
            let StaticKind::Operation {
                basis: checked_basis,
                meaning: checked_meaning,
                access,
            } = &formal.kind
            else {
                unreachable!("checked finite static category differs");
            };
            let binder = self.locals.info(self.locals.binder(&parameter.name));
            assert_eq!(
                binder.kind,
                BindingKind::StaticOperation,
                "finite Op binder"
            );
            assert_eq!(binder.key, formal.key, "checked formal lexical identity");
            let parameter_key = formal.key.clone();
            let access = *access;
            let meaning_key = *checked_meaning;
            assert_eq!(
                meaning_key.is_some(),
                original_meaning.is_some(),
                "checked Meaning refinement"
            );
            let mut work = self.work;
            let basis = finite_type(
                self,
                &mut work,
                &key_name.0,
                original_basis,
                checked_basis,
                Stage::Basis,
            );
            self.work = work;
            let basis = basis?;
            contract_basis(&basis)
                .bits()
                .map_err(|error| self.op_error(&key_name.0, original_basis.span, error))?;
            let meaning = if let Some(meaning_key) = meaning_key {
                let original_meaning = original_meaning
                    .as_ref()
                    .expect("paired Meaning refinement");
                assert_eq!(
                    self.locals.usage(original_meaning).target,
                    ResolvedUse::Global(Target::Declaration(meaning_key)),
                    "checked Meaning declaration identity"
                );
                let target = &self.meanings[&meaning_key];
                if target.basis != basis {
                    return Err(self.error(
                        &key_name.0,
                        original_meaning.span,
                        ErrorCode::TypeMismatch,
                        "parameter and meaning basis trees differ",
                    ));
                }
                let cost = target.matrix.entries().len();
                self.charge(&key_name.0, original_meaning.span, cost)?;
                Some(self.meanings[&meaning_key].matrix.clone())
            } else {
                None
            };
            bindings.insert(
                parameter_key,
                RequiredOperation {
                    basis,
                    access,
                    meaning,
                },
            );
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
                    "static provider requires an ordinary fn with inferred Unitary body effect"
                        .to_owned();
                if namespace == "std::quantum" && matches!(gate.as_str(), "h" | "x" | "z" | "t") {
                    message.push_str(&format!(
                        "; wrap the gate as `fn wrapped_gate(q: Q<Bit>) -> Q<Bit> {{ {}(q) }}` and pass `[wrapped_gate]`",
                        name.text
                    ));
                }
                return Err(self.error(module, name.span, ErrorCode::TypeMismatch, message));
            }
        };
        let decl = self.declarations[&key];
        let key_name = self.resolution.declaration(key).name.clone();
        if self.effects.get(&key).map(|fact| fact.inferred()) != Some(Effect::Unitary) {
            return Err(self.error(
                module,
                name.span,
                ErrorCode::Effect,
                crate::frontend::effects::unitary_required(
                    "static provider's inferred body effect must be Unitary",
                ),
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
        let Kind::Q(basis) = &result.kind else {
            return Err(self.error(
                module,
                name.span,
                ErrorCode::TypeMismatch,
                "static provider requires Q<A> -> Q<A>",
            ));
        };
        let ports = crate::frontend::types::UnaryInterface::new(&params, &result);
        if ports.is_none_or(|ports| ports.input != ports.output) {
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
        let cache = (key, mkey);
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
            format!("{}::{}", key_name.0, key_name.1),
            mkey.as_ref().map_or_else(
                || format!("{}::{}", key_name.0, key_name.1),
                |m| format!("meaning {}", self.resolution.path(*m)),
            ),
            sources,
        );
        let budget = &mut self.exact_work;
        let evidence = if let Some(mkey) = &mkey {
            MeaningEvidence::check_retained_with_kernel(
                &self.kernel,
                implementation,
                self.meanings[mkey].target.clone(),
                identity,
                budget,
            )
            .map(|e| e.receipt())
        } else {
            FunctionEvidence::check_retained_with_kernel(
                &self.kernel,
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
                basis = Ty::pair(Ty::bit(), basis);
                ([caps[2]; 3], Node::Controlled(a))
            }
            StaticOpKind::Repeat(count, ..) => {
                let Count::Natural(Natural {
                    kind: NatKind::Number(n),
                    ..
                }) = count
                else {
                    return Err(self.error(
                        module,
                        span,
                        ErrorCode::Unsupported,
                        "finite repetition requires a literal count",
                    ));
                };
                let n = u16::try_from(*n)
                    .ok()
                    .filter(|n| *n <= 4096)
                    .ok_or_else(|| {
                        self.error(
                            module,
                            span,
                            ErrorCode::Limit,
                            "static repetition exceeds 4096",
                        )
                    })?;
                (caps, Node::Repeat(n, a))
            }
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
                format!(
                    "missing {} access in the generic declaration",
                    formals::access_name(access)
                ),
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
        let steps = self
            .materialize(access)
            .map_err(|e| compiler.op_error(module, span, e))?;
        compiler.charge(module, span, total_size(steps.iter().map(circuit::size)))?;
        let basis = if access == Access::Controlled {
            Ty::pair(Ty::bit(), self.basis.clone())
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
