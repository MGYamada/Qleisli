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
    pub codomain: Ty,
    pub target: Option<crate::frontend::meaning::Target>,
    pub raw: Option<RawProgram>,
    pub references: Vec<Key>,
    pub matrix: Matrix,
    pub pure: Option<Arc<crate::interchange::pure_leaf::CheckedPureLeaf>>,
}
#[derive(Clone, Debug)]
pub(super) struct Operation {
    pub basis: Ty,
    pub codomain: Ty,
    pub access: [bool; 3],
    pub meaning: Option<Matrix>,
    pub effect: Effect,
    pub(super) node: Arc<Node>,
    /// Untrusted original provider occurrence, retained for paired source/body
    /// transport. Native receipts and whole-source equations remain separate.
    pub(super) source_origin: Option<Arc<ProviderOrigin>>,
    /// A real original Op-formal reference keeps its declaration instance and
    /// mixed-kind ordinal. The actual provider never substitutes for this gate.
    pub(super) source_formal: Option<Arc<FormalOrigin>>,
    depth: usize,
    nodes: usize,
}
pub(super) struct CachedProvider {
    pub operation: Operation,
    pub body: AcceptedProgram,
}

#[derive(Clone)]
pub(super) struct ProviderOrigin {
    pub(super) definition: Key,
    pub(super) table: Arc<crate::frontend::resolve::locals::Table>,
    pub(super) instance: Option<Arc<super::instances::ClosedInstance>>,
    pub(super) meaning: Option<Key>,
    /// The exact original lowering whose contexts and programs will be encoded
    /// into the one fresh v5 graph. This handle does not authorize that graph.
    pub(super) body: AcceptedProgram,
}

impl std::fmt::Debug for ProviderOrigin {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ProviderOrigin")
            .field("definition", &self.definition)
            .field("meaning", &self.meaning)
            .field(
                "instance",
                &self.instance.as_ref().map(|instance| instance.record),
            )
            .finish_non_exhaustive()
    }
}

#[derive(Clone)]
pub(super) struct FormalOrigin {
    pub(super) definition: Key,
    pub(super) table: Arc<crate::frontend::resolve::locals::Table>,
    // Nonconcrete dormant probes retain the original formal but have no actual
    // instance. A v5 encoder must refuse those incomplete producer objects.
    pub(super) instance: Option<Arc<super::instances::ClosedInstance>>,
    pub(super) ordinal: usize,
}

impl std::fmt::Debug for FormalOrigin {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FormalOrigin")
            .field("definition", &self.definition)
            .field("ordinal", &self.ordinal)
            .field("concrete", &self.instance.is_some())
            .finish_non_exhaustive()
    }
}
#[derive(Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub(super) enum ProviderRoot {
    Raw,
    Ordinary,
    Runtime,
}
impl ProviderRoot {
    pub(super) fn of(body: &AcceptedProgram) -> Self {
        if body.runtime_result().is_some() {
            Self::Runtime
        } else if body.ordinary_result().is_some() {
            Self::Ordinary
        } else {
            Self::Raw
        }
    }
}
#[derive(Debug)]
pub(super) enum Node {
    Provider(Arc<FunctionEvidence>),
    Carrier(Option<Vec<CircuitStep>>),
    Pure(PureProvider),
    Inverse(Operation),
    Then(Operation, Operation),
    Tensor(Operation, Operation),
    Controlled(Operation),
    Repeat(u16, Operation),
    Conjugate(Operation, Operation),
    Requested(Key, Operation),
}
#[derive(Clone, Copy)]
pub(super) enum Constructor {
    Inverse,
    Then,
    Tensor,
    Controlled,
    Repeat(u16),
    Conjugate,
}
#[derive(Clone, Debug)]
pub(super) struct PureProvider {
    pub(super) origin: Option<Arc<PureOrigin>>,
    pub(super) leaf: Arc<crate::interchange::pure_leaf::CheckedPureLeaf>,
    pub(super) inverse: Option<Arc<FunctionEvidence>>,
}
#[derive(Debug)]
pub(super) struct PureOrigin {
    pub(super) definition: Key,
    pub(super) table: Arc<crate::frontend::resolve::locals::Table>,
    pub(super) meaning: Option<Key>,
    pub(super) equation: Arc<crate::interchange::pure_leaf::SourcePureEquation>,
}
mod bindings;
mod carrier;
#[cfg(test)]
mod identity_tests;
mod pure;
mod source;
pub(super) type Bindings = BTreeMap<BinderKey, Operation>;

/// Bounded port-copy work, including nominal fields and their retained metadata.
pub(super) fn port_nodes(ty: &Ty) -> usize {
    match &ty.kind {
        Kind::Q(child) => 1 + port_nodes(child),
        Kind::Tuple(fields) => fields.iter().fold(1usize, |cells, field| {
            cells.saturating_add(port_nodes(field))
        }),
        Kind::Nominal(nominal) => nominal.fields().fold(
            1usize.saturating_add(nominal.metadata_cells()),
            |cells, field| cells.saturating_add(port_nodes(field)),
        ),
        _ => 1,
    }
}

/// Owned type cloning shares immutable original source identities.
pub(super) fn port_copy_nodes(ty: &Ty) -> usize {
    match &ty.kind {
        Kind::Q(child) => 1 + port_copy_nodes(child),
        Kind::Tuple(fields) => fields.iter().fold(1usize, |cells, field| {
            cells.saturating_add(port_copy_nodes(field))
        }),
        Kind::Nominal(nominal) => nominal.fields().fold(
            1usize.saturating_add(nominal.metadata_copy_cells()),
            |cells, field| cells.saturating_add(port_copy_nodes(field)),
        ),
        _ => 1,
    }
}

/// Required metadata from the complete checked declaration; never executable.
pub(super) struct RequiredOperation {
    pub(super) basis: Ty,
    pub(super) codomain: Ty,
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
        Kind::Bits(size) => BasisType::Bits(*size),
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
pub(super) fn controlled(steps: Vec<CircuitStep>, bits: usize) -> Vec<CircuitStep> {
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
    /// This registry counts distinct descriptions; it is not an executable
    /// cache. Callers discharge actual ports/access/Meaning before every visit.
    #[cfg(test)]
    pub(super) fn record_operation_instance(
        &mut self,
        definition: Key,
        identity: Vec<Operation>,
        module: &str,
        span: Span,
    ) -> Result<(), CompileError> {
        if identity.is_empty() {
            return Ok(());
        }
        let source_effect = self.effect_in_module(module, definition).ok_or_else(|| {
            self.error(
                module,
                span,
                ErrorCode::Effect,
                "specialization has no available source effect",
            )
        })?;
        self.charge(module, span, identity.len())?;
        self.record_instance_identity(
            instances::Identity {
                definition,
                arguments: identity
                    .into_iter()
                    .map(instances::Argument::Operation)
                    .collect(),
                source_effect,
            },
            module,
            span,
        )?;
        Ok(())
    }

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
        let key_name = self.source.resolution.declaration(*key).name.clone();
        let (_, codomain) = self.signature(key)?;
        let interface = &self.source.interfaces[key];
        let mut work = self.work;
        let basis = finite_type(
            self,
            &mut work,
            &key_name.0,
            decl.meaning_domain.as_ref().unwrap_or(&decl.return_type),
            interface.meaning_input(),
            Stage::Basis,
        )?;
        self.work = work;
        let typed = basis.basis_bits().is_none() || codomain.basis_bits().is_none();
        if typed {
            self.basis_codes(&key_name.0, decl.span, &basis)?;
            self.basis_codes(&key_name.0, decl.span, &codomain)?;
        } else {
            contract_basis(&basis)
                .bits()
                .map_err(|e| self.op_error(&key_name.0, decl.span, e))?;
        }
        if let FnBody::MeaningReference { function } = &decl.body {
            let Callee::User(reference) = self.resolve(&key_name.0, function)? else {
                unreachable!("common reference judgment requires an ordinary definition")
            };
            let ceiling = if basis == codomain {
                Effect::Unitary
            } else {
                Effect::Isometry
            };
            if self
                .effect_in_module(&key_name.0, reference)
                .is_none_or(|effect| effect > ceiling)
            {
                return Err(self.error(
                    &key_name.0,
                    function.span,
                    ErrorCode::Effect,
                    "Meaning reference requires an available pure source effect",
                ));
            }
            if typed {
                let body = self
                    .checked
                    .get(&reference)
                    .ok_or_else(|| {
                        self.error(
                            &key_name.0,
                            function.span,
                            ErrorCode::InvalidIr,
                            "original reference function has not been independently checked",
                        )
                    })?
                    .clone();
                let matrix =
                    self.carrier_program_action(&key_name.0, decl.span, &basis, &codomain, &body)?;
                self.retain_carrier_meaning(*key, basis, codomain, matrix, vec![reference]);
                return Ok(());
            }
            let target = crate::frontend::meaning::Target::reference(
                contract_basis(&basis),
                contract_basis(&codomain),
                reference,
            )
            .map_err(|e| self.op_error(&key_name.0, function.span, e))?;
            return self.finish_meaning(key, basis, codomain, target);
        }
        if let FnBody::MeaningCompose { first, second }
        | FnBody::MeaningTensor {
            left: first,
            right: second,
        } = &decl.body
        {
            let left = self.meaning_key(&key_name.0, first)?;
            let right = self.meaning_key(&key_name.0, second)?;
            let tensor = matches!(&decl.body, FnBody::MeaningTensor { .. });
            if typed
                || self.meanings[&left].target.is_none()
                || self.meanings[&right].target.is_none()
            {
                self.basis_codes(&key_name.0, decl.span, &basis)?;
                self.basis_codes(&key_name.0, decl.span, &codomain)?;
                let a = &self.meanings[&left];
                let b = &self.meanings[&right];
                let matrix = if tensor {
                    a.matrix.tensor(&b.matrix, &mut self.exact_work)
                } else {
                    b.matrix.compose(&a.matrix, &mut self.exact_work)
                }
                .map_err(|e| self.op_error(&key_name.0, decl.span, e.into()))?;
                self.charge(
                    &key_name.0,
                    decl.span,
                    self.meanings[&left].references.len() + self.meanings[&right].references.len(),
                )?;
                let references = self.meanings[&left]
                    .references
                    .iter()
                    .chain(&self.meanings[&right].references)
                    .copied()
                    .collect();
                self.retain_carrier_meaning(*key, basis, codomain, matrix, references);
                return Ok(());
            }
            let dimension = 1usize
                << contract_basis(&basis)
                    .bits()
                    .map_err(|e| self.op_error(&key_name.0, decl.span, e))?;
            self.charge(&key_name.0, decl.span, dimension * 2)?;
            let left = self.meanings[&left]
                .target
                .as_ref()
                .expect("built-in Meaning");
            let right = self.meanings[&right]
                .target
                .as_ref()
                .expect("built-in Meaning");
            let target = if tensor {
                left.tensor(right)
            } else {
                left.compose(right)
            }
            .map_err(|e| self.op_error(&key_name.0, decl.span, e))?;
            return self.finish_meaning(key, basis, codomain, target);
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
        self.prepare_required_classical_table(fkey, &key_name.0, function.span)?;
        let nominal = if self.deferred_nominal_tables.contains(&fkey) {
            Some(self.nominal_meaning_table(fkey)?)
        } else {
            None
        };
        let f = if let Some(table) = &nominal {
            table
        } else {
            self.basis.get(&fkey).ok_or_else(|| {
                self.missing_basis_error(
                    &key_name.0,
                    function.span,
                    &fkey,
                    "meaning requires an ordinary total classical function",
                )
            })?
        };
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
        if typed {
            let length = f.table.len();
            self.charge(&key_name.0, decl.span, length)?;
            let f = nominal.as_ref().unwrap_or_else(|| &self.basis[&fkey]);
            let labels = f.table.clone();
            let matrix =
                self.carrier_table_action(&key_name.0, decl.span, &basis, *permutation, &labels)?;
            self.retain_carrier_meaning(*key, basis, codomain, matrix, Vec::new());
            return Ok(());
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
        self.finish_meaning(
            key,
            basis.clone(),
            basis,
            crate::frontend::meaning::Target::monomial(target),
        )
    }
    fn finish_meaning(
        &mut self,
        key: &Key,
        basis: Ty,
        codomain: Ty,
        target: crate::frontend::meaning::Target,
    ) -> Result<(), CompileError> {
        let declaration = self.declarations[key];
        let name = self.source.resolution.declaration(*key).name.clone();
        let span = declaration.span;
        let (raw, matrix, pure) = if let Ok(finite) = target.finite() {
            let raw = finite
                .target_ir()
                .map_err(|e| self.op_error(&name.0, span, e))?;
            let matrix = finite
                .matrix(&mut self.exact_work)
                .map_err(|e| self.op_error(&name.0, span, e))?;
            (raw, matrix, None)
        } else {
            let sources = self.retained_sources(&name.0, span, &[*key], &Bindings::new(), &[])?;
            let path = self.source.resolution.path(*key);
            let identity =
                || RetainedIdentity::interned(path.clone(), path.clone(), sources.clone());
            let mut references = BTreeMap::new();
            for id in target.references() {
                let program = self.checked.get(&id).ok_or_else(|| {
                    self.error(
                        &name.0,
                        span,
                        ErrorCode::InvalidIr,
                        "original reference function has not been independently checked",
                    )
                })?;
                references.insert(id, program.program().clone());
            }
            let raw = target
                .materialize(&self.kernel, &references, &identity, &mut self.exact_work)
                .map_err(|e| self.op_error(&name.0, span, e))?;
            let evidence = crate::frontend::pure::check(
                &self.kernel,
                &raw,
                target.signature(),
                target.codomain(),
                None,
                &mut self.exact_work,
            )
            .map_err(|e| self.op_error(&name.0, span, e))?;
            (raw, evidence.meaning().clone(), Some(Arc::new(evidence)))
        };
        self.charge(&name.0, span, target.cells())?;
        let references = target.reference_occurrences().collect();
        self.meanings.insert(
            *key,
            DeclaredMeaning {
                basis,
                codomain,
                target: Some(target),
                raw: Some(raw),
                references,
                matrix,
                pure,
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
    pub(super) fn required_bindings_closed(
        &mut self,
        key: &Key,
        closed: &super::super::closed::ClosedInterface,
    ) -> Result<BTreeMap<BinderKey, RequiredOperation>, CompileError> {
        let decl = self.declarations[key];
        let module = self.dormant_module(*key, decl.span)?;
        self.charge(&module, decl.span, decl.static_params.len() + 1)?;
        let mut bindings = BTreeMap::new();
        for (ordinal, parameter) in decl.static_params.iter().enumerate() {
            let StaticParamKind::Operation {
                basis: original_basis,
                codomain: original_codomain,
                meaning: original_meaning,
            } = &parameter.kind
            else {
                continue;
            };
            self.charge(
                &module,
                parameter.name.span,
                self.source.interfaces[key].statics[ordinal].key.name.len()
                    + parameter.name.text.len()
                    + 3,
            )?;
            let formal = &self.source.interfaces[key].statics[ordinal];
            let StaticKind::Operation {
                basis: _,
                codomain: _,
                meaning: checked_meaning,
                access,
            } = &formal.kind
            else {
                unreachable!("checked finite static category differs");
            };
            let binder = self.locals().info(self.locals().binder(&parameter.name));
            assert_eq!(
                binder.kind,
                BindingKind::StaticOperation,
                "finite Op binder"
            );
            assert_eq!(binder.key, formal.key, "checked formal lexical identity");
            let parameter_key = formal.key.clone();
            let access = *access;
            let meaning_key = *checked_meaning;
            let checked_operation = &closed.operations[&parameter_key];
            let checked_basis = checked_operation
                .input
                .quantum_basis()
                .expect("closed operation input owner");
            let checked_codomain = checked_operation
                .output()
                .quantum_basis()
                .expect("closed operation output owner");
            assert_eq!(
                meaning_key.is_some(),
                original_meaning.is_some(),
                "checked Meaning refinement"
            );
            let mut work = self.work;
            let basis = finite_type(
                self,
                &mut work,
                &module,
                original_basis,
                checked_basis,
                Stage::Basis,
            );
            self.work = work;
            let basis = basis?;
            let mut work = self.work;
            let codomain = finite_type(
                self,
                &mut work,
                &module,
                original_codomain.as_deref().unwrap_or(original_basis),
                checked_codomain,
                Stage::Basis,
            );
            self.work = work;
            let codomain = codomain?;
            for (port, span) in [
                (&basis, original_basis.span),
                (&codomain, parameter.name.span),
            ] {
                if port.basis_bits().is_none() {
                    self.basis_codes(&module, span, port)?;
                } else {
                    contract_basis(port)
                        .bits()
                        .map_err(|e| self.op_error(&module, span, e))?;
                }
            }
            let meaning = if let Some(meaning_key) = meaning_key {
                let original_meaning = original_meaning
                    .as_ref()
                    .expect("paired Meaning refinement");
                assert_eq!(
                    self.locals().usage(original_meaning).target,
                    ResolvedUse::Global(Target::Declaration(meaning_key)),
                    "checked Meaning declaration identity"
                );
                let target = &self.meanings[&meaning_key];
                let mut work = self.work;
                let same = (|| {
                    let mut charge =
                        |cells| self.charge_at(&mut work, &module, original_meaning.span, cells);
                    Ok::<_, CompileError>(
                        same_port_budgeted(&target.basis, &basis, &mut charge)?
                            && same_port_budgeted(&target.codomain, &codomain, &mut charge)?,
                    )
                })();
                self.work = work;
                if !same? {
                    return Err(self.error(
                        &module,
                        original_meaning.span,
                        ErrorCode::TypeMismatch,
                        "parameter and meaning basis trees differ",
                    ));
                }
                let cost = self.meanings[&meaning_key].matrix.entries().len();
                self.charge(&module, original_meaning.span, cost)?;
                Some(self.meanings[&meaning_key].matrix.clone())
            } else {
                None
            };
            bindings.insert(
                parameter_key,
                RequiredOperation {
                    basis,
                    codomain,
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
            Callee::Primitive(primitive) => {
                let mut message =
                    "static provider requires an ordinary fn with inferred Unitary body effect"
                        .to_owned();
                if primitive == PrimitiveId::H {
                    message.push_str(&format!(
                        "; wrap the gate as `fn wrapped_gate(q: Q<Bit>) -> Q<Bit> {{ {}(q) }}` and pass `[wrapped_gate]`",
                        name.text
                    ));
                }
                return Err(self.error(module, name.span, ErrorCode::TypeMismatch, message));
            }
        };
        let decl = self.declarations[&key];
        let effect = self.effect_in_module(module, key).ok_or_else(|| {
            self.error(
                module,
                name.span,
                ErrorCode::Effect,
                "static provider has no available source effect",
            )
        })?;
        if effect > Effect::Isometry {
            return Err(self.error(
                module,
                name.span,
                ErrorCode::Effect,
                "static provider's available source effect must be at most Isometry",
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
        let Kind::Q(codomain) = &result.kind else {
            return Err(self.error(
                module,
                name.span,
                ErrorCode::TypeMismatch,
                "static provider requires Q<A> -> Q<B>",
            ));
        };
        let ports = crate::frontend::types::UnaryInterface::new(&params, &result);
        if ports.is_none() {
            return Err(self.error(
                module,
                name.span,
                ErrorCode::TypeMismatch,
                "static provider requires one quantum input and output",
            ));
        }
        let Kind::Q(basis) = &params[0].kind else {
            unreachable!("quantum unary interface")
        };
        let mkey = meaning.map(|m| self.meaning_key(module, m)).transpose()?;
        if mkey.is_none() && (basis.basis_bits().is_none() || codomain.basis_bits().is_none()) {
            return Err(self.error(
                module,
                name.span,
                ErrorCode::Unsupported,
                "typed provider requires an original checked Meaning occurrence",
            ));
        }
        if let Some(mkey) = &mkey {
            if self.meanings[mkey].basis != **basis || self.meanings[mkey].codomain != **codomain {
                return Err(self.error(
                    module,
                    name.span,
                    ErrorCode::TypeMismatch,
                    "provider and meaning basis trees differ",
                ));
            }
        }
        // A same-module Unitary provider must never lend inverse/control access
        // to a caller whose public contract only promises Isometry.
        let program = self.checked.get(&key).ok_or_else(|| {
            self.error(
                module,
                name.span,
                ErrorCode::InvalidIr,
                "provider has not been independently checked",
            )
        })?;
        let cache = (key, mkey, effect, ProviderRoot::of(program));
        if let Some(op) = self.providers.get(&cache) {
            let cost = op
                .body
                .artifact()
                .len()
                .saturating_add(program.artifact().len())
                .saturating_add(op.operation.copy_size());
            self.charge(module, name.span, cost)?;
            if self.providers[&cache].body.artifact() != self.checked[&key].artifact() {
                return Err(self.error(
                    module,
                    name.span,
                    ErrorCode::Contract,
                    "cached provider has a different freshly checked Raw/source graph",
                ));
            }
            return Ok(self.providers[&cache].operation.clone());
        }
        self.charge(
            module,
            name.span,
            basis.tree_size().nodes
                + codomain.tree_size().nodes
                + codomain.basis_bits().unwrap_or(0)
                + 8,
        )?;
        let program = self
            .checked
            .get(&key)
            .ok_or_else(|| {
                self.error(
                    module,
                    name.span,
                    ErrorCode::InvalidIr,
                    "provider has not been independently checked",
                )
            })?
            .clone();
        let operation = self.provider_program(
            module,
            name.span,
            key,
            mkey,
            false,
            effect,
            (**basis).clone(),
            (**codomain).clone(),
            &program,
            &Bindings::new(),
        )?;
        self.charge(module, name.span, operation.copy_size() + 1)?;
        self.providers.insert(
            cache,
            CachedProvider {
                operation: operation.clone(),
                body: program,
            },
        );
        Ok(operation)
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn provider_program(
        &mut self,
        module: &str,
        span: Span,
        key: Key,
        meaning: Option<Key>,
        inside_formal_meaning: bool,
        effect: Effect,
        basis: Ty,
        codomain: Ty,
        program: &AcceptedProgram,
        bindings: &Bindings,
    ) -> Result<Operation, CompileError> {
        if basis.basis_bits().is_none()
            || codomain.basis_bits().is_none()
            || meaning.is_some_and(|key| self.meanings[&key].target.is_none())
        {
            return self.carrier_provider_program(
                module,
                span,
                key,
                meaning,
                inside_formal_meaning,
                effect,
                basis,
                codomain,
                program,
            );
        }
        contract_basis(&basis)
            .bits()
            .map_err(|error| self.op_error(module, span, error))?;
        contract_basis(&codomain)
            .bits()
            .map_err(|error| self.op_error(module, span, error))?;
        if effect == Effect::Isometry || basis != codomain {
            return self.pure_provider_program(
                module, span, key, meaning, basis, codomain, effect, program, bindings,
            );
        }
        let raw = program.raw();
        let raw_work = crate::frontend::raw_state::operations_size(&raw.operations)
            .saturating_add(raw.classical_inputs.len())
            .saturating_add(raw.classical_outputs.len())
            .saturating_add(raw.quantum_outputs.len())
            .saturating_add(total_size(
                raw.quantum_inputs.iter().map(|port| port.wires.len() + 3),
            ));
        self.charge(module, span, raw_work.saturating_mul(2))?;
        let implementation = raw.clone();
        let roots: Vec<_> = [Some(key), meaning].into_iter().flatten().collect();
        let sources = self.retained_sources(module, span, &roots, bindings, &[program.raw()])?;
        let identity = RetainedIdentity::interned(
            self.source.resolution.path(key),
            meaning.map_or_else(
                || self.source.resolution.path(key),
                |meaning| format!("meaning {}", self.source.resolution.path(meaning)),
            ),
            sources,
        );
        let evidence = if let Some(meaning) = meaning {
            let target = &self.meanings[&meaning];
            let legacy = target.target.as_ref().expect("built-in Meaning provider");
            if let Ok(finite) = legacy.finite() {
                MeaningEvidence::check_retained_with_kernel(
                    &self.kernel,
                    implementation,
                    finite.clone(),
                    identity,
                    &mut self.exact_work,
                )
                .map(|evidence| evidence.receipt())
            } else {
                FunctionEvidence::check_retained_with_kernel(
                    &self.kernel,
                    legacy.signature().clone(),
                    implementation,
                    target.raw.as_ref().expect("built-in Meaning body").clone(),
                    identity,
                    &mut self.exact_work,
                )
                .map(Arc::new)
                .map_err(|error| error.error)
            }
        } else {
            FunctionEvidence::check_retained_with_kernel(
                &self.kernel,
                contract_basis(&basis),
                implementation.clone(),
                implementation,
                identity,
                &mut self.exact_work,
            )
            .map(Arc::new)
            .map_err(|error| error.error)
        }
        .map_err(|error| self.op_error(module, span, error))?;
        let operation = Operation {
            basis,
            codomain,
            access: [true; 3],
            meaning: Some(evidence.meaning().clone()),
            effect,
            node: Arc::new(Node::Provider(evidence)),
            source_origin: Some(self.provider_origin(key, meaning, program, module, span)?),
            source_formal: None,
            depth: 1,
            nodes: 1,
        };
        self.charge(module, span, operation.copy_size())?;
        Ok(operation)
    }

    pub(super) fn provider_origin(
        &mut self,
        definition: Key,
        meaning: Option<Key>,
        body: &AcceptedProgram,
        module: &str,
        span: Span,
    ) -> Result<Arc<ProviderOrigin>, CompileError> {
        // AcceptedProgram shares its immutable graph and context Arcs. Its
        // ordered output-port vector is copied with the retained wrapper.
        self.charge(
            module,
            span,
            16 + total_size(body.output_ports().iter().map(|port| port.wires.len() + 3)),
        )?;
        Ok(Arc::new(ProviderOrigin {
            definition,
            table: Arc::clone(&self.source.lexical[&definition]),
            instance: None,
            meaning,
            body: body.clone(),
        }))
    }

    pub(super) fn retain_source_formal(
        &mut self,
        mut operation: Operation,
        owner: Key,
        key: &BinderKey,
        module: &str,
        span: Span,
    ) -> Result<Operation, CompileError> {
        self.charge(
            module,
            span,
            key.name
                .len()
                .saturating_mul(self.source.interfaces[&owner].statics.len() + 1)
                .saturating_add(8),
        )?;
        let ordinal = self.source.interfaces[&owner]
            .statics
            .iter()
            .position(|formal| {
                formal.key == *key && matches!(formal.kind, StaticKind::Operation { .. })
            })
            .ok_or_else(|| {
                self.error(
                    module,
                    span,
                    ErrorCode::InvalidIr,
                    "Op reference lost its original mixed-kind formal ordinal",
                )
            })?;
        let instance = self
            .concrete_context
            .current
            .as_ref()
            .filter(|instance| instance.definition == owner)
            .cloned();
        operation.source_formal = Some(Arc::new(FormalOrigin {
            definition: owner,
            table: Arc::clone(&self.source.lexical[&owner]),
            instance,
            ordinal,
        }));
        Ok(operation)
    }
    pub(super) fn construct_closed(
        &mut self,
        module: &str,
        span: Span,
        kind: Constructor,
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
        self.charge(
            module,
            span,
            nodes
                .saturating_add(a.copy_size().saturating_mul(2))
                .saturating_add(
                    b.as_ref()
                        .map_or(0, |operation| operation.copy_size().saturating_mul(2)),
                ),
        )?;
        let mut basis = a.basis.clone();
        let mut codomain = a.codomain.clone();
        let effect = a
            .effect
            .max(b.as_ref().map_or(Effect::Unitary, |b| b.effect));
        let caps = a.access;
        if let Some(b) = &b {
            if match kind {
                Constructor::Then => a.codomain != b.basis,
                Constructor::Conjugate => a.basis != b.basis || b.basis != b.codomain,
                _ => false,
            } {
                return Err(self.error(
                    module,
                    span,
                    ErrorCode::TypeMismatch,
                    format!("static composition requires identical basis trees: expected `Op<{}>`, found `Op<{}>`", a.basis, b.basis),
                ));
            }
        }
        let (access, node) = match kind {
            Constructor::Inverse => {
                std::mem::swap(&mut basis, &mut codomain);
                ([caps[1], caps[0], caps[2]], Node::Inverse(a))
            }
            Constructor::Controlled => {
                if basis != codomain {
                    return Err(self.error(
                        module,
                        span,
                        ErrorCode::TypeMismatch,
                        "control requires identical input/output types",
                    ));
                }
                basis = Ty::pair(Ty::bit(), basis);
                codomain = basis.clone();
                ([caps[2]; 3], Node::Controlled(a))
            }
            Constructor::Repeat(n) => {
                if basis != codomain {
                    return Err(self.error(
                        module,
                        span,
                        ErrorCode::TypeMismatch,
                        "repeat requires identical input/output types",
                    ));
                }
                if n > 4096 {
                    return Err(self.error(
                        module,
                        span,
                        ErrorCode::Limit,
                        "static repetition exceeds 4096",
                    ));
                }
                (caps, Node::Repeat(n, a))
            }
            Constructor::Then | Constructor::Tensor | Constructor::Conjugate => {
                let b = b.expect("binary constructor");
                let mut access = std::array::from_fn(|i| caps[i] && b.access[i]);
                let node = match kind {
                    Constructor::Then => {
                        codomain = b.codomain.clone();
                        Node::Then(a, b)
                    }
                    Constructor::Tensor => {
                        basis = Ty::pair(basis, b.basis.clone());
                        codomain = Ty::pair(codomain, b.codomain.clone());
                        Node::Tensor(a, b)
                    }
                    _ => {
                        basis = a.codomain.clone();
                        codomain = basis.clone();
                        access = std::array::from_fn(|i| caps[0] && caps[1] && b.access[i]);
                        Node::Conjugate(a, b)
                    }
                };
                (access, node)
            }
        };
        self.check_tree(module, span, basis.tree_size())?;
        self.check_tree(module, span, codomain.tree_size())?;
        for port in [&basis, &codomain] {
            if port.basis_bits().is_none() {
                self.basis_codes(module, span, port)?;
            } else {
                contract_basis(port)
                    .bits()
                    .map_err(|e| self.op_error(module, span, e))?;
            }
        }
        let meaning = node
            .meaning(&mut self.exact_work)
            .map_err(|e| self.op_error(module, span, e))?;
        Ok(Operation {
            basis,
            codomain,
            access,
            meaning,
            effect,
            node: Arc::new(node),
            source_origin: None,
            source_formal: None,
            depth,
            nodes,
        })
    }

    pub(super) fn validate_operation_meaning(
        &mut self,
        operation: &Operation,
        meaning: Key,
        module: &str,
        span: Span,
    ) -> Result<(), CompileError> {
        let expected = self.meanings.get(&meaning).ok_or_else(|| {
            self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "operation specification is not an original Meaning",
            )
        })?;
        let cost = port_nodes(&expected.basis)
            + port_nodes(&expected.codomain)
            + expected.matrix.entries().len()
            + 1;
        self.charge(module, span, cost)?;
        let expected = &self.meanings[&meaning];
        let required = RequiredOperation {
            basis: expected.basis.clone(),
            codomain: expected.codomain.clone(),
            access: [false; 3],
            meaning: Some(expected.matrix.clone()),
        };
        self.validate_required_operation(&required, operation, module, span)
    }

    pub(super) fn bind_operation_meaning(
        &mut self,
        operation: Operation,
        meaning: Key,
        module: &str,
        span: Span,
    ) -> Result<Operation, CompileError> {
        self.validate_operation_meaning(&operation, meaning, module, span)?;
        if operation.depth >= MAX_DEPTH || operation.nodes >= MAX_TREE_NODES {
            return Err(self.error(
                module,
                span,
                ErrorCode::Limit,
                "checked_op description exceeds its node/depth limit",
            ));
        }
        self.charge(module, span, operation.copy_size() + 2)?;
        Ok(Operation {
            basis: operation.basis.clone(),
            codomain: operation.codomain.clone(),
            access: operation.access,
            effect: operation.effect,
            meaning: operation.meaning.clone(),
            depth: operation.depth + 1,
            nodes: operation.nodes + 1,
            node: Arc::new(Node::Requested(meaning, operation)),
            source_origin: None,
            source_formal: None,
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
            Self::Carrier(_) => unreachable!("carrier leaves retain their logical matrix"),
            Self::Pure(e) => Some(e.leaf.meaning().clone()),
            Self::Requested(_, operation) => operation.meaning.clone(),
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
                    let dimension = if let Some(matrix) = &a.meaning {
                        matrix.cols()
                    } else {
                        1 << a
                            .basis
                            .basis_bits()
                            .ok_or(ContractError::EvidenceMismatch)?
                    };
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
    pub(super) fn uses_carrier(&self) -> bool {
        match self.node.as_ref() {
            Node::Carrier(_) => true,
            Node::Provider(_) | Node::Pure(_) => false,
            Node::Requested(_, child)
            | Node::Inverse(child)
            | Node::Controlled(child)
            | Node::Repeat(_, child) => child.uses_carrier(),
            Node::Then(left, right) | Node::Tensor(left, right) | Node::Conjugate(left, right) => {
                left.uses_carrier() || right.uses_carrier()
            }
        }
    }

    /// Compare complete private descriptions without expanding their issued
    /// native receipts. Equal matrices alone do not identify an operation.
    /// Construction bounds description depth/nodes before this traversal;
    /// every visited field and temporary type-stack entry is charged first.
    pub(super) fn same_descriptor_budgeted<E>(
        &self,
        other: &Self,
        charge: &mut impl FnMut(usize) -> Result<(), E>,
    ) -> Result<bool, E> {
        charge(1)?;
        if self.access != other.access
            || self.effect != other.effect
            || self.depth != other.depth
            || self.nodes != other.nodes
        {
            return Ok(false);
        }
        charge(1)?;
        match (&self.source_origin, &other.source_origin) {
            (Some(left), Some(right)) if !Arc::ptr_eq(left, right) => return Ok(false),
            (None, None) | (Some(_), Some(_)) => {}
            _ => return Ok(false),
        }
        match (&self.source_formal, &other.source_formal) {
            (Some(left), Some(right)) => {
                charge(4)?;
                if left.definition != right.definition
                    || left.ordinal != right.ordinal
                    || !Arc::ptr_eq(&left.table, &right.table)
                    || match (&left.instance, &right.instance) {
                        (Some(left), Some(right)) => !Arc::ptr_eq(left, right),
                        (None, None) => false,
                        _ => true,
                    }
                {
                    return Ok(false);
                }
            }
            (None, None) => {}
            _ => return Ok(false),
        }
        if !same_port_budgeted(&self.basis, &other.basis, charge)?
            || !same_port_budgeted(&self.codomain, &other.codomain, charge)?
            || !same_meaning_budgeted(self.meaning.as_ref(), other.meaning.as_ref(), charge)?
        {
            return Ok(false);
        }
        charge(1)?;
        if Arc::ptr_eq(&self.node, &other.node) {
            // The shared node is immutable, including every child and issued
            // dependency. Root ports/effect/access/Meaning were still checked.
            return Ok(true);
        }
        Ok(match (&*self.node, &*other.node) {
            (Node::Provider(a), Node::Provider(b)) => {
                charge(1)?;
                a == b // FunctionEvidence compares issued proof identity only.
            }
            (Node::Carrier(Some(a)), Node::Carrier(Some(b))) => {
                charge(total_size(a.iter().chain(b).map(circuit::size)))?;
                a == b
            }
            (Node::Carrier(None), Node::Carrier(None)) => true,
            (Node::Pure(a), Node::Pure(b)) => {
                charge(3)?;
                Arc::ptr_eq(&a.leaf, &b.leaf)
                    && a.inverse == b.inverse
                    && match (&a.origin, &b.origin) {
                        (Some(a), Some(b)) => Arc::ptr_eq(a, b),
                        (None, None) => true,
                        _ => false,
                    }
            }
            (Node::Inverse(a), Node::Inverse(b)) | (Node::Controlled(a), Node::Controlled(b)) => {
                charge(1)?;
                a.same_descriptor_budgeted(b, charge)?
            }
            (Node::Repeat(n, a), Node::Repeat(m, b)) => {
                charge(2)?;
                // Zero repetitions retain the original child and dependency.
                n == m && a.same_descriptor_budgeted(b, charge)?
            }
            (Node::Requested(left, a), Node::Requested(right, b)) => {
                charge(2)?;
                left == right && a.same_descriptor_budgeted(b, charge)?
            }
            (Node::Then(a, b), Node::Then(c, d))
            | (Node::Tensor(a, b), Node::Tensor(c, d))
            | (Node::Conjugate(a, b), Node::Conjugate(c, d)) => {
                charge(2)?;
                a.same_descriptor_budgeted(c, charge)? && b.same_descriptor_budgeted(d, charge)?
            }
            _ => false,
        })
    }

    /// Cloning shares the description DAG/receipt, but copies its root matrix
    /// and exact type tree. Charge these before populating binding caches.
    pub(super) fn copy_size(&self) -> usize {
        port_nodes(&self.basis)
            + port_nodes(&self.codomain)
            + self.meaning.as_ref().map_or(0, |m| m.entries().len())
            + 3
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
        let bits = self.basis.basis_width().expect("closed basis") as usize
            + usize::from(access == Access::Controlled);
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
        let actual = if basis.basis_bits().is_none() {
            compiler.carrier_circuit_action(module, span, &basis, steps.clone())?
        } else {
            Circuit::new(contract_basis(&basis), steps.clone())
                .and_then(|c| c.matrix(&mut compiler.exact_work))
                .map_err(|e| compiler.op_error(module, span, e))?
        };
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
        let bits = self.basis.basis_width().expect("closed basis") as usize;
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
            Node::Requested(_, operation) => operation.materialize(access)?,
            Node::Pure(PureProvider { inverse: None, .. }) => {
                return Err(ContractError::Type(
                    "rectangular preparation requires its original Raw body",
                ));
            }
            Node::Carrier(None) => {
                return Err(ContractError::Type(
                    "typed preparation requires its original Raw body",
                ));
            }
            Node::Carrier(Some(steps)) => match access {
                Access::Apply => steps.clone(),
                Access::Adjoint => inverse(steps.clone()),
                Access::Controlled => controlled(steps.clone(), bits),
            },
            Node::Provider(e)
            | Node::Pure(PureProvider {
                inverse: Some(e), ..
            }) => {
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
                let abits = a.basis.basis_width().expect("closed basis") as usize;
                let bbits = b.basis.basis_width().expect("closed basis") as usize;
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

pub(super) fn same_port_budgeted<E>(
    left: &Ty,
    right: &Ty,
    charge: &mut impl FnMut(usize) -> Result<(), E>,
) -> Result<bool, E> {
    left.equivalent_by_budgeted(right, &mut |a, b| Ok(a == b), charge)
}

pub(super) fn same_meaning_budgeted<E>(
    left: Option<&Matrix>,
    right: Option<&Matrix>,
    charge: &mut impl FnMut(usize) -> Result<(), E>,
) -> Result<bool, E> {
    charge(1)?;
    match (left, right) {
        (None, None) => Ok(true),
        (Some(a), Some(b)) => {
            charge(1)?;
            if a.rows() != b.rows() || a.cols() != b.cols() {
                return Ok(false);
            }
            // Exact coefficients have fixed-size fields. Reserve the entire
            // borrowed cell comparison before comparing any matrix entry.
            charge(a.entries().len().saturating_add(b.entries().len()))?;
            Ok(a.entries() == b.entries())
        }
        _ => Ok(false),
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
