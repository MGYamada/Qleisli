//! Exact source-bound function pairs. Native receipts remain the sole authority.
// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::contract::{FunctionEvidence, function::RetainedIdentity, meaning::MeaningEvidence};
use crate::frontend::{ast::FnKind, check::ObligationKind, resolve::DefId};
use crate::ir::{CircuitAction, CircuitStep, RawOp, TokenId, WireId};

type Key = (DefId, DefId);

#[derive(Debug)]
pub(in crate::frontend::specialize) struct CheckedContract {
    pub receipt: Arc<FunctionEvidence>,
    pub leaf: CheckedUnitaryLeaf,
}

#[derive(Debug)]
pub(in crate::frontend::specialize) struct CheckedTarget {
    pub raw: RawProgram,
    pub sources: Arc<Vec<(String, String)>>,
}

pub(in crate::frontend::specialize) fn check(
    source: &ElaboratedProgram,
    kernel: &native::Kernel,
    budget: &mut Budget,
) -> Result<ElaboratedProgram> {
    if budget.remaining() > DEFAULT_EXACT_WORK {
        return Err(Error::new(
            "limit",
            Span::default(),
            "function contract budget exceeds the shared exact-work ceiling",
        ));
    }
    let mut source = source.clone();
    // Each public check is fresh, including its dependency receipts.
    source.contracts.clear();
    source.meaning_artifacts.clear();
    let requests = source
        .instantiation()
        .program
        .checked
        .obligations
        .iter()
        .filter_map(|obligation| {
            if let ObligationKind::FunctionEquality {
                implementation,
                specification,
            } = obligation.kind
            {
                let module = source
                    .instantiation()
                    .program
                    .checked
                    .resolution
                    .declaration(obligation.definition)
                    .name
                    .0
                    .clone();
                Some(((implementation, specification), obligation.span, module))
            } else {
                None
            }
        })
        .collect::<Vec<_>>();
    if requests.len() > MAX_CALLS {
        return Err(Error::new(
            "limit",
            Span::default(),
            "function contracts exceed 1024 original obligations",
        ));
    }
    let targets = source
        .instantiation()
        .program
        .meaning_targets
        .iter()
        .filter_map(|(id, target)| (!target.references().is_empty()).then_some(*id))
        .collect::<Vec<_>>();
    if requests.is_empty() && targets.is_empty() {
        return Ok(source);
    }
    let original = &source.instantiation().program.sources;
    let size = original.iter().try_fold(0usize, |size, (name, module)| {
        if name.len() > crate::contract::function::MAX_IDENTITY_NAME_BYTES {
            return Err(Error::new(
                "limit",
                Span::default(),
                "function source name exceeds its metadata profile",
            ));
        }
        size.checked_add(name.len())
            .and_then(|n| n.checked_add(module.text().len()))
            .ok_or_else(|| {
                Error::new(
                    "limit",
                    Span::default(),
                    "function source byte accounting overflow",
                )
            })
    })?;
    if original.iter().count() > crate::contract::function::MAX_FUNCTION_SOURCES
        || size > crate::contract::function::MAX_FUNCTION_SOURCE_BYTES
    {
        return Err(Error::new(
            "limit",
            Span::default(),
            "function source snapshot exceeds its metadata profile",
        ));
    }
    budget
        .charge(size)
        .map_err(|e| Error::new("limit", Span::default(), e.to_string()))?;
    let sources = Arc::new(
        original
            .iter()
            .map(|(name, module)| (name.to_owned(), module.text().to_owned()))
            .collect(),
    );
    let mut collector = Collector {
        source: &mut source,
        kernel,
        budget,
        sources,
        active: BTreeSet::new(),
        active_targets: BTreeSet::new(),
        bytes: 0,
    };
    for id in targets {
        collector.target(id, Span::default())?;
    }
    for (key, span, module) in requests {
        collector
            .pair(key, span)
            .map_err(|e| e.in_module(&module))?;
    }
    source.require_function_contracts()?;
    Ok(source)
}

struct Collector<'a> {
    source: &'a mut ElaboratedProgram,
    kernel: &'a native::Kernel,
    budget: &'a mut Budget,
    sources: Arc<Vec<(String, String)>>,
    active: BTreeSet<Key>,
    active_targets: BTreeSet<DefId>,
    bytes: usize,
}
impl Collector<'_> {
    fn target(&mut self, id: DefId, span: Span) -> Result<()> {
        if self.source.meaning_artifacts.contains_key(&id) {
            return Ok(());
        }
        let target = self.source.instantiation().program.meaning_targets[&id].expression(span)?;
        if target.references().is_empty() {
            return Ok(());
        }
        self.charge(target.cells(), span)?;
        if self.active_targets.len() >= MAX_DEPTH || !self.active_targets.insert(id) {
            return Err(Error::new(
                "limit",
                span,
                "reference Meaning dependency depth/cycle exceeds its profile",
            ));
        }
        let mut references = BTreeMap::new();
        for original in target.references() {
            let provider = self.definition(original, span)?;
            references.insert(original, self.provider(provider, span)?);
        }
        let path = self
            .source
            .instantiation()
            .program
            .checked
            .resolution
            .path(id);
        let sources = self.sources.clone();
        let identity = || RetainedIdentity::shared(path.clone(), path.clone(), sources.clone());
        let raw = target
            .materialize(self.kernel, &references, &identity, self.budget)
            .map_err(|e| {
                Error::new(
                    if e.is_capacity() { "limit" } else { "meaning" },
                    span,
                    e.to_string(),
                )
            })?;
        // Validate even an unused reference target. This fresh decision checks
        // its exact original artifact/dependencies; no matrix assertion is cached.
        let receipt = FunctionEvidence::check_retained_with_kernel(
            self.kernel,
            target.signature().clone(),
            raw.clone(),
            raw.clone(),
            identity(),
            self.budget,
        )
        .map_err(|e| {
            Error::new(
                if e.error.is_capacity() {
                    "limit"
                } else {
                    "meaning"
                },
                span,
                e.to_string(),
            )
        })?;
        let proposal = native::Proposal::from_raw(&raw, None, Version::V2, None)
            .map_err(|e| invalid(span, &e.to_string()))?;
        self.account(proposal.artifact().len(), span)?;
        debug_assert_eq!(receipt.signature(), target.signature());
        self.source.meaning_artifacts.insert(
            id,
            Arc::new(CheckedTarget {
                raw,
                sources: self.sources.clone(),
            }),
        );
        self.active_targets.remove(&id);
        Ok(())
    }
    fn charge(&mut self, amount: usize, span: Span) -> Result<()> {
        self.budget
            .charge(amount)
            .map_err(|e| Error::new("limit", span, e.to_string()))
    }
    fn definition(&self, original: DefId, span: Span) -> Result<usize> {
        self.source
            .definitions()
            .iter()
            .position(|d| d.original == original)
            .ok_or_else(|| invalid(span, "original closed contract function is absent"))
    }
    fn pair(&mut self, key: Key, span: Span) -> Result<()> {
        self.charge(1, span)?;
        if self.source.contracts.contains_key(&key) {
            return Ok(());
        }
        if self.active.len() >= MAX_DEPTH || !self.active.insert(key) {
            return Err(Error::new(
                "limit",
                span,
                "function contract dependency depth/cycle exceeds its profile",
            ));
        }
        let (implementation_id, specification_id) = key;
        let id = self.definition(implementation_id, span)?;
        let definition = &self.source.definitions()[id];
        if definition.effect() == "observe" {
            return Err(Error::new(
                "unsupported",
                span,
                "observing contract obligations are not supported in this specialization profile",
            ));
        }
        let [input] = definition.inputs() else {
            return Err(invalid(span, "contract function is not unary"));
        };
        if definition.effect() != "unitary" || input.ty() != definition.output().ty() {
            return Err(invalid(
                span,
                "contract function changes its exact principal-Unitary interface",
            ));
        }
        let signature = input
            .ty()
            .quantum_basis()
            .and_then(finite_basis)
            .ok_or_else(|| invalid(span, "contract requires a finite exact quantum basis"))?;
        signature
            .bits()
            .map_err(|e| Error::new("limit", span, e.to_string()))?;
        // Resolve the independent request before materializing the candidate.
        let target = if self
            .source
            .instantiation()
            .program
            .checked
            .interface(specification_id)
            .kind
            == FnKind::Meaning
        {
            Some(
                self.source.instantiation().program.meaning_targets[&specification_id]
                    .expression(span)?,
            )
        } else {
            None
        };
        if target
            .as_ref()
            .is_some_and(|target| target.signature() != &signature)
        {
            return Err(invalid(
                span,
                "contract Meaning changes the exact basis tree",
            ));
        }
        let specification = match &target {
            None => Some(self.provider(self.definition(specification_id, span)?, span)?),
            Some(target) if !target.references().is_empty() => {
                self.target(specification_id, span)?;
                Some(self.source.meaning_artifacts[&specification_id].raw.clone())
            }
            Some(_) => None,
        };
        let implementation = self.provider(id, span)?;
        let checked = &self.source.instantiation().program.checked;
        let identity = RetainedIdentity::shared(
            checked.resolution.path(implementation_id),
            checked.resolution.path(specification_id),
            self.sources.clone(),
        );
        let receipt = if let Some(target) = target
            .as_ref()
            .filter(|target| target.references().is_empty())
        {
            MeaningEvidence::check_retained_with_kernel(
                self.kernel,
                implementation,
                target
                    .finite()
                    .map_err(|e| invalid(span, &e.to_string()))?
                    .clone(),
                identity,
                self.budget,
            )
            .map(|e| e.receipt())
            .map_err(|e| {
                Error::new(
                    if e.is_capacity() { "limit" } else { "contract" },
                    span,
                    e.to_string(),
                )
            })?
        } else {
            Arc::new(
                FunctionEvidence::check_retained_with_kernel(
                    self.kernel,
                    signature.clone(),
                    implementation,
                    specification.expect("ordinary original specification"),
                    identity,
                    self.budget,
                )
                .map_err(|e| {
                    Error::new(
                        if e.error.is_capacity() {
                            "limit"
                        } else {
                            "contract"
                        },
                        span,
                        e.to_string(),
                    )
                })?,
            )
        };
        // Preserve the complete pair/dependency evidence inside the actual leaf bytes.
        let bits = signature
            .bits()
            .map_err(|e| invalid(span, &e.to_string()))?;
        let input = QuantumPort {
            token: TokenId(0),
            wires: (0..bits).map(|n| WireId(n as u32)).collect(),
            shape: BasisShape { bits: bits as u8 },
        };
        let output = QuantumPort {
            token: TokenId(1),
            ..input.clone()
        };
        let wrapper = RawProgram {
            quantum_inputs: vec![input.clone()],
            classical_inputs: vec![],
            operations: vec![RawOp::ApplyUnitary {
                input: input.token,
                output: output.token,
                steps: vec![CircuitStep {
                    controls: vec![],
                    action: CircuitAction::Contract {
                        indices: (0..bits).collect(),
                        evidence: receipt.clone(),
                        adjoint: false,
                    },
                }],
            }],
            quantum_outputs: vec![output.token],
            classical_outputs: vec![],
            declared_effect: Effect::Unitary,
        };
        let interface = RootInterface {
            input: signature.clone(),
            output: signature.clone(),
        };
        let proposal = native::Proposal::from_raw(&wrapper, Some(&interface), Version::V2, None)
            .map_err(|e| invalid(span, &e.to_string()))?;
        self.account(proposal.artifact().len(), span)?;
        let boundary = UnitaryBoundary::new(signature, input, output)
            .map_err(|e| invalid(span, &e.to_string()))?;
        let leaf = finite_leaf::check_with_kernel(
            self.kernel,
            proposal.artifact(),
            &boundary,
            receipt.meaning(),
            self.budget,
        )
        .map_err(|e| Error::new(e.code, span, e.to_string()))?;
        self.source
            .contracts
            .insert(key, Arc::new(CheckedContract { receipt, leaf }));
        self.active.remove(&key);
        Ok(())
    }
    fn account(&mut self, bytes: usize, span: Span) -> Result<()> {
        self.bytes = self
            .bytes
            .checked_add(bytes)
            .ok_or_else(|| invalid(span, "contract byte accounting overflow"))?;
        if self.bytes > MAX_CELLS {
            return Err(Error::new(
                "limit",
                span,
                "function contracts exceed 100000 aggregate artifact bytes",
            ));
        }
        self.charge(bytes, span)
    }
    fn provider(&mut self, subject: usize, span: Span) -> Result<RawProgram> {
        let selected = dependencies(self.source, subject, span)?;
        self.charge(selected.len(), span)?;
        let mut targets = BTreeSet::new();
        for id in &selected {
            let definition = &self.source.definitions()[*id];
            for formal in &self
                .source
                .instantiation()
                .program
                .checked
                .interface(definition.original)
                .statics
            {
                if let crate::frontend::check::StaticKind::Operation {
                    meaning: Some(id), ..
                } = formal.kind
                {
                    targets.insert(id);
                }
            }
            let mut pending = definition
                .operations()
                .values()
                .chain(
                    definition
                        .steps()
                        .iter()
                        .filter_map(|step| step.operation()),
                )
                .collect::<Vec<_>>();
            let mut visited = 0;
            while let Some(operation) = pending.pop() {
                visited += 1;
                if visited > MAX_CELLS {
                    return Err(Error::new(
                        "limit",
                        span,
                        "reference Meaning operation dependencies exceed cell bounds",
                    ));
                }
                targets.extend(operation.meanings.iter().map(|request| request.id));
                pending.extend(operation.children());
            }
        }
        for target in targets {
            self.target(target, span)?;
        }
        let requests = selected
            .iter()
            .flat_map(|id| self.source.definitions()[*id].steps())
            .filter_map(|step| step.contract().map(|key| (key, step.span())))
            .collect::<Vec<_>>();
        for (key, at) in requests {
            self.pair(key, at)?;
        }
        let meanings = check_operation_meanings_selected(
            self.source,
            self.kernel,
            self.budget,
            Some(&selected),
        )?;
        let proposal = lower_inner(
            self.source,
            subject,
            Some(&selected),
            None,
            Some((self.kernel, self.budget, &meanings.leaves)),
        )?;
        self.account(proposal.payload().len(), span)?;
        // Fresh acceptance binds the exact bytes, then source replay binds both
        // candidates to their independent original definition graphs.
        let accepted = self
            .kernel
            .accept(proposal.proposal())
            .map_err(|e| Error::new(e.code, span, e.to_string()))?;
        self.charge(accepted.native_exact_work(), span)?;
        Ok(accepted.raw().clone())
    }
}

fn dependencies(source: &ElaboratedProgram, subject: usize, span: Span) -> Result<BTreeSet<usize>> {
    let mut selected = BTreeSet::new();
    let mut pending = vec![subject];
    let mut cells = 0usize;
    while let Some(id) = pending.pop() {
        if !selected.insert(id) {
            continue;
        }
        let definition = &source.definitions()[id];
        let mut operations = definition.operations().values().collect::<Vec<_>>();
        for step in definition.steps() {
            cells += 1;
            if let Some(child) = step.called_definition() {
                pending.push(child);
            }
            operations.extend(step.operation());
            operations.extend(
                step.operation_bindings()
                    .into_iter()
                    .flat_map(|map| map.values()),
            );
        }
        while let Some(operation) = operations.pop() {
            cells += 1;
            if cells > MAX_CELLS {
                return Err(Error::new(
                    "limit",
                    span,
                    "contract source dependencies exceed existing cell bounds",
                ));
            }
            if let Some(id) = operation.definition() {
                pending.push(id);
            }
            operations.extend(operation.children());
        }
    }
    Ok(selected)
}

/// Embed the complete independently checked pair, including original request
/// dependencies, rather than replacing it with its host-side matrix.
pub(super) fn leaf(
    kernel: &native::Kernel,
    receipt: &Arc<FunctionEvidence>,
    budget: &mut Budget,
    span: Span,
) -> Result<CheckedUnitaryLeaf> {
    let signature = receipt.signature().clone();
    let bits = signature
        .bits()
        .map_err(|e| invalid(span, &e.to_string()))?;
    let input = QuantumPort {
        token: TokenId(0),
        wires: (0..bits).map(|n| WireId(n as u32)).collect(),
        shape: BasisShape { bits: bits as u8 },
    };
    let output = QuantumPort {
        token: TokenId(1),
        ..input.clone()
    };
    let wrapper = RawProgram {
        quantum_inputs: vec![input.clone()],
        classical_inputs: vec![],
        operations: vec![RawOp::ApplyUnitary {
            input: input.token,
            output: output.token,
            steps: vec![CircuitStep {
                controls: vec![],
                action: CircuitAction::Contract {
                    indices: (0..bits).collect(),
                    evidence: receipt.clone(),
                    adjoint: false,
                },
            }],
        }],
        quantum_outputs: vec![output.token],
        classical_outputs: vec![],
        declared_effect: Effect::Unitary,
    };
    let interface = RootInterface {
        input: signature.clone(),
        output: signature.clone(),
    };
    let proposal = native::Proposal::from_raw(&wrapper, Some(&interface), Version::V2, None)
        .map_err(|e| invalid(span, &e.to_string()))?;
    if proposal.artifact().len() > MAX_CELLS {
        return Err(Error::new(
            "limit",
            span,
            "Meaning contract exceeds 100000 artifact bytes",
        ));
    }
    budget
        .charge(proposal.artifact().len())
        .map_err(|e| Error::new("limit", span, e.to_string()))?;
    let boundary = UnitaryBoundary::new(signature, input, output)
        .map_err(|e| invalid(span, &e.to_string()))?;
    finite_leaf::check_with_kernel(
        kernel,
        proposal.artifact(),
        &boundary,
        receipt.meaning(),
        budget,
    )
    .map_err(|e| Error::new(e.code, span, e.to_string()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::compile::ParsedProgram;

    #[test]
    fn reference_operation_replay_rejects_equal_matrix_receipt_substitution() {
        let prefix = "use std::quantum::{h,init0}; use std::observe::measure_z;
            fn reference_h(q:Q<Bit>)->Q<Bit>{h(q)}
            meaning H:Bit=reference(reference_h);
            fn implementation(q:Q<Bit>)->Q<Bit>{h(h(h(q)))}";
        let kernel = native::Kernel::new(std::env::var_os("QLEISLI_KERNEL").unwrap());
        for body in [
            "fn client[const U:Op<Bit,H>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}
             pub observe fn main()->Bit{measure_z(client[implementation](init0()))}",
            "pub observe fn main()->Bit{measure_z(adjoint(checked_op(implementation,H))(init0()))}",
            "pub observe fn main()->(Bit,Bit){let(c,q)=controlled(checked_op(implementation,H))(init0(),init0());(measure_z(c),measure_z(q))}",
        ] {
            let text = format!("{prefix}{body}");
            let source = ParsedProgram::parse(BTreeMap::from([("main".into(), text)]))
                .unwrap()
                .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
                .unwrap()
                .elaborate()
                .unwrap()
                .check_function_contracts(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK))
                .unwrap();
            let checked = source
                .check_operation_meanings(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK))
                .unwrap();
            let raw = checked
                .lower_raw(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK))
                .unwrap();
            let accepted = kernel.accept(raw.proposal()).unwrap();
            let original = checked
                .leaves
                .iter()
                .find_map(|(_, _, receipt)| receipt.clone())
                .unwrap();
            let replacement = Arc::new(
                FunctionEvidence::check_retained_with_kernel(
                    &kernel,
                    original.signature().clone(),
                    original.specification().clone(),
                    original.specification().clone(),
                    RetainedIdentity::shared(
                        original.identity().implementation.clone(),
                        original.identity().specification.clone(),
                        Arc::new(original.identity().sources.clone()),
                    ),
                    &mut Budget::new(DEFAULT_EXACT_WORK),
                )
                .unwrap(),
            );
            assert_eq!(original.meaning(), replacement.meaning());
            let mut changed = accepted.raw().clone();
            let mut count = 0;
            for op in &mut changed.operations {
                if let RawOp::ApplyUnitary { steps, .. } = op {
                    for step in steps {
                        if let CircuitAction::Contract { evidence, .. } = &mut step.action {
                            *evidence = replacement.clone();
                            count += 1;
                        }
                    }
                }
            }
            assert_eq!(count, 1);
            let accepted = kernel.accept_raw(changed).unwrap();
            // Bypass the public immutable-byte preflight deliberately to test
            // the deeper independent source attachment check itself.
            let error = preservation::validate_subject_with_meanings(
                &source,
                source.root(),
                None,
                accepted.raw(),
                Some(&kernel),
                &mut Budget::new(DEFAULT_EXACT_WORK),
                &checked.leaves,
            )
            .unwrap_err();
            assert_eq!(error.code(), "preservation", "{error}");
        }
    }

    #[test]
    fn source_contract_replay_rejects_same_matrix_different_native_pair() {
        let text = "use std::quantum::h; use std::quantum::init0; use std::observe::measure_z;
            fn implementation(q:Q<Bit>)->Q<Bit>{h(h(h(q)))}
            fn specified(q:Q<Bit>)->Q<Bit>{h(q)}
            pub observe fn main()->Bit{measure_z(apply_contract(implementation,specified,init0()))}";
        let kernel = native::Kernel::new(std::env::var_os("QLEISLI_KERNEL").unwrap());
        let source = ParsedProgram::parse(BTreeMap::from([("main".into(), text.into())]))
            .unwrap()
            .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap()
            .check_function_contracts(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK))
            .unwrap();
        let proposal = source.lower_raw().unwrap();
        let accepted = kernel.accept(proposal.proposal()).unwrap();
        let mut changed = accepted.raw().clone();
        let receipt = source.contracts.values().next().unwrap().receipt.clone();
        let replacement = FunctionEvidence::check(
            receipt.signature().clone(),
            receipt.specification().clone(),
            receipt.specification().clone(),
            receipt.identity().clone(),
            &mut Budget::new(DEFAULT_EXACT_WORK),
        )
        .unwrap();
        assert_eq!(receipt.meaning(), replacement.meaning());
        for op in &mut changed.operations {
            if let RawOp::ApplyUnitary { steps, .. } = op {
                for step in steps {
                    if let CircuitAction::Contract { evidence, .. } = &mut step.action {
                        *evidence = Arc::new(replacement.clone());
                    }
                }
            }
        }
        let changed = native::Proposal::from_raw(&changed, None, Version::V2, None).unwrap();
        let changed = kernel.accept(&changed).unwrap();
        let error = preservation::validate_subject_with_kernel(
            &source,
            source.root(),
            None,
            changed.raw(),
            Some(&kernel),
        )
        .unwrap_err();
        assert_eq!(error.code(), "preservation");
        assert!(
            error
                .message()
                .contains("original implementation, independent request or dependencies"),
            "{error}"
        );
    }
}
