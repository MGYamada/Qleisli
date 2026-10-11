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
    if requests.is_empty() {
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
        bytes: 0,
    };
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
    bytes: usize,
}
impl Collector<'_> {
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
                    .finite(span)?,
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
        let specification = if target.is_none() {
            Some(self.provider(self.definition(specification_id, span)?, span)?)
        } else {
            None
        };
        let implementation = self.provider(id, span)?;
        let checked = &self.source.instantiation().program.checked;
        let identity = RetainedIdentity::shared(
            checked.resolution.path(implementation_id),
            checked.resolution.path(specification_id),
            self.sources.clone(),
        );
        let receipt = if let Some(target) = target {
            MeaningEvidence::check_retained_with_kernel(
                self.kernel,
                implementation,
                target,
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::compile::ParsedProgram;

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
