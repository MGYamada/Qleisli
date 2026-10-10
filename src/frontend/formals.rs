//! Shared untrusted declaration facts; never kernel acceptance or provider evidence.
use super::ast::{Access, StaticParam, StaticParamKind};
use super::resolve::locals::BinderKey;
use super::types::Type;
use std::collections::{BTreeMap, BTreeSet};

pub(super) fn access_index(access: Access) -> usize {
    match access {
        Access::Apply => 0,
        Access::Adjoint => 1,
        Access::Controlled => 2,
    }
}

pub(super) fn access_name(access: Access) -> &'static str {
    match access {
        Access::Apply => "Applicable",
        Access::Adjoint => "Adjointable",
        Access::Controlled => "Controllable",
    }
}

#[derive(Clone, Copy)]
pub(super) struct Prefix<'a> {
    pub naturals: &'a BTreeSet<BinderKey>,
    pub bases: &'a BTreeSet<BinderKey>,
}

pub(super) struct Operation<N, M> {
    pub basis: Type<N>,
    pub codomain: Option<Type<N>>,
    pub meaning: Option<M>,
    pub access: [bool; 3],
}

pub(super) enum AccessError {
    UnknownOperation,
    Duplicate,
}

pub(super) struct Formals<N, M> {
    next: usize,
    naturals: BTreeSet<BinderKey>,
    bases: BTreeSet<BinderKey>,
    operations: BTreeMap<BinderKey, Operation<N, M>>,
}

impl<N, M> Formals<N, M> {
    pub fn new() -> Self {
        Self {
            next: 0,
            naturals: BTreeSet::new(),
            bases: BTreeSet::new(),
            operations: BTreeMap::new(),
        }
    }

    /// The adapter checks the original kind and lexical table association.
    /// Only an Op invokes the profile's staged basis/Meaning checks.
    pub fn advance<E>(
        &mut self,
        ordinal: usize,
        source: &StaticParam,
        key: BinderKey,
        check: impl FnOnce(Prefix<'_>) -> Result<(Type<N>, Option<Type<N>>, Option<M>), E>,
    ) -> Result<(), E> {
        assert_eq!(ordinal, self.next, "complete ordered static formals");
        assert_eq!(key.name, source.name.text, "paired static spelling");
        match &source.kind {
            StaticParamKind::Natural => {
                assert!(self.naturals.insert(key), "unique Natural formal key");
            }
            StaticParamKind::Basis => {
                assert!(self.bases.insert(key), "unique Basis formal key");
            }
            StaticParamKind::Operation { .. } => {
                let (basis, codomain, meaning) = check(Prefix {
                    naturals: &self.naturals,
                    bases: &self.bases,
                })?;
                assert!(
                    self.operations
                        .insert(
                            key,
                            Operation {
                                basis,
                                codomain,
                                meaning,
                                access: [false; 3],
                            },
                        )
                        .is_none(),
                    "unique operation formal key"
                );
            }
        }
        self.next += 1;
        Ok(())
    }

    pub fn grant(&mut self, key: Option<&BinderKey>, access: Access) -> Result<(), AccessError> {
        let operation = key
            .and_then(|key| self.operations.get_mut(key))
            .ok_or(AccessError::UnknownOperation)?;
        let slot = &mut operation.access[access_index(access)];
        if *slot {
            return Err(AccessError::Duplicate);
        }
        *slot = true;
        Ok(())
    }

    pub fn into_operations(self, count: usize) -> BTreeMap<BinderKey, Operation<N, M>> {
        assert_eq!(self.next, count, "complete static formals consumed");
        self.operations
    }
}
