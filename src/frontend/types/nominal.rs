//! Full source-bound ordinary finite declarations. No encoding or native authority.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;
use crate::frontend::ast::Span;
use std::sync::Arc;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::frontend) struct Origin {
    pub module: String,
    pub name: String,
    pub source: Arc<str>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub(in crate::frontend) struct Nominal<N> {
    pub origin: Arc<Origin>,
    pub body: Body<N>,
}

#[derive(Clone, Debug)]
pub(in crate::frontend) enum Body<N> {
    Enum(Vec<String>),
    Record(Vec<Field<N>>),
}

#[derive(Clone, Debug)]
pub(in crate::frontend) struct Field<N> {
    pub name: String,
    pub public: bool,
    pub ty: Type<N>,
}

impl<N> Nominal<N> {
    pub fn fields(&self) -> impl DoubleEndedIterator<Item = &Type<N>> + ExactSizeIterator {
        let fields = match &self.body {
            Body::Enum(_) => &[][..],
            Body::Record(fields) => fields.as_slice(),
        };
        fields.iter().map(|field| &field.ty)
    }

    /// Metadata visits/copies are charged independently of the field type walk.
    pub fn metadata_cells(&self) -> usize {
        self.origin.source.len()
            + self.origin.module.len()
            + self.origin.name.len()
            + 1
            + match &self.body {
                Body::Enum(variants) => variants.iter().map(|name| name.len() + 1).sum::<usize>(),
                Body::Record(fields) => fields
                    .iter()
                    .map(|field| field.name.len() + 2)
                    .sum::<usize>(),
            }
    }

    pub fn map_parts<M, E>(
        &self,
        sizes: &mut impl FnMut(&N) -> Result<M, E>,
        bases: &mut impl FnMut(&TypeParameter) -> Result<Type<M>, E>,
    ) -> Result<Nominal<M>, E> {
        Ok(Nominal {
            origin: Arc::clone(&self.origin),
            body: match &self.body {
                Body::Enum(variants) => Body::Enum(variants.clone()),
                Body::Record(fields) => Body::Record(
                    fields
                        .iter()
                        .map(|field| {
                            Ok(Field {
                                name: field.name.clone(),
                                public: field.public,
                                ty: field.ty.map_parts(sizes, bases)?,
                            })
                        })
                        .collect::<Result<_, E>>()?,
                ),
            },
        })
    }
}
