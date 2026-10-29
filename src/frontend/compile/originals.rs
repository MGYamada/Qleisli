//! Borrow actual source owners without constructing or reparsing a Project.
//! A view confers no source judgment or native acceptance.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;
use crate::frontend::source::SourceCollection;

#[derive(Clone, Copy)]
pub(super) enum Originals<'a> {
    Project(&'a Project),
    Selected(&'a SourceCollection),
}

pub(super) struct Module<'a> {
    pub ast: &'a super::super::ast::Module,
    pub source: &'a str,
    pub path: Option<&'a Path>,
}

impl<'a> Originals<'a> {
    pub fn len(self) -> usize {
        match self {
            Self::Project(project) => project.modules.len(),
            Self::Selected(sources) => sources.iter().count(),
        }
    }

    pub fn module(self, name: &str) -> Option<Module<'a>> {
        match self {
            Self::Project(project) => project.modules.get(name).map(|source| Module {
                ast: &source.ast,
                source: &source.source,
                path: Some(&source.path),
            }),
            Self::Selected(sources) => sources.get(name).map(|source| Module {
                ast: source.syntax(),
                source: source.text(),
                path: source.path(),
            }),
        }
    }

    pub fn modules(self) -> impl Iterator<Item = (&'a str, Module<'a>)> {
        let (project, selected) = match self {
            Self::Project(project) => (Some(project), None),
            Self::Selected(selected) => (None, Some(selected)),
        };
        project
            .into_iter()
            .flat_map(|project| &project.modules)
            .map(|(name, source)| {
                (
                    name.as_str(),
                    Module {
                        ast: &source.ast,
                        source: &source.source,
                        path: Some(source.path.as_path()),
                    },
                )
            })
            .chain(
                selected
                    .into_iter()
                    .flat_map(SourceCollection::iter)
                    .map(|(name, source)| {
                        (
                            name,
                            Module {
                                ast: source.syntax(),
                                source: source.text(),
                                path: source.path(),
                            },
                        )
                    }),
            )
    }

    pub fn root(self) -> &'a Path {
        match self {
            Self::Project(project) => &project.root,
            Self::Selected(_) => Path::new("<selected-source>"),
        }
    }

    pub fn error(self, error: SourceError) -> CompileError {
        source_error(self, self.root(), error)
    }
}

impl<'a> From<&'a Project> for Originals<'a> {
    fn from(project: &'a Project) -> Self {
        Self::Project(project)
    }
}
