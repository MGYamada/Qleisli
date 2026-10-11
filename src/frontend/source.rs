//! Immutable original source and common syntax, outside semantic acceptance.
//!
//! Adapters retain their own loading, capacity and diagnostic order. Building
//! this collection does not type-check a body or confer a native accepted handle.

use std::collections::BTreeMap;
use std::path::PathBuf;

use super::ast::{Module, Span};
use super::parser::{ParseError, parse_bounded_module, parse_module};

/// Existing parser capacities, independently of downstream lowering eligibility.
#[derive(Clone, Copy)]
pub(super) enum ParsePolicy {
    Project,
    ExplicitModules,
}

pub(super) struct BundledSource {
    name: &'static str,
    path: &'static str,
    text: &'static str,
}

impl BundledSource {
    pub fn path(&self) -> &'static str {
        self.path
    }
    pub fn text(&self) -> &'static str {
        self.text
    }
}

/// The only construction source for bundled provenance. No external registry
/// or name-based semantic exception exists; these remain ordinary source bodies.
pub(super) struct BundledRegistry;
impl BundledRegistry {
    pub fn manifest() -> &'static str {
        include_str!("../../stdlib/Qargo.toml")
    }
    pub fn manifest_path() -> &'static str {
        "<bundled>/std/Qargo.toml"
    }
    pub fn sources() -> &'static [BundledSource] {
        static SOURCES: &[BundledSource] = &[
            BundledSource {
                name: "std::basis",
                path: "<bundled>/std/basis.qli",
                text: include_str!("../../stdlib/src/basis.qli"),
            },
            BundledSource {
                name: "std::gate",
                path: "<bundled>/std/gate.qli",
                text: include_str!("../../stdlib/src/gate.qli"),
            },
            BundledSource {
                name: "std::measurement",
                path: "<bundled>/std/measurement.qli",
                text: include_str!("../../stdlib/src/measurement.qli"),
            },
            BundledSource {
                name: "std::reflection",
                path: "<bundled>/std/reflection.qli",
                text: include_str!("../../stdlib/src/reflection.qli"),
            },
            BundledSource {
                name: "std::transform",
                path: "<bundled>/std/transform.qli",
                text: include_str!("../../stdlib/src/transform.qli"),
            },
        ];
        SOURCES
    }
}

#[derive(Clone, Debug)]
pub(super) struct Source {
    name: String,
    path: Option<PathBuf>,
    text: String,
    syntax: Module,
    bundled: bool,
}

pub(super) enum FailureKind {
    ReservedModule,
    Parse(ParseError),
}

pub(super) struct Failure {
    pub name: String,
    pub path: Option<PathBuf>,
    pub text: String,
    pub kind: FailureKind,
}

impl Failure {
    pub fn span(&self) -> Span {
        match &self.kind {
            FailureKind::ReservedModule => Span::default(),
            FailureKind::Parse(error) => error.span,
        }
    }
}

impl Source {
    pub fn local(
        name: String,
        path: Option<PathBuf>,
        text: String,
        policy: ParsePolicy,
    ) -> Result<Self, Failure> {
        if name == "std" || name.starts_with("std::") {
            return Err(Failure {
                name,
                path,
                text,
                kind: FailureKind::ReservedModule,
            });
        }
        Self::parse(name, path, text, false, policy)
    }

    pub fn bundled(source: &'static BundledSource, policy: ParsePolicy) -> Result<Self, Failure> {
        Self::parse(
            source.name.into(),
            Some(source.path.into()),
            source.text.into(),
            true,
            policy,
        )
    }

    fn parse(
        name: String,
        path: Option<PathBuf>,
        text: String,
        bundled: bool,
        policy: ParsePolicy,
    ) -> Result<Self, Failure> {
        let result = match policy {
            ParsePolicy::Project => parse_module(&text),
            ParsePolicy::ExplicitModules => parse_bounded_module(&text),
        };
        let syntax = match result {
            Ok(syntax) => syntax,
            Err(error) => {
                return Err(Failure {
                    name,
                    path,
                    text,
                    kind: FailureKind::Parse(error),
                });
            }
        };
        Ok(Self {
            name,
            path,
            text,
            syntax,
            bundled,
        })
    }

    pub fn text(&self) -> &str {
        &self.text
    }
    pub fn syntax(&self) -> &Module {
        &self.syntax
    }
    pub fn path(&self) -> Option<&std::path::Path> {
        self.path.as_deref()
    }
    /// Consumed only for the mutable public Project compatibility view. Do not
    /// retain this collection beside that view or recover provenance from it.
    pub fn into_parts(self) -> (String, Option<PathBuf>, String, Module, bool) {
        (self.name, self.path, self.text, self.syntax, self.bundled)
    }
}

#[derive(Default)]
pub(super) struct Builder {
    entries: BTreeMap<String, Source>,
}
impl Builder {
    /// Reject a collision without replacing the earlier original source.
    pub fn insert(&mut self, source: Source) -> Result<(), String> {
        use std::collections::btree_map::Entry;
        match self.entries.entry(source.name.clone()) {
            Entry::Occupied(entry) => Err(entry.key().clone()),
            Entry::Vacant(entry) => {
                entry.insert(source);
                Ok(())
            }
        }
    }
    pub fn finish(self) -> SourceCollection {
        SourceCollection {
            entries: self.entries,
        }
    }
}

/// Original text and the complete common AST share one immutable owner. Every
/// body remains present; profile checking takes place in downstream adapters.
#[derive(Clone, Debug)]
pub(super) struct SourceCollection {
    entries: BTreeMap<String, Source>,
}
impl SourceCollection {
    pub fn get(&self, name: &str) -> Option<&Source> {
        self.entries.get(name)
    }
    pub fn iter(&self) -> impl Iterator<Item = (&str, &Source)> {
        self.entries
            .iter()
            .map(|(name, source)| (name.as_str(), source))
    }
    pub fn into_entries(self) -> impl Iterator<Item = Source> {
        self.entries.into_values()
    }
}
