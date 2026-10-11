//! Syntax, module resolution, and checked lowering of a finite `.qli` subset.
//!
//! Parsing and import resolution alone do not establish type or ownership
//! validity. The `compile` API checks source and independently verifies its IR.

pub mod ast;
mod check;
pub mod compile;
pub mod core;
pub mod diagnostic;
pub mod documentation;
pub mod effects;
mod error;
mod formals;
mod instrument;
pub mod lexer;
mod linear;
mod meaning;
mod ordinary;
pub mod parser;
mod pattern;
pub mod project;
mod raw_state;
mod resolve;
mod scanner;
mod source;
mod specialize;
mod types;

/// Constitutional edition selected by in-memory source APIs and the bundled
/// library, independently of grammar, product version and Rust's Cargo edition.
pub const CURRENT_EDITION: &str = "2026";
