//! Syntax, module resolution, and checked lowering of a finite `.qli` subset.
//!
//! Parsing and import resolution alone do not establish type or ownership
//! validity. The `compile` API checks source and independently verifies its IR.

pub mod ast;
pub mod compile;
pub mod core;
pub mod diagnostic;
pub mod documentation;
pub mod lexer;
mod ordinary;
pub mod parser;
pub mod project;
mod resolve;
mod scanner;
pub mod sized;
mod types;

/// Language edition for the current grammar, in-memory source APIs and bundled
/// library. This is independent of the product version and Rust's Cargo edition.
pub const CURRENT_EDITION: &str = "2026";
