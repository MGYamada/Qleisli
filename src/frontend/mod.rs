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
pub mod parser;
pub mod project;
pub mod sized;
