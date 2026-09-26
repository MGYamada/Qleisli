//! Source syntax and module resolution for the provisional `.qli` frontend.
//!
//! Parsing and name resolution do not establish type, effect, ownership, or
//! quantum validity. A future lowering pass must verify its generated IR.

pub mod ast;
pub mod lexer;
pub mod parser;
pub mod project;
