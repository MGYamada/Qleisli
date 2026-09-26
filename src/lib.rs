//! Provisional Qleisli frontend and independently checked finite IR.
//!
//! The frontend parses `.qli` and resolves modules, but does not yet type-check
//! source or lower it to IR. [`verify`] checks the finite operation subset in
//! [`ir`]. Raw IR is untrusted regardless of who or what generated it.

pub mod frontend;
pub mod ir;
pub mod sim;
mod verify;

pub use verify::{ValidationError, VerifiedProgram, verify};
