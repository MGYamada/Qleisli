//! Provisional Qleisli frontend and independently checked finite IR.
//!
//! The frontend checks a finite `.qli` subset and lowers it to IR. Every
//! generated function is passed through [`verify`], which checks the operation
//! subset in [`ir`]. Raw IR is untrusted regardless of its producer.

pub mod contract;
pub mod frontend;
pub mod host;
pub mod interchange;
pub mod interop;
pub mod ir;
pub mod sim;
mod verify;

pub use verify::{ValidationError, VerifiedProgram, verify};
