//! Qleisli: an experimental quantum language with independently checked finite IR.
//!
//! The frontend checks a finite `.qli` subset and lowers it to IR. Every
//! generated function is passed through [`verify`], which checks the operation
//! subset in [`ir`]. Raw IR is untrusted regardless of its producer.
//! This Rust library and the `qleisli` CLI require neither Lean nor Python.
//! The separately built Lean kernel is an experimental, staged migration;
//! the production acceptance path still uses the Rust verifier.
//!
//! # Start with a verified circuit
//!
//! The package name is `qleisli`; Rust imports use `qleisli`.
//! Import the supported OpenQASM 3 terminal subset and inspect its numerical
//! reference distribution. Qubits must be explicitly initialized with `reset`.
//!
//! ```
//! use qleisli::{interop::import_openqasm3, sim};
//!
//! let program = import_openqasm3(r#"
//! OPENQASM 3.0;
//! include "stdgates.inc";
//! qubit q;
//! bit c;
//! reset q;
//! h q;
//! c = measure q;
//! "#)?;
//! let distribution = sim::run_closed(&program, sim::SimulationLimits::default())?;
//! assert_eq!(distribution.len(), 2);
//! for bits in [vec![false], vec![true]] {
//!     assert!((distribution[&bits] - 0.5).abs() < 1e-12);
//! }
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```
//!
//! # API guide
//!
//! - [`frontend::compile::compile_project`] compiles a directory with `main.qli`
//!   to a [`VerifiedProgram`]; its diagnostic/policy variants provide located
//!   errors and explicit source-loading limits.
//! - [`verify`] checks manually constructed [`ir::RawProgram`] values.
//! - [`interchange`] imports/exports QIRF artifacts and rechecks retained evidence.
//! - [`interop`] imports bounded OpenQASM 3 and exports OpenQASM 3 or QIR Base.
//!   QIR input is provided by the separate optional Python/PyQIR host layer.
//! - [`sim::run_closed`] enumerates a reference distribution;
//!   [`sim::sample_closed`] samples a freshly initialized trajectory.
//! - [`contract`] checks exact finite semantic evidence; floating-point
//!   simulation results cannot create a certificate.
//!
//! # Scope and compatibility
//!
//! Sized `Bits<n>` / `CBits<m>` source experiments are not production frontend
//! APIs. General Soundness, Physical Realizability and Resource Safety theorems
//! remain proof goals. Successful checking is not an algorithm or hardware proof.
//! Simulated probabilities are approximate and may contain tiny rounding residues.
//! The first-registry-release name migration replaces the earlier Git/path
//! `qleisli-core` package and `qleisli_core` import with `qleisli`. Existing
//! clients must migrate dependency/import names or use a Cargo dependency alias.
//! This explicit identity exception leaves other 0.2.x contracts compatible;
//! the planned 0.3.0 type-system work is a separate breaking-change boundary.
//! See the [language quick reference](https://github.com/MGYamada/Qleisli/blob/v0.2.1/docs/qli-quick-reference.md),
//! [trust boundary](https://github.com/MGYamada/Qleisli/blob/v0.2.1/TRUST_BOUNDARY.md)
//! and [versioning policy](https://github.com/MGYamada/Qleisli/blob/v0.2.1/docs/versioning.md).

pub mod contract;
pub mod frontend;
pub mod host;
pub mod interchange;
pub mod interop;
pub mod ir;
pub mod sim;
mod verify;

pub use verify::{ValidationError, VerifiedProgram, verify};
