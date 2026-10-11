//! Qleisli: an experimental quantum language with independently checked finite IR.
//!
//! The frontend checks a finite `.qli` subset and lowers it to IR. Every
//! generated function is submitted to [`interchange::native::Kernel`]. Raw IR
//! is untrusted regardless of its producer. Lean is the only acceptance authority.
//! Cargo builds and documents this library without Lean; checking requires a
//! separately built, compatible native checker. Set `QLEISLI_KERNEL` to its
//! executable or use the explicit `*_with_kernel` APIs. Missing, incompatible
//! or failing checkers reject; no runtime download or Rust fallback exists.
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
//!   to an [`AcceptedProgram`]; its diagnostic/policy variants provide located
//!   errors and explicit source-loading limits.
//! - [`interchange::native::Kernel::accept_raw`] checks manually constructed [`ir::RawProgram`] values.
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
//! Sized `Q<Bits<n>>` / ordinary `Bits<m>` source experiments retain bounded
//! execution profiles. General Soundness, Physical Realizability and Resource Safety theorems
//! remain proof goals. Successful checking is not an algorithm or hardware proof.
//! Simulated probabilities are approximate and may contain tiny rounding residues.
//! The first-registry-release name migration replaces the earlier Git/path
//! `qleisli-core` package and `qleisli_core` import with `qleisli`. Existing
//! clients must migrate dependency/import names or use a Cargo dependency alias.
//! Version 0.2.9 is an explicitly approved breaking verifier migration: use
//! `AcceptedProgram` and `Kernel::accept_raw` in place of the removed Rust
//! verifier and its handles. Version 0.3.0 uses ordinary `Unit`, `Bit`, `Bits<n>`
//! and `0`/`1`; their retired classical spellings reject. General basis
//! polymorphism and common-checker convergence remain unfinished.
//! See the [language quick reference](https://github.com/MGYamada/Qleisli/blob/v0.3.0-alpha/tests/fixtures/quick_reference/README.md),
//! [trust boundary](https://github.com/MGYamada/Qleisli/blob/v0.3.0-alpha/TRUSTBOUNDARY.md)
//! and versioning policy.

pub mod contract;
pub mod frontend;
pub mod host;
pub mod interchange;
pub mod interop;
pub mod ir;
pub mod sim;

pub use interchange::native::AcceptedProgram;
