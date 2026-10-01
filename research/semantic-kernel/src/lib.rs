//! Experimental symbolic semantics and independent contract checking.
//!
//! This non-published research package is not a new public Qleisli language,
//! compiler API, or replacement for the released finite checker. Its modules
//! distinguish mathematical operator evidence from ownership and runtime entry
//! guarantees. See the package README for the implemented profile and limits.

pub mod adapter;
pub mod kernel;

// CI latency probe: comment-only source edit; compilation and tests unchanged.
