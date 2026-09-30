# Ordinary measured QPE wrappers

These Qleisli-authored Apache-2.0 helpers wrap the unchanged
[shared coherent QPE source](../qualtran_qpe/estimation.qli). They add no external
corpus source, bundled stdlib API or finite-manifest case. Their
[first sources and diagnostics](../../../tests/fixtures/authoring_sessions/measured-qpe-v021/checkpoint.md)
remain separate from executable translations and subsequent results.

`init_zero[n]` constructs a fresh `Q<Bits<n>>` in the exact zero state using
ordinary recursion and explicit empty-register/put-bit operations. It has Iso
effect, accepts 0–8 bits within the aggregate profile, and preserves all caller
owners and reference correlations. `measure_bits[n]` consumes that register,
measures its axes in increasing logical bit order, explicitly consumes the empty
owner, and returns `CBits<n>` with the first outcome at the low bit. It retains
the complete outcome/residual-state instrument; it does not return only a
probability. The empty result is explicit.

`qpe[n,m,U]` initializes the phase register, calls the existing `estimate`, and
returns `(CBits<m>, Q<Bits<n>>)`. It requires positive n/m and actual controlled
access to the phase-fixed transparent provider. It retains the target for every
outcome and arbitrary reference. No algorithm name grants evidence.

The experimental source producer emits an initialization proposal, shared pure
graph and readout/packing proposal. Independent component checks and small
complex/reference tests are required. The separate Rust sized API/CLI and named instrument checker now compose
these helpers; current small-system evidence and explicit theorem premises are
recorded in the checkpoint above. General source/runtime preservation remains
open. The main manifest registers these as original local compositions, with
hashes and dependencies, separately from its three upstream sources.
