# Authoring ergonomics source cases

Run `cargo test --test authoring_ergonomics --test qli_corpus`. The harness copies
one source into a temporary project; this directory intentionally includes
rejected programs and is not itself an executable project.

- `permutation`, `multi_parameter`, `tuple_evaluation` and `nary_lift` execute
  patterned basis functions and arity-preserving tuples. `nary_lift` uses explicit
  conversions at binary split/join boundaries. SWAP is bound to
  an independent mathematical permutation; the multi-parameter case retains
  Unit nodes and whole-subtree bindings.
- Duplicate/shape/arity/capture cases reject during ordinary source checking.
  `phase_mismatch` fails existing exact evidence checking. Ignoring a basis
  component does not authorize a noninjective quantum lift.
- `dropped_*` sources retain precise diagnostic cases for parameters, nested
  tuple binders, shadowing, zero-wire owners and computed auxiliaries. The test
  also checks UTF-8 byte offsets, CRLF coordinates and paths in another module.
- Rust-generated very long syntax exercises resource limits; ordinary quantum
  programs are kept here as `.qli` source. Existing binary examples stay in the
  other corpus as regressions.

The earlier [authoring corpus](../qli_authoring/README.md) now classifies
`accepted/nary_tuple.qli` and `accepted/basis_tuple_pattern.qli` as successful
programs; the two-argument `phase_by` mismatch remains a useful arity rejection.
