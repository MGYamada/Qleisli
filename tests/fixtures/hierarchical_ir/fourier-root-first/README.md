# Outer Fourier first attempts

The bounded contract is recorded in [the packet](../fourier-root-packet.md).
First versions were saved before compilation or native execution:

- [Pure inspector](FourierRoot.lean.txt) and [compiler output](compile.txt):
  `prefix` is a Lean syntax keyword. The implementation uses `enter`; the
  actual-body equality direction and explicit Option-bind projection were
  also corrected without weakening the acceptance predicate.
- [Complex interpretation](HierarchicalFourierRoot.lean.txt) and
  [compiler output](math-compile.txt): use explicit list arguments for coefficient
  rewriting, prove the equivalent reverse-index arithmetic, and expose the
  physical-evaluation form before rewriting the aligned-fuel child evaluations.
- [Native generator](test_hierarchical_fourier_root.py.txt),
  [generated first program](native.lean.txt) and [execution diagnostics](native-diagnostics.txt):
  the fixture's optional root lookup replaces `getElem!`, which required an
  unavailable `Inhabited Definition` instance. Production acceptance is unchanged
  by this fixture repair. The [first report](../fourier-root-native-first.json)
  preserves the failed native build; the [current report](../fourier-root-native.json)
  records all comparison results and fresh exact reconstruction.

No failed compilation or test was counted as validation. The final actual-entry
theorem retains full-byte H obligations and makes no production-seal claim.

Copyright 2026 Masahiko G. Yamada. Apache-2.0.
