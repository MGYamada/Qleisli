# Recursive Fourier body: first attempts and validation

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

The [work packet](../fourier-recursion-packet.md) precedes implementation.
This is informed development, not a controlled authoring benchmark.

- [First base inspector](FourierBase-first.lean.txt) built successfully.
  [First base coefficient proof](HierarchicalFourierBase-first.lean.txt) and
  [actual diagnostics](base-first-check.log) retain a Boolean theorem-projection
  error and an unused simplifier. The repair extracts the conjunction by rewriting.
- [First H inspector](Hadamard-first.lean.txt) built successfully.
  [First H proof](HierarchicalHadamard-first.lean.txt) and
  [actual diagnostics](hadamard-first-check.log) retain two unavailable array/list
  lemma names. Definitional reduction suffices; the proof assumptions did not change.
- [First control inspector](FourierControl-first.lean.txt),
  [actual diagnostics](control-first-check.log), and
  [first complex bridge](HierarchicalFourierControl-first.lean.txt) retain the
  direct-child equality simplification repair.
- [First complete body inspector](FourierBody-first.lean.txt) and
  [first inductive physical-evaluation proof](HierarchicalFourierBody-first.lean.txt)
  both built successfully. Direct `Nat.rec` avoids partial generated helpers.
- [First base/H native source](BaseHadamard-first.lean.txt) failed on a missing
  `Inhabited QuantumPort` instance; the [actual build](../fourier-base-native-first.json)
  is retained. Optional port lookup replaced partial indexing in the fixture.
- [First integrated body native source](FourierBody-native-first.lean.txt) and
  [its passing first run](../fourier-body-native-first.json) retain the composed
  inspection and exported actual H requests.

[Final base/H checks](../fourier-base-native.json) pass 206 native outcomes,
32 complex vectors and 40 fresh exact finite reconstructions. The
[complete-body checks](../fourier-body-native.json) pass 172 native outcomes,
200 complex/reference vectors and 40 reconstructions, including global -H.
[Builds and audits](../fourier-recursion-registry.json) and
[runtime regressions](../fourier-recursion-runtime-validation.json) record the
executed checks. No external schema is enabled. The actual outer reversal,
independently requested Fourier root and full v0.2.1 source/corpus gates remain open.
