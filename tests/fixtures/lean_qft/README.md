# QFT symbolic paths and Fourier proof record

This informed development packet continues the adopted shared-QPE goal on
2026-09-29. It is not a controlled model benchmark or a completed 0.2.0 release.
The [selected contract](../../../lean/Qleisli/Qft.lean) preceded changes
to acceptance-related definitions. The earlier desired sized QPE source remains
unimplemented; no external corpus source or new wire protocol was added.

## First sources and semantic fault

[first_source](first_source/main.qli) uses the existing ordinary qft3 and its
adjoint on |001> in integer notation (returned low bit first: `100`). Its
[actual baseline](baseline.json) is deterministic. It required no repairs.
This finite round trip does not prove shared source or Fourier phases.

[wrong_reversal](wrong_reversal/main.qli) explicitly reverses qft3's output
again, erasing the required final reversal. Its [first run](wrong-reversal-baseline.json)
passes finite typing and gives a different distribution. The test computes
F† R F |1> independently, comparing all eight probabilities including zeros.
The correct outcome's probability is only about 0.02145. Both sources retain
their first hashes and are CI checked.

## Proof development evidence

- [PathSum-first.lean.txt](PathSum-first.lean.txt) and
  [first-path-diagnostics.txt](first-path-diagnostics.txt) retain a reserved-word
  identifier error, unresolved lookup/branch reductions and a namespace ambiguity.
  Repairs use explicit names, index inequalities and ordinary fold induction.
- [Qft-first.lean.txt](Qft-first.lean.txt), [first-qft-diagnostics.txt](first-qft-diagnostics.txt)
  and [first-qft-proof-diagnostics.txt.gz](first-qft-proof-diagnostics.txt.gz)
  retain the missing prerequisite build, initial equality proof and reduction
  failures. The large unabridged diagnostics are gzip-compressed. Additional
  [reduction output](qft-second-proof-diagnostics.txt.gz) is retained.
  Direct `decide`/`rfl` could not reduce the standard sort implementation across
  this module boundary; `cbv` produced kernel-checkable equality proofs. Its
  default step limit was insufficient, so only this fixed eight-case proof's
  elaboration budget was raised. No native proof oracle was substituted.
- [Fourier-first.lean.txt](Fourier-first.lean.txt) and
  [first-fourier-diagnostics.txt](first-fourier-diagnostics.txt) retain the first
  modular-algebra proof attempt. Repairs make list/finite sums and natural casts
  explicit, prove vanishing high powers in ZMod 256, and factor the two bit sums.

The final complex theorem concerns the actual literal circuit matcher and a
direct sum of primitive-entry products. It is not equality between two aliases
of a named QFT. Output reversal, exact phase and H count are part of the proof.

## Executed checks and remaining integration

[native.json](native.json) records 109 C-compiled cases, 3,180 path comparisons,
1,600 modular Fourier comparisons, all 84 small matrix entries and nine joint
reference cases. [source-after.json](source-after.json) and
[msrv-source-after.json](msrv-source-after.json) record both finite source cases
on the existing primary/MSRV binaries. [proof-checks.json](proof-checks.json)
records both Lean builds, runtime reductions and compiled/axiom audits.
[fresh-replay.json](fresh-replay.json) records fresh kernel replay;
[regressions.json](regressions.json) records prior component and helper checks.

```sh
python3 scripts/test_lean_qft.py
python3 scripts/test_lean_qft.py --source-only target/debug/qleisli
```

Native normalization/compilation constructs no dense matrix. The small external
numerical oracle uses vectors of dimension at most eight, with numerical
comparisons distinct from exact proof evidence. Large widths use symbolic
phases and no full simulation requirement.

Source repair count, body duplication and manual wiring remain unchanged.
This packet removes the need to re-prove the literal QFT gate pattern at each
supported width. Typed hierarchy, ports, encoding/theorem-manifest binding,
QPE instruments, a `.qli` producer and release validation remain required.
The internal matcher is not an enabled `qft-dyadic8/1` external registry entry.
