# Ordinary primitive test regression continuation

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.

This curated, informed continuation was assembled after reading the actual hosted
PR #419 failures at bd07cee947f10801375e5e0ef741834ed4904533. It is not a pre-run
archive, blind authoring task, model benchmark or source repair. The sources were
already committed before execution; immutable commit/path/hash references in
session.json retain the original test drivers, selected fixtures and std bodies.
The historical predecessor QLI files and their existing source-map chains remain
untouched. The checked PR merge checkout is recorded separately from its head.

The three attempt-01 files are separate Rust-source inputs, not a claim that a
single filesystem project was tested. Their enclosing Qargo declares edition
2026 for storage only; the hosted tests used their existing SourceRoot or
ParsedProgram helpers. The NOT input is reconstructed byte-for-byte from the
committed Rust literal and its decoded imports; the two other files are exact
copies of client-336 and client-341. No string/body/import repair occurred.

The focused observations preserve complete relevant panic blocks and command/test
result context from actual provider logs. They retain log line ranges and full
provider/log hashes. They do not pretend to be full workflow stdout/stderr, and
retrieval time is not a fabricated execution timestamp. In the native comparison
observation, exit 1 belongs to the containing comparison command; the unprinted
numeric Cargo child exit is explicitly unavailable. The runner also failed other
unrelated groups; these two assertions are not claimed to be its sole cause.

The independent intended contracts are unchanged:

- init0 prepares |0> with the singleton [0] injection. The user's NOT is the
  separate [1,0] injection. Mutating only that NOT to identity leaves a natively
  valid program with the independently wrong false rather than true outcome.
- The exact source-bearing X contract is H Z H. Its mathematical output has one
  true outcome of mass one. Numerical simulator rounding is checked with the
  existing engineering 1e-12 bound, not normalization or an acceptance tolerance.
- consume_empty explicitly converts Bits<0> to a fresh Unit owner, then finish
  consumes Unit. Both source events are pure; unpack_unit is the nested native
  structural operation tag. The live Bit owner/axis and complete complex
  reference-branch oracle remain checked through both transitions.

All test/native acceptance/source checks, physical/reference sizes and execution
limits remain. The repair changes only test assertions. The broader QS, PR, RS
and EXACT obligations remain pending; no protected guarantee is newly admitted
or weakened. The separate after observations retain the completed root commands:
20 normal tests (14 ordinary types plus all six source-correspondence tests),
14 MSRV ordinary-type tests and only the changed NOT regression on MSRV. The
latter explicitly filters the other five source-correspondence tests. Every
command passes its native skip gate and records a stable whole-working input,
compiler and kernel binding. The dirty working-input digest, not Git HEAD alone,
identifies the tested source. CLI after-hashes are observations, not standalone
build attestations. Full current all-target CI remains a separate gate.

Each after observation retains complete stdout/stderr and the original driver's
metadata except the repeated full input maps. It records their canonical hash,
count and the two repaired test hashes; the complete original external driver
record is separately bound by byte length and SHA-256. This projection is not
claimed to be a full driver copy. Initial hosted observations and all source
bytes remain unchanged. V1 first-failure-only material remains external history.
Recorded commands are evidence and must never be executed from this session.
