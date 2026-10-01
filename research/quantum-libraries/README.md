# Lean quantum-library investigation

Status: **independent, preliminary interoperability investigation**, 2026-09-27.
This is not a dependency-adoption decision, a production API, a new release
condition, or a resumption of the deferred symbolic-kernel implementation.
The production Lean/Mathlib versions and imports are unchanged.

**Subsequent environment decisions:** Physlib was added at compatible `v4.30.0`
after this survey, then removed from required dependencies/CI in the v0.1.5
maintenance candidate until a concrete instrument bridge needs it. The
[current dependency gate](../../lean/README.md#future-physlib-bridge) states
the reintroduction conditions; earlier decisions are available in Git history. [PhyslibAudit.lean](PhyslibAudit.lean) preserves
the optional eight-declaration integration probe from 4.30.0; it is not runnable
in the current default environment. The survey below retains its separate
4.34.1 experiment and original validation scope.

Qleisli's [license](../../LICENSE) and [attribution](../../NOTICE) apply to the
original probes and this report: Apache-2.0, Copyright 2026 Masahiko G. Yamada.
No upstream implementation has been copied into this directory. Both surveyed
repositories separately use Apache-2.0 and retain their own authorship.

## Question and provisional recommendation

Can an existing Lean library supply the mathematical models needed to connect
Qleisli's phase-sensitive encoded operators, reference-aware partial traces,
and measurement instruments? **Yes, substantial foundations already exist.**
These are ordinary Lean libraries, not changes to Lean's trusted kernel.

Such a library is not logically necessary: Qleisli already proves local Kraus
completeness and encoded-composition lemmas using Mathlib in
[Kraus.lean](../../lean/Qleisli/Kraus.lean) and
[SemanticContract.lean](../../lean/Qleisli/SemanticContract.lean). The proposed
benefit is reusing positivity, density-state, channel and partial-trace theory
instead of rebuilding that mathematical infrastructure inside Qleisli.

Physlib's `QuantumInfo` is the closer first candidate for a finite matrix/state/
measurement adapter. `lean-quantum` is a credible alternative for a more abstract
finite-dimensional operator foundation; its two central modules also passed a
compatibility experiment using Qleisli's current toolchain. Neither library
supplies Qleisli's source-to-IR correspondence, ownership rules, evidence binding,
or a production symbolic checker. There is no reason to import both into the
production proof environment at this stage.

## Exact sources and environments

| Source | Inspected commit | Upstream environment | Environment actually tested |
| --- | --- | --- | --- |
| [Physlib / QuantumInfo](https://github.com/leanprover-community/physlib/tree/44c66d54be78db4693be9f8f92bd3b5ad124ed6f/QuantumInfo) | `44c66d54be78db4693be9f8f92bd3b5ad124ed6f` | Lean 4.34.1; Mathlib 4.34.1, `d13f23b723b8a846827a245b89c10fc7d3f11612` | Matching upstream environment; selected modules only |
| [lean-quantum](https://github.com/Hayata-Yamasaki-Group/lean-quantum/tree/bf1c4f6aaec84948f1a1c76c0728432813404a0f) | `bf1c4f6aaec84948f1a1c76c0728432813404a0f` | Lean 4.29.0-rc6; manifest Mathlib `f156f7abd91ac67adb22bf999e5a71ba22e22e41` | Original `QuantumState` and `QuantumChannel` sources compiled with Lean 4.30.0 and Qleisli's Mathlib 4.30.0 |

Qleisli's Mathlib commit in the compatibility experiment was
`c5ea00351c28e24afc9f0f84379aa41082b1188f`. The upstream sources were not edited.
The experiment did not run `lean-quantum`'s full build or its original 4.29.0-rc6
environment, and did not try downgrading Physlib to Lean 4.30.0.

The source checkouts and build outputs were isolated under a temporary directory.
Installed Lean toolchains were reused; external dependencies and matching Mathlib
caches were downloaded there or into the ordinary external cache. No upstream
repository was added as a Qleisli production dependency.

## Interfaces inspected

| Requirement | Physlib / QuantumInfo | lean-quantum |
| --- | --- | --- |
| Pure, phase-sensitive operation | Finite matrices with typed indices; straightforward match to the existing matrix denotation | `Qudit` finite-dimensional complex inner-product spaces and `LinearMap` operators |
| Mixed states | `MState`, bundling positivity and unit trace | `IsDensity` predicate on operators |
| Channels and composition | Bundled `CPTPMap`, composition, tensor product, unitary channels and partial traces | `CPTP` over Mathlib's `CompletelyPositiveMap`; additional unbundled CP, Kraus, Choi and Stinespring theory |
| Discard with a reference | `traceLeft`, `traceRight`, state-product and relabeling lemmas | `Tr₂`, `TrRight` and tensor-operator lemmas |
| Measurement and residual state | `POVM.measurementMap` retains quantum output and a classical outcome register | The inspected two modules provide Kraus branch machinery; a comparable high-level POVM/instrument interface was not found there |
| Integration cost observed | Newer toolchain; the selected import closure includes helpers importing all of Mathlib | The two selected modules compiled on 4.30.0 without source edits, with one deprecated-import warning |

Physlib's README distinguishes the `QuantumInfo` codebase and its review process
from Physlib's core; membership in the same repository is not a uniform review
guarantee. In either library, audit the specific declarations imported and used.

## Probe obligations and limits

The probes intentionally establish interface compatibility, not novel upstream
theorems. They reuse existing library results and inspect their transitive axiom
dependencies. In both representations, composition uses associativity and the
two given encoded equations:

```text
U E0 = E1 u,  V E1 = E2 v  =>  (V U) E0 = E2 (v u).
```

No whole composite matrix is evaluated by these proofs. A matrix in a denotation
does not by itself require an executable checker to enumerate its entries.
Conversely, proving this algebraic lemma does not make the current Rust checker
symbolic or prove that its implementation follows the lemma. The algebraic
composition lemmas do not need isometry hypotheses; physical admissibility and
encoding isometry must be established separately before admitting a contract.

The partial-trace probes discard an independent normalized auxiliary while
retaining an arbitrary joint target/reference state. They do **not** assume that
the target and reference are separable. An independent mixed auxiliary can be
discarded by a channel, but Qleisli's **pure** release still requires the stronger
zero-return contract. The theorem is not a new release authorization.

The local Kraus probes extend `K` by the identity on a reference. Complete
positivity holds for arbitrary `K`; a physically admissible instrument needs
additional normalization, such as `sum K†K = I` across all outcomes. An individual
trace-nonincreasing branch requires `K†K <= I`. Neither follows from CP alone.
The lean-quantum poststate lemma treats arbitrary, possibly entangled, pure joint
inputs and keeps the unnormalized branch, including probability-zero outputs.
It does not prove a general mixed-state instrument interface.

Physlib's `POVM.measurementMap` implements the **square-root/Lüders instrument**:
`rho -> sum_x sqrt(E_x) rho sqrt(E_x) tensor |x><x|`. It is not a unique instrument
determined by the POVM probabilities. Qleisli must retain a more general
outcome-indexed CP-map or Kraus contract when an algorithm specifies another
post-measurement operation. The Physlib probe also applies the bundled channel
tensored with identity to an arbitrary joint mixed input; no product-input
premise is imposed.

The probes keep tensor factors typed. They do not prove Qleisli's low-left bit
flattening, physical wire permutation, or final-IR correspondence. A concrete
pitfall is that lean-quantum's `Tr₂` **traces the left factor**, as its defining
theorem confirms: `Tr₂(X tensor Y) = Tr(X) * Y`. Names alone are insufficient to
choose a layout adapter.

## Results

- [LeanQuantumProbe.lean](LeanQuantumProbe.lean): four local lemmas compiled with
  `-DwarningAsError=true`. All four depend only on `propext`, `Classical.choice`
  and `Quot.sound`; no `sorryAx` or additional axiom appears in their audits.
  [Axiom output](results/lean-quantum-axioms.txt),
  [state-module output](results/lean-quantum-state-build.txt),
  [channel-module output](results/lean-quantum-channel-build.txt).
- [PhyslibProbe.lean](PhyslibProbe.lean): `QuantumInfo.Channels.CPTP` and
  `QuantumInfo.Measurements.POVM` built successfully on their pinned 4.34.1
  environment. Four local lemmas and the reference-framed measurement definition
  compiled with `-DwarningAsError=true`; all five audited declarations depend only
  on `propext`, `Classical.choice` and `Quot.sound`, with no `sorryAx` or additional
  axiom. [Build output](results/physlib-build.txt),
  [axiom output](results/physlib-axioms.txt).

Both upstream checkouts remained clean after the experiments. The saved probes
are identical to the successfully checked files. Qleisli's documentation-link
checker was run for this report and its roadmap/index links. Production Rust
tests and the production Lean build were not rerun for this investigation:
neither their source nor dependency selection was changed by this work.

The lean-quantum source scan covered its two local modules, 2,605 lines. The
Physlib local import-closure scan for `POVM` covered 53 `QuantumInfo` modules,
27,501 lines; this count excludes Mathlib. Text occurrences of `sorry` in that
closure were comments. Elsewhere in Physlib, `QuantumInfo/States/Mixed/Fidelity.lean`
contains an explicitly marked unfinished theorem. None of this is a blanket
verification claim: the declaration-level axiom output is the relevant evidence
for the selected proofs, and unrelated modules were not audited as a whole.

## Consequences for Qleisli

Keep two connected semantic layers:

1. Phase-sensitive linear/isometric/unitary operators and encodings for coherent
   composition and control. Passing to `rho -> U rho U†` loses global phase:
   `U` and `-U` induce the same channel but different coherently controlled gates.
2. Unnormalized CP branches, complete instruments and CPTP composition for
   measurement, discard, probability and residual ownership. Reference framing
   must apply to arbitrary joint inputs, not only independently prepared states.

Above either library, Qleisli still needs its own typed semantic terms, layout
maps, encoding contracts, instrument outcomes, and denotation of actual IR.
Proof rules connect these terms to library mathematics; they do not authorize
runtime execution merely because a theorem with a similar name exists.

If the deferred semantics work is resumed, first build a small Physlib adapter
in a separate proof package, checking a known-zero auxiliary, a local measurement
on an entangled input, and phase-sensitive controlled composition. Keep the
lean-quantum operator route available if its abstraction reduces the adapter
burden. Before choosing a production dependency, verify the complete selected
import set on a deliberately chosen toolchain, audit the actual bridge theorems,
and record layout and source/IR correspondence obligations. This investigation
does not itself adopt that future work or raise Qleisli's required toolchain.

## Reproduction

Check out the exact commits above in separate directories; preserve their
licenses. Build outputs must stay outside production source directories.

For lean-quantum, use Qleisli's Lean 4.30.0 executable, save the value of
`lake env printenv LEAN_PATH` from Qleisli's `lean` directory, and prepend an
empty experimental output directory to that path. In order, invoke Lean on
`Quantum/QuantumMechanics/QuantumState.lean` and `QuantumChannel.lean`, passing
`-R` with the upstream checkout and `-o` with the corresponding module-relative
`.olean` destination under the experimental output directory. Then invoke the
same executable on `LeanQuantumProbe.lean` with `-DwarningAsError=true` and the
same `LEAN_PATH`. This tests those original sources against 4.30.0, independently
of upstream's default Lake targets. Inspect all emitted axiom lists, not just the
process exit status.

For Physlib, use its pinned toolchain and manifest, then run:

```sh
lake exe cache get Mathlib
lake build QuantumInfo.Channels.CPTP QuantumInfo.Measurements.POVM
lake env lean -DwarningAsError=true /absolute/path/to/PhyslibProbe.lean
```

The full Mathlib cache is relevant because two modules in the selected
QuantumInfo closure import the umbrella `Mathlib` module. Merely asking the
Mathlib cache tool for the two `QuantumInfo` module names did not fetch their
dependencies in this experiment. Interrupted initial builds while preparing
caches are not counted as either library failures or successful validations.
