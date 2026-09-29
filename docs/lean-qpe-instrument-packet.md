# QPE controlled powers and residual instrument

Status: **internal checking, branch/reference equations and conditional completeness proved**,
2026-09-29. Continue the adopted
[QPE instrument specification](hierarchical-ir-spec.md#first-qpe-profile-and-exact-angles)
from the actual QFT circuit and typed graph theorems. No external schema is
enabled by an algebraic formula alone.

Keep the original desired shared source and add a finite off-grid phase client:
two-bit QPE of T on half of a Bell pair, followed by X measurements of the
reference and retained target. A type-correct variant measures and re-prepares
the target before those X measurements. This distinguishes residual coherence
from merely matching a distribution of phase labels. Preserve first sources,
real diagnostics and independent branch calculations.

The runtime component matches actual ordered controlled-repeat descriptors:
control k, positive polarity, the independently requested target definition and
count 2^k, for k=0..m-1. It checks m in 1..8 before generating the bounded
template. Prove its literal conditional repetition equals U raised to the
little-endian control value for every target action; retain phase by using the
actual U, not equality up to scalar. Verification visits m descriptors and
never iterates a power count. Operational execution still uses 2^m-1 possible
U applications. Provider typing, whole-space unitarity and available controlled
access must come from independently checked evidence in the external importer;
an artifact flag or the schedule theorem cannot supply them.

Prove preparation from the actual sequence of H gates on a fresh zero register.
Interpret inverse of an accepted positive QFT as its conjugate transpose, and
terminal Z measurement as the corresponding row projection, leaving the target
and arbitrary reference indices intact. Establish each branch amplitude and
then its target/reference density map as

```text
K_y = 2^(-m) Σ_j exp(-2πi j y / 2^m) U^j,
rho_y = (K_y ⊗ I_R) rho (K_y† ⊗ I_R).
```

The theorem must connect these sums to actual accepted component definitions,
not define QPE to be the desired K_y and prove reflexivity. A complete production
QPE schema additionally requires the full fresh-zero/H/powers/inverse-QFT/Z
hierarchical binding, target output ownership, encoding/premise registry and
unitary/completeness proofs. Record any remaining premise explicitly.

Check native schedule mutations, all widths, powers/counts and independent
literal actions. For small quantum cases compare full complex Kraus entries
and arbitrary joint-reference branches, including non-exact phases and the
coherence-destroying source fault. Large widths need symbolic generation and
checking, not full distribution simulation. Numerical checks issue no evidence.

The internal plan checker also fixes the complete boundary: one `Bits(n)` target
input and retained output; no classical input; one `CBits(m)` result; observe
effect; target/precision owners 0/1; disjoint target and precision axis maps;
fresh literal zero precision bits; the actual H word; inverse (not forward)
orientation of the checked QFT; and ascending precision measurement axes.
Require n,m in 1..8 and n+m≤16 before building those expectations. This is a
checked projection for the later external importer, not a new wire format or
an artifact-supplied assertion of provider unitarity. Its acceptance theorem
must expose each matched boundary and both component acceptance premises.

## Implemented definitions and exact proof scope

| Actual definition/theorem | Established obligation |
| --- | --- |
| [ControlledPowers.check_action](../lean-kernel/QleisliKernel/ControlledPowers.lean) | Every accepted actual schedule acts as the requested provider iterated by the little-endian control value, for any action/state; exact scalar phase is retained. |
| `maximumUses_template` | Expanded provider uses plus one equal 2^m. Checking visits the m descriptors; execution retains its real count. |
| [Uniform.run_word](../lean-kernel/QleisliKernel/Uniform.lean) | The literal H word on fresh zeros yields the chosen path bits with zero phase and exactly m H entries. |
| [Qpe.check_conditions](../lean-kernel/QleisliKernel/Qpe.lean) | Actual acceptance fixes every boundary/freshness/preparation field and yields the accepted powers and actual typed QFT graph. |
| [Qpe.bitEquiv_value](../lean/Qleisli/Qpe.lean) | The bit-index sum is bijectively reindexed to j in 0..2^m-1 with the specified little-endian value. |
| `uniform_coefficient`, `checked_powers`, `inverse_coefficient` | Primitive preparation paths, literal target matrix products and conjugate transpose of the actual checked QFT give their stated coefficients. |
| `checked_branch`, `checked_instrument`, `checked_plan` | Their actual composition equals K_y and the entire residual target/reference map. The plan theorem fixes target matrix dimension to 2^n. |

These are operator equations for arbitrary target matrices, not just eigenstate
probabilities. The subsequent [completeness proof](../lean/Qleisli/QpeComplete.lean)
proves `kraus_complete`, `checked_complete` and `checked_plan_complete` from the
explicit premise U†U=I. `accepted_plan` packages the branch equations,
completeness and joint trace result while deriving existence of the actual
graph denotation from acceptance, rather than assuming evaluation succeeds.
`complete_withReference` and `complete_trace` extend the
result to any finite reference and every joint input matrix. The proof uses
character orthogonality to sum all outcomes; it does not enumerate matrices in
the runtime or assume an eigenstate. The branch equations themselves require
no such premise: U=2I at precision one gives total Gram matrix 5I/2. The external
importer must independently establish its actual provider's whole-space
unitarity and controlled access before enabling `qpe-instrument/1` acceptance.
Inverse is the hierarchical mathematical
adjoint; correctness of an executor's reversed primitive-gate expansion is a
separate binding/execution obligation. Native compilation, transport and source
adequacy are not proved by this packet.

The [native experiment](../scripts/test_lean_qpe.py) checks all 64 width pairs
n,m=1..8 and 37 mutations. It compares 4,080 literal controlled paths and 4,080
preparation paths. Independent complex execution compares 1,080 Kraus entries,
180 arbitrary joint-density branches, completeness and reference-trace
preservation for 24 unitary cases, and three completeness counterexamples
(nonisometric provider, omitted outcome, incorrect normalization).
The oracle's largest vector has dimension 64; checker dense dimension is zero.
Both retained source programs match all 32 independently expected probabilities;
the dephasing fault changes some probabilities by 1/16. See the
[development record](../tests/fixtures/lean_qpe_instrument/README.md) for commands,
first attempts, source hashes and remaining gates.

## Closed component dispatch

[Schema.check](../lean-kernel/QleisliKernel/Schema.lean) now compares an
independent `Request` with a proposed fixed ID, template version, complete
parameter list and actual typed witness. It dispatches only these components:

| Fixed ID | Internal parameters and checked witness | Semantic theorem |
| --- | --- | --- |
| `qft-dyadic8/1` | m in 1..8; actual typed QFT graph and entry | `Qleisli.Schema.qft_sound`: actual denotation, both inverse laws and every phase-exact positive Fourier coefficient |
| `controlled-power/1` | exponent k in 0..12, provider reference; one literal positive controlled repeat of count 2^k with local control coordinate zero | `Qleisli.Schema.power_coherent_sound`: actual coherent amplitude action, phase-exact diag(I,U^(2^k)), both unitary laws and full joint reference maps; provider-isometry premise and external port binding remain explicit |
| `qpe-instrument/1` | n,m in 1..8 with n+m≤16, provider reference; actual complete internal QPE plan | `Qleisli.Schema.qpe_sound`: actual denotation, exact boundary/freshness, all residual branch maps, completeness and joint trace preservation; provider-isometry premise explicit |

Template version is one. Provider references must fit u32. Unknown IDs,
Lean declaration strings, changed versions/parameters and mismatched witness
constructors reject. `controlled-power/1` checks one power; the QPE schedule
composes m such powers for k=0..m−1. Its exponent limit follows the existing
repeat-count limit 4096, and does not increase the QPE precision profile.
The [proof bridge](../lean/Qleisli/Schema.lean) concerns this actual dispatcher,
not a second model of its control flow.

This is an internal dispatch component. Receipts are ordinary data, not a
production evidence seal. Full external IR extraction, logical provider requirements,
finite-leaf reconstruction, encodings and transport remain required. In particular,
matching a provider index alone does not establish its requested mathematical
meaning. No schema is enabled in the production CLI by this component.

## Shipped type and source manifest

The repository-owned [registry](../lean/schema-registry.json) now binds all
three component IDs to complete exported Lean theorem types, including universe
parameters, every binder and implicit argument. The structural expression tree
is authoritative for comparison; a fully qualified readable type accompanies it.
[SchemaExport.lean](../lean/SchemaExport.lean) reads the rebuilt declarations,
checks theorem/definition kinds and exports the actual `Schema.check` signature.
This is a build-time audit tool outside the executable acceptance library.

The manifest includes parameter domains, template versions, modules/declarations
and a source revision: SHA-256 of the sorted path/content-hash map of the project
runtime/proof sources, package locks, toolchains and audit tools. This content
revision works before a release commit exists; it is not a claim of tagging or
publication. No producer-supplied theorem name or digest replaces this manifest.

`python3 scripts/check_schema_registry.py` rebuilds both packages, runs both
compiled audits and fresh runtime kernel replay, exports current types and
compares the full manifest. CI runs this gate. `--write` explicitly refreshes
the manifest only after those checks; source changes during checking reject.
`--source-only` is the weaker source-archive/packaging identity check and cannot
refresh theorem types. Its success is not proof validation. The mutation suite
rejects changed theorem types under the same name, checker declarations, IDs,
domains, versions, enablement, source hashes and unknown/duplicate fields.

Every entry still records `external_enabled: false`. The manifest binds the
proved internal components; external typed IR projection, provider evidence and
complete schema importer tests must establish the remaining premises before
production enablement. The controlled-power component now has the
[coherent operator/reference bridge](../lean/Qleisli/ControlledPowers.lean).
The original `power_sound` iteration theorem remains available; the registry
binds the stronger `power_coherent_sound` statement. This changes no enabled
external profile: the provider's mathematical evidence and actual hierarchical
control/count/port binding must still be reconstructed independently.


## Coherent controlled-power bridge

The actual executable `coherentStage` lifts `applyStage` across all control
sectors without measuring them; `coherentRun` composes those lifted stages.
`coherentRun_apply` relates this actual composition to the existing literal
execution. The separate complex bridge proves that this amplitude action is
multiplication by the full block operator, not a family of observed branches.
For one accepted stage this is diag(I,U^(2^k)); for the accepted schedule the
blocks are U^j in the declared little-endian order. The provider phase is kept.

The single-stage theorem includes both unitary laws under the explicit
whole-space provider-isometry premise. Its reference equation covers arbitrary
joint matrices, including off-diagonal control/reference coherences. The
schedule also has actual native-amplitude and conditional-isometry theorems.
No native matrix is constructed by the checker; Mathlib is confined to the
separate interpretation proof package.

The [native exact suite](../scripts/test_lean_controlled_power.py) checks
188 decisions (180 accepted, 8 rejected), 9,352 Gaussian-integer coefficients,
17,280 joint-density entries and 295,026 counted literal oracle uses. Its
independent matrix-power oracle has maximum dimension four. X^2 and (iX)^2
have equal basis probabilities but different controlled coherences. Two
retained ordinary `.qli` programs similarly distinguish X from −X after a
control/reference Bell preparation and interference. Both type-check; the
negative source is a semantic counterexample to the positive expectation.
The [packet](../tests/fixtures/lean_qpe_instrument/coherent-power-packet.md)
and fixture preserve first implementations, real diagnostics and source hashes.

This closes the internal coherent operator bridge, not external provider
verification, complete hierarchy proof derivation, source translation or the
full v0.2.0 gates. No source-author burden reduction is claimed by this step.

The subsequent [direct artifact binding](hierarchical-ir-spec.md#direct-controlled-power-artifact-binding)
now projects the actual control/repeat and logical control/power bodies, with
an exact provider-premise reference and independent static request. Its
[operator/reference bridge](../lean/Qleisli/HierarchicalPower.lean) proves these
actual projections agree when that provider equation is discharged. The native
182-case suite includes type-correct binding mutations and independent table
permutations. This is still a pending obligation interface: generic derivation,
finite reconstruction and external schema enablement remain separate gates.
