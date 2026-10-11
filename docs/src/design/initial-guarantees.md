# Initial scoped QS guarantees

**Status: admitted by the human Guardian on 2026-10-04 (Asia/Tokyo).**
Masahiko G. Yamada affirmed the adequacy of both formalizations and approved
their registration as proved scoped guarantees. The separate event is
`governance/guarantees/initial-2026-admission.json`; its SHA-256 is
`9f20661fd98ec56c58286b70f4e9d9f49c76570313b5ddc90ae4685d4e251dd2`.
The [QS interpretation](initial-interpretations.md), that human judgment and
the checked proofs have separate roles. A checked helper lemma does not
promote itself.

The exact reviewed proposal is preserved at repository file
`governance/proposals/initial-guarantees.json`. It contains the exact two
guarantee definitions, declarations, source identity, proof-evidence references,
assumptions and requested decision, with SHA-256
`bf9eb89d9ebadd41f16f40c5896b824b0e04fe1655264e102fb179948fa06c02`.
Its historical candidate status remains unchanged. This chapter explains that
record and the subsequent admission; it is not a second normative definition.
The included JSON at the end is rendered directly from the frozen record.

## The two admitted components

| Scoped guarantee | Actual theorem | Independent property |
| --- | --- | --- |
| `QS-QLV1-OWNERSHIP-2026-01` | `QleisliKernel.Protocol.Validity.check_ownershipSafe` | `QleisliKernel.Semantics.Ownership.OwnershipSafe` |
| `QS-QLV1-SCOPE-2026-01` | `Qleisli.NativeValidity.check_scopeSafe` | `QleisliKernel.Semantics.ClassicalScope.ScopeSafe` |

Both start from success of the actual
`QleisliKernel.Protocol.Validity.check bytes` definition. They quantify every
packet, request-presence result and initial/remaining natural-number work
budget satisfying that premise. Each produces an `Acceptance` witness that
retains the packet split, original body/request bytes, actual decoded artifact
and order, decoded optional request, intermediate work values and successful
inspection. The guaranteed program is the root selected from that artifact.
Neither theorem needs an optional finite request to be present.

The ordinary native wrapper currently invokes that definition through
`QleisliKernel.Cli.runValidity` with `contract = false` and work budget
10,000,000. This identifies the production connection; the mathematical premise
is Lean execution success. The contract-mode branch and hierarchy modes have
different entry points and are outside these two admitted scopes.

Ownership safety accounts for the actual root's quantum ports and output
owners, including zero-width owners, exclusive live wires, complete live
frames, fresh identities, both branch arms and complete quantum phis. It uses
independent `Inputs`, `Run` and `Returned` judgments over the original operation
lists. This is a structural ownership property. It does not derive source
tuple or basis equality from matching bit widths.

Classical scope safety accounts for the root's classical inputs, fresh
definitions, visible uses, both lexical branch arms, simultaneous phi operands
and returned identities. Its independent `Inserts`, `Run` and `Visible`
judgments resolve phi inputs before introducing destinations. They do not
assert computed values or probabilities.

The terminology change to `OwnershipSafe` under
[Issue #287](https://github.com/MGYamada/Qleisli/issues/287) preserved the
predicate and proof content. It created no new acceptance rule, assumption or
guarantee. [Exact clean-workspace discharge](https://github.com/MGYamada/Qleisli/issues/157)
remains a distinct QS duty; [quantitative Resource Safety](https://github.com/MGYamada/Qleisli/issues/280)
remains an RS duty.

## What the evidence establishes

`tests/fixtures/constitution_v030/initial-guarantees/Review.lean` exposes the
actual elaborated theorem types, the declarative predicates and their axiom
information. The proposal binds its captured output and the validation record,
including the reviewed source identity and recorded build/audit/replay checks.
The standard axiom basis is `propext`, `Classical.choice` and `Quot.sound`;
no project axiom was added.

The source hash identifies the reviewed implementation and proof definitions.
It does not determine whether those predicates adequately express the intended
two QS components. The separate human admission records that judgment. A locally observed
native binary identity also does not prove native compiler or runtime
correspondence and is not a portable release attestation.

The theorems include the actual Lean decoder computations in their acceptance
witnesses. Correspondence with an independently specified external wire
format, native IO/runtime, selected executable provenance, Rust decoding and
re-materialization remain separate. The statements concern the Lean-decoded
root; they do not by themselves establish source preservation or the meaning of
an execution result or exported artifact.

These two components also do not establish ordinary-root quantum CPTP/effect
soundness, clean/dirty workspace semantics, full source type or tuple-shape
preservation, a requested algorithm's meaning, hierarchy coverage, PR or
quantitative RS. Those exclusions bound the admission; they do not
waive the broader duties in the adopted interpretations.

## Human decision and later continuity

The Guardian reviewed whether each independent property and its exact
actual-checker formalization adequately expresses its stated narrow QS
component and supports its admission with the checked proof evidence. The
affirmative reply was: “2件とも提示された範囲・前提で妥当と認め、保証登録を承認する”.
The original proposal retains `proposed` and `human_adoption: null` as the exact
historical text submitted for review. The later event and live ledger record
the affirmative decision through the [authority process](../reference/authority.md).

Admission of both components leaves **QS-2026-01, PR-2026-01 and
RS-2026-01 pending** as broader obligations. It does not certify every
production path or authorize a release. Later releases must connect each
admitted component to their current actual acceptance and artifacts, preserving
its meaning and premises with justified semantic transport when necessary.
Retaining today's old theorem or source hash is insufficient. The historical
reviewed source and registry are retained beside the first validation record;
`governance/guarantees/current-evidence.json` separately binds current proof
evidence and acceptance sources. An unrelated source change can update that
binding after checking without rewriting the protected meaning or human act.

The current checker protects the elaborated independent semantic dependency
closure and every field of the actual `Acceptance` witness. Its fixed extractor
compares exact definition bodies, types, constructors and recursor rules with a
baseline rebuilt from the approved historical source archive. The proof lane
also retains the original theorem and `Acceptance`/`Artifact` reviews. This
matters because an unchanged theorem's outer type can hide a weakened witness
field. The retained enforcement counterexample
at `tests/fixtures/constitution_v030/witness-weakening/` compiled after replacing
the original-packet binding with `True`; the live Lean comparison rejects that
change even when mutable source identities are refreshed. It is a regression
in evidence enforcement, not a counterexample to the admitted theorems.

This first identity transport permits formatting and theorem proof-body changes
that preserve the exact elaborated closure. The actual current checker's body
may change within the protected dependency closure; its type and successful
input-byte/original-root theorem types remain fixed and checked. Binder and
universe names, module origins, definition proof subterms and semantic
representations remain conservatively protected. Representation-changing
transport is still unimplemented. The historical/current extraction and compiled
weakening, decoder and proof-refactor examples are preserved in
`tests/fixtures/constitution_v030/initial-guarantees-continuity/`.

Default checks validate recorded identities only. `--verify-lean` executes the
fixed extractor in the built/audited current environment and fixes the current
evidence record for the whole run, rejecting concurrent source/evidence
replacement. A recorded hash or implication about an obsolete checker cannot
substitute for that check. The original admission, two scoped guarantees and
three broader pending duties are unchanged.

The live ledger uses schema v5, retaining the schema-v4 separation of admitted
identities from current evidence. Each admitted entry has a canonical identity
that binds its constitutional edition, interpreted obligation, human admission
and exact reviewed proposal entry. That identity excludes mutable current
source/proof evidence. Separate bindings must cover every registered guarantee
exactly once through fixed verifier profiles; one QLV1 profile currently covers
both admitted entries. Neither a new JSON approval nor a successful unregistered
helper proof creates an admission. Historical v3 bytes are archived, and
trusted-base checks reject removal or substitution of any earlier identity.
The complete ledger and selected evidence remain fixed throughout live replay.
The v4 identity migration kept the same two guarantees and three pending broader
duties. The subsequent [EXACT-2026-01 adoption](../reference/authority.md#exact-constitutional-obligations) adds a pending
supplement across QS, PR and RS in v5; it creates no fourth jurisdiction or
discharged guarantee. Release readiness and full constitutional conformance
remain separate.

## Authoritative proposal record

The following is a generated inclusion of the repository proposal, not another
editing source:

```json
{{#include ../../../governance/proposals/initial-guarantees.json}}
```
