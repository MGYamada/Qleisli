# Authority and constitutional obligations

This chapter is normative for authority, change review and the distinction
between specification, acceptance and proof. It is subordinate to the ratified
`CONSTITUTION.md` in the [Qleisli repository](https://github.com/MGYamada/Qleisli).
It does not supply a binding mathematical interpretation of QS, PR or RS.

Edition 2026 was ratified effective 2026-10-04 (Asia/Tokyo). The repository record
`governance/ratification-2026.json` identifies the exact adopted text and the
affirmative human decision. The same decision adopted the preserved governance
candidate and appointed Masahiko G. Yamada as the initial sole human holder of
the Constitution Guardian Office. `GOVERNANCE.md` records that separate role.
The [ratification record and process](../design/ratification.md) explain these
acts and their scope.

## Normative authority hierarchy

The order of authority is:

| Layer | Authority and responsibility |
| --- | --- |
| 1. Constitution | `CONSTITUTION.md` establishes the permanent QS, PR and RS obligations, institutional authority, continuity and amendment rules. |
| 2. Binding interpretations and guarantee ledger | Human Guardian interpretations apply the Constitution to defined cases. Discharged ledger guarantees form the protected minimum for their recorded scopes and premises. |
| 3. Formal obligations and checked proofs or evidence | Current formalizations must express the applicable requirements and connect their discharge to actual production acceptance and accepted artifacts. |
| 4. Language Reference | The Reference specifies admitted language behavior consistently with the higher requirements and the stated verified boundary. |
| 5. Implementation and conformance evidence | Implementations, tests and examples must conform to the applicable specification. Informative guides explain it without creating new rules. |

This order cannot make a failed proof true. The Constitution Guardian Office
determines what must be proved and whether a proposed formalization adequately
addresses the constitutional case. Lean or the designated independent proof
checker establishes mathematical derivability under the recorded assumptions.
Neither decision substitutes for the other.

Maintainers choose ordinary designs and implementations within that boundary.
The Office has no general veto over those choices. A constitutional suspension
requires a written constitutional ground and the review or remedy needed to
resolve it, as specified in `GOVERNANCE.md`.

Only natural humans may exercise the Office's authority. AI, automated tools
and proof assistants may assist with drafting, analysis and verification. They
cannot issue, approve or automatically adopt a binding interpretation or act
as a human holder's proxy. Affirmative human adoption must be substantive;
silence, general implementation permission and passing checks are insufficient.

## Interpretation, obligation and discharge

A **proposed interpretation** is material for human review. Its presence in an
issue, document or Lean declaration does not make it binding.

A **binding interpretation** is an affirmative ruling of the authorized human
Guardian for an identified case or scope. Its record must identify the
applicable constitutional obligations, required proposition or evidence,
relationship to existing guarantees, and reasons the ruling remains within the
Constitution. It establishes an obligation; it does not prove that obligation.

A **pending obligation** is binding but lacks its recorded formal discharge.
It cannot be ignored because it is absent from the discharged ledger. A
correction or supersession requires a reasoned human ruling and must not evade
an applicable obligation or weaken an existing protected guarantee.

A **discharged guarantee** requires the checked proof or evidence and an
explicit ledger record binding the interpreted property, scope, premises,
semantic definitions, proof boundary and actual accepted artifacts. An ordinary
helper lemma is not promoted into the ledger merely because Lean proves it.
One proof may discharge several obligations when the correspondence is explicit
and mechanically justified.

Later releases must preserve every applicable ledger guarantee against their
current production acceptance and artifacts. Refactoring definitions or
replacing implementations requires justified semantic transport where their
representations differ. Retaining an old proof about an old checker, or proving
an implication between two already closed propositions, does not establish that
connection.

## Current adoption and proof status

The constitutional ledger, `governance/guarantees.json`, records **three binding
pending broader obligations and two discharged scoped QS guarantees**. The appointed Guardian
explicitly adopted QS-2026-01, PR-2026-01 and RS-2026-01 in a separate human act
on 2026-10-04. The event is recorded in
`governance/interpretations/initial-2026-adoption.json`, bound to the exact
reviewed text preserved in `initial-2026-reviewed.txt` in that directory.

The subsequent human adequacy and admission judgment is recorded separately
in `governance/guarantees/initial-2026-admission.json`. It admits
`QS-QLV1-OWNERSHIP-2026-01` and `QS-QLV1-SCOPE-2026-01` for the actual ordinary
QLV1 decoded root, under their exact recorded premises and exclusions. The
[scoped-guarantee record](../design/initial-guarantees.md) identifies those
meanings and evidence. These two entries do not discharge all of QS or any
PR/quantitative RS obligation.

The [initial QS, PR and RS interpretations](../design/initial-interpretations.md)
state their scopes, required properties and premises. Their adoption does not
constitute formal discharge. Existing theorems, tests, audits and engineering
decisions have not been automatically promoted into constitutional guarantees;
their recorded scope and outstanding obligations remain in force.

Before v1.0.0, release claims must disclose their applicable interpretations,
actual proof coverage, provisional formalizations and outstanding obligations.
A capability with incomplete required coverage must not be described as fully
constitutionally certified for that scope. Already discharged guarantees remain
binding throughout this period. From v1.0.0, a claim of full constitutional
conformance requires all applicable obligations over the current admitted scope
and preservation of the accumulated ledger.

Constitutional text and record-identity checks establish only the properties
they actually check. They do not authenticate human identity independently,
prove QS, PR or RS, or implement all ledger-continuity and production-coverage
requirements of [Issue #141](https://github.com/MGYamada/Qleisli/issues/141).

## Production acceptance and the trust boundary

The adopted architectural policy in repository `TRUSTBOUNDARY.md` remains in
force. Reference meanings require human specification review independently of
the checker and producer. Library placement, authorship, compiler output and
successful tests confer no semantic acceptance authority.

The [single-verifier decision #276](https://github.com/MGYamada/Qleisli/issues/276)
places production acceptance in the Mathlib-free native Lean checker. Fresh
decisions bind private accepted handles to immutable artifact/request bytes.
Rust performs parsing, diagnostics, transport, proposal generation, simulation
and packaging outside semantic acceptance. Missing, incompatible or failed
native checking must not fall back to Rust acceptance.

That implementation boundary is distinct from the Lean proof kernel and from
proof of the complete production pipeline. An accepted IR artifact alone does
not establish preservation of its source, execution result or exported target.
Claims must identify the actual accepted representation, requested contract
where present, emitted artifact and relevant checker/profile identity, together
with their preservation links and remaining assumptions. Native compilation,
decoding and runtime correspondence do not become proved merely because the
checker is implemented in Lean. Full supported-profile Soundness remains a
separate proof milestone; ratification does not complete it.

## Change and impact review

A language feature, semantic breaking change, or change to the acceptance or
trusted boundary must record its constitutional impact before admission. The
record must cover:

- each of QS, PR and RS, identifying an applicable binding interpretation or a
  pending interpretation question and explaining the affected scope;
- changes to normative definitions, accepted representations, trusted
  assumptions or semantic primitives;
- applicable ledger entries, current acceptance/artifact bindings and any
  required semantic transport;
- existing proof coverage, new proof or evidence duties, and remaining gaps;
- constitutional edition impact, separately from release compatibility and
  source/artifact migration.

This is the change-review process tracked in
[Issue #140](https://github.com/MGYamada/Qleisli/issues/140). A routine change
already covered by existing interpretations need not obtain a new individual
Guardian ruling or invent a new proof. It must identify that coverage. Wording,
test refactors and implementation changes with no constitutional effect may
record that conclusion with its reason. New constitutional cases or disputes
require the Office's interpretation; the author's impact assessment is not a
substitute for that ruling.

Proposed semantic primitives must additionally justify why ordinary checked
source, elaboration, a verified transformation or target lowering is
insufficient, and state the effects on the trusted boundary and all three
obligations. Performance or popularity alone is insufficient. A backend
intrinsic that implements an existing meaning does not thereby acquire a new
primitive meaning. The admission work in
[Issue #154](https://github.com/MGYamada/Qleisli/issues/154) must preserve the
current policy against project axioms and unchecked acceptance paths. This
chapter admits no new primitive or trusted assumption.

## Conflicts and corrections

- If a formalization omits an applicable protected case, repair and prove the
  obligation. The omission creates no constitutional exemption.
- If required proof or evidence fails, repair the implementation or proof, or
  withhold the affected acceptance or certification. A Guardian ruling cannot
  waive the failure.
- If a later interpretation conflicts with a discharged guarantee, preserve or
  strengthen the guarantee through the recorded correction process. Neither
  renaming nor narrowing the formal boundary can remove its protected scope.
- If the Reference and implementation disagree, resolve the specification or
  conformance defect under the higher requirements. Passing examples and tests
  do not redefine the language. An informative guide cannot settle the conflict.
- If ratified constitutional text must change, follow Article III's edition
  amendment process and Article IV's non-weakening rule, except for a valid
  strictly pre-v1 Article IX rectification. That exception requires an explicit
  reasoned human authorization, repairs an already adopted principle and
  expires permanently at v1.0.0.

Adding a new Fundamental-Theorem jurisdiction requires constitutional amendment
and an edition transition. Applying QS, PR or RS to a new case, or proving a
helper lemma, does not add a jurisdiction. New jurisdictions must justify their
distinct enduring purpose, relation to existing obligations, assumptions and
current proof coverage; see
[Issue #138](https://github.com/MGYamada/Qleisli/issues/138). An edition increment
cannot authorize weakening an existing protected guarantee.

## Editions, releases and compatibility

An **edition identifies the constitutional regime**, not a grammar generation,
source dialect or compiler version. A release/formalization state identifies
the current implementation, accepted language and formal realization within
that regime. Syntax, type-system and CLI changes belong to release versioning
and its published compatibility and migration policy. The unified 0.3.0
language therefore remains in constitutional edition 2026.

Source trees explicitly declare the constitutional edition through schema-2
`Qargo.toml`, in `[qrate].edition`. Updating the compiler does not implicitly
change that selection. Edition identity alone does not identify an executable
checker version, a grammar, a complete acceptance predicate or a proof of all
three obligations.

Constitutional continuity, source compatibility and continued implementation
support are separate promises. Reducing the accepted language does not by
itself weaken a safety implication, but may violate the release compatibility
policy. Retiring a parser does not erase historical ledger guarantees. Any
historical case accepted through a current migration remains subject to its
applicable guarantees and justified connection to the current artifact.
