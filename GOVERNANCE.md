# Qleisli governance

**Status: adopted, effective 2026-10-04 (Asia/Tokyo).** The
[human ratification and appointment record](governance/ratification-2026.json)
records adoption of the exact constitutional and governance candidates and the
initial Guardian appointment. The
[approved governance candidate](tests/fixtures/constitution_v030/governance-candidate.txt)
is preserved unchanged; this file updates its status and conditional wording
to reflect that event. The [ratification record and process](docs/src/design/ratification.md)
explain the separate acts. Adoption does not create a binding QS, PR or RS
interpretation or discharge a proof obligation.

The ratified [Constitution](CONSTITUTION.md) establishes the Constitution
Guardian Office. This governance document separates that institution from its
holder and from ordinary repository maintenance. It records the institutional
arrangements adopted with this document, developed in
[Issue #149](https://github.com/MGYamada/Qleisli/issues/149) under the
[constitutional adoption](https://github.com/MGYamada/Qleisli/issues/129).
The adopted Constitution governs any conflict with this file.

## Initial holder

**Current sole human holder: Masahiko G. Yamada.**

The initial appointment took effect on 2026-10-04 (Asia/Tokyo) through the
affirmative human decision preserved in the ratification record. Preparing a
document, checking its consistency or accepting an implementation does not
itself appoint a holder or confer authority to act for the Office.

The holder's identity belongs in governance records, outside the entrenched
constitutional text. The adoption record must identify the responsible human,
the adopted candidate and the effective date of the appointment.

## Existing ordinary maintenance

Masahiko G. Yamada currently maintains the repository and makes its ordinary
project and operational decisions. That existing role continues after
constitutional ratification. It does not derive from the Guardian appointment.

Ordinary maintainer authority remains distinct from Guardian
authority. Until the maintainer framework in
[Issue #150](https://github.com/MGYamada/Qleisli/issues/150) takes effect,
Masahiko G. Yamada remains the ordinary repository maintainer. Later delegation
or succession follows the adopted maintainer framework. Historical authorship
or use of the title *Founder* grants no additional governing authority.

## Constitutional interpretation and proof

The Office has final and exclusive authority to interpret
the Constitution and its QS, PR and RS obligations for a defined case or scope.
It determines which obligations apply and whether a proposed formalization
adequately expresses them. Maintainers choose language designs and
implementations within that interpreted boundary.

Lean or the designated independent checker establishes the resulting formal
proposition under its recorded assumptions. An Office ruling is not a proof.
The Office cannot waive a failed check, withdraw a protected guarantee or amend
the Constitution by interpretation. Any pre-v1 constitutional rectification
must satisfy the Constitution's Article IX and its expiry at v1.0.0.

A binding interpretation must be affirmatively adopted by the authorized human
holder or human members and recorded with its scope, constitutional grounds,
required proposition or evidence, relationship to existing guarantees and
reasons it remains within the Constitution. Pending obligations and formally
discharged ledger guarantees must be recorded separately. Routine changes
already covered by existing interpretations do not require a new ruling.

## Human exercise of the Office

Every holder or member exercising constitutional authority must be a natural
human person. AI, autonomous agents, software and analogous non-human systems
may assist with research, drafting, criticism, formalization, search and
analysis. They cannot hold the Office, vote, issue or approve binding rulings,
exercise suspension or rectification powers, or act as a holder's proxy or
successor.

Automation, preauthorization, default adoption and a human's failure to
intervene cannot confer that authority. The responsible human must knowingly
review and affirmatively adopt a judgment as their own; review and
responsibility must be substantive. Machine-generated drafts and successful
checks alone have no constitutional force.

## Reasoned constitutional suspension

The Office may suspend a proposed merge or release to resolve a plausible
constitutional violation. Each suspension must have a written record that:

1. identifies the proposed change and affected constitutional provision or
   protected guarantee;
2. explains the alleged weakening, evasion, trust-boundary change or semantic
   redefinition;
3. distinguishes the constitutional ground from ordinary technical preference;
4. states the review or remedy needed to resolve the objection.

An objection without that reasoning has no constitutional force. A suspension
protects the boundary; it grants no general veto over ordinary syntax, types,
compiler architecture, libraries, tooling, naming, performance or release
management within that boundary. Resolution must be recorded. Ordinary
maintainers cannot resolve a suspension by waiving a binding obligation or a
required proof.

## Succession and a possible council

The Office is transferable, and no individual has an inherent permanent claim
to it. Governance may provide a successor human holder or a council of human
members occupying the same Constitution Guardian Office. Such arrangements
must preserve its constitutional scope, exclusively human authority and the
separation of interpretation from mathematical verification.

Detailed succession, procedural-review and council rules remain future
governance work. This document does not establish those procedures or grant
an outside body authority to override the Constitution or its protected
guarantees. Holder changes must be recorded through the applicable adopted
governance process.

## Project identity and attribution

The proposed direction is to move project-level identity toward **Qleisli
Project Contributors** early after v0.3.0, and for Masahiko G. Yamada to cease
using *Founder* as a current project title. Present authority derives from
documented roles; historical origin grants no continuing office.

That transition is future work. Existing copyright notices, licenses,
third-party attribution, authorship records and Git provenance remain intact.
This document does not rename their authors or change their terms.
