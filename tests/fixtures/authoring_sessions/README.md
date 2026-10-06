# Authoring and repair observations

These records begin in 0.1.8. They are development observations, not a controlled
LLM benchmark. No external model was invoked. Context is documented honestly,
including prior repository access and known workarounds; the exact deployed
model identifier and sampling settings were unavailable.

| Session | Kind and observed outcome |
| --- | --- |
| [Iterative QPE](iterative-qpe/session.json) | Informed new-source attempt, preserved before checking. Initial check passed; T on `|1>` returned `1001` within numerical tolerance. The five semantic tests subsequently passed. **Zero source repairs**; tiny numerical zero outcomes are retained in raw output. |
| [Product layout](type-layout-repair/session.json) | Curated replay of an existing rejected program. The same source rejects before/after, but now names the expected and actual trees. A previously known adapter checks/runs and returns `101`. One source revision, not blind model repair. |
| [Cleanup](cleanup-repair/session.json) | Curated replay of H H in restricted `with_computed`. The same source rejects before/after; the new hint identifies the three-argument contract form. A known explicit identity contract checks/runs and returns `0`. One source revision, not evidence that hints alone improve model success. |

The 0.2.0 continuation adds [shared QPE](shared-qpe-v020/session.json), whose original `CWord` spelling and parse failure are immutable history, and [sampled Grover](grover-trial-v020/session.json), whose missing-kernel repair precedes the implementation of sampling. Current design uses `CBits`; the appended Grover observation uses the unchanged repaired source with the new sampler.

The [0.2.1 reshape draft](reshape-v021/session.json) preserves an explicitly
typed conversion before checking and its real parse failure. It is informed
desired source, with no claim that the draft spelling is implemented. The
separate Lean metadata experiment does not repair that source yet.

The [sized-Xor first attempt](sized-xor-v021/session.json) starts the authorized
0.2.1 corpus-completion work. One desired size-parametric definition retains
both owners, including the empty-fold boundary. The first check rejects the
reserved name `xor`; a saved rename reaches the unsupported static-fold range token `..`.
Hierarchy and G020-1 prerequisites remain pending.

The [linear-size reshape first attempt](sized-reshape-v021/session.json) retains
split/merge, `n+1` low-bit peeling and doubled-size source before checking.
The actual parser rejects `+` in `Bits<n+m>`. This records the adopted next
design obligation, not an executable adapter or algorithm proof.

Each `session.json` names the task, kind, baseline commit/version, context,
ordered attempts and observations. Each attempt contains a complete project,
source hashes and a reason; observations retain argument lists, exit codes and
actual JSON output or a test transcript. Before/after refers to diagnostic
changes in this working tree, not a version bump. First observations were
captured before modifying Rust diagnostics. No failed attempt was invented
for the initially successful QPE source.

An attempt may also link `reports`: retained JSON diagnostics or validation
summaries whose original metadata differs from command observations. Related
clients may use separate `source_records` with repository-relative source hashes
and reports; they are not numbered repair attempts. The checker validates these
links and hashes without inventing missing commands, exit codes or timestamps.

For the next session:

1. Record the task, available context and author/model information **before**
   the first check. Preserve the untouched source as `attempt-01` and hash it.
2. Append actual diagnostic/execution observations. Never replace the initial
   result with a later run. Do not execute commands read from a record.
3. If source changes, save a full next attempt and its reason. Keep deliberate
   counterexamples outside the repair sequence and label curated replays.
4. Link semantic oracles, not just compilation. State context differences when
   comparing attempts; no model success-rate claim follows from these records.
5. Track newly exposed friction in a GitHub Issue or the
   backlog. A GitHub Issue needs no duplicate
   backlog entry, update or A020 ID.

The [operator-arrow study](operator-arrow-v030/README.md) retains twelve
programs, three honest source snapshots and 72 actual check observations.
It records private-entry/import repairs, the current Iso-root/quantum-Unit
profile limit and parser rejection of unadopted arrow/capture candidates.
Its context clarification and raw-event companions preserve the actual read
and metadata-repair chronology. Check success is not a semantic oracle.

`python3 scripts/check_authoring_sessions.py` checks hashes, source inventories,
context/observation presence and consistent recorded exits. It does not replay
commands, authenticate provenance or certify program meaning. Seven checker
tests protect against lost/edited snapshots and contradictory records. Both
commands run in the docs CI job; Rust tests replay the QPE snapshot and repair
regressions. Existing records are retained even when diagnostics evolve.

The [Iso preparation study](isometry-preparation-v030/README.md) retains fourteen
first projects and 56 before/after checks with actual native invocation counts.
Eight supported Iso roots now use existing preparation and empty-readout
transport; the pure control and five rejection cases retain their behavior.
Independent exact requests, reference coefficients and real failed validation
attempts are recorded separately from these check-only observations.

The [corpus-first Xor/GHZ continuation](sized-corpus-v021/session.json) preserves
both actual sources before experimental compilation. Initial direct lowering
hit the checker budget at Xor width four; an intermediate normalized producer
still failed at eight. Register-tail factoring and explicit one-bit conversions
now admit all selected widths without changing any checker limit or rule.
Complete basis/reference diagnostics and deliberate valid-circuit faults are
in the [execution record](../../../corpus/sized/validation.json). Production
CLI support and general source preservation are separate outstanding work.

The [shared QFT and inverse client](sized-qft-v021/session.json) retains the
first static-comparison lexer rejection and the later missing-module rejection.
The repaired development compiler executes the unchanged forward source and
its imported `adjoint` client. [Validation](../../../corpus/sized/qft-validation.json)
includes independently requested forward Fourier meaning, all inverse columns,
shared repeated calls, an entangled frame and valid-but-wrong source mutations.
The original sources were not rewritten after checking; no controlled-model
success rate or general source-preservation theorem is claimed.

The [shared coherent QPE session](sized-qpe-v021/session.json) saves source with
transparent operation access and controlled repetitions before the first
missing-phase-adapter rejection. It retains the subsequent (8,8) capacity
failure and corrects the upstream attribution year in a separate snapshot.
Small-system checks now cover phase/reference-sensitive providers and the
same imported inverse QFT. The user's 2026-09-30 instruction defers further
maximum-size checks; prior failures remain historical. Measured `CBits`,
production integration and named QPE binding remain open.

The [shared AddK/Equals session](sized-arithmetic-v021/session.json) preserves
recursive source before its first missing-operation rejection and a later
small width-three equality budget failure. A second snapshot extracts shared
complement; complete-content imported-graph sharing admits the same small case.
The final record covers widths 0–3, inverse/controlled clients, 557 basis and
96 reference columns, seven algorithm faults and twenty source rejections.
No maximum-size check or universal source/algorithm proof is claimed.

The [shared QPE client session](sized-qpe-clients-v021/session.json) preserves
local order/amplitude sources and their common QPE inputs before the first
static-argument parser rejection. Operation forwarding now keeps explicit
capabilities, exact types and nested-provider identity. Small tests include
N=15, non-dyadic order phases, p=0/1, off-grid amplitude estimation and full
residual target/reference behavior. These are local integration fixtures, not
new upstream translations or a measured `CBits` implementation.

The [measured QPE first attempt](measured-qpe-v021/session.json) preserves the
desired initialization/readout wrapper and its actual missing-import failure.
Its second snapshot retains the recursive helpers and classical word assembly;
the [checkpoint](measured-qpe-v021/checkpoint.md) separates later implementation
and validation from the original failure and stopping point. A current parser
replay is recorded separately from the retained historical diagnostic reports.

The [0.3.0 type-foundation session](type-foundation-v030/session.json) saves
three desired projects before checking: unmarked observation output, an empty
quantum owner and one generic operation body at two basis types. The current
compiler rejects the ordinary `Bit` result and proposed basis parameter grammar.
The unit project initially violates the existing CLI entry convention; a
separate snapshot changes only `main` to `observe` and passes. This validates
that small ownership identity example, not scalar-phase semantics or the new
generic design. It is informed authoring, not a blind model benchmark.

The [finite Unit-pattern study](finite-unit-pattern-v030/session.json) preserves
nineteen informed first sources before checking with the existing canonical
CLI: seven desired exact Unit patterns currently reject, three named-binder
controls pass, eight deliberate type/effect/arity counterexamples reject, and
one broader runtime parameter-pattern draft remains a parse rejection. The
study separates ordinary Unit matching from coherent basis lifting and retains
effectful-body/scalar-phase obligations for the implementation; it neither
rewrites historical observations nor claims that the new patterns already work.

The [runtime parameter-pattern study](runtime-parameter-pattern-v030/session.json)
preserves exact ordinary Unit/product/wildcard parameters, ownership and
declaration counterexamples, and existing named controls before implementation.
Its 39 first finite/sized checks retain the original diagnostics; separate
follow-ups preserve three unchanged named-control IR artifacts. Parameter trees
remain distinct from argument lists, and the later bounded tests separate source
checking, native acceptance and independent phase/reference expectations.

The [ordinary Boolean study](ordinary-boolean-v030/session.json) preserves twelve
informed first projects and thirty-three actual pre-change CLI observations.
Nine closed execution probes agree with independent expectations; the sized
failures distinguish projection and transport limits from source typing.
These historical results remain unchanged while common Boolean preparation and
source-bound execution are implemented. Mixed quantum execution and open
classical invocation remain separate unfinished parts of that work.

The [mixed Boolean study](mixed-boolean-v030/session.json) preserves twelve
complete first projects and thirty-five observations of the preceding CLI.
Independent Bell and pending-argument expectations retain measurement order and
caller correlations. Its existing hierarchy accepts the recorded fine phase;
the following Raw implementation's exact-eighth limitation is a selected-target
boundary, not a language-wide rejection. Original sources and observations are
unchanged; independent mixed execution tests accompany the new shared state.

The [selected-source CLI study](selected-source-cli-v030/session.json) preserves
an explicit Unit-parameter source before CLI changes. Its four actual baseline
observations separate an unavailable command form from hierarchy profile
rejection. Zero physical width does not supply a missing runtime argument.
The existing mixed and parameter-pattern first sources remain unchanged.

The [quantum Unit study](quantum-unit-v030/session.json) preserves fourteen
informed first projects and 28 actual checks using the existing selected-source
CLI. Q<Unit> identity, helper, scalar and provider candidates still encounter
the sized basis-profile restriction; finite checks separately expose ownership
rejections and existing capabilities. Ordinary Unit and Q<Bits<0>> controls
remain distinct. Earlier profile rejection does not establish a downstream
type/ownership condition, and checking an empty main does not execute the open
phase function. Original source/manifest hashes precede all observations.

The [quantum Unit map study](quantum-unit-maps-v030/session.json) preserves
22 complete first projects and 44 actual baseline checks before public
`unit`/`finish` implementation. Nineteen projects stop at the unavailable names;
those results do not validate their downstream type, owner or effect conditions.
The packaged-product example exposes a separate projection boundary, while
the two existing controls retain their behavior. Independent intended equations
and reference conditions remain separate from these diagnostic observations.

The [explicit inference-law study](inference-law-v030/session.json) preserves nine
informed first-source projects, 24 checks before/after repair and exact native
invocation counts. Its open checks and separate bounded action tests are not a
zero-prior benchmark or source-preservation theorem.

The [packaged quantum tuple study](quantum-tuple-unitors-v030/session.json)
preserves 22 complete first projects and 88 actual observations. Concurrent
Cargo tests replaced the first observer's CLI; all 44 original observations and
the failed identity check remain intact. The 44 appended repetitions identify
a fixed CLI before and after each invocation. Their agreement does not remove
the first run's provenance limitation. Exact unitor, scalar and reference laws
were authored before execution and require separate validation.

The historical local QFT family study recorded31 bounded observations at widths
0–3: twelve checks, fifteen complete basis columns and four coherent/reference
probes. The maintainer subsequently excluded generic-QFT completion from v0.3.0
and the current goal, and requested retention only under experimental/.
[Retained attempts and archives](../../../experimental/qft/README.md) preserve
the source, first failures, results and review bytes. These archived observations
are not current authoring-checker sessions, canonical stdlib exposure or a
general proof; no historical command is replayed by this index.

The [common source-collection study](common-source-collection-v030/session.json)
freezes eight complete projects and 23 real pre-code observations before the
private loader refactor. [Results](common-source-collection-v030/results-before.md)
retain finite bundled QFT checking, sized private siblings, complete-declaration
rejection, diagnostic ordering and reserved-namespace boundaries. The frozen
driver records later output/proposal-byte comparisons separately; source
collection identities do not prove source preservation or expand acceptance.
The [authorized replay](common-source-collection-v030/results-after.md) preserves
all 23 original stdout/stderr/status/native-count observations and the exact
untrusted proposal bytes, including both diagnostic-order controls. Rebuilt CLI
and current source identities are recorded separately from the frozen baseline.

The [common declaration/pattern study](common-pattern-check-v030/session.json)
preserves eight complete first projects and forty actual check/emit observations
before sharing checker judgments. [Results](common-pattern-check-v030/results-before.md)
retain profile-specific diagnostics, zero-width logical owners, unused invalid
declarations and complete source/CLI/native identity. Emitted proposals remain
untrusted; this baseline does not complete a common checker or source preservation.
The [separate after capture](common-pattern-check-v030/results-after.md) preserves
all forty original raw outputs, exits, native argv/counts and proposal bytes.
Original session records remain fixed; the additional capture is indexed by
its own summary, with no runtime, new mathematical guarantee or completion claim.

The [common parameter-declaration study](common-parameter-declaration-v030/session.json)
preserves ten first projects and forty actual checks before sharing ordered
name judgments. [Results](common-parameter-declaration-v030/results-before.md)
separate genuine duplicate/type-order observations from earlier profile and
projection failures, retain complete unused-declaration rejection and all44
native calls, and make no source-preservation or Issue completion claim.
The [separate after comparison](common-parameter-declaration-v030/results-after.md)
matches all forty raw outputs, exits and native argv/counts, while preserving
the original session. Both actual Rust versions pass the existing bounded
declaration/type/effect suites; complete common checking remains unfinished.

The historical exact-QFT request study and its generation/capture tooling are
also retained in the [experimental history archives](../../../experimental/qft/history/relocation.json).
The first capture retained four tiny emissions/inspections and four unchanged-
request refusals; later canonical-label checks retained eight successes and
wrong-target refusals. The original invalid-rewire failure kept its request
skipped. Archive identity preserves those observations without replaying them
or claiming source preservation, a general family, specialization equivalence
or completion of the standard-library migration.

The [shared formal-operation study](common-formal-access-v030/session.json)
preserves ten complete first projects and forty actual pre-code observations.
[First results](common-formal-access-v030/results-before.md) retain ordered
kind/access diagnostics, private unused-body checks, profile barriers and all46
forwarded invocation attempts. Those attempts are not child-start attestation;
unchanged original sources and raw results are the later comparison baseline.
