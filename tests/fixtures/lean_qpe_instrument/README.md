# QPE residual-instrument development record

This informed 2026-09-29 packet continues the active full-v0.2.0 goal under the
[selected contract](../../../lean/Qleisli/Qpe.lean). It is not a
controlled model benchmark, an external schema importer or a completed release.

## Preserved programs and independent discrimination

[first_source/main.qli](first_source/main.qli) performs two-bit QPE of T on
half of a Bell pair, retaining the target and then measuring both target and
reference in the X basis. Precision two cannot exactly resolve T's 1/8 phase.
[dephased/main.qli](dephased/main.qli) is a type-correct fault that measures and
re-prepares the target before the X measurements. The phase-label marginal is
unchanged, but the residual coherence and some joint probabilities differ by
1/16. The independently computed full K_y branches distinguish them.

The [first source baseline](first_source-baseline.json) and
[fault baseline](dephased-baseline.json) saved file hashes before either run;
both first attempts passed typing/execution without repair. The local ordinary
estimation/gate definitions were copied from the existing finite example, with
no new external corpus source. Original shared-sized drafts remain the target;
this packet does not remove source duplication or manual wiring yet.

## Actual proof development

- [ControlledPowers-first.lean.txt](ControlledPowers-first.lean.txt) and
  [first-power-diagnostics.txt](first-power-diagnostics.txt): `repeat` was a
  reserved Lean token; the implementation uses `iterate`. Explicit function
  composition and induction avoid uncontrolled unfolding of natural recursion.
- [Uniform-first.lean.txt](Uniform-first.lean.txt) and
  [first-uniform-diagnostics.txt](first-uniform-diagnostics.txt): split valid and
  invalid indices explicitly instead of asking arithmetic automation to prove
  equality between propositions directly.
- [Qpe-first.lean.txt](Qpe-first.lean.txt) and
  [first-instrument-diagnostics.txt](first-instrument-diagnostics.txt): repair
  sum simplification and use the actual complex conjugation ring homomorphism.
  The final plan theorem also fixes the target matrix dimension to 2^n.
- [Qpe-plan-first.lean.txt](Qpe-plan-first.lean.txt) and
  [first-plan-diagnostics.txt](first-plan-diagnostics.txt): simplify boolean
  guards before extracting bounds; convert positive natural bounds explicitly.
- [first-reduction-diagnostics.json](first-reduction-diagnostics.json): a finite
  count reduction exceeded the elaborator recursion limit. The final example
  derives 255 from the proved general count theorem and arithmetic; no runtime
  limit, audit rule or proof axiom was weakened.

## Executed evidence

[native.json](native.json) records 101 C-compiled plan decisions (64 positive
width pairs and 37 mutations), 4,080 literal controlled paths and 4,080 H
preparation paths. It also compares 1,080 full Kraus entries, 180 mixed
joint-reference density branches and 24 unitary-completeness cases. The latter
are numerical checks, not a completeness theorem. Checker dense dimension is
zero; the separate oracle's largest vector is 64.

[source-after.json](source-after.json) and
[msrv-source-after.json](msrv-source-after.json) record 32 expected probabilities
on each existing primary/MSRV binary, while checking all original source hashes.
[proof-checks.json](proof-checks.json) records both Lean builds, runtime
reductions and compiled/axiom audits. [regressions.json](regressions.json)
records fresh kernel replay, compiled-policy/helper tests and earlier QFT graph
regressions. Original and final checker/proof hashes are kept separately.

```sh
python3 scripts/test_lean_qpe.py
python3 scripts/test_lean_qpe.py --source-only target/debug/qleisli
```

The full operator and residual reference equations are proved for the actual
accepted internal components. Provider whole-space unitarity and controlled
access, external IR/encoding/registry binding, native execution
correspondence and sized source remain obligations. No external acceptance
format, production Rust authority or release publication changed.

## Completeness continuation (2026-09-29)

[QpeComplete-first.lean.txt](QpeComplete-first.lean.txt) and
[completeness-first-record.json](completeness-first-record.json) preserve the
first attempted proof before checking, including U=2I as the missing-premise
counterexample. [first-completeness-diagnostics.txt](first-completeness-diagnostics.txt)
records the real initial errors. Repairs made matrix sum ordering explicit,
reduced the finite-index coercions, removed unused typeclass assumptions and
used one cyclic trace rewrite instead of a looping simplifier rule. No proof
hole, native-evaluation axiom or audit exception was introduced.

The actual accepted plan's Kraus family is now proved complete conditional on
an independently established provider equation U†U=I. Tensoring with any finite
reference preserves completeness, and the sum of residual output traces equals
the input trace for every joint matrix. This is stronger than the earlier
numerical checks; it does not establish the provider premise or external binding.

[completeness-proof-checks.json](completeness-proof-checks.json) records the
3,369-job proof build and 707-declaration axiom audit; only `propext`,
`Classical.choice` and `Quot.sound` occur. The expanded independent oracle in
[completeness-native.json](completeness-native.json) replays the 101 native
decisions, 4,080 controlled and 4,080 preparation paths, 1,080 matrix entries,
180 joint branches and 24 completeness cases. It adds 24 reference-trace
checks and three faults: U=2I, a missing measurement outcome and the wrong
normalization. Original checkpoint records remain unchanged.

The next proof step also preserves
[QftUnitary-first.lean.txt](QftUnitary-first.lean.txt) and
[first-qft-unitary-diagnostics.txt](first-qft-unitary-diagnostics.txt). Repairs
separate conjugation rewrites, use equality/inequality branches correctly and
mark proof-only index equivalences noncomputable. The resulting
`QftGraph.check_unitary` proves both inverse laws for actual accepted graph
coefficients. [QpeComplete-acceptance-first.lean.txt](QpeComplete-acceptance-first.lean.txt)
adds `accepted_plan`, whose first build passes: acceptance now supplies actual
denotation existence as well as full branch, completeness and trace equations.
[unitarity-proof-checks.json](unitarity-proof-checks.json) records the final
3,370-job build and 728-declaration axiom audit, with the same three allowed
logical axioms. [proof-source-sha256.json](proof-source-sha256.json) binds the
final sources; earlier native and proof records retain their historical hashes.

## Fixed component dispatch continuation

[Schema-first.lean.txt](Schema-first.lean.txt),
[schema-first-record.json](schema-first-record.json),
[first-schema-diagnostics.txt](first-schema-diagnostics.txt),
[SchemaBridge-first.lean.txt](SchemaBridge-first.lean.txt) and
[first-schema-bridge-diagnostics.txt](first-schema-bridge-diagnostics.txt)
retain the initial dispatcher and semantic wrapper attempts. Repairs use
reflexivity after dependent case splitting and substitute the extracted
variables without erasing the independently named input variables.
[first-schema-reduction-diagnostics.json](first-schema-reduction-diagnostics.json)
records two `cbv` heartbeat failures. Kernel `decide` proves those closed test
propositions without increasing a runtime limit or using `native_decide`.

During specification alignment, the initial entire-schedule dispatch was
replaced by a single controlled power: exponent k, provider, positive local
control zero and literal count 2^k. This matches the fixed `controlled-power/1`
contract. k≤12 follows the repeat bound 4096; QPE still uses k=0..m−1≤7.
The earlier `schema-schedule-*` records preserve that intermediate stage; they
are not the final contract. The complete QPE schedule checker remains separate.

[schema-native.json](schema-native.json) records all 101 plan decisions through
actual fixed dispatch, plus **40** independent metadata/witness decisions
(**6** accept, **34** reject). Cases include exact `/2` ID mutations, declaration
strings, template versions, arity/order of parameters, witness-kind mismatch,
u32 reference boundaries, exponents 0/12/13/1,000,000, count zero/wrong count,
control axis, polarity and provider. Original numerical/path regressions also
pass. CI already invokes this script; no separate optional test path is needed.

[schema-runtime-checks.json](schema-runtime-checks.json) records **32** runtime
build jobs, reductions, **2,558** compiled declarations, **1050/1043** pure/
executable import modules, fresh kernel replay, and **19** source modules with
zero external packages. [schema-proof-checks.json](schema-proof-checks.json)
records **3,372** mathematical build jobs and **731** audited declarations.
Only `propext`, `Classical.choice` and `Quot.sound` occur in either audit.
[schema-source-sha256.json](schema-source-sha256.json) identifies final code.
At that checkpoint the complete external projection and exported-type/source-revision
registry manifest were unimplemented; no production wire profile was enabled.

## Type/source registry continuation

`SchemaExport-first.lean.txt` was saved before its first check;
`first-schema-export-diagnostics.txt` records the actual errors. The corrections
use Lean 4.30.0's `format.width` option and direct lifted `IO.println` in the
build-time command. Runtime source policy is unchanged. The shipped
[manifest](../../../lean/schema-registry.json) contains complete rebuilt types
and a source content revision; all three entries remain externally disabled.
`registry-checks.json` records package builds, both audits, fresh kernel replay
and the current export. The source-only check is deliberately weaker and does
not certify theorem types. See the [packet](../../../lean/README.md#component-registry-review).


## Coherent controlled-power completion

The [packet](coherent-power-packet.md) identifies the gap between literal
iteration with a fixed control and the full coherent operator. First runtime,
mathematical and schema sources are retained as `CoherentRuntime-first`,
`CoherentProof-first` and `CoherentSchema-first` text files. The runtime first
build passed. The first mathematical build's actual diagnostics are in
`coherent-proof-first-diagnostics.txt`: a namespace was opened as a declaration,
and several section typeclass assumptions were unused. Fully qualified runtime
names and explicit `omit` declarations fixed them. One subsequent build found
one more unused Fintype assumption; removing that extra premise completed the
proof. No linter or axiom-audit exception was introduced.

The actual `coherentStage` / `coherentRun` definitions retain the control sector.
Their complex interpretation proves arbitrary joint amplitude action equals
the complete block matrix, with the provider's phase intact. The single-stage
operator is diag(I,U^(2^k)); the schedule has U^j blocks in actual bit order.
Both single-stage unitary laws and the full arbitrary-reference map follow
under the explicit provider-isometry premise. External provider/evidence/IR
binding remains pending. The old `Schema.power_sound` theorem is retained;
the registry selects `Schema.power_coherent_sound` for this stronger statement.

`CoherentHarness-first.py.txt` and `coherent-first-native.json` preserve the
first native harness and actual compile failure: `State` was ambiguous with
an imported runtime type. Renaming the local type to `ProbeState` fixed it.
`coherent-native-before-source-mode.json` retains the successful intermediate
run before adding the source-only CLI mode. The final `coherent-native.json`
contains **188 decisions (180 accepted, 8 rejected)**, **9,352 exact Gaussian-
integer coefficients**, **17,280 joint-density entries** and **295,026 actual
oracle uses**. Providers and powers are checked against independent literal
Python matrices and repeated squaring; checker dense dimension is zero and the
largest mathematical oracle matrix has dimension four. The coherent X^2 versus
(iX)^2 fault keeps basis probabilities equal but changes an off-diagonal entry.

The two [ordinary QLI sources](coherent_phase/plus_x/main.qli) and
[type-correct phase counterexample](coherent_phase/minus_x/main.qli) were saved
before execution and remain unchanged. Both first attempts passed: correlated
control/reference preparation, a target in |+>, controlled X or −X, then
uncompute/interference returns 000 or 100. The hash baseline records the retained
sources and observed first outcomes; the captured follow-up CLI run is in
`coherent-source-checks.json`. This exercises the existing finite Rust source
path, not the future sized-source compiler. No authoring burden reduction or
measured model-performance claim follows.

The existing **101 plan / 40 schema** suite was rerun, including 4,080 power/
preparation paths, 1,080 Kraus entries, 180 joint branches, 24 completeness and
24 trace checks plus three completeness faults. Its previous record is
`native-before-coherent-power.json`. Kernel reduction tests also pass, recorded
in `coherent-reductions.json`. CI includes the new native suite and both Rust
jobs' source probes; no hosted CI run or local MSRV source rerun is claimed.


Final coherent-power registry rebuild, both audits and fresh runtime kernel
replay pass: **3,940** runtime/transport and **754** mathematical declarations,
with the same three permitted logical axioms. Runtime policy covers 25 modules
and no external Lake package. `registry-before-power-binding.json` binds the stronger actual
theorem type; `registry-before-coherent-power.json` preserves the previous
statement and validation. All external entries stay disabled. Registry mutation
checks and source identity pass, and the final native record hashes match the
current runtime and harness. Full v0.2.0 validation is still pending.
