# Independent ordinary-type cutover observations

This is an informed, bounded implementation review of Issue #27's
2026-10-05 ordinary-type contract, retained in `contract.md`. The reviewer had
repository/design context and coordinated with the implementation agent; this
is not a blind authoring experiment or a model benchmark. No external model was
invoked. The deployed model identifier and sampling settings were unavailable.

The production change gives ordinary `Unit`, `Bit`, and `Bits<n>` one source
type identity and uses `0`/`1` as ordinary Bit literals. These observations do
not expand native acceptance, adopt a new guarantee, or establish a general
source-preservation theorem.

## Preserved inputs and executions

- `first-sources.json` records 38 first sources, including deliberate type,
  ownership and syntax counterexamples, before the implementation observations.
- Three first attempts used `!`, `^`, and `&`, which are not the existing QLI
  Boolean operator spelling. Their real failures remain unchanged. The four
  separately recorded `follow-up-sources.json` cases use `not`, `xor`, and `and`,
  or the old spelling of the Unit-returning readout comparison. This correction
  is test authoring, not a new grammar requirement.
- `source-bearing-cases.json` adds an old/new explicit source pair whose native
  contract evidence retains source text. `unit-pattern-case.json` adds an
  unchanged consume/return program exposing the genuine-Unit pattern regression.
- `all-sources.json` contains all 45 unique cases. Every project has its own
  schema-2 edition-2026 manifest. Sources were not repaired in place.
- `before-source.json` and `before-source.tar.gz` preserve 106 input files from
  the initial Rust/stdlib checkout at `18f55693e31585dde67eeddeb064e77c138f9a57`.
  `after-source.json` and its archive preserve the 106-file implementation
  snapshot, including the Unit-pattern fix. These exact input identities, not
  the later shared working tree or its HEAD label, define the two builds.
- `before/`, `before-follow-up/`, `before-source-bearing/`, and
  `unit-pattern-before/` retain all 45 before observations; `after/` retains
  all 45 after observations. Each stage saves argument lists, working directory,
  exit status, streams, requested artifacts, and executable/input hashes.

`Observe.rs` uses the public common parser, finite frontend, and sized
parse/instantiate/elaborate/lower APIs. Successful proposals are submitted to
the actual native kernel. Instrument cases also run the native source-event
check and execute a small joint input with a two-dimensional reference.
Observer exit zero means observations were captured, including explicit
rejections; it does not mean that every input was accepted. For example,
finite checks of sized-only stdlib imports report missing modules. Each raw
diagnostic is retained without reclassifying it as a successful profile check.

## Results and repaired counterexample

`tests/ordinary_types.rs` has 14 tests, all passed with none ignored in the
isolated after checkout. It checks ordinary copy/drop, calls, literals and
Boolean actions; quantum/ordinary mismatches; exact Unit/Bits<0>/Bit/Bits<1>
and tuple distinctions; public `SourceType` accessors; small symbolic sizes;
genuine Unit lowering; empty and nested Unit patterns; zero-axis ownership;
and explicit unsupported profiles. `isolated-test-inputs.json` binds the test,
common test helper, manifests and included sources separately from the build
archive. `isolated-final/` records the tests and a successful Rust 1.98.1
`cargo clippy --offline --test ordinary_types -- -D warnings` run.

The independent review found that `let () = consume_empty(q)` was incorrectly
rejected when sized Unit became its own constructor. The unchanged program
had previously lowered and passed the native check. The actual intermediate
failure, test and relevant implementation source are preserved in
`unit-pattern-current-rejection/`; `unit-pattern-fixed/` records the same test
passing after the production fix. The final test also rejects attempts to use
that pattern on `Bits<0>` or `Q<Bits<0>>`. `test-first/` retains the earlier
13-test transcript as a development observation; the exact final 14-test replay
is the isolated result above.

`compare.py` independently checks the saved artifacts and produces
`comparison.json`: 18 files are byte-identical across the explicit migration
pairs, covering finite IR/actions, sized readout proposals/requests/precursors,
reference-sensitive instrument actions, and the unchanged Unit-pattern case.
For the source-bearing pair, every non-source QIRF field is identical. Both
changed source entries (`main` and `std::routines`) are separately checked
against their actual old/new source inputs. Source text is not silently
ignored or rewritten by an acceptance path. Source-event spans can change
with source spelling and are not claimed byte-identical.

The Unit-returning consume test checks that its quantum work survives and
that all four events pass native source-event validation. Its empty quantum
owner is retained until consumption; only genuine ordinary Unit has no port.
The independent expected branch amplitudes retain the untouched reference.

## Limits and replay

Existing profile restrictions remain explicit: finite register types, sized
classical entry lowering, sized runtime literal/Boolean expressions, and the
sized `Q<Unit>` profile are unsupported. The Unit-returning discarded-readout
case still rejects because current instrument results must retain every
observation. Its existing downstream diagnostic has no module and span 0..0;
this record preserves that limitation, with diagnostic integration left to
Issues #225/#27. No runtime work is silently discarded to make it pass.

Run `python3 tests/fixtures/frontend_v030/ordinary-types-independent/compare.py`
to repeat the saved-output comparisons. `record.py --help` describes fresh
stage recording; use a new output label, an independently unpacked recorded
checkout, and an explicitly selected built native kernel. The final integration
test needs `QLEISLI_KERNEL` pointing at that binary. Absolute temporary paths
are historical command context, not portable executable attestation.

This unit did not run full CI, a new maximum-size case, or a separate MSRV lint
run; repository-wide checks are coordinated by the root task. Hashes record
input/output identity, not mathematical adequacy, source preservation, or
trusted compilation. Existing Lean semantics and native acceptance were not
edited by this independent test task.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
