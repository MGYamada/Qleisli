# Bounded quantum Unit source integration

The immutable first fourteen sources and original diagnostics live in
`tests/fixtures/authoring_sessions/quantum-unit-v030/`. This directory retains nine first
integration translations and adds separately named readout derivatives. `translation-first-files.json`
records their initial bytes before test execution; it does not replace the study.

`tests/quantum_unit_source.rs` exercises the actual shared source API and native
hierarchy interface. Direct `phase_eighth` cases independently request the
literal equation `I_A tensor (pack_unit; [omega]; unpack_unit)`, followed by the
fresh owner rename, for Unit, Bit and Bits<0/1/2>. The exact coefficient is fixed
as `Exact::phase(1)`, independently of the candidate's producer meaning. Literal
owner labels 101..104 are inspected transport placement. A valid wrong phase
with a matching producer description must fail the unchanged external request;
valid Unit/Bits<0> identities must fail each other's exact typed request.

Provider apply, adjoint, repetition and coherent control are checked against
fixed external requests authored from exact omega, inverse, power and control.
Only transport labels and placement were inspected in the emitted proposals;
`fixed-requests/` preserves those observations and the first eleven-test source.
A twelfth test gives a wrong provider a matching producer description: native
acceptance of that valid wrong equation must succeed, while the unchanged
external requests reject it for both controlled variants. An independent
full-coefficient numerical oracle also checks a two-dimensional reference.
These checks do not claim an arbitrary root-matrix decision. Native checking
remains the existing conditional hierarchy boundary; these bounded cases do
not prove general source preservation.

The tests also retain zero-axis ownership and order, generic rejection in unused
and zero-count bodies, exact SourceType distinctions, and the explicit Raw
limitation. Scalar work before observation is checked as a pure source event;
scalar work after observation remains a located unsupported operation. The
previous finite coherent-control example supplies a separate interference oracle.
All cases use at most two system qubits. No build or execution result is claimed
by this authoring record; the root's subsequent actual validation records results.

The first actual new-target run retained in `latest-fifth/3.stdout.txt` passed
8 of 9 tests. Its readout case stopped at the existing hierarchy profile because
the first source returned ordinary Bit instead of exactly one packed Bits value.
The two original sources and their first hashes are unchanged. Explicit `-bits`
derivatives now use `empty_bits` and `prepend_bit[0]`; `derivative-map.json` binds
both versions and the actual failure. `first-test.rs.txt` preserves the original
Rust test and `new-test-repair.patch` records the complete test correction.

Two additional tests reject ordinary Unit/Bit, a tuple of quantum owners and
incorrect static/runtime arities, and check nested `phase_eighth` argument
execution exactly once through two fresh owners and the independent coefficient
`omega^2 = i`. Their first execution remains the root's coordinated rerun.


## Initial integrated validation

Rust 1.98.1 and actual 1.85.0 each pass **125 tests**: 102 across nine integration
targets, 16 sized library tests, two explicitly run native CLI tests, and five
existing small Fourier/QPE/gate tests. The last five are relevant because exact
port kinds also affect Fourier recognition. They retain their existing small
cases; no maximum-profile input was added or run. Both toolchains also pass
all-target Clippy, library rustdoc with warnings denied, and formatting. The
selected 366-input manifest is identical across all four final runs:
`5cfa5884e26275d0b4f42b4238f77fcf00efc448551a9d25f3f4314b7066d40a`.
Source and native checker bytes remain stable during each recorded run.

The new target has eleven tests. The first nine-test run passed eight and
exposed an invalid test-entry assumption: ordinary Bit readout must be packed
explicitly as Bits<1> for this hierarchy profile. The original files remain
byte-identical; `derivative-map.json` identifies the two named translations,
original failure and test repair. The original test is `first-test.rs.txt`.
Additional checks reject wrong scalar argument types/arities and verify that a
nested scalar argument is evaluated once, giving exact leaf phases and whole
operator action i rather than an omitted or repeated computation.

`validation-summary.json` classifies the real initial failures, including the
explicit vector annotation, two stale-profile test repairs and documentation
markup. Failed records are not relabeled as successful. The native/checking
semantics were not relaxed to make those cases pass. The initial authoring and
pending-repair records above remain historical; those executed results live in
`latest-final/`, `msrv-final/`, `latest-native/` and `msrv-native/`.

## Current fixed-request validation

After strengthening the transformed-provider requests and adding the independent
wrong-provider regression, Rust 1.98.1 and actual 1.85.0 each pass **126 tests**:
103 across the same nine integration targets (including all twelve new-target
tests), 16 sized library tests, two explicitly run native CLI tests, and five
existing small Fourier/QPE/gate tests. Both toolchains also pass all-target
Clippy, warnings-denied library rustdoc and formatting. All selected ignored
tests are explicitly accounted for. The four current records are
`latest-fixed-requests/`, `msrv-fixed-requests/`, `latest-fixed-native/` and
`msrv-fixed-native/`; their 366-input manifest is
`a615de916190042c6e997e30d80c37a7e9e4e134e35f53bee10cd01c6e600359`.
Every recorded command succeeds, with stable selected inputs and reused native
checker bytes. The prior 125-test records above remain unchanged.

`policy-identity/` separately records passing constitutional continuity against
the reviewed base, public-constructor inventory, production-coverage and docs
checks. Its 303 selected inputs remained unchanged. This is source/evidence
identity checking, not a new Lean replay or constitutional guarantee admission.

The separate `cli-current/` packet repeats all 28 original commands using the
identified successful latest-Rust build. Selected checking now accepts eight
programs and rejects six for their intended type/ownership violations. All
fourteen finite results, including stderr and exit codes, remain byte-identical
to the original baseline. This compares source acceptance, not open-function
execution. The direct scalar native-request and reference oracles are separate.

The preceding pushed head's hosted CI failed on the old ordinary-type assertion
and a distribution rustdoc command. Exact hosted excerpts are retained in
`tests/fixtures/review_v030alpha/hosted-109-37242938514/`. Local rustdoc reproduced
an unclosed Q<Bit> HTML tag in a Rust doc comment; backticks fix that local
failure. The inner hosted diagnostic was not downloaded, so this is a local
reproduction, not an authenticated reconstruction of that archived stream.

These checks retain the original source/evidence distinctions and outstanding
#27/#32/#43 obligations. They add no native acceptance rule or Lean proof, admit
no constitutional guarantee, and are not same-commit full CI or release
validation. Physical source atoms remain Unit/Bit/Bits; general Basis support,
public quantum Unit structural maps and the full common-language migration are
still unfinished.
