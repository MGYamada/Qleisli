# Small access and explicit-owner algorithm pairs

This informed study for #29 fixes ten complete edition-2026 projects before
their first checks. The [original context](context.txt), [source provenance](provenance.json),
[frozen packet](manifest.json), [independent expectations](expectations.json),
[observer](observe-first.py), [binary identities](observation-identity.json),
[license](LICENSE) and [notice](NOTICE) are retained. The manifest's unexecuted
status is the original pre-observation state; it is not a current result.
The author had repository and conversation context. This is not independent
first-author usability evaluation or a model benchmark.

Each algorithm has access-call and explicit consume/return forms: fixed
two-bit addition by three, a one-bit equality predicate, one N=4 Grover iterate,
a two-phase-bit QPE prefix with S and S-squared, and a two-vertex coined walk.
The QPE prefix deliberately excludes inverse QFT; generic QFT remains outside
the agreed beta work. Inputs and outputs retain their exact tuple trees and
source leaf order. Addition and walk include an untouched reference bit;
equality and QPE probe phase kickback. Grover uses the positive reflection
`2|s><s| - I`, including its scalar phase. At most three physical axes are used.
These are small first-party tests, not new upstream corpus imports or general
algorithm implementations.

The [session](session.json) links thirty actual CLI observations: ten project
checks, ten selected Raw checks and ten project runs. All project checks and
runs succeeded. Eight selected Raw checks succeeded. Both Grover variants
refused the `std::reflection` computed body with `unsupported runtime expression`
in the sized preparation profile. That profile limitation is retained without
translating the first source or treating project success as selected-IR success.
Check output expressly does not establish source-preservation verification.

Observation JSON preserves every original field, including verbatim stdout,
stderr, argument vector, exit status, source hash and recorded time. Retention
only adds parsed `stdout` for the existing session reader and the original
external record's SHA-256; no command is rerun to reconstruct first diagnostics.
The original external records remain unchanged. The observer checked frozen
source/manifest hashes before and after all calls, and stable CLI/kernel hashes.
Recorded binary hashes identify the observed files; they are not a native
compiler/runtime attestation. The observation HEAD predates the separate
metadata-only commit and the dirty-diff hash remains explicit.

The [distribution comparison](distribution-comparison.json) checks the ten
observed distributions against the prior mathematical expectations without
renormalizing probabilities. All pass absolute tolerance `1e-12`; the largest
error is approximately `2.22e-16`. This is numerical evidence only. The full
exact coefficients in `expectations.json` were fixed before checking and are
separate from this distribution comparison.

The integration regression imports each unchanged first module behind an
explicit contract wrapper. Its self-comparison retains the actual provider
body; an independently specified complete matrix is the semantic oracle.
Artifact checks, counterexamples and current test runs are separate from these
historical observations. General source elaboration preservation, static slice
integration, lifetime/footprint proofs, target correspondence and quantitative
resource bounds remain open. Ending `excl` restores authority, not a prior
state, separability, clean release or inverse operation.
