# Current-artifact identity transport for the two admitted QLV1 guarantees

This implements the first conservative continuity unit recorded in #140/#141.
It does not change the approved proposal, its admission event, the historical
source archive, the two admitted scopes, or the three broader pending QS/PR/RS
obligations. It grants no additional guarantee and no release approval.

The prior guard required eleven semantic source files and the `Acceptance`
source block to retain their exact bytes. That guard rejected harmless comments,
formatting and theorem proof maintenance. The replacement compares the actual
elaborated meaning in the already-built current Lean environment with a baseline
extracted from a separate fresh build of the approved historical sources.

## What the fixed extractor compares

`Extract.lean` has nine fixed roots: `OwnershipSafe`, `ScopeSafe`, the ordinary
`Program`, `Artifact`, the complete `Acceptance` witness, the actual native
`check`, and the actual `check_acceptance`, `check_ownershipSafe` and
`check_scopeSafe` theorem types. No evidence record selects or omits roots.
The extractor follows all project constant references in declaration types,
definition bodies and recursor rules, including private and generated helpers.
Inductive mutual types and every constructor are included even when a theorem
only mentions the outer type. Thus all packet, decoder, request, accepted-root
and optional-request witness fields are compared, not just `Acceptance`'s name.

The result contains 1,244 declarations: 965 project declarations and 279 external
boundary declarations. Declaration origin comes from Lean's imported-module
map. The 204 historical project module names are generated from the immutable
source archive. Only the 39 external module origins actually reached by this
closure are allowed; they are in the pinned Lean/Init/Std toolchain. Unknown
origins cannot silently become trusted external definitions. External declaration
types and origins are recorded, and the Lean 4.30.0 toolchain plus package
manifests remain pinned. This does not authenticate a compiler installation.

The encoding uses tagged `Expr`, `Level` and `Name` constructors, not formatted
Lean text. It retains de Bruijn indices, full constant and universe names,
binder names and binder information, literals, let types/values/nondependent
flags, projection structure/index, and inductive/constructor/recursor metadata
and reduction rules. Free variables and unresolved metavariables are rejected.
Project axioms, opaque boundaries and unsafe/partial definitions are rejected.
Only expression metadata is erased. Reducibility performance hints and
non-kernel bookkeeping for a definition/theorem's original mutual declaration
block are not semantic content and are not serialized.

The bodies of theorem declarations are omitted; their exact closed types remain
in the closure. Definition bodies retain their proof subterms. The sole varying
executable body is `Protocol.Validity.check`. Its type, origin and direct use in
the three actual success theorem types remain exact. Its body dependencies are
still traversed, so new helpers cannot silently escape the protected closure.
Existing generated checker helpers remain fixed. Current builds, audits, axiom
checks and proof replay remain required. Every definition reached through
the byte-bound witness, including decoding and inspection, is conservatively
fixed in this first unit. The replayed guarantee proofs directly concern actual
current checker success and the original decoded root. The comparison does not
replace them with an implication between two closed theorem names.

This unit permits source formatting and theorem proof-body changes/additions
that leave that elaborated closure identical. It intentionally rejects binder or
universe renaming, declaration movement, private/generated name changes,
definition proof-subterm changes and representation changes when they alter the
encoding. Even a mathematically equivalent implementation can require a later,
explicitly checked artifact transport. No generic representation-changing
transport is implemented here. None of these comparisons proves the native
`Main`/IO route, Rust correspondence, runtime behavior or complete #141 coverage.

## Historical and current evidence

`baseline.json` binds the fixed extractor, the approved historical archive and
source revision, a gzip-compressed exact extraction, external manifests and the
original build/extraction records. `historical-setup.json` records archive and
213 source-file checks plus dependency revision checks. The separate historical
build used its own project oleans; only pinned package dependency caches were
reused. Its actual command and output remain beside this file. The final fixed
extractor produced byte-identical output in the historical and current
environments. Compression is storage only; the uncompressed stream hash is also
recorded. The original human-reviewed proposal and initial proof outputs remain
unchanged.

`governance/guarantees/current-evidence.json` schema 2 binds the current complete
source revision, existing build/audit evidence, fixed continuity extractor,
fixed baseline and freshly captured current extraction. Current evidence may be
refreshed after covered implementation maintenance; it cannot redefine the
historical baseline. Trusted-base checks protect the continuity files after
first introduction, independently of the earlier admission stage.

The default `check_initial_guarantees.py` checks saved file and source identities
only. Saved hashes and claimed exit codes cannot authenticate execution. The
`--verify-lean` path reruns the historical type/axiom review, the full binding
review and the fixed extractor in the current built environment, then rechecks
source identities. The normal selected model/full CI build and audits must run
before it. Tests-only or documentation checks do not claim fresh proof replay.
The existing release-ready gate still rejects the three broader pending duties.

From the repository root:

```sh
python3 scripts/test_check_initial_guarantees.py
python3 scripts/check_initial_guarantees.py
python3 scripts/check_initial_guarantees.py --verify-lean
```

The unit tests exercise strict record identity, confinement, stale source
bindings, extractor/baseline omission or substitution, external manifest changes,
changed full elaborated output and non-admission behavior. Their synthetic
records and mocked subprocesses are protocol tests, not Lean proof evidence.
Independent small Lean mutations are recorded separately in `regressions/`.
