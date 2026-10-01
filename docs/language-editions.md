# Qleisli language editions and Qargo manifests

Status: **adopted and implemented for v0.2.3 at the user's request on
2026-09-30**. [Issue 96](https://github.com/MGYamada/Qleisli/issues/96) tracks
the decision, migration and validation. Production specifications remain English.

## Edition 2026

Qleisli adopts Rust's concept of a language edition. **All current Qleisli
`.qli` sources and `.qlt` drafts use edition `"2026"`.** It names the current
grammar, resolution, typing, ownership and semantic rules. This update adds no
new `.qli` expression, sealed operation or standard-library API. Quantum
linearity, explicit discard, exact phase and evidence for clean release remain
required.

The product version (`0.2.3`), Qleisli language edition (`"2026"`), Qargo
manifest schema (`2`) and Rust implementation edition (`"2024"`) are independent.
A compiler version bump does not silently change a source's language edition.
Only Qleisli edition `"2026"` is currently supported; future editions require
their own specified rules, checking support and migration. No cross-edition
compatibility guarantee is introduced by this first edition.

## Explicit declaration for every source tree

Every `.qli` and `.qlt` file belongs to a source tree with a `Qargo.toml` in
its top-level directory, whether or not the tree is a qrate. Non-qrate trees
use this minimal form, explicitly selected by the user:

```toml
schema-version = 2

[qrate]
edition = "2026"
```

The `[qrate]` table with edition alone is an edition declaration, not a package
identity. It does not make the directory a qrate or claim that current qargo
commands manage it. The current full qrate format comes from the
[in-progress qargo specification](https://github.com/MGYamada/qargo/blob/main/docs/specification.md);
its development checkout was consulted because qargo is being updated.

In this repository there is **no repository-root `Qargo.toml`**:

| Source tree | Governing manifest | Current management |
| --- | --- | --- |
| Standard library | [stdlib/Qargo.toml](../stdlib/Qargo.toml) | Full qrate now, schema 2, name `std`, version synchronized with Qleisli, separate `src`/`tests`/`docs` roots |
| Algorithm corpus, including source drafts and historical attempts | [corpus/Qargo.toml](../corpus/Qargo.toml) | Edition-only declaration; not yet a qrate |
| Each executable example | Its own `examples/<project>/Qargo.toml`, for example [Bell](../examples/bell/Qargo.toml) | Edition-only declaration; not yet a qrate |
| Test fixtures | [tests/Qargo.toml](../tests/Qargo.toml), with a separate [QLT design root](../tests/fixtures/qlt_design/Qargo.toml) | Edition-only declarations; not yet qrates |

The qrate name is **`std`**, matching the public `std::` namespace; `stdlib/`
is its directory name. The tested in-progress qargo accepts the full manifest
and captures its source tree, but its linked Qleisli 0.2.1 checker rejects the
local filename `basis.qli`. The [qrate guide](../stdlib/docs/README.md) records
this namespace-adapter gap; manifest compatibility does not imply a passing
qargo source check.

Include the governing manifest when distributing or copying a source tree.
For example, copy `corpus/Qargo.toml` to the top-level directory of an extracted
standalone corpus case. Source bytes, counterexamples, historical diagnostics,
licenses and attribution remain intact; adding edition metadata does not rerun
or change earlier validation.

## Frontend checking and boundaries

For each filesystem source, the frontend searches its directory and ancestors
for the **closest** `Qargo.toml`. It requires integer `schema-version = 2`
and an explicit TOML string `[qrate].edition = "2026"`. Omission has no default.
Numeric, Boolean or array editions, unsupported edition strings, malformed TOML
and unsupported schema versions fail before source parsing. An invalid,
unreadable, symlinked or non-file nearer manifest is an error; search does not
continue upward past it. Manifest reads are bounded to 65,536 bytes and do not
consume the separate source byte budget.
The regular-file check uses `symlink_metadata` before the platform opener, so
static symlinks (including dangling links) and non-files receive the same
manifest diagnostic on every platform. Hardened macOS/Linux openers additionally
reject replacement symlinks; other platforms retain the filesystem trust
assumption for concurrent replacements. The Linux component walk on x86/x86_64,
ARM/aarch64 and RISC-V requires accessible `/proc/self/fd` descriptors and
diagnoses their absence without falling back to following source symlinks.

The caller's module root and explicit sized-module map are unchanged by
manifest discovery. `Project::load`, source checking/compilation, source CLI
commands, documentation-file reads and `ParsedProgram::load` all check edition
configuration. In-memory parsing APIs use the current 2026 grammar and do not
invent filesystem metadata. The bundled standard-library manifest is embedded
beside its source, independent of user manifests.

QLT files receive edition-coverage checking only; **`.qlt` execution and
`qleisli test` remain unimplemented**. Raw IR checking does not take a source
manifest. The TOML reader is frontend configuration, outside the independent
IR verifier and evidence kernel. It validates only schema/edition; qargo owns
full qrate metadata, root validation and package orchestration. Metadata is not
semantic evidence and bypasses no ownership, effect, contract or IR check.

CI independently parses manifests with Python's `tomllib`, checks all `.qli`
and `.qlt` coverage and checks the standard library's complete qrate shape:

```sh
python3 scripts/check_editions.py
python3 scripts/test_check_editions.py
```

## Compatibility and future qrate migration

Requiring a manifest rejects formerly supported manifest-free filesystem
projects. The user's explicit v0.2.3 selection is a **narrow compatibility
exception for this edition declaration requirement**, not a compatible bug fix
or permission for unrelated PATCH breaks. Migration consists of adding the
minimal manifest above. Existing edition-2026 source syntax and meaning, Rust
API shapes, import namespaces and proof/release gates remain in force.

`stdlib` is already a qrate with a full qargo-compatible manifest and existing
source/test/documentation roots. **All other source trees are to migrate to
qrate management in the future**, including corpus cases, examples and test
sources. They are not qrates today. The package decomposition, names, dependency
relationships, toolchain selection and migration schedule remain to be specified
and tested; an edition-only manifest does not implement them. Preserve source
identities, module resolution, semantic contracts and third-party notices during
that migration. Qrate management does not confer acceptance authority on qargo
or complete the deferred QLT, verification-migration or theorem goals.
