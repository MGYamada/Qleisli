# Language editions and Qargo manifests

Adopted/implemented v0.2.3 ([#96](https://github.com/MGYamada/Qleisli/issues/96)).
All current .qli/.qlt trees explicitly use Qleisli edition 2026. Product version,
language edition, manifest schema2 and Rust edition2024 are independent; a compiler
bump does not change syntax/meaning. Only 2026 is supported, with no cross-edition
promise. Quantum linearity, discard, phase and exact cleanup stay required.

## Explicit declaration for every source tree

```toml
schema-version = 2

[qrate]
edition = "2026"
```

Edition-only [qrate] is not package identity/current qargo management. No repository
root manifest. [stdlib](../stdlib/Qargo.toml) is full qrate std (directory stdlib),
synchronized release and separate src/tests/docs; [corpus](../corpus/Qargo.toml),
each example (e.g. [Bell](../examples/bell/Qargo.toml)) and [tests](../tests/Qargo.toml)/
[QLT root](../tests/fixtures/qlt_design/Qargo.toml) remain edition-only. Include the
manifest when copying/distributing a tree, including extracted standalone corpus cases.
Preserve first-source identities/diagnostics/notices; metadata does not rerun history.
[Std qrate guide](../stdlib/docs/README.md) records the tested qargo manifest and old
linked-checker basis.qli namespace gap; manifest compatibility is not source success.

## Frontend checking and boundaries

Search source directory/ancestors for closest Qargo.toml. Require integer schema2
and explicit string edition2026; no defaults/coercion. Malformed/unsupported metadata
or nearer unreadable/symlink/non-file manifest fails before parsing, never skips upward.
Manifest bound65,536 bytes is separate from source bytes. symlink_metadata rejects
static/dangling symlinks/non-files consistently; hardened macOS/Linux openers reject
replacement links. Linux x86/x86_64/ARM/aarch64/RISC-V requires accessible held
/proc/self/fd descriptors, no link-following fallback; other systems retain concurrent
filesystem trust assumptions.

Default module roots/explicit sized maps remain unchanged. Ordinary --qrate selects
string [source].root from the passed qrate directory: existing relative descendant
with no parent traversal, symlink or target components. Visit all .qli inside, even
unimported; ignore unrelated outside files/builds/links. This is not full qargo or
import-reachable discovery. Passing qrate/src explicitly still works.

check/run/sample/emit-ir warn about unused schema2 keys, category project/JSON warning,
without rejecting formerly accepted unknown metadata or changing success exit0.
Host qrate_source_root/manifest_warnings expose configuration only, no Project shape
change or authority. Project load/check/compile, source commands/doc reads and sized
ParsedProgram::load check editions; in-memory parsing uses2026 without invented files.
Bundled std manifest is embedded independent of user manifests.

QLT has edition coverage only: no .qlt execution/qleisli test. Raw IR has no source
manifest. TOML configuration stays outside independent verification; qargo owns full
package metadata/root/orchestration, never semantic evidence.

```sh
python3 scripts/check_editions.py
python3 scripts/test_check_editions.py
```

## Compatibility and future qrate migration

User-selected v0.2.3 manifest requirement is a narrow preexisting compatibility
exception, not permission for other PATCH breaks. Add the minimal manifest to migrate;
source rules/imports/Rust APIs/proof gates remain unchanged. All other trees will
migrate to qrate management later; names/decomposition/dependencies/toolchains/schedule
need specification/testing. Metadata confers no acceptance or theorem/VM/QLT completion.
