# Language editions and Qargo manifests

Adopted0.2.3 [#96](https://github.com/MGYamada/Qleisli/issues/96). All current .qli/.qlt edition2026, independent of product/schema2/Rust2024. Only2026 supported, no implicit default/coercion/cross-edition claim; phase/linearity/cleanup unchanged.

## Explicit declaration for every source tree

```toml
schema-version = 2
[qrate]
edition = "2026"
```

Edition-only not qrate identity; no root Qargo. [std](../stdlib/Qargo.toml) full synchronized qrate, other corpus/examples/tests/QLT edition-only pending management. Include manifest in standalone distributions, preserve first sources/diagnostics/licenses. In-memory parse2026, no invented files; raw IR no manifest. QLT no execution/qleisli test.

## Frontend checking and boundaries

Closest ancestor Qargo required, integer schema2/string2026. Malformed/unsupported/nearer unreadable/symlink/nonfile rejects, never skip upward; manifest65,536bytes. Static/dangling/replacement symlink reject via hardened macOS/Linux; Linux listed architectures require held /proc/self/fd,no fallback; other targets retain concurrent-filesystem assumptions. Bundled std manifest embedded.

Default root unchanged; --qrate requires existing relative descendant [source].root, no parent/symlink/target components; check every source inside even unused, ignore outside. Explicit src path still works. Source commands/load/sized/doc check editions; unknown metadata warns project/warning/outcome ok/exit0, no formerly accepted rejection. qrate_source_root/manifest_warnings configuration only. TOML/qargo orchestration outside semantic verification.

## Compatibility and future qrate migration

0.2.3 explicit user exception: add manifest; no other PATCH breaks. Future full qrate names/dependencies/layout/toolchains/schedule need separate specs/checks, grant no semantic/VM/QLT completion. `python3 scripts/check_editions.py` and test_check_editions.py verify.
