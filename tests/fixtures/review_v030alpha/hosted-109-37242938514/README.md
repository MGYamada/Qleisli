# Hosted failure audit: run 37242938514

This packet retains exact failure excerpts from four completed failed jobs of
[the PR 307 workflow run](https://github.com/MGYamada/Qleisli/actions/runs/37242938514).
The tested merge was `dca850b5e8b543af36cf1a907826a7a819dd9a4b`, merging head
`d753962de3eedd39629c8441f2b82521ce01d70f` into base
`ba83c5c97a9c67bf3904423745b3e9c019a083cb`.

Each excerpt line has its original one-based job-log line number, a tab, and the
unaltered timestamped log line. Full logs and distribution packages are not
copied into this packet. `metadata.json` names the actual failed steps and
skipped-step counts.

The Rust 1.98.1, Rust 1.85.0 and native-acceptance runs reached the same stale
negative in `tests/ordinary_types.rs:369`: the ordinary Bit constant `0` now
parses, while the test still calls `unwrap_err()`. Each recorded 13 ordinary-type
passes and one failure. The native-comparison job reported its other named
tasks as passed; subsequent steps and commands after failure are not covered.
The source expectation should be updated to the adopted Boolean/Raw behavior,
while retaining separate unsupported runtime-if checks. This observation does
not justify rejecting the supported Bit literal in production.

Distribution failed separately during `cargo rustdoc --offline --locked --lib
--target-dir .../package-docs -- -D warnings` (exit 101). Its precise compiler
diagnostic is in uploaded `logs/10.stderr`, absent from the job log. The
connector returned a remote artifact reference, but no ZIP was saved or
extracted locally. No diagnosis beyond the failing rustdoc command is claimed;
source tests did not produce the recorded failure.

Root separately reproduced a local `rustdoc -D warnings` failure from an
unquoted `Q<Bit>` documentation comment. The local command, source hashes and
diagnostic are retained in
`tests/fixtures/frontend_v030/quantum-unit-source/rustdoc-first/`. That record
uses the current local tree and does not replace the unavailable hosted
`logs/10.stderr` diagnostic.

This was a read-only audit: no build, test, retry, or production change was
performed. It does not establish that the current working tree or any later CI
run passes. Issue completion at this checkpoint remains 6/109 (5.50%).
