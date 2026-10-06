# Additive original-source capture preparation

This new wrapper reuses only the pinned authored `CASES`, `FORMS`, `command` and recording helpers from the original 72-command first-source driver. Importing those definitions never invokes its `main`; its historical 715-row build association and original output/session writer are not used. The original FIRST41 map, all eighteen two-file projects, session, registry and before observations remain immutable. This preparation has not been executed, imported, frozen against a future build or captured by its author.

After actual successful latest and final MSRV validation, the root records the exact `results.json` hash and runs the separate prospective freeze:

```text
python3 tests/fixtures/frontend_v030/common-original-ast-design/implementation-01/original-source-capture-01/driver.py freeze --msrv-attempt attempt-NN --msrv-results-sha256 <actual-final-results-sha256>
```

`freeze` writes new `prospective-inputs.json` using exclusive creation. It requires actual nine-stage terminal MSRV success, equal before/after declared input maps, matching current input bytes, unchanged checker, valid raw stage hashes, actual Rust/Cargo 1.85.0 version text and a successful rebuilt-CLI association matching the current fixed target. It records actual source/context bytes and modes, the entire historical first-source tree, capture machinery and validation records. Extra context absent from the validation map is explicitly listed; this remains a declared incomplete closure. Checkout HEAD is an identity marker, never compiled-HEAD attestation. Root reviews the concrete map before capture:

```text
python3 tests/fixtures/frontend_v030/common-original-ast-design/implementation-01/original-source-capture-01/driver.py capture --inputs-sha256 <reviewed-prospective-inputs-sha256>
```

Capture selects exactly eighteen by four authored commands: finite and selected-auto check, text and JSON. Metadata can assert identity and command equality but cannot select or execute arbitrary argv. The guarded CLI, native-log forwarder and bounded-process helper retain the original paths. Each command has 55 seconds, bounded 1 MiB raw stdout/stderr prefixes and a 1 MiB regular-file ceiling. All source, mode, original-record, MSRV-record, binary and capture-design identities are checked before and after every command. Output uses exclusive creation in the new `observations/` directory, with raw streams, command records, native-forwarding journals, events and final identity/file map. Observation paths are relative to this new packet.

Nonzero CLI exits are actual check observations. Launch, timeout, output-bound or identity failures retain partial evidence and `incomplete.json`, and stop without retry. Native journal rows attest forwarding immediately before `execv`; they do not separately attest native process start or exit. Outer process-group cleanup does not establish cleanup of separate descendant groups. No original source/session/status is rewritten and no original/final output byte parity is forced. This capture supplies no source-preservation theorem, complete generic/stdlib support, guarantee discharge, full CI, release result or Issue completion.
