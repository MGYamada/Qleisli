# Fixed forty-check after collector

Preparation only. Root reported latest Rust attempt-02 successful; the observed
rebuilt CLI is pinned at 2209c0528e4f25dc46498bbbe8cc3ca3df31201e0fa7bed41130bff593e233c9.
This collector has not been imported or executed during preparation.

Root reviews inputs.json and invokes observe-after.py with its exact SHA-256
using --inputs-sha256. The output is the single new after-attempt-01 directory;
an existing partial directory is never overwritten or retried. The original
46-file FIRST map, complete 203-file before directory and session remain fixed.
Each of the forty commands uses the exact original source/manifest paths and
guarded authored command function; recorded argv is never executed. The map
pins the current full declared source/contract closure, including all seven
Formals production inputs, rather than demanding the historical old closure.

Raw stdout, stderr, status, native journal bytes/argv and row counts compare
exactly, without normalization. The same bounded streaming helper supplies a
55-second outer deadline and 1 MiB captured-output/file ceilings. Native journal
rows are forwarded invocation attempts immediately before execv; they do not
independently attest native starts/exits. Outer group cleanup does not establish
complete descendant cleanup. Operational failures and genuine differences stay
in additive output. No runtime oracle, source-preservation proof, guarantee or
Issue completion is asserted.

Completed output contains forty per-call .json records, literal command-before
records, raw .stdout.bin/.stderr.bin/.native.jsonl files, identity.before/final,
summary.json (comparisons and all_equal/differences-observed) and files.json
(byte/hash inventory excluding itself). A terminal record is required separately.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
