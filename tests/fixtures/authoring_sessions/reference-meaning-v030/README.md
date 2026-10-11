# Endomorphic reference-Meaning boundary

Issue: [#46](https://github.com/MGYamada/Qleisli/issues/46).
The [context](context.md) and [first projects](attempt-01/) were saved before
the six CLI observations in [the session record](session.json). No source
repairs or production changes precede these observations.

| First project / public path | Actual result |
| --- | --- |
| Candidate `meaning Expected: Bit = reference(reference_h)` / project check | Parse rejection at `reference`; the form is not adopted or implemented. |
| Existing `apply_contract`, HHH against H / project check | Native contract accepted. |
| Same positive project / run | Complete closed distribution is classical zero with probability 1. |
| Existing `apply_contract`, identity against H / project check | Contract rejection at column 0, row 0: 1 differs from sqrt(2)/2. |
| Existing `apply_contract`, -H against H / project check | Contract rejection at column 0, row 0: -sqrt(2)/2 differs from sqrt(2)/2. |
| Unchanged positive source / explicitly selected Raw check | Unsupported runtime expression at `apply_contract`, before that adapter's native comparison. |

The reference body is independently written H. The final H/readout in the
positive control is only an execution observation; probabilities cannot detect
the deliberately wrong global phase. The negative native equation does.

The named `nonmonomial_reference_checks_preserve_exact_phase_and_axis` regression
in `tests/function_evidence.rs` additionally compares the retained result with
the literal matrix `[s,s;s,-s]`, where `s = 1/sqrt(2)`, and rejects swapped axes.
Its native equation compares separately supplied Raw programs; the literal
matrix is an independent host assertion, not a new native request. Its first
test source was frozen before running on Rust 1.99.0 and MSRV 1.85.0. Each full
function-evidence target passed 21 tests and retained one historical ignored
maximum-stress test. That host test predates this source session.

This study separates an unadopted syntax candidate, functioning ordinary
contracts and a selected-source adapter gap. It does not unify those paths,
extend general matrix/composite hierarchy equality, prove source preservation,
complete #46 or admit a guarantee. General arrows and rectangular Meaning
remain deferred beyond v0.3.0. QFT and large cases are outside this study.
