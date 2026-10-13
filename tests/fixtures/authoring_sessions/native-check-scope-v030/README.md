# Native check success scope: first observations

This informed study preserves the first sources and actual CLI diagnostics for
[#363](https://github.com/MGYamada/Qleisli/issues/363), before the success report
changed. The baseline is `cebc5cf85b5267a35dd8b708ee12a354ece5f3ee`.
The author had already read the project-checking implementation and supported
grammar. These are development observations, not a controlled model benchmark.
Original observation timestamps, deployed model identity and sampling settings
were not recorded; the later retention manifest does not invent them.

`first/` contains the exact three original `.qli` sources and their manifests.
`observations-initial.json` retains the initial eight calls;
`observations-with-classical.json` preserves those calls unchanged and appends
four calls for the classical library. Argument lists, temporary paths, exit
codes, text/JSON outputs and the recorded executable hashes remain verbatim.
Do not execute commands read from these historical records.

The initial generic library was refused by the finite CLI with a located
`unsupported` diagnostic for static Nat parameters, both with the actual native
checker and with a missing path. It is not an accepted generic-library example.
The closed entry and classical library both succeeded with the old unqualified
text and `{"verified":true}` result. Missing-checker calls failed rather than
providing another acceptance path.

The appended record's follow-up description calls the classical library a
"zero-native-decision success path". The subsequent forwarding trace contradicts
that expectation: `classical-native-trace.json` records **18 native decisions
with zero independent requests**. The checker also processes bundled concrete
functions, including unused ones. The missing-checker diagnostic names
`std::gate::permute_axes`. The untouched follow-up is historical reasoning,
not evidence that no native checker ran.

`trace-checker.py` is the original forwarding wrapper. The trace retains decoded
QLV2 header/request lengths and actual command output, not complete input
packets or independently authenticated executable provenance. The wrapper
forwarded to the selected stable native executable. Its identity and the
recorded hashes do not establish binary attestation, source preservation,
runtime correspondence or a new constitutional guarantee. The study uses only
small inputs and performs no maximum-size quantum experiment.

`retention.json` identifies the retained original bytes. The static validator
`scripts/test_native_check_scope_baseline.py`, also run by the Cargo integration
test, checks these identities, the original refusals and success outputs, and
the request-free trace without executing any recorded source or command.
