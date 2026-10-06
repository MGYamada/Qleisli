# Atomic Bits CI repair

[Run 37540210797](https://github.com/MGYamada/Qleisli/actions/runs/37540210797)
failed two Native comparisons after the explicit atomic Bits extension.
[Observations](observations.json) identify the original head, synthetic PR merge,
job and complete retrieved log digest. [Failure excerpts](native-failure-excerpts.txt)
preserve selected original timestamped lines; they are not the whole log.
The original test sources remain in Git at the recorded head.

The finite projection test still expected all atomic Bits to be rejected.
The repaired test checks pending requests for widths 0, 1, 2 and 6, including
actual tags, axes and payload bytes. Width 7 and same-width substitutions
between Bits and Unit, Bit or tuple remain rejected. Opaque bodies never confer
semantic acceptance: [73 local cases](finite-local.json) pass with zero acceptances.

The test-only Lean decoder view omitted the new finite atom constructor.
It now renders its tag and width. Six additional QIRF1/2 cases observe atomic
Bits 0, 1 and 2, including nested products. [368 local comparisons](decoders-local.json)
pass through the actual Rust and Lean readers, retaining malformed-input checks.
Current report metadata now identifies Lean production authority and the actual
22 definition / 21 meaning variants; historical reports are unchanged.

The first local decoder attempt lacked an explicitly selected checker and failed
before the Lean driver ran. The recorded successful rerun selects the matching
current checker. This packet does not establish full hosted CI, universal decoder
or source correspondence, new constitutional guarantees, or release readiness.
