# less_than_one2

Frozen source: `LessThanConstant` in `qualtran/bloqs/arithmetic/comparison.py` at `8db02b8b3fb39d69d2900dcc7b52d9d6a36834c3`.
License: Apache-2.0; attribution and modification notices are in both QLI files.

|x,t> -> |x,t xor [x<1]> for a two-bit unsigned x, scalar +1. Both target values and input restoration are required.

bitsize=2, less_than_val=1; a direct negative-control predicate, not a general comparator.
First leaf is the least-significant integer bit; printed results follow tuple order.
Every input owner is returned; no hidden discard or clean-release premise.

[Session](../../authoring/v029-small/README.md) retains the first source and real checks.
Full complex columns use an independent mathematical reference with X/Y interference,
including an initially nonzero input and reference control. No upstream framework is executed.
