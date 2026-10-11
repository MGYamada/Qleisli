# Type and pattern acceptance review

This review covers the existing 0.3.0 criteria of Issues #84 and #35 at
9a1ecef79f2f1e42f94093b6f4822f282f6e9129. It neither admits implicit coherence
nor implements future rest patterns or general Basis polymorphism.

## Classification (#84)

The Reference distinguishes structural definitional equality, explicit checked
canonical maps and physical operations. Complete constructor/arity/nesting and
size equality remain enforced; equal width is insufficient. Neither physical
maps nor axis permutations are inserted by coercion, and inference cannot
choose among semantic meanings. Future implicit conveniences remain #197.

An independent read-only review matched all seven criteria to the Reference,
shared Type::equivalent_by, symbolic size comparison and exact function-evidence
binding. Five existing bounded regression tests were then run on actual Rust
1.98.1 and actual 1.85.0: implicit reassociation rejection, explicit layout with
an entangled reference, wrong permutation rejection, exact evidence basis-tree
attachment and wrong Meaning phase/tree rejection. All ten invocations pass.
They are selected tests, not complete runs of their integration targets.

The original Unit-map packet separately records 149 passing checks per
toolchain, including ordinary exact-type, pattern and phase/reference tests.
Neither these tests nor the classification itself are a general preservation
proof or a new constitutional guarantee.

## Patterns (#35)

All admitted destructuring positions use the common recursive Pattern parser
and Type::pattern_fields. Basis/coherent, ordinary parameter/let and sized
symbolic/concrete consumers preserve one value's exact shape and call arity.
Existing runtime_parameter_patterns and unit_patterns tests cover duplicate
names, static collisions, nested/zero-width linear wildcards, located errors,
complete argument evaluation and retained effects/scalar phase; both suites
passed in the published Unit-map validation.

The accompanying Reference paragraph states the Issue's existing conditional
rest-pattern obligations: omitted components must be unrestricted or separately
consumed, rest syntax implies no physical action, future rejections must identify
hidden linear components, and this is an intentional Rust divergence. Rest is
not in today's grammar; no present field-level rest diagnostic is claimed.

## Scope and recorded observer interference

The selected source map remains unchanged across these checks. The existing
native binary is reused, with no Lean rebuild/audit/replay or maximum-size run.
The command records identify the bounded reusable Cargo target and actual
toolchains; they do not attest every dependency or operating-system input.

Cargo's integration-test builds also relinked target/debug/qleisli while a
separate first-source tuple study was using that shared binary. That study's
initial final-identity check failed and its original observations are retained.
After this run ended, it repeated its observations with a stable identified
binary. The test success here does not turn the earlier unstable-observer study
into stable evidence; the study records that distinction itself.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
