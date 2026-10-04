# Contextual static-natural type words: retained CI regression

The hosted sized-dialect comparison exposed a compatibility regression in the
common parser. On the isolated baseline
`fae0e6a149f5b218bcc7f67f38d9509eb8aeb4f3`, the unchanged test
`python_static_comparisons_keep_type_angles_separate_in_both_dialects` fails at
line 97 for the exact source saved in `minimal.qli`:

```qli
pub unitary fn f[static Q: Nat](q: Q<Bit>) -> Q<Bit> { if static Q < 2 { q } else { q } }
```

Rust rejects the binder at bytes 24..25 with `expected an identifier`; the
concrete Python oracle accepts it. The error occurs before the comparison.
The shared lexer correctly retains `Q` as a type-word token, but the migrated
parser treated only ordinary `Ident` tokens as static-natural names. The old
sized parser had read these names contextually. `cases.json` retains the small
source/argument cases and Python results; `rust-before.stdout.txt` records the
actual Rust diagnostics. `n`, `Bits` and `CBits` already accepted, while `Q`,
`Op`, `Unit`, `Bit` and `CBit` rejected. The original failing CI assertion is
retained unchanged.

## Repair boundary

The parser now interprets precisely those five existing type-word token
categories as natural names in static-natural grammar positions, alongside
existing ordinary identifiers. The lexer is unchanged. A static declaration
uses this contextual rule only with `: Nat`; an operation-parameter declaration
still uses ordinary identifier rules. The same natural-name rule covers type
dimensions, arithmetic, constraints and comparisons, fold bounds and natural
index binders, specialization arguments, and natural repetition counts.

The ordinary function/runtime/operation-binder identifier parser is unchanged.
This does not generally adopt the old sized parser's acceptance of arbitrary
reserved words as names. Type constructors retain their existing meaning in
type syntax. Names retain their original spelling and source byte spans.

Parsing does not establish binding or types. For example, an unbound type-word
natural in a comparison or static argument can now reach a later resolution
error. Finite-profile static-Nat syntax can similarly reach its unsupported
profile diagnostic. No invariance of every invalid-input parse diagnostic is
claimed, and no finite execution capability or accepted IR evidence is added.

## Performed checks

- Six new common-parser tests cover retained binder spans/type structure,
  zero and small natural values, all six comparisons, fold indices/bounds,
  imported specialization arguments, operation dimensions/repetition counts,
  unbound-name rejection, and unchanged runtime/global/operation-binder guards.
- All twenty existing parser tests pass.
- All four original ignored Python sized-dialect comparisons pass, including
  the unchanged failing test, 400 existing bounded mutation comparisons, and
  the existing small corpus comparisons.

Command records preserve stdout, stderr, arguments, timing and exit status.
The isolated baseline failure has exit 101; the fixed focused/parser/Python
commands all have exit 0. The captured integration outputs contain two existing
dead-code warnings in the concurrently developed lexical-ID module. They are
not suppressed or reported as warning-free results.

`baseline-source-identities.json` records the isolated `git archive` input
identities and its observed library identity. `parser.before.rs.txt` and
`lexer.before.rs.txt` preserve the actual baseline source bytes. The baseline
diagnostic executable was compiled by the recorded `rustc` command against
that freshly built isolated library; its build and run are separate records.
`current-source-identities.json` records actual current Rust/Python/source inputs
and checks that this inventory and all its file hashes are identical before and
after the three successful commands. Its dirty working tree is explicit.

These records describe a parser repair and bounded tests, not source-preservation
proof, full hosted CI, a release, or a constitutional guarantee admission.
No new maximum-size case was generated.

To replay the successful checks from the repository root:

```sh
cargo test --offline --lib frontend::parser::tests -- --nocapture
cargo test --offline --test parser
cargo test --offline --test sized_review_dialects python_ -- --ignored --nocapture
```
