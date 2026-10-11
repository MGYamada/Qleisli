# Ordinary type surface: bounded pre-implementation study

Status: **read-only implementation preparation**, not an adopted implementation
contract, source acceptance change, guarantee admission or Issue closure.
The parent task authorized this fixture path only. Production Rust, Lean,
existing source consumers and GitHub Issues were not edited for this study.

## Actual observations

The six [Issue snapshots](issues) were read from GitHub (`gh issue view` with
`number,title,body,updatedAt,state`) before writing these sources. The relevant
selected contract is in the current type-model Reference: one ordinary finite
universe, explicit Q ownership, 0/1 Bit literals, exact tree equality and no
implicit preparation, observation or coherence. General Basis polymorphism is
not assumed here.

[First session](initial-study/session.json) preserves 34 desired/legacy/control
sources and their hashes **before** execution. The first observer used a function
named `main`; the finite checker applies executable entry policy to that name,
so even a valid ordinary library identity reported `invalid_entry`. Those
sources and diagnostics remain untouched. The [separate library follow-up](library-study/session.json)
changes only `fn main` to `fn f`, with sized entry explicitly selected as
`main::f`. It exposes the intended body/type checks without disguising the
initial authoring error. There were 68 observer processes; every process exited
zero, including diagnostic rejections. All source and observer identities were
rechecked after execution. See [stage counts](summary.json), exact per-case
stdout/stderr and `observations.json` in each session.

| Small library example | Finite profile now | Sized profile now |
| --- | --- | --- |
| `CBit -> CBit` identity | Checks | Generic check and elaboration pass; lowering rejects classical entry values |
| `Bit -> Bit` identity | Rejects ordinary Bit | Rejects unsupported runtime type |
| `CBits<2> -> CBits<2>` or copying that value | Unsupported register type | Generic check/elaboration pass; lowering rejects classical entry values |
| `Bits<2> -> Bits<2>` | Unsupported register type | Rejects unsupported runtime type |
| `Unit -> Unit` identity | Checks | Rejects unsupported runtime type |
| Legacy `() -> ()` identity | Rejects empty tuple type; suggests Unit | Checks, elaborates and emits an 835-byte untrusted pure proposal |
| Ordinary `0` / `1` | Common parser rejects | Same common parse rejection |
| Legacy ordinary `false` and Boolean `if` | Checks | Rejects unsupported runtime expression |
| `measure_z: Q<Bit> -> CBit` | Checks | Checks/elaborates; selected observe root requires a packed CBits result |
| Existing one-bit packed readout to `CBits<1>` | No finite `std::classical` module | Checks, elaborates and emits a 1748-byte untrusted instrument proposal |
| Same readout with `Bits<1>` | Same finite import boundary | Rejects unsupported runtime type |
| Return Q as ordinary, or ordinary as Q, using old names | Type mismatch | Type mismatch |
| Use runtime word `n` in `Q<Bits<n>>` | Register profile rejects first | `unknown natural name n` |
| Duplicate/drop `Q<Unit>` | Ownership rejection | Unsupported Q basis; no Q<Unit> support assumed |
| Duplicate `Q<Bit>` | Ownership rejection | Ownership rejection |
| `Q<Bits<1>>` returned as `Q<Bit>` | Unsupported Bits profile | Exact-type mismatch despite equal width |
| Ordinary `CBits<0>` returned as `()` | Unsupported Bits profile | Exact-type mismatch |
| Call a `basis fn` from ordinary runtime code | Explicit staging rejection | Basis declaration outside sized profile |

The proposal byte counts record successful **untrusted lowering**, not native
acceptance. No hierarchy checker or simulator was invoked by this observer.
The source checker may perform its existing finite checks; this study does not
infer a general source-preservation result from them. All examples are bounded
by two declared quantum bits and small finite types.

## Current implementation dependencies

- `src/frontend/types.rs`: `Type<N>` already has Unit, Bit, Bits, Q and ordered
  Tuple. Exact comparison and recursive linearity are shared. `Stage` records
  evaluation category; it is not a second value universe.
- `ast.rs` / `parser.rs`: source types still have CBit/CBits variants. Ordinary
  expressions have `CBit(bool)` parsed from true/false; basis expressions have
  `Bit(bool)` parsed from 0/1. The parser and lexical resolution are shared by
  both consumers, so the cutover belongs here once, not in two token adapters.
- `compile/mod.rs::ty`: finite stage mapping accepts Bit only in Basis and CBit
  only in Runtime. `lower/value.rs::Value::Classical` already maps to the same
  internal Bit. Existing ClassicalConst/Not/And/Xor/Branch IR operations can
  retain their behavior after canonical spelling changes.
- `compile/profile.rs`: Bits and static naturals remain explicit unsupported
  finite-profile cases. Finite QIRF has no Bits atom; a rename must not replace
  Bits<1> by Bit or Bits<0> by Unit to evade this boundary.
- `sized/parser.rs`: a projection of the common AST, currently retaining another
  private runtime Type enum and translating value `()` to empty Tuple. Its
  supported quantum bases are only Bit and Bits. It admits neither ordinary
  Unit nor runtime literal/Boolean/ordinary-if expressions.
- `sized/check.rs` and `elaborate.rs`: both consume the shared Type and use lexical
  BinderKeys; classical values already copy/drop and quantum values move.
  `SourceValue` distinguishes identity from source type. Public SourceType
  accessors currently report legacy cbit/cbits and panic on unreachable Unit.
- `sized/lower.rs::{leaves,check_profile}` and `lower/preservation.rs::atoms`:
  only Tuple is structurally traversed. Unit needs an explicit zero-value-port
  case, not a generic width-zero erasure that could discard Q<Bits<0>>. Current
  lowerer restrictions on classical entry values, classical unitary results,
  and packed observe results are real and must remain explicit.

## Proposed smallest next implementation contract

Perform one **canonical ordinary type/literal cutover over the existing
executable profiles**, without implementing a second classical evaluator or
pretending the backend profiles have equal expressive power.

1. Add one shared source-type elaboration/classification function over the
   common AST. It creates `Type<N>` for Unit/Bit/Bits/Q/Tuple, parameterized only
   by the existing bounded size resolver and diagnostic context. Reject Q in a
   Q basis, preserve every constructor/tuple edge, and keep profile support
   checks separate. Both finite signatures and sized projected signatures must
   consume this function. Prefer storing the common tree with projected natural
   expressions in sized AST over extending its parallel CBit/CBits Type enum.
2. The common parser recognizes 0/1 as the ordinary Bit literal node; a single
   literal recognizer serves ordinary and basis expression parsing. A numeral
   in explicit Nat syntax remains Nat. Remove active CBit/CBits type forms and
   true/false literal forms with clear migration rejections, not aliases. Remove
   `()` in type position in favor of Unit; value `()` remains valid. These are
   one grammar changes, followed by one explicit active-source migration.
3. Reuse the finite classical value/IR paths and sized existing classical
   value paths. Add genuine ordinary Unit to the sized type and value projection,
   checking and elaboration. Its common type is Unit, not Tuple([]) or Bits<0>.
   Give its public view a documented Unit case and no quantum owner identity;
   ordinary Unit may be copied/dropped. Lower an ordinary Unit value to no value
   ports while retaining the exact source interface and every computation step.
   Update both actual lowerer and source-event validator consistently. Never
   apply this rule to any Q owner, even when its width is zero.
4. Keep runtime Boolean/literal source classification common, but do not invent
   a sized Boolean StepKind or another evaluator merely for this cutover.
   Sized operations outside the existing supported profile report a precise
   unsupported-lowering/profile diagnostic after common syntax classification.
   Finite Bits, sized Q<Unit>/general product bases, runtime classical entry
   lowering, general Basis polymorphism and automatic basis-function runtime
   reuse keep their existing explicit obligations; this unit does not claim
   they are implemented or defer their parent Issues wholesale.

The maintainer should explicitly choose the public SourceType accessor migration
in the unit contract. A minimal consistent choice is `kind()` returning the
basis leaf name `bit`/`bits` for both ordinary and quantum leaves, with
`is_quantum()` retaining the ownership distinction; Unit becomes `unit` with
width zero and no fields. Then update all string-based lowerer tests to combine
leaf kind with ownership. Alternatively, a constructor-level API can expose Q
and its basis separately, but that is a larger API change. Either choice needs
new public accessor regressions; do not silently retain misleading source-level
C names or change `is_quantum` semantics. Native classical port tags remain
port classifications and do not require an IR/schema rename.

This is an ordinary implementation decision within the selected Reference.
No new Guardian interpretation is needed. It does not complete #22/#27/#43/#44:
opaque type parameters, generic checking convergence and explicit pure Unit
introduction/elimination remain separate unimplemented obligations. No pure
`Q<Unit> -> Unit` map is introduced by renaming ordinary Unit.

## Migration footprint and acceptance before merge

[Candidate inventory](migration-candidates.json) contains tracked-file text
matches, not a blanket replacement list. C-prefixed types or legacy literal
words occur in 1 stdlib file, 27 example files, 97 active corpus files and 70
corpus counterexamples. It also finds 19 production Rust files, 50 Rust test or
client files and 11 Python scripts/clients with C-prefixed names. Comments,
expected diagnostics and native port classifications need separate treatment.
248 corpus authoring-history files and 227 fixture candidates must be classified
by their consuming harness; they must not be rewritten just because they match.
Untracked new integration fixtures are outside this tracked-file snapshot and
must be added to the final migration inventory before the actual cutover.

Required validation is concrete:

- Check every declaration, including unused siblings and zero-iteration bodies;
  retain lexical shadowing, moved-name reservation and actual dynamic owner IDs.
- Positive ordinary copy/drop/Boolean/call/branch cases use Bit, with zero/one
  literals. Negative Q-to-ordinary and ordinary-to-Q assignments, guards and
  expected returns must reject without hidden preparation/measurement.
- Unit differs from Bits<0>; Bit differs from Bits<1>; tuple trees and Q-versus-
  tuple-of-Q remain exact. Test both symbolic and closed size substitutions.
- Compare old finite Classical* operations and existing sized one-bit readout
  proposals after explicit migration. For source-bearing evidence, record changed
  source snapshots and compare all unchanged semantic/structural fields rather
  than assert full artifact identity. Bind new handles to their actual new bytes.
- Test actual Unit value lowering and source-event validation together. Retain
  existing Q<Unit>/Q<Bits<0>> loss, duplication, phase and controlled-scalar tests;
  do not create a new quantum Unit acceptance path in the sized adapter.
- Preserve historical source/session bytes and fixed old native artifacts. Give
  affected active fixture harnesses named current translations and explicit
  obsolete-spelling rejections, following the preceding predicate-domain unit.
- Run relevant parser/docs, type/accessor, source ownership/judgment, finite
  semantic/contract/CLI, sized generic/elaboration/readout/preservation, generated
  Rust/Python-client and bounded corpus tests. Latest and real Rust1.85 Clippy,
  source inventory, docs/book links and current native gates remain required.
  No maximum-sized quantum case is needed to establish this surface cutover.

The saved preparation/observation scripts use the original local paths and are
session records, not production CI entrypoints. [Observer build summary](observer-builds.json)
is labelled post-execution; actual per-case streams were captured directly.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
