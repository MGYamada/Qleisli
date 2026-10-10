# Source text and lexical boundary

These rules govern the current `0.3.0-alpha` source scanner and parser in
constitutional edition 2026. Both finite project loading and sized explicit
module loading use one scanner, token stream, parser and source `Module`/`Span`
representation under the
[common frontend decision](https://github.com/MGYamada/Qleisli/issues/32).
A single mandatory judgment checks each complete original AST before finite or
selected concrete eligibility. Declaration and lexical identities, types,
static premises, owner/access rules, body dependencies and principal effects
come from the same original-source checker in `src/frontend/check.rs` and
`src/frontend/check/`. Every declaration is checked, including private and
unused siblings, both arms and zero-iteration bodies. Parsing alone confers
neither source approval nor native verification evidence.

The [elaboration whitelist](elaboration.md) specifies permitted surface-to-core
expansion, evaluation order, owners, phase, original locations and remaining
independent checking obligations. It does not grant an unsupported projection.

Runtime wildcard, duplicate-name and exact tuple/Unit rules use the common
pattern traversal. Ordered static kinds and runtime parameter names retain
original declaration ordinals and binder identities. A static kind may refer
only to preceding static parameters; complete declaration registration does
not make a forward static kind available. Valid forward and backward sibling
references resolve against the complete registered declaration table. Quantum
values have fresh
dynamic owner identities distinct from these lexical keys. Arguments and RHS
expressions evaluate completely, once, from left to right before binding.

The raw AST also retains bare lexical assignment and a `let mut name = ...`
marker solely for typed refusal. Neither form can occur in a successfully
checked program or be lowered to replacement. Assignment inspects the resolved
destination's current type before checking its RHS; even a consuming RHS does
not authorize replacing a quantum-containing place. A mutable binding checks
its initializer's type to distinguish quantum ownership from unsupported
ordinary mutability. Both refusals retain original byte locations. `mut` is
contextual: `let mut = 0; mut` remains an ordinary immutable binding and use.
General field/index assignment syntax and ordinary reassignment are unsupported;
these diagnostic forms grant neither. See the
[assignment and mutability boundary](rust-boundary.md).

One private source collection retains complete original bytes, common AST and
provenance. Filesystem entries retain their selected path; in-memory entries
carry no invented file or manifest. Both loaders add the fixed registry's five
ordinary source modules and validate its edition-2026 manifest. Both loaders
apply their byte policies to bundled bytes before copying or parsing;
placement under `std::` supplies no checking exemption. The selected loader
also reserves all five bundled module slots. It accepts 1 through 59 supplied
modules: the five bundles count toward its
64-module ceiling and its 1 MiB aggregate byte limit. Its 64 KiB/module limit
also applies. Finite bounded and explicit legacy byte-loading policies remain
separate; this unit does not make an unbounded byte loader bounded.

The finite loader consumes the collection into the existing mutable `Project`
compatibility view. Finite checking, compilation and checked-effect operations
reconstruct facts from that view's current original ASTs; no stale parallel
collection or approval is reused after caller mutation. Source-only
documentation and rendering do not acquire semantic checking from this rule.
The selected path retains its immutable originals
and records a concrete projection result for each declaration only after the
complete common judgment. A located unsupported projection is an eligibility
failure when that definition is requested, not a skipped original body or
fallback source approval. Retirement of that lowering projection, canonical
generic std APIs and source-preservation proofs remain separate work in
[#32](https://github.com/MGYamada/Qleisli/issues/32) and
[#317](https://github.com/MGYamada/Qleisli/issues/317).

## One structured quantum result boundary

Verified quantum-core functions are expression-oriented. A body has one
structured result boundary: its final block expression. Every runtime branch
must retain and merge the complete required owner frame and exact result tree.
Both arms are checked even when one is statically unreachable. No early exit
can discard, release, reset or uncompute a live owner implicitly.

Early `return q`, residual propagation `q?`, runtime `panic!`, `assert!` and
`unreachable!` macro edges, unwinding, hidden abort and partial quantum
functions are not admitted. This applies to Unitary, Isometry and Observe bodies;
an observing effect does not authorize a hidden exit. Syntax refusals explain
the final-expression alternative and retain the original token's byte span.
Use explicit ordinary branches, admitted coherent control and finite folds
under their own owner/effect rules; this chapter grants no unsupported
`qmatch`, `qreturn` or `qtry` form.

For example, `unitary fn keep(q:Q<Bit>)->Q<Bit>{q}` has the structured result;
replacing its body with `{return q}` is invalid. A final `if` whose arm returns
Unit while the other returns `Q<Bit>` is also invalid; refusal inserts no
cleanup. Ordinary identifier names retain normal resolution. A variable or
checked ordinary function named `return`, or a function named `panic`, is not
a return/abort primitive; an ordinary `return(q)` call keeps normal call rules.
Comments containing these spellings do not create executable edges.

A future host orchestration language may specify `Result`, residual exits,
assertions or process failure separately. No such host failure semantics is
imported into the present core. Ordinary error values, if separately admitted
as data, would not themselves imply propagation or unwinding. The runtime
checker/transport's fail-closed refusal is likewise not a source-level exit.

## Checking failures and quantum execution

Within the declared finite model, a supported verified quantum-core operation
has no implicit exceptional execution edge. This applies to Unitary, Isometry and
Observe: measurement supplies its specified ordinary outcome and instrument,
not permission to panic, unwind, abort, partially return or abandon an owner.
This totality requirement is the adopted failure contract; it is not a claim
that every source form or target has a completed production Soundness proof.

Invalid sizes, type trees, static indices, access/capability requirements and
required constraints reject during checking or specialization. The current
`take_bit[n,k]` requires an established `k < n`; it does not compile an unknown
index into a quantum runtime bounds trap. Checked Nat arithmetic cannot wrap
or defer overflow to a quantum exception. Bounded elaboration, unsupported
profiles and unproved obligations also reject before an executable handle is
issued for that proposal. See [static checking](static-language.md).

An explicit ordinary result such as a Bit may select an ordinary `if`, but
both arms must satisfy the complete required owner frame, exact type tree and
effect rules. A recoverable alternative returns its declared data and owners
through the normal structured boundary. It must not implement a hidden exit,
implicit cleanup or a success-only path. For example, an operation may return
`(flag, q)` or `(flag, x(q))` in its two arms when their declared interfaces
agree; omitting `q` in one arm is invalid. The unchanged caller frame, including
correlated owners and zero-width quantum owners, still participates in the
branch merge. An ordinary condition does not establish separability.

The finite project path supports those runtime ordinary branches. The current
selected specialization projection can reject such a runtime expression as
unsupported during preparation; it must not turn it into an unchecked body or
a runtime failure path. This profile restriction is separate from the language
contract and the shared original-body ownership/effect judgment.

Source failure handling cannot reset/discard workspace, discharge a clean or
dirty restoration obligation, erase exact phase or owner ordering, or shorten
an access lifetime to omit required work. The absence of an unwind construct
does not prove pending access, restoration, target or quantitative resource
contracts. Their implementations must obey this rule when admitted.

Operating-system failure, verifier/transport failure, backend crash and device
loss are external faults, outside the quantum-core operational theorem unless
an explicit future target contract models them. They provide no source escape
hatch or owner-disposal semantics. Missing, incompatible, timed-out or malformed
native checking rejects without an accepted handle or fallback. Such a refusal
is a failed attempt to check an artifact, not an executed quantum branch.

Reference simulation can separately refuse its host execution/component/space
budgets or report a numerical/internal-consistency error. No result distribution
is thereby certified as the successful program result. These host limits are
not static quantum resource certificates, and reporting an error is not proof
of physical state recovery or clean/dirty restoration after an external fault.
The current Rust simulator and native IO retain their disclosed correspondence
assumptions; the core failure contract does not prove host panic freedom.

## Ordinary function effects and assertions

An ordinary body-bearing function may use `fn`, `unitary fn`, `isometry fn` or
`observe fn`. Its principal quantum effect is derived from the completely
checked body and checked callees at fixed ordinary inputs. The order is
`Unitary <= Isometry <= Observe`; composition takes the least upper bound. Copying
an ordinary Bit does not copy a quantum owner or add a quantum effect.

An optional prefix is a checked upper-bound assertion, never an inference
seed. A body inferred as Observe cannot assert Unitary or Isometry. A body inferred
as Unitary may carry an Isometry or Observe assertion, but its principal effect
remains Unitary for calls, provider eligibility and checked interface metadata.
Type, ownership, access and termination checks still apply independently;
an annotation cannot supply a missing check or arbitrary mathematical Meaning.

The selected vocabulary in [#57](https://github.com/MGYamada/Qleisli/issues/57)
is **isometry**: `V†V = I_input`, without a claim of surjectivity or executable
inverse/control access. Zero-state preparation is an isometry but not a unitary
between its different input/output dimensions. A unitary additionally satisfies
`VV† = I_output`. In categorical terminology these are a dagger-monomorphism
and a dagger-isomorphism, respectively.

The old source prefix `iso` is retired in 0.3.0. Replace `iso fn` with
`isometry fn`; the old word produces a lexical migration error located at its
original token before native checking. It remains reserved for that error,
not an accepted alias or an ordinary identifier. Comments and longer ordinary
identifiers such as `isotope` and `iso_value` are unaffected.

The canonical names are:

| Surface | Canonical spelling |
| --- | --- |
| Source effect assertion | `isometry fn` |
| Rust effect | `qleisli::ir::Effect::Isometry` |
| Rust function and token kinds | `frontend::ast::FnKind::Isometry`, `frontend::lexer::TokenKind::Isometry` |
| Lean Raw effect | `QleisliKernel.Semantics.Raw.Effect.isometry` |
| Lean hierarchy effect | `QleisliKernel.Hierarchical.Artifact.Effect.isometry` |
| Lean retained bounded QFT graph effect | `QleisliKernel.QftGraph.Effect.isometry` |

Rust callers migrate `Effect::Iso`, `FnKind::Iso` and `TokenKind::Iso` to their
`Isometry` variants; there is no Rust compatibility alias. Body-effect
diagnostics also use `Isometry`.

The three Lean names are reducible aliases for their existing `Effect.iso`
constructors. They provide the canonical spelling for new Lean expressions
without changing constructor identity, generated recursors, existing `.iso`
case names or derived `Repr` output. Historical formal statements and callers
using the constructor retain that compatibility. The QFT graph alias changes
only an existing public type's vocabulary; it adds no QFT implementation.

Versioned JSON/QIRF effect tags, the checked source graph's effect tag and
native hierarchy adapters retain `"iso"`; the binary hierarchy effect tag
remains `1`. These explicit transport exceptions neither introduce a second
source effect nor grant inverse/control access.

`QleisliKernel.Raw.State.iso` is an internal allocation-tracking Boolean, not
an effect assertion or evidence of the isometry law. Local proof witnesses
named `iso` likewise are not public effect vocabulary. These implementation
names and the compatibility constructors remain unchanged; naming alone
establishes no semantic property or constitutional guarantee.

Both arms and the body of a zero-iteration static fold participate in common
checking and effect inference. A decreasing runtime self-call uses the least
effect solution only after the actual decrease check; mutual dependencies
reject. An invalid or unresolved source body yields no checked effect fact.
A valid source body may retain its principal effect while its requested
concrete projection or lowering remains unsupported. These source facts are
not accepted IR handles or a source-preservation proof; finite and selected
concrete lowering and native checks remain distinct.

**`"externally unitary"` is not supported.** The current compositional rules
retain internal observation, reset and discard as Observe. Even if a separate
argument claims the induced public channel is unitary, an ordinary annotation
cannot replace those rules with an external certificate. A contradictory
annotation is therefore an effect/semantic error. Its diagnostic states the
inferred and asserted effects and explains this unsupported semantic boundary,
without a GitHub Issue reference. This does not prove that the public channel
is mathematically non-unitary; it means the proposed external justification
is unavailable. Externally isometric justification is likewise unsupported.

The Rust interface exposes immutable `ProjectEffects` from
`project_effects_with_kernel` for finite projects, and `ParsedProgram` facts
for sized source. `function_effect` separates the principal effect from an
optional checked assertion. Their `documentation` methods render those facts
from the retained source bytes; changing a source file afterward cannot rebind
the report. Concrete finite declarations still undergo native verification;
generic facts remain conditional on their checked source premises. The
source-only `doc` command and `render_markdown` keep their explicit lack of
semantic checking and do not manufacture inferred facts.

An operation provider selected by the host has the same principal-Unitarity
requirement as a source-selected provider. An Observe or Isometry body rejects with
an effect/semantic error and the unsupported external-justification explanation.
A principal-Unitary body with a broader assertion remains eligible, subject to
its separate type, ownership, access and native checks. A provider input/output
shape mismatch remains a type error; it is not external effect justification.

## Total classical declarations

Provisional `static fn` declarations instead return static Nat values through
the [bounded helper rules](static-language.md#provisional-bounded-nat-helpers).
They have no runtime interface, effect or accepted-handle authority.

`classical fn f(pattern: T, ...) -> U { expression }` declares a total, pure
finite function on ordinary values. Its body is one restricted label expression:
names, `()`, `0`/`1`, ordered products, eager `not`/`and`/`xor`, and acyclic calls
to other classical functions. It has no runtime statements, observation or
quantum capture. Parameter/result trees and argument-list arity remain exact;
noninjective functions are permitted.

The same checked body may be called in ordinary runtime expressions, existing
Meaning/predicate construction and coherent `basis` expressions. Runtime
arguments evaluate once, left to right, before parameter binding. Their effects
and owner consumption remain in the caller, including when an ordinary result
is ignored. An already measured Bit is ordinary data; a live `Q<T>` cannot be
passed as `T` without explicit observation. For example:

```qli
use std::observe::measure_z;
classical fn flip(b: Bit) -> Bit { not b }
fn invert(q: Q<Bit>) -> Q<Bit> { basis q as b { flip(b) } }
fn read_flipped(q: Q<Bit>) -> Bit { flip(measure_z(q)) }
```

Coherent lifting independently requires injectivity of the complete map;
computed predicates retain their separate exact cleanup contracts. A classical
declaration or its name grants no inverse/control access, Meaning evidence or
native acceptance. Meaning declarations remain descriptions, not runtime
callees. Supported Unit/Bit/product runtime calls lower their original
expression nodes through ordinary operations in both concrete consumers;
ordinary execution does not evaluate a precomputed truth table. Existing Bits,
selected coherent-lift and target-profile limitations remain separate.

The retired declaration spelling `basis fn` rejects with a located migration
diagnostic directing authors to `classical fn`; there is no compatibility alias.
The coherent expression `basis q as pattern { expression }` and static
`A: Basis` parameters keep their existing meanings. Historical first sources
and validation records retain their original spelling; current replay selects
explicitly recorded derivatives.

## Bytes, characters and positions

Source is UTF-8. Every source span is a half-open byte interval in the original
input. Source loading, scanning and diagnostics must not normalize those bytes.
LF and CRLF are accepted line endings. Ordinary whitespace is ASCII space or
tab; bare CR, vertical tab, form feed and non-ASCII whitespace reject. Bidi
control characters and other control characters reject, including in comments.
A rejected Unicode scalar's span covers its complete UTF-8 encoding.

Identifiers use ASCII letters or underscore initially, followed by ASCII
letters, digits or underscore. Comment prose may contain other ordinary Unicode
characters. This does not admit Unicode identifiers or alternate whitespace.

The existing finite keywords are reserved in the common grammar, including
identifier positions formerly treated contextually by the sized parser:
`use`, `meaning`, `static`, `Op`, `requires`, `Apply`, `Adjoint`, `Controlled`,
`permutation_by`, `phase_by`, `checked_op`, `bind_op`, `inverse_op`, `then_op`, `tensor_op`,
`controlled_op`, `repeat_op`, `conjugate_op`, `pub`, `classical`, `basis`, `isometry`, `iso`, `unitary`,
`observe`, `fn`, `let`, `if`, `else`, `qfor`, `do`, `pure`, `with_computed`,
`apply_contract`, `adjoint`, `repeat_static`, `qif`, `true`, `false`, `not`,
`xor`, `and`, `Unit`, `Bit`, `CBit` and `Q`. The existing import exception admits
`basis`, `observe` and `classical` immediately after `std::` as module names.

`iso` remains reserved solely for the effect-prefix migration error described
above; it does not introduce an accepted declaration or identifier.

`do` and `pure` remain reserved tokens solely to reject the removed coherent
notation with a migration diagnostic. They introduce no accepted expression,
alias, monadic operation or state preparation. `classical fn` declares total
ordinary computations; the distinct `basis` expression is specified in
[Coherent basis maps](coherent-basis.md).

`checked_op` is the reserved exact-meaning constructor described in
[Checked operations](checked-operations.md). The retired `bind_op` spelling
remains reserved solely for a located migration error; it is never an alias.
Existing declarations or finite filesystem module names using `checked_op`
as an ordinary identifier must be renamed. Occurrences in comments and longer
identifiers remain unaffected. The lexer scans the complete file before
parsing, so a later retired token can precede an earlier grammar error. Token
capacity rejection keeps precedence over that token's migration diagnostic.
Selected explicit module keys retain their separate existing validation rules;
this change does not unify them with finite filesystem module names.

`Applicable`, `Adjointable` and `Controllable` are contextual predicates in
`requires` clauses, followed by an operation parameter in parentheses. They
remain ordinary identifiers elsewhere. The old `Apply`, `Adjoint` and
`Controlled` tokens and `inverse_op`/`controlled_op` remain reserved for located
migration errors. `adjoint(U)` is the current static description and
`adjoint(U)(q)` its application; the two-argument form is retired.
`controlled` and `inverse` retain ordinary single-stage name resolution.

`Bits`, `CBits` and `Nat` are contextual type/kind names and remain valid names
in identifier positions. `as` is contextual: it separates the quantum input
expression and pattern in `basis input as pattern { expression }`, and remains
an ordinary identifier elsewhere. Retained tokens for `CBit`, `true` and `false` permit
targeted rejection of their old type/literal uses; they do not keep those uses
accepted. Type-position `CBits<n>` likewise rejects. The replacement types and
literals are `Bit`, `Bits<n>` and `0`/`1`.
`qfor` is reserved and starts an explicitly static quantum-owner fold.
`for static` starts an ordinary-only fold. The `for` word, the `in`/`carry` parts of either header,
and `yield` at the start of a fold tail recognize their existing sized roles.
Those words remain identifiers in other positions. `controlled(op)(args)` is
the existing controlled-application construct; `controlled(q)` remains an
ordinary call to an identifier. Neither spelling guesses a resolved provider
category or grants control access.

Numeral tokens retain their decimal spelling. The scanner does not convert
them to a machine integer, infer a Bit/Nat category or grant a static value.
The common natural-expression parser rejects leading zeroes except `0` and
literals exceeding `i128`. It retains addition/subtraction, multiplication and
parentheses with source spans; multiplication binds more tightly than addition
or subtraction. Existing static checks still require nonnegative, bounded and
supported expressions. A power repetition count has the existing `2^e` form,
with compound exponents parenthesized; this is not general exponentiation in
the natural-expression language. The finite lowering profile still requires
literal `repeat_op` counts in 0 through 4096. Ordinary and basis Bit expressions
share the `0`/`1` literal recognizer; other numerals are not Bit values. This
does not change static-Nat literals or infer a quantum owner from a numeral.

## Comments and documentation

`//` starts a line comment. `/* ... */` is a nested block comment. Unclosed
block comments reject. Character validation applies equally to code, ordinary
comments and documentation comments; comments cannot hide forbidden controls.

`//!` and `/*! ... */` are inner documentation comments. `///` and
`/** ... */` are outer documentation comments, except that `////`, `/***` and
`/**/` begin ordinary comments. Documentation text may normalize CRLF to LF in
its extracted metadata; source offsets continue to refer to the original bytes.

Classification and placement are shared. Outer docs must precede a function
or use item; inner docs belong to the module or the initial documentation area
of a function body. The common declaration attachment check rejects misplaced
docs before either profile checks source. Metadata remains descriptive and is
available through `parse_documented_module`; ordinary module loading may retain
only the syntax and original source. No profile may silently ignore invalid
placement.

## Punctuation and bounded scanning

The physical scanner recognizes individual punctuation marks. The common lexer
forms composite tokens only from immediately adjacent marks: whitespace and
comments never join them. For example, `::` is distinct from
`: /* comment */ :`. The token stream includes the existing sized arithmetic
and comparison marks; `==>` is `==` followed by `>`, not a valid alternative
arrow. The scanner/parser never retries another grammar or chooses a backend
based on the input.

The sized entry retains its limit of 10,000 non-EOF tokens and block-comment
depth 64. Comments and EOF do not consume the token allowance; the next excess
token is rejected before allocating its owned text. The finite entry retains
its existing iterative comment processing without a newly imposed depth limit.
Source-byte and aggregate project limits remain separate entry-point policies.
The common parser applies its 64-level recursive syntax and runtime/type tree
bounds, 64-field tuple bound and 128-depth natural-expression bound. This counts
the quantum wrapper and its basis parse in the same recursion budget; certain
deep sized natural types therefore reach the common limit one level earlier
than the removed parser. These are engineering limits, not the constitutional
quantitative Resource Safety theorem.

All declarations remain in the common AST and undergo the original-source
judgment before either concrete profile. Source-semantic errors therefore
precede an unsupported concrete form, including in unused declarations. Empty
parentheses in a type position reject with a diagnostic directing the author
to `Unit`; the value and pattern remain `()`. Existing empty pattern/block,
empty `yield`, empty specialization brackets and parameter trailing-comma
spellings remain represented by the shared syntax. Parsing or source checking
adds no emitter support or new `Op<A,B>` form.

The common judgment has a 1,000,000-work engineering budget. It charges visits,
allocated/copied type and lexical cells, normalized arithmetic and solver work
before the corresponding operation. Per-value type size is bounded by 4096
cells and depth 64. The same judgment takes an additional 16,384 retained-scope
cell limit on the selected path; finite retains its existing aggregate/type
and snapshot capacities without that extra selected limit. Concrete
elaboration, evidence, native work and loader/parser limits are separate.
Exhaustion rejects; it is not a discharged quantitative Resource Safety
certificate or evidence that the program's mathematical obligation is false.

Ordinary and classical function parameters use the existing name, wildcard and
tuple pattern syntax. The colon annotates the entire parameter pattern, and
the source argument list keeps that parameter as one argument. For example,
`unitary fn first((a, _): (Bit, Bit)) -> Bit { a }` takes one ordinary pair.
Pattern checking preserves exact arity and nesting, rejects duplicate parameter
names and checks quantum ownership even in unused declarations. Tuple patterns
do not implicitly split a quantum register. Argument expressions retain their
evaluation order and effects before callee binding; a wildcard or Unit pattern
does not erase the computation that produced its argument.

## Declaration resolution and current profiles

An imported declaration retains its canonical module and declaration name.
Visibility is checked before use: a private declaration cannot be imported from
another module or selected as a host entry. A sized host-supplied provider is
checked from the entry module's context, including when the provider is unused.
Imports add no runtime action or verification privilege. A moved local binding
continues to shadow a declaration with the same name; failed local lookup does
not fall back to that declaration. Evidence retains the original source,
dependencies, canonical names and static bindings.

Both paths resolve imports against the complete registered declaration tables.
Unused import-only cycles are permitted because imports have no runtime action.
Every self-import is a declaration-name collision, including a private or
public declaration imported into its own module. Duplicate imports and clashes
with local declarations reject. Missing members, private members, collisions
and unknown sealed primitives point to the final path token; a missing module
points to the complete `use` span.

Same-module sibling calls may refer forward or backward and may use private
declarations. Cross-module imports and host-selected entries require public
visibility. Runtime calls, static providers, classical and Meaning dependencies
from every original body enter the checked graph. Mutual cycles reject. Only
an actual runtime self-call to the identical DefId with the checked Nat decrease
is permitted, including its directly transformed runtime form; a recursive
opaque provider, classical/Meaning cycle or failed decrease does not qualify.
Finite may subsequently refuse to materialize such a source definition under
its concrete profile. Names, effect fixed points and zero-count repetition
cannot stand for the required decrease proof.

Runtime parameter, let and fold-carry bindings cannot shadow an active static
Nat, Basis, Op or fold-index binder. Static formals may shadow global
declarations. A consumed quantum owner may be rebound after complete RHS
evaluation; hiding a live owner rejects, including a zero-axis owner or one
nested in a product. A static name used as a runtime value is a located type
error; reusing an actually consumed runtime owner remains an ownership error.
A resolved local value used as a callee is a wrong-category error, never a
retry through a same-named global declaration.

`src/frontend/resolve.rs` and `resolve/locals.rs` retain canonical declaration,
lexical-use and original-span associations. The common typed primitive catalog
has 27 fixed names; finite and selected concrete emitters still support their
own subsets. The five ordinary bundled modules undergo the same common
judgment as caller source. No ambient standard-library discovery, replacement
of reserved `std` modules or new alias/re-export syntax is admitted here.
Source facts, concrete capability and independent native acceptance remain
separate responsibilities. Remaining lowering and namespace integration is
tracked in [#32](https://github.com/MGYamada/Qleisli/issues/32),
[#41](https://github.com/MGYamada/Qleisli/issues/41) and
[#65](https://github.com/MGYamada/Qleisli/issues/65).

## Migration and evidence

The old sized scanner skipped bare CR/form feed and forbidden characters inside
comments. Those inputs now reject. Replace noncanonical whitespace with ordinary
space/tab or LF/CRLF and remove forbidden controls. VT already rejected before
this change; its diagnostic now comes from the shared character rule.

Remove legacy self-imports and use the module's declaration directly; ordinary
import-only cycles now need no source repair. Rename runtime binders that shadow
active static names. Earlier profile refusal may now be preceded by the actual
source type, owner, access or dependency error. Both paths charge all original
bodies and bundled sources, so an old symbolic input may reach the common work
capacity before an inner solver limit. Earlier sources and diagnostics remain
historical records; these migrations do not change edition 2026.

Reserved-word identifiers in old sized source must be renamed. Misplaced docs
must move to their module/declaration attachment boundary. Unclosed block
comments now use the common `unterminated block comment` diagnostic. The former
one-function restriction is removed: supported ordinary siblings share one
module, while mutual recursion remains rejected. Edition remains 2026 because
edition names the constitutional regime, while release compatibility records
these source changes.

`tests/fixtures/frontend_v030/shared-scanner/` in the
[repository](https://github.com/MGYamada/Qleisli) preserves the original byte
fixtures and actual old/new CLI diagnostics. The two successful small source
pairs emitted identical untrusted proposal hashes. The subsequent
`tests/fixtures/frontend_v030/common-parser/` packet preserves ten initial
source observations, independent review counterexamples, exact commands/results
and four small before/after proposals with identical bytes. It also records the
shared-depth edge above. These are bounded migration evidence, not a general
source-preservation proof, new formal guarantee or native acceptance claim.

`tests/fixtures/frontend_v030/shared-resolution/` retains the resolver's ten
original profile observations, 25 matching command results and five identical
small proposals, including distinct same-named providers and decreasing
self-recursion. Private Rust debug representations are not canonical names or
evidence formats; their printed fields change with the internal resolver.

`tests/fixtures/frontend_v030/lexical-resolution/` retains the subsequent shared
local/static binding comparisons. The `multi-declaration/` and
`sized-declarations-independent/` packets preserve original rejected siblings,
their declared acceptance/diagnostic changes, and independent small phase/axis
comparisons of split-module and same-module programs. Earlier failed sources
and results remain historical evidence. Existing single-declaration observations
and six small proposal byte sequences are unchanged by the sibling extension;
newly accepted source still undergoes its actual native check.

Both current finite `with_computed` forms now require the
[explicit predicate domain](type-model.md#predicate-domains-and-argument-lists).
Replace a legacy `p(a: A, b: B)` predicate with `p((a,b): (A,B))` for a
`Q<(A,B)>` register. For three or more parameters, write the register's exact
tree; the old fold was left-associated. A `Q<Unit>` predicate takes an explicit
Unit parameter. Ordinary calls retain their argument-list arity, so update any
ordinary callers or provide a separate unary wrapper. The
`tests/fixtures/frontend_v030/predicate-domain/` and
`predicate-domain-independent/` packets retain old diagnostics, explicit current
translations, small proposal comparisons and independent phase/reference
checks. Source-bearing artifact identities change when embedded source changes.

The former `do p <- q; pure e` expression is removed. Its explicit migration is
`basis q as p { e }`, preserving the input expression, complete pattern and
single basis expression. The braces delimit the restricted basis-expression
grammar, not an ordinary statement block. The migration does not join separate
owners, allow outer runtime captures, remove injectivity checking or prepare a
state. [Coherent basis maps](coherent-basis.md) specifies the semantics,
diagnostics and concrete-profile limits. Both finite and selected source use
this one parser; a profile cannot retain the retired notation as an alias.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
