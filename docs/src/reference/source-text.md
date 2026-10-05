# Source text and lexical boundary

These rules govern the current `0.3.0-alpha` source scanner and parser in
constitutional edition 2026. Both finite project loading and sized explicit
module loading use one scanner, token stream, parser and source `Module`/`Span`
representation under the
[common frontend decision](https://github.com/MGYamada/Qleisli/issues/32).
The sized checker consumes an explicit projection of that AST; it does not
parse source again. Declaration and lexical identities and source type
classification are shared. Static/owner/effect checking and lowering are not
yet fully unified. A parsed AST does not accept a program or confer native
verification evidence.

Runtime wildcard, duplicate-name and exact tuple/Unit shape judgments share
one binding traversal in finite lowering and sized generic checking. Values
and names retain their existing lexical and dynamic identities, eager argument
evaluation, accounting and located diagnostics. The sized checker borrows its
existing pattern projection. Ordered static-name insertion and runtime parameter
name scanning also share a private rule over the original common AST. The sized
caller uses its actual resolved declaration and source parameter ordinals, with
complete projection counts checked before pairing. Existing type/kind/access
stages, static-shadow policy, concrete elaboration and basis-pattern checking
remain separate. This bounded sharing does not establish complete common
checking or source preservation.

One private source collection retains each complete original text, common AST
and provenance together. Filesystem entries retain the selected source path;
in-memory entries carry no invented file or manifest. The finite loader consumes
that collection into the existing mutable `Project` compatibility view, with
no parallel cached collection or checked facts. The sized preparation retains
the immutable collection. Both adapters keep their existing complete declaration
checks, byte/parser policies and first-failure ordering: sized projection of a
module completes before parsing the next module. The fixed bundled registry
contains the current four ordinary sources and their manifest; it grants no
semantic authority and does not inject unsupported bundles into sized loading.
Complete common checking and canonical namespace migration remain required by
[#32](https://github.com/MGYamada/Qleisli/issues/32) and
[#317](https://github.com/MGYamada/Qleisli/issues/317).

## Ordinary function effects and assertions

An ordinary body-bearing function may use `fn`, `unitary fn`, `iso fn` or
`observe fn`. Its principal quantum effect is derived from the completely
checked body and checked callees at fixed ordinary inputs. The order is
`Unitary <= Iso <= Observe`; composition takes the least upper bound. Copying
an ordinary Bit does not copy a quantum owner or add a quantum effect.

An optional prefix is a checked upper-bound assertion, never an inference
seed. A body inferred as Observe cannot assert Unitary or Iso. A body inferred
as Unitary may carry an Iso or Observe assertion, but its principal effect
remains Unitary for calls, provider eligibility and checked interface metadata.
Type, ownership, access and termination checks still apply independently;
an annotation cannot supply a missing check or arbitrary mathematical Meaning.

Both arms of a supported branch and the body of a zero-iteration static fold
participate in checking and effect inference. Sized decreasing self-recursion
uses the least effect solution only after the existing decrease check; mutual
recursion remains unsupported. An unsupported or unresolved body publishes no
checked effect fact. These source checks are not accepted IR handles or a
source-preservation proof, and finite and sized lowering remain distinct.

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
requirement as a source-selected provider. An Observe or Iso body rejects with
an effect/semantic error and the unsupported external-justification explanation.
A principal-Unitary body with a broader assertion remains eligible, subject to
its separate type, ownership, access and native checks. A provider input/output
shape mismatch remains a type error; it is not external effect justification.

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
`permutation_by`, `phase_by`, `bind_op`, `inverse_op`, `then_op`, `tensor_op`,
`controlled_op`, `repeat_op`, `conjugate_op`, `pub`, `basis`, `iso`, `unitary`,
`observe`, `fn`, `let`, `if`, `else`, `do`, `pure`, `with_computed`,
`apply_contract`, `adjoint`, `repeat_static`, `qif`, `true`, `false`, `not`,
`xor`, `and`, `Unit`, `Bit`, `CBit` and `Q`. The existing import exception admits
`basis` and `observe` immediately after `std::` as module names.

`Bits`, `CBits` and `Nat` are contextual type/kind names and remain valid names
in identifier positions. Retained tokens for `CBit`, `true` and `false` permit
targeted rejection of their old type/literal uses; they do not keep those uses
accepted. Type-position `CBits<n>` likewise rejects. The replacement types and
literals are `Bit`, `Bits<n>` and `0`/`1`.
`for static`, the `in`/`carry` parts of that header,
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

All declarations remain in the common AST. The sized profile projects every
supported ordinary function in source order and checks each declaration,
including unused siblings, before preparation succeeds. Empty sized modules
remain unsupported. Empty parentheses in a type position reject with a
diagnostic directing the author to `Unit`; the value and pattern remain `()`.
Existing empty sized pattern/block,
empty `yield`, empty specialization brackets and parameter trailing-comma
spellings are represented by the shared syntax. Unsupported finite constructs
receive a located profile rejection; parsing a spelling does not add backend
support. This implementation step does not add `Op<A,B>`/Basis-generic features.

Ordinary and basis function parameters use the existing name, wildcard and
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

The current shared declaration resolver has the following profile boundaries:

| Condition | Finite project | Sized explicit module map |
| --- | --- | --- |
| Unused import cycle | Rejected | Permitted; actual call/provider cycles are still checked |
| Import of the module's own declaration | Rejected as a collision, or as private | Permitted for that same declaration, including private visibility |
| Declaration recursion | Rejected | Only the existing checked decreasing self-call is permitted |
| Multiple declarations in a module | Checked, including unused declarations | Checked, including unused declarations |

Same-module sibling calls may refer forward or backward and may use private
declarations. Every declaration has its own lexical table; its identity is
distinct from its source position and from equal names in other modules.
Sized self-recursion must call the identical declaration and satisfy the
existing natural-parameter decrease check. Mutual call/provider cycles remain
rejected. Checking all generic bodies includes static branches and zero-count
fold bodies; it does not certify every concrete specialization or bypass the
independent native checks on actual proposals.

Existing module-name and primitive-set restrictions remain profile-specific.
The sized API loads only the supplied module map and its specified primitives;
it does not implicitly discover bundled source modules. Common declaration
and lexical identities are shared, while the finite and sized type, effect and
ownership judgments still require convergence. This does not grant the final
set of 0.3.0 constructs. The implementation contract and remaining convergence are tracked
in [#32](https://github.com/MGYamada/Qleisli/issues/32),
[#41](https://github.com/MGYamada/Qleisli/issues/41) and
[#65](https://github.com/MGYamada/Qleisli/issues/65).

## Migration and evidence

The old sized scanner skipped bare CR/form feed and forbidden characters inside
comments. Those inputs now reject. Replace noncanonical whitespace with ordinary
space/tab or LF/CRLF and remove forbidden controls. VT already rejected before
this change; its diagnostic now comes from the shared character rule.

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

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
