# Source text and lexical boundary

The **source text** of a Qleisli program is the UTF-8 bytes of its modules.
This chapter specifies how the scanner and the parser read source text in
constitutional edition 2026. It also specifies the source forms and the source
obligations that the frontend checks on every program.

Every program goes through one mandatory check, the **common judgment**. It
checks each complete original AST. It runs before any concrete profile
decides eligibility.

Two loaders read source text, one for each route of the CLI. The **project
loader** reads a source root for the project route. The **selected loader**
reads explicitly supplied modules for the selected-entry route. The chapter
also uses these terms:

| Term | Meaning | Defined in |
| --- | --- | --- |
| Project route, selected-entry route | The two routes of the `qleisli` CLI | [Diagnostics and recovery](diagnostics.md#routes) |
| Finite project, Selected Raw, Selected hierarchy | The three lowering profiles | [Elaboration](elaboration.md#source-and-acceptance-boundary) |
| Native checker | The checker executable that `lean-kernel/` builds | [Elaboration](elaboration.md#source-and-acceptance-boundary) |

Each rule names the class of diagnostic that the common judgment reports for
a program that breaks the rule. [Codes](diagnostics.md#codes) maps each class
to the code of each route. A syntax error has the code `parse` on both
routes, except for the limit refusals that
[Status and limits](#status-and-limits) lists.

Two other chapters cover neighboring subjects. The
[qrate and artifact Reference](packages-and-artifacts.md) keeps two things
apart. One is the canonical identity of a module or a declaration. The other
is the storage of source files and the resolved configuration. The gaps that
it records in edition binding are separate from the scanner and parser
checks.

The [elaboration whitelist](elaboration.md) specifies the permitted expansion
from surface forms to core forms. It also specifies evaluation order, owners,
phase, original locations and the independent checking obligations that stay
open. It grants no unsupported projection.

## Source loading and the common judgment

Loading turns the bytes of the modules into a form that the checker can
read. Whichever loader reads a program, the result is one source
representation, and the common judgment checks it.

Rules:

- Both loaders must use one scanner, one token stream, one parser and one
  source `Module`/`Span` representation.
- The common judgment must check each complete original AST first. Finite or
  selected concrete eligibility is decided after it.
- The common judgment supplies these facts about a program: declaration and
  lexical identities, types, static premises, owner and access rules, body
  dependencies and principal effects.
- The common judgment checks every declaration. This includes private and
  unused siblings, both arms of a branch and the body of a fold with zero
  iterations.
- A program that only parses has no source approval and no native
  verification evidence. Neither parsing nor source checking adds emitter
  support or an `Op<A,B>` form.
- A source-semantic error takes precedence over an unsupported concrete
  form. This holds even when the error is in an unused declaration.
- When a profile does not support the projection of a declaration and that
  definition is requested, the result is an eligibility failure with a
  location. The original body is not skipped, and the failure is not a
  fallback source approval.
- Both loaders add the eight ordinary source modules of the fixed registry and
  validate its edition-2026 manifest. The bundled modules undergo the same
  common judgment as caller source.
- Each loader applies its byte policy to bundled bytes before copying or
  parsing. A module placed under `std::` is exempt from no check.
- The selected loader reserves all eight bundled module slots. It accepts 1
  through 56 supplied modules. [Status and limits](#status-and-limits) gives
  its byte limits.

> **Implementation note.** `src/frontend/check.rs` and the modules under
> `src/frontend/check/` implement the common judgment. One private source
> collection retains the complete original bytes, the common AST and the
> provenance. A filesystem entry retains its selected path. An in-memory entry
> carries no invented file or manifest.

> **Implementation note.** The project loader moves the collection into the
> mutable `Project` compatibility view. Three kinds of operation rebuild
> their facts from the original ASTs that the view holds at the time they
> run: finite checking, compilation and checked-effect operations. After a
> caller mutates the view, nothing reuses a stale parallel collection or a
> stale approval. Documentation and rendering that read source only gain no
> semantic checking from this. The selected loader retains its immutable
> originals. It records a concrete projection result for each declaration
> only after the common judgment is complete.

### Native check modes

The implementation notes and the status section of this chapter refer to
four modes of the native checker. Each mode has a short name:

| Short name | Mode of the native checker | Request | Specified in |
| --- | --- | --- | --- |
| **ordinary-v2 check** | `--ordinary-root-check` | `qleisli.ordinary-root-request` version 2, profile `finite-ordinary-root-v2` | [Ordinary input/result requests](production-boundary.md#ordinary-inputresult-requests) |
| **runtime-v2 check** | `--runtime-root-check` | `qleisli.runtime-root-request` version 2, profile `finite-runtime-root-v2` | [Mixed runtime root requests](production-boundary.md#mixed-runtime-root-requests) |
| **v5 source check** | `--qmatch-source-v5-check` | `qleisli.qmatch-request` version 5 | [Version 5: source-body requests](production-boundary.md#version-5-source-body-requests) |
| **encoded-contract check** | `--qirf-contract` | A `qleisli.native-contract` encoded equation | [Entrypoints](production-boundary.md#entrypoints-and-actual-checked-representations) |

**QDV1** is the canonical encoding of an execution view. The
[execution-view chapter](execution-view.md) specifies the encoding and the
comparison that the native checker makes with it. This chapter writes "QDV"
for a record in that encoding.

## Bytes, characters and positions

This section says which bytes and characters the scanner accepts, and how a
diagnostic points into the source. Source is a sequence of UTF-8 bytes. A
**span** is a half-open byte interval in the original input: it includes its
first offset and excludes its last.

Rules:

- Source must be UTF-8. Source loading, scanning and diagnostics must not
  normalize its bytes.
- LF and CRLF are the accepted line endings. Ordinary whitespace is ASCII
  space or tab.
- Bare CR, vertical tab, form feed and non-ASCII whitespace are rejected
  (`parse`).
- Bidi controls and other control characters are rejected, including in
  comments (`parse`).
- The scanner rejects every Unicode scalar value that has either of two
  properties in Unicode 17.0.0 (`parse`). The properties are
  `Default_Ignorable_Code_Point` and `General_Category=Format (Cf)`. They
  cover Unicode tags, variation selectors, U+200B ZERO WIDTH SPACE and
  U+FEFF, including a leading U+FEFF.
- The diagnostic of a rejected scalar prints the offending `U+XXXX` code point
  and its original byte span. The span covers the complete UTF-8 encoding of
  the scalar.
- The scalar rule applies everywhere: inside all comments, to documentation
  input such as `qleisli doc`, and to bundled and project sources. The
  scanner does not repair the text. It preserves the original bytes and
  rejects the scalar, and the author removes the scalar from the source.
- An identifier begins with an ASCII letter or an underscore. ASCII letters,
  digits and underscores follow.
- A comment may contain ordinary Unicode prose that satisfies the same scalar
  rules.

The pinned properties come from the Unicode 17.0.0
[derived core properties](https://www.unicode.org/Public/17.0.0/ucd/DerivedCoreProperties.txt)
and [general categories](https://www.unicode.org/Public/17.0.0/ucd/extracted/DerivedGeneralCategory.txt).

## Comments and documentation

A comment holds prose for readers of the source. A documentation comment
also belongs to an item. An **outer** documentation comment stands before
its item, and an **inner** one stands at the start of the module or the body
that it documents.

| Spelling | Kind |
| --- | --- |
| `//` | A line comment |
| `/* ... */` | A nested block comment |
| `//!` and `/*! ... */` | Inner documentation comments |
| `///` and `/** ... */` | Outer documentation comments |
| `////`, `/***` and `/**/` | The start of an ordinary comment |

Rules:

- An unclosed block comment is rejected (`parse`) with the common
  `unterminated block comment` diagnostic.
- Character validation applies equally to code, ordinary comments and
  documentation comments. A comment cannot hide a forbidden control.
- Documentation text may normalize CRLF to LF in its extracted metadata.
  Source offsets refer to the original bytes.
- Outer documentation must precede a function, a type, a type member or a
  `use` item (`parse`).
- Inner documentation must start a module, a type body or a function body
  (`parse`).
- Both loaders classify comments and place documentation by the same rules.
  One common check attaches documentation to declarations. It rejects
  misplaced documentation before either profile checks source. No profile
  may silently ignore invalid placement.
- Type and member documentation attaches to the original occurrences of the
  type and the member.
- Documentation metadata only describes. Rendering from source alone makes
  no verification claim.

> **Implementation note.** `parse_documented_module` returns the documentation
> metadata. Ordinary module loading may retain only the syntax and the
> original source.

## Punctuation and tokens

The grammar reads tokens, and tokens are built in two steps. The physical
scanner recognizes individual punctuation marks. The common lexer then forms
the tokens of the grammar from them.

Rules:

- The lexer forms a composite token only from immediately adjacent marks.
  Whitespace and comments never join marks. For example, `::` is distinct from
  `: /* comment */ :`.
- The token stream includes the arithmetic and comparison marks. `==>` is `==`
  followed by `>`. It is not an alternative arrow.
- The scanner and the parser never retry another grammar. They never choose a
  backend from the input.
- The lexer scans the complete file before parsing. The diagnostic for a
  retired token later in the file can therefore come before a grammar error
  earlier in the file.
- A file can exceed the token capacity at a token that also has a migration
  diagnostic. The capacity rejection keeps precedence over that migration
  diagnostic.
- Empty parentheses in a type position are rejected (`parse`) with a
  diagnostic that directs the author to `Unit`. The value and the pattern are
  `()`.
- The shared syntax can represent these forms: the empty pattern and block,
  the empty `yield`, empty specialization brackets and a trailing comma after
  a parameter.
- The recursion budget of the parser counts the quantum wrapper and its basis
  parse together. [Status and limits](#status-and-limits) gives the scanner
  and parser limits.

## Reserved words and contextual words

A **reserved word** has a fixed role in the grammar, so a program cannot use
it as a name.

The common grammar reserves these words in every identifier position:
`use`, `meaning`, `static`, `Op`, `requires`, `Apply`, `Adjoint`, `Controlled`,
`permutation_by`, `phase_by`, `checked_op`, `bind_op`, `inverse_op`, `then_op`,
`tensor_op`, `controlled_op`, `repeat_op`, `conjugate_op`, `pub`, `classical`,
`basis`, `isometry`, `iso`, `unitary`, `observe`, `fn`, `let`, `if`, `else`,
`qfor`, `do`, `pure`, `with_computed`, `apply_contract`, `adjoint`,
`repeat_static`, `qif`, `qmatch`, `enum`, `struct`, `match`, `true`, `false`,
`not`, `xor`, `and`, `Unit`, `Bit`, `CBit` and `Q`.

Rules:

- A function, a binding or a module path must not use a reserved word as its
  name. For example, a declaration or a finite filesystem module name that
  uses `checked_op`, `enum`, `struct`, `match` or `qmatch` as an ordinary
  identifier must be renamed.
- The rule does not reach a comment or a longer identifier that contains a
  reserved word. `isotope` and `iso_value` are ordinary identifiers.
- One exception serves imports. It admits `basis`, `observe` and `classical`
  as module names immediately after `std::`.
- A second exception serves static Nat positions. The static-Nat grammar
  permits `Q`, `Op`, `Unit`, `Bit` and `CBit` in three positions: as a
  `const` Nat formal, as a static fold index, or as the first name atom of a
  Nat expression. The exception is confined to those Nat positions. The
  reserved-word rules apply unchanged to ordinary runtime identifiers, to
  Basis and Op formal names and to the tails of qualified paths.
- `qfor` starts an explicitly static quantum-owner fold. `for static` starts
  an ordinary-only fold.
- `checked_op` is the exact-meaning constructor that
  [Checked operations](checked-operations.md) specifies. `classical fn`
  declares a total ordinary computation. The `basis` expression is a
  distinct form, and [Coherent basis maps](coherent-basis.md) specifies it.
- The selected route names its modules by explicit keys. Those keys keep
  their separate validation rules. They are not unified with finite
  filesystem module names.

Some words are reserved only so that the parser can reject a retired form with
a located migration error. Such a word is never an accepted alias, and it is
not an ordinary identifier.

| Reserved word | Retired form | Replacement |
| --- | --- | --- |
| `iso` | The effect prefix `iso fn` | `isometry fn` |
| `do`, `pure` | The coherent notation `do p <- q; pure e` | `basis q as p { e }` |
| `bind_op` | The exact-meaning constructor | `checked_op` |
| `Apply`, `Adjoint`, `Controlled` | Capability requirements | `Applicable`, `Adjointable`, `Controllable` |
| `inverse_op`, `controlled_op` | Static operation descriptions | `adjoint(U)`, `controlled(U)` |
| `repeat_op`, `repeat_static` | Static repetition | `power(U, k)`, and `power(U, k)(q)` for an application |
| `CBit`, `true`, `false` | The old type and literal uses | `Bit`, and `0`/`1` |

`do` and `pure` introduce no accepted expression, alias, monadic operation or
state preparation. The lexer retains the tokens for `CBit`, `true` and
`false` so that the parser can reject their old uses with a targeted
diagnostic. Retaining the tokens does not keep those uses accepted.
`adjoint(U)` is the static description and `adjoint(U)(q)` is its application.
The two-argument form is retired.

A **contextual word** has a role in one position and is an ordinary identifier
elsewhere:

| Word | Role | Elsewhere |
| --- | --- | --- |
| `Applicable`, `Adjointable`, `Controllable` | A capability requirement in a `requires` clause, followed by an operation parameter in parentheses | An ordinary identifier |
| `Bits`, `CBits`, `Nat` | A type name or a kind name. Type-position `CBits<n>` is rejected; the replacement is `Bits<n>`. | A valid name in identifier positions |
| `as` | Separates the quantum input expression and the pattern in `basis input as pattern { expression }` | An ordinary identifier |
| `mut` | The marker of `let mut name = ...`, which the common judgment rejects | An ordinary identifier: `let mut = 0; mut` is an ordinary immutable binding and its use |
| `for`, `in`, `carry`, `yield` | `for` in `for static`, the `in` and `carry` parts of either fold header, and `yield` at the start of a fold tail | An identifier |
| `controlled` | `controlled(op)(args)` is the controlled-application construct | Ordinary single-stage name resolution: `controlled(q)` is an ordinary call to an identifier |
| `inverse` | The two-stage form `inverse(U)(q)` is rejected (`parse`), and the diagnostic suggests `adjoint(U)(q)`. [Adjoint application](static-language.md#adjoint-application) gives the rules. | Normal name resolution: `inverse(q)` is an ordinary call, and a function or a local named `inverse` is an ordinary name |
| `qlet` | None | An ordinary identifier |

Neither spelling of `controlled` guesses the category of a resolved
provider, and neither grants control access.

## Numerals and natural expressions

A numeral is a run of decimal digits. A program writes numerals as Bit
literals, as static Nat literals and inside natural expressions such as a
repetition count.

Rules:

- A numeral token retains its decimal spelling. The scanner does not convert
  it to a machine integer, infer a Bit or Nat category, or grant a static
  value.
- The common parser for natural expressions rejects a numeral with leading
  zeroes, except `0` itself. It also rejects a literal that exceeds `i128`.
- The parser retains addition, subtraction, multiplication and parentheses
  with their source spans. Multiplication binds more tightly than addition or
  subtraction.
- Static checks require an expression to be nonnegative, bounded and
  supported.
- A power repetition count has the `2^e` form, with a compound exponent in
  parentheses. This is not general exponentiation in the natural-expression
  language.
- Finite lowering evaluates each original `power` count under its complete
  static bindings. It computes with checked ordinary-u32 intermediates, and
  it bounds every nested count to 0 through 4096. An outer count of zero
  does not excuse an invalid inner count or the closed contract of a child.
- Ordinary Bit expressions and basis Bit expressions recognize the literals
  `0`/`1` with one shared recognizer. Other numerals are not Bit values.
  This rule does not change static-Nat literals, and it infers no quantum
  owner from a numeral.

## Bindings, patterns and evaluation order

A pattern names the parts of a value where a program binds it: in a
parameter, a `let` or a fold carry. This section gives the rules for
patterns, for the names they bind and for the order in which expressions
evaluate before binding. One common traversal of patterns applies the
runtime rules for wildcards, for duplicate names and for exact tuple and
Unit shapes.

Rules:

- Ordered static kinds and runtime parameter names retain the ordinals of
  their original declaration and their binder identities.
- A static kind may refer only to static parameters that precede it.
  Registering the complete declaration does not make a forward static kind
  available.
- Each quantum value has a fresh dynamic owner identity. These identities
  are distinct from the lexical keys.
- Arguments and right-hand-side expressions evaluate completely, once and
  from left to right, before binding.
- A parameter of an ordinary or a classical function uses the name, wildcard
  and tuple pattern syntax. The colon annotates the entire parameter
  pattern, and the source argument list keeps that parameter as one
  argument. For example,
  `unitary fn first((a, _): (Bit, Bit)) -> Bit { a }` takes one ordinary pair.
- Pattern checking preserves exact arity and nesting. It rejects duplicate
  parameter names (class `binding`), and it checks quantum ownership even in
  unused declarations.
- A tuple pattern does not implicitly split a quantum register.
- Argument expressions keep their evaluation order and their effects, and
  they run before the callee binds its parameters. A wildcard or Unit
  pattern does not erase the computation that produced its argument.
- A runtime parameter, a `let` binding or a fold-carry binding must not shadow
  an active static Nat, Basis, Op or fold-index binder (class `shadow`).
  Static formals may shadow global declarations.
- Once a right-hand side is completely evaluated, a consumed quantum owner
  may be rebound. Hiding a live owner is rejected. This includes a zero-axis
  owner and an owner nested in a product.
- A static name used as a runtime value is a located type error. Reuse of a
  consumed runtime owner is an ownership error.
- A resolved local value used as a callee is a wrong-category error. The
  checker never retries through a global declaration of the same name.

### Assignment and `let mut`

A checked program contains no assignment and no mutable binding. The raw AST
retains bare lexical assignment and a `let mut name = ...` marker solely so
that the checker can refuse them with a typed diagnostic. See the
[assignment and mutability boundary](rust-boundary.md).

Rules:

- Neither form can occur in a successfully checked program, and neither is
  lowered to replacement.
- For an assignment, the checker inspects the type of the resolved
  destination before it checks the right-hand side. Even a consuming
  right-hand side does not authorize replacing a place that contains a
  quantum value.
- For a mutable binding, the checker checks the type of the initializer. The
  type tells quantum ownership (class `ownership`) apart from unsupported
  ordinary mutability (class `unsupported`).
- Both refusals retain the original byte locations.
- General field and index assignment syntax and ordinary reassignment are
  unsupported. These diagnostic forms grant neither.

## Declaration resolution

Resolution finds the declaration that a name refers to. An unqualified call
resolves its name in this order:

1. Lexical runtime and static bindings.
2. Ordinary declarations of the same module, and explicit imports.
3. The six derived names of the [ordinary prelude](prelude.md).
4. A language primitive, only when the spelling is otherwise unbound.

Rules:

- The first place that binds the name selects the use. A fault in that use
  is the error that the checker reports, and no fallback exists. This holds
  for a moved binding, for a wrong callable category and for a failed
  ordinary type, effect or access check.
- A local binding that has been moved shadows a declaration with the same
  name. When the local lookup fails, the checker does not fall back to that
  declaration.
- Primitives require no import and no prelude, and their names are not
  reserved. Qualified foundation paths and hidden aliases are unavailable.
- An ordinary standard-library import keeps its visibility, its public
  effects and its source and body obligations.
- An imported declaration keeps its canonical module and declaration name.
  Imports add no runtime action and no verification privilege.
- Visibility is checked before use. A private declaration cannot be imported
  from another module or selected as a host entry. Cross-module imports and
  host-selected entries require public visibility.
- On the selected-entry route, the host can supply a provider. The checker
  checks such a provider from the context of the entry module, even when the
  provider is unused.
- Both loaders resolve imports against the complete tables of registered
  declarations. A valid reference to a sibling resolves against the same
  tables, whether the sibling is declared before or after the reference. A
  call to a sibling in the same module may use a private declaration.
- A cycle that consists only of unused imports is permitted, because imports
  have no runtime action.
- Every self-import is a declaration-name collision. This includes a private
  or public declaration imported into its own module. Duplicate imports and
  clashes with local declarations are rejected.
- The diagnostic for a missing member, a private member, a collision or a
  retired foundation entry points to the final path token. The diagnostic
  for a missing module points to the complete `use` span.
- The checker builds one graph from every original body. Runtime calls,
  static providers, classical dependencies and Meaning dependencies all
  enter this checked graph. Mutual cycles are rejected.
- Only one kind of recursion is permitted: a runtime self-call to the identical
  DefId with the checked Nat decrease. The directly transformed runtime form
  of such a call is permitted too. A recursive opaque provider, a classical
  or Meaning cycle or a failed decrease does not qualify.
- Names, effect fixed points and zero-count repetition cannot stand for the
  required decrease proof.
- Transparent `pub use`, root-qualified references and the explicit prelude
  opt-out follow the [prelude and import contract](prelude.md).
- The checker discovers no standard library from its surroundings, and a
  reserved `std` module cannot be replaced. `as`, glob and relative imports
  are unsupported.
- Evidence retains the original source, dependencies, canonical names and
  static bindings.

The [primitive boundary](primitive-boundary.md#bare-lookup-and-ordinary-shadowing)
gives the canonical primitive identities and the complete migration of the 27
retired qualified entries.

> **Implementation note.** `src/frontend/resolve.rs` and `resolve/locals.rs`
> retain the associations among canonical declarations, lexical uses and
> original spans. The common typed primitive catalog has 13 bare typed
> identities. The finite and selected concrete emitters keep their
> profile-specific adapters. Private Rust debug representations are not
> canonical names or evidence formats. Their printed fields change with the
> internal resolver.

## Parsed finite type declarations

```text
enum Name { A, B, ... }
struct Name { field: Type, ... }
```

A program declares its own finite ordinary types with these two forms. An
`enum` declaration has fieldless variants. A `struct` declaration is a
record with named fields. Either may follow `pub`, and each record field has
its own `pub` marker.

The common judgment elaborates a declaration into an ordinary nominal type
tree. The tree keeps the original module, declaration and source identity,
the variant order and the complete ordered field types.

Four expression forms use these types:

| Form | Meaning |
| --- | --- |
| `Type::Variant` | An explicit fieldless variant |
| `Type { field: expression, ... }` | A record literal |
| `value.field` | An ordinary field of a record |
| `match value { Type::A => arm, ... }` | Ordinary selection on an enum value |

The [type model](type-model.md#opaque-basis-specialization-in-the-selected-profile)
specifies these forms and their capacities.

Rules:

- A declaration has at most 64 members, which is the source product limit.
- Payload variants, discriminant assignments, tuple structs and generic type
  declarations are not parsed.
- An empty record is a distinct declaration. The parser does not replace it
  with Unit.
- Parsing does not make an empty enum, or invalid or duplicate type members,
  semantically valid. Three faults are rejected at the original offending
  name: a collision between a function and a type, an empty enum, and a
  duplicate variant or field name. These name checks come before finite
  field elaboration.
- A field must have an ordinary finite type. Unknown, recursive, non-type and
  quantum-owned fields are rejected.
- A closed field size reuses the arithmetic and the premise checks of the Nat
  helpers. It adds no general `const<T>`.
- A signature keeps both `T` and `Q<T>`. Nominal identity is not reduced to
  physical width.
- The common resolver for modules, imports and reexports also resolves
  nominal names. They form a distinct type category that is local to the
  collection. A transparent reexport keeps the original declaration and its
  visibility. Source-path traversal keeps each alias module.
- Each module or import spelling must have an unambiguous binding.
- A local ordered Basis binder cannot fall back to a global enum. A consumer
  that expects a callable or an operation rejects a type target.
- The common judgment checks the variant, record and field forms. It checks
  them with their original type and member identity, their visibility and
  the written initializer order.
- An ordinary `match` must use exact qualified enum labels, and its arms must
  be exhaustive and disjoint. It has at most 64 arms. A runtime block allows
  an expression or a block for each arm. A classical body allows an ordinary
  expression for each arm.
- Each declaration keeps its whole original span, its body span and its
  ordered variants or fields. A named type path keeps all its qualified
  segments and their byte span.

The project route accepts this program, and `main` returns 1. The record
literal writes its fields in an order other than the declared order:

```qli
struct Empty {}
struct Packet { bit: Bit, empty: Empty }
classical fn bit() -> Bit { Packet { empty: Empty {}, bit: 1 }.bit }
fn main() -> Bit { bit() }
```

> **Implementation note.** For nominal elaboration, the complete retained
> module sources must parse to the supplied ASTs. The check also inspects the
> original `enum` and `struct` tokens, so deleting AST declarations cannot
> hide them. Comments and identifier substrings are not declarations.
> Non-nominal constructed-AST consumers keep their own boundary.

> **Implementation note.** Prepared nominal facts keep the original references
> in field types and in closed Nat-helper calls. Ordinary provenance
> collection follows these type dependencies, their transparent reexport
> chains and the original lexical dependencies of the helpers. It checks the
> retained declaration, source and occurrence identity before it collects
> bytes. This is untrusted provenance preparation. Read-only retained nominal
> maps preserve the `Send + Sync` contract of source handles.

> **Implementation note.** The Rust `Project` view labels
> `ResolvedImport.kind` as `ImportKind::Function(FnKind)` or
> `ImportKind::Type`. Its `declaration_span` points to the original
> declaration in the canonical `module`, and `span` is the importing
> occurrence. A Rust caller matches the import category explicitly. Project
> loading and this descriptive metadata grant no source acceptance and no
> native handle.

## Total classical declarations

```text
classical fn f(pattern: T, ...) -> U { expression }
```

A `classical fn` declares a total, pure finite function on ordinary values.
A program writes one for a computation on ordinary data that it wants to use
in several settings: at run time, in a Meaning or a predicate, and inside a
coherent `basis` expression.

A `classical fn` is distinct from a provisional `static fn` declaration. A
`static fn` returns a static Nat value through the
[bounded helper rules](static-language.md#provisional-bounded-nat-helpers).
It has no runtime interface, no effect and no accepted-handle authority.

The retired declaration spelling `basis fn` is rejected (`parse`) with a
located migration diagnostic that directs the author to `classical fn`. No
compatibility alias exists. The coherent expression
`basis q as pattern { expression }` and static `A: Basis` parameters keep
their meanings.

### The body of a classical function

The body is a single expression that computes the result from the
parameters.

Rules:

- The body must be one restricted label expression. Its forms are names,
  `()`, `0`/`1`, ordered products, eager `not`/`and`/`xor`, and acyclic calls
  to other classical functions.
- The body may also use the nominal forms `Type::Variant`, a record literal
  and `.field`, and an ordinary `match` on exact qualified enum labels.
  [The body of a coherent basis map](coherent-basis.md#the-body) tabulates
  every form.
- `empty_bits()` is the ordinary language primitive constructor that takes no
  arguments. It requires no import, and it has the exact `Bits<0>` signature.
  Other quantum primitive calls are excluded.
- `word[k]` reads one ordinary `Bits<n>` coordinate and returns a `Bit`. The
  nonnegative integer literal `k` must satisfy `k < n` under the declared
  static premises. `Bits<0>` has no valid coordinate.
- Coordinate zero is the first bit, with the lowest weight in the basis
  ordinal. The read copies the coordinate and does not consume the ordinary
  register.
- The body has no runtime statements, no observation and no quantum capture.
- Parameter trees, result trees and argument-list arity are exact.
  Noninjective functions are permitted.

A `Bits<n>` word has an unsigned ordinal in `0 .. 2^n - 1`, and its first
coordinate carries weight one. Each Boolean operation returns an exact Bit.
A program can write word arithmetic explicitly with bit operations. Such
arithmetic keeps the result width that its return type states. For example,
the two-bit increment flips the low bit and XORs the original low bit into
the high bit. It returns `(x + 1) mod 4`, and the carry beyond the high bit
has no output coordinate.

Static `Nat` expressions follow the separate
[bounded natural rules](static-language.md). No implicit conversion exists
from a static natural or an arbitrary integer to a `Bits<n>` word.

The project route accepts this program, and `main` returns 1. The classical
body is an ordinary `match` on a nominal label:

```qli
enum Tri { A, B, C }
classical fn flag() -> Bit {
    match Tri::C { Tri::A => 0, Tri::B => 0, Tri::C => 1 }
}
fn main() -> Bit { flag() }
```

### Static parameters of a classical function

A static parameter lets one classical declaration work at more than one
size, as `width` does in the example below.

Rules:

- A classical declaration may take compile-time parameters of kind Nat and
  declare natural premises with `requires`. The premises must establish every
  coordinate bound in the original body.
- A classical declaration without static parameters must not have a
  `requires` clause (`parse`).
- An ordinary runtime call supplies the exact actuals in brackets.
- A `with_computed` predicate reference uses the same syntax. It must match
  the complete input basis and the Bit result at that specialization.

The following declarations use a static parameter, a premise and a
`with_computed` predicate reference:

```qli
classical fn marked[const width: Nat](word: Bits<width>) -> Bit requires width>=3 {
    word[0] and not word[1] and word[2]
}

pub unitary fn oracle[const n: Nat](q: Q<Bits<n>>) -> Q<Bits<n>> requires n>=3 {
    with_computed(q, marked[n]) { |flag| phase[1,1](flag) }
}
```

After a program collects three measurement results in `word: Bits<3>`, an
ordinary call can instantiate the same declaration with width 3 and pass
`word` as its argument.

### Calls of a classical function

A classical function has one checked body, and every kind of call uses that
body.

Rules:

- A program may call the same checked body in ordinary runtime expressions,
  in Meaning and predicate construction and in coherent `basis` expressions.
- Runtime arguments evaluate once, left to right, before parameter binding.
  Their effects and their owner consumption stay in the caller. This holds
  even when the caller ignores an ordinary result.
- A measured Bit is ordinary data. A live `Q<T>` cannot be passed as `T`
  without explicit observation.
- Coherent lifting has a requirement of its own: the complete map is
  injective. Computed predicates keep their separate exact cleanup
  contracts.
- A classical declaration or its name grants no inverse access, no controlled
  access, no Meaning evidence and no native acceptance. A Meaning declaration
  is a description, not a runtime callee.
- Totality describes the classical declaration on its entire type. Coherent
  compilation also requires a supported reversible embedding and a successful
  check within the [capacity of the finite profile](production-boundary.md).

The following declarations call one classical function in a coherent `basis`
expression and on a measured Bit:

```qli
classical fn flip(b: Bit) -> Bit { not b }
fn invert(q: Q<Bit>) -> Q<Bit> { basis q as b { flip(b) } }
fn read_flipped(q: Q<Bit>) -> Bit { flip(measure_z(q)) }
```

> **Implementation note.** The Selected Raw route checks the original
> declaration and its Nat arguments before use. The supported structural
> predicate path synthesizes its literal control clauses directly. Structural
> synthesis charges work for processing the original expression and for the
> intermediate and emitted control clauses. Conjunction can increase the
> number of clauses, so a total predicate can exceed the work limit. A finite
> consumer that needs a table must satisfy its own checked domain and work
> limits. Failed preparation yields a diagnostic before an execution handle is
> issued.

## Exact-label coherent selection

```text
qmatch(selector, target) { label => arm, ... }
```

`qmatch` selects a coherent operation without measuring its selector. Each
label names a basis value of the selector, and the arm of that label acts on
the target. An **arm** is a resolved static operation or an inline block.

Let arm `s` denote the exact operator `U_s`. The operation maps each basis
vector `|s,y>` to `sum_z U_s[z,y] |s,z>`. It extends linearly to every input,
including an input entangled with an external reference. It therefore
preserves coherence between selector sectors, and it agrees exactly with `qif`
for `Bit`.

Selector axes precede target axes. The pair `(s,y)` therefore has the integer
coordinate `s + 2^selector_bits * y`, whatever the written order of the arms.

### Selector, target and labels

The selector and the target are two separate quantum owners. The labels name
the basis values of the selector.

Rules:

- The selector must be one `Q<A>` owner, and the target must be one distinct
  `Q<B>` owner (class `type`). The expression returns `(Q<A>, Q<B>)` with both
  complete type trees unchanged.
- An owner of zero physical width is a linear owner like any other. Zero
  width removes neither the selector owner nor the target owner.
- For `Unit`, `Bit` and closed `Bits<n>` with `0 <= n <= 6`, a label is a
  canonical decimal ordinal from `0` to `cardinality(A)-1`.
- For a fieldless nominal enum, a label is a qualified variant name of that
  exact original declaration. It respects imports, reexports and visibility.
  Unused physical tags are not enum labels.
- Labels may be written in any order. They must cover the logical basis of
  the selector exactly once (class `type`).
- A `qmatch` has at most 64 arms.
- Wildcards, ranges, payloads, guards and dynamic arm calls are outside this
  form.

### Arms

Every arm acts on the same target, and the checker holds every arm to the
same requirements.

Rules:

- An arm must have the exact target interface and a valid Unitary effect. It
  must permit controlled access under the operation rules (class `access`).
- Each arm meets its own type, effect, access and dependency obligations. A
  generic earlier arm, a constant selector or an unused declaration cannot
  skip those obligations for a later arm.
- Unitarity alone grants neither control nor inverse access.
- The phase of every arm is exact.
- `qif` keeps its fixed syntax, with the `0` arm first and the `1` arm
  second, and its access contract. It uses the same labelled sectors as
  `qmatch`.

### Block arms

A block arm is an inline block in place of a static operation. It lets an
arm spell out its steps on the target where the arm is written.

Rules:

- Inside a block arm, the written target name is bound to the target owner.
  The block must return one owner of the exact quantum type of the target
  (class `ownership`).
- Other quantum owners and ordinary runtime owners of the enclosing scope are
  unavailable in the block.
- A block arm that ends in a semicolon returns its original target binding.
  That binding must be live at the end of the block. An explicit final
  expression can return a target reassembled from local owners.
- A block arm may contain an `if static`. This includes a `basis` lift that
  preserves the exact target owner, and an indexed `excl` call whose selected
  and other owners are issued and retired within the checked access.
- Within the finite profile, an inline arm can use `basis`, `with_computed`,
  `clean` and `dirty`. The checker reads the original basis table or the
  computed predicate, and it applies the same scratch restoration checks as
  for a named body. A `dirty` scratch owner must come from the local target of
  the branch.
- An `excl` call in a block arm can update a whole local owner or disjoint,
  [statically selected places](elaboration.md#static-ordered-axis-places) in
  a local register. The callee must return the same ordered selected types.
  An empty selection has an owner.
- In a call with `ctrl` places, the operation of the callee must preserve the
  computational-basis sectors of those places. Relative phases within a
  coherent state may change.

### Examples of coherent selection

The following functions show block arms of `qif`:

```qli
pub unitary fn select_bit(s: Q<Bit>, q: Q<Bit>) -> (Q<Bit>, Q<Bit>) {
    qif(s, q) { 0 => h, 1 => { let r = h(q); phase[1,1](r) } }
}

pub unitary fn select_exclusive(s: Q<Bit>, q: Q<Bit>) -> (Q<Bit>, Q<Bit>) {
    qif(s, q) { 0 => { h(excl q); h(excl q); }, 1 => { h(excl q); } }
}
```

The following functions show `qmatch` with labels in a written order other
than the ordinal order, and with block arms:

```qli
pub unitary fn select(s: Q<Bit>, q: Q<Bit>) -> (Q<Bit>, Q<Bit>) {
    qmatch(s, q) { 1 => global_phase_eighth, 0 => h }
}

pub unitary fn select_word(s: Q<Bits<2>>, q: Q<Bit>) -> (Q<Bits<2>>, Q<Bit>) {
    qmatch(s, q) {
        0 => { q },
        1 => { h(excl q); },
        2 => { phase[1,1](q) },
        3 => h,
    }
}
```

The selected-entry route with the native checker accepts `main::route` of this
module. Its second arm is a constructed static operation:

```qli
#![no_implicit_prelude]
unitary fn keep(q:Q<Bit>)->Q<Bit>{q}
unitary fn sign(q:Q<Bit>)->Q<Bit>{phase[1,1](q)}
meaning Sign:Bit=reference(sign);
pub unitary fn route(s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){
    qmatch(s,q){0=>keep,1=>checked_op(sign,Sign)}
}
```

With `reference(keep)` in place of `reference(sign)`, the same route rejects
the module with the code `contract`.

> **Implementation note.** For a block arm, the producer submits the literal
> arm Raw and the positions of the events within the original block. The v5
> source check follows those events in the arm Raw, checks the control
> evidence of their operations, and checks the resulting sector against the
> enclosing Raw interval. For an `if static`, the check covers the original
> Raw interval of the selected branch and its local owner frame. For an `excl`
> call, the checker binds the written selectors to the Raw extraction, checks
> the original callee, and reinserts the returned owners in their written
> places.

> **Implementation note.** On the encoded-contract route, the complete
> proposed circuit and the independently obtained exact block meaning go
> through a fresh native encoded equation before emission. A Rust sector
> projection cannot issue acceptance. The emitted Raw root undergoes ordinary
> native checking. When the containing function needs the v5 source check,
> each `qif` and each `qmatch` keeps its own source position, its ordered arms
> and its literal Raw interval. [Status and limits](#coherent-selection) gives
> the route of each selection and the components of the check.

## One structured quantum result boundary

Verified quantum-core functions are expression-oriented: a body produces its
result as the value of its final block expression. That expression is the one
**structured result boundary** of the body. A function leaves through it and
through no other exit.

Rules:

- Every runtime branch must retain and merge the complete required owner
  frame and the exact result tree. Both arms are checked even when one is
  statically unreachable.
- No early exit can discard, release, reset or uncompute a live owner
  implicitly.
- These exits are not admitted: early `return q`, residual propagation `q?`,
  the runtime macro edges `panic!`, `assert!` and `unreachable!`, unwinding,
  hidden abort and partial quantum functions. The parser rejects the written
  exits (`parse`).
- The rule applies to Unitary, Isometry and Observe bodies. An observing
  effect does not authorize a hidden exit.
- The diagnostic of a syntax refusal explains the alternative, a final
  expression. It keeps the byte span of the original token.
- For control flow, a program uses explicit ordinary branches, admitted
  coherent control and finite folds, each under its own owner and effect
  rules. `qmatch` keeps its separate limits.
- This chapter grants no `qreturn` or `qtry` form.
- Ordinary identifier names keep normal resolution. A variable or a checked
  ordinary function named `return`, or a function named `panic`, is not a
  return or abort primitive. An ordinary `return(q)` call keeps the normal
  call rules.
- A comment that contains these spellings creates no executable edge.

For example, `unitary fn keep(q:Q<Bit>)->Q<Bit>{q}` has the structured result.
Replacing its body with `{return q}` is invalid. A final `if` whose one arm
returns Unit while the other returns `Q<Bit>` is also invalid, and the refusal
inserts no cleanup.

Both routes reject this program with the code `parse`, at the token `return`:

```qli
unitary fn bad(q:Q<Bit>)->Q<Bit>{return q}
observe fn main()->Bit{1}
```

Both loaders accept the next program. Its names and comments spell exits, and
none of them is an exit:

```qli
unitary fn panic(q:Q<Bit>)->Q<Bit>{q}
unitary fn return(q:Q<Bit>)->Q<Bit>{let return=panic(q);return}
unitary fn forward(q:Q<Bit>)->Q<Bit>{return(q)}
// return q? panic!(); unreachable!()
/* assert!(1); q? */
observe fn main()->Bit{1}
```

A future host orchestration language may specify `Result`, residual exits,
assertions or process failure separately. The present core imports no such
host failure semantics. If ordinary error values were separately admitted as
data, they would not by themselves imply propagation or unwinding. The
runtime checker and its transport refuse fail-closed. Such a refusal is
likewise not a source-level exit.

## Checking failures and quantum execution

This section says where a failure can occur and where it cannot. Within the
declared finite model, a supported verified quantum-core operation has no
implicit exceptional execution edge. This applies to Unitary, Isometry and
Observe. Measurement supplies its specified ordinary outcome and instrument.
It gives no permission to panic, unwind, abort, partially return or abandon
an owner. This totality requirement is the adopted failure contract.

### Rejection before execution

The checker rejects an invalid program during checking or specialization. It
does not turn the fault into a trap at run time.

Rules:

- Invalid sizes, type trees, static indices, access or capability
  requirements and required constraints are rejected during checking or
  specialization. See [static checking](static-language.md).
- `take_bit[n,k]` requires an established `k < n` (class `size`). It does not
  compile an unknown index into a quantum runtime bounds trap.
- Checked Nat arithmetic cannot wrap, and it cannot defer overflow to a
  quantum exception.
- Bounded elaboration, unsupported profiles and unproved obligations are
  rejected before an executable handle is issued for that proposal.

### Ordinary alternatives

A program expresses an alternative outcome with ordinary data and an
ordinary `if`. Each alternative returns through the normal structured
boundary.

Rules:

- An explicit ordinary result such as a Bit may select an ordinary `if`. Both
  arms must satisfy the complete required owner frame, the exact type tree
  and the effect rules.
- A recoverable alternative returns its declared data and owners through the
  normal structured boundary. It must not implement a hidden exit, implicit
  cleanup or a success-only path.
- For example, an operation may return `(flag, q)` or `(flag, x(q))` in its
  two arms when their declared interfaces agree. Omitting `q` in one arm is
  invalid.
- The unchanged caller frame takes part in the branch merge. This includes
  correlated owners and zero-width quantum owners. An ordinary condition does
  not establish separability.
- Failure handling in source cannot do any of these: reset or discard
  workspace, discharge a clean or dirty restoration obligation, erase exact
  phase or owner ordering, or shorten an access lifetime to omit required
  work.
- The absence of an unwind construct does not prove pending access,
  restoration, target or quantitative resource contracts. Their
  implementations must obey this rule when they are admitted.

The Finite project profile accepts this program. The function `choose`
returns its data and its owner in both arms:

```qli
use std::state::init0;
use std::gate::x;use std::gate::cnot;
fn choose(b:Bit,q:Q<Bit>)->(Bit,Q<Bit>){if b {(0,q)}else{(1,x(q))}}
pub observe fn main()->(Bit,Bit,Bit,Bit){
    let (a,r)=cnot(h(init0()),init0());
    let b=measure_z(h(init0()));
    let (tag,a)=choose(b,a);
    (b,tag,measure_z(a),measure_z(r))
}
```

### External faults

Some failures happen outside the quantum core. The rules below say what such
a failure does not give a program.

Rules:

- Operating-system failure, verifier or transport failure, backend crash and
  device loss are external faults. They are outside the quantum-core
  operational theorem unless an explicit future target contract models them.
  They provide no source escape hatch and no owner-disposal semantics.
- Native checking that is missing, incompatible, timed out or malformed
  is rejected. No accepted handle is issued, and no fallback runs. Such a
  refusal is a failed attempt to check an artifact. It is not an executed
  quantum branch.
- Reference simulation can separately refuse its host execution, component or
  space budgets, or report a numerical or internal-consistency error. Such a
  refusal or error certifies no result distribution as the successful
  program result.
- These host limits are not static quantum resource certificates. Reporting
  an error is not proof of physical state recovery, or of clean or dirty
  restoration after an external fault.

## Ordinary function effects and assertions

An effect prefix states how much quantum behavior a function permits itself.
An ordinary function that has a body may use `fn`, `unitary fn`,
`isometry fn` or `observe fn`. The prefix is an **effect assertion**: a
declared upper bound on the effect of the body. The effect order is
`Unitary <= Isometry <= Observe`. The effect of a composition is the least
upper bound of the effects of its parts.

An **isometry** satisfies `V†V = I_input`. The word claims no surjectivity and
no executable inverse or control access. Zero-state preparation is an
isometry. It is not a unitary, because its input and output dimensions
differ. A unitary additionally satisfies `VV† = I_output`. In categorical
terminology these are a dagger-monomorphism and a dagger-isomorphism,
respectively.

### Effect assertions on declarations

A public function that processes quantum values or operations states its
effect explicitly. Other functions can leave their effect to inference.

Rules:

- A public function that processes quantum values or operations must
  explicitly use `unitary`, `isometry` or `observe`. This includes closed
  functions, zero-width owners, quantum intermediates and operation formals.
- Ordinary classical public functions may keep inference. Private functions
  keep inference.
- Copying an ordinary Bit does not copy a quantum owner, and it adds no
  quantum effect.
- An explicit effect prefix permits quantum processing even behind an
  entirely classical signature. Checking of quantum use from outside the
  module conservatively keeps that public permission. It does not inspect
  the use flag of the implementation.
- A public classical API without an annotation cannot acquire hidden quantum
  work. Such work requires a change of its public declaration and a pass of
  the complete checks.
- Changing the public effect is an API change. An edit to the body alone
  cannot silently regenerate the public effect.

### Effect checking of a body

The checker infers the effect of a body without using the declared prefix.
It then compares the result with that prefix.

Rules:

- The complete body is checked independently. Its inferred effect must fit
  the declared upper bound (class `effect`). A prefix is never a starting
  point for inference.
- An Observe body cannot assert Unitary or Isometry, and an Isometry body
  cannot assert Unitary.
- An implementation inferred as Unitary may expose Isometry or Observe.
  External callers use only that checked public effect. This holds even when
  the source is available, and under inlining, specialization or a cached
  provider.
- Both arms of a branch and the body of a static fold with zero iterations
  take part in effect inference.
- A decreasing runtime self-call uses the least effect solution only after
  the decrease check. Mutual dependencies are rejected.
- An invalid or unresolved source body yields no checked effect fact.
- Type, ownership, access and termination checks apply independently. An
  annotation cannot supply a missing check or an arbitrary mathematical
  Meaning.

### Effects that callers use

The effect that a caller sees depends on whether the caller and the callee
share a module.

Rules:

- A call within one module uses the checked internal inference of the
  original callee.
- A call between modules with different original identities uses the checked
  public effect of the callee. An import alias does not change that identity.
- Internal inference keeps any further external boundary. An internal wrapper
  cannot wash an external Observe call into Unitary.

### Effects of providers

The effect that a provider contributes depends on who selects the provider:
the source or the host.

Rules:

- A provider that the source selects uses the checked effect that is visible
  in the original module of the caller.
- A public provider that the host selects always uses the public contract,
  even for an unused binding. The host cannot claim same-module status.
- Where the own module of the selected entry supports an explicit binding to
  a private provider, that binding keeps its internal visibility.
- A generic body uses its formal bounds. It cannot sharpen them from a
  fortunate later provider.
- Adjoint, control and pure contracts require their separate evidence and a
  visible Unitary effect. Other general arrows obey their declared effect
  ceiling.
- A mismatch of the input or output shape of a provider is a type error. It
  is not an external effect justification.

### The `isometry` spelling

Source spells the Isometry effect `isometry`. The shorter `iso` is a retired
effect prefix. The parser rejects it with a lexical migration error at its
original token, before native checking. Replace `iso fn` with `isometry fn`.

The canonical names are:

| Surface | Canonical spelling |
| --- | --- |
| Source effect assertion | `isometry fn` |
| Rust effect | `qleisli::ir::Effect::Isometry` |
| Rust function and token kinds | `frontend::ast::FnKind::Isometry`, `frontend::lexer::TokenKind::Isometry` |
| Lean Raw effect | `QleisliKernel.Semantics.Raw.Effect.isometry` |
| Lean hierarchy effect | `QleisliKernel.Hierarchical.Artifact.Effect.isometry` |
| Lean retained bounded QFT graph effect | `QleisliKernel.QftGraph.Effect.isometry` |

Rules:

- Rust callers use the `Isometry` variants in place of `Effect::Iso`,
  `FnKind::Iso` and `TokenKind::Iso`. No Rust compatibility alias exists.
  Body-effect diagnostics also use `Isometry`.
- Some transports keep the tag `"iso"`. They are the versioned JSON and QIRF
  effect tags, the effect tag of the checked source graph and the native
  hierarchy adapters. The binary hierarchy effect tag is `1`.
- These explicit transport exceptions introduce no second source effect, and
  they grant no inverse or control access.
- Naming alone establishes no semantic property and no constitutional
  guarantee.

> **Implementation note.** The three Lean names are reducible aliases for
> their `Effect.iso` constructors. They provide the canonical spelling for
> Lean expressions without a change of constructor identity, generated
> recursors, `.iso` case names or derived `Repr` output. Historical formal
> statements and callers that use the constructor keep that compatibility.
> The QFT graph alias changes only the vocabulary of a public type; it adds no
> QFT implementation.

> **Implementation note.** `QleisliKernel.Raw.State.iso` is an internal
> allocation-tracking Boolean. It is not an effect assertion or evidence of
> the isometry law. Local proof witnesses named `iso` likewise are not public
> effect vocabulary. These implementation names and the compatibility
> constructors are unchanged.

### External effect justification

A body can observe, reset or discard internally while a separate argument
claims that the channel its callers see is unitary. An annotation cannot
rest on such an argument: the justification `"externally unitary"` is not
supported. The compositional rules keep internal observation, reset and
discard as Observe.

Rules:

- An ordinary annotation cannot replace the compositional rules with an
  external certificate, even if a separate argument claims that the induced
  public channel is unitary.
- A contradictory annotation is an effect and semantic error (class
  `effect`). Its diagnostic states the inferred effect and the asserted
  effect, and it explains this unsupported semantic boundary without a GitHub
  Issue reference.
- The refusal does not prove that the public channel is mathematically
  non-unitary. It means that the proposed external justification is
  unavailable.
- Externally isometric justification is likewise unsupported.

### Source effects and artifact effects

A function has an effect in its source contract, and the artifact lowered
from it has an effect of its own. Source contract effects and artifact
effects are distinct.

Rules:

- A conservative Observe contract does not rewrite a genuinely pure Raw body
  as observing.
- The sharper classification of that Raw body grants no external source
  capability.
- The operations and histories of the artifact go through fresh native
  checking.
- A valid source body may keep its principal effect while its requested
  concrete projection or lowering is unsupported.
- Source effect facts are not accepted IR handles and not a
  source-preservation proof. Finite lowering, selected concrete lowering and
  the native checks are distinct.

### Rust interface

| Interface | What it exposes |
| --- | --- |
| `project_effects_with_kernel` | Immutable `ProjectEffects` for finite projects |
| `ParsedProgram` | The effect facts for selected source |
| `function_effect` | The internal inferred effect, the checked assertion, the typed quantum-use flag and the distinct `public_effect()`, for inspection |
| `public_effect()`, also `public_function_effect(path)` | The exported effect contract |
| The `documentation` methods | The public contract of a public function, and the inferred and asserted diagnostic facts of a private function, rendered from retained source bytes |
| The source-only `doc` command and `render_markdown` | A rendering that states explicitly that it has no semantic checking. It manufactures no inferred facts. |

Rules:

- Only `public_effect()` is an exported effect contract. Inspecting internal
  inference grants no eligibility.
- Changing a source file after a `documentation` report cannot rebind the
  report.
- Concrete finite declarations undergo native verification. Generic facts are
  conditional on their checked source premises.

## Instruments and ordinary feed-forward

An Observe expression can measure, so it can end with more than one ordinary
result. This section gives the meaning of such an expression: an instrument,
which has one map for each public result.

The judgment `Γ ; Δ ⊢ e : T ! Observe` gives an upper bound on the quantum
behavior of the complete expression. Fix the ordinary inputs `x`. Let `A` and
`B` be its complete input and output quantum interfaces, including the live
caller frame that the ownership judgment retains. Let `c` range over the
ordinary projection of its declared result. The intended meaning is a finite
quantum **instrument**: completely positive, trace-nonincreasing maps
`Φ[x,c] : L(A) -> L(B)` whose complete sum is trace preserving.

For the complete hidden histories `h` and their public-result projection,
write:

```text
Φ[x,c](ρ) = Σ_{h : public(x,h) = c} K[x,h] ρ K[x,h]†
Σ_h K[x,h]† K[x,h] = I_A
```

The rules of this section are normative source obligations. The
[target realization judgment](realization.md#observing-instruments-on-a-target)
adds profile-specific capability and artifact evidence. The
[primitive boundary](primitive-boundary.md) and the
[standard-library contracts](stdlib.md) give the admitted measurement actions.

### The instrument contract

The contract counts every history, including the histories whose outcomes a
function does not return.

Rules:

- Every history contributes its unnormalized weight. Hidden measurement,
  reset and discard outcomes stay in the sum even when they are not returned
  as ordinary data.
- If the ordinary result is Unit, its public outcome set is the singleton
  `{()}`.
- For every finite external reference `E`, the same instrument acts on an
  arbitrary joint input through `Φ[x,c] ⊗ id_E`. Separate owners do not imply
  a product state.
- Normalizing a selected branch, or comparing only outcome probabilities,
  does not establish this contract.

### Pure implementations and the effect order

A pure implementation fits the same contract. Its density map is an
instrument with a single public result.

Rules:

- The effect order `Unitary <= Isometry <= Observe` is an order of permitted
  quantum behavior.
- For fixed ordinary inputs, a pure implementation has one public result. It
  acts by its exact `U[x]` or `V[x]`, with `U†U = UU† = I` or `V†V = I`
  respectively. Their density maps are singleton instruments.
- The underlying pure meanings keep their exact phase and their separate
  inverse-access and controlled-access obligations. Instrument equality
  cannot erase those contracts, and it cannot turn a public Observe interface
  into a pure capability.
- An Observe bound permits a pure implementation. It does not require every
  call to create a public Bit.
- Body inference is independent, and callers across an original module
  boundary use the checked public bound.
- Observation, reset and discard infer Observe under the compositional rules,
  even when a separately described public channel happens to be pure.

### Measurement

A measurement produces an ordinary Bit from a quantum state. The rules give
the maps of the destructive measurement, of a measurement that retains its
owners, and of reset.

Rules:

- Destructive `measure_z : Q<Bit> -> Bit` consumes its input owner. For the
  result `b`, its map uses `K[b] = <b|`. It keeps the conditional state and
  the weight of all other owners and references.
- The state-retaining example is `std::measurement::parity_zz`. It returns
  both data owners and a Bit, consumes its internal meter, and acts by
  `P[s] = (I + (-1)^s Z tensor Z)/2`. Coherence within each parity sector is
  retained.
- Retaining an owner does not promise an unchanged state.
- The implementation of reset that explicitly discards and then prepares
  consumes the original owner and returns a fresh zero owner.

### Ordinary feed-forward

**Feed-forward** uses a measured Bit to choose what a program does next.

Rules:

- Ordinary `if` uses an ordinary Bit. After an observation it selects the
  next operation separately in each complete history.
- Both arms must pass checking and return the same complete result and
  live-owner shape, including zero-width owners.
- Sequential composition keeps every intermediate history and its weight.
  Only histories with the same final public result are summed.
- A coherent `qif` uses its separately checked coherent operation and
  preserves coherence between selector sectors.
- An ordinary branch cannot inspect a live `Q<Bit>` or insert an implicit
  measurement.

## Observation and postselection

Postselection keeps only chosen outcomes and continues on their renormalized
state. Qleisli provides no source postselection effect and no postselection
construct. Ordinary Observe has the complete-instrument contract above: the
sum of all outcome maps is trace preserving.

Rules:

- An individual outcome map may decrease trace. Its trace is the probability
  of that outcome. The decrease is not permission to discard the other
  outcomes and advertise the selected map as the whole operation.
- None of these authorizes keeping only chosen outcomes and continuing on
  their renormalized state: Observe, an ordinary `if`, a successful check or
  a clean-release operation.
- Returning a success Bit together with the declared owners is an ordinary
  instrument only when both the success and the failure outcomes stay in its
  semantics.
- Classical feed-forward executes the selected arm for each history. It does
  not remove histories whose measured Bit selects the other arm.
- Hidden outcomes of explicit discard also stay in the complete sum.
- A zero-probability event supplies no conditional state.

A future postselection proposal would need a distinct semantic category. For a
chosen outcome set `S`, it would have to specify three things: the
trace-nonincreasing map `Φ_S = Σ_{c in S} Φ[c]`, its success probability
`p_S(ρ) = Tr(Φ_S(ρ))`, and any conditional state `Φ_S(ρ) / p_S(ρ)` only where
`p_S(ρ) > 0`. It must expose four things: success and failure outcomes,
ownership on both outcomes, composition with surrounding operations and
reference systems, and resource accounting for any requested retries. This
paragraph describes requirements for a future proposal. It is not an
admitted API, and it does not extend the effect order.

Postselection is distinct from the
[checking and external failures](#checking-failures-and-quantum-execution).

Rules:

- A failed check, a panic, a target fault or an exhausted host budget
  supplies no accepted successful quantum branch.
- The bounded host trial driver separately reports retries, exhaustion and
  execution errors. It retains no quantum state, and it grants no
  source-level postselection and no clean-release capability.
- Exact clean release requires its independently checked obligation: a zero
  return that holds for all inputs and is safe for references. The
  obligation does not condition on a favorable observation.
- Numerical trajectory sampling may normalize a branch after it draws the
  outcome from the supplied random source. That representation does not
  permit the source to choose a favorable outcome, erase its probability or
  omit alternative outcomes from the instrument contract.
- Simulation keeps its stated numerical and runtime assumptions.
- The observing Physical Realizability target concerns the complete
  instrument and the admitted realization without hidden conditioning, as in
  [the realization contract](realization.md).

## Parser guidance for surface syntax

Some syntax errors sit at a place where the parser recognizes a Qleisli
surface rule. There the parser may explain the canonical local form.

Rules:

- `qlet owner = value;` is an invalid binding statement (`parse`). Use
  `let owner = value;` for an ordinary binding, including a binding to a
  `Q<A>` owner.
- When a `qif` or `qmatch` header lacks its opening parenthesis, or a `qfor`
  header lacks `static`, the diagnostic can show the corresponding construct
  as the grammar writes it.
- Text diagnostics and structured diagnostics carry the same guidance and the
  same original source location.
- A grammar example supplies a syntactic form. Name resolution, typing,
  effects and ownership determine whether a program that uses the form is
  valid. See [the roles of quantum syntax and types](type-model.md#surface-roles).

## Diagnostics at control boundaries

Ordinary control branches on ordinary data, and coherent control acts on
quantum owners. This section covers a rejection at the boundary between the
two. At such a source rejection, a diagnostic names the language rule and
the nearby valid construct, so that authors and coding agents can revise the
program from the diagnostic.

| Construct | Role |
| --- | --- |
| Ordinary `if` | Evaluates a `Bit` |
| Ordinary `match` | Discriminates among ordinary enum alternatives |
| Coherent `qif` and `qmatch` | Apply checked controlled arms to a separate target, and return the selector and the target |

For example, `qif(control, target) { 0 => h, 1 => h }` is a coherent selection
when both arguments are `Q<Bit>` and the arm operation supports control. For a
nominal selector, the `qmatch` arms use its exact checked labels.

An explicit `measure_z` consumes a `Q<Bit>` and returns an ordinary `Bit` in
an `observe` context. That bit can direct ordinary branching. Coherent
selection keeps the relative phase of the selector sectors. See
[ordinary feed-forward](#instruments-and-ordinary-feed-forward) and
[static folds and carry](static-language.md#static-branches-folds-and-termination).

Rules:

- The common judgment adds the control explanation where it rejects a
  selector or a carry directly. A name, ownership, type or limit error that
  is nested inside keeps its original diagnostic.
- Text output and `--format=json` output preserve the category and the
  location.
- The optional `control_flow_boundary` object is available on both routes.
  Its `boundary` is `classical_quantum_control`. Its `reason` is
  `if_condition`, `qif_control`, `match_selector`, `qmatch_selector`,
  `for_carry` or `qfor_carry`. [Refinements](diagnostics.md#refinements)
  specifies the object.
- An ordinary binding of a quantum owner uses `let` and follows the
  [linear ownership rules](type-model.md).

## Migration

This section tells an author how to bring older source to the forms of this
chapter.

### Finite and sized programs

Edition 2026 uses one source grammar for literal and parameterized programs.
The project loader and the selected-entry loader both check the original
declarations. A checked program must also satisfy the entry and IR profile
requirements of the command that consumes it.

| Source in a finite or sized program | Disposition and migration |
| --- | --- |
| `Unit`, `Bit`, ordered tuples, `Bits<n>` and `Q<A>` | Kept. Preserve the type tree. `Bits<1>` and `Bit` are distinct, as are `Bits<0>` and `Unit`. See the [type model](type-model.md). |
| `CBit`, `CBits<n>` and `()` in a result type | Use `Bit`, `Bits<n>` and `Unit`, respectively. The Unit value is `()`. See [retired type spellings](type-model.md#retired-spellings). |
| Ordinary bit literals `false` and `true` | Use `0` and `1`, respectively. |
| Functions, module paths, imports and explicit static specialization | Kept. Declare the edition in the owning manifest. Both loaders use the same [declaration resolution](#declaration-resolution). |
| `[static n: Nat]`, `Op` parameters and `requires` | The parameter marker is `const`. Numeric predicates and capability requirements share one clause. See [retired spellings](static-language.md#retired-spellings) for each capability name. |
| `if static` and static folds with `carry` and `yield` | Static selection is kept. Use `for static` for an ordinary carry and `qfor static` for a carry containing a quantum owner. Both folds thread the written carry in order. See [static branches and folds](static-language.md#static-branches-folds-and-termination). |
| Runtime `if` and coherent `qif` | Kept. The former branches on an ordinary bit. The latter elaborates coherent control and preserves relative phase. See [runtime control](static-language.md#finite-runtime-control-and-resources). |
| `split`, `join`, `take_bit`, `put_bit` and access to a register place | The structural primitives are kept. An indexed or sliced `excl` call elaborates to ordered partition, application and reassembly. See [static ordered-axis places](elaboration.md#static-ordered-axis-places). |
| `adjoint`, controlled application and static repetition | Use the operation description followed by application. For example, `repeat_static(n,U,q)` becomes `power(U,n)(q)`. The [operation spelling table](static-language.md#retired-spellings) maps each retired constructor. |
| `basis fn` and `do p <- q; pure e` | Renamed to `classical fn` and replaced by `basis q as p { e }`, respectively. The latter elaborates a checked coherent basis map. See [coherent notation](#the-coherent-notation). |
| `meaning`, `bind_op(F,M)` and `apply_contract(F,S,q)` | Meaning declarations and function contracts are kept. Use `checked_op(F,M)` for the retired binding constructor. See [checked operations](checked-operations.md) and [function contracts](elaboration.md#function-contracts). |
| `with_computed` | Kept. Its checked expansion computes, uses and uncomputes the workspace. Migrate argument-list predicates to an explicit [predicate domain](#predicate-domains). |
| Qualified gate, preparation, measurement, reset and discard names | Use the [primitive and library name mapping](primitive-boundary.md#retired-qualified-names). Reset in `std::state` consumes the old owner and returns a fresh zero owner. |

The [elaboration whitelist](elaboration.md#whitelist) gives the targets of
individual expansions. The [selected-entry commands](type-model.md#selected-entry-commands)
give the CLI migration for programs that select a module, entry and static arguments.

### Rejected source

The table gives the replacement for each source form that the common scanner,
parser and judgment reject.

| Rejected source | Replacement |
| --- | --- |
| Bare CR, form feed, or a forbidden character inside a comment | Ordinary space or tab, LF or CRLF. Remove forbidden controls. |
| A self-import | Use the declaration of the module directly. An ordinary import-only cycle needs no source repair. |
| A runtime binder that shadows an active static name | Rename the binder |
| A reserved word as an identifier | Rename the identifier |
| Misplaced documentation | Move it to its module or declaration attachment boundary |
| A legacy `with_computed` predicate `p(a: A, b: B)` | `p((a,b): (A,B))` for a `Q<(A,B)>` register |
| `do p <- q; pure e` | `basis q as p { e }` |

### Predicate domains

A legacy `with_computed` predicate listed the parts of its register as
separate parameters. A migrated predicate takes the register as one
parameter with an explicit pattern.

Rules:

- Both finite `with_computed` forms require the
  [explicit predicate domain](type-model.md#predicate-domains-and-argument-lists).
- For three or more parameters, write the exact tree of the register. The
  legacy fold was left-associated.
- A `Q<Unit>` predicate takes an explicit Unit parameter.
- Ordinary calls keep their argument-list arity. Update any ordinary caller,
  or provide a separate unary wrapper.

### The coherent notation

The retired notation `do p <- q; pure e` becomes `basis q as p { e }`.

Rules:

- The migration to `basis q as p { e }` preserves the input expression, the
  complete pattern and the single basis expression.
- The braces delimit the restricted basis-expression grammar. They do not
  delimit an ordinary statement block.
- The migration does not join separate owners, allow outer runtime captures,
  remove injectivity checking or prepare a state.
- Both loaders use this one parser. A profile cannot retain the retired
  notation as an alias. [Coherent basis maps](coherent-basis.md) specifies the
  semantics, the diagnostics and the concrete-profile limits.

### Identities and edition

Rules:

- Supported ordinary siblings share one module. Mutual recursion is rejected.
- Source-bearing artifact identities change when embedded source changes.
- These migrations do not change edition 2026. The edition names the
  constitutional regime, and release compatibility records these source
  changes.

## Status and limits

This section gives the limits of the implementation, the state of the
concrete profiles and the proof status.

### Limits

The loaders, the parser and the common judgment each stop at fixed limits:

| Limit | Value | Applies to |
| --- | --- | --- |
| Supplied modules | 1 through 56. The eight bundled modules count toward the 64-module ceiling. | Selected loader |
| Source bytes | 64 KiB for each module and 1 MiB in aggregate. The bundled modules count toward the aggregate. | Selected loader |
| Tokens | 10,000 non-EOF tokens | Selected loader |
| Block-comment depth | 64 | Selected loader |
| Recursive syntax, runtime tree and type tree | 64 levels | Common parser |
| Tuple fields | 64 | Common parser |
| Natural-expression depth | 128 | Common parser |
| Work of the common judgment | 1,000,000 | Common judgment |
| Type size of one value | 4096 cells and depth 64 | Common judgment |
| Retained-scope cells | 16,384 | Common judgment on the selected-entry route |

- Comments and EOF do not consume the token allowance. The first token beyond
  the allowance is rejected before its owned text is allocated.
- The project loader processes comments iteratively, without a depth limit.
- Source-byte limits and aggregate project limits are separate entry-point
  policies. The finite bounded byte-loading policy and the explicit legacy
  byte-loading policy are separate. The common source collection does not
  make an unbounded byte loader bounded.
- The common judgment charges work before it performs the corresponding
  operation. It charges for visits, for the type and lexical cells that it
  allocates and copies, for normalized arithmetic and for solver work.
- The project route keeps its aggregate, type and snapshot capacities. The
  retained-scope limit does not apply to it.
- Both loaders charge all original bodies and bundled sources. A symbolic
  input can therefore reach the common work capacity before an inner solver
  limit.
- Concrete elaboration, evidence, native work and the loader and parser
  limits are separate.
- A program that exhausts a limit is rejected. The rejection is not a
  discharged quantitative Resource Safety certificate, and it is not evidence
  that the mathematical obligation of the program is false.
- These are engineering limits. They are not the constitutional quantitative
  Resource Safety theorem.

> **Implementation note.** The selected loader reports a scanner or parser
> refusal with the code `limit` when its message starts with `source exceeds`
> or contains the word "limit". This covers the token limit and the nesting
> limits. It reports every other scanner or parser refusal with the code
> `parse`.

### Loading, resolution and projection

The common judgment establishes facts about source. Whether a concrete
profile can lower a program, and whether the native checker accepts the
result, are separate questions.

- Source facts, concrete capability and independent native acceptance are
  separate responsibilities.
- Lowering integration is unfinished. Three further pieces of work are
  separate and also unfinished: retirement of the selected lowering
  projection, canonical generic `std` APIs and source-preservation proofs.
- The Finite project profile may refuse to materialize a source definition
  with a decreasing self-call under its concrete profile.

### Nominal types and ordinary match

This subsection says which native check each kind of program with nominal
types goes through, and what is unfinished.

- The Finite project adapter executes eligible closed ordinary callers through
  the strict ordinary-v2 check. This includes ordinary parameter functions
  that the common emitter inlines.
- A nongeneric public selected root that is an ordinary runtime root or a
  classical root uses that same emitter and native check. It does so after a
  fresh, complete judgment of the original source.
- Small quantum temporaries use the same Raw emitter and complete
  hidden-history checks.
- Mixed interfaces use the separate runtime-v2 check with full original type
  and storage trees. This includes nominal quantum ports and selected Basis
  and Nat arguments.
- Ordinary generic dependencies use the same source emitter.
- Operation-formal transport, full qmatch and nominal finite-table consumers
  are unfinished.
- The ordinary-v2 check separately binds the actual signature and
  recursive-field type paths, the nominal origins and the complete input and
  result storage.
  Validating an unused helper grants no source-row coverage.
- The ordinary-v2 and runtime-v2 checks reuse the original runtime body
  reader for additional type provenance. The reader keeps resolved original
  type paths and checks nominal declarations and member visibility. The v5
  source check also checks the original body.
- An explicit Rust carrier adapter checks without executing. It uses the same
  complete judgment and source lowering to check an exact logical matrix
  that is requested independently. Its sealed typed result grants no
  ordinary execution. The linked type model describes its precise scope and
  its open AST-preservation duty.
- Common frontend facts alone provide no execution evidence and no accepted
  handle. A host Basis description alone grants no execution authority.
- Nominal elaboration checks the original bytes. That check is not a general
  source-preservation theorem. It is not the pending binding of source to
  native evidence and cache.
- The parsed declarations do not complete finite algebraic data types.

The [type model](type-model.md#opaque-basis-specialization-in-the-selected-profile)
and the [production boundary](production-boundary.md#mixed-runtime-root-requests)
specify the distinct capacities and the checked scope.

### Classical declarations

This subsection says how a runtime call of a classical function executes in
the concrete profiles.

- Supported Unit, Bit and product runtime calls, and exact closed
  empty-register runtime calls, lower their original expression nodes through
  ordinary operations in both concrete consumers. Ordinary execution does not
  evaluate a precomputed truth table.
- Nonzero finite register indexing executes through the Raw profile.
- Selected Raw supports bounded complete label maps. General Selected
  hierarchy coherent-lift conversion keeps its separate profile refusals.

### Runtime branches and effects

A concrete profile can refuse a program that is valid as source. Such a
refusal is a limit of the profile. It is not an error in the source.

- The Finite project profile supports runtime ordinary branches.
- Selected elaboration can reject such a runtime expression as unsupported
  during preparation (`unsupported`). It must not turn the expression into an
  unchecked body or a runtime failure path.
- This profile restriction is separate from the language contract. It is
  also separate from the shared judgment of ownership and effects on the
  original body.
- Nongeneric public selected roots that use the common emitter execute an
  ordinary `if` on a measured Bit.
- A concrete profile may refuse a contract that is valid as source. The
  observing FunctionEquality profile requires genuinely observing original
  artifacts. A conservative Observe annotation on a pure body therefore
  cannot select a pure-contract fallback.
- Such a refusal discloses a concrete-profile limit. It is not a false pure
  label, a source effect error or a general preservation theorem.

### Coherent selection

The common judgment accepts every arm form on every route. The checks behind
it differ:

| Check | Selections | Limits |
| --- | --- | --- |
| Encoded-contract check of the whole circuit | Selections with built-in selector and target interfaces | Six joined selector and target bits, and 1024 circuit steps |
| v5 source check on the selected-entry route | Supported coherent selections, including built-in ordinal selectors | Six physical bits for each owner, 1024 circuit steps and the shared exact-work budget |
| Selected hierarchy projection | None. It refuses `qmatch` (`unsupported`). | — |

Arm forms:

- The Finite project profile lowers two arm forms: the name of a function,
  and an operation formal that the specialization binds.
- The Selected Raw profile lowers those forms and two more: a constructed
  static operation such as `checked_op(sign, Sign)`, and an inline block.
  The tests of constructed arms and of block arms run on the selected-entry
  route.
- For a nominal target, an arm must name a declared function without static
  parameters. A function with static parameters is refused (`unsupported`):
  instantiate it in an ordinary wrapper. A constructed static operation is
  refused (`unsupported`).
- On the v5 source route, a constructed arm for a built-in target must resolve
  to an original function-evidence entry (`unsupported`).

Route selection:

- Selected Basis and Nat roots and their ordinary callers use the common
  emitter for the built-in slice. Before lowering, named arms obtain their
  original checked provider bodies through the native evidence checks. This
  includes arms in inactive static branches.
- The next rule applies when `--ir-profile` has the value `raw` or `auto` and
  no independent hierarchy request exists. The CLI then selects this route
  from the original `qmatch` occurrences in the lexical dependency closure
  of the entry. An unrelated `qmatch` declaration or a comment does not
  redirect a built-in entry.
- The selected CLI and the Rust API prefer the v5 source check for supported
  coherent selections, including built-in ordinal selectors.
- When the v5 source check is optional, these forms keep the typed
  runtime-root check: register primitives, access calls, function contracts,
  ordinary matches, static folds and computed bodies. Optional v5 checks
  cover selected static blocks with Hadamard, phase, global phase and
  coherent selection events.
- The compiler chooses the route from the original lowered body before it
  submits a request. A selection that requires the v5 source check goes
  through it.
- A failed check never triggers a different acceptance path.

Small nominal enum selectors:

- They use the shared emitter for one shape of function. The function is
  nongeneric and named. It has quantum parameters, a flat result of quantum
  owners and a structural body that contains one or more selections with
  named arms.
- A target may be a built-in basis, a fieldless enum or a finite record,
  including an empty record. A built-in ordinal selector may also select a
  nominal target.
- Original names, tuple bindings and the complete structural return may
  surround the selections. Additional quantum arguments stay in the complete
  original frame.
- Parameter order and result order may differ. The original source return
  determines the result order, including distinct zero-width owners.
- Public Isometry and Observe annotations are the outer contract even when the
  selected operation is pure.
- An ordinary caller may retain other owners. Only the actual callee fragment
  is submitted for its original function, and the complete runtime root passes
  its independent typed check.
- General expressions and nonstructural prefixes and suffixes are unsupported
  on this route. No source text or owner frame is synthesized to avoid a
  refusal.

Each actual call fragment passes the v5 source check with its original input
and output owners and every emitted operation:

- Each original selection binds a literal, contiguous Raw interval and its
  actual owner frame. All intervals cover the complete emitted call in source
  order.
- Each interval passes its own exact equations even when successive
  operations cancel. Whole-body cancellation cannot replace the exact action
  or the owner-frame obligation of any interval.
- A built-in target arm provides its function evidence.
- A nominal target arm submits its original physical body and a proposed
  controlled implementation through the same QIRF encoder. The native check
  binds the full original target type and checks its actual code, body and
  controlled equations. The physical entry alone grants no operation capability.
- A wider literal interval goes through the original source and arm checks
  and a separate sector reconstruction. Acceptance uses the shared exact-work
  budget.

The v5 source check has these components:

| Component or case | What it checks |
| --- | --- |
| Finite restriction component | It proves correspondence through actual contributions, accumulation, steps and complete circuit execution, and it checks every ordered local sector. |
| Forward arms | For a forward arm with a checked full-width circuit tape, the checker reconstructs its exact columns from the original events and checks the physical Gram condition. Arms with other original event forms use the instrument evaluator. |
| Internal Raw component | It checks the original pure program and an independently reconstructed trace. It retains every circuit event and proves that omitted identity reorders are literal identities. It checks the physical port and wire frame separately from logical source owner transport. Empty wire lists alone cannot identify or order zero-width owners. Physical widths do not establish original nominal or source type identity. |
| Enclosing QIRF component | It reuses fresh graph and root checks and proves exact original-program embedding into that pure Raw subject. It rejects observing, classical and branch instructions in this straight-line component. |
| Internal nominal component | It independently checks original type declarations and the code of each ordered owner. It then compares each active physical sector on that code with the exact requested logical map. Product labels keep their actual physical coordinates. Padding sectors are checked separately and do not increase logical cardinality. The requested-sector checks and the computed-sector path share one reconstruction. |
| Internal arm component | It reconstructs the logical map of each original QIRF implementation and checks a separate controlled implementation against exact identity and arm sectors. One fresh graph checks the main subject plus all actual arm and control subjects that the request names. Root membership comes from those subjects. Unrelated nodes are refused, and root membership supplies no source usage. Ordinary requests keep their main-only root and reachability rules. Every canonical logical ordinal binds its actual original arm, independently of written order. |
| Source component | It binds original named functions to actual function-evidence entries and their fresh complete inputs and dependency snapshots. It preserves the original function bytes, the full target types and the public effects. |
| Source metadata component | It retains the actual `qmatch` token occurrence in its original function, the complete named-arm parameter and result owner forests, the canonical enum labels and the original import and reexport paths. It rejects public observing or isometric arms and keeps an absent private annotation unknown. Body checking must independently establish the inferred effect. |
| Source frame | Original quantum parameter patterns and structural let and tuple moves identify operands in the complete live source frame. Quantum product owners are atomic, and ordinary tuples can group separate owners. A two-port subject keeps the exact original parameter and result order and distinct logical identities at zero width. It cannot sharpen a public observing or isometric function to Unitary. Unknown prefix expressions are refused instead of contributing unproved type facts. |
| Context reader | It checks direct `h`, `global_phase_eighth` and finite `phase[j,k]` events around named-arm selections. It traverses runtime call arguments first, keeps the original callee token and the `qmatch` keyword through grouping and comments, and compares every event with its literal Raw interval. Original lexical, module and prelude lookup establishes primitive identity. |
| Structural suffix and result | They keep the actual returned roles. An independent run over original Raw joins, splits and owner-moving operations compares those roles with the actual output-token order, including at zero width. A matching zero-width permutation of source and Raw is allowed, and a mismatched one is refused. |
| Native and QDV component | It retains its actual graph and request, and it grants no ordinary source execution handle on its own. The bounded compiler adapter checks that component before the separate runtime-root acceptance. |

The context reader applies these rules to the source around a selection:

- Closed phase parameters and body-local `static let` initializers use
  original Nat syntax and lexical lookup.
- Every ordinary caller intermediate and helper argument must fit u32,
  including unused initializers and ignored arguments. Original static helper
  bodies keep their checked signed-affine rules.
- An alias keeps the helper resolution and the lexical environment of its
  initializer. A runtime pattern cannot shadow an earlier static alias,
  including an unused alias.
- The finite phase rule requires `k <= 8`, `j < 2^k` and an exact multiple of
  one eighth, without rounding and without a replacement modulo-one
  normalization.
- These context checks themselves add no transport of generic caller
  arguments and no constructed-arm support. The arm forms above state what
  each profile lowers.

Open work:

- Validation of the full twelve-joined-bit and 64-label boundary is open.
- Opaque-owner refinements, allocation and release, and general calls and
  control flow need their checked source and representation rules.
- General source binding and nominal integration are unfinished. Ordinary
  nominal execution uses the separate ordinary-v2 check.

### Proof status

The statements below separate what a check establishes from what is proved.

- The failure contract is a totality requirement. It is not a claim that
  every source form or target has a completed production Soundness proof.
- The Rust simulator and native IO keep their disclosed correspondence
  assumptions. The core failure contract does not prove host panic freedom.
- Ordinary native validity checks its stated structural ownership and
  classical-scope properties. General EffectSound/CPTP and source preservation
  are unfinished.
- The dedicated
  [original-artifact instrument request](production-boundary.md#original-artifact-observing-instrument-requests)
  checks both original bodies, the complete Kraus sums, the requested complete
  signature trees and their ordered root-port projections. It checks every
  unnormalized public map on arbitrary finite references within its bounded
  profile. Recovering the original source type trees is a separate
  obligation.
- That profile requires genuinely observing original artifacts. A
  conservative public Observe bound on a pure implementation can therefore be
  well typed while this request refuses it. The refusal supplies no
  pure-contract fallback.
- The postselection boundary does not discharge ordinary-root
  EffectSound/CPTP, source and runtime preservation or the broader QS, PR,
  quantitative RS and EXACT obligations.
- For coherent selection, three things do not prove original-source
  preservation or complete nominal integration: common enum checks, native
  acceptance of a proposed circuit and conformance tests.
- Source effect facts and the source facts of the common judgment are not
  accepted IR handles and not a source-preservation proof.

### Tests

The [repository](https://github.com/MGYamada/Qleisli) keeps these packets of
bounded migration evidence:

| Packet | Content |
| --- | --- |
| `tests/fixtures/frontend_v030/shared-scanner/` | The original byte fixtures and the CLI diagnostics before and after the common scanner. The two successful small source pairs emitted identical untrusted proposal hashes. |
| `tests/fixtures/frontend_v030/common-parser/` | Ten initial source observations, independent review counterexamples, exact commands and results, and four small before and after proposals with identical bytes. It also records the shared-depth edge of the recursion budget. |
| `tests/fixtures/frontend_v030/shared-resolution/` | The ten original profile observations of the resolver, 25 matching command results and five identical small proposals, including distinct same-named providers and decreasing self-recursion |
| `tests/fixtures/frontend_v030/lexical-resolution/` | The subsequent shared local and static binding comparisons |
| `multi-declaration/` and `sized-declarations-independent/` | Original rejected siblings, their declared acceptance and diagnostic changes, and independent small phase and axis comparisons of split-module and same-module programs |
| `tests/fixtures/frontend_v030/predicate-domain/` and `predicate-domain-independent/` | The earlier diagnostics, explicit translations, small proposal comparisons and independent phase and reference checks |

- The sibling extension leaves the single-declaration observations and six
  small proposal byte sequences unchanged. Source that the extension accepts
  undergoes its native check.
- Earlier failed sources and results are historical evidence.
- These packets are bounded migration evidence. They are not a general
  source-preservation proof, a formal guarantee or a native acceptance claim.

## History

- This chapter describes the scanner and the parser of `0.3.0-beta`.
- The common frontend is the decision of
  [Issue #32](https://github.com/MGYamada/Qleisli/issues/32): one scanner,
  token stream, parser and source representation for finite project loading
  and sized explicit module loading. That Issue also tracks the unfinished
  lowering integration.
- Retirement of the selected lowering projection, canonical generic `std`
  APIs and source-preservation proofs are separate work in
  [#32](https://github.com/MGYamada/Qleisli/issues/32) and
  [#317](https://github.com/MGYamada/Qleisli/issues/317).
- [#58](https://github.com/MGYamada/Qleisli/issues/58) tracks the prelude and
  import integration and its conformance evidence.
- `enum`, `struct`, `match` and `qmatch` became reserved keywords in the
  unpublished beta language. The parser changes do not complete
  [finite ADTs](https://github.com/MGYamada/Qleisli/issues/64).
- The effect vocabulary "isometry" was selected in
  [#57](https://github.com/MGYamada/Qleisli/issues/57). The source prefix
  `iso` was retired in 0.3.0, and the Rust variants `Effect::Iso`,
  `FnKind::Iso` and `TokenKind::Iso` were renamed with it.
- `basis fn` was replaced by `classical fn`, and the `do p <- q; pure e`
  expression was removed. Historical first sources and validation records
  keep their original spelling. Replay selects explicitly recorded
  derivatives.
- The statement that Qleisli provides no source postselection effect was
  written for Qleisli 0.3.0.
- The common grammar reserves words in identifier positions that the sized
  parser had treated contextually.
- The sized scanner before the common scanner skipped bare CR, form feed and
  forbidden characters inside comments. It already rejected vertical tab; the
  shared character rule supplies that diagnostic.
- The common parser reaches its nesting limit one level earlier than the
  removed sized parser for certain deep sized natural types. The project
  loader received no comment depth limit.
- The one-function restriction of sized source was removed. Legacy sources
  could contain self-imports, and an import-only cycle needed a source repair
  before the common resolver.
- After the common judgment, a source type, owner, access or dependency error
  can precede a profile refusal that an earlier release reported first.
  Earlier sources and diagnostics are historical records.
- `ResolvedImport.kind` replaced a bare `FnKind` in the Rust `Project` view.
- In the v5 source check, the computed-sector path was added by a refactor
  that preserved all earlier results, errors and open work. The source
  metadata component and the source-frame identification of operands are
  additions to the earlier form of that check.
- The explicit predicate domain of `with_computed` replaced the legacy
  argument-list predicate form.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
