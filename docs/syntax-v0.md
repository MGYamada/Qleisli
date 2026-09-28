<a id="qli-表層構文-v0"></a>

# `.qli` surface syntax v0

Status: **normative grammar for finite core v0** (2026-09-26). This document
specifies the lexical rules, grammar, names, and scopes of the
[v0 language specification](language-spec.md). Read it with the
[module rules](standard-library.md). Syntactic acceptance, acceptance of types,
effects and evidence, and execution within implementation limits are distinct.
The [conformance record](specification-status.md) tracks their status separately.
This English edition is authoritative and replaces the earlier Japanese edition.
This revision extends v0 with patterned coherent-lift binders and runtime
`CBit` literals and Boolean expressions. It reserves `true` and `false`, a source
compatibility change described below. The import-path grammar and Unicode
comment policy clarify existing parser behavior.

The later finite-contract extensions add the three-argument computed form
and [`apply_contract`](function-contracts-v0.1.md). The latter reserves a new
keyword; source identifiers with that spelling must be renamed. Their exact
evidence requirements and capacity limits are separate from parsing.

The 2026-09-28 [documentation-comment extension](documentation-comments.md)
adds Rust-style line/block documentation and nested ordinary block comments.
It is retained in product 0.1.6 by the user's explicit version-policy exception.
Attachment and line-ending changes have migration guidance in that specification;
docstrings carry no quantum meaning or evidence authority.

The 0.1.8 [fixed-width operation supplement](next-minor-spec.md) additionally
specifies meaning declarations, static parameters/arguments, access constraints
and operation constructors. These are language forms, not runtime values or
sealed gates. Their complete normative productions and reserved words are in
that supplement; they extend the base EBNF below. Follow its source/Rust
migration and exact checking rules. `adjoint`, `repeat_static` and `qif` also
accept eligible static parameter names with the corresponding declared access.

<a id="構文と組み込みの境界"></a>

## Boundary between syntax and built-in operations

| Notation | Classification | Types, ownership, and effects | IR translation |
| --- | --- | --- | --- |
| `//`, `/* ... */`, `///`, `//!`, `/** ... */`, `/*! ... */` | Lexical language forms; documentation metadata where marked | No value type, ownership, effect or proof authority. Doc comments have independently validated syntactic attachment. | Ordinary comments disappear; doc text is available through a sidecar API and emits no IR. |
| `use`, `pub`, the four kinds of `fn`, `let`, `if` | Language forms | `basis` declares a total finite basis function; `iso` a pure isometry; `unitary` a pure unitary; `observe` permits observation. `let` rebinds linear ownership, and `if` branches exclusively on a `CBit`. | Resolve declarations/imports; represent `let` by SSA bindings and `if` by `ClassicalBranch`. |
| `do p <- q; pure e` | Language form | Consume `q:Q<A>` once. Match the name/wildcard/tuple pattern `p` against the exact basis tree `A`; its names are coherent basis labels, not measurements. Produce `Q<B>` only when `e:B` defines a total injection over the whole input basis. | Destructure each finite input label according to `p`, check the full table, and emit `LiftBasis`. |
| `true`, `false`, `not e`, `e1 and e2`, `e1 xor e2` | Language forms | Literals return `CBit`; Boolean operators require and return `CBit`. They have own effect `Unitary` and preserve quantum ownership themselves. Evaluate operands eagerly from left to right, retaining their effects and resource transitions. | Emit classical SSA `ClassicalConst`, `ClassicalNot`, `ClassicalAnd`, or `ClassicalXor`; independently verify input visibility and fresh outputs. |
| `with_computed(q, f) { \|a\| body }` | Language form | Require `q:Q<A>`, a total `f:A -> Bit`, and temporary `a:Q<Bit>`. The body returns that temporary ownership and, after ordinary call expansion, contains only an auxiliary `Z/T` chain or an empty chain. The outer result is the original `Q<A>`. | Emit one certified `ComputeUseUncompute`; never emit a standalone `Release0`. |
| `with_computed(q,f,u) { \|d,a\| body }` | Language form | Consume `Q<A>` once, expose private data/auxiliary ownership, return both in order, and check `W Ef=Ef u` for a fixed logical unitary. Return `Q<A>` with own effect `Unitary`. | Retain actual W, f, and u in independently checked `CertifiedCompute`. |
| `apply_contract(implementation,specification,q)` | Language form | Both names denote ordinary declared unitaries with exactly `Q<A>->Q<A>`. Evaluate q once, consume and return its ownership, and require exact operator equality. Join q's effect with `Unitary`. | `ApplyUnitary` contains a retained `CircuitAction::Contract` with immutable independently checked function evidence. |
| `adjoint(u,q)`, `repeat_static(n,u,q)` | Language forms | Invert or finitely repeat a statically resolved unitary with identical input/output type. Consume and return the quantum ownership once. | Translate to `ApplyUnitary` and independently reverify, following the [finite static-operation rules](static-operations.md). |
| `qif(c,q) { 0 => u0, 1 => u1 }` | Language form | Consume and return both control and target. Require distinct ownership and static unitary branches with the same input/output type. | Emit flat controlled `ApplyUnitary` steps, preserving branch phases. |
| `init0`, gates, `split/join`, `measure_z/reset/discard` | Sealed built-in operations | Follow the [public contracts](standard-library.md). Observation operations have effect `observe`; `measure_z` returns only `CBit`. | Resolve the public names to IR constructors with fixed meanings. |
| `xor2`, `and2`, `s`, `measure_x`, and similar helpers | Ordinary `.qli` definitions | Apply the same type, effect, and ownership rules as for user definitions. | Check each body and translate calls or their expansion to IR. |

`Q<A>` is an ownership type; `iso` and the other classifications above are
static function effects. `Iso<A,B>` and `Unitary<A,B>` are not first-class value
types. Earlier documents' `lift(e)` denotes the meaning of `LiftBasis`; the v0
surface form introducing it is `do x <- q; pure e(x)`. A direct `lift(e)` source
form is not part of v0.

<a id="字句と文法"></a>

## Lexical rules and grammar

A `.qli` file is UTF-8. Identifiers are ASCII
`[A-Za-z_][A-Za-z0-9_]*`, excluding the reserved words below; `_` alone is
reserved for wildcard patterns. Token-separating whitespace is limited to
ASCII space, tab, LF, and CR. A `//` comment ends at LF or end of file; block
comments nest. `//!`/`/*! ... */` document the containing module/function and
`///`/`/** ... */` the following supported item, under the
[attachment rules](documentation-comments.md#lexical-forms-and-attachment).
Doc text normalizes CRLF to LF and rejects bare CR; ordinary line comments no
longer end at bare CR. Diagnostic spans retain original UTF-8 byte offsets.
The grammar below describes executable tokens after comment extraction;
documentation attachment is checked separately before parsing succeeds.

The following characters are forbidden both inside and outside comments:

- Bidirectional controls U+061C, U+200E, U+200F, U+202A–U+202E, and
  U+2066–U+2069.
- Unsupported line separators U+000B (VT), U+000C (FF), U+0085, U+2028, and
  U+2029.
- Other Unicode whitespace, except the four ASCII separators listed above.
- Other control characters in Unicode's `Cc` category, except tab, LF, and CR.

Other Unicode characters are permitted in comments. This includes ordinary
non-ASCII text and format characters such as U+200B and U+FEFF; v0 does not ban
all characters in Unicode's `Cf` category. These two characters do not terminate
a comment. Outside comments, neither is a valid token or separator, so each is
rejected as an unexpected character. In particular, a leading U+FEFF byte order
mark (BOM) is rejected rather than stripped. Non-ASCII identifiers are not
permitted.

The base reserved words are `use`, `pub`, `basis`, `iso`, `unitary`, `observe`, `fn`,
`let`, `if`, `else`, `do`, `pure`, `with_computed`, `adjoint`, `repeat_static`,
`qif`, `apply_contract`, `true`, `false`, `not`, `xor`, `and`, `Unit`, `Bit`, `CBit`, and `Q`.
The M1 supplement also reserves `meaning`, `static`, `Op`, `requires`,
`Apply`, `Adjoint`, `Controlled`, `permutation_by`, `phase_by`, `bind_op`,
`inverse_op`, `then_op`, `tensor_op`, `controlled_op`, `repeat_op`, and
`conjugate_op`; rename colliding identifiers, including module components.
The only basis `Bit`
literals are `0` and `1`. A decimal natural number is allowed only in the count
position of `repeat_static` or M1 `repeat_op`, with no leading zero except for `0` itself. The
current implementation profile accepts counts from 0 through 4,096 and diagnoses
larger counts. A consecutive run of digits is one token, so `10` and `2` remain
invalid basis literals. Strings, floating-point numbers, arrays, general
recursion, and user-defined operators are outside v0.

The newly reserved words `true` and `false` can no longer be used as declaration,
parameter, binding, import, or module-component names. Existing source that used
either as an identifier must rename it; neither keyword is a basis `Bit` literal.
The basis literals `0` and `1` remain distinct from the ordinary `CBit` literals.

To protect its stack, the Rust parser imposes a depth limit of 64 on recursive
syntax, patterns, and basis or runtime expression trees, including
left-associated Boolean chains. This is an implementation
limit, not a limit on the language's mathematical meaning; exceeding it produces
a located diagnostic.

The notation below is EBNF-like: `*` means zero or more repetitions, `?` means
optional, and `|` separates alternatives. Quoted terminals are literal source
characters or words. `Ident` is a nonreserved identifier other than `_`; `Name`
is one such identifier visible in the current module. `Digit` is an ASCII
character from `0` through `9`, and `NonzeroDigit` from `1` through `9`.
Statements end with semicolons; a block's final expression does not. Parameter
lists, argument lists, tuples, and `qif` branches do not permit trailing commas.

```ebnf
Module       ::= (Use | Decl)*
Use          ::= "use" Path "::" Ident ";"
Path         ::= Ident ("::" Ident)*
               | "std" "::" ("basis" | "observe") ("::" Ident)*
Decl         ::= "pub"? (BasisDecl | QuantumDecl)
BasisDecl    ::= "basis" "fn" Ident "(" BasisParams? ")"
                 "->" BasisType BasisBlock
QuantumDecl  ::= Kind "fn" Ident "(" Params? ")" "->" Type Block
Kind         ::= "iso" | "unitary" | "observe"
BasisParams  ::= BasisParam ("," BasisParam)*
BasisParam   ::= Ident ":" BasisType
Params       ::= Param ("," Param)*
Param        ::= Ident ":" Type
Type         ::= BasisType | "CBit" | "Q" "<" BasisType ">"
               | "(" Type "," Type ")"
BasisType    ::= "Unit" | "Bit" | "(" BasisType "," BasisType ")"
ClassicalType ::= "Unit" | "CBit" | "(" ClassicalType "," ClassicalType ")"
Block        ::= "{" Stmt* Expr "}"
BasisBlock   ::= "{" BasisExpr "}"
Stmt         ::= "let" Pattern "=" Expr ";" | Expr ";"
Pattern      ::= Ident | "_" | "(" Pattern "," Pattern ")"
Expr         ::= RuntimeXor
RuntimeXor   ::= RuntimeAnd ("xor" RuntimeAnd)*
RuntimeAnd   ::= RuntimeUnary ("and" RuntimeUnary)*
RuntimeUnary ::= "not" RuntimeUnary | RuntimeAtom
RuntimeAtom  ::= Name | "true" | "false" | "()"
               | "(" Expr ")" | "(" Expr "," Expr ")"
               | Call | If | CoherentLift | WithComputed | Adjoint | Repeat | Qif
               | ApplyContract
ApplyContract ::= "apply_contract" "(" Name "," Name "," Expr ")"
Adjoint      ::= "adjoint" "(" Name "," Expr ")"
Repeat       ::= "repeat_static" "(" StaticNat "," Name "," Expr ")"
StaticNat    ::= "0" | NonzeroDigit Digit*
Qif          ::= "qif" "(" Expr "," Expr ")"
                 "{" "0" "=>" Name "," "1" "=>" Name "}"
Call         ::= Name "(" Args? ")"
Args         ::= Expr ("," Expr)*
If           ::= "if" Expr Block "else" Block
CoherentLift ::= "do" Pattern "<-" Expr ";" "pure" BasisExpr
WithComputed ::= "with_computed" "(" Expr "," Name ")"
                 "{" "|" Ident "|" Stmt* Expr "}"
               | "with_computed" "(" Expr "," Name "," Name ")"
                 "{" "|" Ident "," Ident "|" Stmt* Expr "}"
BasisExpr    ::= XorExpr
XorExpr      ::= AndExpr ("xor" AndExpr)*
AndExpr      ::= UnaryExpr ("and" UnaryExpr)*
UnaryExpr    ::= "not" UnaryExpr | BasisAtom
BasisAtom    ::= Ident | "0" | "1" | "()" | "(" BasisExpr ")"
               | "(" BasisExpr "," BasisExpr ")"
               | BasisCall
BasisCall    ::= Name "(" BasisArgs? ")"
BasisArgs    ::= BasisExpr ("," BasisExpr)*
```

Only the second component of `std::basis` or `std::observe` may use those
declaration keywords as module names. All later components, the final imported
name, and local module components must be ordinary identifiers. The parser
retains further identifier components: for example, `use std::basis::a::b;`
is syntactically valid and denotes an attempted import of `b` from
`std::basis::a`. Parsing does not establish that such a module or declaration
exists; project resolution diagnoses unsupported standard modules or missing
names. This does not add nested standard modules to v0.

In both runtime and basis expressions, `not` binds more tightly than `and`,
which binds more tightly than `xor`. Both binary operators associate to the
left. Runtime Boolean operands are evaluated exactly once, eagerly from left to
right: `false and measure_z(q)` still measures and consumes `q`, and has effect
`Observe`. The operator's effect joins all operand effects; `and` does not
short-circuit. `if` remains the form that conditionally executes an arm.
Call arguments are evaluated from left to right; a `let` evaluates its
right-hand side before binding the result.
Function-body statements run in source order. An `if` evaluates its condition
first and executes only the selected arm, although both arms are checked.
All functions are nonrecursive; repetition is a finite static expansion.
`repeat_static` checks its target even at count zero, so zero cannot hide an
invalid target body.

A `basis fn` takes and returns only `BasisType`, and its body is a total
`BasisExpr`. Literals `0` and `1` have type `Bit`; `()` has type `Unit`.
The primitive basis operations are `not : Bit -> Bit`,
`xor : (Bit,Bit) -> Bit`, and `and : (Bit,Bit) -> Bit`. These are total finite
operations, but a direct lift to `Q` separately requires the entire map to be
injective. For example, `basis fn and2(x: Bit, y: Bit) -> Bit { x and y }` is a
valid ordinary basis definition. The semantic domain of multiple basis
parameters is their product type; `with_computed(q, and2)` requires
`q:Q<(Bit,Bit)>`. A direct lift of `and2` on the whole quantum register is
rejected because that map is not injective.

Basis expressions can construct and pass tuples. A coherent lift can
access their components by binding a name/wildcard/binary-tuple `Pattern` after
`do`. Pattern shape must match the input basis tree exactly; all names in one
pattern must be distinct. `_` ignores a basis label, not quantum ownership.
The lift still consumes one whole quantum input and checks totality and
injectivity of the map on its **entire** basis. For example,
`do (a,b) <- q; pure (a,xor2(a,b))` defines an injective update on a two-bit
basis, whereas `do (a,b) <- q; pure xor2(a,b)` alone is noninjective.
There is no `()` pattern; use `_` or a name for a `Unit` component. Basis
function parameters remain individual names, and a basis body has no `let`
statements or projection/indexing operator.

The basis expression following `pure` extends through its complete basis
operator expression. Parentheses close that expression before an enclosing
runtime operator; for example, `(do p <- q; pure e)` explicitly delimits the
lift. Runtime operators accept `CBit` operands, so applying one to that lift's
`Q<B>` result fails type checking.

Runtime classical literals are `false : CBit` and `true : CBit`.
`not : CBit -> CBit`, `and : (CBit,CBit) -> CBit`, and
`xor : (CBit,CBit) -> CBit` have their Boolean truth-table meanings. These are
source expression forms, not callable standard-library function names.
They compute classical SSA values, perform no observation themselves, and do
not read quantum basis labels. A `CBit` can also be supplied as an ordinary
function argument or produced by observation, then copied, returned, used in a
Boolean expression, or used as an `if` condition. Basis and runtime values do
not implicitly convert to each other.

The `Type` production intentionally accepts more syntax than the type-formation
rules accept in every role. Ordinary `iso`, `unitary`, and `observe` parameters
and results cannot contain a bare `Bit`. `Bit` occurs in basis signatures,
inside `Q<...>`, and as a coherent index in `do/pure`. There is no implicit
conversion from `Bit` to `CBit`. A comma-separated parameter or argument list
has its own arity; one tuple-valued argument is not multiple arguments.
Multiple result values use explicit binary tuples. Binding quantum ownership
to `_`, or discarding a quantum-valued expression with `Expr;`, is syntactically
expressible but rejected by resource checking.

`ClassicalType` describes the semantic restriction on a root `main` result.
It is a named subset of the types parsed by `Type`, not a separate production
selected while parsing a declaration named `main`. Declaration and entry-point
checking enforce this restriction after parsing, as specified below.

<a id="名前とスコープ"></a>

## Names and scopes

- Each file is one module, with a source-root-relative module name under the
  module rules. `use foo::bar::name;` binds the public declaration from
  `foo/bar.qli` as `name`. `std::` is reserved for the bundled standard library.
  Imports occur only at top level; there are no aliases, wildcards, reexports,
  relative import paths, or cyclic imports. An import/local-definition name
  collision produces a located diagnostic.
- The execution entry point is the unique `observe fn main() -> T` in the
  root's `main.qli`. `T` must satisfy `ClassicalType`, and no quantum ownership
  may remain at exit. A library does not need a root `main`.
- Function names resolve independently of declaration order, but the
  function-call graph must be acyclic. Ordinary calls have form `Name(args)`;
  operations are not ordinary argument values. Static-operation names resolve
  at compile time and contribute to that graph. The second operand of
  `with_computed` is a statically resolved **basis-function name**, not a runtime
  function value. In the finite semantic-contract extension, the third
  operand is an eligible unitary function name (ordinary or sealed H/X/Z/T), also resolved statically
  and included in the acyclic dependency graph. The [name rules](source-typing-rules.md#2-names-declarations-and-project-acceptance)
  specify when local names hide each kind of callable.
- Parameters and `let` bindings have lexical scope. In `let q = h(q);`, the
  right-hand side consumes the old `q` before the new `q` enters scope.
  Hiding a still-owned old quantum binding is an error. Quantum identity is
  tracked by ownership tokens and logical wire IDs, not by spelling alone.
- `apply_contract` evaluates its input expression before resolving both
  names in the residual environment. Live or spent local names hide the
  targets. Both must be ordinary declared unitary definitions with the exact
  single-register signature; a sealed gate must first be wrapped in such a
  definition. The two references participate in acyclic dependency checking.
  No caller values are captured by either function body. The
  [FC-SOURCE rules](function-contracts-v0.1.md#2-source-language-form) specify
  ownership, effects, exact phase, retained evidence, and rejection boundaries.
- Names introduced in an `if` arm expire outside that arm. The arms receive the
  same linear input context exclusively and must merge their result types and
  quantum ownership interfaces. The [merge rule](language-spec.md#7-古典分岐の合流)
  uses result positions, surviving frames, and outer consumption sets; IR `φ`
  interfaces also align wires newly allocated in an arm.
- The names introduced by a `do` pattern are **coherent basis indices** scoped
  over its one following `BasisExpr`. That expression's static context contains
  exactly those pattern bindings; it captures neither outer classical nor outer
  quantum values. Top-level basis functions remain callable. Consequently, an
  outer runtime value named `f` does not hide a basis function `f` within this
  isolated context, while any pattern binder named `f` does hide it. `pure` is
  neither a general return form nor a constructor for runtime classical values.
- The two-argument `with_computed` binder `a` is temporary `Q<Bit>` ownership scoped over its
  body. The source register is protected and inaccessible there, as are other
  outer quantum values; outer classical values remain usable. The body's final
  expression must return the updated ownership of that auxiliary. The
  [computed-scope rule](source-typing-rules.md#6-classical-and-coherent-control-repetition-and-computed-scope)
  masks outer linear bindings into a private frame before introducing `a`.
  The auxiliary may have the same spelling as a masked outer name without
  consuming or exposing that outer resource.
- The three-argument extension `with_computed(q,f,u){|d,a| body}` binds
  distinct private data and auxiliary owners. It captures no outer values,
  including classical values. Both names may shadow masked outer names.
  Return `(Q<A>,Q<Bit>)` in data/auxiliary order. The exact source types,
  unitary effect, ownership, and `W E_f=E_f u` are checked according to the
  [semantic-contract specification](semantic-contracts-v0.1.md).

<a id="構文受理と静的拒否の例"></a>

## Examples of syntactic acceptance and static rejection

These are **v0 acceptance/rejection examples** with imports omitted. See the
[frontend profile](frontend-v0.md) for complete executable projects and the
implemented type and ownership checks.

```qli
iso fn entangle(q: Q<Bit>) -> Q<(Bit, Bit)> {
    do x <- q;
    pure (x, x)
}

basis fn predicate(x: Bit) -> Bit { not x }
basis fn xor2(a: Bit, b: Bit) -> Bit { a xor b }

unitary fn xor_into(q: Q<(Bit,Bit)>) -> Q<(Bit,Bit)> {
    do (a,b) <- q; pure (a,xor2(a,b))
}

unitary fn classical_flag(a: CBit, b: CBit) -> CBit {
    not a and b xor true
}

unitary fn phase_oracle(q: Q<Bit>) -> Q<Bit> {
    with_computed(q, predicate) { |a| z(a) }
}

observe fn feedback(q: Q<Bit>, r: Q<Bit>) -> (CBit, Q<Bit>) {
    let b = measure_z(q);
    let r1 = if b { x(r) } else { r };
    (b, r1)
}

observe fn bell_result() -> (CBit, CBit) {
    let pair = entangle(h(init0()));
    let (left, right) = split(pair);
    let a = measure_z(left);
    let b = measure_z(right);
    (a, b)
}
```

Assume the appropriate `use` declarations for `z`, `measure_z`, `x`, `h`,
`init0`, and `split`. The map `x -> (x,x)` in `entangle` is injective, and
`z(a)` in `phase_oracle` preserves the protected auxiliary's basis label.
The arms of `feedback` use the same input `r` exclusively. `measure_z` consumes
the old `q` and returns only `CBit`. The two measurements in `bell_result`
consume both logical wires produced by `split`.

| Fragment | Syntax | Static decision |
| --- | --- | --- |
| `do x <- q; pure (x,x)` | Valid | Accept when `x -> (x,x)` is injective. |
| `do x <- q; pure 0` | Valid | Reject the noninjective constant map `Bit -> Bit`. |
| `do (a,b) <- q; pure (a,xor2(a,b))` | Valid | Accept for `q:Q<(Bit,Bit)>` and the total XOR basis function; the full map is injective. |
| `do (a,b) <- q; pure xor2(a,b)` | Valid | Reject for `q:Q<(Bit,Bit)>`: XOR alone loses one input bit and is not injective. |
| `do (_,b) <- q; pure b` | Valid | Accept for `q:Q<(Unit,Bit)>`; reject for `q:Q<(Bit,Bit)>` because ignoring a bit makes the full map noninjective. |
| `do (a,a) <- q; pure a` | Valid | Reject duplicate names in the basis pattern. |
| `true and not false` | Valid | Accept as `CBit` with effect `Unitary`; its value is true. |
| `false and measure_z(q)` | Valid | Accept for owned `q:Q<Bit>` in an `observe` context; consume `q` even though the classical result is false. |
| `not q` | Valid | Reject when `q:Q<Bit>`: a runtime Boolean operand must be `CBit`. |
| `unitary fn f() -> CBit { 1 }` | Invalid | `1` is a basis literal, not a runtime `CBit` literal. |
| `basis fn f() -> Bit { true }` | Invalid | `true` is a runtime literal, not a basis literal. |
| `let pair = (q,q); pair` | Valid | Reject duplicate use of the same quantum ownership. |
| `let b = measure_z(q); h(q)` | Valid | Reject reuse of the old `q` consumed by measurement. |
| `iso fn bad(q: Q<Bit>) -> CBit { measure_z(q) }` | Valid | Reject an `observe` effect inside `iso`. |
| `with_computed(q, predicate) { \|a\| h(a) }` | Valid | Reject: H does not preserve the auxiliary basis label and fails the zero-return certificate rule. |
| `do x <- q; let y = x; pure y` | Invalid | A v0 `do` permits only one `pure BasisExpr`. |
| `use oracle::*;` | Invalid | Wildcard imports are not part of v0. |

The parser regressions
[`reserved_std_module_keywords_allow_further_identifier_components`](../tests/parser.rs)
and [`unicode_format_characters_are_comment_text_but_not_source_tokens`](../tests/parser.rs)
check these import and Unicode boundaries. Additional parser tests check
[`coherent_lifts_parse_nested_basis_patterns_and_keep_their_spans`](../tests/parser.rs),
[`classical_boolean_operators_have_precedence_and_left_associativity`](../tests/parser.rs),
[`classical_literals_are_reserved_and_distinct_from_basis_bits`](../tests/parser.rs),
and [`classical_operator_chains_and_basis_patterns_obey_depth_limits`](../tests/parser.rs).
Parsing these cases does not establish successful module resolution, typing,
or execution; the compilation and execution regressions are recorded in the
[conformance ledger](specification-status.md).

<a id="構文を保留する項目"></a>

## Deferred syntax

- Runtime first-class operations, operations with classical parameters, and
  inverses between different basis types remain deferred. Current `qif`,
  `adjoint`, and `repeat_static` resolve function names statically and target
  only `Q<A> -> Q<A>` unitaries with no classical arguments.
- General `with_computed` that borrows its source while operating on a work
  register `R`, sized registers, higher-order functions with quantum arguments,
  dynamic loops, and runtime truth-table generation are not in this grammar.
  Adding them requires an accompanying definition of protected wire-ID sets,
  effects, and checkable evidence.

<a id="証明と後続仕様"></a>

### Proof status and subsequent specifications

The grammar, precedence, finite type rules, and branch interfaces are fixed
for v0. The [resource calculus](source-resource-rules.md) and
[typing supplement](source-typing-rules.md) give explicit rules, and
[Q1–Q3](source-soundness.md) establishes paper ideal soundness for those
mathematical derivations. Their adequacy for every Rust acceptance path and
general source-to-IR meaning preservation remain
[Stage 1 obligations](specification-status.md). General preservation effects
passed through signatures or evidence belong to later specifications;
the two-argument `with_computed` continues to use its restricted structural
certificate. The three-argument extension has the separately specified
[SC evidence rules](semantic-contracts-v0.1.md). Together with the
[retained function-contract path](function-contracts-v0.1.md), it meets the
declared finite V01-C1–C6 profile. General implementation proofs and the v1
algorithm-structure target remain open. The [language evolution framework](language-evolution.md)
organizes future design notation without adding forms to this grammar.
