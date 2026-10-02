<a id="qli-表層構文-v0"></a>

# `.qli` surface syntax v0

English normative edition-2026 finite grammar. [Language](language-spec.md),
[types](type-system.md), [modules](standard-library.md), [documentation comments](documentation-comments.md)
and [M1 static forms](next-minor-spec.md) supply separate semantic/extension rules.
Parsing does not establish types/effects/evidence/execution or general compiler
adequacy. [Qargo](language-editions.md) selects edition per source tree.

## Grouped imports added in product 0.2.2

use std::{quantum::{h,x,},observe::measure_z}; expands nonempty nested groups
in source order into existing UseDecl leaves. Each leaf contains module+name;
trailing commas only in groups, nesting≤64. Before copying prefixes, one shared
per-module budget checks 65,536 identifiers and 1,048,576 UTF-8 name bytes across
nested/separate uses; original path tokens do not spend it. Ungrouped paths stay
iterative. basis/observe are keyword components only immediately after std.
No aliases/globs/self; normal duplicate/visibility/cycle rules still apply.

Each leaf retains the full use-item span plus identifier spans. Group docs attach
to every leaf; copied documentation has separate per-module limits of 65,536
comments/1,048,576 text bytes checked before clones. Ungrouped docs move without
copy. Render each original use once. No runtime ownership/effect/IR is introduced.

## Authoring forms added in product 0.1.8

Current tuples retain 2..64 immediate fields in types/values/patterns; flat and
nested products differ (0.2.0 supersedes the old left-fold spelling). Each AST
field has its own span; outer span includes parentheses. Evaluate once in order.
Basis parameter names/_/nested products match exact trees; names across all
parameters distinct, ignored components remain in domain. One tuple parameter
is one source argument, with no implicit packing. Ordinary parameters are names.
No unit/singleton patterns or trailing commas; () expression/grouping retains
meaning. Nested syntax depth≤64.

Accept basis fn swap((a,b):(Bit,Bit))->(Bit,Bit){(b,a)}; reject duplicate a,
pair pattern on Bit and swap(0,1). These elaborate existing label bindings/tables,
not owner duplication or new primitives. [Fixtures](../tests/fixtures/ergonomics/README.md)
retain whole-domain injection tests.

<a id="構文と組み込みの境界"></a>

## Boundary between syntax and built-in operations

Declarations/imports/bindings, classical literals/Booleans, do/pure, both
with_computed forms, apply_contract, adjoint/repeat/qif and M1 forms are language
forms. Sealed init/gates/split/join/observe have fixed independently checked
meanings ([API](standard-library.md)); ordinary helpers obey user rules.
Comments/docstrings emit no IR or evidence. Q<A> is ownership, fn classification
is effect; Iso<A,B>/Unitary<A,B>/lift(e) are metanotation. The source lift is
do p<-q;pure e. The compatible s/sdg/tdg/id/phase_eighth aliases are sealed.

<a id="字句と文法"></a>

## Lexical rules and grammar

UTF-8 files; identifiers ASCII [A-Za-z_][A-Za-z0-9_]* excluding keywords;
_ alone is wildcard. Separators only ASCII space/tab/LF/CRLF. Line comments end
at LF/EOF; block comments nest. Docs attach separately before parse success,
normalize CRLF but retain original UTF-8 diagnostic offsets. Bare CR rejects at
its original byte even in comments; leading BOM rejects, never strips.

Forbidden everywhere, including comments: bidi controls U+061C/200E/200F,
U+202A–202E/2066–2069; VT/FF/U+0085/2028/2029; other Unicode whitespace;
Cc controls except tab/LF/CR in CRLF. Other Unicode comment text is allowed,
including U+200B/U+FEFF, which neither terminate comments nor form source tokens.
Non-ASCII identifiers are forbidden.

Reserved base: use,pub,basis,iso,unitary,observe,fn,let,if,else,do,pure,
with_computed,adjoint,repeat_static,qif,apply_contract,true,false,not,xor,and,
Unit,Bit,CBit,Q. M1 additionally reserves meaning,static,Op,requires,Apply,
Adjoint,Controlled,permutation_by,phase_by,bind_op,inverse_op,then_op,tensor_op,
controlled_op,repeat_op,conjugate_op. Rename collisions in all names/module
components. Basis literals only 0/1; digit runs are single tokens, so 10/2 are
invalid basis literals. Static decimal naturals have no leading zero except 0;
counts 0..4,096. No strings/floats/arrays/user operators/general recursion.
Recursive syntax/pattern/expression trees, including left-associated chains,
have located depth-64 rejection.

EBNF *,?,| mean repetition/optional/alternatives. Ident excludes _; Name is a
visible nonreserved identifier. Statements end in semicolons, final expressions
do not. No trailing comma in parameter/argument/tuple/qif lists.

```ebnf
Module       ::= (Use | Decl)*
Use          ::= "use" UseTree ";"
UseTree      ::= ImportName ("::" UseTree)?
               | "{" UseTree ("," UseTree)* ","? "}"
ImportName   ::= Ident | "basis" | "observe"
Path         ::= Ident ("::" Ident)*
               | "std" "::" ("basis" | "observe") ("::" Ident)*
Decl         ::= "pub"? (BasisDecl | QuantumDecl)
BasisDecl    ::= "basis" "fn" Ident "(" BasisParams? ")"
                 "->" BasisType BasisBlock
QuantumDecl  ::= Kind "fn" Ident "(" Params? ")" "->" Type Block
Kind         ::= "iso" | "unitary" | "observe"
BasisParams  ::= BasisParam ("," BasisParam)*
BasisParam   ::= Pattern ":" BasisType
Params       ::= Param ("," Param)*
Param        ::= Ident ":" Type
Type         ::= BasisType | "CBit" | "Q" "<" BasisType ">"
               | "(" Type "," Type ("," Type)* ")"
BasisType    ::= "Unit" | "Bit" | "(" BasisType "," BasisType ("," BasisType)* ")"
ClassicalType ::= "Unit" | "CBit" | "(" ClassicalType "," ClassicalType ("," ClassicalType)* ")"
Block        ::= "{" Stmt* Expr "}"
BasisBlock   ::= "{" BasisExpr "}"
Stmt         ::= "let" Pattern "=" Expr ";" | Expr ";"
Pattern      ::= Ident | "_" | "(" Pattern "," Pattern ("," Pattern)* ")"
Expr         ::= RuntimeXor
RuntimeXor   ::= RuntimeAnd ("xor" RuntimeAnd)*
RuntimeAnd   ::= RuntimeUnary ("and" RuntimeUnary)*
RuntimeUnary ::= "not" RuntimeUnary | RuntimeAtom
RuntimeAtom  ::= Name | "true" | "false" | "()"
               | "(" Expr ")" | "(" Expr "," Expr ("," Expr)* ")"
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
               | "(" BasisExpr "," BasisExpr ("," BasisExpr)* ")"
               | BasisCall
BasisCall    ::= Name "(" BasisArgs? ")"
BasisArgs    ::= BasisExpr ("," BasisExpr)*
```

Import keywords basis/observe are allowed only directly after std, including
groups; later components/imported names are identifiers. Further components
parse without implying supported modules. Operator precedence not>and>xor,
binary left association, eager runtime operands/left-to-right calls and tuples;
let RHS precedes binding, statements run in order. if executes only selected arm,
but checks both. Zero repetition checks target body.

Basis expressions are total/isolated, with no let/projection/indexing; current
basis parameters admit patterns. do binds labels from the complete input tree,
checks full-domain injection, and pure extends through one full BasisExpr.
Parentheses delimit it before outer runtime operators. _ ignores labels, never
owners; no () pattern. Basis predicates need not be injective for computed use.
Runtime true/false and Boolean operators use CBit; 0/1 and basis Booleans use Bit.
No implicit conversion. Type grammar is broader than ordinary type formation:
no bare Bit in ordinary signatures. One tuple argument is not several arguments.
Quantum _ bindings/expression discards parse but resource checking rejects.
ClassicalType is a semantic restriction on root main, enforced after parsing.

<a id="名前とスコープ"></a>

## Names and scopes

One source-root-relative file/module; use foo::bar::name imports pub name from
foo/bar.qli. std is reserved. Top-level imports only, no alias/glob/reexport/
relative path/cycle; imported/local collisions reject. Unique execution main is
parameterless observe main in root main.qli with a classical result and empty
quantum exit; libraries need none.

Declaration order is irrelevant, dependency graph acyclic including static names.
Runtime lexical live/spent bindings hide ordinary/static/predicate callables;
let q=h(q) consumes old q before rebinding, while live-owner hiding rejects.
if locals expire; merge uses complete result/frame/consumption interfaces.

Do's basis Ξ contains exactly pattern labels, no runtime capture: a runtime f
does not hide top-level basis f there, but a pattern f does. pure is not a
runtime return form. Computed forms resolve names after input evaluation.
Legacy computed scope masks quantum owners, retains classical values, permits
aux binder to reuse a masked spelling while outer owner survives. Certified
scope captures neither quantum nor classical outer values, binds distinct d/a,
returns data/aux order. apply_contract resolves two ordinary eligible names after
input evaluation, includes both dependencies and captures no caller values.
[Finite contracts](finite-contracts.md) fix all evidence/effect rules.

<a id="構文受理と静的拒否の例"></a>

## Examples of syntactic acceptance and static rejection

Imports omitted; executable projects live in [examples](../README.md#try-it).
Parsing and static acceptance remain separate.

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

Accept injective (a,b)→(a,a xor b), coherent x→(x,x), and eager classical
false and measure_z(q) in observe. Reject noninjective Bit→0/XOR alone,
ignored Bit (ignored Unit may be removed), duplicate binder/owner, measured-owner
reuse, observe inside iso, legacy auxiliary H, runtime 1/basis true, let inside
pure continuation, and wildcard import. [Parser regressions](../tests/parser.rs)
cover spans/Unicode/precedence/depth; checking/runtime regressions are separate.

<a id="構文を保留する項目"></a>

## Deferred syntax

Runtime operation values/closures, classical-argument inverse targets,
different-type adjoints, general borrowed computed regions, sized registers,
higher-order quantum functions, dynamic loops and runtime table generation need
separate specifications/evidence. Experimental sized grammar is separate.

<a id="証明と後続仕様"></a>

### Proof status and subsequent specifications

Paper source rules establish ideal mathematical derivations; general agreement
with every Rust check/lowering path remains open. [Formal scope](formal-core.md)
and [milestones](release-milestones.md) separate finite V01 checking from v1 and
production soundness. Neither parsing, documentation nor draft notation grants
semantic authority.
