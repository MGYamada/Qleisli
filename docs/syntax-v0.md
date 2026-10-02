# `.qli` surface syntax v0

English normative edition2026 finite grammar, with [M1 extension](next-minor-spec.md); [Qargo](language-editions.md) selects edition. Parsing supplies no semantic evidence.

## Grouped imports added in product 0.2.2

use std::{quantum::{h,x,},observe::measure_z}; expands nonempty groups in source order. Leaf module+name, trailing commas only groups, depth64; shared per-module budget65,536 copied identifiers/1,048,576 name bytes before copy. Original tokens uncharged. Every leaf retains item/identifier spans; grouped doc copies separately bounded65,536 comments/1,048,576 bytes. Render original use once. No aliases/globs/self; keywords basis/observe only directly after std.

## Authoring forms added in product 0.1.8

Products retain immediate arity2..64/nesting/spans; evaluate once in order. Basis names/_/nested patterns match exact domain; ignored fields stay in domain. Ordinary parameters are names. One tuple parameter is one argument. No unit/singleton patterns/trailing commas; no implicit left-fold tuple spelling.

## Boundary between syntax and built-in operations

do/pure, computed/contract/static forms are syntax; [sealed/ordinary APIs](frontend-v0.md) are distinct. Q means ownership, declaration kind effect. Iso<A,B>/Unitary<A,B>/lift are metanotation. Comments/docs emit no IR.

## Lexical rules and grammar

UTF-8, ASCII identifiers [A-Za-z_][A-Za-z0-9_]* excluding keywords; `_` wildcard. Space/tab/LF/CRLF separators, line/nested-block comments. Bare CR/BOM reject with original byte location. Forbid everywhere bidi U+061C/200E/200F/202A-202E/2066-2069, VT/FF/U+0085/2028/2029, other Unicode whitespace and Cc except allowed separators. Unicode comment text including U+200B/FEFF allowed. Docs normalize CRLF, preserve diagnostic offsets.

Reserve use/pub/basis/iso/unitary/observe/fn/let/if/else/do/pure/with_computed/adjoint/repeat_static/qif/apply_contract/true/false/not/xor/and/Unit/Bit/CBit/Q, plus meaning/static/Op/requires/Apply/Adjoint/Controlled/permutation_by/phase_by/bind_op/inverse_op/then_op/tensor_op/controlled_op/repeat_op/conjugate_op. Digit runs single tokens; basis only0/1, static canonical naturals0..4096. No strings/floats/arrays/operators/recursion. All recursive syntax/chains depth64.

```ebnf
Module ::= (Use | Decl)*
Use ::= "use" UseTree ";"
UseTree ::= ImportName ("::" UseTree)? | "{" UseTree ("," UseTree)* ","? "}"
ImportName ::= Ident | "basis" | "observe"
Decl ::= "pub"? ("basis" "fn" Ident "(" BasisParams? ")" "->" BasisType "{" BasisExpr "}"
       | Kind "fn" Ident "(" Params? ")" "->" Type Block)
Kind ::= "iso" | "unitary" | "observe"
BasisParams ::= Pattern ":" BasisType ("," Pattern ":" BasisType)*
Params ::= Ident ":" Type ("," Ident ":" Type)*
BasisType ::= "Unit" | "Bit" | "(" BasisType "," BasisType ("," BasisType)* ")"
Type ::= BasisType | "CBit" | "Q" "<" BasisType ">" | "(" Type "," Type ("," Type)* ")"
Pattern ::= Ident | "_" | "(" Pattern "," Pattern ("," Pattern)* ")"
Block ::= "{" Stmt* Expr "}"
Stmt ::= "let" Pattern "=" Expr ";" | Expr ";"
Expr ::= And ("xor" And)*
And ::= Unary ("and" Unary)*
Unary ::= "not" Unary | Atom
Atom ::= Name | "true" | "false" | "()" | "(" Expr ")" | "(" Expr "," Expr ("," Expr)* ")"
       | Name "(" (Expr ("," Expr)*)? ")" | "if" Expr Block "else" Block
       | "do" Pattern "<-" Expr ";" "pure" BasisExpr
       | "adjoint" "(" Name "," Expr ")"
       | "repeat_static" "(" StaticNat "," Name "," Expr ")"
       | "qif" "(" Expr "," Expr ")" "{" "0" "=>" Name "," "1" "=>" Name "}"
       | "with_computed" "(" Expr "," Name ")" "{" "|" Ident "|" Stmt* Expr "}"
       | "with_computed" "(" Expr "," Name "," Name ")" "{" "|" Ident "," Ident "|" Stmt* Expr "}"
       | "apply_contract" "(" Name "," Name "," Expr ")"
BasisExpr ::= BasisAnd ("xor" BasisAnd)*
BasisAnd ::= BasisUnary ("and" BasisUnary)*
BasisUnary ::= "not" BasisUnary | Ident | "0" | "1" | "()"
             | "(" BasisExpr ")" | "(" BasisExpr "," BasisExpr ("," BasisExpr)* ")"
             | Name "(" (BasisExpr ("," BasisExpr)*)? ")"
StaticNat ::= "0" | NonzeroDigit Digit*
```

Name is visible nonreserved identifier; no qualified runtime calls. Statements semicolon/final expression none; no trailing commas except import groups. not>and>xor; binaries left-associated, eager/left-to-right. if executes selected arm/checks both; repeat0 checks body. Basis isolated/no let/projection/indexing; pure extends a full BasisExpr, parentheses delimit outer runtime use. Runtime true/false:CBit vs basis0/1:Bit, no conversion; parsed bare Bit ordinary signatures reject semantically. `_` ignores labels/classical values, never quantum ownership.

## Names and scopes

File/module source-root-relative; use foo::bar::name imports pub from foo/bar.qli; std reserved. No aliases/glob/reexport/relative paths/cycles. Root execution entry parameterless observe main.qli/classical result/empty owner exit. Declaration order irrelevant, full dependency DAG includes static targets. Live/spent lexical names hide callables; basis Ξ has only own binders. Computed forms resolve names after input; legacy captures classical only, certified captures neither outer quantum nor classical. [Evidence rules](finite-contracts.md).

## Examples of syntactic acceptance and static rejection

Accept `do (a,b)<-q;pure (a,a xor b)` and x->(x,x); reject Bit->0, owner discard/reuse, observation in iso, runtime1/basis true and let in basis. [Parser regressions](../tests/parser.rs) and [examples](../README.md#try-it) retain executable cases.

## Deferred syntax

Runtime operation values/closures, heterogeneous/classical-port inverse, borrowing, general sized source/higher-order/dynamic loops require separate contracts. Sized experimental grammar is separate.

### Proof status and subsequent specifications

Paper rules and component proofs do not prove all Rust paths; [formal core](formal-core.md) and [milestones](release-milestones.md) fix scope.
