import QleisliKernel.SourceTypes.Members
import QleisliKernel.Tests.SourceMembers.Legacy.Declarations

/-! Bounded comparison against exact preserved old scanner bodies.
The Legacy namespace is a test-only rename, never an acceptance/fallback path.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace MemberLegacyComparison
open QleisliKernel


/-- Test-local total equality, including exact error text and complete success values. -/
local instance exceptDecidableEq {α : Type} [DecidableEq α] :
    DecidableEq (Except String α)
  | .error first, .error second =>
      if equal : first = second then .isTrue (by cases equal; rfl)
      else .isFalse (by intro result; cases result; exact equal rfl)
  | .ok first, .ok second =>
      if equal : first = second then .isTrue (by cases equal; rfl)
      else .isFalse (by intro result; cases result; exact equal rfl)
  | .error _, .ok _ => .isFalse (by intro result; cases result)
  | .ok _, .error _ => .isFalse (by intro result; cases result)

def oldDecls (source : String) :=
  (SourceTypesLegacy.declarations source).map fun declarations =>
    declarations.map fun declaration =>
      (declaration.name,declaration.isPublic,declaration.kind,declaration.body)

def newDecls (source : String) :=
  (SourceTypes.declarations source).map fun declarations =>
    declarations.map fun declaration =>
      (declaration.name,declaration.isPublic,declaration.kind,declaration.body)

/-- Compare the complete result, including exact error text and every success value. -/
def sameExcept {α : Type} [DecidableEq α] (left right : Except String α) : Bool :=
  match left, right with
  | .error first, .error second => decide (first = second)
  | .ok first, .ok second => decide (first = second)
  | _, _ => false

def same (source : String) : Bool :=
  sameExcept (SourceTypes.lex source) (SourceTypesLegacy.lex source) &&
    sameExcept (newDecls source) (oldDecls source)

-- Separate proofs keep first failures attributable and bound each reduction.
-- Preserved input 01.
example : same "" = true := by decide +kernel
-- Preserved input 02.
example : same "word" = true := by decide +kernel
-- Preserved input 03.
example : same "2abc" = true := by decide +kernel
-- Preserved input 04.
example : same "0" = true := by decide +kernel
-- Preserved input 05.
example : same "::" = true := by decide +kernel
-- Preserved input 06.
example : same ": :" = true := by decide +kernel
-- Preserved input 07.
example : same ":/* c */:" = true := by decide +kernel
-- Preserved input 08.
example : same "/* */enum E{A}" = true := by decide +kernel
-- Preserved input 09.
example : same "pub enum E { A, B, }" = true := by decide +kernel
-- Preserved input 10.
example : same "pub struct R { pub x:(Bit,Bits<0>), y:Unit }" = true := by decide +kernel
-- Preserved input 11.
example : same "fn f() -> Unit { pure () }" = true := by decide +kernel
-- Preserved input 12.
example : same "pub observe fn f() -> Unit { if true { pure () } else { pure () } }" = true := by decide +kernel
-- Preserved input 13.
example : same "fn f" = true := by decide +kernel
-- Preserved input 14.
example : same "fn f;" = true := by decide +kernel
-- Preserved input 15.
example : same "fn" = true := by decide +kernel
-- Preserved input 16.
example : same "fn f() -> Unit" = true := by decide +kernel
-- Preserved input 17.
example : same "fn f() -> Unit {" = true := by decide +kernel
-- Preserved input 18.
example : same "fn {" = true := by decide +kernel
-- Preserved input 19.
example : same "fn f() -> Unit {} fn f() -> Unit {}" = true := by decide +kernel
-- Preserved input 20.
example : same "fn f() -> Unit { fn inner() -> Unit {} }" = true := by decide +kernel
-- Preserved input 21.
example : same "fn f() pub -> Unit {}" = true := by decide +kernel
-- Preserved input 22.
example : same "pub pub fn f() -> Unit {}" = true := by decide +kernel
-- Preserved input 23.
example : same "pub static fn n() -> Nat { 0 }" = true := by decide +kernel
-- Preserved input 24.
example : same "static fn n() -> Nat;" = true := by decide +kernel
-- Preserved input 25.
example : same "static enum E { A }" = true := by decide +kernel
-- Preserved input 26.
example : same "static" = true := by decide +kernel
-- Preserved input 27.
example : same "use a::E;" = true := by decide +kernel
-- Preserved input 28.
example : same "pub use a::{E,R};" = true := by decide +kernel
-- Preserved input 29.
example : same "use" = true := by decide +kernel
-- Preserved input 30.
example : same "use a;" = true := by decide +kernel
-- Preserved input 31.
example : same "use a::;" = true := by decide +kernel
-- Preserved input 32.
example : same "use a::{E,};" = true := by decide +kernel
-- Preserved input 33.
example : same "use a::{,E};" = true := by decide +kernel
-- Preserved input 34.
example : same "use a::{E,,R};" = true := by decide +kernel
-- Preserved input 35.
example : same "use a::{E,R;" = true := by decide +kernel
-- Preserved input 36.
example : same "pub use a::E; enum E { A }" = true := by decide +kernel
-- Preserved input 37.
example : same "meaning M: Bit = reference(f);" = true := by decide +kernel
-- Preserved input 38.
example : same "meaning M" = true := by decide +kernel
-- Preserved input 39.
example : same "meaning M { f }" = true := by decide +kernel
-- Preserved input 40.
example : same "meaning M: Bit = reference(f)" = true := by decide +kernel
-- Preserved input 41.
example : same "pub meaning M: Bit = reference(f); struct R {}" = true := by decide +kernel
-- Preserved input 42.
example : same "pub struct R { x:Bit, x:Unit }" = true := by decide +kernel
-- Preserved input 43.
example : same "struct R<T> { x:T }" = true := by decide +kernel
-- Preserved input 44.
example : same "enum E { A(Bit) }" = true := by decide +kernel
-- Preserved input 45.
example : same "pub enum E { A } pub enum E { B }" = true := by decide +kernel
-- Preserved input 46.
example : same "enum E {}" = true := by decide +kernel
-- Preserved input 47.
example : same "struct R {}" = true := by decide +kernel
-- Preserved input 48.
example : same "// pub struct Fake { x:Bit }\r\npub enum E { A }" = true := by decide +kernel
-- Preserved input 49.
example : same "/* 日本語 /* nested */ 🐈 */\r\npub struct R { x:Unit }" = true := by decide +kernel
-- Preserved input 50.
example : same "// tail" = true := by decide +kernel
-- Preserved input 51.
example : same "/* unterminated" = true := by decide +kernel
-- Preserved input 52.
example : same "/* /* nested */" = true := by decide +kernel
-- Preserved input 53.
example : same "a\rb" = true := by decide +kernel
-- Preserved input 54.
example : same "pub enum 猫 { A }" = true := by decide +kernel
-- Preserved input 55.
example : same "#![no_implicit_prelude]\n/* ok */pub enum E { A }" = true := by decide +kernel
-- Preserved input 56.
example : same "; #![no_implicit_prelude] pub struct R {}" = true := by decide +kernel
-- Preserved input 57.
example : same "use facade::{Tri, Record};\nclassical fn read(r: Record) -> Tri { r.tag }\nclassical fn bad(r: Record) -> (Unit, Bits<0>) { r.hidden }\n" = true := by decide +kernel
-- Preserved input 58.
example : same "// pub struct Ghost { pub x: Bit }\npub enum One { Only }\n/* 😀 */ pub struct Empty {}\nfn before() -> Unit { pure () }\nfn after() -> Unit { /* fn before() -> Unit { } */ pure () }\n" = true := by decide +kernel
-- Preserved input 59.
example : same "pub struct Bad { pub x: Bit, x: Unit }\n" = true := by decide +kernel
-- Preserved input 60.
example : same "pub use owner::{Tri, Record};\n" = true := by decide +kernel
-- Preserved input 61.
example : same "pub struct Pair { pub left: (Bit, Bits<2>), right: Unit }\nclassical fn nested(x: Bit) -> Bit { if x { true } else { false } }\n" = true := by decide +kernel
-- Preserved input 62.
example : same "/* 日本語 /* nested pub struct Fake { pub leak: Bit } */ 🐈 */\r\npub enum Tri { A, B, C }\r\npub struct Record { pub tag: Tri, hidden: (Unit, Bits<0>), pub bits: Bits<2>, }\r\nclassical fn own(r: Record) -> Tri { r.tag }\r\n" = true := by decide +kernel
-- Preserved input 63.
example : same "observe pub struct Bad { pub x: Bit }\n" = true := by decide +kernel
example : same ("// " ++ String.singleton (Char.ofNat 0x202e) ++ "\npub enum E { A }") = true := by decide +kernel
example : same ("/* " ++ String.singleton (Char.ofNat 0) ++ " */pub struct R {}") = true := by decide +kernel

-- Exact token positions under multibyte comments, CRLF, numeric splitting and EOF.
def slices (source : String) : Bool :=
  match SourceTypes.lexLocated source with
  | .error _ => false
  | .ok tokens => SourceTypes.LocatedFacts.checkOrdered source.toUTF8 0 tokens
example : slices "/* 🐈 */\r\n2abc::name" = true := by decide +kernel
example : (SourceTypes.lexLocated "2abc::name").map (List.map (fun token =>
    (token.text,token.span.startByte,token.span.endByte))) =
    .ok [("2",0,1),("abc",1,4),("::",4,6),("name",6,10)] := by decide +kernel

example : (SourceTypes.lexLocated "/* 🐈 */\r\n2abc::name").map (List.map (fun token =>
    (token.text,token.span.startByte,token.span.endByte))) =
    .ok [("2",12,13),("abc",13,16),("::",16,18),("name",18,22)] := by decide +kernel
-- Independent metadata refusal, without source-reader success as a premise.
example : SourceTypes.LocatedFacts.checkOrdered "abc".toUTF8 0
    [⟨"abc",⟨0,2⟩⟩] = false := by decide +kernel
example : SourceTypes.LocatedFacts.checkOrdered "abc".toUTF8 0
    [⟨"bc",⟨1,3⟩⟩,⟨"a",⟨0,1⟩⟩] = false := by decide +kernel
example : SourceTypes.LocatedFacts.checkOrdered "abc".toUTF8 0
    [⟨"abc",⟨0,4⟩⟩] = false := by decide +kernel
end MemberLegacyComparison
