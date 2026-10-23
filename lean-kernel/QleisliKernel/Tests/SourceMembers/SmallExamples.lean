import QleisliKernel.SourceTypes.Members

/-! Small original-source observations, not runtime acceptance tests.
The original source string reproduces the first preserved bytes, including CRLF.
Copyright 2026 Qleisli Project Contributors. Apache-2.0. -/
namespace MemberSmallExamples
open QleisliKernel QleisliKernel.SourceTypes QleisliKernel.SourceTypes.Members


/-- Test-local total equality, including exact error text and complete success values. -/
local instance exceptDecidableEq {ε α : Type} [DecidableEq ε] [DecidableEq α] :
    DecidableEq (Except ε α)
  | .error first, .error second =>
      if equal : first = second then .isTrue (by cases equal; rfl)
      else .isFalse (by intro result; cases result; exact equal rfl)
  | .ok first, .ok second =>
      if equal : first = second then .isTrue (by cases equal; rfl)
      else .isFalse (by intro result; cases result; exact equal rfl)
  | .error _, .ok _ => .isFalse (by intro result; cases result)
  | .ok _, .error _ => .isFalse (by intro result; cases result)

def original : String := "/* 日本語 /* nested pub struct Fake { pub leak: Bit } */ 🐈 */\r\npub enum Tri { A, B, C }\r\npub struct Record { pub tag: Tri, hidden: (Unit, Bits<0>), pub bits: Bits<2>, }\r\nclassical fn own(r: Record) -> Tri { r.tag }\r\n"
def sources : Sources := #[("owner",original)]
def action := readOriginal sources "owner" "Record"
def summary := (action.run 2000000).1.map fun result =>
  result.members.map fun item =>
    (item.name.text,item.isPublic,item.typeTokens.map (List.map LocatedToken.text))

example : summary = .ok [
    ("tag",true,some ["Tri"]),
    ("hidden",false,some ["(","Unit",",","Bits","<","0",">",")"]),
    ("bits",true,some ["Bits","<","2",">"])] := by decide +kernel
example : (action.run 0).1.isOk = false := by decide +kernel
-- Preserve the measured work consumption as a kernel-checked regression.
example : (action.run 2000000).2 = 1979563 := by decide +kernel

example : ((readOriginal #[("owner",original),("owner",original)] "owner" "Record").run
    2000000).1.isOk = false := by decide +kernel
example : ((readOriginal #[("owner","pub struct R { pub x:Bit, x:Unit }")] "owner" "R").run
    2000000).1.isOk = false := by decide +kernel
example : ((readOriginal #[("owner","observe pub struct R { pub x:Bit }")] "owner" "R").run
    2000000).1.isOk = false := by decide +kernel
example : ((readOriginal #[("owner","/* 🐈 */\r\n#![no_implicit_prelude] pub struct R {}")] "owner" "R").run
    2000000).1.isOk = true := by decide +kernel
example : ((readOriginal #[("owner","; #![no_implicit_prelude] pub struct R {}")] "owner" "R").run
    2000000).1.isOk = false := by decide +kernel
end MemberSmallExamples
