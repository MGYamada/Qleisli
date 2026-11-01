import QleisliKernel.SourceTypes.CallSyntax

/-! Bounded original-token controls; no name/owner/effect or body acceptance.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.CallSyntaxTests
open QleisliKernel.SourceTypes
open QleisliKernel.SourceTypes CallSyntax

def parsed (source : String) : Option Call := do
  let tokens ← (lexLocated source).toOption
  let checked ← (read tokens).toOption
  return checked.call

def shape (source : String) : Option (List String × List (List String) × List Bool) :=
  (parsed source).map fun call =>
    (call.callee.map (·.text),call.arguments.map fun arg => arg.tokens.map (·.text),
      call.arguments.map (·.followingComma.isSome))

example : shape "h(q)" = some (["h"],[["q"]],[false]) := by decide +kernel
example : shape "f()" = some (["f"],[],[]) := by decide +kernel
example : shape "f(q,)" = some (["f"],[["q"]],[true]) := by decide +kernel
example : shape "defs::swap(q,r)" =
    some (["defs","::","swap"],[["q"],["r"]],[true,false]) := by decide +kernel
example : shape "f[Q<Bit>,2](x)" =
    some (["f","[","Q","<","Bit",">",",","2","]"],[["x"]],[false]) := by decide +kernel
example : shape "h(sign(q))" =
    some (["h"],[["sign","(","q",")"]],[false]) := by decide +kernel
example : shape "power(f,2)(q)" =
    some (["power","(","f",",","2",")"],[["q"]],[false]) := by decide +kernel
example : shape "f((q,r),s)" =
    some (["f"],[["(","q",",","r",")"],["s"]],[true,false]) := by decide +kernel
example : shape "h(qmatch(s,q){0=>idle,1=>sign})" =
    some (["h"],[["qmatch","(","s",",","q",")","{","0","=",">","idle",",",
      "1","=",">","sign","}"]],[false]) := by decide +kernel

-- Opaque callee tokens are never silently replaced by a convenient final name.
-- This splitter alone does not establish that the callee is a valid expression.
example : (shape "h(q);f(r)").map (·.1) =
    some ["h","(","q",")",";","f"] := by decide +kernel

example : (parsed "h").isNone = true := by decide +kernel
example : (parsed "(q)").isNone = true := by decide +kernel
example : (parsed "h(q) trailing").isNone = true := by decide +kernel
example : (parsed "h(q]").isNone = true := by decide +kernel
example : (parsed "h([q))").isNone = true := by decide +kernel
example : (parsed "h(q,,r)").isNone = true := by decide +kernel
example : (parsed "h(,q)").isNone = true := by decide +kernel
example : (parsed "h(q").isNone = true := by decide +kernel

example : ((parsed "/*λ*/h(q)").map fun call =>
    (call.callee.head?.map (·.span.startByte),call.opening.span.startByte,
      call.arguments.head?.map (fun arg => arg.tokens.head?.map (·.span.startByte)),
      call.closing.span.endByte)) = some (some 6,7,some (some 8),10) := by decide +kernel

end QleisliKernel.Tests.CallSyntaxTests
