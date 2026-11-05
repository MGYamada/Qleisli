import QleisliKernel.SourceTypes.StaticCallPremises
import QleisliKernel.SourceTypes.QuantumSignatureCore
import QleisliKernel.SourceTypes.LexicalNatural

/-! Small all-binding call-premise regressions. A selected closed value cannot
repair a missing generic implication; original mixed ordinals remain positional.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.StaticCallPremises
open SourceTypes Finite

private def adapt {α : Type} (value : Except String α) : WorkM α :=
  lift (value.mapError fun _ => .request)

private def accepts (requirements actual : String) (n : Nat := 1) : Bool :=
  let source :=
    "#![no_implicit_prelude] unitary fn target[const m:Nat](q:Q<Bit>)->Q<Bit> requires m>=1{q} " ++
    "pub unitary fn caller[const n:Nat](q:Q<Bit>)->Q<Bit> " ++ requirements ++ "{target[" ++ actual ++ "](q)}"
  let action : WorkM Unit := do
    let sources : Sources := #[("main",source)]
    let signature ← QuantumSignatureCore.prepareWithArguments sources "main" "caller" {naturals := [("n",n)]}
    let call ← adapt (CallSyntax.read signature.original.occurrence.body)
    let written ← adapt (CallSyntax.readStatic call.call.callee)
    let target ← StaticHeaders.read sources "main" "target"
    let _ ← SourceTypes.StaticCallPremises.read signature.instantiation none ["n","q"] target written.call.arguments
    pure ()
  (action.run 10000000).1.isOk

-- Even n=1 does not establish n>=1 for every original caller valuation.
#guard accepts "" "n" = false
#guard accepts "requires n>=1" "n" = true

-- A caller premise and original affine actual expression can prove the request.
#guard accepts "" "n+1" 0 = true
#guard accepts "requires n>=2" "n-1" 2 = true
#guard accepts "" "n-1" 1 = false

-- A nonlinear original expression is not repaired by its chosen closed zero.
#guard accepts "" "n*n" 0 = false

private def mixed (actual : String) : Bool :=
  let source :=
    "#![no_implicit_prelude] unitary fn target[const A:Basis,const z:Nat,const a:Nat](q:Q<A>)->Q<A> requires a>=z{q} " ++
    "pub unitary fn caller[const n:Nat](q:Q<Bit>)->Q<Bit>{target[" ++ actual ++ "](q)}"
  let action : WorkM Unit := do
    let sources : Sources := #[("main",source)]
    let signature ← QuantumSignatureCore.prepareWithArguments sources "main" "caller" {naturals := [("n",1)]}
    let call ← adapt (CallSyntax.read signature.original.occurrence.body)
    let written ← adapt (CallSyntax.readStatic call.call.callee)
    let target ← StaticHeaders.read sources "main" "target"
    let _ ← SourceTypes.StaticCallPremises.read signature.instantiation none ["n","q"] target written.call.arguments
    pure ()
  (action.run 10000000).1.isOk

-- Name-first affine order must not swap original mixed-kind ordinals.
#guard mixed "type(Bit),n,n+1" = true
#guard mixed "type(Bit),n+1,n" = false

private def guarded (branch : Bool) (condition : Semantics.SourceNatural.Predicate)
    (expression : Semantics.SourceNatural.Expr) (aliasFirst : Bool := false) : Bool :=
  let source := "#![no_implicit_prelude] pub unitary fn caller[const n:Nat](q:Q<Bit>)->Q<Bit>{q}"
  let action : WorkM Unit := do
    let sources : Sources := #[("main",source)]
    let signature ← QuantumSignatureCore.prepareWithArguments sources "main" "caller" {naturals := [("n",1)]}
    let state ← SourceTypes.StaticCallPremises.callerState signature.instantiation none
    let scope := ["n","q"]
    let (state,scope) ← if aliasFirst then do
        let state ← GenericLexicalNatural.bind state "main" scope "earlier" (.add (.name ["n"]) (.number 1))
        pure (state,"earlier" :: scope)
      else pure (state,scope)
    let state ← GenericLexicalNatural.assume state "main" scope condition branch
    GenericLexicalNatural.validate state "main" scope expression
  (action.run 10000000).1.isOk

-- The selected n=1 supplies no missing all-binding premise. Only the original
-- true guard n>0 establishes this subtraction; the other branch does not.
#guard guarded true ⟨.name ["n"],.gt,.number 0⟩ (.sub (.name ["n"]) (.number 1)) = true
#guard guarded false ⟨.name ["n"],.gt,.number 0⟩ (.sub (.name ["n"]) (.number 1)) = false

-- Earlier lexical meanings remain intact when their guard is assumed.
#guard guarded true ⟨.name ["earlier"],.gt,.number 1⟩ (.sub (.name ["n"]) (.number 1)) true = true

-- Even a false branch cannot repair arithmetic inside the condition itself.
#guard guarded false ⟨.sub (.name ["n"]) (.number 1),.eq,.number 0⟩ (.number 0) = false

private def closedPredicate (n : Nat) : Option Bool :=
  let action : WorkM Bool := do
    let sources : Sources := #[("main","#![no_implicit_prelude] pub unitary fn caller(q:Q<Bit>)->Q<Bit>{q}")]
    let entries ← NaturalHelpers.prepare sources
    let environment := LexicalNatural.ofBindings entries [("n",n)]
    let checked ← LexicalNatural.readPredicate sources "main" entries environment ["n"]
      ⟨.name ["n"],.gt,.number 0⟩
    pure checked.value
  (action.run 10000000).1.toOption

#guard closedPredicate 0 = some false
#guard closedPredicate 1 = some true

end QleisliKernel.Tests.StaticCallPremises
