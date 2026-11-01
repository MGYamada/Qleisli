import QleisliKernel.SourceTypes.StaticCallPremises
import QleisliKernel.SourceTypes.QuantumSignatureCore

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

end QleisliKernel.Tests.StaticCallPremises
