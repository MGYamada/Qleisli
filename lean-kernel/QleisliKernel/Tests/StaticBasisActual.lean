import QleisliKernel.SourceTypes.StaticBasisActual
import QleisliKernel.SourceTypes.PhaseApplication

/-! Small original lexical Basis-actual regressions. The full tree is read
under the same checked aliases as Nat actuals, without changing source tokens.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.StaticBasisActual
open SourceTypes Finite Semantics.FiniteCarrier

private def adapt {α : Type} (value : Except String α) : WorkM α :=
  lift (value.mapError fun _ => .request)

private def basis (initializer : String) (n : Nat) (requirements : String := "") : Option Basis :=
  let source := "#![no_implicit_prelude] unitary fn keep[const A:Basis](q:Q<A>)->Q<A>{q} " ++
    "pub unitary fn caller[const n:Nat](q:Q<Bit>)->Q<Bit> " ++ requirements ++
    "{static let width=" ++ initializer ++ ";keep[type(Bits<width>)](q)}"
  let action : WorkM Basis := do
    let sources : Sources := #[("main",source)]
    let signature ← QuantumSignatureCore.prepareWithArguments sources "main" "caller" {naturals := [("n",n)]}
    let initial ← PhaseApplication.prepareWithInstantiation signature.instantiation
    let prefix ← adapt (StaticBindings.readPrefix signature.original.occurrence.body)
    let (naturals,scope) ← PhaseApplication.extend sources "main" prefix initial (signature.staticNames ++ ["q"])
    let call ← adapt (CallSyntax.read prefix.suffix)
    let written ← adapt (CallSyntax.readStatic call.call.callee)
    let [argument] := written.call.arguments | throw .request
    let checked ← SourceTypes.StaticBasisActual.read signature.instantiation naturals.helpers.val naturals.environment scope
      naturals.generic argument.tokens
    pure checked.query.basis
  (action.run 10000000).1.toOption

#guard basis "n" 1 = some [.bits 1]
#guard basis "n-1" 2 "requires n>=1" = some [.bits 1]
#guard basis "n-1" 1 = none
#guard basis "n*n" 0 = none

-- The established finite type bound is checked after exact lexical evaluation.
#guard basis "n+1" 6 = none

end QleisliKernel.Tests.StaticBasisActual
