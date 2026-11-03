import QleisliKernel.SourceTypes.SourceRuntimeOrdinary
import QleisliKernel.SourceTypes.SourceBasisFunction

/-! Independent logical ordinary evaluation and actual result extraction.
No native SSA, source-AST or instrument correspondence is assumed by these
small controls; those are separate obligations of the enclosing body gate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceRuntimeOrdinary
open QleisliKernel QleisliKernel.SourceTypes
open Semantics.SourceOrdinary

private def values (inputs : List Nat := []) (measurement : Option Nat := none) : Valuation :=
  ⟨fun ordinal => inputs[ordinal]?,fun _ => none,fun _ _ _ => measurement⟩
private def site : Site := ⟨"main","route",17⟩
private def owner : Semantics.SourceOwners.Owner := ⟨2,[.bit]⟩

#guard evaluate (values [1,0]) (.xor (.input 0) (.input 1)) = some 1
#guard evaluate (values) (.choose (.bit false) (.measured site [] owner) (.ordinal 7)) = some 7
#guard evaluate (values) (.and (.bit false) (.measured site [] owner)) = none
#guard evaluate (values [] (some 1)) (.measured site [] owner) = some 1
#guard evaluate (values [2]) (.not (.input 0)) = none
#guard evaluate (values [1,2]) (.combine 2 (.input 0) (.input 1)) = some 5
#guard evaluate (values [5]) (.field 2 3 (.input 0)) = some 2
#guard evaluate (values [1]) (.field 0 2 (.input 0)) = none

-- A flat source can produce a chain deeper than the parser's nesting limit.
private def negations : Expression := (List.range 129).foldl (fun e _ => .not e) (.bit false)
#guard evaluate values negations = some 1
#guard (SourceRuntimeValues.expressionSize negations,SourceRuntimeValues.expressionFields negations) = (130,130)
#guard (SourceRuntimeValues.expressionTransport site [] [] negations).toOption = some negations

private def result : Value :=
  [.tuple 3,.ordinary [.bit] (.input 0),.ordinary [.bits 0] (.ordinal 0),.owner owner]
#guard (QleisliKernel.SourceTypes.SourceRuntimeOrdinary.extract (values [1]) result).toOption =
  some [.tuple 3,.ordinary [.bit] 1,.ordinary [.bits 0] 0,.owner owner]
#guard (QleisliKernel.SourceTypes.SourceRuntimeOrdinary.extract (values [2]) result).toOption.isNone

private def tri : Semantics.FiniteCarrier.Basis :=
  [.enumeration ⟨"main","Tri","enum Tri{A,B,C}"⟩ ["A","B","C"]]
#guard (QleisliKernel.SourceTypes.SourceRuntimeOrdinary.extract (values) [.ordinary tri (.ordinal 2)]).isOk
#guard (QleisliKernel.SourceTypes.SourceRuntimeOrdinary.extract (values) [.ordinary tri (.ordinal 3)]).toOption.isNone

private def calleeSite : Site := ⟨"lib","observe",41⟩
private def canonicalOwner : Semantics.SourceOwners.Owner := ⟨0,[.bit]⟩
private def actualOwner : Semantics.SourceOwners.Owner := ⟨7,[.bit]⟩
private def callerValues : Valuation :=
  ⟨fun i => if i == 0 then some 0 else none,fun _ => none,
    fun origin calls measured =>
      if origin == calleeSite && calls == [site] && measured.ordinal == 7 then some 1 else none⟩
private def calleeValue : Expression :=
  .choose (.not (.input 0)) (.measured calleeSite [] canonicalOwner) (.bit false)
private def arguments : List (Semantics.FiniteCarrier.Basis × Expression) := [([.bit],.input 0)]
#guard (SourceRuntimeValues.expressionTransport site [actualOwner] arguments calleeValue).toOption.map
  (evaluate callerValues) = some (some 1)
#guard evaluate (QleisliKernel.SourceTypes.SourceRuntimeOrdinary.calledValuation callerValues site [actualOwner] arguments)
  calleeValue = some 1
#guard (SourceRuntimeValues.expressionTransport site [⟨7,[.bits 1]⟩] arguments calleeValue).toOption.isNone

#print axioms QleisliKernel.Semantics.SourceOrdinary.evaluate
#print axioms QleisliKernel.SourceTypes.SourceRuntimeOrdinary.readAtom_sound
#print axioms QleisliKernel.SourceTypes.SourceRuntimeOrdinary.extract_sound
#print axioms QleisliKernel.SourceTypes.SourceRuntimeOrdinary.expressionTransport_reference
#print axioms QleisliKernel.SourceTypes.SourceBasisFunction.evaluate_reference
end QleisliKernel.Tests.SourceRuntimeOrdinary
