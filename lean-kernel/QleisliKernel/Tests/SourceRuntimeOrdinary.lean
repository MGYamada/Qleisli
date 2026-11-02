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

private def result : Value :=
  [.tuple 3,.ordinary [.bit] (.input 0),.ordinary [.bits 0] (.ordinal 0),.owner owner]
#guard (QleisliKernel.SourceTypes.SourceRuntimeOrdinary.extract (values [1]) result).toOption =
  some [.tuple 3,.ordinary [.bit] 1,.ordinary [.bits 0] 0,.owner owner]
#guard (QleisliKernel.SourceTypes.SourceRuntimeOrdinary.extract (values [2]) result).toOption.isNone

private def tri : Semantics.FiniteCarrier.Basis :=
  [.enumeration ⟨"main","Tri","enum Tri{A,B,C}"⟩ ["A","B","C"]]
#guard (QleisliKernel.SourceTypes.SourceRuntimeOrdinary.extract (values) [.ordinary tri (.ordinal 2)]).isOk
#guard (QleisliKernel.SourceTypes.SourceRuntimeOrdinary.extract (values) [.ordinary tri (.ordinal 3)]).toOption.isNone

#print axioms QleisliKernel.Semantics.SourceOrdinary.evaluate
#print axioms QleisliKernel.SourceTypes.SourceRuntimeOrdinary.readAtom_sound
#print axioms QleisliKernel.SourceTypes.SourceRuntimeOrdinary.extract_sound
#print axioms QleisliKernel.SourceTypes.SourceBasisFunction.evaluate_reference
end QleisliKernel.Tests.SourceRuntimeOrdinary
