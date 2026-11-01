import QleisliKernel.SourceTypes.SourceBasisFunction

/-! Complete tiny basis-function enumerations, including captured classical
valuations. These are finite component tests, not native source-body proofs.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceBasisFunction
open QleisliKernel QleisliKernel.SourceTypes SourceRuntimeValues
open Semantics.FiniteCarrier

private def read (input output : Basis) (value : Value) (inputTypes : List Basis := []) :=
  ((SourceTypes.SourceBasisFunction.read input output inputTypes value).run 10000000).1.toOption

#guard (read [.unit] [.bit] [.ordinary [.bit] (.bit false)]).map (fun checked =>
  (checked.rows,checked.effect)) = some ([[0]],.iso)
#guard (read [.bit] [.bit] [.ordinary [.bit] (.basisInput 0)]).map (fun checked =>
  (checked.rows,checked.effect)) = some ([[0,1]],.unitary)
#guard (read [.bit] [.bit] [.ordinary [.bit] (.not (.basisInput 0))]).map (·.rows) = some [[1,0]]
#guard (read [.bit] [.bit] [.ordinary [.bit] (.bit false)]).isNone
#guard (read [.bit] [.bit] [.ordinary [.bit] (.xor (.basisInput 0) (.input 0))] [[.bit]]).map
  (·.rows) = some [[0,1],[1,0]]
#guard (read [.bit] [.bit] [.ordinary [.bit] (.and (.basisInput 0) (.input 0))] [[.bit]]).isNone

private def origin : Origin := ⟨"main","E","pub enum E{A,B,C}"⟩
private def nominal : Basis := [.enumeration origin ["A","B","C"]]
#guard (read nominal nominal [.ordinary nominal (.basisInput 0)]).map (·.rows) = some [[0,1,2]]

#print axioms QleisliKernel.SourceTypes.SourceBasisFunction.read
end QleisliKernel.Tests.SourceBasisFunction
