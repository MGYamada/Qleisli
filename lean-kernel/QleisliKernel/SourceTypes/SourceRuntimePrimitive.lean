import QleisliKernel.SourceTypes.SourceRuntimeValues
import QleisliKernel.SourceTypes.CallName

/-! The existing pure original runtime-primitive evaluation.
The source traversal retains the equation from its same single evaluation.
This helper adds no native check, work charge or source-name authority.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace QleisliKernel.SourceTypes.SourceRuntimePrimitive
open QleisliKernel QleisliKernel.SourceTypes
open SourceRuntimeValues

def apply (kind : CallName.Primitive) (site : Site) (arguments : List Value)
    (nextOrdinal : Nat) : Except String
      (Value × List Semantics.SourceOwners.Owner × List Semantics.SourceOwners.Owner × Nat) := do
  match kind,arguments with
  | .emptyBits,[] => return ([.ordinary [.bits 0] (.ordinal 0)],[],[],nextOrdinal)
  | .h,[[.owner owner]] =>
    if owner.basis != [.bit] then throw "H runtime source type"
    return ([.owner owner],[],[],nextOrdinal)
  | .globalPhaseEighth,[[.owner owner]] => return ([.owner owner],[],[],nextOrdinal)
  | .measureZ,[[.owner owner]] =>
    if owner.basis != [.bit] then throw "measure_z runtime source type"
    return ([.ordinary [.bit] (.measured site [] owner)],[],[owner],nextOrdinal)
  | .discard,[[.owner owner]] => return ([.ordinary [.unit] .unit],[],[owner],nextOrdinal)
  | .unit,[[.ordinary basis _]] =>
    if basis != [.unit] then throw "unit requires ordinary Unit"
    let owner : Semantics.SourceOwners.Owner := ⟨nextOrdinal,[.unit]⟩
    return ([.owner owner],[owner],[],nextOrdinal+1)
  | .finish,[[.owner owner]] =>
    if owner.basis != [.unit] then throw "finish requires the exact Unit owner type"
    return ([.ordinary [.unit] .unit],[],[owner],nextOrdinal)
  | .join,[[.owner first],[.owner second]] =>
    if first.ordinal == second.ordinal then throw "join aliases owners"
    let owner : Semantics.SourceOwners.Owner := ⟨nextOrdinal,.pair :: first.basis ++ second.basis⟩
    return ([.owner owner],[owner],[first,second],nextOrdinal+1)
  | .split,[[.owner owner]] =>
    let (first,second) ← pairBases owner.basis
    let left : Semantics.SourceOwners.Owner := ⟨nextOrdinal,first⟩
    let right : Semantics.SourceOwners.Owner := ⟨nextOrdinal+1,second⟩
    return ([.tuple 2,.owner left,.owner right],[left,right],[owner],nextOrdinal+2)
  | _,_ => throw "runtime primitive argument or static-application shape"

end QleisliKernel.SourceTypes.SourceRuntimePrimitive
