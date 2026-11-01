import QleisliKernel.Semantics.Raw

/-! Original-body effect inference and the original-module public boundary.
An annotation is checked after inference; it never seeds body inference.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceEffect
open QleisliKernel.Semantics.Raw

def rank : Effect → Nat
  | .unitary => 0 | .iso => 1 | .observe => 2

def join (first second : Effect) : Effect :=
  if rank first ≤ rank second then second else first

def permits (declared : Option Effect) (inferred : Effect) : Bool :=
  declared.all fun bound => rank inferred ≤ rank bound

/-- Aliases, inlining and specialization do not change original module identity.
Private and same-module calls retain checked internal inference. -/
def visible (caller callee : String) (isPublic : Bool)
    (declared : Option Effect) (inferred : Effect) : Effect :=
  if caller != callee && isPublic then declared.getD inferred else inferred

theorem unitary_permits (effect : Effect) : permits (some .unitary) effect = true →
    effect = .unitary := by
  cases effect <;> simp [permits,rank]

theorem same_module (owner : String) (isPublic : Bool)
    (declared : Option Effect) (inferred : Effect) :
    visible owner owner isPublic declared inferred = inferred := by
  simp [visible]

end QleisliKernel.SourceTypes.SourceEffect
