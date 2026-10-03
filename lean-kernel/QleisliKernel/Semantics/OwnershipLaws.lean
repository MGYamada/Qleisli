import QleisliKernel.Semantics.Ownership

/-! Consequences and counterexamples of the independent resource judgment.
No checker is imported: these obligations constrain the specification itself.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Semantics.Ownership
open Raw Observation

theorem Inputs.live {before after : State} {ports : List Port}
    (inputs : Inputs before ports after) : after.live = before.live ++ ports := by
  induction inputs with
  | nil state => simp
  | cons before port middle ports after head tail ih =>
    rw [ih,head.result]
    simp

/-- Omitting the returned owner is forbidden even when all ports have width 0. -/
theorem no_implicit_drop (ports : List Port) (classicalInputs classicalOutputs : List Nat)
    (effect : Effect) (nonempty : ports ≠ []) :
    ¬ ResourceSafe ⟨ports,classicalInputs,[],[],classicalOutputs,effect⟩ := by
  rintro ⟨initial,final,inputs,run,returned⟩
  have equal : final = initial := by cases run; rfl
  subst final
  have empty : initial.live = [] := by simpa using returned.count.symm
  have same := inputs.live
  simp only [List.nil_append] at same
  exact nonempty (same.symm.trans empty)

/-- No owner may disappear at an empty phi interface, including caller Unit. -/
theorem Phi.empty_left {left right : State} (phi : Phi left right []) : left.live = [] := by
  simpa using phi.leftCount.symm

theorem Phi.empty_right {left right : State} (phi : Phi left right []) : right.live = [] := by
  simpa using phi.rightCount.symm

/-- Every declared output, including an empty owner, is globally fresh. -/
theorem Pure.no_reuse {before after : State} {op : Raw.Op} (step : Pure before op after)
    (valid : Valid after) (token : Nat) (issued : token ∈ before.tokens) : token ∉ outputs op :=
  fun output => (step.fresh valid).1 token output issued

/-- A zero-width owner's empty wire list does not make it droppable. -/
theorem unit_drop : ¬ ResourceSafe ⟨[⟨0,[],0⟩],[],[],[],[],.unitary⟩ :=
  no_implicit_drop _ _ _ _ (by decide)

/-- A local index cannot fall back to axis 0 of a different live owner. -/
theorem unit_has_no_gate : ¬ Circuit 0 [⟨[],.hadamard 0⟩] := by
  simp [Circuit,actionAxes]

theorem unit_has_no_bit_access : ¬ Access ⟨[⟨0,[],0⟩],[0],[],[]⟩ (.gate .h 0 1) := by
  rintro ⟨port,present,bit⟩
  have same : port = ⟨0,[],0⟩ := List.mem_singleton.mp present.1
  subst port
  cases bit

theorem unit_return : ResourceSafe ⟨[⟨0,[],0⟩],[],[],[0],[],.unitary⟩ := by
  let state : State := ⟨[⟨0,[],0⟩],[0],[],[]⟩
  refine ⟨state,state,.cons _ _ _ _ _ ?_ (.nil _),.nil _ ?_,?_⟩
  · exact ⟨rfl,by simp,by simp,by simp,rfl⟩
  · constructor <;> simp [state]
  · constructor <;> simp [state]

end QleisliKernel.Semantics.Ownership
