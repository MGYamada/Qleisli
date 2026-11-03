import Qleisli.RuntimeNominalSupport

/-! Injectivity of the independent finite carrier's physical code labels.
The proof follows the actual prefix interpreter, including ordered tensors,
nominal leaves and zero-width nodes. It assumes no fresh encoding/Gram run,
materializes no joined matrix and changes no reader or acceptance condition.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeCarrierLabels
open QleisliKernel QleisliKernel.Qirf QleisliKernel.Semantics.FiniteCarrier
open RuntimeForestCode
open Qleisli.RuntimeForestProduct

/-- Distinct high labels cannot share a packed physical coordinate because
every actual low label is below the retained first carrier's bit capacity. -/
theorem tensor_labels {first second : Layout} (left : LayoutBounds first)
    (firstUnique : first.labels.Nodup) (secondUnique : second.labels.Nodup) :
    (tensor first second).labels.Nodup := by
  change (second.labels.flatMap fun high => first.labels.map fun low => low+2^first.bits*high).Nodup
  apply List.nodup_flatMap.mpr
  constructor
  · intro high _member
    exact firstUnique.map (fun _ _ same => Nat.add_right_cancel same)
  · apply secondUnique.imp
    intro high other different
    apply List.disjoint_left.mpr
    intro value leftMember rightMember
    obtain ⟨low,lowMember,leftEq⟩ := List.mem_map.mp leftMember
    obtain ⟨another,anotherMember,rightEq⟩ := List.mem_map.mp rightMember
    have equal : QleisliKernel.FiniteRestriction.pack first.bits low high =
        QleisliKernel.FiniteRestriction.pack first.bits another other := leftEq.trans rightEq.symm
    have highEq : QleisliKernel.FiniteRestriction.pack first.bits low high / 2^first.bits =
        QleisliKernel.FiniteRestriction.pack first.bits another other / 2^first.bits :=
      congrArg (fun label => label / 2^first.bits) equal
    rw [QleisliKernel.FiniteRestriction.pack_high _ _ _ (left.2 low lowMember),
      QleisliKernel.FiniteRestriction.pack_high _ _ _ (left.2 another anotherMember)] at highEq
    exact different highEq

private theorem leaf_labels (atom : Atom) (code : Layout) (read : leaf atom = some code) : code.labels.Nodup := by
  cases atom with
  | unit =>
    have same : code = QleisliKernel.Semantics.FiniteCarrier.singleton := by simpa [leaf] using read.symm
    subst code
    simp [QleisliKernel.Semantics.FiniteCarrier.singleton]
  | bit =>
    have same : code = ⟨1,[0,1]⟩ := by simpa [leaf] using read.symm
    subst code
    simp
  | bits width =>
    have same : code = ⟨width,List.range (2^width)⟩ := by simpa [leaf] using read.symm
    subst code
    exact List.nodup_range
  | enumeration origin variants =>
    cases empty : variants.isEmpty with
    | true => simp [leaf,empty] at read
    | false =>
      have same : code = ⟨tagBits variants.length,List.range variants.length⟩ := by
        simpa [leaf,empty] using read.symm
      subst code
      exact List.nodup_range
  | pair => simp [leaf] at read
  | tuple _ => simp [leaf] at read
  | record _ _ => simp [leaf] at read

private def Valid (code : Layout) : Prop := LayoutBounds code ∧ code.labels.Nodup

private theorem singleton_valid : Valid QleisliKernel.Semantics.FiniteCarrier.singleton := by
  constructor
  · simp [LayoutBounds,QleisliKernel.Semantics.FiniteCarrier.singleton]
  · simp [QleisliKernel.Semantics.FiniteCarrier.singleton]

private theorem fold_valid (stack : List Layout) : ∀ initial, Valid initial →
    (∀ code ∈ stack,Valid code) → Valid (stack.foldl tensor initial) := by
  induction stack with
  | nil => intro initial valid _all; exact valid
  | cons first rest ih =>
    intro initial valid all
    have head := all first (List.mem_cons_self)
    exact ih _ ⟨tensor_bounds valid.1 head.1,tensor_labels valid.1 valid.2 head.2⟩
      (fun code member => all code (List.mem_cons_of_mem _ member))

private def StackValid : Option (List Layout) → Prop
  | none => True
  | some stack => ∀ code ∈ stack,Valid code

private theorem step_valid (atom : Atom) (pending : Option (List Layout)) (valid : StackValid pending) :
    StackValid (layoutStep atom pending) := by
  cases pending with
  | none => trivial
  | some stack =>
    cases arities : children atom with
    | none =>
      cases leaves : leaf atom with
      | none => simp [layoutStep,arities,leaves,StackValid]
      | some first =>
        have all : ∀ code ∈ first::stack,Valid code := by
          intro code member
          rcases List.mem_cons.mp member with same | later
          · subst code
            exact ⟨leaf_bounds atom first leaves,leaf_labels atom first leaves⟩
          · exact valid code later
        simpa only [layoutStep,arities,leaves,bind,Option.bind,pure,StackValid] using all
    | some arity =>
      by_cases tooMany : arity > stack.length
      · simp [layoutStep,arities,tooMany,StackValid]
      · have combined := fold_valid (stack.take arity) QleisliKernel.Semantics.FiniteCarrier.singleton singleton_valid
          (fun code member => valid code (List.mem_of_mem_take member))
        have all : ∀ code ∈ (stack.take arity).foldl tensor QleisliKernel.Semantics.FiniteCarrier.singleton :: stack.drop arity,Valid code := by
          intro code member
          rcases List.mem_cons.mp member with same | later
          · subst code
            exact combined
          · exact valid code (List.mem_of_mem_drop later)
        simpa only [layoutStep,arities,bind,Option.bind,tooMany,if_false,StackValid] using all

private theorem stack_valid (basis : Basis) : StackValid (basis.foldr layoutStep (some [])) := by
  induction basis with
  | nil => intro code member; cases member
  | cons atom rest ih => exact step_valid atom _ ih

theorem layout_labels (basis : Basis) (code : Layout)
    (read : QleisliKernel.Semantics.FiniteCarrier.layout basis = some code) : code.labels.Nodup := by
  have all := stack_valid basis
  rw [layout_continuation basis code read []] at all
  exact (all code (List.mem_singleton_self code)).2

theorem owner_labels {binding} (actual : OwnerCode binding) : actual.layout.labels.Nodup :=
  layout_labels binding.owner.basis actual.layout actual.reference.1

theorem owner_label_injective {binding} (actual : OwnerCode binding) (first second : Nat)
    (inside : first < actual.layout.labels.length)
    (same : actual.layout.labels[first]? = actual.layout.labels[second]?) : first = second :=
  (List.getElem?_inj inside (owner_labels actual)).mp same

#print axioms tensor_labels
#print axioms layout_labels
#print axioms owner_label_injective

end Qleisli.RuntimeCarrierLabels
