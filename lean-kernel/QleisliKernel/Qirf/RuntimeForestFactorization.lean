import QleisliKernel.Qirf.RuntimeForestCode

/-! Coordinates of a complete two-owner runtime forest, using the retained
original carrier reads. Logical indices use each owner's actual cardinality;
physical indices use the actual caller-frame order and each port's ordered
wires. The exact binding list retains nominal trees and distinct zero-width
owners. No joined matrix, owner permutation, Gram check or accepted handle is
constructed. General selected/spectator permutations remain a separate duty.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace QleisliKernel.Qirf.RuntimeForestCode
open QleisliKernel Finite Semantics.Exact Semantics.FiniteCarrier
open RuntimeOwnerMap (Binding)

theorem OwnerCode.reference {binding : Binding} (owner : OwnerCode binding) :
    Semantics.FiniteCarrier.layout binding.owner.basis = some owner.layout ∧
      binding.port.bits = owner.layout.bits ∧ binding.port.wires.length = owner.layout.bits := by
  obtain ⟨before,after,ran⟩ := owner.original
  exact Carrier.readOwner_conditions ⟨binding.port,binding.owner.basis⟩ owner.layout before after ran

private theorem layoutStep_suffix (atom : Atom) (before after suffix : List Layout)
    (read : layoutStep atom (some before) = some after) :
    layoutStep atom (some (before ++ suffix)) = some (after ++ suffix) := by
  cases arities : children atom with
  | none =>
    cases leaves : leaf atom with
    | none => simp [layoutStep,arities,leaves] at read
    | some first =>
      have same : after = first :: before := by
        simpa [layoutStep,arities,leaves] using read.symm
      subst after
      simp [layoutStep,arities,leaves]
  | some arity =>
    by_cases tooMany : arity > before.length
    · simp [layoutStep,arities,tooMany] at read
    · have bounded : arity ≤ before.length := Nat.le_of_not_gt tooMany
      have stillBounded : ¬ arity > (before ++ suffix).length := by
        simp only [List.length_append]
        omega
      have same : after = (before.take arity).foldl tensor singleton :: before.drop arity := by
        simpa [layoutStep,arities,tooMany] using read.symm
      subst after
      change (if arity > (before ++ suffix).length then none else
        some (((before ++ suffix).take arity).foldl tensor singleton ::
          (before ++ suffix).drop arity)) = _
      simp only [if_neg stillBounded,List.take_append_of_le_length bounded,
        List.drop_append_of_le_length bounded,List.cons_append]

private theorem layoutFold_suffix (basis : Basis) (before after suffix : List Layout)
    (read : basis.foldr layoutStep (some before) = some after) :
    basis.foldr layoutStep (some (before ++ suffix)) = some (after ++ suffix) := by
  induction basis generalizing before after with
  | nil =>
    have same : before = after := Option.some.inj read
    subst after
    rfl
  | cons atom rest ih =>
    cases tailRead : rest.foldr layoutStep (some before) with
    | none => simp [List.foldr_cons,tailRead,layoutStep] at read
    | some middle =>
      have headRead : layoutStep atom (some middle) = some after := by
        simpa only [List.foldr_cons,tailRead] using read
      have tail := ih before middle tailRead
      simpa only [List.foldr_cons,tail] using layoutStep_suffix atom middle after suffix headRead

private theorem layoutFold_original (basis : Basis) (code : Layout)
    (read : Semantics.FiniteCarrier.layout basis = some code) :
    basis.foldr layoutStep (some []) = some [code] := by
  unfold Semantics.FiniteCarrier.layout at read
  cases folded : basis.foldr layoutStep (some []) with
  | none => simp [folded] at read
  | some stack =>
    cases stack with
    | nil => simp [folded] at read
    | cons first rest =>
      cases rest with
      | cons second rest => simp [folded] at read
      | nil =>
        have same : first = code := by simpa only [folded,bind,Option.bind,pure,Option.some.injEq] using read
        subst code
        exact folded

/-- A successful original prefix tree cannot consume a neighbouring owner's
nodes. It pushes the same layout over every existing continuation stack. -/
theorem layout_continuation (basis : Basis) (code : Layout)
    (read : Semantics.FiniteCarrier.layout basis = some code) (suffix : List Layout) :
    basis.foldr layoutStep (some suffix) = some (code :: suffix) := by
  simpa only [List.nil_append,List.cons_append] using
    layoutFold_suffix basis [] [code] suffix (layoutFold_original basis code read)

private theorem singleton_tensor (code : Layout) : tensor singleton code = code := by
  cases code
  simp [tensor,singleton]

/-- Derive the complete pair's layout from the two original owner reads,
without assuming a forest equality or identifying owners by their width. -/
theorem layout_pair_reference (first second : Basis) (left right : Layout)
    (leftRead : Semantics.FiniteCarrier.layout first = some left)
    (rightRead : Semantics.FiniteCarrier.layout second = some right) :
    Semantics.FiniteCarrier.layout (.pair :: first ++ second) = some (tensor left right) := by
  have firstRead := layout_continuation first left leftRead [right]
  have secondRead := layout_continuation second right rightRead []
  unfold Semantics.FiniteCarrier.layout
  rw [List.foldr_cons,List.foldr_append,secondRead,firstRead]
  simp [layoutStep,children,singleton_tensor]

/-- Exact selected/spectator identity and physical order for this complete
two-owner frame. Empty wire lists preserve their separate owner positions. -/
theorem Frame.pairIdentities {roles state checked} (_frame : @Frame roles state checked)
    (selected spectator : Binding) (ordered : checked.bindings = [selected,spectator]) :
    roles = [selected.owner,spectator.owner] ∧
      forestAxes state.quantum.frame checked.bindings =
        selected.port.wires.map state.quantum.frame.idxOf ++
          spectator.port.wires.map state.quantum.frame.idxOf := by
  constructor
  · simpa only [ordered,List.map_cons,List.map_nil] using checked.ordered.symm
  · simp only [forestAxes,ordered,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.map_append]

/-- The first logical owner varies fastest by its actual logical dimension,
which can differ from a power of two. Both layouts come from the retained
Carrier.readOwner executions in this same complete Frame. -/
theorem Frame.pairCoordinates {roles state checked} (frame : @Frame roles state checked)
    (selected spectator : Binding) (ordered : checked.bindings = [selected,spectator]) :
    ∃ left : OwnerCode selected, ∃ right : OwnerCode spectator,
      frame.code.bits = left.layout.bits + right.layout.bits ∧
      frame.code.dimension = left.layout.labels.length * right.layout.labels.length ∧
      ∀ logical, frame.code.coordinate logical = (do
        let low ← left.layout.labels[logical % left.layout.labels.length]?
        let high ← right.layout.labels[logical / left.layout.labels.length]?
        pure (low + 2^left.layout.bits * high)) := by
  have owners : OwnerCodes [selected,spectator] := ordered ▸ frame.owners
  cases owners with
  | cons left rest =>
    cases rest with
    | cons right tail =>
      cases tail
      have pairRead := layout_pair_reference selected.owner.basis spectator.owner.basis
        left.layout right.layout left.reference.1 right.reference.1
      have wholeRead : Semantics.FiniteCarrier.layout (forestBasis checked.bindings) =
          some (tensor left.layout right.layout) := by
        simpa only [forestBasis,carrierOwners,ordered,List.map_cons,List.map_nil,
          Semantics.CarrierInterface.forest] using pairRead
      obtain ⟨whole,original,same⟩ := frame.originalCode
      have equal : whole = tensor left.layout right.layout := Option.some.inj (original.symm.trans wholeRead)
      subst whole
      have product := tensor_agrees (ofLayout_agrees left.layout) (ofLayout_agrees right.layout)
      refine ⟨left,right,same.bits,same.dimension.trans product.dimension.symm,?_⟩
      intro logical
      exact (same.labels logical).trans (product.labels logical).symm

/-- Concrete sparse embedding in the real Raw frame. The mixed-radix logical
coordinate and the ordered physical axes are independently retained here. -/
theorem Frame.pairEmbedding {roles state checked} (frame : @Frame roles state checked)
    (selected spectator : Binding) (ordered : checked.bindings = [selected,spectator]) :
    ∃ left : OwnerCode selected, ∃ right : OwnerCode spectator,
      roles = [selected.owner,spectator.owner] ∧ ∀ physical logical,
        frame.embedding physical logical = (if (do
          let low ← left.layout.labels[logical % left.layout.labels.length]?
          let high ← right.layout.labels[logical / left.layout.labels.length]?
          pure (low + 2^left.layout.bits * high)) == some (Semantics.Finite.gather physical
            (selected.port.wires.map state.quantum.frame.idxOf ++
              spectator.port.wires.map state.quantum.frame.idxOf))
          then Scalar.one else Scalar.zero) := by
  obtain ⟨left,right,_bits,_dimension,coordinates⟩ := frame.pairCoordinates selected spectator ordered
  have identities := frame.pairIdentities selected spectator ordered
  refine ⟨left,right,identities.1,?_⟩
  intro physical logical
  change (if frame.code.coordinate logical == some
    (Semantics.Finite.gather physical (forestAxes state.quantum.frame checked.bindings))
      then Scalar.one else Scalar.zero) = _
  rw [coordinates,identities.2]

end QleisliKernel.Qirf.RuntimeForestCode
