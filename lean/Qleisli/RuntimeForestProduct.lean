import Qleisli.ExactMatrix
import QleisliKernel.Qirf.RuntimeForestFactorization
import QleisliKernel.Qirf.RuntimeScatterTransport

/-! Product coefficients of the actual two-binding sparse runtime code.
Original logical cardinalities and ordered Raw wire coordinates are separate.
All reference amplitudes remain arbitrary. The only bounded-to-complex bridge
below consumes an actual successful ownerCode read; no matrix equality implies
bounded availability, work equality, a Gram check or a new accepted handle.
No joined matrix is constructed by these sparse action definitions.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeForestProduct
open QleisliKernel QleisliKernel.Semantics.Exact
open QleisliKernel.Semantics.FiniteCarrier
open QleisliKernel.Semantics.Finite (bit gather)
open QleisliKernel.Qirf QleisliKernel.Qirf.RuntimeForestCode
open Qleisli.Semantics.Exact

def LayoutBounds (code : Layout) : Prop :=
  0 < code.labels.length ∧ ∀ label ∈ code.labels, label < 2^code.bits

private theorem tagBits_capacity (count : Nat) : count ≤ 2^tagBits count := by
  unfold tagBits
  split
  · omega
  · have remaining := Nat.lt_log2_self (n := count-1)
    omega

theorem tensor_bounds {first second : Layout}
    (left : LayoutBounds first) (right : LayoutBounds second) : LayoutBounds (tensor first second) := by
  constructor
  · have dimensions := (tensor_agrees (ofLayout_agrees first) (ofLayout_agrees second)).dimension
    rw [← dimensions]
    exact Nat.mul_pos left.1 right.1
  · intro label member
    change label ∈ second.labels.flatMap (fun high => first.labels.map (fun low => low+2^first.bits*high)) at member
    obtain ⟨high,highMember,mapped⟩ := List.mem_flatMap.mp member
    obtain ⟨low,lowMember,same⟩ := List.mem_map.mp mapped
    subst label
    change low+2^first.bits*high < 2^(first.bits+second.bits)
    rw [Nat.pow_add]
    calc
      low+2^first.bits*high < 2^first.bits+2^first.bits*high :=
        Nat.add_lt_add_right (left.2 low lowMember) _
      _ = 2^first.bits*(high+1) := by ring
      _ ≤ 2^first.bits*2^second.bits :=
        Nat.mul_le_mul_left _ (Nat.succ_le_of_lt (right.2 high highMember))

private theorem singleton_bounds : LayoutBounds QleisliKernel.Semantics.FiniteCarrier.singleton := by
  simp [LayoutBounds,QleisliKernel.Semantics.FiniteCarrier.singleton]

theorem leaf_bounds (atom : Atom) (code : Layout) (read : leaf atom = some code) : LayoutBounds code := by
  cases atom with
  | unit =>
    have same : code = QleisliKernel.Semantics.FiniteCarrier.singleton := by simpa [leaf] using read.symm
    subst code
    exact singleton_bounds
  | bit =>
    have same : code = ⟨1,[0,1]⟩ := by simpa [leaf] using read.symm
    subst code
    simp [LayoutBounds]
  | bits width =>
    have same : code = ⟨width,List.range (2^width)⟩ := by simpa [leaf] using read.symm
    subst code
    refine ⟨by simpa only [List.length_range] using Nat.two_pow_pos width,?_⟩
    intro label member
    exact List.mem_range.mp member
  | enumeration origin variants =>
    cases empty : variants.isEmpty with
    | true => simp [leaf,empty] at read
    | false =>
      have same : code = ⟨tagBits variants.length,List.range variants.length⟩ := by
        simpa [leaf,empty] using read.symm
      subst code
      have positive : 0 < variants.length := List.length_pos_iff.mpr (by
        intro nilEq
        simp [nilEq] at empty)
      refine ⟨by simpa only [List.length_range] using positive,?_⟩
      intro label member
      exact Nat.lt_of_lt_of_le (List.mem_range.mp member) (tagBits_capacity variants.length)
  | pair => simp [leaf] at read
  | tuple _ => simp [leaf] at read
  | record _ _ => simp [leaf] at read

private theorem fold_bounds (stack : List Layout) : ∀ (initial : Layout), LayoutBounds initial →
    (∀ code ∈ stack,LayoutBounds code) → LayoutBounds (stack.foldl tensor initial) := by
  induction stack with
  | nil => intro initial valid _all; exact valid
  | cons first rest ih =>
    intro initial valid all
    exact ih _ (tensor_bounds valid (all first (List.mem_cons_self)))
      (fun code member => all code (List.mem_cons_of_mem _ member))

private def StackBounds : Option (List Layout) → Prop
  | none => True
  | some stack => ∀ code ∈ stack,LayoutBounds code

private theorem step_bounds (atom : Atom) (pending : Option (List Layout)) (valid : StackBounds pending) :
    StackBounds (layoutStep atom pending) := by
  cases pending with
  | none => trivial
  | some stack =>
    cases arities : children atom with
    | none =>
      cases leaves : leaf atom with
      | none => simp [layoutStep,arities,leaves,StackBounds]
      | some first =>
        have all : ∀ code ∈ first::stack,LayoutBounds code := by
          intro code member
          rcases List.mem_cons.mp member with same | later
          · subst code
            exact leaf_bounds atom first leaves
          · exact valid code later
        simpa only [layoutStep,arities,leaves,bind,Option.bind,pure,StackBounds] using all
    | some arity =>
      by_cases tooMany : arity > stack.length
      · simp [layoutStep,arities,tooMany,StackBounds]
      · have combined := fold_bounds (stack.take arity) QleisliKernel.Semantics.FiniteCarrier.singleton singleton_bounds
          (fun code member => valid code (List.mem_of_mem_take member))
        have all : ∀ code ∈ (stack.take arity).foldl tensor QleisliKernel.Semantics.FiniteCarrier.singleton :: stack.drop arity,
            LayoutBounds code := by
          intro code member
          rcases List.mem_cons.mp member with same | later
          · subst code
            exact combined
          · exact valid code (List.mem_of_mem_drop later)
        simpa only [layoutStep,arities,bind,Option.bind,tooMany,if_false,StackBounds] using all

private theorem stack_bounds (basis : Basis) : StackBounds (basis.foldr layoutStep (some [])) := by
  induction basis with
  | nil => intro code member; cases member
  | cons atom rest ih => exact step_bounds atom _ ih

/-- Bounds follow from the independent original tree interpreter, including
padded enums, nested records and every distinct singleton carrier. -/
theorem layout_bounds (basis : Basis) (code : Layout)
    (read : QleisliKernel.Semantics.FiniteCarrier.layout basis = some code) : LayoutBounds code := by
  have all := stack_bounds basis
  rw [layout_continuation basis code read []] at all
  exact all code (List.mem_singleton_self code)

theorem owner_bounds {binding} (owner : OwnerCode binding) : LayoutBounds owner.layout :=
  layout_bounds binding.owner.basis owner.layout owner.reference.1

private theorem gather_cons (label first : Nat) (rest : List Nat) :
    gather label (first::rest) = bit label first+2*gather label rest := by
  have weights (pairs : List (Nat × Nat)) :
      (pairs.map (fun pair => bit label pair.1*2^(pair.2+1))).sum =
        2*(pairs.map (fun pair => bit label pair.1*2^pair.2)).sum := by
    induction pairs with
    | nil => rfl
    | cons first rest ih =>
      simp only [List.map_cons,List.sum_cons]
      rw [ih]
      simp only [Nat.pow_succ,Nat.mul_add]
      ac_rfl
  unfold gather
  simp only [List.zipIdx_cons,List.map_cons,List.sum_cons,Nat.pow_zero,Nat.mul_one]
  rw [List.zipIdx_succ]
  simp only [List.map_map,Function.comp_def]
  rw [weights]

theorem gather_append (label : Nat) (first second : List Nat) :
    gather label (first ++ second) = gather label first+2^first.length*gather label second := by
  induction first with
  | nil => simp [gather]
  | cons first rest ih =>
    simp only [List.cons_append,gather_cons,ih,List.length_cons,Nat.pow_succ]
    ring

theorem gather_bound (label : Nat) (axes : List Nat) : gather label axes < 2^axes.length := by
  induction axes with
  | nil => simp [gather]
  | cons first rest ih =>
    rw [gather_cons,List.length_cons,Nat.pow_succ]
    have small := RuntimeScatterTransport.bit_lt label first
    omega

private theorem sparse_coefficient (code : Sparse) (physical logical : Nat) :
    scalar (sparseEntry code physical logical) = if code.coordinate logical = some physical then 1 else 0 := by
  by_cases equal : code.coordinate logical = some physical <;>
    simp [sparseEntry,beq_iff_eq,equal,Qleisli.Exact.scalar_one_meaning,Qleisli.Exact.scalar_zero_meaning]

private theorem packed_equal (bits low high otherLow otherHigh : Nat)
    (lowBound : low < 2^bits) (otherBound : otherLow < 2^bits) :
    low+2^bits*high = otherLow+2^bits*otherHigh ↔ low = otherLow ∧ high = otherHigh := by
  constructor
  · intro equal
    change QleisliKernel.FiniteRestriction.pack bits low high = QleisliKernel.FiniteRestriction.pack bits otherLow otherHigh at equal
    have lows := congrArg (· % 2^bits) equal
    have highs := congrArg (· / 2^bits) equal
    exact ⟨by simpa only [QleisliKernel.FiniteRestriction.pack_low _ _ _ lowBound,
      QleisliKernel.FiniteRestriction.pack_low _ _ _ otherBound] using lows,
      by simpa only [QleisliKernel.FiniteRestriction.pack_high _ _ _ lowBound,
        QleisliKernel.FiniteRestriction.pack_high _ _ _ otherBound] using highs⟩
  · rintro ⟨rfl,rfl⟩
    rfl

theorem tensor_coefficient (left right : Layout) (valid : LayoutBounds left)
    (low high logical : Nat) (bound : low < 2^left.bits) :
    scalar (sparseEntry ((Sparse.ofLayout left).tensor (.ofLayout right)) (low+2^left.bits*high) logical) =
      scalar (sparseEntry (.ofLayout left) low (logical % left.labels.length)) *
        scalar (sparseEntry (.ofLayout right) high (logical / left.labels.length)) := by
  simp only [sparse_coefficient]
  cases leftRead : left.labels[logical % left.labels.length]? with
  | none => simp [Sparse.tensor,Sparse.ofLayout,leftRead]
  | some lowCode =>
    cases rightRead : right.labels[logical / left.labels.length]? with
    | none => simp [Sparse.tensor,Sparse.ofLayout,leftRead,rightRead]
    | some highCode =>
      have inside := valid.2 lowCode (List.mem_of_getElem? leftRead)
      have condition := packed_equal left.bits lowCode highCode low high inside bound
      simp only [Sparse.tensor,Sparse.ofLayout,leftRead,rightRead,bind,Option.bind,pure,Option.some.injEq,condition]
      by_cases equalLow : lowCode = low <;> by_cases equalHigh : highCode = high <;> simp [equalLow,equalHigh]

theorem encoding_coefficient (code : Layout) (physical logical : Nat)
    (rowBound : physical < 2^code.bits) (colBound : logical < code.labels.length) :
    scalar (sparseEntry (.ofLayout code) physical logical) = entry (QleisliKernel.Semantics.FiniteCarrier.encoding code) physical logical :=
  congrArg scalar ((ofLayout_agrees code).encodingEntry physical logical rowBound colBound)

private theorem pair_product_coefficient {roles state checked} (frame : @Frame roles state checked)
    (selected spectator : RuntimeOwnerMap.Binding) (ordered : checked.bindings = [selected,spectator]) :
    ∃ left : OwnerCode selected, ∃ right : OwnerCode spectator,
      frame.code.dimension = left.layout.labels.length*right.layout.labels.length ∧
      roles = [selected.owner,spectator.owner] ∧ ∀ physical logical,
        scalar (frame.embedding physical logical) =
          scalar (sparseEntry (.ofLayout left.layout)
            (gather physical (selected.port.wires.map state.quantum.frame.idxOf)) (logical % left.layout.labels.length)) *
          scalar (sparseEntry (.ofLayout right.layout)
            (gather physical (spectator.port.wires.map state.quantum.frame.idxOf)) (logical / left.layout.labels.length)) := by
  obtain ⟨left,right,_bits,dimension,coordinates⟩ := frame.pairCoordinates selected spectator ordered
  have identities := frame.pairIdentities selected spectator ordered
  refine ⟨left,right,dimension,identities.1,?_⟩
  intro physical logical
  have lowBound : gather physical (selected.port.wires.map state.quantum.frame.idxOf) < 2^left.layout.bits := by
    simpa only [List.length_map,left.reference.2.2] using
      gather_bound physical (selected.port.wires.map state.quantum.frame.idxOf)
  have packed : gather physical (forestAxes state.quantum.frame checked.bindings) =
      gather physical (selected.port.wires.map state.quantum.frame.idxOf)+
        2^left.layout.bits*gather physical (spectator.port.wires.map state.quantum.frame.idxOf) := by
    rw [identities.2,gather_append,List.length_map,left.reference.2.2]
  have sameCode : sparseEntry frame.code (gather physical (forestAxes state.quantum.frame checked.bindings)) logical =
      sparseEntry ((Sparse.ofLayout left.layout).tensor (.ofLayout right.layout))
        (gather physical (forestAxes state.quantum.frame checked.bindings)) logical := by
    unfold sparseEntry
    rw [coordinates logical]
    rfl
  change scalar (sparseEntry frame.code (gather physical (forestAxes state.quantum.frame checked.bindings)) logical) = _
  rw [sameCode,packed]
  exact tensor_coefficient left.layout right.layout (owner_bounds left) _ _ logical lowBound

/-- These are the two independent original owner encodings at their actual
ordered Raw wires. The logical radix is cardinality, including enum padding. -/
theorem pair_product_entry {roles state checked} (frame : @Frame roles state checked)
    (selected spectator : RuntimeOwnerMap.Binding) (ordered : checked.bindings = [selected,spectator]) :
    ∃ left : OwnerCode selected, ∃ right : OwnerCode spectator,
      frame.code.dimension = left.layout.labels.length*right.layout.labels.length ∧
      roles = [selected.owner,spectator.owner] ∧ ∀ physical logical, logical < frame.code.dimension →
        scalar (frame.embedding physical logical) =
          entry (QleisliKernel.Semantics.FiniteCarrier.encoding left.layout)
            (gather physical (selected.port.wires.map state.quantum.frame.idxOf)) (logical % left.layout.labels.length) *
          entry (QleisliKernel.Semantics.FiniteCarrier.encoding right.layout)
            (gather physical (spectator.port.wires.map state.quantum.frame.idxOf)) (logical / left.layout.labels.length) := by
  obtain ⟨left,right,dimension,identities,coefficients⟩ := pair_product_coefficient frame selected spectator ordered
  refine ⟨left,right,dimension,identities,?_⟩
  intro physical logical bound
  have lowRow : gather physical (selected.port.wires.map state.quantum.frame.idxOf) < 2^left.layout.bits := by
    simpa only [List.length_map,left.reference.2.2] using
      gather_bound physical (selected.port.wires.map state.quantum.frame.idxOf)
  have highRow : gather physical (spectator.port.wires.map state.quantum.frame.idxOf) < 2^right.layout.bits := by
    simpa only [List.length_map,right.reference.2.2] using
      gather_bound physical (spectator.port.wires.map state.quantum.frame.idxOf)
  have lowCol : logical % left.layout.labels.length < left.layout.labels.length :=
    Nat.mod_lt _ (owner_bounds left).1
  have highCol : logical / left.layout.labels.length < right.layout.labels.length :=
    Nat.div_lt_of_lt_mul (by rw [← dimension]; exact bound)
  rw [coefficients physical logical,encoding_coefficient left.layout _ _ lowRow lowCol,
    encoding_coefficient right.layout _ _ highRow highCol]

/-- A lazy complex action of the same sparse code; no joined encoding matrix
or restriction on the supplied joint amplitudes is introduced. -/
noncomputable def referenceAction {roles state checked} (frame : @Frame roles state checked)
    {Reference : Type} (joint : Nat → Reference → ℂ) (physical : Nat) (reference : Reference) : ℂ :=
  ((List.range frame.code.dimension).map fun logical => scalar (frame.embedding physical logical)*joint logical reference).sum

/-- Sum the actual product coefficients against an arbitrary logical/reference
family, in the existing low-first mixed-radix order. This is a total complex
identity; no bounded scalar computation is reassociated. -/
theorem pair_product_action {Reference : Type} {roles state checked} (frame : @Frame roles state checked)
    (selected spectator : RuntimeOwnerMap.Binding) (ordered : checked.bindings = [selected,spectator]) :
    ∃ left : OwnerCode selected, ∃ right : OwnerCode spectator,
      frame.code.dimension = left.layout.labels.length*right.layout.labels.length ∧
      roles = [selected.owner,spectator.owner] ∧ ∀ (joint : Nat → Reference → ℂ) physical reference,
        referenceAction frame joint physical reference =
          ((List.range (left.layout.labels.length*right.layout.labels.length)).map fun logical =>
            entry (QleisliKernel.Semantics.FiniteCarrier.encoding left.layout)
              (gather physical (selected.port.wires.map state.quantum.frame.idxOf)) (logical % left.layout.labels.length) *
            entry (QleisliKernel.Semantics.FiniteCarrier.encoding right.layout)
              (gather physical (spectator.port.wires.map state.quantum.frame.idxOf)) (logical / left.layout.labels.length) *
            joint logical reference).sum := by
  obtain ⟨left,right,dimension,identities,entries⟩ := pair_product_entry frame selected spectator ordered
  refine ⟨left,right,dimension,identities,?_⟩
  intro joint physical reference
  unfold referenceAction
  rw [dimension]
  apply Qleisli.Exact.sum_map_congr
  intro logical member
  rw [entries physical logical (by rw [dimension]; exact List.mem_range.mp member)]

/-- If the enclosing native component retains the actual ownerCode execution
for this exact forest, its successful result has this sparse complex action.
No old reader execution or joined matrix/isometry receipt is fabricated. -/
theorem ownerCode_reference_action {Reference : Type} {roles state checked} (frame : @Frame roles state checked)
    (native : Matrix) (before after : Nat)
    (ran : (Carrier.ownerCode (carrierOwners checked.bindings)).run before = (.ok native,after))
    (joint : Nat → Reference → ℂ) (physical : Nat) (reference : Reference)
    (bound : gather physical (forestAxes state.quantum.frame checked.bindings) < 2^frame.code.bits) :
    action native joint (gather physical (forestAxes state.quantum.frame checked.bindings)) reference =
      referenceAction frame joint physical reference := by
  obtain ⟨⟨codeBefore,codeAfter,codeRan⟩,_owners⟩ :=
    Carrier.ownerCode_conditions (carrierOwners checked.bindings) native before after ran
  obtain ⟨layout,_gramBefore,_gramAfter,original,nativeEq,_gram⟩ :=
    QleisliKernel.FiniteCarrier.code_conditions _ _ codeBefore codeAfter codeRan
  obtain ⟨whole,wholeRead,same⟩ := frame.originalCode
  have equal : whole = layout := Option.some.inj (wholeRead.symm.trans original)
  subst whole
  rw [nativeEq]
  unfold action referenceAction
  change ((List.range layout.labels.length).map fun logical =>
    scalar ((QleisliKernel.Semantics.FiniteCarrier.encoding layout).entry
      (gather physical (forestAxes state.quantum.frame checked.bindings)) logical)*joint logical reference).sum = _
  rw [← same.dimension]
  apply Qleisli.Exact.sum_map_congr
  intro logical member
  have rowBound : gather physical (forestAxes state.quantum.frame checked.bindings) < 2^layout.bits := by
    rw [← same.bits]
    exact bound
  have colBound : logical < layout.labels.length := by
    rw [← same.dimension]
    exact List.mem_range.mp member
  change scalar ((QleisliKernel.Semantics.FiniteCarrier.encoding layout).entry
    (gather physical (forestAxes state.quantum.frame checked.bindings)) logical)*joint logical reference =
      scalar (sparseEntry frame.code (gather physical (forestAxes state.quantum.frame checked.bindings)) logical)*
        joint logical reference
  rw [same.encodingEntry _ _ rowBound colBound]

#print axioms layout_bounds
#print axioms pair_product_entry
#print axioms pair_product_action
#print axioms ownerCode_reference_action

end Qleisli.RuntimeForestProduct
