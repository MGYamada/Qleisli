import Qleisli.RuntimeForestRegroup
import QleisliKernel.Qirf.RuntimePureBody

/-! The actual source target's digit in the complete caller logical order.
Cardinalities come from the same retained original owner-code reads, including
every dimension-one owner. The authentic output partition exposes the two Bit
roles as low digits without replacing the original dense logical coordinate.
The output-code slice action uses this index equality. Its physical scatter
identity and the final intertwining equation require separate proofs.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeTargetDigit
open QleisliKernel QleisliKernel.Qirf
open RuntimeOwnerMap (Binding Map)
open RuntimeForestCode RuntimeOwnerCodeReindex
open Qleisli.MixedRadix Qleisli.RuntimeForestRegroup

/-- Replace only this exact source binding's logical digit. Its source owner,
nominal tree and actual port identity participate in the equality test. -/
def update {roles state checked} (frame : @Frame roles state checked) (target : Binding)
    (logical replacement : Nat) : Nat :=
  encode checked.bindings (dimensionAt frame.owners) fun binding =>
    if binding = target then replacement else decode checked.bindings (dimensionAt frame.owners) logical binding

private theorem bit_card {bindings} (owners : OwnerCodes bindings) (binding : Binding)
    (member : binding ∈ bindings) (basis : binding.owner.basis = [.bit]) :
    dimensionAt owners binding = 2 := by
  obtain ⟨actual,_ran⟩ := lookup_exists owners binding member
  have original := actual.reference.1
  rw [basis] at original
  change some (⟨1,[0,1]⟩ : QleisliKernel.Semantics.FiniteCarrier.Layout) = some actual.layout at original
  have layout := Option.some.inj original
  rw [dimensionAt_eq owners binding member actual,← layout]
  rfl

/-- At an actual two-Bit source selection, changing the original caller's
target digit is exactly changing the second low digit after its proved Regroup
bijection. All other original digits, including Unit, retain their values.
Physical bit positions or owner ordinals never supply logical strides. -/
theorem source_target_update
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {inputCode outputCode}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (selectorBasis : selector.basis = [.bit]) (targetBasis : target.basis = [.bit])
    {selectorBits targetBits retained restricted}
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      codes.owners.before codes.owners.transport.after)
    (logical replacement : Nat) (bound : logical < literal.outputCode.code.dimension) (small : replacement < 2) :
    let output := literal.outputCode
    let order := codes.owners.transport.after.bindings
    let wanted := codes.owners.returned.toList ++
      RuntimeSelectionPartition.complement order codes.owners.returned.toList
    update output codes.owners.returned.second logical replacement < output.code.dimension ∧
      (∀ binding ∈ order,
        decode order (dimensionAt output.owners) (update output codes.owners.returned.second logical replacement) binding =
          if binding = codes.owners.returned.second then replacement else
            decode order (dimensionAt output.owners) logical binding) ∧
      regroupIndex output wanted (update output codes.owners.returned.second logical replacement) =
        regroupIndex output wanted logical % 2 + 2*replacement + 4*(regroupIndex output wanted logical / 4) := by
  let output := literal.outputCode
  let order := codes.owners.transport.after.bindings
  let first := codes.owners.returned.first
  let second := codes.owners.returned.second
  let rest := RuntimeSelectionPartition.complement order codes.owners.returned.toList
  let wanted := codes.owners.returned.toList ++ rest
  let cards := dimensionAt output.owners
  let digits := decode order cards logical
  let changed := fun binding => if binding = second then replacement else digits binding
  have actual := RuntimeSelectionPartition.order_values _ _ _ codes.owners.returned.ordered
  have members : first ∈ order ∧ second ∈ order := ⟨actual.1 (by simp [first]),actual.1 (by simp [second])⟩
  have originalOwners : first.owner = selector ∧ second.owner = target := by
    simpa only [List.map_cons,List.map_nil,List.cons.injEq,and_true] using actual.2
  have firstCard : cards first = 2 := bit_card output.owners first members.1 (by rw [originalOwners.1,selectorBasis])
  have secondCard : cards second = 2 := bit_card output.owners second members.2 (by rw [originalOwners.2,targetBasis])
  have unique : order.Nodup :=
    List.Pairwise.of_map (fun binding : Binding => binding.port.token)
      (fun _ _ different equal => different (congrArg (fun binding : Binding => binding.port.token) equal))
      codes.owners.transport.after.tokensDistinct
  have permutation : wanted.Perm order := RuntimeSelectionPartition.source_output_partition frame codes.owners
  have groupedUnique : (first::second::rest).Nodup := permutation.symm.nodup unique
  have firstDifferent : first ≠ second := by
    intro equal
    apply (List.nodup_cons.mp groupedUnique).1
    rw [equal]
    exact List.mem_cons_self
  have secondAbsent : second ∉ rest := (List.nodup_cons.mp (List.nodup_cons.mp groupedUnique).2).1
  have positive := cards_positive output.owners
  have logicalBound : logical < volume order cards := by rw [frame_volume output]; exact bound
  have digitBounds : ∀ binding ∈ order,digits binding < cards binding :=
    decode_bound order cards logical positive logicalBound
  have changedBounds : ∀ binding ∈ order,changed binding < cards binding := by
    intro binding member
    by_cases same : binding = second
    · subst binding
      simpa only [changed,if_pos rfl,secondCard] using small
    · simpa only [changed,if_neg same] using digitBounds binding member
  have updateBound : update output second logical replacement < output.code.dimension := by
    rw [← frame_volume output]
    exact encode_bound order cards changed changedBounds
  have updateDigits : ∀ binding ∈ order,
      decode order cards (update output second logical replacement) binding = changed binding :=
    decode_encode order cards changed changedBounds
  have newEncoding : regroupIndex output wanted (update output second logical replacement) =
      encode wanted cards changed := by
    apply encode_congr
    intro binding member
    exact updateDigits binding (permutation.mem_iff.mp member)
  have tail : encode rest cards changed = encode rest cards digits := by
    apply encode_congr
    intro binding member
    have different : binding ≠ second := by intro equal; exact secondAbsent (equal ▸ member)
    exact if_neg different
  have oldPrefix : regroupIndex output wanted logical =
      digits first + 2*(digits second + 2*encode rest cards digits) := by
    change digits first + cards first*(digits second + cards second*encode rest cards digits) = _
    rw [firstCard,secondCard]
  have newPrefix : regroupIndex output wanted (update output second logical replacement) =
      digits first + 2*(replacement + 2*encode rest cards digits) := by
    rw [newEncoding]
    change changed first + cards first*(changed second + cards second*encode rest cards changed) = _
    rw [tail,firstCard,secondCard]
    simp only [changed,if_neg firstDifferent,if_pos rfl]
  have firstBound : digits first < 2 := by rw [← firstCard]; exact digitBounds first members.1
  have secondBound : digits second < 2 := by rw [← secondCard]; exact digitBounds second members.2
  have low : regroupIndex output wanted logical % 2 = digits first := by omega
  have high : regroupIndex output wanted logical / 4 = encode rest cards digits := by omega
  refine ⟨updateBound,updateDigits,?_⟩
  rw [low,high,newPrefix]
  omega

#print axioms source_target_update

end Qleisli.RuntimeTargetDigit
