import Qleisli.RuntimeForestProduct
import Qleisli.RuntimeBitSectorAction
import Qleisli.Semantics.RawAction
import QleisliKernel.Qirf.RuntimeOwnerTransition
import QleisliKernel.Qirf.RuntimeSelectionPartition
import QleisliKernel.Qirf.RuntimeSelectionWires

/-! Concrete mathematical consumers of original owner-transition receipts.
Empty intervals preserve their full codes. A singleton original quantumIf
retains every source owner and ordered wire vector across fresh output tokens,
including separate zero-width spectators. Its checked Bit-sector slice acts on
the authentic full output frame and arbitrary joint reference amplitudes.
General multi-step transport, logical target-digit recoding and Gram transfer
remain separate. No bounded availability, new checker or handle is supplied.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeOwnerTransitionAction
open QleisliKernel QleisliKernel.Finite QleisliKernel.Semantics.Exact
open QleisliKernel.Semantics
open QleisliKernel.Qirf QleisliKernel.Qirf.RuntimeForestCode
open QleisliKernel.Qirf.RuntimeOwnerMap (Binding Map)
open Qleisli.Semantics.Exact Qleisli.RuntimeForestProduct

private def seedCell (binding : Binding) : Nat × RawOwnerFlow.Tree :=
  (binding.port.token,.owner binding.owner binding.port.bits)

private theorem put_result (token : Nat) (tree : RawOwnerFlow.Tree) (before after : RawOwnerFlow.Frame)
    (ran : RawOwnerFlow.put token tree before = some after) : after = (token,tree)::before := by
  unfold RawOwnerFlow.put at ran
  split at ran
  · cases ran
  · exact (Option.some.inj ran).symm

private theorem seed_fold (bindings : Map) : ∀ initial final : RawOwnerFlow.Frame,
    bindings.foldlM (fun current binding => RawOwnerFlow.put binding.port.token
      (.owner binding.owner binding.port.bits) current) initial = some final →
    ∀ cell ∈ final,cell ∈ initial ∨ ∃ binding ∈ bindings,cell = seedCell binding := by
  induction bindings with
  | nil =>
    intro initial final ran cell member
    have same : initial = final := Option.some.inj ran
    subst final
    exact Or.inl member
  | cons first rest ih =>
    intro initial final ran cell member
    simp only [List.foldlM_cons] at ran
    obtain ⟨next,head,tail⟩ := Option.bind_eq_some_iff.mp ran
    have same := put_result first.port.token (.owner first.owner first.port.bits) initial next head
    rcases ih next final tail cell member with present | supplied
    · rw [same] at present
      rcases List.mem_cons.mp present with equal | old
      · exact Or.inr ⟨first,List.mem_cons_self,equal⟩
      · exact Or.inl old
    · obtain ⟨binding,inside,equal⟩ := supplied
      exact Or.inr ⟨binding,List.mem_cons_of_mem _ inside,equal⟩

private theorem seed_origins (bindings : Map) (initial : RawOwnerFlow.Frame)
    (ran : RawOwnerFlow.seed (bindings.map (·.owner)) (bindings.map (·.port)) = some initial) :
    ∀ cell ∈ initial,∃ binding ∈ bindings,cell = seedCell binding := by
  have folded : bindings.foldlM (fun current binding => RawOwnerFlow.put binding.port.token
      (.owner binding.owner binding.port.bits) current) [] = some initial := by
    simpa [RawOwnerFlow.seed,List.zip_map',List.foldlM_map] using ran
  intro cell member
  rcases seed_fold bindings [] initial folded cell member with impossible | supplied
  · cases impossible
  · exact supplied

private theorem resolve_result (state : QleisliKernel.Raw.Observation.State) (cell : Nat × RawOwnerFlow.Tree)
    (binding : Binding) (work left : Nat)
    (ran : (RuntimeOwnerTransition.resolve state cell).run work = (.ok binding,left)) :
    cell = (binding.port.token,.owner binding.owner binding.port.bits) ∧ binding.port ∈ state.quantum.live := by
  obtain ⟨token,tree⟩ := cell
  cases tree with
  | pair _ _ _ =>
    have impossible : (Except.error Error.request : Except Error Binding) = .ok binding := congrArg Prod.fst ran
    cases impossible
  | owner role bits =>
    cases found : state.quantum.live.find? (fun port => port.token == token) with
    | none =>
      have impossible : (Except.error Error.request : Except Error Binding) = .ok binding := by
        simpa only [RuntimeOwnerTransition.resolve,found] using congrArg Prod.fst ran
      cases impossible
    | some port =>
      have performed : ((do
          guard (port.bits == bits) .request
          pure (⟨role,port⟩ : Binding)) : Finite.WorkM Binding).run work = (.ok binding,left) := by
        simpa only [RuntimeOwnerTransition.resolve,found] using ran
      obtain ⟨_unit,middle,guardRead,returned⟩ := bind_success _ _ _ _ _ performed
      have same : binding = ⟨role,port⟩ := (pure_success _ _ _ _ returned).1
      subst binding
      have sameBits : port.bits = bits := beq_iff_eq.mp (guard_success _ _ _ _ guardRead).1
      have sameToken : port.token = token := beq_iff_eq.mp
        (List.find?_some (p := fun candidate : QleisliKernel.Semantics.Raw.Port => candidate.token == token) found)
      exact ⟨by simp only [sameToken,sameBits],List.mem_of_find?_eq_some found⟩

private theorem resolved_origins (state : QleisliKernel.Raw.Observation.State) (cells : RawOwnerFlow.Frame) :
    ∀ (moved : Map) work left,
      ((cells.mapM (RuntimeOwnerTransition.resolve state)).run work = (.ok moved,left)) →
        ∀ binding ∈ moved,∃ cell ∈ cells,
          cell = (binding.port.token,.owner binding.owner binding.port.bits) ∧ binding.port ∈ state.quantum.live := by
  induction cells with
  | nil =>
    intro moved work left ran binding member
    have same : moved = [] := (pure_success _ _ _ _ ran).1
    subst moved
    cases member
  | cons cell cells ih =>
    intro moved work left ran binding member
    simp only [List.mapM_cons] at ran
    obtain ⟨first,middle,head,rest⟩ := bind_success _ _ _ _ _ ran
    obtain ⟨tail,last,tailRead,returned⟩ := bind_success _ _ _ _ _ rest
    have same : moved = first::tail := (pure_success _ _ _ _ returned).1
    subst moved
    rcases List.mem_cons.mp member with equal | later
    · subst binding
      exact ⟨cell,List.mem_cons_self,resolve_result state cell first work middle head⟩
    · obtain ⟨entry,present,facts⟩ := ih tail middle last tailRead binding later
      exact ⟨entry,List.mem_cons_of_mem _ present,facts⟩

private theorem map_unique {α β : Type} (f : α → β) (values : List α) :
    (values.map f).Nodup → ∀ first ∈ values,∀ second ∈ values,f first = f second → first = second := by
  induction values with
  | nil => intro _unique first member; cases member
  | cons head rest ih =>
    intro unique first firstMember second secondMember equal
    have separate := List.nodup_cons.mp unique
    rcases List.mem_cons.mp firstMember with same | firstLater
    · subst first
      rcases List.mem_cons.mp secondMember with same | secondLater
      · exact same.symm
      · exact False.elim (separate.1 (List.mem_map.mpr ⟨second,secondLater,equal.symm⟩))
    · rcases List.mem_cons.mp secondMember with same | secondLater
      · subst second
        exact False.elim (separate.1 (List.mem_map.mpr ⟨first,firstLater,equal⟩))
      · exact ih separate.2 first firstLater second secondLater equal

private theorem owner_order_eq (before : Map) : ∀ after : Map,
    (before.map (fun binding => binding.owner.ordinal)).Nodup → after ⊆ before →
      after.map (·.owner) = before.map (·.owner) → after = before := by
  induction before with
  | nil =>
    intro after _unique _subset ordered
    cases after with
    | nil => rfl
    | cons first rest => simp at ordered
  | cons head rest ih =>
    intro after unique subset ordered
    cases after with
    | nil => simp at ordered
    | cons first tail =>
      have order : first.owner = head.owner ∧ tail.map (·.owner) = rest.map (·.owner) := by
        simpa only [List.map_cons,List.cons.injEq] using ordered
      have same : first = head := map_unique (fun binding : Binding => binding.owner.ordinal) _ unique
        first (subset (List.mem_cons_self)) head (List.mem_cons_self) (congrArg (·.ordinal) order.1)
      subst first
      have separate := List.nodup_cons.mp unique
      have tailSubset : tail ⊆ rest := by
        intro binding member
        rcases List.mem_cons.mp (subset (List.mem_cons_of_mem _ member)) with equal | later
        · have ownerMember : binding.owner ∈ rest.map (·.owner) := by
            rw [← order.2]
            exact List.mem_map.mpr ⟨binding,member,rfl⟩
          subst binding
          obtain ⟨other,present,sameOwner⟩ := List.mem_map.mp ownerMember
          exact False.elim (separate.1 (List.mem_map.mpr ⟨other,present,congrArg (·.ordinal) sameOwner⟩))
        · exact later
      rw [ih tail separate.2 tailSubset order.2]

private theorem checkOps_empty (dependencies : List Semantics.Finite.Dependency) (fuel : Nat)
    (before after : QleisliKernel.Raw.Observation.State) (work left : Nat)
    (ran : (QleisliKernel.Raw.Observation.checkOps dependencies fuel before []).run work = (.ok after,left)) : after = before := by
  cases fuel with
  | zero =>
    have impossible : (Except.error Error.limit : Except Error QleisliKernel.Raw.Observation.State) = .ok after :=
      congrArg Prod.fst ran
    cases impossible
  | succ fuel =>
    simp only [QleisliKernel.Raw.Observation.checkOps,List.foldlM_nil] at ran
    obtain ⟨initial,middle,initialRead,rest⟩ := bind_success _ _ _ _ _ ran
    have same : initial = before := (pure_success _ _ _ _ initialRead).1
    subst initial
    obtain ⟨_unit,_remaining,_guard,returned⟩ := bind_success _ _ _ _ _ rest
    exact (pure_success _ _ _ _ returned).1

theorem empty_state {dependencies program block start}
    (interval : @RuntimeInterval.Checked dependencies program block start 0) : interval.after = interval.before := by
  obtain ⟨work,left,ran⟩ := interval.intervalRead
  have original : (QleisliKernel.Raw.Observation.checkOps dependencies block.fuel interval.before []).run work =
      (.ok interval.after,left) := by simpa only [List.take_zero] using ran
  exact checkOps_empty _ _ _ _ work left original

/-- The actual recorded seed/resolve/reorder excludes the swapped-after
metadata example. Every original zero-width and spectator binding survives. -/
theorem empty_bindings {dependencies program block start}
    (interval : @RuntimeInterval.Checked dependencies program block start 0) {roles}
    (before : RuntimeOwnerMap.Checked roles interval.before)
    (transport : RuntimeOwnerTransition.Checked interval before.bindings) :
    transport.after.bindings = before.bindings := by
  obtain ⟨operations,initial,final,moved,parsed,seeded,flow,resolved,reordered⟩ := transport.flow
  have noOperations : operations = [] := by simpa [Sector.pureOps] using parsed.symm
  subst operations
  have noChange : initial = final := Option.some.inj flow
  subst final
  have subsetMoved := (RuntimeSelectionPartition.order_values _ _ _ reordered).1
  have liveTokens : (interval.before.quantum.live.map (·.token)).Nodup :=
    (before.complete.map (·.token)).nodup (by simpa only [List.map_map] using before.tokensDistinct)
  have subset : transport.after.bindings ⊆ before.bindings := by
    intro binding member
    obtain ⟨work,left,ran⟩ := resolved
    obtain ⟨cell,present,origin,portPresent⟩ := resolved_origins interval.after initial moved work left ran
      binding (subsetMoved member)
    obtain ⟨old,oldMember,seedOrigin⟩ := seed_origins before.bindings initial seeded cell present
    have sameCell : seedCell old = (binding.port.token,.owner binding.owner binding.port.bits) := seedOrigin.symm.trans origin
    have sameToken : old.port.token = binding.port.token := congrArg Prod.fst sameCell
    have sameTree : RawOwnerFlow.Tree.owner old.owner old.port.bits = .owner binding.owner binding.port.bits :=
      congrArg Prod.snd sameCell
    have sameOwner := (RawOwnerFlow.Tree.owner.inj sameTree).1
    have oldPort : old.port ∈ interval.before.quantum.live :=
      before.complete.mem_iff.mp (List.mem_map.mpr ⟨old,oldMember,rfl⟩)
    have newPort : binding.port ∈ interval.before.quantum.live := by
      rw [empty_state interval] at portPresent
      exact portPresent
    have samePort := map_unique (fun port : Semantics.Raw.Port => port.token) _ liveTokens
      old.port oldPort binding.port newPort sameToken
    have sameBinding : old = binding := congrArg₂ Binding.mk sameOwner samePort
    exact sameBinding ▸ oldMember
  have ordinals : (before.bindings.map (fun binding => binding.owner.ordinal)).Nodup := by
    have ordered := congrArg (List.map (fun owner : RuntimeOwnerMap.Owner => owner.ordinal)) before.ordered
    simp only [List.map_map,Function.comp_def] at ordered
    rw [ordered]
    exact before.ownersDistinct
  exact owner_order_eq before.bindings transport.after.bindings ordinals subset transport.after.ordered

theorem empty_embedding {dependencies program block start}
    (interval : @RuntimeInterval.Checked dependencies program block start 0) {roles}
    {before : RuntimeOwnerMap.Checked roles interval.before} (input : Frame before)
    (transport : RuntimeOwnerTransition.Checked interval before.bindings) (output : Frame transport.after)
    (physical logical : Nat) : input.embedding physical logical = output.embedding physical logical := by
  have bindings := empty_bindings interval before transport
  obtain ⟨left,leftRead,leftSame⟩ := input.originalCode
  obtain ⟨right,rightRead,rightSame⟩ := output.originalCode
  rw [bindings] at rightRead
  have same : left = right := Option.some.inj (leftRead.symm.trans rightRead)
  subst right
  change sparseEntry input.code (Semantics.Finite.gather physical (forestAxes interval.before.quantum.frame before.bindings)) logical =
    sparseEntry output.code (Semantics.Finite.gather physical (forestAxes interval.after.quantum.frame transport.after.bindings)) logical
  have sameFrame : interval.after.quantum.frame = interval.before.quantum.frame :=
    congrArg (fun state : QleisliKernel.Raw.Observation.State => state.quantum.frame) (empty_state interval)
  rw [bindings,sameFrame]
  unfold sparseEntry
  rw [leftSame.labels logical,rightSame.labels logical]

/-- A genuine empty Raw interval intertwines its complete actual sparse codes
and logical identity on every joint reference family, with original order. -/
theorem empty_code_action {Reference : Type} {dependencies program block start}
    (interval : @RuntimeInterval.Checked dependencies program block start 0) {roles}
    {before : RuntimeOwnerMap.Checked roles interval.before} (input : Frame before)
    (transport : RuntimeOwnerTransition.Checked interval before.bindings) (output : Frame transport.after)
    (joint : Nat → Reference → ℂ) (physical : Nat) (reference : Reference) :
    Qleisli.Semantics.RawAction.events dependencies [] (fun row => referenceAction input joint row reference) physical =
      referenceAction output joint physical reference := by
  have bindings := empty_bindings interval before transport
  obtain ⟨left,leftRead,leftSame⟩ := input.originalCode
  obtain ⟨right,rightRead,rightSame⟩ := output.originalCode
  rw [bindings] at rightRead
  have same : left = right := Option.some.inj (leftRead.symm.trans rightRead)
  subst right
  have dimensions : input.code.dimension = output.code.dimension := leftSame.dimension.trans rightSame.dimension.symm
  change referenceAction input joint physical reference = referenceAction output joint physical reference
  unfold referenceAction
  rw [dimensions]
  apply Qleisli.Exact.sum_map_congr
  intro logical _member
  rw [empty_embedding interval input transport output]

private theorem take_fold_first (token : Nat) (values : RawOwnerFlow.Frame) :
    (values.foldr (fun cell (rest,result) =>
      (cell :: rest,if cell.1 == token then some (cell.2,rest)
        else result.map fun (tree,remaining) => (tree,cell :: remaining))) ([],none)).1 = values := by
  induction values with
  | nil => rfl
  | cons first rest ih => exact congrArg (List.cons first) ih

private theorem flow_take_cons (token : Nat) (cell : Nat × RawOwnerFlow.Tree) (rest : RawOwnerFlow.Frame) :
    RawOwnerFlow.take token (cell::rest) =
      if cell.1 == token then some (cell.2,rest)
      else (RawOwnerFlow.take token rest).map fun (tree,remaining) => (tree,cell::remaining) := by
  simp only [RawOwnerFlow.take,List.foldr_cons,take_fold_first]

private theorem flow_take_origins (token : Nat) (initial : RawOwnerFlow.Frame) :
    ∀ tree remaining, RawOwnerFlow.take token initial = some (tree,remaining) →
      (token,tree) ∈ initial ∧ remaining ⊆ initial := by
  induction initial with
  | nil => intro tree remaining ran; cases ran
  | cons first rest ih =>
    intro tree remaining ran
    rw [flow_take_cons] at ran
    split at ran
    · rename_i selected
      have equal := Option.some.inj ran
      have same : (token,tree) = first :=
        Prod.ext (beq_iff_eq.mp selected).symm (congrArg Prod.fst equal).symm
      refine ⟨List.mem_cons.mpr (Or.inl same),?_⟩
      intro value member
      have restEq : rest = remaining := congrArg Prod.snd equal
      rw [← restEq] at member
      exact List.mem_cons_of_mem _ member
    · obtain ⟨⟨other,tail⟩,taken,equal⟩ := Option.map_eq_some_iff.mp ran
      have origins := ih other tail taken
      have sameTree : other = tree := congrArg Prod.fst equal
      rw [sameTree] at origins
      refine ⟨List.mem_cons_of_mem _ origins.1,?_⟩
      intro value member
      have restEq : first::tail = remaining := congrArg Prod.snd equal
      rw [← restEq] at member
      rcases List.mem_cons.mp member with same | later
      · exact List.mem_cons.mpr (Or.inl same)
      · exact List.mem_cons_of_mem _ (origins.2 later)

private theorem move_pair_origins (initial final : RawOwnerFlow.Frame)
    (a b aOut bOut : Nat)
    (ran : RawOwnerFlow.moveMany [⟨a,aOut⟩,⟨b,bOut⟩] initial = some final) :
    ∃ left right, (a,left) ∈ initial ∧ (b,right) ∈ initial ∧
      ∀ cell ∈ final, cell = (aOut,left) ∨ cell = (bOut,right) ∨ cell ∈ initial := by
  unfold RawOwnerFlow.moveMany at ran
  obtain ⟨⟨values,remaining⟩,taken,inserted⟩ := Option.bind_eq_some_iff.mp ran
  have taking : (do
      let (left,next) ← RawOwnerFlow.take a initial
      let (right,last) ← RawOwnerFlow.take b next
      pure ([(bOut,right),(aOut,left)],last)) = some (values,remaining) := by
    simpa only [List.foldlM_cons,List.foldlM_nil,bind_assoc,pure_bind] using taken
  obtain ⟨⟨left,next⟩,leftTaken,tail⟩ := Option.bind_eq_some_iff.mp taking
  obtain ⟨⟨right,last⟩,rightTaken,returned⟩ := Option.bind_eq_some_iff.mp tail
  have valuesEq := Option.some.inj returned
  have sameValues : [(bOut,right),(aOut,left)] = values := congrArg Prod.fst valuesEq
  have sameRemaining : last = remaining := congrArg Prod.snd valuesEq
  rw [← sameValues,← sameRemaining] at inserted
  have putting : (do
      let next ← RawOwnerFlow.put bOut right last
      RawOwnerFlow.put aOut left next) = some final := by
    simpa only [List.foldlM_cons,List.foldlM_nil,bind_pure] using inserted
  obtain ⟨middle,rightPut,leftPut⟩ := Option.bind_eq_some_iff.mp putting
  have rightAdded := put_result bOut right last middle rightPut
  have leftAdded := put_result aOut left middle final leftPut
  have leftOrigins := flow_take_origins a initial left next leftTaken
  have rightOrigins := flow_take_origins b next right last rightTaken
  refine ⟨left,right,leftOrigins.1,leftOrigins.2 rightOrigins.1,?_⟩
  intro cell member
  rw [leftAdded,rightAdded] at member
  rcases List.mem_cons.mp member with same | later
  · exact Or.inl same
  · rcases List.mem_cons.mp later with same | earlier
    · exact Or.inr (Or.inl same)
    · exact Or.inr (Or.inr (leftOrigins.2 (rightOrigins.2 earlier)))

/-- A literal join, unitary application and split retain the two original
trees in order and retain every remaining frame cell. The successful original
operations, including their token and split-width guards, supply this fact. -/
theorem join_apply_split_origins (initial final : RawOwnerFlow.Frame)
    (a b joined applied aOut bOut leftBits : Nat) (steps : List Semantics.Finite.Step)
    (ran : ([Semantics.Raw.Op.join a b joined,.applyUnitary joined applied steps,
      .split applied aOut bOut leftBits].foldlM RawOwnerFlow.step initial) = some final) :
    ∃ left right remaining,
      (a,left) ∈ initial ∧ (b,right) ∈ initial ∧ remaining ⊆ initial ∧
      final = (bOut,right)::(aOut,left)::remaining := by
  have performed : (do
      let next ← RawOwnerFlow.step initial (.join a b joined)
      let after ← RawOwnerFlow.step next (.applyUnitary joined applied steps)
      RawOwnerFlow.step after (.split applied aOut bOut leftBits)) = some final := by
    simpa only [List.foldlM_cons,List.foldlM_nil,bind_pure] using ran
  obtain ⟨joinedFrame,joinRead,tail⟩ := Option.bind_eq_some_iff.mp performed
  obtain ⟨appliedFrame,applyRead,splitRead⟩ := Option.bind_eq_some_iff.mp tail
  simp only [RawOwnerFlow.step] at joinRead
  obtain ⟨⟨left,afterLeft⟩,leftTaken,tail⟩ := Option.bind_eq_some_iff.mp joinRead
  obtain ⟨⟨right,remaining⟩,rightTaken,joinedPut⟩ := Option.bind_eq_some_iff.mp tail
  let pair := RawOwnerFlow.Tree.pair left right (left.width+right.width)
  have joinedEq : joinedFrame = (joined,pair)::remaining := put_result joined pair remaining joinedFrame joinedPut
  subst joinedFrame
  have takeJoined : RawOwnerFlow.take joined ((joined,pair)::remaining) = some (pair,remaining) := by
    rw [flow_take_cons]
    simp
  have appliedPut : RawOwnerFlow.put applied pair remaining = some appliedFrame := by
    simpa only [RawOwnerFlow.step,RawOwnerFlow.move,takeJoined,pure_bind] using applyRead
  have appliedEq := put_result applied pair remaining appliedFrame appliedPut
  subst appliedFrame
  have takeApplied : RawOwnerFlow.take applied ((applied,pair)::remaining) = some (pair,remaining) := by
    rw [flow_take_cons]
    simp
  have separated : (if left.width != leftBits then none else do
      let next ← RawOwnerFlow.put aOut left remaining
      RawOwnerFlow.put bOut right next) = some final := by
    simpa only [RawOwnerFlow.step,takeApplied,pure_bind,pair] using splitRead
  split at separated
  · cases separated
  · obtain ⟨afterOutLeft,leftPut,rightPut⟩ := Option.bind_eq_some_iff.mp separated
    have firstAdded := put_result aOut left remaining afterOutLeft leftPut
    have secondAdded := put_result bOut right afterOutLeft final rightPut
    have leftOrigins := flow_take_origins a initial left afterLeft leftTaken
    have rightOrigins := flow_take_origins b afterLeft right remaining rightTaken
    refine ⟨left,right,remaining,leftOrigins.1,leftOrigins.2 rightOrigins.1,?_,?_⟩
    · exact fun {_} member => leftOrigins.2 (rightOrigins.2 member)
    · rw [secondAdded,firstAdded]

private theorem pair_flow_spectators
    {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles)
    (initial final : RawOwnerFlow.Frame) (moved : Map)
    (seeded : RawOwnerFlow.seed (source.before.bindings.map (·.owner))
      (source.before.bindings.map (·.port)) = some initial)
    (resolved : RuntimeInterval.Computed
      (final.mapM (RuntimeOwnerTransition.resolve frame.interval.after)) moved)
    (reordered : RuntimeInterval.Computed
      (RuntimeOwnerMap.order (source.before.bindings.map (·.owner)) moved) source.transport.after.bindings)
    (origins : ∃ left right,
      (source.selected.first.port.token,left) ∈ initial ∧
      (source.selected.second.port.token,right) ∈ initial ∧
      ∀ cell ∈ final, cell = (source.returned.first.port.token,left) ∨
        cell = (source.returned.second.port.token,right) ∨ cell ∈ initial) :
    ∀ binding ∈ source.transport.after.bindings,
      binding.owner ≠ source.selected.first.owner → binding.owner ≠ source.selected.second.owner →
        binding ∈ source.before.bindings := by
  obtain ⟨left,right,leftOrigin,rightOrigin,origins⟩ := origins
  have selectedSubset := (RuntimeSelectionPartition.order_values _ _ _ source.selected.ordered).1
  have firstMember : source.selected.first ∈ source.before.bindings := selectedSubset (by simp)
  have secondMember : source.selected.second ∈ source.before.bindings := selectedSubset (by simp)
  have initialTree (old : Binding) (member : old ∈ source.before.bindings) (tree : RawOwnerFlow.Tree)
      (present : (old.port.token,tree) ∈ initial) : tree = .owner old.owner old.port.bits := by
    obtain ⟨binding,inside,same⟩ := seed_origins _ _ seeded _ present
    have sameToken : binding.port.token = old.port.token := (congrArg Prod.fst same).symm
    have equal := map_unique (fun value : Binding => value.port.token) _ source.before.tokensDistinct
      binding inside old member sameToken
    simpa only [equal,seedCell] using congrArg Prod.snd same
  have leftTree := initialTree _ firstMember left leftOrigin
  have rightTree := initialTree _ secondMember right rightOrigin
  have movedSubset := (RuntimeSelectionPartition.order_values _ _ _ reordered).1
  have afterTokens : (frame.interval.after.quantum.live.map (·.token)).Nodup :=
    (source.transport.after.complete.map (·.token)).nodup
      (by simpa only [List.map_map] using source.transport.after.tokensDistinct)
  intro binding member notFirst notSecond
  obtain ⟨work,leftWork,ran⟩ := resolved
  obtain ⟨cell,present,origin,newLive⟩ := resolved_origins _ _ moved work leftWork ran binding (movedSubset member)
  rcases origins cell present with first | second | unchanged
  · have trees := congrArg Prod.snd (first.symm.trans origin)
    rw [leftTree] at trees
    exact False.elim (notFirst (RawOwnerFlow.Tree.owner.inj trees).1.symm)
  · have trees := congrArg Prod.snd (second.symm.trans origin)
    rw [rightTree] at trees
    exact False.elim (notSecond (RawOwnerFlow.Tree.owner.inj trees).1.symm)
  · obtain ⟨old,oldMember,seedOrigin⟩ := seed_origins _ _ seeded cell unchanged
    have sameCell := seedOrigin.symm.trans origin
    have sameToken : old.port.token = binding.port.token := congrArg Prod.fst sameCell
    have sameOwner : old.owner = binding.owner :=
      (RawOwnerFlow.Tree.owner.inj (congrArg Prod.snd sameCell)).1
    have differentFirst : old.port.token ≠ source.selected.first.port.token := by
      intro equal
      have same := map_unique (fun value : Binding => value.port.token) _ source.before.tokensDistinct
        old oldMember _ firstMember equal
      exact notFirst (sameOwner.symm.trans (congrArg Binding.owner same))
    have differentSecond : old.port.token ≠ source.selected.second.port.token := by
      intro equal
      have same := map_unique (fun value : Binding => value.port.token) _ source.before.tokensDistinct
        old oldMember _ secondMember equal
      exact notSecond (sameOwner.symm.trans (congrArg Binding.owner same))
    have notInput : old.port.token ∉ inputs := by
      rw [source.inputTokens]
      intro present
      rcases List.mem_cons.mp present with first | later
      · exact differentFirst first
      · rcases List.mem_cons.mp later with second | impossible
        · exact differentSecond second
        · cases impossible
    have notContains : inputs.contains old.port.token = false :=
      Bool.eq_false_iff.mpr (fun h => notInput (List.contains_iff_mem.mp h))
    have oldLive := source.before.complete.mem_iff.mp (List.mem_map.mpr ⟨old,oldMember,rfl⟩)
    have oldSpectator : old.port ∈ PureInterval.spectators frame.interval.before inputs :=
      List.mem_filter.mpr ⟨oldLive,by simp only [notContains,Bool.not_false]⟩
    have oldAfter : old.port ∈ frame.interval.after.quantum.live :=
      (List.mem_filter.mp (frame.spectators ▸ oldSpectator)).1
    have samePort := map_unique (fun port : Semantics.Raw.Port => port.token) _ afterTokens
      old.port oldAfter binding.port newLive sameToken
    have equal : old = binding := congrArg₂ Binding.mk sameOwner samePort
    exact equal ▸ oldMember

/-- One original Raw quantumIf cannot reassign an untouched source owner to
another spectator port. This consumes its actual whole-frame owner-flow run,
not just the unchanged unlabelled spectator-port set. Every empty owner counts.
The singleton-operation hypothesis is explicit; arbitrary multi-step fragments
still require their owner-flow frame-extension proof. -/
theorem quantumIf_spectators {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles)
    (zero one : List Semantics.Raw.UnitaryStep)
    (original : frame.operations = [.quantumIf source.selected.first.port.token source.selected.second.port.token
      source.returned.first.port.token source.returned.second.port.token zero one]) :
    ∀ binding ∈ source.transport.after.bindings,
      binding.owner ≠ source.selected.first.owner → binding.owner ≠ source.selected.second.owner →
        binding ∈ source.before.bindings := by
  obtain ⟨operations,initial,final,moved,parsed,seeded,flow,resolved,reordered⟩ := source.transport.flow
  have operationsEq : operations = [.quantumIf source.selected.first.port.token source.selected.second.port.token
      source.returned.first.port.token source.returned.second.port.token zero one] := by
    rw [frame.literal,original] at parsed
    simpa [Sector.pureOps,Sector.pureOp] using parsed.symm
  subst operations
  have moving : RawOwnerFlow.moveMany
      [⟨source.selected.first.port.token,source.returned.first.port.token⟩,
       ⟨source.selected.second.port.token,source.returned.second.port.token⟩] initial = some final := by
    simpa only [List.foldlM_cons,List.foldlM_nil,RawOwnerFlow.step,bind_pure] using flow
  exact pair_flow_spectators frame source initial final moved seeded resolved reordered
    (move_pair_origins _ _ _ _ _ _ moving)

/-- The real three-operation register lowering preserves every untouched
source binding, including empty owners. The two selected trees are recovered
by the successful original join/move/split flow, never from equal widths. -/
theorem joinApplySplit_spectators {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles)
    (joined applied leftBits : Nat) (steps : List Semantics.Finite.Step)
    (original : frame.operations =
      [.join source.selected.first.port.token source.selected.second.port.token joined,
       .applyUnitary joined applied steps,
       .split applied source.returned.first.port.token source.returned.second.port.token leftBits]) :
    ∀ binding ∈ source.transport.after.bindings,
      binding.owner ≠ source.selected.first.owner → binding.owner ≠ source.selected.second.owner →
        binding ∈ source.before.bindings := by
  obtain ⟨operations,initial,final,moved,parsed,seeded,flow,resolved,reordered⟩ := source.transport.flow
  have operationsEq : operations =
      [.join source.selected.first.port.token source.selected.second.port.token joined,
       .applyUnitary joined applied steps,
       .split applied source.returned.first.port.token source.returned.second.port.token leftBits] := by
    rw [frame.literal,original] at parsed
    simpa [Sector.pureOps,Sector.pureOp] using parsed.symm
  subst operations
  obtain ⟨left,right,remaining,leftOrigin,rightOrigin,subset,finalEq⟩ :=
    join_apply_split_origins initial final _ _ joined applied _ _ leftBits steps flow
  have origins : ∃ left right,
      (source.selected.first.port.token,left) ∈ initial ∧
      (source.selected.second.port.token,right) ∈ initial ∧
      ∀ cell ∈ final, cell = (source.returned.first.port.token,left) ∨
        cell = (source.returned.second.port.token,right) ∨ cell ∈ initial := by
    refine ⟨left,right,leftOrigin,rightOrigin,?_⟩
    intro cell member
    rw [finalEq] at member
    rcases List.mem_cons.mp member with same | later
    · exact Or.inr (Or.inl same)
    · rcases List.mem_cons.mp later with same | untouched
      · exact Or.inl same
      · exact Or.inr (Or.inr (subset untouched))
  exact pair_flow_spectators frame source initial final moved seeded resolved reordered origins

private theorem owner_ordinals {roles state} (checked : RuntimeOwnerMap.Checked roles state) :
    (checked.bindings.map (fun binding => binding.owner.ordinal)).Nodup := by
  have ordered := congrArg (List.map (fun owner : RuntimeOwnerMap.Owner => owner.ordinal)) checked.ordered
  simp only [List.map_map,Function.comp_def] at ordered
  rw [ordered]
  exact checked.ownersDistinct

private theorem wire_map_eq (before : Map) : ∀ after : Map,
    after.map (·.owner) = before.map (·.owner) →
    (∀ old ∈ before,∀ current ∈ after,old.owner = current.owner → old.port.wires = current.port.wires) →
    after.map (fun binding => (binding.owner,binding.port.wires)) =
      before.map (fun binding => (binding.owner,binding.port.wires)) := by
  induction before with
  | nil =>
    intro after ordered _wires
    cases after with
    | nil => rfl
    | cons first rest => simp at ordered
  | cons old before ih =>
    intro after ordered wires
    cases after with
    | nil => simp at ordered
    | cons current after =>
      have equal : current.owner = old.owner ∧ after.map (·.owner) = before.map (·.owner) := by
        simpa only [List.map_cons,List.cons.injEq] using ordered
      have headWire := wires old (List.mem_cons_self) current (List.mem_cons_self) equal.1.symm
      have tail := ih after equal.2 (fun a member b present same =>
        wires a (List.mem_cons_of_mem _ member) b (List.mem_cons_of_mem _ present) same)
      simp only [List.map_cons,equal.1,headWire,tail]

private theorem selection_wires
    {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles)
    {selectorBits targetBits retained restricted}
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      source.before source.transport.after)
    (spectators : ∀ binding ∈ source.transport.after.bindings,
      binding.owner ≠ source.selected.first.owner → binding.owner ≠ source.selected.second.owner →
        binding ∈ source.before.bindings) :
    source.transport.after.bindings.map (fun binding => (binding.owner,binding.port.wires)) =
      source.before.bindings.map (fun binding => (binding.owner,binding.port.wires)) := by
  have selected := (RuntimeSelectionPartition.order_values _ _ _ source.selected.ordered).1
  have returned := (RuntimeSelectionPartition.order_values _ _ _ source.returned.ordered).1
  have boundary := (RuntimeSelectionWires.source_boundary frame source literal).1
  have pair : (source.returned.first.owner,source.returned.first.port.wires) =
        (source.selected.first.owner,source.selected.first.port.wires) ∧
      (source.returned.second.owner,source.returned.second.port.wires) =
        (source.selected.second.owner,source.selected.second.port.wires) := by
    simpa only [List.map_cons,List.map_nil,List.cons.injEq,and_true] using boundary
  apply wire_map_eq source.before.bindings source.transport.after.bindings source.transport.after.ordered
  intro old oldMember current currentMember sameOwner
  by_cases first : current.owner = source.selected.first.owner
  · have currentEq := map_unique (fun binding : Binding => binding.owner.ordinal) _
      (owner_ordinals source.transport.after) current currentMember
      source.returned.first (returned (by simp))
      (congrArg (·.ordinal) (first.trans (congrArg Prod.fst pair.1).symm))
    have oldEq := map_unique (fun binding : Binding => binding.owner.ordinal) _
      (owner_ordinals source.before) old oldMember source.selected.first (selected (by simp))
      (congrArg (·.ordinal) (sameOwner.trans first))
    rw [currentEq,oldEq]
    exact (congrArg Prod.snd pair.1).symm
  · by_cases second : current.owner = source.selected.second.owner
    · have currentEq := map_unique (fun binding : Binding => binding.owner.ordinal) _
        (owner_ordinals source.transport.after) current currentMember
        source.returned.second (returned (by simp))
        (congrArg (·.ordinal) (second.trans (congrArg Prod.fst pair.2).symm))
      have oldEq := map_unique (fun binding : Binding => binding.owner.ordinal) _
        (owner_ordinals source.before) old oldMember source.selected.second (selected (by simp))
        (congrArg (·.ordinal) (sameOwner.trans second))
      rw [currentEq,oldEq]
      exact (congrArg Prod.snd pair.2).symm
    · have present := spectators current currentMember first second
      have equal := map_unique (fun binding : Binding => binding.owner.ordinal) _
        (owner_ordinals source.before) old oldMember current present (congrArg (·.ordinal) sameOwner)
      exact congrArg (fun binding : Binding => binding.port.wires) equal

private theorem quantumIf_wires {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles)
    (zero one : List Semantics.Raw.UnitaryStep)
    (original : frame.operations = [.quantumIf source.selected.first.port.token source.selected.second.port.token
      source.returned.first.port.token source.returned.second.port.token zero one])
    {selectorBits targetBits retained restricted}
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      source.before source.transport.after) :
    source.transport.after.bindings.map (fun binding => (binding.owner,binding.port.wires)) =
      source.before.bindings.map (fun binding => (binding.owner,binding.port.wires)) := by
  exact selection_wires frame source literal (quantumIf_spectators frame source zero one original)

/-- The three original operations preserve the complete source-owner/wire
layout in its original order, including every separate zero-width spectator. -/
theorem joinApplySplit_wires
    {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles)
    (joined applied leftBits : Nat) (steps : List Semantics.Finite.Step)
    (original : frame.operations =
      [.join source.selected.first.port.token source.selected.second.port.token joined,
       .applyUnitary joined applied steps,
       .split applied source.returned.first.port.token source.returned.second.port.token leftBits])
    {selectorBits targetBits retained restricted}
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      source.before source.transport.after) :
    source.transport.after.bindings.map (fun binding => (binding.owner,binding.port.wires)) =
      source.before.bindings.map (fun binding => (binding.owner,binding.port.wires)) := by
  exact selection_wires frame source literal
    (joinApplySplit_spectators frame source joined applied leftBits steps original)

private theorem take_frame {before after : Semantics.RawTrace.Interface} {token port}
    (ran : Semantics.RawTrace.take before token = some (port,after)) : after.frame = before.frame := by
  unfold Semantics.RawTrace.take at ran
  obtain ⟨found,_lookup,returned⟩ := Option.bind_eq_some_iff.mp ran
  have equal := Option.some.inj returned
  exact (congrArg (fun pair : Semantics.Raw.Port × Semantics.RawTrace.Interface => pair.2.frame) equal).symm

private theorem quantumIf_step_frame {before after : Semantics.RawTrace.Interface}
    {control target controlOut targetOut zero one events}
    (ran : Semantics.RawTrace.step before (.quantumIf control target controlOut targetOut zero one) =
      some (after,events)) : after.frame = before.frame := by
  simp only [Semantics.RawTrace.step] at ran
  obtain ⟨⟨c,next⟩,controlRead,tail⟩ := Option.bind_eq_some_iff.mp ran
  obtain ⟨⟨t,last⟩,targetRead,returned⟩ := Option.bind_eq_some_iff.mp tail
  have equal := Option.some.inj returned
  have same : last.frame = after.frame :=
    congrArg (fun pair : Semantics.RawTrace.Interface × List Semantics.Raw.Event => pair.1.frame) equal
  exact same.symm.trans ((take_frame targetRead).trans (take_frame controlRead))

private theorem quantumIf_frame {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles)
    (zero one : List Semantics.Raw.UnitaryStep)
    (original : frame.operations = [.quantumIf source.selected.first.port.token source.selected.second.port.token
      source.returned.first.port.token source.returned.second.port.token zero one])
    {selectorBits targetBits retained restricted}
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      source.before source.transport.after) :
    frame.interval.after.quantum.frame = frame.interval.before.quantum.frame := by
  have ran : Semantics.RawTrace.advance
      ⟨frame.interval.before.quantum.reference,[],frame.interval.before.quantum.frame.length⟩
      (.quantumIf source.selected.first.port.token source.selected.second.port.token
        source.returned.first.port.token source.returned.second.port.token zero one) = some literal.traceResult := by
    simpa only [RuntimeLocalEvents.trace,original,List.foldlM_cons,List.foldlM_nil,bind_pure] using literal.executed
  unfold Semantics.RawTrace.advance at ran
  obtain ⟨⟨after,events⟩,stepped,returned⟩ := Option.bind_eq_some_iff.mp ran
  have equal := Option.some.inj returned
  have same : after.frame = literal.traceResult.state.frame :=
    congrArg (fun prepared : Semantics.RawTrace.Prepared => prepared.state.frame) equal
  have actual := congrArg (fun state : Semantics.RawTrace.Interface => state.frame) literal.afterState
  exact actual.symm.trans (same.symm.trans (quantumIf_step_frame stepped))

private theorem join_step_frame {before after : Semantics.RawTrace.Interface}
    {left right output events}
    (ran : Semantics.RawTrace.step before (.join left right output) = some (after,events)) :
    after.frame = before.frame := by
  simp only [Semantics.RawTrace.step] at ran
  obtain ⟨⟨l,next⟩,leftRead,tail⟩ := Option.bind_eq_some_iff.mp ran
  obtain ⟨⟨r,last⟩,rightRead,returned⟩ := Option.bind_eq_some_iff.mp tail
  have equal := Option.some.inj returned
  have same : last.frame = after.frame :=
    congrArg (fun pair : Semantics.RawTrace.Interface × List Semantics.Raw.Event => pair.1.frame) equal
  exact same.symm.trans ((take_frame rightRead).trans (take_frame leftRead))

private theorem apply_step_frame {before after : Semantics.RawTrace.Interface}
    {input output steps events}
    (ran : Semantics.RawTrace.step before (.applyUnitary input output steps) = some (after,events)) :
    after.frame = before.frame := by
  simp only [Semantics.RawTrace.step] at ran
  obtain ⟨⟨port,next⟩,taken,returned⟩ := Option.bind_eq_some_iff.mp ran
  have equal := Option.some.inj returned
  have same : next.frame = after.frame :=
    congrArg (fun pair : Semantics.RawTrace.Interface × List Semantics.Raw.Event => pair.1.frame) equal
  exact same.symm.trans (take_frame taken)

private theorem split_step_frame {before after : Semantics.RawTrace.Interface}
    {input left right leftBits events}
    (ran : Semantics.RawTrace.step before (.split input left right leftBits) = some (after,events)) :
    after.frame = before.frame := by
  simp only [Semantics.RawTrace.step] at ran
  obtain ⟨⟨port,next⟩,taken,returned⟩ := Option.bind_eq_some_iff.mp ran
  have equal := Option.some.inj returned
  have same : next.frame = after.frame :=
    congrArg (fun pair : Semantics.RawTrace.Interface × List Semantics.Raw.Event => pair.1.frame) equal
  exact same.symm.trans (take_frame taken)

private theorem advance_frame {before after : Semantics.RawTrace.Prepared} {operation}
    (ran : Semantics.RawTrace.advance before operation = some after)
    (preserved : ∀ state events, Semantics.RawTrace.step before.state operation = some (state,events) →
      state.frame = before.state.frame) : after.state.frame = before.state.frame := by
  unfold Semantics.RawTrace.advance at ran
  obtain ⟨⟨state,events⟩,stepped,returned⟩ := Option.bind_eq_some_iff.mp ran
  have equal := Option.some.inj returned
  have same : state.frame = after.state.frame :=
    congrArg (fun prepared : Semantics.RawTrace.Prepared => prepared.state.frame) equal
  exact same.symm.trans (preserved state events stepped)

/-- These actual original operations preserve the Raw frame order. Their
circuits may have nontrivial phase/action; no identity of operators follows. -/
theorem joinApplySplit_frame {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles)
    (joined applied leftBits : Nat) (steps : List Semantics.Finite.Step)
    (original : frame.operations =
      [.join source.selected.first.port.token source.selected.second.port.token joined,
       .applyUnitary joined applied steps,
       .split applied source.returned.first.port.token source.returned.second.port.token leftBits])
    {selectorBits targetBits retained restricted}
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      source.before source.transport.after) :
    frame.interval.after.quantum.frame = frame.interval.before.quantum.frame := by
  let initial : Semantics.RawTrace.Prepared :=
    ⟨frame.interval.before.quantum.reference,[],frame.interval.before.quantum.frame.length⟩
  have traced : (do
      let next ← Semantics.RawTrace.advance initial
        (.join source.selected.first.port.token source.selected.second.port.token joined)
      let after ← Semantics.RawTrace.advance next (.applyUnitary joined applied steps)
      Semantics.RawTrace.advance after
        (.split applied source.returned.first.port.token source.returned.second.port.token leftBits)) =
      some literal.traceResult := by
    simpa only [RuntimeLocalEvents.trace,original,List.foldlM_cons,List.foldlM_nil,bind_pure] using literal.executed
  obtain ⟨joinedState,joinedRead,tail⟩ := Option.bind_eq_some_iff.mp traced
  obtain ⟨appliedState,appliedRead,splitRead⟩ := Option.bind_eq_some_iff.mp tail
  have first := advance_frame joinedRead (fun _ _ ran => join_step_frame ran)
  have second := advance_frame appliedRead (fun _ _ ran => apply_step_frame ran)
  have third := advance_frame splitRead (fun _ _ ran => split_step_frame ran)
  have actual := congrArg (fun state : Semantics.RawTrace.Interface => state.frame) literal.afterState
  exact actual.symm.trans (third.trans (second.trans first))

private theorem forest_by_bases (owners : List Semantics.CarrierInterface.Owner) :
    Semantics.CarrierInterface.forest owners =
      match owners.map (·.basis) with
      | [] => [.unit]
      | [basis] => basis
      | [first,second] => .pair :: first ++ second
      | bases => .tuple bases.length :: bases.flatMap id := by
  cases owners with
  | nil => rfl
  | cons first rest => cases rest with
    | nil => rfl
    | cons second rest => cases rest with
      | nil => rfl
      | cons third rest =>
        simp only [Semantics.CarrierInterface.forest,List.map_cons,List.length_cons,List.flatMap_cons]
        rw [List.length_map,List.flatMap_map]
        rfl

private theorem selection_codes {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles)
    {selectorBits targetBits retained restricted}
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      source.before source.transport.after)
    (wiresMap : source.transport.after.bindings.map (fun binding => (binding.owner,binding.port.wires)) =
      source.before.bindings.map (fun binding => (binding.owner,binding.port.wires)))
    (actualFrame : frame.interval.after.quantum.frame = frame.interval.before.quantum.frame) :
    literal.inputCode.code.dimension = literal.outputCode.code.dimension ∧
      ∀ physical logical,literal.inputCode.embedding physical logical = literal.outputCode.embedding physical logical := by
  have owners := source.transport.after.ordered
  have bases := congrArg (List.map (fun owner : RuntimeOwnerMap.Owner => owner.basis)) owners
  have sameForest : forestBasis source.transport.after.bindings = forestBasis source.before.bindings := by
    unfold forestBasis
    rw [forest_by_bases,forest_by_bases]
    have same : (carrierOwners source.transport.after.bindings).map (·.basis) =
        (carrierOwners source.before.bindings).map (·.basis) := by
      simpa only [carrierOwners,List.map_map,Function.comp_def] using bases
    rw [same]
  have wires := congrArg (List.flatMap (fun pair : RuntimeOwnerMap.Owner × List Nat => pair.2))
    wiresMap
  simp only [List.flatMap_map] at wires
  obtain ⟨left,leftRead,leftSame⟩ := literal.inputCode.originalCode
  obtain ⟨right,rightRead,rightSame⟩ := literal.outputCode.originalCode
  rw [sameForest] at rightRead
  have same : left = right := Option.some.inj (leftRead.symm.trans rightRead)
  subst right
  refine ⟨leftSame.dimension.trans rightSame.dimension.symm,?_⟩
  intro physical logical
  change sparseEntry literal.inputCode.code
      (Semantics.Finite.gather physical (forestAxes frame.interval.before.quantum.frame source.before.bindings)) logical =
    sparseEntry literal.outputCode.code
      (Semantics.Finite.gather physical (forestAxes frame.interval.after.quantum.frame source.transport.after.bindings)) logical
  unfold forestAxes
  rw [actualFrame,wires]
  unfold sparseEntry
  rw [leftSame.labels logical,rightSame.labels logical]

/-- The same nonempty original quantumIf preserves the complete sparse code
coordinates across fresh output tokens. Every owner remains in original order,
and zero-width owners retain their separate positions. This is code equality,
not an assertion that the nonempty quantum action is logical identity. -/
theorem quantumIf_codes {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles)
    (zero one : List Semantics.Raw.UnitaryStep)
    (original : frame.operations = [.quantumIf source.selected.first.port.token source.selected.second.port.token
      source.returned.first.port.token source.returned.second.port.token zero one])
    {selectorBits targetBits retained restricted}
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      source.before source.transport.after) :
    literal.inputCode.code.dimension = literal.outputCode.code.dimension ∧
      ∀ physical logical,literal.inputCode.embedding physical logical = literal.outputCode.embedding physical logical := by
  exact selection_codes frame source literal
    (quantumIf_wires frame source zero one original literal)
    (quantumIf_frame frame source zero one original literal)

/-- The literal three-operation lowering preserves the complete original
sparse code across fresh output tokens. This is equality of retained encodings,
not an identity, availability or Gram assertion for the unitary application. -/
theorem joinApplySplit_codes {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles)
    (joined applied leftBits : Nat) (steps : List Semantics.Finite.Step)
    (original : frame.operations =
      [.join source.selected.first.port.token source.selected.second.port.token joined,
       .applyUnitary joined applied steps,
       .split applied source.returned.first.port.token source.returned.second.port.token leftBits])
    {selectorBits targetBits retained restricted}
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      source.before source.transport.after) :
    literal.inputCode.code.dimension = literal.outputCode.code.dimension ∧
      ∀ physical logical,literal.inputCode.embedding physical logical = literal.outputCode.embedding physical logical := by
  exact selection_codes frame source literal
    (joinApplySplit_wires frame source joined applied leftBits steps original literal)
    (joinApplySplit_frame frame source joined applied leftBits steps original literal)

/-- The same actual trace and source port lookups identify the local selected
axes with the returned original-owner axes in the complete output frame. -/
theorem joinApplySplit_axes {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles)
    (joined applied leftBits : Nat) (steps : List Semantics.Finite.Step)
    (original : frame.operations =
      [.join source.selected.first.port.token source.selected.second.port.token joined,
       .applyUnitary joined applied steps,
       .split applied source.returned.first.port.token source.returned.second.port.token leftBits])
    {selectorBits targetBits retained restricted}
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      source.before source.transport.after) :
    forestAxes frame.interval.before.quantum.frame literal.selection.selected =
      forestAxes frame.interval.after.quantum.frame source.returned.toList := by
  have selectedPorts := literal.selectedPorts.trans (RuntimeSelectionPartition.source_ports frame source).1
  have selectedWires := congrArg (List.flatMap (fun port : Semantics.Raw.Port => port.wires)) selectedPorts
  have returnedWires := congrArg (List.flatMap (fun pair : RuntimeOwnerMap.Owner × List Nat => pair.2))
    (RuntimeSelectionWires.source_boundary frame source literal).1
  simp only [List.flatMap_map] at selectedWires returnedWires
  unfold forestAxes
  rw [joinApplySplit_frame frame source joined applied leftBits steps original literal,returnedWires,selectedWires]
  rfl

/-- Shapes of the actual checked selection interval with the original source
tokens. In both shapes the native sector reader reconstructs the arm action. -/
inductive SelectionForm {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles) : Prop where
  | quantumIf (zero one : List Semantics.Raw.UnitaryStep)
      (original : frame.operations = [.quantumIf source.selected.first.port.token source.selected.second.port.token
        source.returned.first.port.token source.returned.second.port.token zero one])
  | joined (joined applied leftBits : Nat) (steps : List Semantics.Finite.Step)
      (original : frame.operations = [.join source.selected.first.port.token source.selected.second.port.token joined,
        .applyUnitary joined applied steps,
        .split applied source.returned.first.port.token source.returned.second.port.token leftBits])

/-! Both original Raw shapes transport the complete input code to the returned axes. -/
/-- Both authentic original Raw forms retain the same complete code. -/
theorem selection_form_codes
    {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles)
    {selectorBits targetBits retained restricted}
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      source.before source.transport.after) (form : SelectionForm frame source) :
    literal.inputCode.code.dimension = literal.outputCode.code.dimension ∧
      ∀ p i,literal.inputCode.embedding p i = literal.outputCode.embedding p i := by
  cases form with
  | quantumIf zero one original => exact quantumIf_codes frame source zero one original literal
  | joined j a n steps original => exact joinApplySplit_codes frame source j a n steps original literal

/-- Both authentic original forms identify selected and returned axis order. -/
theorem selection_form_axes
    {dependencies program block start count inputs outputs roles}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs roles)
    (source : RuntimeOwnerTransition.Selection frame.interval inputs outputs roles)
    {selectorBits targetBits retained restricted}
    (literal : RuntimeLocalEvents.Literal frame selectorBits targetBits retained restricted
      source.before source.transport.after) (form : SelectionForm frame source) :
    forestAxes frame.interval.before.quantum.frame literal.selection.selected =
      forestAxes frame.interval.after.quantum.frame source.returned.toList := by
  cases form with
  | joined j a n steps original => exact joinApplySplit_axes frame source j a n steps original literal
  | quantumIf zero one original =>
    have selectedPorts := literal.selectedPorts.trans (RuntimeSelectionPartition.source_ports frame source).1
    have selectedWires := congrArg (List.flatMap (fun port : Semantics.Raw.Port => port.wires)) selectedPorts
    have returnedWires := congrArg (List.flatMap (fun pair : RuntimeOwnerMap.Owner × List Nat => pair.2))
      (RuntimeSelectionWires.source_boundary frame source literal).1
    simp only [List.flatMap_map] at selectedWires returnedWires
    unfold forestAxes
    rw [quantumIf_frame frame source zero one original literal,returnedWires,selectedWires]
    rfl

theorem bit_target_selection_output {Reference : Type}
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {selectorBits : Nat} {retained : Raw.Sector.Retained}
    {restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits selectorBits] [.bits 1]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained}
    {inputCode outputCode : Matrix}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (targetBasis : target.basis = [.bit])
    (literal : RuntimeLocalEvents.Literal frame selectorBits 1 retained restricted codes.owners.before codes.owners.transport.after)
    (form : SelectionForm frame codes.owners)
    {label required logical}
    (binding : QleisliKernel.Qirf.NominalSector.LogicalBinding inputCode outputCode retained.sectors (label,required) logical)
    (joint : Nat → Reference → ℂ) (physical row : Nat) (reference : Reference)
    (coordinate : Semantics.Finite.gather physical
        (forestAxes frame.interval.after.quantum.frame codes.owners.returned.toList) =
      QleisliKernel.FiniteRestriction.pack selectorBits label row)
    (rowBound : row < 2) :
    Qleisli.Semantics.RawAction.events dependencies literal.traceResult.events
        (fun input => referenceAction literal.inputCode joint input reference) physical =
      action required (fun input ref => referenceAction literal.outputCode joint
        (Semantics.Finite.scatter physical (forestAxes frame.interval.after.quantum.frame codes.owners.returned.toList)
          (QleisliKernel.FiniteRestriction.pack selectorBits label input)) ref) row reference := by
  have code := selection_form_codes frame codes.owners literal form
  have referenceCode : ∀ physical reference,
      referenceAction literal.inputCode joint physical reference =
        referenceAction literal.outputCode joint physical reference := by
    intro physical reference
    unfold referenceAction
    rw [code.1]
    apply Qleisli.Exact.sum_map_congr
    intro logical _member
    rw [code.2 physical logical]
  have axes := selection_form_axes frame codes.owners literal form
  have inputCoordinate : Semantics.Finite.gather physical
      (forestAxes frame.interval.before.quantum.frame literal.selection.selected) =
        QleisliKernel.FiniteRestriction.pack selectorBits label row := by rw [axes]; exact coordinate
  have sector := Qleisli.RuntimeBitSectorAction.bit_target_sector_references frame codes targetBasis literal binding
    joint physical row reference inputCoordinate rowBound
  rw [axes] at sector
  calc
    _ = _ := sector
    _ = _ := by
      apply congrArg (fun values : Nat → Reference → ℂ => action required values row reference)
      funext input ref
      exact referenceCode _ _

theorem bit_target_quantumIf_output {Reference : Type}
    {dependencies program block start count inputs outputs selector target}
    (frame : @RuntimePureInterval.Checked dependencies program block 2 start count inputs outputs [selector,target])
    {retained : Raw.Sector.Retained}
    {restricted : RuntimeInterval.Computed (Raw.Sector.read dependencies [.bits 1] [.bits 1]
      (RuntimePureInterval.fragment frame.selected frame.operations outputs)) retained}
    {inputCode outputCode : Matrix}
    (codes : RuntimePureBody.SelectionCodes frame.interval inputs outputs selector target inputCode outputCode)
    (targetBasis : target.basis = [.bit])
    (literal : RuntimeLocalEvents.Literal frame 1 1 retained restricted codes.owners.before codes.owners.transport.after)
    (zero one : List Semantics.Raw.UnitaryStep)
    (original : frame.operations = [.quantumIf codes.owners.selected.first.port.token codes.owners.selected.second.port.token
      codes.owners.returned.first.port.token codes.owners.returned.second.port.token zero one])
    {label required logical}
    (binding : QleisliKernel.Qirf.NominalSector.LogicalBinding inputCode outputCode retained.sectors (label,required) logical)
    (joint : Nat → Reference → ℂ) (physical row : Nat) (reference : Reference)
    (coordinate : Semantics.Finite.gather physical
        (forestAxes frame.interval.after.quantum.frame codes.owners.returned.toList) =
      QleisliKernel.FiniteRestriction.pack 1 label row)
    (rowBound : row < 2) :
    Qleisli.Semantics.RawAction.events dependencies literal.traceResult.events
        (fun input => referenceAction literal.inputCode joint input reference) physical =
      action required (fun input ref => referenceAction literal.outputCode joint
        (Semantics.Finite.scatter physical (forestAxes frame.interval.after.quantum.frame codes.owners.returned.toList)
          (QleisliKernel.FiniteRestriction.pack 1 label input)) ref) row reference := by
  exact bit_target_selection_output frame codes targetBasis literal (.quantumIf zero one original)
    binding joint physical row reference coordinate rowBound

#print axioms empty_bindings
#print axioms empty_embedding
#print axioms empty_code_action
#print axioms join_apply_split_origins
#print axioms joinApplySplit_spectators
#print axioms joinApplySplit_wires
#print axioms joinApplySplit_frame
#print axioms joinApplySplit_codes
#print axioms joinApplySplit_axes
#print axioms quantumIf_spectators
#print axioms quantumIf_codes
#print axioms bit_target_quantumIf_output

end Qleisli.RuntimeOwnerTransitionAction
