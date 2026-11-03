import Qleisli.RuntimeForestProduct
import Qleisli.Semantics.RawAction
import QleisliKernel.Qirf.RuntimeOwnerTransition
import QleisliKernel.Qirf.RuntimeSelectionPartition
import QleisliKernel.Qirf.RuntimeSelectionWires

/-! A concrete mathematical consumer of the original owner-transition receipt.
For an empty interval, its actual seed/resolve/reorder execution preserves every
source owner and port, including zero-width spectators. The complete sparse
code then intertwines the actual empty Raw action and logical identity on every
joint reference family. This supplies no nontrivial gate/sector/Gram theorem,
bounded availability, new checker or accepted handle.
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
  obtain ⟨left,right,leftOrigin,rightOrigin,origins⟩ := move_pair_origins _ _ _ _ _ _ moving
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

#print axioms empty_bindings
#print axioms empty_embedding
#print axioms empty_code_action
#print axioms quantumIf_spectators

end Qleisli.RuntimeOwnerTransitionAction
