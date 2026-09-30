import Qleisli.CoordinateOperators
import Qleisli.HierarchicalWiring
import Qleisli.HierarchicalFourier
import Qleisli.HierarchicalTensorCoordinates
import QleisliKernel.Hierarchical.CircuitTrace

/-! Exact phase-sensitive interpretation of constructed circuit traces.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
The atom environment must be bound to evaluations of the requested actual
indices. It is not a submitted whole-circuit interpretation or QPE certificate.
-/
namespace Qleisli.HierarchicalCircuitTrace
open QleisliKernel.Hierarchical
open Artifact HierarchicalOperators HierarchicalSemantics HierarchicalFiniteEvaluation
open scoped BigOperators Matrix

noncomputable def eventMatrix (atoms : Nat → Operator) (n : Nat) (event : CircuitTrace.Event) : Matrix (Fin n → Bool) (Fin n → Bool) ℂ := by
  classical
  exact fun output input =>
    if ∀ i : Fin n, i.val ∉ event.positions → output i = input i then
      (atoms event.atom).coefficient
        (HierarchicalWiring.select event.positions (List.ofFn output))
        (HierarchicalWiring.select event.positions (List.ofFn input)) else 0

noncomputable def routeMatrix (n : Nat) (route : List Nat) : Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  fun output input => if List.ofFn output = HierarchicalWiring.select route (List.ofFn input) then 1 else 0

noncomputable def eventsMatrix (atoms : Nat → Operator) (n : Nat) (events : List CircuitTrace.Event) : Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  events.foldl (fun before event => eventMatrix atoms n event * before) 1

noncomputable def meaning (atoms : Nat → Operator) (trace : CircuitTrace.Trace) : Matrix (Fin trace.width → Bool) (Fin trace.width → Bool) ℂ :=
  routeMatrix trace.width trace.route * eventsMatrix atoms trace.width trace.events.toList

def positions (n : Nat) (axes : List Nat) (inside : ∀ i ∈ axes, i < n) : Fin axes.length → Fin n :=
  fun i => ⟨axes[i],inside _ (List.getElem_mem i.isLt)⟩

theorem selected_ofFn (n : Nat) (axes : List Nat) (inside : ∀ i ∈ axes, i < n)
    (bits : Fin n → Bool) :
    HierarchicalWiring.select axes (List.ofFn bits) = List.ofFn (bits ∘ positions n axes inside) := by
  apply List.ext_getElem
  · simp [HierarchicalWiring.select]
  · intro i left right
    have bound : i < axes.length := by simpa [HierarchicalWiring.select] using left
    simp [HierarchicalWiring.select,positions,inside _ (List.getElem_mem bound)]

theorem positions_injective (n : Nat) (axes : List Nat) (inside : ∀ i ∈ axes, i < n)
    (distinct : axes.Nodup) : Function.Injective (positions n axes inside) := by
  intro i j equal
  apply Fin.ext
  exact distinct.getElem_inj_iff.mp (congrArg Fin.val equal)

theorem outside_positions (n : Nat) (axes : List Nat) (inside : ∀ i ∈ axes, i < n)
    (output input : Fin n → Bool) :
    CoordinateOperators.outside (positions n axes inside) output input ↔
      ∀ i : Fin n, i.val ∉ axes → output i = input i := by
  constructor
  · intro same i absent
    apply same i
    intro selected equal
    apply absent
    have equal := congrArg Fin.val equal
    change axes[selected.val] = i.val at equal
    rw [← equal]
    exact List.getElem_mem selected.isLt
  · intro same i absent
    apply same i
    intro member
    obtain ⟨j,bound,equal⟩ := List.mem_iff_getElem.mp member
    exact absent ⟨j,bound⟩ (Fin.ext equal)

theorem event_eq_lift (atoms : Nat → Operator) (n : Nat) (event : CircuitTrace.Event)
    (inside : ∀ i ∈ event.positions, i < n) :
    eventMatrix atoms n event = CoordinateOperators.lift (positions n event.positions inside)
      (matrixAt event.positions.length event.positions.length (atoms event.atom)) := by
  ext output input
  simp only [eventMatrix,CoordinateOperators.lift,outside_positions,matrixAt]
  rw [selected_ofFn n event.positions inside output, selected_ofFn n event.positions inside input]

noncomputable def permutation (n : Nat) (axes : List Nat) (permuted : axes.Perm (List.range n)) :
    Equiv.Perm (Fin n) := by
  have size : axes.length = n := by simpa using permuted.length_eq
  have inside : ∀ i ∈ axes, i < n := by intro i member; simpa using permuted.mem_iff.mp member
  let pick : Fin n → Fin n := fun i => ⟨axes[i.val]'(by omega),inside _ (List.getElem_mem (by omega))⟩
  exact Equiv.ofBijective pick ⟨by
    intro i j equal
    apply Fin.ext
    exact (permuted.nodup_iff.mpr List.nodup_range).getElem_inj_iff.mp (congrArg Fin.val equal),by
    intro i
    have member : i.val ∈ axes := permuted.mem_iff.mpr (by simp)
    obtain ⟨j,bound,equal⟩ := List.mem_iff_getElem.mp member
    exact ⟨⟨j,by omega⟩,Fin.ext equal⟩⟩

theorem permutation_val (n : Nat) (axes : List Nat) (permuted : axes.Perm (List.range n)) (i : Fin n) :
    (permutation n axes permuted i).val = QleisliKernel.Layout.indexAt axes i.val := by
  have size : axes.length = n := by simpa using permuted.length_eq
  simp [permutation,QleisliKernel.Layout.indexAt,List.getElem?_eq_getElem (by omega : i.val < axes.length)]

theorem selected_permutation (n : Nat) (axes : List Nat) (permuted : axes.Perm (List.range n))
    (bits : Fin n → Bool) :
    HierarchicalWiring.select axes (List.ofFn bits) =
      List.ofFn (CoordinateOperators.basisEquiv (permutation n axes permuted) bits) := by
  have size : axes.length = n := by simpa using permuted.length_eq
  apply List.ext_getElem
  · simp [HierarchicalWiring.select,size]
  · intro i left right
    have bound : i < n := by simpa [HierarchicalWiring.select,size] using left
    have selected : axes[i]'(by omega) < n := by
      have member := List.getElem_mem (by omega : i < axes.length)
      simpa using permuted.mem_iff.mp member
    simp [HierarchicalWiring.select,CoordinateOperators.basisEquiv,Function.comp_def,
      permutation,selected]

theorem route_eq (n : Nat) (axes : List Nat) (permuted : axes.Perm (List.range n)) :
    routeMatrix n axes = CoordinateOperators.routeMatrix (permutation n axes permuted) := by
  ext output input
  simp only [routeMatrix,CoordinateOperators.routeMatrix,
    selected_permutation n axes permuted,List.ofFn_inj]

theorem route_identity (n : Nat) : routeMatrix n (List.range n) = 1 := by
  ext output input
  have selected : HierarchicalWiring.select (List.range n) (List.ofFn input) = List.ofFn input := by
    simpa [HierarchicalWiring.select] using range_select (List.ofFn input)
  simp [routeMatrix,selected,List.ofFn_inj,Matrix.one_apply]

theorem event_atomic (atoms : Nat → Operator) (n index : Nat) :
    eventMatrix atoms n ⟨index,List.range n⟩ = matrixAt n n (atoms index) := by
  ext output input
  have selected (bits : Fin n → Bool) :
      HierarchicalWiring.select (List.range n) (List.ofFn bits) = List.ofFn bits := by
    simpa [HierarchicalWiring.select] using range_select (List.ofFn bits)
  simp [eventMatrix,selected,matrixAt]

theorem meaning_atomic (atoms : Nat → Operator) (n index : Nat) :
    meaning atoms (CircuitTrace.atomic index n) = matrixAt n n (atoms index) := by
  dsimp only [meaning,CircuitTrace.atomic,eventsMatrix]
  simp only [List.foldl_cons,List.foldl_nil,route_identity,event_atomic]
  simp only [Matrix.mul_one,Matrix.one_mul]

theorem meaning_identity (atoms : Nat → Operator) (n : Nat) :
    meaning atoms (CircuitTrace.identity n) = 1 := by
  dsimp only [meaning,CircuitTrace.identity,eventsMatrix]
  rw [route_identity]
  change (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) * 1 = 1
  exact Matrix.mul_one _

theorem positions_list (n : Nat) (axes : List Nat) (inside : ∀ i ∈ axes, i < n) :
    List.ofFn (fun i => (positions n axes inside i).val) = axes := by
  apply List.ext_getElem
  · simp
  · intro i left right
    simp [positions]

theorem event_ofFn (atoms : Nat → Operator) {n k : Nat} (index : Nat) (pos : Fin k → Fin n) :
    eventMatrix atoms n ⟨index,List.ofFn (fun i => (pos i).val)⟩ =
      CoordinateOperators.lift pos (matrixAt k k (atoms index)) := by
  ext output input
  have selected (bits : Fin n → Bool) :
      HierarchicalWiring.select (List.ofFn (fun i => (pos i).val)) (List.ofFn bits) =
        List.ofFn (bits ∘ pos) := by
    apply List.ext_getElem
    · simp [HierarchicalWiring.select]
    · intro i left right
      simp [HierarchicalWiring.select]
  have outside : (∀ i : Fin n, i.val ∉ List.ofFn (fun i => (pos i).val) → output i = input i) ↔
      CoordinateOperators.outside pos output input := by
    simp only [CoordinateOperators.outside,List.mem_ofFn,not_exists]
    constructor
    · intro same i absent
      exact same i (fun j equal => absent j (Fin.ext equal))
    · intro same i absent
      exact same i (fun j equal => absent j (congrArg Fin.val equal))
  simp only [eventMatrix,CoordinateOperators.lift,selected,matrixAt]
  split_ifs with first second second
  · rfl
  · exact False.elim (second (outside.mp first))
  · exact False.elim (first (outside.mpr second))
  · rfl

theorem event_transport (atoms : Nat → Operator) (n : Nat) (route : List Nat)
    (permuted : route.Perm (List.range n)) (event : CircuitTrace.Event)
    (inside : ∀ i ∈ event.positions, i < n) :
    eventMatrix atoms n event * routeMatrix n route =
      routeMatrix n route * eventMatrix atoms n (CircuitTrace.transport route event) := by
  let pos := positions n event.positions inside
  let perm := permutation n route permuted
  have old : event = ⟨event.atom,List.ofFn (fun i => (pos i).val)⟩ := by
    rw [positions_list]
  have moved : CircuitTrace.transport route event =
      ⟨event.atom,List.ofFn (fun i => (perm (pos i)).val)⟩ := by
    apply congrArg (CircuitTrace.Event.mk event.atom)
    change event.positions.map _ = _
    conv_lhs => rw [← positions_list n event.positions inside]
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    exact (permutation_val n route permuted (pos i)).symm
  rw [moved]
  conv_lhs => rw [old]
  rw [event_ofFn,event_ofFn,route_eq n route permuted]
  exact CoordinateOperators.local_route pos _ perm

theorem permutation_list (n : Nat) (axes : List Nat) (permuted : axes.Perm (List.range n)) :
    List.ofFn (fun i => (permutation n axes permuted i).val) = axes := by
  have size : axes.length = n := by simpa using permuted.length_eq
  apply List.ext_getElem
  · simp [size]
  · intro i left right
    simp [permutation]

theorem route_ofFn (n : Nat) (perm : Equiv.Perm (Fin n)) :
    routeMatrix n (List.ofFn (fun i => (perm i).val)) = CoordinateOperators.routeMatrix perm := by
  ext output input
  have selected : HierarchicalWiring.select (List.ofFn (fun i => (perm i).val)) (List.ofFn input) =
      List.ofFn (CoordinateOperators.basisEquiv perm input) := by
    apply List.ext_getElem
    · simp [HierarchicalWiring.select]
    · intro i left right
      simp [HierarchicalWiring.select,CoordinateOperators.basisEquiv,Function.comp_def]
  simp only [routeMatrix,CoordinateOperators.routeMatrix,selected,List.ofFn_inj]

theorem route_compose (n : Nat) (first second : List Nat)
    (firstPerm : first.Perm (List.range n)) (secondPerm : second.Perm (List.range n)) :
    routeMatrix n (second.map (QleisliKernel.Layout.indexAt first)) =
      routeMatrix n second * routeMatrix n first := by
  let a := permutation n first firstPerm
  let b := permutation n second secondPerm
  have combined : second.map (QleisliKernel.Layout.indexAt first) =
      List.ofFn (fun i => ((b.trans a) i).val) := by
    conv_lhs => rw [← permutation_list n second secondPerm]
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    exact (permutation_val n first firstPerm (b i)).symm
  rw [combined,route_ofFn,route_eq n first firstPerm,route_eq n second secondPerm]
  exact (CoordinateOperators.route_comp b a).symm

theorem events_initial (atoms : Nat → Operator) (n : Nat) (events : List CircuitTrace.Event)
    (initial : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) :
    events.foldl (fun before event => eventMatrix atoms n event * before) initial =
      eventsMatrix atoms n events * initial := by
  induction events generalizing initial with
  | nil => simp [eventsMatrix]
  | cons event rest ih =>
    change rest.foldl (fun before event => eventMatrix atoms n event * before)
      (eventMatrix atoms n event * initial) =
      rest.foldl (fun before event => eventMatrix atoms n event * before)
        (eventMatrix atoms n event * 1) * initial
    rw [ih (eventMatrix atoms n event * initial),ih (eventMatrix atoms n event * 1)]
    simp only [Matrix.mul_one,Matrix.mul_assoc]

theorem events_cons (atoms : Nat → Operator) (n : Nat) (event : CircuitTrace.Event)
    (rest : List CircuitTrace.Event) :
    eventsMatrix atoms n (event::rest) = eventsMatrix atoms n rest * eventMatrix atoms n event := by
  change rest.foldl (fun before event => eventMatrix atoms n event * before)
    (eventMatrix atoms n event * 1) = eventsMatrix atoms n rest * eventMatrix atoms n event
  rw [events_initial,Matrix.mul_one]

theorem events_append (atoms : Nat → Operator) (n : Nat) (first second : List CircuitTrace.Event) :
    eventsMatrix atoms n (first++second) = eventsMatrix atoms n second * eventsMatrix atoms n first := by
  unfold eventsMatrix
  rw [List.foldl_append,events_initial]
  rfl

theorem events_transport (atoms : Nat → Operator) (n : Nat) (route : List Nat)
    (permuted : route.Perm (List.range n)) (events : List CircuitTrace.Event)
    (inside : ∀ event ∈ events, ∀ i ∈ event.positions, i < n) :
    eventsMatrix atoms n events * routeMatrix n route =
      routeMatrix n route * eventsMatrix atoms n (events.map (CircuitTrace.transport route)) := by
  induction events with
  | nil => simp [eventsMatrix]
  | cons event rest ih =>
    have first := event_transport atoms n route permuted event (inside event (by simp))
    have tail := ih (fun e member => inside e (by simp [member]))
    simp only [List.map_cons,events_cons]
    calc
      _ = eventsMatrix atoms n rest * (eventMatrix atoms n event * routeMatrix n route) := Matrix.mul_assoc _ _ _
      _ = eventsMatrix atoms n rest * (routeMatrix n route * eventMatrix atoms n (CircuitTrace.transport route event)) := by rw [first]
      _ = (eventsMatrix atoms n rest * routeMatrix n route) * eventMatrix atoms n (CircuitTrace.transport route event) := (Matrix.mul_assoc _ _ _).symm
      _ = (routeMatrix n route * eventsMatrix atoms n (rest.map (CircuitTrace.transport route))) *
          eventMatrix atoms n (CircuitTrace.transport route event) := by rw [tail]
      _ = _ := Matrix.mul_assoc _ _ _

theorem sequence_matrix (atoms : Nat → Operator) (n : Nat) (first second : List Nat)
    (firstPerm : first.Perm (List.range n)) (secondPerm : second.Perm (List.range n))
    (firstEvents secondEvents : List CircuitTrace.Event)
    (inside : ∀ event ∈ secondEvents, ∀ i ∈ event.positions, i < n) :
    routeMatrix n (second.map (QleisliKernel.Layout.indexAt first)) *
      eventsMatrix atoms n (firstEvents ++ secondEvents.map (CircuitTrace.transport first)) =
      (routeMatrix n second * eventsMatrix atoms n secondEvents) *
        (routeMatrix n first * eventsMatrix atoms n firstEvents) := by
  rw [route_compose n first second firstPerm secondPerm,events_append]
  rw [Matrix.mul_assoc,← Matrix.mul_assoc (routeMatrix n first),← events_transport atoms n first firstPerm secondEvents inside]
  simp only [Matrix.mul_assoc]

theorem event_left (atoms : Nat → Operator) (n m : Nat) (event : CircuitTrace.Event)
    (inside : ∀ i ∈ event.positions, i < n) :
    eventMatrix atoms (n+m) event =
      CoordinateOperators.lift (Fin.castAdd m) (eventMatrix atoms n event) := by
  let pos := positions n event.positions inside
  have old : event = ⟨event.atom,List.ofFn (fun i => (pos i).val)⟩ := by rw [positions_list]
  rw [old,event_ofFn]
  rw [CoordinateOperators.lift_compose _ (Fin.castAdd_injective n m)]
  have same : List.ofFn (fun i => ((pos i).castAdd m).val) = List.ofFn (fun i => (pos i).val) := rfl
  rw [← same,event_ofFn]
  rfl

theorem event_right (atoms : Nat → Operator) (n m : Nat) (event : CircuitTrace.Event)
    (inside : ∀ i ∈ event.positions, i < m) :
    eventMatrix atoms (n+m) (CircuitTrace.shift n event) =
      CoordinateOperators.lift (Fin.natAdd n) (eventMatrix atoms m event) := by
  let pos := positions m event.positions inside
  have old : event = ⟨event.atom,List.ofFn (fun i => (pos i).val)⟩ := by rw [positions_list]
  have shifted : CircuitTrace.shift n event =
      ⟨event.atom,List.ofFn (fun i => ((pos i).natAdd n).val)⟩ := by
    apply congrArg (CircuitTrace.Event.mk event.atom)
    change event.positions.map _ = _
    conv_lhs => rw [← positions_list m event.positions inside]
    simp only [List.map_ofFn,Fin.val_natAdd]
    rfl
  rw [shifted,event_ofFn]
  conv_rhs => rw [old,event_ofFn]
  rw [CoordinateOperators.lift_compose _ (Fin.natAdd_injective m n)]
  rfl

theorem events_left (atoms : Nat → Operator) (n m : Nat) (events : List CircuitTrace.Event)
    (inside : ∀ event ∈ events, ∀ i ∈ event.positions, i < n) :
    eventsMatrix atoms (n+m) events =
      CoordinateOperators.lift (Fin.castAdd m) (eventsMatrix atoms n events) := by
  induction events with
  | nil => simp [eventsMatrix,CoordinateOperators.lift_one]
  | cons event rest ih =>
    rw [events_cons,events_cons,CoordinateOperators.lift_left_mul,
      event_left atoms n m event (inside event (by simp)),
      ih (fun e member => inside e (by simp [member]))]

theorem events_right (atoms : Nat → Operator) (n m : Nat) (events : List CircuitTrace.Event)
    (inside : ∀ event ∈ events, ∀ i ∈ event.positions, i < m) :
    eventsMatrix atoms (n+m) (events.map (CircuitTrace.shift n)) =
      CoordinateOperators.lift (Fin.natAdd n) (eventsMatrix atoms m events) := by
  induction events with
  | nil => simp [eventsMatrix,CoordinateOperators.lift_one]
  | cons event rest ih =>
    rw [List.map_cons,events_cons,events_cons,CoordinateOperators.lift_right_mul,
      event_right atoms n m event (inside event (by simp)),
      ih (fun e member => inside e (by simp [member]))]

theorem route_tensor (n m : Nat) (first second : List Nat)
    (firstPerm : first.Perm (List.range n)) (secondPerm : second.Perm (List.range m)) :
    routeMatrix (n+m) (first ++ second.map (n + ·)) =
      CoordinateOperators.tensor (routeMatrix n first) (routeMatrix m second) := by
  let a := permutation n first firstPerm
  let b := permutation m second secondPerm
  have combined : first ++ second.map (n + ·) =
      List.ofFn (fun i => (CoordinateOperators.appendRoute a b i).val) := by
    rw [List.ofFn_add]
    change first ++ second.map (n + ·) =
      List.ofFn (fun i : Fin n => (CoordinateOperators.appendRoute a b (i.castAdd m)).val) ++
        List.ofFn (fun i : Fin m => (CoordinateOperators.appendRoute a b (i.natAdd n)).val)
    simp only [CoordinateOperators.appendRoute_left,CoordinateOperators.appendRoute_right,
      Fin.val_castAdd,Fin.val_natAdd]
    rw [permutation_list n first firstPerm]
    congr 1
    conv_lhs => rw [← permutation_list m second secondPerm]
    rw [List.map_ofFn]
    rfl
  rw [combined,route_ofFn,route_eq n first firstPerm,route_eq m second secondPerm,
    CoordinateOperators.tensor_route]

theorem tensor_matrix (atoms : Nat → Operator) (n m : Nat) (first second : List Nat)
    (firstPerm : first.Perm (List.range n)) (secondPerm : second.Perm (List.range m))
    (firstEvents secondEvents : List CircuitTrace.Event)
    (firstInside : ∀ event ∈ firstEvents, ∀ i ∈ event.positions, i < n)
    (secondInside : ∀ event ∈ secondEvents, ∀ i ∈ event.positions, i < m) :
    routeMatrix (n+m) (first ++ second.map (n + ·)) *
      eventsMatrix atoms (n+m) (firstEvents ++ secondEvents.map (CircuitTrace.shift n)) =
      CoordinateOperators.tensor (routeMatrix n first * eventsMatrix atoms n firstEvents)
        (routeMatrix m second * eventsMatrix atoms m secondEvents) := by
  rw [route_tensor n m first second firstPerm secondPerm,events_append,
    events_left atoms n m firstEvents firstInside,events_right atoms n m secondEvents secondInside,
    CoordinateOperators.tensor_lifts,CoordinateOperators.tensor_mul]

def Routing (trace : CircuitTrace.Trace) : Prop :=
  trace.route.Perm (List.range trace.width) ∧
    ∀ event ∈ trace.events.toList, ∀ i ∈ event.positions, i < trace.width

theorem valid_routing (width : Nat) (trace : CircuitTrace.Trace)
    (checked : CircuitTrace.valid width trace = true) : Routing trace := by
  obtain ⟨_,size,permuted,events⟩ := CircuitTrace.valid_fields width trace checked
  exact ⟨by simpa only [size] using permuted,
    fun e member i inside => by simpa only [size] using (events e member).2 i inside⟩

theorem identity_routing (n : Nat) : Routing (CircuitTrace.identity n) := by
  simp [Routing,CircuitTrace.identity]

theorem compose_routing (first second result : CircuitTrace.Trace)
    (a : Routing first) (b : Routing second)
    (computed : CircuitTrace.compose first second = some result) : Routing result := by
  rcases first with ⟨n,first,firstEvents⟩
  rcases second with ⟨m,second,secondEvents⟩
  unfold CircuitTrace.compose at computed
  split at computed
  next same =>
    change n = m at same
    subst m
    cases Option.some.inj computed
    obtain ⟨firstPerm,firstInside⟩ := a
    obtain ⟨secondPerm,secondInside⟩ := b
    have size : first.length = n := by simpa using firstPerm.length_eq
    have lookup (i : Nat) (bound : i < n) : QleisliKernel.Layout.indexAt first i < n := by
      have member := List.getElem_mem (by omega : i < first.length)
      have inside : first[i]'(by omega) < n := by simpa using firstPerm.mem_iff.mp member
      simpa [QleisliKernel.Layout.indexAt,List.getElem?_eq_getElem (by omega : i < first.length)] using inside
    have selectRange : (List.range n).map (QleisliKernel.Layout.indexAt first) = first := by
      apply List.ext_getElem
      · simp [size]
      · intro i left right
        simp [QleisliKernel.Layout.indexAt,List.getElem?_eq_getElem right]
    have rangePerm : ((List.range n).map (QleisliKernel.Layout.indexAt first)).Perm (List.range n) := by
      rw [selectRange]
      exact firstPerm
    refine ⟨(secondPerm.map (QleisliKernel.Layout.indexAt first)).trans rangePerm,?_⟩
    intro event member i selected
    simp only [Array.toList_append,Array.toList_map,List.mem_append,List.mem_map] at member
    rcases member with left | ⟨old,present,rfl⟩
    · exact firstInside event left i selected
    · obtain ⟨old,inside,rfl⟩ := List.mem_map.mp selected
      exact lookup old (secondInside _ present old inside)
  next different => contradiction

def At (atoms : Nat → Operator) (trace : CircuitTrace.Trace) (op : Operator) : Prop :=
  op.inputWidth = trace.width ∧ op.outputWidth = trace.width ∧
    matrixAt trace.width trace.width op = meaning atoms trace

theorem identity_at (atoms : Nat → Operator) (n : Nat) :
    At atoms (CircuitTrace.identity n) (identity n) := by
  refine ⟨rfl,rfl,?_⟩
  rw [meaning_identity]
  exact matrix_identity n

theorem compose_at (atoms : Nat → Operator) (first second result : CircuitTrace.Trace)
    (before after : Operator) (firstAt : At atoms first before) (secondAt : At atoms second after)
    (firstRouting : Routing first) (secondRouting : Routing second)
    (computed : CircuitTrace.compose first second = some result) :
    At atoms result (compose after before) := by
  rcases first with ⟨n,first,firstEvents⟩
  rcases second with ⟨m,second,secondEvents⟩
  unfold CircuitTrace.compose at computed
  split at computed
  next same =>
    change n = m at same
    subst m
    cases Option.some.inj computed
    rcases firstAt with ⟨beforeInput,beforeOutput,beforeMatrix⟩
    rcases secondAt with ⟨afterInput,afterOutput,afterMatrix⟩
    change before.inputWidth = n at beforeInput
    change before.outputWidth = n at beforeOutput
    change after.inputWidth = n at afterInput
    change after.outputWidth = n at afterOutput
    refine ⟨beforeInput,afterOutput,?_⟩
    have matrix := matrix_compose after before
    rw [beforeInput,afterInput,afterOutput] at matrix
    change matrixAt n n (compose after before) = _
    rw [matrix,beforeMatrix,afterMatrix]
    symm
    simpa only [meaning,Array.toList_append,Array.toList_map] using
      sequence_matrix atoms n first second firstRouting.1 secondRouting.1
        firstEvents.toList secondEvents.toList secondRouting.2
  next different => contradiction

theorem fold_at (atoms : Nat → Operator) (traces : List CircuitTrace.Trace) (ops : List Operator)
    (ready : List.Forall₂ (At atoms) traces ops)
    (routed : ∀ trace ∈ traces, Routing trace)
    (start result : CircuitTrace.Trace) (initial : Operator)
    (initialAt : At atoms start initial) (initialRouting : Routing start)
    (computed : traces.foldlM CircuitTrace.compose start = some result) :
    At atoms result (ops.foldl (fun before after => compose after before) initial) := by
  induction ready generalizing start initial with
  | nil => cases Option.some.inj computed; exact initialAt
  | @cons trace op traces ops head tail ih =>
    cases hc : CircuitTrace.compose start trace with
    | none => simp [List.foldlM,hc] at computed
    | some next =>
      have rest : traces.foldlM CircuitTrace.compose next = some result := by
        simpa [List.foldlM,hc] using computed
      exact ih (fun t member => routed t (by simp [member])) next (compose op initial)
        (compose_at atoms start trace next initial op initialAt head initialRouting (routed trace (by simp)) hc)
        (compose_routing start trace next initialRouting (routed trace (by simp)) hc) rest

def ofWiring : Wiring.Operation → CircuitTrace.Operation
  | .route axes => .route axes
  | .sequence => .sequence
  | .tensor => .tensor

theorem tensor_at (atoms : Nat → Operator) (interface : Interface)
    (first second : CircuitTrace.Trace) (before after : Operator)
    (firstAt : At atoms first before) (secondAt : At atoms second after)
    (firstRouting : Routing first) (secondRouting : Routing second)
    (hi : width interface.inputs = first.width+second.width)
    (ho : width interface.outputs = first.width+second.width) :
    At atoms (CircuitTrace.tensor first second) (apply interface .tensor [before,after]) := by
  refine ⟨hi,ho,?_⟩
  change matrixAt (first.width+second.width) (first.width+second.width)
    (apply interface .tensor [before,after]) = _
  rw [HierarchicalTensorCoordinates.apply_tensor_matrix interface first.width second.width
    before after hi ho firstAt.1 firstAt.2.1 secondAt.1 secondAt.2.1,firstAt.2.2,secondAt.2.2]
  symm
  simpa only [meaning,CircuitTrace.tensor,Array.toList_append,Array.toList_map] using
    tensor_matrix atoms first.width second.width first.route second.route firstRouting.1 secondRouting.1
      first.events.toList second.events.toList firstRouting.2 secondRouting.2

/-- Exact normalization of each non-opaque actual operation. Routing, tensor
lifting and event order are derived from the computed trace. -/
theorem eval_at (atoms : Nat → Operator) (interface : Interface) (n : Nat)
    (operation : Wiring.Operation) (traces : List CircuitTrace.Trace) (ops : List Operator)
    (trace : CircuitTrace.Trace) (ready : List.Forall₂ (At atoms) traces ops)
    (validChildren : ∀ t ∈ traces, CircuitTrace.valid t.width t = true)
    (hi : width interface.inputs = n) (ho : width interface.outputs = n)
    (computed : CircuitTrace.eval n (ofWiring operation) traces = some trace)
    (valid : CircuitTrace.valid n trace = true) :
    At atoms trace (apply interface (HierarchicalWiring.tag operation) ops) := by
  have size := (CircuitTrace.valid_fields n trace valid).2.1
  have routed : ∀ t ∈ traces, Routing t := fun t member => valid_routing t.width t (validChildren t member)
  cases operation with
  | route axes =>
    cases ready with
    | cons => simp [ofWiring,CircuitTrace.eval] at computed
    | nil =>
      have equal : trace = ⟨n,axes,#[]⟩ := (Option.some.inj computed).symm
      subst trace
      refine ⟨hi,ho,?_⟩
      dsimp only [meaning,eventsMatrix]
      simp only [List.foldl_nil,Matrix.mul_one]
      ext output input
      simp [matrixAt,apply,bounded,raw,HierarchicalWiring.tag,hi,ho,routeMatrix,HierarchicalWiring.select]
  | sequence =>
    have folded := fold_at atoms traces ops ready routed (CircuitTrace.identity n) trace
      (identity n) (identity_at atoms n) (identity_routing n) computed
    refine ⟨hi.trans size.symm,ho.trans size.symm,?_⟩
    have same : matrixAt trace.width trace.width (apply interface .sequence ops) =
        matrixAt trace.width trace.width (HierarchicalOperators.sequence n ops) := by
      ext output input
      simp [matrixAt,apply,bounded,raw,hi,ho,size]
    exact same.trans folded.2.2
  | tensor =>
    cases ready with
    | nil => simp [ofWiring,CircuitTrace.eval] at computed
    | @cons first before traces ops firstAt rest =>
      cases rest with
      | nil => simp [ofWiring,CircuitTrace.eval] at computed
      | @cons second after traces ops secondAt rest =>
        cases rest with
        | cons => simp [ofWiring,CircuitTrace.eval] at computed
        | nil =>
          have equal : trace = CircuitTrace.tensor first second := (Option.some.inj computed).symm
          subst trace
          exact tensor_at atoms interface first second before after firstAt secondAt
            (routed first (by simp)) (routed second (by simp)) (hi.trans size.symm) (ho.trans size.symm)

end Qleisli.HierarchicalCircuitTrace
