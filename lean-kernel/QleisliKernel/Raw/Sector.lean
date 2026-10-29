import QleisliKernel.FiniteRestriction.Check
import QleisliKernel.Raw.Trace
import QleisliKernel.Raw.Finite
import QleisliKernel.Semantics.Function

/-! Original Raw trace and owner binding for bounded finite sector equations.
Reuse the actual Raw reader and common literal extraction. This internal component
enables no native mode and infers no nominal/source type identity from widths.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Raw.Sector
open QleisliKernel.Semantics.Finite QleisliKernel.Semantics.Exact
open QleisliKernel.Semantics.Raw QleisliKernel.Finite

/-- Same exact permutation coordinate as the existing independent Raw meaning. -/
theorem gather_range (label n : Nat) : gather label (List.range n) = label % 2^n := by
  induction n with
  | zero => simp only [gather,List.range_zero,List.zipIdx_nil,List.map_nil,List.sum_nil,Nat.pow_zero]; omega
  | succ n ih =>
    simp only [gather,List.range_succ,List.zipIdx_append,List.length_range,
      Nat.zero_add,List.zipIdx_cons,List.zipIdx_nil,List.map_append,List.map_cons,
      List.map_nil,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero]
    change gather label (List.range n) + bit label n * 2^n = label % 2^(n+1)
    rw [ih,Nat.pow_succ,Nat.mod_mul]
    simp [bit,Nat.mul_comm]

theorem gather_identity (label bits : Nat) (bound : label < 2^bits) :
    gather label (List.range bits) = label := by
  rw [gather_range,Nat.mod_eq_of_lt bound]

def eventValid (bits : Nat) : Event → Bool
  | .circuit width _ => width == bits
  | .reorder width axes => width == bits && axes == List.range bits
  | _ => false

/-- No producer steps are accepted. The existing independent extraction is
called only for full-width circuits and the exact identity output permutation. -/
def eventSteps (bits : Nat) (event : Event) : Except Error (List Step) := do
  if !eventValid bits event then throw .request
  readOption (QleisliKernel.Semantics.Function.extracted event)

def EventPiece (bits : Nat) (event : Event) (steps : List Step) : Prop :=
  event = .circuit bits steps ∨
    (event = .reorder bits (List.range bits) ∧ steps = [])

theorem eventSteps_bound (bits : Nat) (event : Event) (steps : List Step)
    (ok : eventSteps bits event = .ok steps) : EventPiece bits event steps := by
  cases event with
  | circuit width body =>
    by_cases same : width = bits
    · subst width
      simp [eventSteps,eventValid,QleisliKernel.Semantics.Function.extracted,readOption,
        bind,Except.bind,pure,Except.pure] at ok
      subst steps
      exact Or.inl rfl
    · simp [eventSteps,eventValid,same,bind,Except.bind] at ok
  | reorder width axes =>
    by_cases same : width = bits
    · subst width
      by_cases identity : axes = List.range bits
      · subst axes
        simp [eventSteps,eventValid,QleisliKernel.Semantics.Function.extracted,readOption,
          bind,Except.bind,pure,Except.pure] at ok
        subst steps
        exact Or.inr ⟨rfl,rfl⟩
      · simp [eventSteps,eventValid,identity,bind,Except.bind] at ok
    · simp [eventSteps,eventValid,same,bind,Except.bind] at ok
  | init0 width => simp [eventSteps,eventValid,bind,Except.bind] at ok
  | liftBasis before after inputAxes outputAxes table => simp [eventSteps,eventValid,bind,Except.bind] at ok
  | computed width axes sourceBits ancillaBits function uses logical =>
    simp [eventSteps,eventValid,bind,Except.bind] at ok
  | protectedComputed width axes sourceBits ancillaBits function uses =>
    simp [eventSteps,eventValid,bind,Except.bind] at ok

def readEvents (bits : Nat) (events : List Event) : Except Error (List Step) := do
  let pieces ← events.mapM (eventSteps bits)
  return pieces.flatten

theorem exceptMap_relation {α β : Type} (step : α → Except Error β) (p : α → β → Prop)
    (preserve : ∀ a b, step a = .ok b → p a b) (xs : List α) (ys : List β)
    (ok : xs.mapM step = .ok ys) : QleisliKernel.Exact.ListRel p xs ys := by
  induction xs generalizing ys with
  | nil =>
    simp only [List.mapM_nil,pure,Except.pure,Except.ok.injEq] at ok
    subst ys
    trivial
  | cons a xs ih =>
    simp only [List.mapM_cons] at ok
    obtain ⟨b,hb,h⟩ := except_bind_success _ _ _ ok
    obtain ⟨rest,hr,h⟩ := except_bind_success _ _ _ h
    simp only [pure,Except.pure,Except.ok.injEq] at h
    subst ys
    exact ⟨preserve a b hb,ih rest hr⟩

theorem readEvents_bound (bits : Nat) (events : List Event) (steps : List Step)
    (ok : readEvents bits events = .ok steps) :
    ∃ pieces, QleisliKernel.Exact.ListRel (EventPiece bits) events pieces ∧ steps = pieces.flatten := by
  obtain ⟨pieces,hp,h⟩ := except_bind_success _ _ _ ok
  simp only [pure,Except.pure,Except.ok.injEq] at h
  exact ⟨pieces,exceptMap_relation (eventSteps bits) (EventPiece bits)
    (eventSteps_bound bits) events pieces hp,h.symm⟩

/-- This is a physical frame check, not nominal type inference. Complete source
trees still need their independent enclosing request/reader. Zero-width ports
remain two distinct forest positions, and returned wire order is unchanged. -/
def ownerInterface (selector target : Basis) (program : Program) (prepared : QleisliKernel.Raw.Prepared) : Bool :=
  match program.inputs,program.outputs with
  | [selectorIn,targetIn],[selectorOut,targetOut] =>
    selectorIn.bits == width selector && targetIn.bits == width target &&
      ((prepared.state.live.find? (·.token == selectorOut)).map fun port =>
        port.bits == selectorIn.bits && port.wires == selectorIn.wires).getD false &&
      ((prepared.state.live.find? (·.token == targetOut)).map fun port =>
        port.bits == targetIn.bits && port.wires == targetIn.wires).getD false
  | _,_ => false

/-- The Raw reader may traverse complete original fields before the sector
profile rejects an event. Charge those fields and duplicate/table scans first. -/
def subjectFields (program : Program) : Nat :=
  16 * ((program.operations.length+1)^2 + QleisliKernel.Raw.rawFields program +
    (program.operations.map fun operation => match operation with
      | .applyUnitary _ _ steps => QleisliKernel.FiniteRestriction.restrictionFields steps
      | .certifiedCompute _ _ _ function uses logical =>
        function.length^2 + QleisliKernel.FiniteRestriction.restrictionFields (uses ++ logical)
      | .computeUseUncompute _ _ _ _ function uses => function.length^2 + uses.length^2
      | .liftBasis _ _ _ table => table.length^2
      | .quantumIf _ _ _ _ zero one => zero.length + one.length
      | _ => 0).sum)

private structure Subject where
  prepared : QleisliKernel.Raw.Prepared
  steps : List Step

private def readSubject (dependencies : List Dependency) (selector target : Basis)
    (program : Program) : WorkM Subject := do
  guard (basisValid selector && basisValid target && program.operations.length ≤ 1024) .limit
  guard (program.effect == .unitary && program.inputs.length == 2 && program.outputs.length == 2) .request
  exactWork (QleisliKernel.Exact.charge (subjectFields program))
  let prepared ← lift (QleisliKernel.Raw.prepare (dependencies.map (·.signature)) program)
  guard (ownerInterface selector target program prepared) .request
  let steps ← lift (readEvents (width selector + width target) prepared.events)
  return ⟨prepared,steps⟩

structure Retained where
  prepared : QleisliKernel.Raw.Prepared
  steps : List Step
  sectors : List Matrix

/-- Check the original Raw program and every extracted event before invoking
the shared sector gate. Fresh dependency/source/arm binding belongs to the
enclosing caller; this component itself grants no native accepted handle. -/
def check (dependencies : List Dependency) (selector target : Basis) (program : Program)
    (required : List Matrix) : WorkM Retained := do
  let subject ← readSubject dependencies selector target program
  let sectors ← QleisliKernel.FiniteRestriction.checkSectors dependencies selector target
    ⟨QleisliKernel.FiniteRestriction.joinedBasis selector target,subject.steps⟩ required
  return ⟨subject.prepared,subject.steps,sectors⟩

/-- A retained physical Raw subject, its independent complete original trace,
and all ordered exact sector equations. Source/nominal identities are separate. -/
def Binding (dependencies : List Dependency) (selector target : Basis) (program : Program)
    (required : List Matrix) (result : Retained) : Prop :=
  (basisValid selector && basisValid target && program.operations.length ≤ 1024) = true ∧
    (program.effect == .unitary && program.inputs.length == 2 && program.outputs.length == 2) = true ∧
    QleisliKernel.Raw.prepare (dependencies.map (·.signature)) program = .ok result.prepared ∧
    QleisliKernel.Semantics.RawTrace.run program = some result.prepared.reference ∧
    ownerInterface selector target program result.prepared = true ∧
    (∃ pieces, QleisliKernel.Exact.ListRel (EventPiece (width selector + width target))
      result.prepared.events pieces ∧ result.steps = pieces.flatten) ∧
    (∃ before after,
      (QleisliKernel.FiniteRestriction.checkSectors dependencies selector target
        ⟨QleisliKernel.FiniteRestriction.joinedBasis selector target,result.steps⟩ required).run before =
          (.ok result.sectors,after)) ∧
    QleisliKernel.Exact.ListRel
      (QleisliKernel.FiniteRestriction.SectorBinding dependencies (width selector) target result.steps)
      required.zipIdx result.sectors

theorem check_bound (dependencies : List Dependency) (selector target : Basis) (program : Program)
    (required : List Matrix) (result : Retained) (work left : Nat)
    (ok : (check dependencies selector target program required).run work = (.ok result,left)) :
    Binding dependencies selector target program required result := by
  simp only [check,readSubject,bind_assoc,pure_bind] at ok
  obtain ⟨_,w₁,hl,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,he,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₃,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨prepared,w₄,hp,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₅,ho,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨steps,w₆,hs,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨sectors,w₇,hc,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst result
  have preparedEq := (lift_success _ _ _ _ hp).1
  have readEq := (lift_success _ _ _ _ hs).1
  have sectorEq := QleisliKernel.FiniteRestriction.checkSectors_bound dependencies selector target
    ⟨QleisliKernel.FiniteRestriction.joinedBasis selector target,steps⟩ required sectors w₆ w₇ hc
  exact ⟨(guard_success _ _ _ _ hl).1,(guard_success _ _ _ _ he).1,preparedEq,
    QleisliKernel.Raw.prepare_reference _ _ _ preparedEq,(guard_success _ _ _ _ ho).1,
    readEvents_bound _ _ _ readEq,⟨w₆,w₇,hc⟩,sectorEq.2.2.2⟩

/-- The discarded reorder events are literally identity on every coordinate
in their full physical domain, including the zero-bit domain. -/
theorem reorder_identity (bits width : Nat) (axes : List Nat) (steps : List Step)
    (piece : EventPiece bits (.reorder width axes) steps) (label : Nat) (bound : label < 2^bits) :
    width = bits ∧ steps = [] ∧ gather label axes = label := by
  rcases piece with impossible | ⟨same,empty⟩
  · cases impossible
  · cases same
    exact ⟨rfl,empty,gather_identity label bits bound⟩

/-- Concatenation preserves literal execution order and every arithmetic error;
no scalar additions or multiplications are rearranged. -/
theorem flatten_execution (dependencies : List Dependency) (pieces : List (List Step))
    (values : List Scalar) :
    pieces.flatten.foldlM (fun values step => applyStep dependencies step values) values =
      pieces.foldlM (fun values steps =>
        steps.foldlM (fun values step => applyStep dependencies step values) values) values := by
  induction pieces generalizing values with
  | nil => rfl
  | cons piece pieces ih =>
    rw [List.flatten_cons,List.foldlM_append,List.foldlM_cons]
    cases executed : piece.foldlM (fun values step => applyStep dependencies step values) values with
    | error error => rfl
    | ok result => simpa only [bind,Except.bind] using ih result

#print axioms check_bound
#print axioms reorder_identity
#print axioms flatten_execution
def read (dependencies : List Dependency) (selector target : Basis)
    (program : Program) : WorkM Retained := do
  let subject ← readSubject dependencies selector target program
  let sectors ← QleisliKernel.FiniteRestriction.readSectors dependencies selector target
    ⟨QleisliKernel.FiniteRestriction.joinedBasis selector target,subject.steps⟩
  return ⟨subject.prepared,subject.steps,sectors⟩

def ReadBinding (dependencies : List Dependency) (selector target : Basis)
    (program : Program) (result : Retained) : Prop :=
  (basisValid selector && basisValid target && program.operations.length ≤ 1024) = true ∧
    (program.effect == .unitary && program.inputs.length == 2 && program.outputs.length == 2) = true ∧
    QleisliKernel.Raw.prepare (dependencies.map (·.signature)) program = .ok result.prepared ∧
    QleisliKernel.Semantics.RawTrace.run program = some result.prepared.reference ∧
    ownerInterface selector target program result.prepared = true ∧
    (∃ pieces, QleisliKernel.Exact.ListRel (EventPiece (width selector + width target))
      result.prepared.events pieces ∧ result.steps = pieces.flatten) ∧
    (∃ before after,
      (QleisliKernel.FiniteRestriction.readSectors dependencies selector target
        ⟨QleisliKernel.FiniteRestriction.joinedBasis selector target,result.steps⟩).run before =
          (.ok result.sectors,after)) ∧
    QleisliKernel.Exact.ListRel
      (QleisliKernel.FiniteRestriction.SectorEvaluationBinding dependencies (width selector) target result.steps)
      (List.range (2^width selector)) result.sectors

theorem read_bound (dependencies : List Dependency) (selector target : Basis)
    (program : Program) (result : Retained) (work left : Nat)
    (ok : (read dependencies selector target program).run work = (.ok result,left)) :
    ReadBinding dependencies selector target program result := by
  simp only [read,readSubject,bind_assoc,pure_bind] at ok
  obtain ⟨_,w₁,hl,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,he,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₃,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨prepared,w₄,hp,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₅,ho,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨steps,w₆,hs,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨sectors,w₇,hc,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst result
  have preparedEq := (lift_success _ _ _ _ hp).1
  have readEq := (lift_success _ _ _ _ hs).1
  have sectorEq := QleisliKernel.FiniteRestriction.readSectors_bound dependencies selector target
    ⟨QleisliKernel.FiniteRestriction.joinedBasis selector target,steps⟩ sectors w₆ w₇ hc
  exact ⟨(guard_success _ _ _ _ hl).1,(guard_success _ _ _ _ he).1,preparedEq,
    QleisliKernel.Raw.prepare_reference _ _ _ preparedEq,(guard_success _ _ _ _ ho).1,
    readEvents_bound _ _ _ readEq,⟨w₆,w₇,hc⟩,sectorEq.2.2.2⟩


end QleisliKernel.Raw.Sector
