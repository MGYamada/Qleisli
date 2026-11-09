import Qleisli.RuntimeCallHistoryRead
import Qleisli.RuntimeAdjacentRootAction
import Qleisli.RuntimeAdjacentInterval

/-! Induct over the two original native operation folds of a call. The local
law is applied to the actual checked states and events at each prefix.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeCallHistory
open QleisliKernel QleisliKernel.Qirf
open QleisliKernel.Finite (bind_success pure_success)
open Semantics.Finite (Dependency)
open Semantics.Raw (Port)
open Semantics.Observation (Op Event readOps)
open Semantics.RawTrace (Interface)
open Raw.Observation (checkStep checkOps)
open Raw.ObservationAgreement (readStep read_succ layer)
open RuntimeCallTraceFrames (Partition)
open Qleisli.RuntimeObservingPrefix (checkStep_reference_with_writes)
open Qleisli.Semantics.ObservingAction (History run)
open Qleisli.RuntimeObservingComposition (runHistories runHistories_append runHistories_singleton)

/-- The final frame relation and the history transfer for an exact segment.
Only actual successful parent runs contribute results. -/
structure Segment (dependencies : List Dependency) (parentDepth childDepth : Nat)
    (parent child parentAfter childAfter : Interface) (spectators : List Port)
    (parentEvents childEvents : List Event) : Prop where
  partition : Partition parentAfter childAfter spectators
  transport : ∀ actual localHistory, Agrees parent child spectators actual localHistory →
    ∀ parents, run dependencies (parentDepth+1) parentEvents actual = some parents →
    ∃ children, Results dependencies (parentDepth+1) (childDepth+1) parentAfter childAfter spectators
      parentEvents childEvents actual localHistory parents children

/-- A local law must use both native step receipts and both independently
read event lists. It is quantified only over occurrences in the given fold. -/
def StepLaw (dependencies : List Dependency) (parentDepth childDepth : Nat)
    (spectators : List Port) (op : Op) : Prop :=
  ∀ (parent child parentAfter childAfter : Raw.Observation.State) parentEvents childEvents,
    RuntimeInterval.Computed (checkStep dependencies (checkOps dependencies parentDepth) parent op) parentAfter →
    RuntimeInterval.Computed (checkStep dependencies (checkOps dependencies childDepth) child op) childAfter →
    readStep (readOps parentDepth) parent.quantum.reference op = some (parentAfter.quantum.reference,parentEvents) →
    readStep (readOps childDepth) child.quantum.reference op = some (childAfter.quantum.reference,childEvents) →
    Partition parent.quantum.reference child.quantum.reference spectators →
    Segment dependencies parentDepth childDepth parent.quantum.reference child.quantum.reference
      parentAfter.quantum.reference childAfter.quantum.reference spectators parentEvents childEvents

private theorem segment_empty (dependencies : List Dependency) (parentDepth childDepth : Nat)
    (parent child : Interface) (spectators : List Port) (partition : Partition parent child spectators) :
    Segment dependencies parentDepth childDepth parent child parent child spectators [] [] := by
  refine ⟨partition,?_⟩
  intro actual localHistory agrees parents executed
  have same : [actual] = parents := Option.some.inj executed
  subst parents
  exact ⟨[localHistory],rfl,fun _ => rfl,.cons agrees .nil⟩

private theorem Segment.append {dependencies : List Dependency} {parentDepth childDepth : Nat}
    {parent child middleParent middleChild finalParent finalChild : Interface} {spectators : List Port}
    {pFirst cFirst pRest cRest : List Event}
    (head : Segment dependencies parentDepth childDepth parent child middleParent middleChild spectators pFirst cFirst)
    (tail : Segment dependencies parentDepth childDepth middleParent middleChild finalParent finalChild spectators pRest cRest) :
    Segment dependencies parentDepth childDepth parent child finalParent finalChild spectators
      (pFirst++pRest) (cFirst++cRest) := by
  refine ⟨tail.partition,?_⟩
  intro actual localHistory agrees parents executed
  have split := executed
  rw [← runHistories_singleton,runHistories_append,runHistories_singleton] at split
  obtain ⟨firstParents,firstRan,_⟩ := Option.bind_eq_some_iff.mp split
  obtain ⟨firstChildren,first⟩ := head.transport actual localHistory agrees firstParents firstRan
  exact first.append_of_run executed tail.transport

private theorem read_cons {depth : Nat} {initial middle final : Interface} {op : Op} {ops : List Op}
    {head tail : List Event}
    (first : readStep (readOps depth) initial op = some (middle,head))
    (rest : readOps (depth+1) middle ops = some (final,tail)) :
    readOps (depth+1) initial (op::ops) = some (final,head++tail) := by
  have single : readOps (depth+1) initial [op] = some (middle,head) := by
    simp [read_succ,layer,first]
  change readOps (depth+1) initial ([op]++ops) = _
  rw [RuntimeAdjacentSlices.readOps_append,single]
  simp [rest]

private theorem checked_fold {dependencies : List Dependency} {parentDepth childDepth : Nat}
    {spectators : List Port} (operations : List Op)
    {parent child parentAfter childAfter : Raw.Observation.State}
    (parentFold : RuntimeInterval.Computed
      (operations.foldlM (checkStep dependencies (checkOps dependencies parentDepth)) parent) parentAfter)
    (childFold : RuntimeInterval.Computed
      (operations.foldlM (checkStep dependencies (checkOps dependencies childDepth)) child) childAfter)
    (partition : Partition parent.quantum.reference child.quantum.reference spectators)
    (localLaw : ∀ op ∈ operations, StepLaw dependencies parentDepth childDepth spectators op) :
    ∃ parentEvents childEvents,
      readOps (parentDepth+1) parent.quantum.reference operations = some (parentAfter.quantum.reference,parentEvents) ∧
      readOps (childDepth+1) child.quantum.reference operations = some (childAfter.quantum.reference,childEvents) ∧
      Segment dependencies parentDepth childDepth parent.quantum.reference child.quantum.reference
        parentAfter.quantum.reference childAfter.quantum.reference spectators parentEvents childEvents := by
  induction operations generalizing parent child with
  | nil =>
    obtain ⟨pWork,pLeft,pRan⟩ := parentFold
    obtain ⟨cWork,cLeft,cRan⟩ := childFold
    have pSame := (pure_success _ _ _ _ pRan).1
    have cSame := (pure_success _ _ _ _ cRan).1
    subst parentAfter
    subst childAfter
    exact ⟨[],[],rfl,rfl,segment_empty dependencies parentDepth childDepth _ _ spectators partition⟩
  | cons op ops ih =>
    obtain ⟨pWork,pLeft,pRan⟩ := parentFold
    obtain ⟨cWork,cLeft,cRan⟩ := childFold
    simp only [List.foldlM_cons] at pRan cRan
    obtain ⟨pMiddle,pNext,pFirst,pRest⟩ := bind_success _ _ _ _ _ pRan
    obtain ⟨cMiddle,cNext,cFirst,cRest⟩ := bind_success _ _ _ _ _ cRan
    obtain ⟨_,pHead,pRead,_⟩ := checkStep_reference_with_writes _ _ _ _ _ _ _ pFirst
    obtain ⟨_,cHead,cRead,_⟩ := checkStep_reference_with_writes _ _ _ _ _ _ _ cFirst
    have head := localLaw op List.mem_cons_self _ _ _ _ pHead cHead
      ⟨pWork,pNext,pFirst⟩ ⟨cWork,cNext,cFirst⟩ pRead cRead partition
    obtain ⟨pTail,cTail,pReadRest,cReadRest,tail⟩ :=
      ih ⟨pNext,pLeft,pRest⟩ ⟨cNext,cLeft,cRest⟩ head.partition
        (fun next member => localLaw next (List.mem_cons_of_mem _ member))
    exact ⟨pHead++pTail,cHead++cTail,read_cons pRead pReadRest,read_cons cRead cReadRest,head.append tail⟩

/-- Lift the original paired operation checks to their exact reader results
and preserve the whole ordered history family on every reference column. -/
theorem checked_operations {dependencies : List Dependency} {parentDepth childDepth : Nat}
    {spectators : List Port} (operations : List Op)
    {parent child parentAfter childAfter : Raw.Observation.State}
    (parentRead : RuntimeInterval.Computed (checkOps dependencies (parentDepth+1) parent operations) parentAfter)
    (childRead : RuntimeInterval.Computed (checkOps dependencies (childDepth+1) child operations) childAfter)
    (partition : Partition parent.quantum.reference child.quantum.reference spectators)
    (localLaw : ∀ op ∈ operations, StepLaw dependencies parentDepth childDepth spectators op) :
    ∃ parentEvents childEvents,
      readOps (parentDepth+1) parent.quantum.reference operations = some (parentAfter.quantum.reference,parentEvents) ∧
      readOps (childDepth+1) child.quantum.reference operations = some (childAfter.quantum.reference,childEvents) ∧
      Segment dependencies parentDepth childDepth parent.quantum.reference child.quantum.reference
        parentAfter.quantum.reference childAfter.quantum.reference spectators parentEvents childEvents :=
  checked_fold operations (RuntimeAdjacentSlices.underlying parentRead)
    (RuntimeAdjacentSlices.underlying childRead) partition localLaw

#print axioms checked_operations
end Qleisli.RuntimeCallHistory
