import QleisliKernel.Qirf.RuntimeNestedArm
import QleisliKernel.Qirf.RuntimeLinkedEligibility

/-! Residual original Meaning duties after checking one common body.
Coverage requires a unique written occurrence with positive semantic evidence.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeArmDutyCoverage
open QleisliKernel Finite SourceTypes
open QleisliKernel.Qirf.RuntimeBodyOperations (Prepared Traversed ArmLink)

variable {artifact : Artifact} {owner name : String} {arguments : StaticTypes.Arguments}
  {request : RuntimeContextRequest.Context} {order : Array Nat} {runtime : RuntimeFamily.Request}
  {prepared : Prepared artifact owner name arguments request}

abbrev Position (prepared : Prepared artifact owner name arguments request) := Fin prepared.source.pending.entries.length

/-- The original queue ordinal survives retention of its assessment. -/
theorem original_index (q : Position prepared) : prepared.source.pending.entries[q.val].index.val = q.val := by
  have every := prepared.source.pending.every
  have length := congrArg List.length every
  simp only [List.length_map,List.length_finRange] at length
  have bound : q.val < (List.finRange prepared.source.pending.queue.items.length).length := by
    rw [List.length_finRange,← length]
    exact q.isLt
  have lookup := congrArg (fun xs : List (Fin prepared.source.pending.queue.items.length) => xs[q.val]?) every
  change (prepared.source.pending.entries.map (·.index))[q.val]? =
    (List.finRange prepared.source.pending.queue.items.length)[q.val]? at lookup
  rw [List.getElem?_map,List.getElem?_eq_getElem q.isLt,Option.map_some,List.getElem?_eq_getElem bound] at lookup
  simpa only [List.getElem_finRange,Fin.val_cast] using congrArg Fin.val (Option.some.inj lookup)

/-- The checked length rules out an unfinished scan at zero fuel. Nat.rec
has a compiled implementation for the dependent report as well as the index. -/
private def foldTotal {α : Type} (p : List α → Type) (empty : p [])
    (step : (a : α) → (tail : List α) → p tail → p (a :: tail)) (xs : List α) : p xs :=
  (Nat.rec (motive := fun n => (ys : List α) → ys.length ≤ n → p ys)
    (fun ys => match ys with
      | [] => fun _ => empty
      | _ :: _ => fun bound => False.elim (Nat.not_succ_le_zero _ bound))
    (fun _ next ys => match ys with
      | [] => fun _ => empty
      | a :: tail => fun bound => step a tail (next tail (Nat.le_of_succ_le_succ bound)))
    xs.length) xs (Nat.le_refl _)

private def references {n : Nat} : List (Fin n) → Nat → Fin n → List Nat :=
  foldTotal (fun _ => Nat → Fin n → List Nat) (fun _ _ => [])
    (fun key _ next start q =>
      let tail := next (start+1) q
      if key = q then start :: tail else tail)

private def buckets {n : Nat} : List (Fin n) → Nat → Vector (List Nat) n :=
  foldTotal (fun _ => Nat → Vector (List Nat) n) (fun _ => Vector.replicate n [])
    (fun key _ next start =>
      let tail := next (start+1)
      tail.set key.val (start :: tail[key.val]) key.isLt)

private theorem buckets_spec {n : Nat} (keys : List (Fin n)) (start : Nat) (q : Fin n) :
    (buckets keys start)[q.val] = references keys start q := by
  induction keys generalizing start with
  | nil =>
    change (Vector.replicate n ([] : List Nat))[q.val] = []
    simp
  | cons key rest ih =>
    change ((buckets rest (start+1)).set key.val (start :: (buckets rest (start+1))[key.val]) key.isLt)[q.val] =
      (if key = q then start :: references rest (start+1) q else references rest (start+1) q)
    by_cases same : key = q
    · subst key
      simp [ih]
    · have different : key.val ≠ q.val := fun h => same (Fin.ext h)
      simp only [Vector.getElem_set,if_neg different,if_neg same,ih]

def Positive (body : Traversed prepared order runtime) (link : ArmLink body.checked) : Prop :=
  let receipt := body.checked.receipts[link.receiptIndex]
  RuntimeLinkedSubject.Positive receipt.location.site receipt.prepared receipt.evidence.checked
    receipt.evidence.source link.markerIndex link.binding.instanceBinding link.subject

private def positive (body : Traversed prepared order runtime) (link : ArmLink body.checked) : Bool :=
  let receipt := body.checked.receipts[link.receiptIndex]
  RuntimeLinkedSubject.positive receipt.location.site receipt.prepared receipt.evidence.checked
    receipt.evidence.source link.markerIndex link.binding.instanceBinding link.subject

private theorem positive_sound (body : Traversed prepared order runtime) (link : ArmLink body.checked) :
    positive body link = true → Positive body link :=
  RuntimeLinkedSubject.positive_sound _ _ _ _ _ _ _

private abbrev Receipt (body : Traversed prepared order runtime) :=
  RuntimeGraphOperation.StagedReceipt (RuntimeBodyOperations.stagedConsumption artifact prepared.source.catalogue body.root)

private abbrev Payload (body : Traversed prepared order runtime) (receipt : Receipt body)
    (entry : SourcePendingMeaning.Entry prepared.source.pending.queue) (marker : Nat) :=
  (binding : RuntimeWrittenDuty.Binding receipt.location.site receipt.prepared receipt.evidence.checked
    receipt.evidence.source marker entry receipt.location.path) ×
  RuntimeLinkedSubject.Evidence receipt.location.site receipt.prepared receipt.evidence.checked
    receipt.evidence.source marker binding.instanceBinding

-- Transport the original payload to the two indexed array reads. The equality
-- proofs erase; the eligibility test receives the actual receipt and entry.
private def indexedPositive (body : Traversed prepared order runtime) (link : ArmLink body.checked)
    (receipt : Receipt body) (entry : SourcePendingMeaning.Entry prepared.source.pending.queue)
    (atReceipt : receipt = body.checked.receipts[link.receiptIndex])
    (atEntry : entry = prepared.source.pending.entries[link.queueIndex]) :
    {value : Bool // value = positive body link} := by
  let original : Payload body body.checked.receipts[link.receiptIndex] prepared.source.pending.entries[link.queueIndex]
      link.markerIndex := ⟨link.binding,link.subject⟩
  let payload : Payload body receipt entry link.markerIndex := atEntry.symm ▸ atReceipt.symm ▸ original
  refine ⟨RuntimeLinkedSubject.positive receipt.location.site receipt.prepared receipt.evidence.checked
    receipt.evidence.source link.markerIndex payload.1.instanceBinding payload.2,?_⟩
  subst receipt
  subst entry
  rfl

/-- A supplying argument and its enclosing arm are distinct claims even
when their exact actions agree. Each points at its own original queue duty. -/
inductive Origin (body : Traversed prepared order runtime) (link : ArmLink body.checked) :
    Position prepared → Type where
  | direct (test : {value : Bool // value = positive body link}) : Origin body link link.queueIndex
  | enclosing (proof : RuntimeNestedArm.Evidence body.checked link .enclosing) : Origin body link link.queueIndex
  | supplying (q : Position prepared) (proof : RuntimeNestedArm.Evidence body.checked link (.supplying q)) :
      Origin body link q

def Origin.accepted {body : Traversed prepared order runtime} {link q} : Origin body link q → Bool
  | .direct test => test.val
  | .enclosing _ | .supplying .. => true

def Origin.Contract {body : Traversed prepared order runtime} {link q} : Origin body link q → Prop
  | .direct _ => Positive body link
  | .enclosing _ => Nonempty (RuntimeNestedArm.Evidence body.checked link .enclosing)
  | .supplying i _ => Nonempty (RuntimeNestedArm.Evidence body.checked link (.supplying i))

theorem Origin.sound {body : Traversed prepared order runtime} {link q} (origin : Origin body link q)
    (accepted : origin.accepted = true) : origin.Contract := by
  cases origin with
  | direct test => exact positive_sound body link (test.property.symm.trans accepted)
  | enclosing proof => exact ⟨proof⟩
  | supplying _ proof => exact ⟨proof⟩

structure Candidate (body : Traversed prepared order runtime) where
  armIndex : Nat
  link : ArmLink body.checked
  atWritten : body.writtenArms[armIndex]? = some link
  queueIndex : Position prepared
  origin : Origin body link queueIndex

/-- Keep one enclosing candidate per written link, including a negative
one, and add the original supplying position only with its own evidence. -/
def readCandidates (body : Traversed prepared order runtime) : WorkM (List (Candidate body)) := do
  let arms := body.writtenArms
  let entries := prepared.source.pending.entries
  exactWork (Exact.charge (32*(arms.length+entries.length+body.checked.receipts.length+1)))
  let values := entries.toArray
  let receipts := body.checked.receipts.toArray
  let armArray := arms.toArray
  let rows ← (List.finRange arms.length).mapM fun (ordinal : Fin arms.length) => do
    let i := ordinal.val
    let chosen := armArray[i]'(by simpa only [armArray,List.size_toArray] using ordinal.isLt)
    have selected : arms[i]? = some chosen := by
      simp only [chosen,armArray,List.getElem_toArray]
      exact List.getElem?_eq_getElem (show i < arms.length from ordinal.isLt)
    let entry := values[chosen.queueIndex.val]'(by simpa only [values,entries,List.size_toArray] using chosen.queueIndex.isLt)
    let original := indexedPositive body chosen
      (receipts[chosen.receiptIndex.val]'(by simpa only [receipts,List.size_toArray] using chosen.receiptIndex.isLt))
      entry
      (by simp only [receipts,List.getElem_toArray,Fin.getElem_fin])
      (by simp only [entry,values,entries,List.getElem_toArray,Fin.getElem_fin])
    let direct : Candidate body := ⟨i,chosen,selected,chosen.queueIndex,.direct original⟩
    if !RuntimeNestedDuty.possible entry then return [direct]
    match ← RuntimeNestedArm.read body.checked chosen with
    | none => return [direct]
    | some nested =>
      let caller : Candidate body := ⟨i,chosen,selected,nested.position,.supplying nested.position nested.supplying⟩
      let parent : Candidate body := match nested.enclosing with
        | some proof => ⟨i,chosen,selected,chosen.queueIndex,.enclosing proof⟩
        | none => direct
      return [parent,caller]
  return rows.flatten

/-- All candidate positions, including unresolved enclosing links. Two
references to one original position stay ambiguous even if one is positive. -/
def occurrences {body : Traversed prepared order runtime} (candidates : List (Candidate body))
    (q : Position prepared) : List Nat :=
  references (candidates.map (·.queueIndex)) 0 q

private def single {body : Traversed prepared order runtime} (q : Position prepared)
    (lookup : Nat → Option (Candidate body)) : List Nat → Bool
  | [index] => match lookup index with
    | none => false
    | some found => decide (found.queueIndex = q ∧ found.origin.accepted = true)
  | _ => false

def covered {body : Traversed prepared order runtime} (candidates : List (Candidate body))
    (q : Position prepared) : Bool :=
  single q (fun i => candidates[i]?) (occurrences candidates q)

def remaining {body : Traversed prepared order runtime} (candidates : List (Candidate body))
    (q : Position prepared) : Bool :=
  prepared.source.pending.entries[q.val].unconsumed && !covered candidates q

structure Discharge {body : Traversed prepared order runtime} (candidates : List (Candidate body)) (q : Position prepared) where
  index : Nat
  candidate : Candidate body
  atCandidate : candidates[index]? = some candidate
  queue : candidate.queueIndex = q
  required : prepared.source.pending.entries[q.val].unconsumed = true
  unique : occurrences candidates q = [index]
  proved : candidate.origin.Contract

/-- The enclosing arm link locates the common traversal. For a supplying
credit, candidate.origin carries its separately indexed caller obligation. -/
def Discharge.link {body : Traversed prepared order runtime} {candidates : List (Candidate body)} {q}
    (witness : Discharge candidates q) := witness.candidate.link

private inductive Decision {body : Traversed prepared order runtime} (candidates : List (Candidate body)) (q : Position prepared) where
  | skipped (already : prepared.source.pending.entries[q.val].unconsumed = false)
  | residual (required : prepared.source.pending.entries[q.val].unconsumed = true) (openDuty : covered candidates q = false)
  | consumed (witness : Discharge candidates q) (closed : covered candidates q = true)

private def classify {body : Traversed prepared order runtime} (candidates : List (Candidate body)) (q : Position prepared)
    (required : Bool) (need : required = prepared.source.pending.entries[q.val].unconsumed)
    (members : List Nat) (same : occurrences candidates q = members)
    (lookup : Nat → Option (Candidate body)) (original : ∀ i,candidates[i]? = lookup i) :
    Decision candidates q := by
  cases required with
  | false => exact .skipped need.symm
  | true =>
    cases members with
    | nil => exact .residual need.symm (by simp [covered,same,single])
    | cons i rest =>
      cases rest with
      | cons j tail => exact .residual need.symm (by simp [covered,same,single])
      | nil =>
        cases atIndex : lookup i with
        | none => exact .residual need.symm (by simp [covered,same,single,(original i).trans atIndex])
        | some found =>
          have selected := (original i).trans atIndex
          if yes : found.queueIndex = q ∧ found.origin.accepted = true then
            exact .consumed ⟨i,found,selected,yes.1,need.symm,same,found.origin.sound yes.2⟩
              (by simp [covered,same,single,selected,yes])
          else exact .residual need.symm (by simp [covered,same,single,selected,yes])

structure Classified {body : Traversed prepared order runtime} (candidates : List (Candidate body)) (indices : List (Position prepared)) where
  residual : List (Position prepared)
  consumed : List ((q : Position prepared) × Discharge candidates q)
  exactResidual : residual = indices.filter (remaining candidates)
  exactConsumed : consumed.map (·.1) =
    indices.filter (fun q => prepared.source.pending.entries[q.val].unconsumed && covered candidates q)

private def collect {body : Traversed prepared order runtime} (candidates : List (Candidate body))
    (row : (q : Position prepared) → Decision candidates q) :
    (indices : List (Position prepared)) → Classified candidates indices :=
  foldTotal (Classified candidates) ⟨[],[],rfl,rfl⟩ (fun q _ later =>
    match row q with
    | .skipped already => ⟨later.residual,later.consumed,
        by simpa [List.filter_cons,remaining,already] using later.exactResidual,
        by simpa [List.filter_cons,already] using later.exactConsumed⟩
    | .residual required openDuty => ⟨q :: later.residual,later.consumed,
        by simpa [List.filter_cons,remaining,required,openDuty] using congrArg (List.cons q) later.exactResidual,
        by simpa [List.filter_cons,required,openDuty] using later.exactConsumed⟩
    | .consumed witness closed => ⟨later.residual,⟨q,witness⟩ :: later.consumed,
        by simpa [List.filter_cons,remaining,witness.required,closed] using later.exactResidual,
        by simpa [List.filter_cons,witness.required,closed] using congrArg (List.cons q) later.exactConsumed⟩)

structure Report (body : Traversed prepared order runtime) (indices : List (Position prepared)) where
  candidates : List (Candidate body)
  candidatesRead : RuntimeInterval.Computed (readCandidates body) candidates
  result : Classified candidates indices

def Report.residual {body : Traversed prepared order runtime} {indices} (report : Report body indices) := report.result.residual
def Report.consumed {body : Traversed prepared order runtime} {indices} (report : Report body indices) := report.result.consumed

def read (body : Traversed prepared order runtime) :
    WorkM (Report body (List.finRange prepared.source.pending.entries.length)) := do
  let candidates ← NaturalAffine.witness (readCandidates body)
  let entries := prepared.source.pending.entries
  exactWork (Exact.charge (32*(entries.length+candidates.val.length+1)))
  let values := entries.toArray
  let links := candidates.val.toArray
  let keys := candidates.val.map (·.queueIndex)
  let table := buckets keys 0
  let result := collect candidates.val (fun q =>
    let entry := values[q.val]'(by simpa only [values,entries,List.size_toArray] using q.isLt)
    classify candidates.val q entry.unconsumed (by simp only [entry,values,entries,List.getElem_toArray])
      table[q.val] (by exact (buckets_spec keys 0 q).symm) (fun i => links[i]?)
      (fun i => (List.getElem?_toArray (xs := candidates.val) (i := i)).symm)) (List.finRange entries.length)
  return ⟨candidates.val,by with_reducible exact candidates.property,result⟩

end QleisliKernel.Qirf.RuntimeArmDutyCoverage
