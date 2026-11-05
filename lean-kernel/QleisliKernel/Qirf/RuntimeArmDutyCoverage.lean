import QleisliKernel.Qirf.RuntimeBodyOperationTraversal
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

/-- All written-arm list positions naming this exact pending queue position. -/
def occurrences (body : Traversed prepared order runtime) (q : Position prepared) : List Nat :=
  references (body.writtenArms.map (·.queueIndex)) 0 q

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

private def single (body : Traversed prepared order runtime) (q : Position prepared)
    (lookup : Nat → Option (ArmLink body.checked)) : List Nat → Bool
  | [index] => match lookup index with
    | none => false
    | some link => decide (link.queueIndex = q ∧ positive body link = true)
  | _ => false

/-- Independent list specification. Duplicate links stay outstanding even
when exactly one copy carries positive evidence. -/
def covered (body : Traversed prepared order runtime) (q : Position prepared) : Bool :=
  single body q (fun i => body.writtenArms[i]?) (occurrences body q)

def remaining (body : Traversed prepared order runtime) (q : Position prepared) : Bool :=
  prepared.source.pending.entries[q.val].unconsumed && !covered body q

structure Discharge (body : Traversed prepared order runtime) (q : Position prepared) where
  index : Nat
  link : ArmLink body.checked
  atWritten : body.writtenArms[index]? = some link
  queue : link.queueIndex = q
  required : prepared.source.pending.entries[q.val].unconsumed = true
  unique : occurrences body q = [index]
  proved : Positive body link

private inductive Decision (body : Traversed prepared order runtime) (q : Position prepared) where
  | skipped (already : prepared.source.pending.entries[q.val].unconsumed = false)
  | residual (required : prepared.source.pending.entries[q.val].unconsumed = true) (openDuty : covered body q = false)
  | consumed (witness : Discharge body q) (closed : covered body q = true)

private def classify (body : Traversed prepared order runtime) (q : Position prepared)
    (required : Bool) (need : required = prepared.source.pending.entries[q.val].unconsumed)
    (members : List Nat) (same : occurrences body q = members)
    (lookup : Nat → Option (ArmLink body.checked)) (original : ∀ i,body.writtenArms[i]? = lookup i)
    (test : (link : ArmLink body.checked) → {value : Bool // value = positive body link}) :
    Decision body q := by
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
        | some link =>
          have selected := (original i).trans atIndex
          let result := test link
          if proof : link.queueIndex = q ∧ result.val = true then
            have yes : link.queueIndex = q ∧ positive body link = true := ⟨proof.1,result.property.symm.trans proof.2⟩
            exact .consumed ⟨i,link,selected,yes.1,need.symm,same,positive_sound body link yes.2⟩
              (by simp [covered,same,single,selected,yes])
          else
            have no : ¬ (link.queueIndex = q ∧ positive body link = true) := by simpa only [result.property] using proof
            exact .residual need.symm (by simp [covered,same,single,selected,no])

structure Report (body : Traversed prepared order runtime) (indices : List (Position prepared)) where
  residual : List (Position prepared)
  consumed : List ((q : Position prepared) × Discharge body q)
  exactResidual : residual = indices.filter (remaining body)
  exactConsumed : consumed.map (·.1) =
    indices.filter (fun q => prepared.source.pending.entries[q.val].unconsumed && covered body q)

private def collect (body : Traversed prepared order runtime) (row : (q : Position prepared) → Decision body q) :
    (indices : List (Position prepared)) → Report body indices :=
  foldTotal (Report body) ⟨[],[],rfl,rfl⟩ (fun q _ later =>
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

/-- Reconcile the entire original queue under the same checked body. No
reader of this report changes the initial source assessment or issues a handle. -/
def read (body : Traversed prepared order runtime) :
    WorkM (Report body (List.finRange prepared.source.pending.entries.length)) := do
  let entries := prepared.source.pending.entries
  let arms := body.writtenArms
  exactWork (Exact.charge (32*(entries.length+arms.length+body.checked.receipts.length+1)))
  let values := entries.toArray
  let links := arms.toArray
  let receipts := body.checked.receipts.toArray
  let table := buckets (arms.map (·.queueIndex)) 0
  let test := fun (link : ArmLink body.checked) =>
    indexedPositive body link
      (receipts[link.receiptIndex.val]'(by simpa only [receipts,List.size_toArray] using link.receiptIndex.isLt))
      (values[link.queueIndex.val]'(by simpa only [values,entries,List.size_toArray] using link.queueIndex.isLt))
      (by simp only [receipts,List.getElem_toArray,Fin.getElem_fin]) (by simp only [values,entries,List.getElem_toArray,Fin.getElem_fin])
  return collect body (fun q =>
    let entry := values[q.val]'(by simpa only [values,entries,List.size_toArray] using q.isLt)
    classify body q entry.unconsumed (by simp only [entry,values,entries,List.getElem_toArray])
      table[q.val] (by exact (buckets_spec (arms.map (·.queueIndex)) 0 q).symm) (fun i => links[i]?)
      (fun i => (List.getElem?_toArray (xs := arms) (i := i)).symm) test) (List.finRange entries.length)

end QleisliKernel.Qirf.RuntimeArmDutyCoverage
