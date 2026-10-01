import QleisliKernel.Hierarchical.NodeTyping

/-! Structural checking of actual meaning and encoding nodes.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
Pure headers, finite dimensions and zero-scratch shape are necessary conditions,
not unitary proofs, entry evidence, finite reconstruction or semantic equations. -/

namespace QleisliKernel.Hierarchical.ContractTyping
open Artifact
open NodeTyping (quantumOnly append disjointFrames closed controlledInterface)

/-- Instruments cannot be operands of the pure meaning constructors. -/
def pureMeaning (meaning : Meaning) : Bool :=
  quantumOnly meaning.interface && match meaning.body with
  | .qpeInstrument _ _ _ => false
  | _ => true

def onePort (side : Side) (basis : Basis) : Bool :=
  side.classical.isEmpty && side.quantum.size == 1 &&
    (side.quantum[0]?.map (fun p => p.basis == basis)).getD false

def meaningSequence (artifact : Artifact) (children : Array Nat) : Option Interface := do
  let firstIndex ← children[0]?
  let first ← artifact.meanings[firstIndex]?
  if !pureMeaning first then none else do
    let output ← children.toList.drop 1 |>.foldlM (fun state index => do
      let child ← artifact.meanings[index]?
      if !pureMeaning child || state != child.interface.inputs then none
      else some child.interface.outputs) first.interface.outputs
    return ⟨first.interface.inputs, output⟩

def qpeBoundary (artifact : Artifact) (meaning : Meaning) (n m provider : Nat) : Bool :=
  (do
    let u ← artifact.meanings[provider]?
    let result : ClassicalPort ← meaning.interface.outputs.classical[0]?
    return pureMeaning u && u.interface.inputs == u.interface.outputs &&
      onePort u.interface.inputs #[Layout.TypeAtom.bits n] &&
      meaning.interface.inputs == u.interface.inputs &&
      meaning.interface.outputs.quantum == u.interface.outputs.quantum &&
      meaning.interface.outputs.classical.size == 1 && result.basis == #[Layout.TypeAtom.bits m]).getD false

def meaningConditions (artifact : Artifact) (meaning : Meaning) : Bool :=
  meaning.interface.valid && meaning.body.bounded && match meaning.body with
  | .qpeInstrument n m provider => qpeBoundary artifact meaning n m provider
  | _ => quantumOnly meaning.interface && match meaning.body with
    | .identity => meaning.interface.inputs == meaning.interface.outputs
    | .finite _ => Ports.wireCount meaning.interface.inputs ≤ 6 &&
      Ports.wireCount meaning.interface.outputs ≤ 6
    | .sequence children => meaningSequence artifact children == some meaning.interface
    | .tensor left right =>
      (do
        let a ← artifact.meanings[left]?
        let b ← artifact.meanings[right]?
        return pureMeaning a && pureMeaning b && disjointFrames a.interface b.interface &&
          meaning.interface == (⟨append a.interface.inputs b.interface.inputs,
            append a.interface.outputs b.interface.outputs⟩ : Interface)).getD false
    | .inverse child =>
      (do
        let u ← artifact.meanings[child]?
        return pureMeaning u && Ports.wireCount u.interface.inputs == Ports.wireCount u.interface.outputs &&
          meaning.interface == (⟨u.interface.outputs,u.interface.inputs⟩ : Interface)).getD false
    | .control child _ =>
      (do
        let u ← artifact.meanings[child]?
        return pureMeaning u && controlledInterface meaning.interface u.interface).getD false
    | .power child _ =>
      (do
        let u ← artifact.meanings[child]?
        return pureMeaning u && u.interface.inputs == u.interface.outputs &&
          meaning.interface == u.interface).getD false
    | .rewire permutation => Ports.shapeValid meaning.interface.inputs meaning.interface.outputs permutation
    | .structural operation => Structural.valid operation meaning.interface
    | .phase _ _ => meaning.interface.inputs == meaning.interface.outputs &&
      onePort meaning.interface.inputs #[.bit]
    | .qft width => meaning.interface.inputs == meaning.interface.outputs &&
      onePort meaning.interface.inputs #[.bits width]
    | .qpeInstrument _ _ _ => false

def encodingInterface (encoding : Encoding) : Interface := ⟨encoding.logical,encoding.physical⟩

/-- Logical owners are an exact prefix. All additional private owners, including
zero-width ones, remain represented; valid physical sides ensure freshness. -/
def zeroScratch (artifact : Artifact) (encoding : Encoding) (bits compute : Nat) : Bool :=
  (do
    let c ← artifact.definitions[compute]?
    let logical := encoding.logical
    let physical := encoding.physical
    return quantumOnly (encodingInterface encoding) && closed c &&
      c.interface.inputs == physical && logical.quantum.size ≤ physical.quantum.size &&
      physical.quantum.extract 0 logical.quantum.size == logical.quantum &&
      Ports.wireCount ⟨physical.quantum.extract logical.quantum.size physical.quantum.size,#[]⟩ == bits).getD false

def encodingConditions (artifact : Artifact) (encoding : Encoding) : Bool :=
  (encodingInterface encoding).valid && encoding.body.bounded && match encoding.body with
  | .identity => encoding.logical == encoding.physical
  | .tensor left right =>
    (do
      let a ← artifact.encodings[left]?
      let b ← artifact.encodings[right]?
      return disjointFrames (encodingInterface a) (encodingInterface b) &&
        encoding.logical == append a.logical b.logical && encoding.physical == append a.physical b.physical).getD false
  | .rewire child permutation =>
    (do
      let e ← artifact.encodings[child]?
      return encoding.logical == e.logical && Ports.shapeValid e.physical encoding.physical permutation).getD false
  | .zeroScratch bits compute => zeroScratch artifact encoding bits compute

/-- These private predicates omit only validity already established on the
same immutable artifact by preparation. Full maps, freshness and shape remain. -/
private def portsAfterHeaders (source destination : Side) (map : PortMap) : Bool :=
  Layout.structureValid (Ports.layout source destination map) (Ports.witness source map) &&
    decide (Ports.ClassicalMatch source destination map)

private theorem portsAfterHeaders_eq (source destination : Side) (map : PortMap)
    (before : sideValid source = true) (after : sideValid destination = true) :
    portsAfterHeaders source destination map = Ports.shapeValid source destination map := by
  simp [portsAfterHeaders, Ports.shapeValid, before, after]

private def structureAfterHeaders (operation : StructuralOp) (interface : Interface) : Bool :=
  operation.bounded && interface.inputs.classical.isEmpty && interface.outputs.classical.isEmpty &&
    Structural.fresh interface && Structural.shape operation interface &&
    decide (Layout.Permutation (wires interface.inputs).size
      (Structural.axisMap interface) (Structural.inverseAxes interface))

private theorem structureAfterHeaders_eq (operation : StructuralOp) (interface : Interface)
    (header : interface.valid = true) :
    structureAfterHeaders operation interface = Structural.valid operation interface := by
  simp [structureAfterHeaders, Structural.valid, header]

private def meaningAfterHeaders (artifact : Artifact) (meaning : Meaning) : Bool :=
  meaning.body.bounded && match meaning.body with
  | .qpeInstrument n m provider => qpeBoundary artifact meaning n m provider
  | _ => quantumOnly meaning.interface && match meaning.body with
    | .identity => meaning.interface.inputs == meaning.interface.outputs
    | .finite _ => Ports.wireCount meaning.interface.inputs ≤ 6 &&
      Ports.wireCount meaning.interface.outputs ≤ 6
    | .sequence children => meaningSequence artifact children == some meaning.interface
    | .tensor left right =>
      (do
        let a ← artifact.meanings[left]?
        let b ← artifact.meanings[right]?
        return pureMeaning a && pureMeaning b && disjointFrames a.interface b.interface &&
          meaning.interface == (⟨append a.interface.inputs b.interface.inputs,
            append a.interface.outputs b.interface.outputs⟩ : Interface)).getD false
    | .inverse child =>
      (do
        let u ← artifact.meanings[child]?
        return pureMeaning u && Ports.wireCount u.interface.inputs == Ports.wireCount u.interface.outputs &&
          meaning.interface == (⟨u.interface.outputs,u.interface.inputs⟩ : Interface)).getD false
    | .control child _ =>
      (do
        let u ← artifact.meanings[child]?
        return pureMeaning u && controlledInterface meaning.interface u.interface).getD false
    | .power child _ =>
      (do
        let u ← artifact.meanings[child]?
        return pureMeaning u && u.interface.inputs == u.interface.outputs &&
          meaning.interface == u.interface).getD false
    | .rewire permutation => portsAfterHeaders meaning.interface.inputs meaning.interface.outputs permutation
    | .structural operation => structureAfterHeaders operation meaning.interface
    | .phase _ _ => meaning.interface.inputs == meaning.interface.outputs &&
      onePort meaning.interface.inputs #[.bit]
    | .qft width => meaning.interface.inputs == meaning.interface.outputs &&
      onePort meaning.interface.inputs #[.bits width]
    | .qpeInstrument _ _ _ => false

private def encodingAfterHeaders (artifact : Artifact) (encoding : Encoding) : Bool :=
  encoding.body.bounded && match encoding.body with
  | .identity => encoding.logical == encoding.physical
  | .tensor left right =>
    (do
      let a ← artifact.encodings[left]?
      let b ← artifact.encodings[right]?
      return disjointFrames (encodingInterface a) (encodingInterface b) &&
        encoding.logical == append a.logical b.logical && encoding.physical == append a.physical b.physical).getD false
  | .rewire child permutation =>
    (do
      let e ← artifact.encodings[child]?
      return encoding.logical == e.logical && portsAfterHeaders e.physical encoding.physical permutation).getD false
  | .zeroScratch bits compute => zeroScratch artifact encoding bits compute


private theorem meaningAfterHeaders_eq (artifact : Artifact) (meaning : Meaning)
    (header : meaning.interface.valid = true) :
    meaningAfterHeaders artifact meaning = meaningConditions artifact meaning := by
  have sides : sideValid meaning.interface.inputs = true ∧ sideValid meaning.interface.outputs = true := by
    simpa only [Interface.valid, Bool.and_eq_true] using header
  cases hb : meaning.body <;>
    simp only [meaningAfterHeaders, meaningConditions, hb, header, Bool.true_and]
  case rewire permutation => rw [portsAfterHeaders_eq _ _ _ sides.1 sides.2]
  case structural operation => rw [structureAfterHeaders_eq _ _ header]

private theorem encodingAfterHeaders_eq (artifact : Artifact) (headers : Headers artifact)
    (encoding : Encoding) (before : sideValid encoding.logical = true)
    (after : sideValid encoding.physical = true) :
    encodingAfterHeaders artifact encoding = encodingConditions artifact encoding := by
  have header : (encodingInterface encoding).valid = true := by
    simp [encodingInterface, Interface.valid, before, after]
  cases hb : encoding.body <;>
    simp only [encodingAfterHeaders, encodingConditions, hb, header, Bool.true_and]
  case rewire child permutation =>
    cases hc : artifact.encodings[child]? with
    | none => simp
    | some source =>
      simp only [bind, Option.bind, portsAfterHeaders_eq _ _ _ (headers.2.2 child source hc).2 after]


inductive Subject where
  | meaning (value : Meaning)
  | encoding (value : Encoding)
  deriving Repr

def subject (artifact : Artifact) (ref : Ref) : Option Subject := match ref.table with
  | .meaning => artifact.meanings[ref.index]?.map Subject.meaning
  | .encoding => artifact.encodings[ref.index]?.map Subject.encoding
  | _ => none

def Subject.interface : Subject → Interface
  | .meaning m => m.interface
  | .encoding e => encodingInterface e

def Subject.referenceCount : Subject → Nat
  | .meaning m => m.body.referenceCount
  | .encoding e => e.body.referenceCount

def Subject.bodyCharge : Subject → Nat
  | .meaning m => m.body.charge
  | .encoding e => e.body.charge

def Subject.references : Subject → Array Ref
  | .meaning m => m.body.references
  | .encoding e => e.body.references

def Subject.conditions (artifact : Artifact) : Subject → Bool
  | .meaning m => meaningConditions artifact m
  | .encoding e => encodingConditions artifact e

private def Subject.afterHeaders (artifact : Artifact) : Subject → Bool
  | .meaning m => meaningAfterHeaders artifact m
  | .encoding e => encodingAfterHeaders artifact e

private theorem subjectAfterHeaders_eq (artifact : Artifact) (headers : Headers artifact)
    (ref : Ref) (value : Subject) (found : subject artifact ref = some value) :
    value.afterHeaders artifact = value.conditions artifact := by
  cases ht : ref.table <;> simp only [subject, ht] at found
  case definition => contradiction
  case proof => contradiction
  case meaning =>
    cases hm : artifact.meanings[ref.index]? with
    | none => simp [hm] at found
    | some meaning =>
      have same : Subject.meaning meaning = value := by simpa [hm] using found
      subst value
      exact meaningAfterHeaders_eq artifact meaning (headers.2.1 ref.index meaning hm)
  case encoding =>
    cases he : artifact.encodings[ref.index]? with
    | none => simp [he] at found
    | some encoding =>
      have same : Subject.encoding encoding = value := by simpa [he] using found
      subst value
      exact encodingAfterHeaders_eq artifact headers encoding
        (headers.2.2 ref.index encoding he).1 (headers.2.2 ref.index encoding he).2

def Subject.capacity : Subject → Bool
  | .meaning m => match m.body with
    | .finite _ => Ports.wireCount m.interface.inputs ≤ 6 && Ports.wireCount m.interface.outputs ≤ 6
    | _ => true
  | .encoding _ => true

def Subject.headerCost (cost : Side → Nat) (artifact : Artifact) (value : Subject) : Nat :=
  cost value.interface.inputs + cost value.interface.outputs +
    value.references.foldl (fun sum ref => sum + 1 + NodeTyping.refCost cost artifact ref) 0

def Subject.mapsCost (artifact : Artifact) : Subject → Nat
  | .meaning m => match m.body with
    | .rewire permutation => Ports.workCharge m.interface.inputs m.interface.outputs permutation
    | .structural _ => Structural.workCharge m.interface
    | _ => 0
  | .encoding e => match e.body with
    | .rewire child permutation => (artifact.encodings[child]?.map
        (fun source => Ports.workCharge source.physical e.physical permutation)).getD 0
    | _ => 0

structure Checked where
  visits : Nat
  deriving Repr

private def fullCharge (artifact : Artifact) (value : Subject) : Nat :=
  let initial := 1 + value.referenceCount + value.bodyCharge + value.interface.scan
  let scan := initial + value.headerCost sideScan artifact
  scan + 16 * (1 + value.bodyCharge + value.headerCost sideCharge artifact) + value.mapsCost artifact

def check (artifact : Artifact) (ref : Ref) (remaining : Nat) : Except Error Checked :=
  if remaining > Limits.maxVisits then .error .limit else
  match subject artifact ref with
  | none => .error .invalidIr
  | some value =>
    let initial := 1 + value.referenceCount + value.bodyCharge + value.interface.scan
    if initial > remaining then .error .limit else
    let scan := initial + value.headerCost sideScan artifact
    if scan > remaining then .error .limit else
    let charge := fullCharge artifact value
    if charge > remaining then .error .limit else
    if !value.capacity then .error .limit else
    if !value.conditions artifact then .error .invalidIr else .ok ⟨charge⟩

theorem check_conditions (artifact : Artifact) (ref : Ref) (remaining : Nat) (checked : Checked)
    (accepted : check artifact ref remaining = .ok checked) :
    checked.visits ≤ remaining ∧ remaining ≤ 2000000 ∧
    ∃ value, subject artifact ref = some value ∧ value.conditions artifact = true := by
  unfold check at accepted
  split at accepted
  next invalid => contradiction
  next limit =>
    cases hv : subject artifact ref with
    | none => simp [hv] at accepted
    | some value =>
      simp only [hv] at accepted
      split at accepted
      next invalid => contradiction
      next initial =>
        split at accepted
        next invalid => contradiction
        next scanned =>
          split at accepted
          next invalid => contradiction
          next charged =>
            split at accepted
            next invalid => contradiction
            next capacity =>
              split at accepted
              next invalid => contradiction
              next valid =>
                cases Except.ok.inj accepted
                exact ⟨Nat.le_of_not_gt charged, Nat.le_of_not_gt limit, value, rfl,
                  by simpa using valid⟩

def step (artifact : Artifact) (used : Nat) (ref : Ref) : Except Failure Nat :=
  match check artifact ref (Limits.maxVisits - used) with
  | .error kind => .error ⟨kind, some ref⟩
  | .ok checked =>
    if used + checked.visits > Limits.maxVisits then .error ⟨.limit,some ref⟩
    else .ok (used + checked.visits)

def scan (artifact : Artifact) (refs : List Ref) (used : Nat) : Except Failure Nat :=
  refs.foldlM (step artifact) used

theorem step_conditions (artifact : Artifact) (used total : Nat) (ref : Ref)
    (accepted : step artifact used ref = .ok total) :
    used ≤ total ∧ total ≤ 2000000 ∧
    ∃ value, subject artifact ref = some value ∧ value.conditions artifact = true := by
  unfold step at accepted
  cases hc : check artifact ref (2000000 - used) with
  | error failure => simp [hc] at accepted
  | ok checked =>
    simp only [hc] at accepted
    split at accepted
    next invalid => contradiction
    next bound =>
      cases Except.ok.inj accepted
      exact ⟨Nat.le_add_right _ _, Nat.le_of_not_gt bound,
        (check_conditions artifact ref _ checked hc).2.2⟩

theorem scan_conditions (artifact : Artifact) (refs : List Ref) (used total : Nat)
    (bounded : used ≤ 2000000) (accepted : scan artifact refs used = .ok total) :
    used ≤ total ∧ total ≤ 2000000 ∧ ∀ ref ∈ refs,
      ∃ value, subject artifact ref = some value ∧ value.conditions artifact = true := by
  induction refs generalizing used with
  | nil =>
    have same : used = total := by simpa [scan, pure, Except.pure] using accepted
    subst total
    exact ⟨Nat.le_refl _, bounded, by simp⟩
  | cons ref rest ih =>
    cases hs : step artifact used ref with
    | error failure => simp [scan, hs, bind, Except.bind] at accepted
    | ok next =>
      have one := step_conditions artifact used next ref hs
      have tail : scan artifact rest next = .ok total := by simpa [scan, hs] using accepted
      have all := ih next one.2.1 tail
      refine ⟨Nat.le_trans one.1 all.1, all.2.1, ?_⟩
      intro entry member
      rcases List.mem_cons.mp member with equal | following
      · subst entry; exact one.2.2
      · exact all.2.2 entry following

def subjects (artifact : Artifact) : List Ref :=
  (List.range artifact.meanings.size).map (⟨.meaning,·⟩) ++
    (List.range artifact.encodings.size).map (⟨.encoding,·⟩)

structure Typed where
  nodes : NodeTyping.Typed
  totalVisits : Nat
  deriving Repr

/- Reuse only actual node typing from the same checkAll invocation. A matching
   slot is a lookup hint, not evidence: complete interfaces and bodies must
   agree. Standalone check/scan retain their original independent contracts. -/
private def mirrored (definition : Definition) (meaning : Meaning) : Bool :=
  decide (definition.interface = meaning.interface) && quantumOnly meaning.interface &&
    match definition.body, meaning.body with
    | .rewire first, .rewire second => decide (first = second)
    | .structural first, .structural second => decide (first = second)
    | _, _ => false

private theorem mirrored_sound (artifact : Artifact) (definition : Definition) (meaning : Meaning)
    (typed : NodeTyping.conditions artifact definition = true)
    (same : mirrored definition meaning = true) : meaningConditions artifact meaning = true := by
  cases hd : definition.body <;> cases hm : meaning.body <;>
    simp only [mirrored,hd,hm,Bool.and_false,Bool.false_eq_true] at same
  all_goals
    simp only [Bool.and_eq_true,decide_eq_true_eq] at same
    obtain ⟨⟨header,pure⟩,body⟩ := same
    subst body
    simp [NodeTyping.conditions,meaningConditions,hd,hm,header,
      Body.bounded,MeaningBody.bounded,pure] at typed ⊢
    exact ⟨typed.1,typed.2.2⟩

private def equalityFields (side : Side) : Nat :=
  1 + side.quantum.foldl (fun n p => n + 3 + 2*p.basis.size + p.axes.size) 0 +
    side.classical.foldl (fun n p => n + 2 + 2*p.basis.size) 0

/-- The matching row's header was checked by actual preparation. Retain
linear equality work and every capacity, map and semantic-shape predicate. -/
private def preparedCharge (original : Nat) (interface : Interface) : Nat :=
  min original (original - 16 * interface.charge +
    16 * (equalityFields interface.inputs + equalityFields interface.outputs))

private theorem preparedCharge_le (original : Nat) (interface : Interface) :
    preparedCharge original interface ≤ original := Nat.min_le_left _ _

private def preparedCheck (artifact : Artifact) (ref : Ref) (remaining : Nat) : Except Error Checked :=
  if remaining > Limits.maxVisits then .error .limit else
  match subject artifact ref with
  | none => .error .invalidIr
  | some value =>
    let initial := 1 + value.referenceCount + value.bodyCharge + value.interface.scan
    if initial > remaining then .error .limit else
    let scan := initial + value.headerCost sideScan artifact
    if scan > remaining then .error .limit else
    let original := fullCharge artifact value
    let charge := preparedCharge original value.interface
    if charge > remaining then .error .limit else
    if !value.capacity then .error .limit else
    if !value.afterHeaders artifact then .error .invalidIr else .ok ⟨charge⟩

private theorem preparedCheck_conditions (artifact : Artifact) (headers : Headers artifact)
    (ref : Ref) (remaining : Nat) (checked : Checked)
    (accepted : preparedCheck artifact ref remaining = .ok checked) :
    checked.visits ≤ remaining ∧ remaining ≤ 2000000 ∧
    ∃ value, subject artifact ref = some value ∧ value.conditions artifact = true := by
  unfold preparedCheck at accepted
  split at accepted
  next invalid => contradiction
  next limit =>
    cases hv : subject artifact ref with
    | none => simp [hv] at accepted
    | some value =>
      simp only [hv] at accepted
      split at accepted
      next invalid => contradiction
      next initial =>
        split at accepted
        next invalid => contradiction
        next scanned =>
          split at accepted
          next invalid => contradiction
          next charged =>
            split at accepted
            next invalid => contradiction
            next capacity =>
              split at accepted
              next invalid => contradiction
              next valid =>
                cases Except.ok.inj accepted
                refine ⟨Nat.le_of_not_gt charged, Nat.le_of_not_gt limit, value, rfl, ?_⟩
                have checked : value.afterHeaders artifact = true := by simpa using valid
                simpa only [subjectAfterHeaders_eq artifact headers ref value hv] using checked

/-- Read only array lengths before comparing full fields. A failed comparison
reads at most the meaning's matching prefix; prepared fallback retains its
linear field allowance. Only equal headers incur the two-header cost scan.
Success uses no permutation search or repeated type validation. -/
private def reused (artifact : Artifact) (ref : Ref) (remaining : Nat) : Option Nat := do
  let .meaning := ref.table | none
  let definition ← artifact.definitions[ref.index]?
  let meaning ← artifact.meanings[ref.index]?
  let scan := 32 + definition.interface.scan + meaning.interface.scan +
    definition.body.charge + meaning.body.charge
  if scan > remaining then none else do
    if !mirrored definition meaning then none else do
    let cost := scan + 8 * (1 + equalityFields definition.interface.inputs +
      equalityFields definition.interface.outputs + equalityFields meaning.interface.inputs +
      equalityFields meaning.interface.outputs + definition.body.charge + meaning.body.charge)
    if cost > remaining then none else
    -- Never spend more than the existing path: old accepted budget boundaries
    -- must not become rejections after this optimization.
    if cost > fullCharge artifact (.meaning meaning) then none else some cost

private def checkTyped (artifact : Artifact) (ref : Ref) (remaining : Nat) : Except Error Checked :=
  if remaining > Limits.maxVisits then .error .limit else
  match reused artifact ref remaining with
  | some cost => .ok ⟨cost⟩
  | none => preparedCheck artifact ref remaining

private def NodeContext (artifact : Artifact) : Prop :=
  ∀ (i : Nat) (definition : Definition), artifact.definitions[i]? = some definition →
    NodeTyping.conditions artifact definition = true

private theorem reused_sound (artifact : Artifact) (context : NodeContext artifact)
    (ref : Ref) (remaining cost : Nat) (accepted : reused artifact ref remaining = some cost) :
    cost ≤ remaining ∧ ∃ value, subject artifact ref = some value ∧ value.conditions artifact = true := by
  cases ht : ref.table <;> try { simp [reused,ht] at accepted }
  cases hd : artifact.definitions[ref.index]? with
  | none => simp [reused,ht,hd] at accepted
  | some definition =>
    cases hm : artifact.meanings[ref.index]? with
    | none => simp [reused,ht,hd,hm] at accepted
    | some meaning =>
      simp only [reused,ht,hd,hm,bind,Option.bind] at accepted
      split at accepted
      next exceeded => contradiction
      next scanned =>
        split at accepted
        next failed => contradiction
        next valid =>
          split at accepted
          next expensive => contradiction
          next bounded =>
            split at accepted
            next expensive => contradiction
            next cheaper =>
              cases Option.some.inj accepted
              refine ⟨by omega,.meaning meaning,by simp [subject,ht,hm],?_⟩
              exact mirrored_sound artifact definition meaning (context _ _ hd) (by simpa using valid)

private theorem checkTyped_conditions (artifact : Artifact) (headers : Headers artifact) (context : NodeContext artifact)
    (ref : Ref) (remaining : Nat) (checked : Checked)
    (accepted : checkTyped artifact ref remaining = .ok checked) :
    checked.visits ≤ remaining ∧ remaining ≤ 2000000 ∧
    ∃ value, subject artifact ref = some value ∧ value.conditions artifact = true := by
  unfold checkTyped at accepted
  split at accepted
  next exceeded => contradiction
  next bounded =>
    cases hr : reused artifact ref remaining with
    | none => exact preparedCheck_conditions artifact headers ref remaining checked (by simpa [hr] using accepted)
    | some cost =>
      have same : (⟨cost⟩ : Checked) = checked := by simpa [hr] using accepted
      subst checked
      obtain ⟨bound,valid⟩ := reused_sound artifact context ref remaining cost hr
      exact ⟨bound,Nat.le_of_not_gt bounded,valid⟩

private def stepTyped (artifact : Artifact) (used : Nat) (ref : Ref) : Except Failure Nat :=
  match checkTyped artifact ref (Limits.maxVisits-used) with
  | .error kind => .error ⟨kind,some ref⟩
  | .ok checked =>
    if used + checked.visits > Limits.maxVisits then .error ⟨.limit,some ref⟩
    else .ok (used + checked.visits)

private def scanTyped (artifact : Artifact) (refs : List Ref) (used : Nat) : Except Failure Nat :=
  refs.foldlM (stepTyped artifact) used

private theorem scanTyped_conditions (artifact : Artifact) (headers : Headers artifact) (context : NodeContext artifact)
    (refs : List Ref) (used total : Nat) (bounded : used ≤ 2000000)
    (accepted : scanTyped artifact refs used = .ok total) :
    used ≤ total ∧ total ≤ 2000000 ∧ ∀ ref ∈ refs,
      ∃ value, subject artifact ref = some value ∧ value.conditions artifact = true := by
  induction refs generalizing used with
  | nil =>
    have same : used = total := by simpa [scanTyped,pure,Except.pure] using accepted
    subst total
    exact ⟨Nat.le_refl _,bounded,by simp⟩
  | cons ref rest ih =>
    cases hc : checkTyped artifact ref (2000000-used) with
    | error e => simp [scanTyped,stepTyped,hc,bind,Except.bind] at accepted
    | ok checked =>
      have facts := checkTyped_conditions artifact headers context ref _ checked hc
      by_cases exceeded : used + checked.visits > 2000000
      · simp [scanTyped,stepTyped,hc,exceeded,bind,Except.bind] at accepted
      · have tail : scanTyped artifact rest (used+checked.visits) = .ok total := by
          simpa [scanTyped,stepTyped,hc,exceeded] using accepted
        have all := ih _ (by omega) tail
        refine ⟨by omega,all.2.1,?_⟩
        intro entry member
        rcases List.mem_cons.mp member with equal | following
        · subst entry; exact facts.2.2
        · exact all.2.2 entry following

/-- Every shared meaning/encoding is checked once, without a dense evaluator.
The later semantic checker must still validate all finite and rule obligations. -/
def checkAll (artifact : Artifact) (order : Array Nat) : Except Failure Typed :=
  match NodeTyping.checkAll artifact order with
  | .error failure => .error failure
  | .ok nodes =>
    let start := nodes.totalVisits + 6 * (artifact.meanings.size + artifact.encodings.size)
    if start > Limits.maxVisits then .error ⟨.limit,none⟩ else
      match scanTyped artifact (subjects artifact) start with
      | .error failure => .error failure
      | .ok total => .ok ⟨nodes,total⟩

theorem checkAll_conditions (artifact : Artifact) (order : Array Nat) (typed : Typed)
    (accepted : checkAll artifact order = .ok typed) :
    NodeTyping.checkAll artifact order = .ok typed.nodes ∧
    typed.nodes.totalVisits ≤ typed.totalVisits ∧ typed.totalVisits ≤ 2000000 ∧
    ∀ ref ∈ subjects artifact,
      ∃ value, subject artifact ref = some value ∧ value.conditions artifact = true := by
  unfold checkAll at accepted
  cases hp : NodeTyping.checkAll artifact order with
  | error failure => simp [hp] at accepted
  | ok nodes =>
    simp only [hp] at accepted
    split at accepted
    next invalid => contradiction
    next bounded =>
      cases hs : scanTyped artifact (subjects artifact)
          (nodes.totalVisits + 6 * (artifact.meanings.size + artifact.encodings.size)) with
      | error failure => simp [hs] at accepted
      | ok total =>
        simp only [hs] at accepted
        cases Except.ok.inj accepted
        have context : NodeContext artifact := by
          intro i d found
          obtain ⟨other,otherFound,valid⟩ := (NodeTyping.checkAll_conditions artifact order nodes hp).2.2.2
            i (Array.getElem?_eq_some_iff.mp found).1
          simpa [Option.some.inj (otherFound.symm.trans found)] using valid
        have headers := prepare_headers artifact order nodes.prepared
          (NodeTyping.checkAll_conditions artifact order nodes hp).1
        have h := scanTyped_conditions artifact headers context _ _ total (Nat.le_of_not_gt bounded) hs
        exact ⟨rfl, Nat.le_trans (Nat.le_add_right _ _) h.1, h.2⟩

theorem checkAll_meaning (artifact : Artifact) (order : Array Nat) (typed : Typed) (index : Nat)
    (accepted : checkAll artifact order = .ok typed) (inside : index < artifact.meanings.size) :
    ∃ meaning, artifact.meanings[index]? = some meaning ∧ meaningConditions artifact meaning = true := by
  have member : (⟨.meaning,index⟩ : Ref) ∈ subjects artifact :=
    List.mem_append_left _ (List.mem_map.mpr ⟨index, List.mem_range.mpr inside, rfl⟩)
  obtain ⟨value, found, valid⟩ := (checkAll_conditions artifact order typed accepted).2.2.2 _ member
  cases hm : artifact.meanings[index]? with
  | none => simp [subject, hm] at found
  | some meaning =>
    have same : Subject.meaning meaning = value := by simpa [subject, hm] using found
    cases same
    exact ⟨meaning, rfl, valid⟩

theorem checkAll_encoding (artifact : Artifact) (order : Array Nat) (typed : Typed) (index : Nat)
    (accepted : checkAll artifact order = .ok typed) (inside : index < artifact.encodings.size) :
    ∃ encoding, artifact.encodings[index]? = some encoding ∧ encodingConditions artifact encoding = true := by
  have member : (⟨.encoding,index⟩ : Ref) ∈ subjects artifact :=
    List.mem_append_right _ (List.mem_map.mpr ⟨index, List.mem_range.mpr inside, rfl⟩)
  obtain ⟨value, found, valid⟩ := (checkAll_conditions artifact order typed accepted).2.2.2 _ member
  cases he : artifact.encodings[index]? with
  | none => simp [subject, he] at found
  | some encoding =>
    have same : Subject.encoding encoding = value := by simpa [subject, he] using found
    cases same
    exact ⟨encoding, rfl, valid⟩

end QleisliKernel.Hierarchical.ContractTyping
