import QleisliKernel.Hierarchical.Structural

/-! Local typing of actual hierarchical definition bodies.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
Finite leaves and compute/uncompute equations remain explicit obligations of
the semantic pass. This module issues no semantic evidence. -/

namespace QleisliKernel.Hierarchical.NodeTyping
open Artifact

/-- Effects are inferred from actual children, never weakened by a declaration. -/
def join (first second : Effect) : Effect := match first, second with
  | .observe, _ | _, .observe => .observe
  | .iso, _ | _, .iso => .iso
  | _, _ => .unitary

def quantumOnly (interface : Interface) : Bool :=
  interface.inputs.classical.isEmpty && interface.outputs.classical.isEmpty

def closed (definition : Definition) : Bool :=
  definition.effect == Effect.unitary && quantumOnly definition.interface &&
    definition.interface.inputs == definition.interface.outputs

def append (first second : Side) : Side :=
  ⟨first.quantum ++ second.quantum, first.classical ++ second.classical⟩

def ownerNames (side : Side) : Array Nat := side.quantum.map QuantumPort.owner

def valueNames (side : Side) : Array Nat := side.classical.map ClassicalPort.value

def disjoint (first second : Array Nat) : Bool := first.all (fun n => !second.contains n)

def disjointFrames (first second : Interface) : Bool :=
  disjoint (ownerNames first.inputs ++ ownerNames first.outputs)
    (ownerNames second.inputs ++ ownerNames second.outputs) &&
  disjoint (wires first.inputs ++ wires first.outputs) (wires second.inputs ++ wires second.outputs) &&
  disjoint (valueNames first.inputs ++ valueNames first.outputs)
    (valueNames second.inputs ++ valueNames second.outputs)

/-- Each pair is (callee identity, caller identity); domains stay separate. -/
def Consistent (pairs : Array (Nat × Nat)) : Prop :=
  ∀ i j : Fin pairs.size, pairs[i].1 = pairs[j].1 ↔ pairs[i].2 = pairs[j].2

instance (pairs : Array (Nat × Nat)) : Decidable (Consistent pairs) := by
  unfold Consistent
  infer_instance

def pairs (source destination map : Array Nat) : Option (Array (Nat × Nat)) :=
  (Array.range destination.size).mapM fun i => do
    let dst ← destination[i]?
    let position ← map[i]?
    let src ← source[position]?
    return (dst, src)

def renamed (caller callee : Interface) (input output : PortMap) : Bool :=
  (do
    let qi ← pairs (ownerNames caller.inputs) (ownerNames callee.inputs) input.owners
    let qo ← pairs (ownerNames callee.outputs) (ownerNames caller.outputs) output.owners
    let wi ← pairs (wires caller.inputs) (wires callee.inputs) input.axes
    let wo ← pairs (wires callee.outputs) (wires caller.outputs) output.axes
    let ci ← pairs (valueNames caller.inputs) (valueNames callee.inputs) input.classical
    let co ← pairs (valueNames callee.outputs) (valueNames caller.outputs) output.classical
    return decide (Consistent (qi ++ qo.map Prod.swap) ∧
      Consistent (wi ++ wo.map Prod.swap) ∧ Consistent (ci ++ co.map Prod.swap))).getD false

def sequence (artifact : Artifact) (children : Array Nat) : Option (Interface × Effect) := do
  let firstIndex ← children[0]?
  let first ← artifact.definitions[firstIndex]?
  let result ← children.toList.drop 1 |>.foldlM (fun state index => do
    let child ← artifact.definitions[index]?
    if state.1 != child.interface.inputs then none else
      some (child.interface.outputs, join state.2 child.effect))
    (first.interface.outputs, first.effect)
  return (⟨first.interface.inputs, result.1⟩, result.2)

def controlledInterface (parent child : Interface) : Bool :=
  (do
    let control : QuantumPort ← parent.inputs.quantum[0]?
    return quantumOnly child &&
      child.inputs.quantum.map QuantumPort.basis == child.outputs.quantum.map QuantumPort.basis &&
      control.basis == #[Layout.TypeAtom.bit] && control.axes.size == 1 &&
      parent.inputs == append ⟨#[control],#[]⟩ child.inputs &&
      parent.outputs == append ⟨#[control],#[]⟩ child.outputs &&
      !(ownerNames child.inputs ++ ownerNames child.outputs).contains control.owner &&
      disjoint control.axes (wires child.inputs ++ wires child.outputs)).getD false

def controlled (parent child : Definition) : Bool :=
  parent.effect == Effect.unitary && child.effect == Effect.unitary &&
    controlledInterface parent.interface child.interface

def phase (definition : Definition) (target : Nat) : Bool :=
  definition.effect == Effect.unitary && definition.interface.inputs == definition.interface.outputs &&
    definition.interface.inputs.quantum.any (fun p => p.owner == target && p.basis == #[Layout.TypeAtom.bit])

def observe (definition : Definition) (input output : Nat) : Bool :=
  let before := definition.interface.inputs
  let after := definition.interface.outputs
  definition.effect == Effect.observe &&
    before.quantum.any (fun p => p.owner == input && p.basis == #[Layout.TypeAtom.bit]) &&
    after.classical.any (fun p => p.value == output && p.basis == #[Layout.TypeAtom.bit]) &&
    !(valueNames before).contains output &&
    after.quantum == before.quantum.filter (fun p => p.owner != input) &&
    before.classical == after.classical.filter (fun p => p.value != output)

def initializeZero (definition : Definition) (output : Nat) : Bool :=
  let before := definition.interface.inputs
  let after := definition.interface.outputs
  definition.effect == Effect.iso && !(ownerNames before).contains output &&
    after.quantum.any (fun p => p.owner == output && p.basis == #[Layout.TypeAtom.bit] &&
      disjoint p.axes (wires before)) &&
    before.quantum == after.quantum.filter (fun p => p.owner != output) &&
    before.classical == after.classical

def computed (artifact : Artifact) (definition : Definition) (compute useOp logical encoding : Nat) : Bool :=
  (do
    let c ← artifact.definitions[compute]?
    let w ← artifact.definitions[useOp]?
    let u ← artifact.meanings[logical]?
    let e ← artifact.encodings[encoding]?
    let .zeroScratch _ actualCompute := e.body | none
    return definition.effect == Effect.unitary && closed c && closed w && actualCompute == compute &&
      quantumOnly definition.interface && definition.interface.inputs == definition.interface.outputs &&
      definition.interface == u.interface && definition.interface.inputs == e.logical &&
      c.interface.outputs == e.physical && w.interface.inputs == e.physical).getD false

/-- Local structural conditions only. A leaf is deferred to the independently
reconstructed finite verifier; `computed` still needs its semantic premise. -/
def conditions (artifact : Artifact) (definition : Definition) : Bool :=
  definition.interface.valid && definition.body.bounded && match definition.body with
  | .leaf _ => true
  | .sequence children =>
    sequence artifact children == some (definition.interface, definition.effect)
  | .tensor left right =>
    (do
      let a ← artifact.definitions[left]?
      let b ← artifact.definitions[right]?
      return disjointFrames a.interface b.interface && definition.effect == join a.effect b.effect &&
        definition.interface == (⟨append a.interface.inputs b.interface.inputs,
          append a.interface.outputs b.interface.outputs⟩ : Interface)).getD false
  | .call child input output =>
    (do
      let callee ← artifact.definitions[child]?
      return definition.effect == callee.effect &&
        Ports.shapeValid definition.interface.inputs callee.interface.inputs input &&
        Ports.shapeValid callee.interface.outputs definition.interface.outputs output &&
        renamed definition.interface callee.interface input output).getD false
  | .repeatOp _ child =>
    (do
      let body ← artifact.definitions[child]?
      return closed body && definition.effect == Effect.unitary && definition.interface == body.interface).getD false
  | .inverse child =>
    (do
      let body ← artifact.definitions[child]?
      return definition.effect == Effect.unitary && body.effect == Effect.unitary && quantumOnly body.interface &&
        definition.interface == (⟨body.interface.outputs, body.interface.inputs⟩ : Interface)).getD false
  | .control child _ => (artifact.definitions[child]?.map (controlled definition)).getD false
  | .rewire map => definition.effect == Effect.unitary &&
    Ports.shapeValid definition.interface.inputs definition.interface.outputs map
  | .structural operation => definition.effect == Effect.unitary &&
    Structural.valid operation definition.interface
  | .dyadicPhase target _ _ => phase definition target
  | .computed c w u e => computed artifact definition c w u e
  | .observeZ input output => observe definition input output
  | .init0 output => initializeZero definition output

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

private def preparedConditions (artifact : Artifact) (definition : Definition) : Bool :=
  definition.body.bounded && match definition.body with
  | .leaf _ => true
  | .sequence children =>
    sequence artifact children == some (definition.interface, definition.effect)
  | .tensor left right =>
    (do
      let a ← artifact.definitions[left]?
      let b ← artifact.definitions[right]?
      return disjointFrames a.interface b.interface && definition.effect == join a.effect b.effect &&
        definition.interface == (⟨append a.interface.inputs b.interface.inputs,
          append a.interface.outputs b.interface.outputs⟩ : Interface)).getD false
  | .call child input output =>
    (do
      let callee ← artifact.definitions[child]?
      return definition.effect == callee.effect &&
        portsAfterHeaders definition.interface.inputs callee.interface.inputs input &&
        portsAfterHeaders callee.interface.outputs definition.interface.outputs output &&
        renamed definition.interface callee.interface input output).getD false
  | .repeatOp _ child =>
    (do
      let body ← artifact.definitions[child]?
      return closed body && definition.effect == Effect.unitary && definition.interface == body.interface).getD false
  | .inverse child =>
    (do
      let body ← artifact.definitions[child]?
      return definition.effect == Effect.unitary && body.effect == Effect.unitary && quantumOnly body.interface &&
        definition.interface == (⟨body.interface.outputs, body.interface.inputs⟩ : Interface)).getD false
  | .control child _ => (artifact.definitions[child]?.map (controlled definition)).getD false
  | .rewire map => definition.effect == Effect.unitary &&
    portsAfterHeaders definition.interface.inputs definition.interface.outputs map
  | .structural operation => definition.effect == Effect.unitary &&
    structureAfterHeaders operation definition.interface
  | .dyadicPhase target _ _ => phase definition target
  | .computed c w u e => computed artifact definition c w u e
  | .observeZ input output => observe definition input output
  | .init0 output => initializeZero definition output

private theorem preparedConditions_eq (artifact : Artifact) (headers : Headers artifact)
    (definition : Definition) (valid : definition.interface.valid = true) :
    preparedConditions artifact definition = conditions artifact definition := by
  have sides : sideValid definition.interface.inputs = true ∧
      sideValid definition.interface.outputs = true := by
    simpa only [Interface.valid, Bool.and_eq_true] using valid
  cases hb : definition.body <;>
    simp only [preparedConditions, conditions, hb, valid, Bool.true_and]
  case call child input output =>
    cases hc : artifact.definitions[child]? with
    | none => simp
    | some callee =>
      have other := headers.1 child callee hc
      have otherSides : sideValid callee.interface.inputs = true ∧
          sideValid callee.interface.outputs = true := by
        simpa only [Interface.valid, Bool.and_eq_true] using other
      simp only [bind, Option.bind, portsAfterHeaders_eq _ _ _ sides.1 otherSides.1,
        portsAfterHeaders_eq _ _ _ otherSides.2 sides.2]
  case rewire map => rw [portsAfterHeaders_eq _ _ _ sides.1 sides.2]
  case structural operation => rw [structureAfterHeaders_eq _ _ valid]

/-- Header cost includes every actual referenced definition/meaning/encoding,
including shared endpoints. Proof references cannot occur in a body. -/
def refCost (cost : Side → Nat) (artifact : Artifact) (ref : Ref) : Nat :=
  match ref.table with
  | .definition => (artifact.definitions[ref.index]?.map
      (fun d => cost d.interface.inputs + cost d.interface.outputs)).getD 0
  | .meaning => (artifact.meanings[ref.index]?.map
      (fun m => cost m.interface.inputs + cost m.interface.outputs)).getD 0
  | .encoding => (artifact.encodings[ref.index]?.map
      (fun e => cost e.logical + cost e.physical)).getD 0
  | .proof => 0

def headerCost (cost : Side → Nat) (artifact : Artifact) (definition : Definition) : Nat :=
  cost definition.interface.inputs + cost definition.interface.outputs +
    definition.body.references.foldl (fun sum ref => sum + 1 + refCost cost artifact ref) 0

def mapsCost (artifact : Artifact) (definition : Definition) : Nat :=
  match definition.body with
  | .call child input output =>
    (artifact.definitions[child]?.map (fun callee =>
      Ports.workCharge definition.interface.inputs callee.interface.inputs input +
      Ports.workCharge callee.interface.outputs definition.interface.outputs output)).getD 0
  | .rewire map => Ports.workCharge definition.interface.inputs definition.interface.outputs map
  | .structural _ => Structural.workCharge definition.interface
  | _ => 0

structure Checked where
  visits : Nat
  deriving Repr

/-- The caller must also check every child body and all semantic obligations.
No cache, body count or finite payload is trusted by this local check. -/
def check (artifact : Artifact) (index remaining : Nat) : Except Error Checked :=
  if remaining > Limits.maxVisits then .error .limit else
  match artifact.definitions[index]? with
  | none => .error .invalidIr
  | some definition =>
    let initial := 1 + definition.body.referenceCount + definition.body.charge + definition.interface.scan
    if initial > remaining then .error .limit else
    let scan := initial + headerCost sideScan artifact definition
    if scan > remaining then .error .limit else
    let charge := scan + 16 * (1 + definition.body.charge + headerCost sideCharge artifact definition) +
      mapsCost artifact definition
    if charge > remaining then .error .limit else
    if !conditions artifact definition then .error .invalidIr else .ok ⟨charge⟩

/-- Acceptance is about the actual indexed node, with a shared remaining budget. -/
theorem check_conditions (artifact : Artifact) (index remaining : Nat) (checked : Checked)
    (accepted : check artifact index remaining = .ok checked) :
    checked.visits ≤ remaining ∧ remaining ≤ 2000000 ∧
    ∃ definition, artifact.definitions[index]? = some definition ∧ conditions artifact definition = true := by
  unfold check at accepted
  split at accepted
  next invalid => contradiction
  next limit =>
    cases hd : artifact.definitions[index]? with
    | none => simp [hd] at accepted
    | some definition =>
      simp only [hd] at accepted
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
            next valid =>
              cases Except.ok.inj accepted
              exact ⟨Nat.le_of_not_gt charged, Nat.le_of_not_gt limit, definition, rfl,
                by simpa using valid⟩

/-- Linear own-header equality still occurs in body checks. Referenced
headers and map/freshness costs retain their original conservative charges. -/
private def equalityFields (side : Side) : Nat :=
  1 + side.quantum.foldl (fun n p => n + 3 + 2*p.basis.size + p.axes.size) 0 +
    side.classical.foldl (fun n p => n + 2 + 2*p.basis.size) 0

private def preparedCharge (original : Nat) (interface : Interface) : Nat :=
  min original (original - 16 * interface.charge +
    16 * (equalityFields interface.inputs + equalityFields interface.outputs))

private theorem preparedCharge_le (original : Nat) (interface : Interface) :
    preparedCharge original interface ≤ original := Nat.min_le_left _ _

private def preparedCheck (artifact : Artifact) (index remaining : Nat) : Except Error Checked :=
  if remaining > Limits.maxVisits then .error .limit else
  match artifact.definitions[index]? with
  | none => .error .invalidIr
  | some definition =>
    let initial := 1 + definition.body.referenceCount + definition.body.charge + definition.interface.scan
    if initial > remaining then .error .limit else
    let scan := initial + headerCost sideScan artifact definition
    if scan > remaining then .error .limit else
    let original := scan + 16 * (1 + definition.body.charge + headerCost sideCharge artifact definition) +
      mapsCost artifact definition
    let charge := preparedCharge original definition.interface
    if charge > remaining then .error .limit else
    if !preparedConditions artifact definition then .error .invalidIr else .ok ⟨charge⟩

private theorem preparedCheck_conditions (artifact : Artifact) (headers : Headers artifact)
    (index remaining : Nat) (checked : Checked)
    (accepted : preparedCheck artifact index remaining = .ok checked) :
    checked.visits ≤ remaining ∧ remaining ≤ 2000000 ∧
    ∃ definition, artifact.definitions[index]? = some definition ∧ conditions artifact definition = true := by
  unfold preparedCheck at accepted
  split at accepted
  next invalid => contradiction
  next limit =>
    cases hd : artifact.definitions[index]? with
    | none => simp [hd] at accepted
    | some definition =>
      simp only [hd] at accepted
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
            next valid =>
              cases Except.ok.inj accepted
              refine ⟨Nat.le_of_not_gt charged, Nat.le_of_not_gt limit, definition, rfl, ?_⟩
              have checked : preparedConditions artifact definition = true := by simpa using valid
              simpa only [preparedConditions_eq artifact headers definition (headers.1 index definition hd)] using checked

private def preparedStep (artifact : Artifact) (used index : Nat) : Except Failure Nat :=
  match preparedCheck artifact index (Limits.maxVisits - used) with
  | .error kind => .error ⟨kind, some ⟨.definition,index⟩⟩
  | .ok checked =>
    if used + checked.visits > Limits.maxVisits then .error ⟨.limit, some ⟨.definition,index⟩⟩
    else .ok (used + checked.visits)

private def preparedScan (artifact : Artifact) (indices : List Nat) (used : Nat) : Except Failure Nat :=
  indices.foldlM (preparedStep artifact) used

private theorem preparedScan_conditions (artifact : Artifact) (headers : Headers artifact)
    (indices : List Nat) (used total : Nat) (bounded : used ≤ 2000000)
    (accepted : preparedScan artifact indices used = .ok total) :
    used ≤ total ∧ total ≤ 2000000 ∧ ∀ index ∈ indices,
      ∃ definition, artifact.definitions[index]? = some definition ∧ conditions artifact definition = true := by
  induction indices generalizing used with
  | nil =>
    have same : used = total := by simpa [preparedScan, pure, Except.pure] using accepted
    subst total
    exact ⟨Nat.le_refl _, bounded, by simp⟩
  | cons index rest ih =>
    cases hc : preparedCheck artifact index (2000000-used) with
    | error e => simp [preparedScan,preparedStep,hc,bind,Except.bind] at accepted
    | ok checked =>
      have facts := preparedCheck_conditions artifact headers index _ checked hc
      by_cases exceeded : used + checked.visits > 2000000
      · simp [preparedScan,preparedStep,hc,exceeded,bind,Except.bind] at accepted
      · have tail : preparedScan artifact rest (used+checked.visits) = .ok total := by
          simpa [preparedScan,preparedStep,hc,exceeded] using accepted
        have all := ih _ (by omega) tail
        refine ⟨by omega,all.2.1,?_⟩
        intro entry member
        rcases List.mem_cons.mp member with equal | following
        · subst entry; exact facts.2.2
        · exact all.2.2 entry following

/-- Charge each shared definition once, including bodies used zero times. -/
def step (artifact : Artifact) (used index : Nat) : Except Failure Nat :=
  match check artifact index (Limits.maxVisits - used) with
  | .error kind => .error ⟨kind, some ⟨.definition,index⟩⟩
  | .ok checked =>
    if used + checked.visits > Limits.maxVisits then .error ⟨.limit, some ⟨.definition,index⟩⟩
    else .ok (used + checked.visits)

def scan (artifact : Artifact) (indices : List Nat) (used : Nat) : Except Failure Nat :=
  indices.foldlM (step artifact) used

theorem step_conditions (artifact : Artifact) (used index total : Nat)
    (accepted : step artifact used index = .ok total) :
    used ≤ total ∧ total ≤ 2000000 ∧
    ∃ definition, artifact.definitions[index]? = some definition ∧ conditions artifact definition = true := by
  unfold step at accepted
  cases hc : check artifact index (2000000 - used) with
  | error failure => simp [hc] at accepted
  | ok checked =>
    simp only [hc] at accepted
    split at accepted
    next invalid => contradiction
    next bound =>
      cases Except.ok.inj accepted
      exact ⟨Nat.le_add_right _ _, Nat.le_of_not_gt bound,
        (check_conditions artifact index _ checked hc).2.2⟩

theorem scan_conditions (artifact : Artifact) (indices : List Nat) (used total : Nat)
    (bounded : used ≤ 2000000) (accepted : scan artifact indices used = .ok total) :
    used ≤ total ∧ total ≤ 2000000 ∧ ∀ index ∈ indices,
      ∃ definition, artifact.definitions[index]? = some definition ∧ conditions artifact definition = true := by
  induction indices generalizing used with
  | nil =>
    have same : used = total := by simpa [scan, pure, Except.pure] using accepted
    subst total
    exact ⟨Nat.le_refl _, bounded, by simp⟩
  | cons index rest ih =>
    cases hs : step artifact used index with
    | error failure => simp [scan, hs, bind, Except.bind] at accepted
    | ok next =>
      have one := step_conditions artifact used index next hs
      have tail : scan artifact rest next = .ok total := by simpa [scan, hs] using accepted
      have all := ih next one.2.1 tail
      refine ⟨Nat.le_trans one.1 all.1, all.2.1, ?_⟩
      intro entry member
      rcases List.mem_cons.mp member with equal | following
      · subst entry; exact one.2.2
      · exact all.2.2 entry following

structure Typed where
  prepared : Prepared
  totalVisits : Nat
  deriving Repr

/-- Structural typing is another necessary phase, not semantic verification.
Finite leaves and computed regions must still discharge their semantic rules. -/
def checkAll (artifact : Artifact) (order : Array Nat) : Except Failure Typed :=
  match prepare artifact order with
  | .error failure => .error failure
  | .ok prepared =>
    let start := prepared.totalVisits + 3 * artifact.definitions.size
    if start > Limits.maxVisits then .error ⟨.limit,none⟩ else
      match preparedScan artifact (List.range artifact.definitions.size) start with
      | .error failure => .error failure
      | .ok total => .ok ⟨prepared,total⟩

theorem checkAll_conditions (artifact : Artifact) (order : Array Nat) (typed : Typed)
    (accepted : checkAll artifact order = .ok typed) :
    prepare artifact order = .ok typed.prepared ∧
    typed.prepared.totalVisits ≤ typed.totalVisits ∧ typed.totalVisits ≤ 2000000 ∧
    ∀ index < artifact.definitions.size,
      ∃ definition, artifact.definitions[index]? = some definition ∧ conditions artifact definition = true := by
  unfold checkAll at accepted
  cases hp : prepare artifact order with
  | error failure => simp [hp] at accepted
  | ok prepared =>
    simp only [hp] at accepted
    split at accepted
    next invalid => contradiction
    next bounded =>
      cases hs : preparedScan artifact (List.range artifact.definitions.size)
          (prepared.totalVisits + 3 * artifact.definitions.size) with
      | error failure => simp [hs] at accepted
      | ok total =>
        simp only [hs] at accepted
        cases Except.ok.inj accepted
        have h := preparedScan_conditions artifact (prepare_headers artifact order prepared hp) _ _ total (Nat.le_of_not_gt bounded) hs
        exact ⟨rfl, Nat.le_trans (Nat.le_add_right _ _) h.1, h.2.1,
          fun index inside => h.2.2 index (List.mem_range.mpr inside)⟩


end QleisliKernel.Hierarchical.NodeTyping
