import QleisliKernel.Layout

/-! Shared typed coordinate transformations with independently checked call adapters.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

namespace QleisliKernel.LayoutDag
open Layout

structure Certified where
  layout : Rewire
  witness : Witness
  deriving Repr

inductive Body where
  | leaf (layout : Rewire)
  | call (child : Nat) (input output : Certified)
  | then (first second : Nat)
  deriving Repr

structure Definition where
  body : Body
  result : Certified
  deriving Repr

def Body.references : Body → List Nat
  | .leaf _ => []
  | .call child _ _ => [child]
  | .then first second => [first, second]

/-- Outside a finite interface the coordinate action is the identity. -/
def lookup (map : List Nat) (i : Nat) : Nat := map[i]?.getD i

/-- On a finite interface this agrees with the checked layout's coordinate map. -/
theorem lookup_eq_indexAt (map : List Nat) (i : Nat) (inside : i < map.length) :
    lookup map i = Layout.indexAt map i := by
  simp [lookup, Layout.indexAt, List.getElem?_eq_getElem inside]

structure Meaning where
  owners : Nat → Nat
  axes : Nat → Nat

def meaning (layout : Rewire) : Meaning := ⟨lookup layout.owners, lookup layout.axes⟩

/-- Output coordinates point backwards through the second and then the first map. -/
def Meaning.then (first second : Meaning) : Meaning :=
  ⟨first.owners ∘ second.owners, first.axes ∘ second.axes⟩

def compose (first second : Rewire) : Option Rewire :=
  if first.outputs = second.inputs ∧ first.owners.length = second.owners.length ∧
      first.axes.length = second.axes.length then
    some ⟨first.inputs, second.outputs, second.owners.map (lookup first.owners),
      second.axes.map (lookup first.axes)⟩
  else none

theorem lookup_compose (first second : List Nat) (same : first.length = second.length) :
    lookup (second.map (lookup first)) = lookup first ∘ lookup second := by
  funext i
  by_cases inside : i < second.length
  · simp [lookup, List.getElem?_map, List.getElem?_eq_getElem inside]
  · have outside : first.length ≤ i := by omega
    simp [lookup, List.getElem?_map, List.getElem?_eq_none (by omega : second.length ≤ i),
      List.getElem?_eq_none outside]

theorem compose_sound (first second result : Rewire) (ok : compose first second = some result) :
    meaning result = (meaning first).then (meaning second) := by
  unfold compose at ok
  split at ok
  next valid =>
    cases Option.some.inj ok
    simp only [meaning, Meaning.then]
    rw [lookup_compose first.owners second.owners valid.2.1,
      lookup_compose first.axes second.axes valid.2.2]
  next invalid => contradiction

def evalNode (env : Array Rewire) : Body → Option Rewire
  | .leaf layout => some layout
  | .call child input output => do
    let callee ← env[child]?
    let first ← compose input.layout callee
    compose first output.layout
  | .then first second => do
    compose (← env[first]?) (← env[second]?)

/-- Operational interpretation follows the graph; it never reads result claims. -/
def denoteNode (env : Array Meaning) : Body → Option Meaning
  | .leaf layout => some (meaning layout)
  | .call child input output =>
    env[child]?.map (fun callee => ((meaning input.layout).then callee).then (meaning output.layout))
  | .then first second => do
    return (← env[first]?).then (← env[second]?)

theorem evalNode_sound (env : Array Rewire) (body : Body) (result : Rewire)
    (ok : evalNode env body = some result) :
    denoteNode (env.map meaning) body = some (meaning result) := by
  cases body with
  | leaf layout => simpa [evalNode, denoteNode] using congrArg (Option.map meaning) ok
  | call child input output =>
    cases hc : env[child]? with
    | none => simp [evalNode, hc] at ok
    | some callee =>
      cases hf : compose input.layout callee with
      | none => simp [evalNode, hc, hf] at ok
      | some first =>
        have last : compose first output.layout = some result := by
          simpa [evalNode, hc, hf] using ok
        rw [compose_sound first output.layout result last,
          compose_sound input.layout callee first hf]
        simp [denoteNode, Array.getElem?_map, hc]
  | «then» first second =>
    cases ha : env[first]? with
    | none => simp [evalNode, ha] at ok
    | some a =>
      cases hb : env[second]? with
      | none => simp [evalNode, ha, hb] at ok
      | some b =>
        have composed : compose a b = some result := by simpa [evalNode, ha, hb] using ok
        rw [compose_sound a b result composed]
        simp [denoteNode, Array.getElem?_map, ha, hb]

-- The standard total list fold avoids project-owned partial recursion replacements.
def evaluateFrom (bodies : List Body) (env : Array Rewire) : Option (Array Rewire) :=
  bodies.foldlM (fun env body => (evalNode env body).map env.push) env

def denoteFrom (bodies : List Body) (env : Array Meaning) : Option (Array Meaning) :=
  bodies.foldlM (fun env body => (denoteNode env body).map env.push) env

theorem evaluateFrom_sound (bodies : List Body) (env result : Array Rewire)
    (ok : evaluateFrom bodies env = some result) :
    denoteFrom bodies (env.map meaning) = some (result.map meaning) := by
  induction bodies generalizing env with
  | nil => simpa [evaluateFrom, denoteFrom] using congrArg (Option.map (Array.map meaning)) ok
  | cons body rest ih =>
    cases hn : evalNode env body with
    | none => simp [evaluateFrom, hn] at ok
    | some node =>
      have tail : evaluateFrom rest (env.push node) = some result := by
        simpa [evaluateFrom, hn] using ok
      simpa [denoteFrom, evalNode_sound env body node hn, Array.map_push] using
        ih (env.push node) tail

structure NodeInfo where
  depth : Nat
  expandedLayouts : Nat

structure Stats where
  nodes : Nat
  references : Nat
  workUnits : Nat
  depth : Nat
  expandedLayouts : Nat
  deriving BEq, DecidableEq, Repr

structure Scan where
  info : Array NodeInfo := #[]
  references : Nat := 0
  workUnits : Nat := 0

structure Failure where
  kind : Layout.Error
  node : Nat
  deriving Repr

private def checkedCost (item : Certified) : Except Layout.Error Nat := do
  return (← Layout.check item.layout item.witness item.layout).workUnits

private def scanNode (scan : Scan) (definition : Definition) : Except Failure Scan := do
  let index := scan.info.size
  let fail (kind : Layout.Error) : Except Failure Scan := .error ⟨kind, index⟩
  let refs := definition.body.references
  let references := scan.references + refs.length
  if references > 4096 then fail .limit else do
    match definition.body with
    | .leaf layout =>
      if !Layout.limits layout then return ← fail .limit
      if layout != definition.result.layout then return ← fail .contract
    | _ => pure ()
    let mut cost := 1 + 4 * refs.length
    -- Both adapters are checked even when their composition later cancels.
    let items := definition.result :: (match definition.body with
      | .call _ input output => [input, output]
      | _ => [])
    for item in items do
      -- Charge before the potentially expensive structural check.
      let charge := Layout.workUnits item.layout
      if scan.workUnits + cost + charge > 2000000 then return ← fail .limit
      match checkedCost item with
      | .error kind => return ← fail kind
      | .ok used => cost := cost + used
    let mut depth := 1
    let mut expanded := match definition.body with | .leaf _ => 1 | .call _ _ _ => 2 | _ => 0
    for ref in refs do
      let some child := scan.info[ref]? | return ← fail .invalidIr
      depth := max depth (child.depth + 1)
      expanded := expanded + child.expandedLayouts
    if depth > 64 then fail .limit else
      return ⟨scan.info.push ⟨depth, expanded⟩, references, scan.workUnits + cost⟩

private def reachable (definitions : List Definition) (entry : Nat) : Bool := Id.run do
  let mut seen := (Array.replicate definitions.length false).set! entry true
  for (definition, index) in definitions.zipIdx |>.reverse do
    if seen[index]?.getD false then
      for ref in definition.body.references do
        seen := seen.set! ref true
  return seen.all id

def preflight (definitions : List Definition) (entry : Nat) (required : Rewire) :
    Except Failure Stats := do
  if definitions.isEmpty || definitions.length > 256 || !Layout.limits required then
    throw ⟨.limit, entry⟩
  let scan ← definitions.foldlM scanNode {}
  let some root := scan.info[entry]? | throw ⟨.invalidIr, entry⟩
  let some rootDefinition := definitions[entry]? | throw ⟨.invalidIr, entry⟩
  let totalWork := scan.workUnits + Layout.workUnits rootDefinition.result.layout
  if totalWork > 2000000 then throw ⟨.limit, entry⟩
  if !reachable definitions entry then throw ⟨.invalidIr, entry⟩
  return ⟨definitions.length, scan.references, totalWork, root.depth, root.expandedLayouts⟩

def checkMeanings (definitions : List Definition) (entry : Nat) (required : Rewire) :
    Except Failure Layout.Stats :=
  match evaluateFrom (definitions.map Definition.body) #[] with
  | none => .error ⟨.invalidIr, entry⟩
  | some actual =>
    if (definitions.zipIdx).any (fun (definition, index) =>
        actual[index]? != some definition.result.layout) then .error ⟨.contract, entry⟩
    else match actual[entry]?, definitions[entry]? with
      | some root, some definition =>
        (Layout.check root definition.result.witness required).mapError (fun kind => ⟨kind, entry⟩)
      | _, _ => .error ⟨.invalidIr, entry⟩

def check (definitions : List Definition) (entry : Nat) (required : Rewire) :
    Except Failure Stats :=
  match preflight definitions entry required with
  | .error failure => .error failure
  | .ok stats =>
    match checkMeanings definitions entry required with
    | .error failure => .error failure
    | .ok _ => .ok stats

/-- Direct graph semantics, independent of all result claims and inverse evidence. -/
def denote (definitions : List Definition) (entry : Nat) : Option Meaning := do
  let meanings ← denoteFrom (definitions.map Definition.body) #[]
  meanings[entry]?

theorem checkMeanings_sound (definitions : List Definition) (entry : Nat) (required : Rewire)
    (stats : Layout.Stats) (accepted : checkMeanings definitions entry required = .ok stats) :
    denote definitions entry = some (meaning required) ∧
      ∃ witness, Layout.check required witness required = .ok stats := by
  unfold checkMeanings at accepted
  split at accepted
  next impossible => contradiction
  next actual heval =>
    split at accepted
    next wrong => contradiction
    next allMatch =>
      split at accepted
      next root definition hroot hdefinition =>
        cases hc : Layout.check root definition.result.witness required with
        | error failure => simp [hc, Except.mapError] at accepted
        | ok info =>
          have eqStats : info = stats := by simpa [hc, Except.mapError] using accepted
          cases eqStats
          have same := (Layout.check_conditions root required definition.result.witness stats hc).1
          subst root
          refine ⟨?_, definition.result.witness, hc⟩
          have semantic := evaluateFrom_sound (definitions.map Definition.body) #[] actual heval
          simp only [Array.map_empty] at semantic
          simp [denote, semantic, Array.getElem?_map, hroot]
      next impossible => contradiction

/-- Actual acceptance binds both graph semantics and the entry resource certificate. -/
theorem check_sound (definitions : List Definition) (entry : Nat) (required : Rewire)
    (stats : Stats) (accepted : check definitions entry required = .ok stats) :
    denote definitions entry = some (meaning required) ∧
      ∃ witness layoutStats, Layout.check required witness required = .ok layoutStats := by
  unfold check at accepted
  cases hp : preflight definitions entry required with
  | error failure => simp [hp] at accepted
  | ok info =>
    cases hm : checkMeanings definitions entry required with
    | error failure => simp [hp, hm] at accepted
    | ok layoutStats =>
      obtain ⟨semantics, witness, checked⟩ := checkMeanings_sound definitions entry required layoutStats hm
      exact ⟨semantics, witness, layoutStats, checked⟩

end QleisliKernel.LayoutDag
