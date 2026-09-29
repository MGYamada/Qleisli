import QleisliKernel.LayoutDag
import QleisliKernel.PhasePolynomial

/-! Typed shared diagonal-phase circuits, with no global dense representation.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

namespace QleisliKernel.PhaseLayout
open Layout PhasePolynomial

structure Summary where
  layout : Rewire
  phases : Polynomial
  deriving BEq, DecidableEq, Repr

structure Definition where
  wiring : LayoutDag.Definition
  sourcePhases : Polynomial
  claimedPhases : Polynomial
  deriving Repr

def Definition.claim (definition : Definition) : Summary :=
  ⟨definition.wiring.result.layout, definition.claimedPhases⟩

structure State where
  bits : Nat → Bool
  phase : Nat

abbrev Action := State → State

def Summary.action (summary : Summary) : Action := fun state =>
  ⟨state.bits ∘ LayoutDag.lookup summary.layout.axes,
    (state.phase + evaluate summary.phases state.bits) % modulus⟩

def thenAction (first second : Action) : Action := fun state => second (first state)

def wire (layout : Rewire) : Summary := ⟨layout, []⟩

def compose (first second : Summary) : Option Summary := do
  let layout ← LayoutDag.compose first.layout second.layout
  return ⟨layout, PhasePolynomial.normalize (first.phases ++ remap (LayoutDag.lookup first.layout.axes) second.phases)⟩

theorem compose_sound (first second result : Summary) (ok : compose first second = some result) :
    result.action = thenAction first.action second.action := by
  cases hc : LayoutDag.compose first.layout second.layout with
  | none => simp [compose, hc] at ok
  | some layout =>
    have same : result = ⟨layout,
        PhasePolynomial.normalize (first.phases ++ remap (LayoutDag.lookup first.layout.axes) second.phases)⟩ := by
      simpa [compose, hc] using ok.symm
    subst result
    have coordinates := congrArg LayoutDag.Meaning.axes
      (LayoutDag.compose_sound first.layout second.layout layout hc)
    simp only [LayoutDag.meaning, LayoutDag.Meaning.then] at coordinates
    funext state
    simp [Summary.action, thenAction, normalize_sound, evaluate_append, remap_sound,
      coordinates, Function.comp_def, Nat.add_assoc]

def evalNode (env : Array Summary) (definition : Definition) : Option Summary :=
  match definition.wiring.body with
  | .leaf layout => some ⟨layout, PhasePolynomial.normalize definition.sourcePhases⟩
  | .call child input output => do
    let callee ← env[child]?
    let first ← compose (wire input.layout) callee
    compose first (wire output.layout)
  | .then first second => do
    compose (← env[first]?) (← env[second]?)

/-- Literal phases and coordinate actions execute directly; claims are never read. -/
def denoteNode (env : Array Action) (definition : Definition) : Option Action :=
  match definition.wiring.body with
  | .leaf layout => some (Summary.action ⟨layout, definition.sourcePhases⟩)
  | .call child input output =>
    env[child]?.map (fun callee =>
      thenAction (thenAction (wire input.layout).action callee) (wire output.layout).action)
  | .then first second => do
    return thenAction (← env[first]?) (← env[second]?)

theorem evalNode_sound (env : Array Summary) (definition : Definition) (result : Summary)
    (ok : evalNode env definition = some result) :
    denoteNode (env.map Summary.action) definition = some result.action := by
  cases hb : definition.wiring.body with
  | leaf layout =>
    have same : result = ⟨layout, PhasePolynomial.normalize definition.sourcePhases⟩ := by
      simpa [evalNode, hb] using ok.symm
    subst result
    simp only [denoteNode, hb, Option.some.injEq]
    funext state
    simp [Summary.action, normalize_sound]
  | call child input output =>
    cases hc : env[child]? with
    | none => simp [evalNode, hb, hc] at ok
    | some callee =>
      cases hf : compose (wire input.layout) callee with
      | none => simp [evalNode, hb, hc, hf] at ok
      | some first =>
        have last : compose first (wire output.layout) = some result := by
          simpa [evalNode, hb, hc, hf] using ok
        rw [compose_sound first (wire output.layout) result last,
          compose_sound (wire input.layout) callee first hf]
        simp [denoteNode, hb, Array.getElem?_map, hc]
  | «then» first second =>
    cases ha : env[first]? with
    | none => simp [evalNode, hb, ha] at ok
    | some a =>
      cases hz : env[second]? with
      | none => simp [evalNode, hb, ha, hz] at ok
      | some b =>
        have composed : compose a b = some result := by simpa [evalNode, hb, ha, hz] using ok
        rw [compose_sound a b result composed]
        simp [denoteNode, hb, Array.getElem?_map, ha, hz]

/-- Verify a result before it is available to any consumer, including for work charging. -/
def checkedNode (env : Array Summary) (definition : Definition) : Option Summary := do
  let result ← evalNode env definition
  if result = definition.claim then some result else none

theorem checkedNode_sound (env : Array Summary) (definition : Definition) (result : Summary)
    (ok : checkedNode env definition = some result) :
    denoteNode (env.map Summary.action) definition = some result.action := by
  unfold checkedNode at ok
  cases hn : evalNode env definition with
  | none => simp [hn] at ok
  | some actual =>
    simp only [hn, bind, Option.bind] at ok
    split at ok
    next equal =>
      cases Option.some.inj ok
      exact evalNode_sound env definition result hn
    next different => contradiction

def evaluateFrom (definitions : List Definition) (env : Array Summary) : Option (Array Summary) :=
  definitions.foldlM (fun env definition => (checkedNode env definition).map env.push) env

def denoteFrom (definitions : List Definition) (env : Array Action) : Option (Array Action) :=
  definitions.foldlM (fun env definition => (denoteNode env definition).map env.push) env

theorem evaluateFrom_sound (definitions : List Definition) (env result : Array Summary)
    (ok : evaluateFrom definitions env = some result) :
    denoteFrom definitions (env.map Summary.action) = some (result.map Summary.action) := by
  induction definitions generalizing env with
  | nil => simpa [evaluateFrom, denoteFrom] using congrArg (Option.map (Array.map Summary.action)) ok
  | cons definition rest ih =>
    cases hn : checkedNode env definition with
    | none => simp [evaluateFrom, hn] at ok
    | some node =>
      have tail : evaluateFrom rest (env.push node) = some result := by
        simpa [evaluateFrom, hn] using ok
      simpa [denoteFrom, checkedNode_sound env definition node hn, Array.map_push] using
        ih (env.push node) tail

abbrev Failure := LayoutDag.Failure

structure Stats where
  layout : LayoutDag.Stats
  phaseWork : Nat
  terms : Nat
  expandedPhaseTerms : Nat
  deriving BEq, DecidableEq, Repr

/-- Bounds are checked before polynomial normalization. Counts are charged from
claims, but a checkedNode must establish each claim before any later consumer. -/
def preflight (definitions : List Definition) (entry : Nat) (required : Summary) :
    Except Failure Stats := do
  let layoutStats ← LayoutDag.preflight (definitions.map Definition.wiring) entry required.layout
  if required.phases.length > 128 then throw ⟨.limit, entry⟩
  let mut phaseWork := 8 * (1 + required.phases.length) ^ 2
  if phaseWork + layoutStats.workUnits > 2000000 then throw ⟨.limit, entry⟩
  if !canonical (wires required.layout.inputs).length required.phases then
    throw ⟨.invalidIr, entry⟩
  let mut counts : Array (Nat × Nat) := #[]
  for (definition, index) in definitions.zipIdx do
    if definition.sourcePhases.length > 128 || definition.claimedPhases.length > 128 then
      throw ⟨.limit, index⟩
    let width := (wires definition.wiring.result.layout.inputs).length
    let (incoming, factor, expanded) ← match definition.wiring.body with
      | .leaf _ => pure (definition.sourcePhases.length, 1, definition.sourcePhases.length)
      | .call child _ _ => do
        if !definition.sourcePhases.isEmpty then throw ⟨.invalidIr, index⟩
        let some count := counts[child]? | throw ⟨.invalidIr, index⟩
        pure (count.1, 2, count.2)
      | .then first second => do
        if !definition.sourcePhases.isEmpty then throw ⟨.invalidIr, index⟩
        let some a := counts[first]? | throw ⟨.invalidIr, index⟩
        let some b := counts[second]? | throw ⟨.invalidIr, index⟩
        pure (a.1 + b.1, 1, a.2 + b.2)
    phaseWork := phaseWork + factor * 64 * (1 + incoming) ^ 2 +
      8 * (1 + definition.claimedPhases.length) ^ 2
    if phaseWork + layoutStats.workUnits > 2000000 then throw ⟨.limit, index⟩
    if !valid width definition.sourcePhases || !canonical width definition.claimedPhases then
      throw ⟨.invalidIr, index⟩
    counts := counts.push (definition.claimedPhases.length, expanded)
  let some root := counts[entry]? | throw ⟨.invalidIr, entry⟩
  return ⟨layoutStats, phaseWork, required.phases.length, root.2⟩

def checkMeanings (definitions : List Definition) (entry : Nat) (required : Summary) :
    Except Failure Layout.Stats :=
  match evaluateFrom definitions #[] with
  | none => .error ⟨.contract, entry⟩
  | some actual =>
    match actual[entry]?, definitions[entry]? with
    | some root, some definition =>
      if root.phases = required.phases then
        (Layout.check root.layout definition.wiring.result.witness required.layout).mapError
          (fun kind => ⟨kind, entry⟩)
      else .error ⟨.contract, entry⟩
    | _, _ => .error ⟨.invalidIr, entry⟩

def check (definitions : List Definition) (entry : Nat) (required : Summary) :
    Except Failure Stats :=
  match preflight definitions entry required with
  | .error failure => .error failure
  | .ok stats =>
    match checkMeanings definitions entry required with
    | .error failure => .error failure
    | .ok _ => .ok stats

def denote (definitions : List Definition) (entry : Nat) : Option Action := do
  let meanings ← denoteFrom definitions #[]
  meanings[entry]?

theorem checkMeanings_sound (definitions : List Definition) (entry : Nat) (required : Summary)
    (stats : Layout.Stats) (accepted : checkMeanings definitions entry required = .ok stats) :
    denote definitions entry = some required.action ∧
      ∃ witness, Layout.check required.layout witness required.layout = .ok stats := by
  unfold checkMeanings at accepted
  split at accepted
  next impossible => contradiction
  next actual heval =>
    split at accepted
    next root definition hroot hdefinition =>
      split at accepted
      next samePhase =>
        cases hc : Layout.check root.layout definition.wiring.result.witness required.layout with
        | error failure => simp [hc, Except.mapError] at accepted
        | ok info =>
          have eqStats : info = stats := by simpa [hc, Except.mapError] using accepted
          cases eqStats
          have sameLayout :=
            (Layout.check_conditions root.layout required.layout definition.wiring.result.witness stats hc).1
          have same : root = required := by cases root; cases required; simp_all
          subst root
          refine ⟨?_, definition.wiring.result.witness, hc⟩
          have semantic := evaluateFrom_sound definitions #[] actual heval
          simp only [Array.map_empty] at semantic
          simp [denote, semantic, Array.getElem?_map, hroot]
      next wrongPhase => contradiction
    next impossible => contradiction

theorem check_sound (definitions : List Definition) (entry : Nat) (required : Summary)
    (stats : Stats) (accepted : check definitions entry required = .ok stats) :
    denote definitions entry = some required.action ∧
      ∃ witness layoutStats, Layout.check required.layout witness required.layout = .ok layoutStats := by
  unfold check at accepted
  cases hp : preflight definitions entry required with
  | error failure => simp [hp] at accepted
  | ok info =>
    cases hm : checkMeanings definitions entry required with
    | error failure => simp [hp, hm] at accepted
    | ok layoutStats =>
      obtain ⟨semantics, witness, checked⟩ := checkMeanings_sound definitions entry required layoutStats hm
      exact ⟨semantics, witness, layoutStats, checked⟩

/-- A frame/reference value is retained exactly, without a separability premise. -/
theorem check_reference (definitions : List Definition) (entry : Nat) (required : Summary)
    (stats : Stats) (accepted : check definitions entry required = .ok stats)
    (actual : Action) (meaning : denote definitions entry = some actual) {R : Type}
    (state : State) (reference : R) :
    (actual state, reference) = (required.action state, reference) := by
  have same := (check_sound definitions entry required stats accepted).1
  rw [meaning] at same
  cases Option.some.inj same
  rfl

end QleisliKernel.PhaseLayout
