import QleisliKernel.Dag

/-! Bounded phase DAG integration. One quantum owner is retained even at width zero.
This is a CD-3 composition slice, not the qpe-dyadic8-v1 hierarchy profile.
Copyright 2026 Masahiko G. Yamada. Apache-2.0. -/

namespace QleisliKernel.Hierarchy
open Dag

inductive Shape where
  | unit | bit | bits0 | bits1
  deriving BEq, DecidableEq, Repr

def Shape.zeroWidth : Shape → Bool
  | .unit | .bits0 => true
  | .bit | .bits1 => false

structure Definition where
  shape : Shape
  body : Instruction
  claimed : Summary
  deriving Repr

structure Request where
  shape : Shape
  meaning : Summary
  deriving Repr

inductive ErrorKind where
  | invalidIr | contract | limit
  deriving BEq, DecidableEq, Repr

structure Failure where
  kind : ErrorKind
  node : Nat
  deriving BEq, DecidableEq, Repr

structure NodeInfo where
  shape : Shape
  depth : Nat
  expandedGates : Nat
  deriving Repr

structure Stats where
  nodes : Nat
  references : Nat
  workUnits : Nat
  depth : Nat
  expandedGates : Nat
  deriving BEq, DecidableEq, Repr

structure Scan where
  info : Array NodeInfo := #[]
  references : Nat := 0
  workUnits : Nat := 0

/-- Every slot is a single logical owner; Unit/Bits0 still require port 0. -/
def validPorts (input output : List Nat) : Bool :=
  decide (input = [0]) && decide (output = [0])

private def validateNode (scan : Scan) (definition : Definition) : Except Failure Scan := do
  let index := scan.info.size
  let fail (kind : ErrorKind) : Failure := ⟨kind, index⟩
  if !summaryValid definition.claimed then throw (fail .contract)
  let children := definition.body.references
  let localWork := match definition.body with
    | .leaf word => 1 + 3 * word.length
    | .call _ input output => input.length + output.length
    | .sequence refs => refs.length
    | .repeatOp _ _ => 16
  let work := scan.workUnits + 1 + 4 * children.length + localWork
  if work > 2000000 || scan.references + children.length > 4096 then
    throw (fail .limit)
  match definition.body with
  | .leaf word =>
    if word.length > maxGates then throw (fail .limit)
    if !(word.all gateValid) then throw (fail .invalidIr)
    if definition.shape.zeroWidth && !word.isEmpty then throw (fail .invalidIr)
  | .call _ input output =>
    if !validPorts input output then throw (fail .invalidIr)
  | .sequence refs =>
    if refs.isEmpty then throw (fail .invalidIr)
  | .repeatOp count _ =>
    if count > 4096 then throw (fail .limit)
  -- This lookup is unconditional, including for zero repetitions.
  let (childDepth, childCost) ← children.foldlM (fun (depth, cost) child => do
    let some body := scan.info[child]? | throw (fail .invalidIr)
    if body.shape != definition.shape then throw (fail .invalidIr)
    return (max depth body.depth, cost + body.expandedGates)) (0, 0)
  let depth := childDepth + 1
  if depth > 64 then throw (fail .limit)
  let cost := match definition.body with
    | .leaf word => word.length
    | .repeatOp count _ => count * childCost
    | _ => childCost
  return { info := scan.info.push ⟨definition.shape, depth, cost⟩
           references := scan.references + children.length, workUnits := work }

/-- Reverse topological traversal checks reachability without expanding a call. -/
def reachable (definitions : List Definition) (entry : Nat) : Bool :=
  let initial := (Array.replicate definitions.length false).setIfInBounds entry true
  let seen := definitions.zipIdx.reverse.foldl (fun seen (definition, index) =>
    if seen[index]?.getD false then
      definition.body.references.foldl (fun seen child => seen.setIfInBounds child true) seen
    else seen) initial
  seen.all id

def preflight (definitions : List Definition) (entry : Nat) (required : Request) :
    Except Failure Stats := do
  if definitions.isEmpty || definitions.length > 256 then
    throw ⟨.limit, entry⟩
  if !summaryValid required.meaning then throw ⟨.contract, entry⟩
  let checked ← definitions.foldlM validateNode {}
  let some root := checked.info[entry]? | throw ⟨.invalidIr, entry⟩
  if root.shape != required.shape || !reachable definitions entry then
    throw ⟨.invalidIr, entry⟩
  return ⟨definitions.length, checked.references, checked.workUnits, root.depth, root.expandedGates⟩

/-- Check each proposed receipt against a freshly derived cached meaning. -/
def checkMeanings (definitions : List Definition) (entry : Nat) (expected : Summary) :
    Except Failure Unit :=
  match evaluate summaryAlgebra (definitions.map Definition.body) with
  | none => .error ⟨.invalidIr, entry⟩
  | some values =>
    match (values.toList.zip definitions).findIdx? (fun (actual, definition) =>
        decide (actual ≠ definition.claimed)) with
    | some index => .error ⟨.contract, index⟩
    | none =>
      if values[entry]? = some expected then .ok ()
      else .error ⟨.contract, entry⟩

/-- No producer claim is used as a cached premise: meanings are recomputed from IR. -/
def check (definitions : List Definition) (entry : Nat) (required : Request) :
    Except Failure Stats :=
  match preflight definitions entry required with
  | .error failure => .error failure
  | .ok stats =>
    match checkMeanings definitions entry required.meaning with
    | .ok () => .ok stats
    | .error failure => .error failure

/-- The denotation executes gates/actions rather than the proposed summaries. -/
def denote (definitions : List Definition) (entry : Nat) : Option Action :=
  (evaluate actionAlgebra (definitions.map Definition.body)).bind (fun values => values[entry]?)

theorem checkMeanings_sound (definitions : List Definition) (entry : Nat) (expected : Summary)
    (accepted : checkMeanings definitions entry expected = .ok ()) :
    denote definitions entry = some expected.action := by
  unfold checkMeanings at accepted
  split at accepted
  next impossible => contradiction
  next values heval =>
    split at accepted
    next index mismatch => contradiction
    next allMatch =>
      split at accepted
      next hroot =>
        unfold denote
        rw [← evaluate_actions, heval]
        simp [Array.getElem?_map, hroot]
      next wrongRoot => contradiction

/-- The actual checking result implies the independent requested operational action. -/
theorem check_sound (definitions : List Definition) (entry : Nat) (required : Request)
    (stats : Stats) (accepted : check definitions entry required = .ok stats) :
    denote definitions entry = some required.meaning.action := by
  unfold check at accepted
  cases h : preflight definitions entry required with
  | error failure => simp [h] at accepted
  | ok info =>
    simp only [h] at accepted
    cases verified : checkMeanings definitions entry required.meaning with
    | ok value =>
      exact checkMeanings_sound definitions entry required.meaning verified
    | error failure => simp [verified] at accepted

end QleisliKernel.Hierarchy
