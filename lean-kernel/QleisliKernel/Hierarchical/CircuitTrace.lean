import QleisliKernel.Hierarchical.Wiring

/-! Routing and ordered opaque operations from actual circuit bodies.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
The cache is constructed from actual definitions. An atom is an independently
requested actual index and complete interface, never a submitted trace. This
component returns derivations and pending atom equations, not semantic evidence.
-/
namespace QleisliKernel.Hierarchical.CircuitTrace
open Artifact

structure Atom where
  index : Nat
  interface : Interface
  deriving BEq, DecidableEq, Repr

structure Event where
  atom : Nat
  /-- Ordered input coordinates, preserving the atom's argument order. -/
  positions : List Nat
  deriving BEq, DecidableEq, Repr

structure Trace where
  width : Nat
  /-- Output position to original input position, after all events. -/
  route : List Nat
  events : Array Event
  deriving BEq, DecidableEq, Repr

abbrev Cache := Array (Option Trace)

def identity (width : Nat) : Trace := ⟨width,List.range width,#[]⟩
def atomic (index width : Nat) : Trace := ⟨width,List.range width,#[⟨index,List.range width⟩]⟩
def transport (route : List Nat) (event : Event) : Event :=
  ⟨event.atom,event.positions.map (Layout.indexAt route)⟩
def compose (first second : Trace) : Option Trace :=
  if first.width = second.width then some
    ⟨first.width,second.route.map (Layout.indexAt first.route),
      first.events ++ second.events.map (transport first.route)⟩ else none

def shift (offset : Nat) (event : Event) : Event :=
  ⟨event.atom,event.positions.map (offset + ·)⟩
def tensor (first second : Trace) : Trace :=
  ⟨first.width+second.width,first.route ++ second.route.map (first.width + ·),
    first.events ++ second.events.map (shift first.width)⟩

inductive Operation where
  | atom (index : Nat) | route (axes : List Nat) | sequence | tensor
  deriving Repr
structure Node where
  operation : Operation
  children : List Nat
  deriving Repr

def project (atoms : Array Atom) (index : Nat) (d : Definition) : Option Node :=
  match atoms.find? (fun atom => atom.index == index) with
  | some atom => if atom.interface == d.interface then some ⟨.atom index,[]⟩ else none
  | none => do
    let node ← Wiring.project d
    return ⟨match node.operation with
      | .route axes => .route axes | .sequence => .sequence | .tensor => .tensor,
      node.children⟩

def eval (width : Nat) : Operation → List Trace → Option Trace
  | .atom index, [] => some (atomic index width)
  | .route axes, [] => some ⟨width,axes,#[]⟩
  | .sequence, children => children.foldlM compose (identity width)
  | .tensor, [first,second] => some (tensor first second)
  | _, _ => none

/-- Atom arity is fixed at atomic creation and preserved by transport/shift.
Only coordinate distinctness and bounds need rechecking after composition. -/
def eventValid (width : Nat) (event : Event) : Bool :=
  decide event.positions.Nodup && event.positions.all (· < width)

def valid (width : Nat) (trace : Trace) : Bool :=
  width ≤ 16 && trace.width == width && decide (trace.route.Perm (List.range width)) &&
    trace.events.all (eventValid width)

def summarize (atoms : Array Atom) (cache : Cache) (index : Nat) (d : Definition) : Option Trace := do
  if (wires d.interface.inputs).size > 16 then none else pure ()
  let node ← project atoms index d
  let children ← node.children.mapM (fun i => (cache[i]?).bind id)
  let width := (wires d.interface.inputs).size
  let trace ← eval width node.operation children
  if decide (d.effect = Effect.unitary) && NodeTyping.quantumOnly d.interface &&
      (wires d.interface.outputs).size == width && valid width trace then some trace else none

inductive Derives (artifact : Artifact) (atoms : Array Atom) : Nat → Trace → Prop where
  | node (index : Nat) (d : Definition) (cache : Cache) (trace : Trace)
      (found : artifact.definitions[index]? = some d)
      (children : ∀ i child, (cache[i]?).bind id = some child → Derives artifact atoms i child)
      (computed : summarize atoms cache index d = some trace) : Derives artifact atoms index trace

def Sound (artifact : Artifact) (atoms : Array Atom) (cache : Cache) : Prop :=
  ∀ i trace, (cache[i]?).bind id = some trace → Derives artifact atoms i trace

structure State where
  cache : Cache
  visits : Nat
  deriving Repr

/-- Only headers and indices are read before any trace content is copied. -/
def scan (atoms : Array Atom) (d : Definition) : Nat :=
  Wiring.scan d + 32 * d.interface.charge + 32 * (1 + atoms.size)

/-- Current and cached widths bound position lists. The child-count factor
covers repeated sequence concatenations; the squared span covers route lookup
and position distinctness. Atom headers are charged separately by `scan`.
Counts are read from array headers before any event transport/materialization. -/
def charge (atoms : Array Atom) (cache : Cache) (node : Node) (d : Definition) : Nat :=
  let events := node.children.foldl (fun count index =>
    count + (((cache[index]?).bind id).map (fun trace => trace.events.size)).getD 0) 0
  let span := node.children.foldl (fun width index =>
    max width ((((cache[index]?).bind id).map Trace.width).getD 0))
    (Ports.wireCount d.interface.inputs)
  scan atoms d + 8 * (1 + node.children.length) * (1 + events) * (1 + span)^2

def step (artifact : Artifact) (atoms : Array Atom) (remaining : Nat)
    (state : State) (index : Nat) : Except Error State :=
  match artifact.definitions[index]?,state.cache[index]? with
  | some d,some none =>
    if state.visits + scan atoms d > remaining then .error .limit else
    match project atoms index d with
    | none => .error .contract
    | some node =>
      let cost := charge atoms state.cache node d
      if state.visits + cost > remaining then .error .limit else
      match summarize atoms state.cache index d with
      | none => .error .contract
      | some trace => .ok ⟨state.cache.setIfInBounds index (some trace),state.visits+cost⟩
  | _,_ => .error .invalidIr

def inspect (artifact : Artifact) (atoms : Array Atom) (order : Array Nat)
    (remaining : Nat) : Except Error State :=
  let header := 32 + artifact.definitions.size + atoms.size + order.size
  if remaining > Limits.maxVisits || header > remaining then .error .limit else
  let cost := header + 32 * (1 + atoms.size)^2 + atoms.foldl (fun cost atom => cost + 32 * atom.interface.charge) 0
  if cost > remaining then .error .limit else
  if !(atoms.map Atom.index).toList.Nodup then .error .contract else
  order.toList.foldlM (step artifact atoms remaining)
    ⟨Array.replicate artifact.definitions.size none,cost⟩

theorem valid_fields (width : Nat) (trace : Trace) (checked : valid width trace = true) :
    width ≤ 16 ∧ trace.width = width ∧ trace.route.Perm (List.range width) ∧
      ∀ event ∈ trace.events.toList, event.positions.Nodup ∧ ∀ i ∈ event.positions, i < width := by
  simpa only [valid,eventValid,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq,
    ← Array.all_toList,List.all_eq_true,and_assoc] using checked

theorem project_cases (atoms : Array Atom) (index : Nat) (d : Definition) (node : Node)
    (projected : project atoms index d = some node) :
    (node = ⟨.atom index,[]⟩ ∧ ∃ atom ∈ atoms.toList,
      atom.index = index ∧ atom.interface = d.interface) ∨
    ∃ wiring, Wiring.project d = some wiring ∧
      node = ⟨match wiring.operation with
        | .route axes => .route axes | .sequence => .sequence | .tensor => .tensor,
        wiring.children⟩ := by
  unfold project at projected
  split at projected
  next atom found =>
    split at projected
    next matched =>
      cases Option.some.inj projected
      exact Or.inl ⟨rfl,atom,by simpa using Array.mem_of_find?_eq_some found,
        by simpa using Array.find?_some found,by simpa using matched⟩
    next absent => contradiction
  next absent =>
    simp only [bind,Option.bind] at projected
    split at projected
    next missing => contradiction
    next wiring found =>
      cases Option.some.inj projected
      exact Or.inr ⟨wiring,found,rfl⟩

theorem summarize_fields (atoms : Array Atom) (cache : Cache) (index : Nat)
    (d : Definition) (trace : Trace) (computed : summarize atoms cache index d = some trace) :
    ∃ node children, project atoms index d = some node ∧
      node.children.mapM (fun i => (cache[i]?).bind id) = some children ∧
      eval (wires d.interface.inputs).size node.operation children = some trace ∧
      d.effect = Effect.unitary ∧ NodeTyping.quantumOnly d.interface = true ∧
      (wires d.interface.outputs).size = (wires d.interface.inputs).size ∧
      valid (wires d.interface.inputs).size trace = true := by
  unfold summarize at computed
  simp only [bind,Option.bind] at computed
  repeat (split at computed <;> (try dsimp only at computed) <;> (try contradiction))
  all_goals
    cases Option.some.inj computed
    simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at *
    exact ⟨_,_,by assumption,by assumption,by assumption,by simp_all,by simp_all,by simp_all,by simp_all⟩

theorem step_sound (artifact : Artifact) (atoms : Array Atom) (remaining : Nat) (state result : State) (index : Nat)
    (sound : Sound artifact atoms state.cache) (accepted : step artifact atoms remaining state index = .ok result) :
    Sound artifact atoms result.cache ∧ result.visits ≤ remaining := by
  unfold step at accepted
  split at accepted
  next d found empty =>
    split at accepted
    next exceeded => contradiction
    next scanned =>
      split at accepted
      next absent => contradiction
      next node projected =>
        dsimp only at accepted
        split at accepted
        next exceeded => contradiction
        next bounded =>
          split at accepted
          next absent => contradiction
          next axes computed =>
            cases Except.ok.inj accepted
            refine ⟨?_,Nat.le_of_not_gt bounded⟩
            intro i code present
            by_cases same : i = index
            · subst i
              have inside := (Array.getElem?_eq_some_iff.mp empty).1
              simp only [Array.getElem?_setIfInBounds_self_of_lt inside,Option.bind_some,id_eq,Option.some.injEq] at present
              subst code
              exact .node index d state.cache axes found sound computed
            · have old : (state.cache[i]?).bind id = some code := by
                simpa only [Array.getElem?_setIfInBounds_ne (Ne.symm same)] using present
              exact sound i code old
  next invalid => contradiction

theorem fold_sound (artifact : Artifact) (atoms : Array Atom) (order : List Nat) (remaining : Nat)
    (state result : State) (sound : Sound artifact atoms state.cache) (budget : state.visits ≤ remaining)
    (accepted : order.foldlM (step artifact atoms remaining) state = .ok result) :
    Sound artifact atoms result.cache ∧ result.visits ≤ remaining := by
  induction order generalizing state with
  | nil => cases Except.ok.inj accepted; exact ⟨sound,budget⟩
  | cons index rest ih =>
    cases checked : step artifact atoms remaining state index with
    | error e => simp [List.foldlM,checked,bind,Except.bind] at accepted
    | ok next =>
      have tail : rest.foldlM (step artifact atoms remaining) next = .ok result := by
        simpa [List.foldlM,checked] using accepted
      have ready := step_sound artifact atoms remaining state next index sound checked
      exact ih next ready.1 ready.2 tail

theorem inspect_sound (artifact : Artifact) (atoms : Array Atom) (order : Array Nat) (remaining : Nat) (result : State)
    (accepted : inspect artifact atoms order remaining = .ok result) :
    Sound artifact atoms result.cache ∧ result.visits ≤ remaining ∧ remaining ≤ 2000000 := by
  unfold inspect at accepted
  dsimp only at accepted
  split at accepted
  next exceeded => contradiction
  next bounded =>
    simp only [Bool.or_eq_true,decide_eq_true_eq,not_or] at bounded
    split at accepted
    next exceeded => contradiction
    next charged =>
      split at accepted
      next duplicate => contradiction
      next distinct =>
        have empty : Sound artifact atoms (Array.replicate artifact.definitions.size none) := by
          intro i code found
          simp [Array.getElem?_replicate] at found
          split at found <;> simp_all
        have result := fold_sound artifact atoms order.toList remaining _ result empty (Nat.le_of_not_gt charged) accepted
        exact ⟨result.1,result.2,by simp only [Limits.maxVisits] at *; omega⟩


end QleisliKernel.Hierarchical.CircuitTrace
