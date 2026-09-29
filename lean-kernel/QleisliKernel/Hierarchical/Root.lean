import QleisliKernel.Hierarchical.Conditional

/-! Bind an actual checked entry to an independently supplied meaning graph.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
Graph pairing is an untrusted proposal. Finite description equalities remain
explicit obligations for the existing transitional exact finite reader. -/

namespace QleisliKernel.Hierarchical.Root
open Artifact

deriving instance DecidableEq for MeaningBody

structure Request where
  kind : Kind
  effect : Effect
  interface : Interface
  meanings : Array Meaning
  entry : Nat
  deriving Repr

structure Pair where
  actual : Nat
  requested : Nat
  children : Array Nat
  deriving Repr

/-- Reference-free constructor data; finite bytes have their own exact
obligation. Counts, polarity, complete maps and structural forms are retained. -/
def shape : MeaningBody → MeaningBody
  | .finite _ => .finite ByteArray.empty
  | .sequence _ => .sequence #[]
  | .tensor _ _ => .tensor 0 0
  | .inverse _ => .inverse 0
  | .control _ polarity => .control 0 polarity
  | .power _ count => .power 0 count
  | .qpeInstrument n m _ => .qpeInstrument n m 0
  | body => body

def children (body : MeaningBody) : List Nat :=
  body.references.toList.map Ref.index

def project (artifact : Artifact) (request : Request) (pairs : Array Pair)
    (pair : Pair) : Option (Meaning × Meaning × List Pair) := do
  let actual ← artifact.meanings[pair.actual]?
  let required ← request.meanings[pair.requested]?
  let ps ← pair.children.toList.mapM (fun i => pairs[i]?)
  return (actual,required,ps)

def aligned (artifact : Artifact) (request : Request) (pairs : Array Pair) (pair : Pair) : Bool :=
  match project artifact request pairs pair with
  | none => false
  | some (actual,required,ps) =>
    actual.interface == required.interface && decide (shape actual.body = shape required.body) &&
      children actual.body == ps.map Pair.actual && children required.body == ps.map Pair.requested

def root (artifact : Artifact) (request : Request) (pairs : Array Pair) : Bool :=
  (do
    let d ← artifact.definitions[artifact.entry.implementation]?
    let p ← artifact.proofs[artifact.entry.proof]?
    let first : Pair ← pairs[0]?
    return p.implementation == artifact.entry.implementation && decide (p.kind = request.kind) &&
      decide (d.effect = request.effect) && d.interface == request.interface &&
      first.actual == p.meaning && first.requested == request.entry).getD false

def covered (request : Request) (pairs : Array Pair) : Bool :=
  (pairs.foldl (fun seen pair => seen.setIfInBounds pair.requested true)
    (Array.replicate request.meanings.size false)).all id

structure FinitePair where
  actual : Meaning
  required : Meaning
  left : ByteArray
  right : ByteArray
  deriving Repr

def finitePair (artifact : Artifact) (request : Request) (pairs : Array Pair)
    (index : Nat) : Option FinitePair := do
  let pair ← pairs[index]?
  let actual ← artifact.meanings[pair.actual]?
  let required ← request.meanings[pair.requested]?
  match actual.body, required.body with
  | .finite left, .finite right => return ⟨actual,required,left,right⟩
  | _, _ => none

def obligations (artifact : Artifact) (request : Request) (pairs : Array Pair) : List Nat :=
  (List.range pairs.size).filter fun i => (finitePair artifact request pairs i).isSome

def rowCharge (artifact : Artifact) (request : Request) (limit used : Nat) (pair : Pair) : Except Error Nat := do
  let some a := artifact.meanings[pair.actual]? | throw .contract
  let some r := request.meanings[pair.requested]? | throw .contract
  let initial := used + 32 + 8 * (pair.children.size + a.body.charge + r.body.charge +
    a.interface.scan + r.interface.scan)
  if initial > limit then throw .limit
  let total := initial + 16 * (a.interface.charge + r.interface.charge)
  if total > limit then throw .limit
  return total

structure Pending where
  visits : Nat
  requests : List Nat
  deriving Repr

/-- Structural work shares the artifact's remaining allowance. Shape matching
does not compare finite bytes or authorize their asserted matrix equality. -/
def payloadCharge (request : Request) : Except Error Nat :=
  request.meanings.foldlM (fun used m =>
    let next := used + match m.body with | .finite bytes => bytes.size | _ => 0
    if next > 16777216 then .error Error.limit else .ok next) 0

def inspect (artifact : Artifact) (request : Request) (pairs : Array Pair)
    (order : Array Nat) (remaining : Nat) : Except Error Pending :=
  if remaining > 2000000 || pairs.isEmpty || pairs.size > 100000 ||
      request.meanings.isEmpty || request.meanings.size > 100000 then .error .limit else
  let initial := 16 * (pairs.size + request.meanings.size + request.interface.scan)
  if initial > remaining then .error .limit else
  let initial := initial + 16 * request.interface.charge
  if initial > remaining then .error .limit else
  match payloadCharge request with
  | .error error => .error error
  | .ok payload =>
    match pairs.foldlM (rowCharge artifact request remaining) initial with
    | .error error => .error error
    | .ok used =>
      if used > remaining then .error .limit else
      let nodes := pairs.map (fun pair => pair.children.toList)
      match Graph.checkWithBudget nodes [0] order (remaining-used) with
      | .error e => .error (match e.kind with | .limit => Error.limit | .invalidIr => Error.invalidIr)
      | .ok schedule =>
        let total := used + schedule.stats.visits
        if total > remaining || payload > 16777216 then .error .limit else
        if !root artifact request pairs || !covered request pairs ||
            !(pairs.all (aligned artifact request pairs)) then .error .contract else
        .ok ⟨total,obligations artifact request pairs⟩

theorem aligned_conditions (artifact : Artifact) (request : Request) (pairs : Array Pair)
    (pair : Pair) (accepted : aligned artifact request pairs pair = true) :
    ∃ actual required ps, project artifact request pairs pair = some (actual,required,ps) ∧
      actual.interface = required.interface ∧ shape actual.body = shape required.body ∧
      children actual.body = ps.map Pair.actual ∧ children required.body = ps.map Pair.requested := by
  unfold aligned at accepted
  split at accepted
  next absent => contradiction
  next actual required ps found =>
    simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at accepted
    exact ⟨actual,required,ps,found,accepted.1.1.1,accepted.1.1.2,accepted.1.2,accepted.2⟩

theorem inspect_conditions (artifact : Artifact) (request : Request) (pairs : Array Pair)
    (order : Array Nat) (remaining : Nat) (pending : Pending)
    (accepted : inspect artifact request pairs order remaining = .ok pending) :
    pending.visits ≤ remaining ∧ pending.requests = obligations artifact request pairs ∧
      root artifact request pairs = true ∧ covered request pairs = true ∧
      ∀ pair ∈ pairs.toList, aligned artifact request pairs pair = true := by
  unfold inspect at accepted
  split at accepted
  next exceeded => simp at accepted
  next bounded =>
    try dsimp only at accepted
    split at accepted
    next exceeded => simp at accepted
    next scanned =>
      try dsimp only at accepted
      split at accepted
      next exceeded => simp at accepted
      next header =>
        split at accepted
        next error failed => simp at accepted
        next payload hp =>
          try simp only [bind,Except.bind] at accepted
          split at accepted
          next error failed => simp at accepted
          next used hu =>
            try simp only [bind,Except.bind] at accepted
            split at accepted
            next exceeded => simp at accepted
            next charged =>
              split at accepted
              next error failed => cases error.kind <;> simp at accepted
              next schedule hs =>
                try simp only [bind,Except.bind] at accepted
                split at accepted
                next exceeded => simp at accepted
                next total =>
                  split at accepted
                  next rejected => simp at accepted
                  next valid =>
                    cases Except.ok.inj accepted
                    have all : root artifact request pairs = true ∧ covered request pairs = true ∧
                        pairs.all (aligned artifact request pairs) = true := by
                      simp only [Bool.or_eq_true,Bool.not_eq_true',not_or,Bool.not_eq_false] at valid
                      exact ⟨valid.1.1,valid.1.2,valid.2⟩
                    refine ⟨?_,rfl,all.1,all.2.1,?_⟩
                    · simp only [Bool.or_eq_true,decide_eq_true_eq,not_or] at total
                      exact Nat.le_of_not_gt total.1
                    · simpa only [← Array.all_toList,List.all_eq_true] using all.2.2

structure Checked where
  artifact : Conditional.Pending
  binding : Pending
  deriving Repr

def checkAll (artifact : Artifact) (order : Array Nat) (request : Request)
    (pairs : Array Pair) (pairOrder : Array Nat) : Except Failure Checked := do
  let pending ← Conditional.checkAll artifact order
  let binding ← match inspect artifact request pairs pairOrder (2000000-pending.state.visits) with
    | .error kind => .error ⟨kind,none⟩
    | .ok binding => .ok binding
  return ⟨pending,binding⟩

theorem checkAll_conditions (artifact : Artifact) (order : Array Nat) (request : Request)
    (pairs : Array Pair) (pairOrder : Array Nat) (checked : Checked)
    (accepted : checkAll artifact order request pairs pairOrder = .ok checked) :
    Conditional.checkAll artifact order = .ok checked.artifact ∧
      inspect artifact request pairs pairOrder (2000000-checked.artifact.state.visits) = .ok checked.binding := by
  unfold checkAll at accepted
  cases ha : Conditional.checkAll artifact order with
  | error e => simp [ha,bind,Except.bind] at accepted
  | ok pending =>
    simp only [ha,bind,Except.bind] at accepted
    cases hb : inspect artifact request pairs pairOrder (2000000-pending.state.visits) with
    | error e => simp [hb] at accepted
    | ok binding =>
      have same : (⟨pending,binding⟩ : Checked) = checked := by simpa [hb,pure,Except.pure] using accepted
      subst checked
      exact ⟨rfl,hb⟩

end QleisliKernel.Hierarchical.Root
