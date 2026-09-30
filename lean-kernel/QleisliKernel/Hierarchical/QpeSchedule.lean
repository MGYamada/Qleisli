import QleisliKernel.Hierarchical.CircuitTrace
import QleisliKernel.Hierarchical.RoutedPower
import QleisliKernel.Hierarchical.FourierRoot

/-! Actual coherent QPE schedule, with independent coordinate and provider requests.
This inspector returns finite H and provider obligations; it does not issue a
named instrument receipt. Complete artifact typing, provider-request binding,
zero preparation and ordered readout remain separate required obligations.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Hierarchical.QpeSchedule
open Artifact

deriving instance ReflBEq, LawfulBEq for CircuitTrace.Atom

structure Request where
  interface : Interface
  /-- Input coordinates in low-bit-first precision order. -/
  phase : Array Nat
  /-- Input coordinates in the provider's complete target order. -/
  target : Array Nat
  /-- Output coordinate to input coordinate, after all local operations. -/
  route : Array Nat
  provider : Nat
  deriving Repr

structure Candidate where
  hadamards : Array CircuitTrace.Atom
  powers : Array CircuitTrace.Atom
  inverseFourier : CircuitTrace.Atom
  traceOrder : Array Nat
  powerOrders : Array (Array Nat)
  fourierOrder : Array Nat
  deriving Repr

def atoms (candidate : Candidate) : Array CircuitTrace.Atom :=
  ((candidate.hadamards ++ candidate.powers).push candidate.inverseFourier).toList.eraseDups.toArray

def expected (request : Request) (candidate : Candidate) : CircuitTrace.Trace :=
  ⟨request.phase.size+request.target.size,request.route.toList,
    (candidate.hadamards.mapIdx fun k atom => ⟨atom.index,[request.phase[k]!]⟩) ++
    (candidate.powers.mapIdx fun k atom => ⟨atom.index,request.phase[k]!::request.target.toList⟩) ++
    #[⟨candidate.inverseFourier.index,request.phase.toList⟩]⟩

def layout (request : Request) : Bool :=
  request.phase.size > 0 && request.phase.size ≤ 8 &&
    request.target.size > 0 && request.target.size ≤ 8 && u32 request.provider &&
    decide ((request.phase ++ request.target).toList.Perm
      (List.range (request.phase.size+request.target.size))) &&
    decide (request.route.toList.Perm (List.range (request.phase.size+request.target.size)))

def sized (n : Nat) (d : Definition) : Bool := RoutedPower.sized n d

structure Leaf where
  definition : Definition
  program : ByteArray
  deriving Repr

/-- A finite H obligation retains the full actual bytes. The later exact reader
must establish the phase-fixed H matrix, including its global phase. -/
def leaf (artifact : Artifact) (atom : CircuitTrace.Atom) : Option Leaf := do
  let d ← artifact.definitions[atom.index]?
  let .leaf program := d.body | none
  if d.interface == atom.interface && sized 1 d && program.size ≤ 16777216 then
    some ⟨d,program⟩ else none

structure Part where
  hadamard : Leaf
  power : RoutedPower.Pending
  visits : Nat
  deriving Repr

def powerRequest (request : Request) (atom : CircuitTrace.Atom) (axis : Nat) : RoutedPower.Request :=
  ⟨request.target.size,axis,request.provider,atom.interface⟩

def checkPart (artifact : Artifact) (request : Request) (h power : CircuitTrace.Atom)
    (axis : Nat) (order : Array Nat) (remaining : Nat) : Except Error Part :=
  match leaf artifact h with
  | none => .error .contract
  | some hadamard =>
    match RoutedPower.inspect artifact power.index (powerRequest request power axis) order remaining with
    | .error error => .error error
    | .ok checked => .ok ⟨hadamard,checked,checked.visits⟩

structure Parts where
  values : List Part
  visits : Nat
  deriving Repr

/-- The same remaining allowance is threaded through every actual power. -/
def checkParts (artifact : Artifact) (request : Request) (candidate : Candidate)
    (remaining : Nat) (axes : List Nat) : Except Error Parts :=
  axes.foldr (fun axis recurse remaining => do
    let h ← match candidate.hadamards[axis]? with | none => .error .contract | some x => .ok x
    let power ← match candidate.powers[axis]? with | none => .error .contract | some x => .ok x
    let order ← match candidate.powerOrders[axis]? with | none => .error .contract | some x => .ok x
    let part ← checkPart artifact request h power axis order remaining
    let parts ← recurse (remaining-part.visits)
    return ⟨part::parts.values,part.visits+parts.visits⟩) (fun _ => .ok ⟨[],0⟩) remaining

theorem checkParts_cons (artifact : Artifact) (request : Request) (candidate : Candidate)
    (remaining axis : Nat) (rest : List Nat) :
    checkParts artifact request candidate remaining (axis::rest) = (do
      let h ← match candidate.hadamards[axis]? with | none => .error .contract | some x => .ok x
      let power ← match candidate.powers[axis]? with | none => .error .contract | some x => .ok x
      let order ← match candidate.powerOrders[axis]? with | none => .error .contract | some x => .ok x
      let part ← checkPart artifact request h power axis order remaining
      let parts ← checkParts artifact request candidate (remaining-part.visits) rest
      return ⟨part::parts.values,part.visits+parts.visits⟩) := rfl

structure InverseView where
  definition : Definition
  child : Nat
  forward : Definition
  deriving Repr

def inverseView (artifact : Artifact) (width : Nat) (atom : CircuitTrace.Atom) : Option InverseView := do
  let d ← artifact.definitions[atom.index]?
  let .inverse child := d.body | none
  let forward ← artifact.definitions[child]?
  if d.interface == atom.interface && sized width d then some ⟨d,child,forward⟩ else none

/-- Only the entry selector changes. Every definition and finite byte remains in
this exact artifact; the Fourier inspector itself never uses a proof selector. -/
def atEntry (artifact : Artifact) (index : Nat) : Artifact :=
  {artifact with entry := {artifact.entry with implementation := index}}

structure Inverse where
  view : InverseView
  fourier : FourierRoot.Pending
  visits : Nat
  deriving Repr

def checkInverse (artifact : Artifact) (width : Nat) (atom : CircuitTrace.Atom)
    (order : Array Nat) (remaining : Nat) : Except Error Inverse :=
  match inverseView artifact width atom with
  | none => .error .contract
  | some view =>
    match FourierRoot.inspect (atEntry artifact view.child) ⟨width,view.forward.interface⟩ order remaining with
    | .error error => .error error
    | .ok fourier => .ok ⟨view,fourier,fourier.visits⟩

/-- All array lengths are checked before constructing bounded expected events.
Full actual H/inverse headers are charged before the projections above read them. -/
def headerCharge (request : Request) (candidate : Candidate) : Nat :=
  64 + 32 * (1 + request.phase.size+request.target.size+request.route.size+
    candidate.hadamards.size+candidate.powers.size+candidate.powerOrders.size) +
    32 * request.interface.charge

def workCharge (artifact : Artifact) (request : Request) (candidate : Candidate) : Nat :=
  headerCharge request candidate +
    ((artifact.definitions[artifact.entry.implementation]?).map (fun d => 32*d.interface.charge)).getD 0 +
    candidate.hadamards.foldl (fun cost atom => cost + 32 * atom.interface.charge +
      ((artifact.definitions[atom.index]?).map (fun d => 32*d.interface.charge)).getD 0) 0 +
    32 * candidate.inverseFourier.interface.charge +
    ((artifact.definitions[candidate.inverseFourier.index]?).map (fun d => 32*d.interface.charge)).getD 0 +
    32 * (1+request.phase.size+request.target.size)^2

structure Pending where
  parts : Parts
  inverse : Inverse
  trace : CircuitTrace.State
  visits : Nat
  deriving Repr

def inspect (artifact : Artifact) (request : Request) (candidate : Candidate)
    (remaining : Nat) : Except Error Pending :=
  if remaining > 2000000 || headerCharge request candidate > remaining then .error .limit else
  if request.phase.size > 8 || request.target.size > 8 || request.route.size > 16 ||
      candidate.hadamards.size != request.phase.size || candidate.powers.size != request.phase.size ||
      candidate.powerOrders.size != request.phase.size then .error .contract else
  let cost := workCharge artifact request candidate
  if cost > remaining then .error .limit else
  if !layout request then .error .contract else
  match artifact.definitions[artifact.entry.implementation]? with
  | none => .error .invalidIr
  | some d =>
    if d.interface != request.interface || !sized (request.phase.size+request.target.size) d then .error .contract else
    match checkParts artifact request candidate (remaining-cost) (List.range request.phase.size) with
    | .error e => .error e
    | .ok parts =>
      match checkInverse artifact request.phase.size candidate.inverseFourier candidate.fourierOrder
        (remaining-cost-parts.visits) with
      | .error e => .error e
      | .ok inverse =>
        match CircuitTrace.inspect artifact (atoms candidate) candidate.traceOrder
          (remaining-cost-parts.visits-inverse.visits) with
        | .error e => .error e
        | .ok trace =>
          if (trace.cache[artifact.entry.implementation]?).bind id ≠ some (expected request candidate)
            then .error .contract else .ok ⟨parts,inverse,trace,cost+parts.visits+inverse.visits+trace.visits⟩

theorem leaf_bound (artifact : Artifact) (atom : CircuitTrace.Atom) (result : Leaf)
    (found : leaf artifact atom = some result) :
    artifact.definitions[atom.index]? = some result.definition ∧
      result.definition.body = .leaf result.program ∧ result.definition.interface = atom.interface ∧
      sized 1 result.definition = true ∧ result.program.size ≤ 16777216 := by
  unfold leaf at found
  simp only [bind,Option.bind] at found
  repeat (split at found <;> (try dsimp only at found) <;> (try contradiction))
  all_goals
    cases Option.some.inj found
    simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at *
    exact ⟨by assumption,by assumption,by simp_all,by simp_all,by simp_all⟩

theorem checkPart_conditions (artifact : Artifact) (request : Request) (h power : CircuitTrace.Atom)
    (axis : Nat) (order : Array Nat) (remaining : Nat) (part : Part)
    (checked : checkPart artifact request h power axis order remaining = .ok part) :
    leaf artifact h = some part.hadamard ∧
      RoutedPower.inspect artifact power.index (powerRequest request power axis) order remaining = .ok part.power ∧
      part.visits = part.power.visits ∧ part.visits ≤ remaining := by
  unfold checkPart at checked
  split at checked
  next absent => contradiction
  next hadamard found =>
    split at checked
    next failed => contradiction
    next power checkedPower =>
      cases Except.ok.inj checked
      exact ⟨found,checkedPower,rfl,
        (RoutedPower.inspect_conditions _ _ _ _ _ _ checkedPower).2.2.2.2.2.1⟩


/-- A retained part records the exact atom selectors and remaining allowance
used for its fresh checks. No externally supplied checked part is accepted. -/
def PartChecked (artifact : Artifact) (request : Request) (candidate : Candidate)
    (axis : Nat) (part : Part) : Prop :=
  ∃ h power order remaining, candidate.hadamards[axis]? = some h ∧
    candidate.powers[axis]? = some power ∧ candidate.powerOrders[axis]? = some order ∧
    checkPart artifact request h power axis order remaining = .ok part

def PartsChecked (artifact : Artifact) (request : Request) (candidate : Candidate)
    (axes : List Nat) (parts : List Part) : Prop :=
  axes.foldr (fun axis recurse values => match values with
    | part::rest => PartChecked artifact request candidate axis part ∧ recurse rest
    | [] => False) (fun values => match values with | [] => True | _ => False) parts

theorem checkParts_conditions (artifact : Artifact) (request : Request) (candidate : Candidate)
    (axes : List Nat) (remaining : Nat) (parts : Parts)
    (checked : checkParts artifact request candidate remaining axes = .ok parts) :
    parts.visits ≤ remaining ∧ PartsChecked artifact request candidate axes parts.values := by
  induction axes generalizing remaining parts with
  | nil =>
    cases Except.ok.inj checked
    exact ⟨Nat.zero_le _,True.intro⟩
  | cons axis rest ih =>
    rw [checkParts_cons] at checked
    cases hh : candidate.hadamards[axis]? with
    | none => simp [hh,bind,Except.bind] at checked
    | some h =>
      simp only [hh,bind,Except.bind] at checked
      cases hp : candidate.powers[axis]? with
      | none => simp [hp] at checked
      | some power =>
        simp only [hp] at checked
        cases ho : candidate.powerOrders[axis]? with
        | none => simp [ho] at checked
        | some order =>
          simp only [ho] at checked
          cases hc : checkPart artifact request h power axis order remaining with
          | error error => simp [hc] at checked
          | ok part =>
            simp only [hc] at checked
            cases ht : checkParts artifact request candidate (remaining-part.visits) rest with
            | error error => simp [ht] at checked
            | ok tail =>
              have same : (⟨part::tail.values,part.visits+tail.visits⟩ : Parts) = parts := by
                simpa [ht,pure,Except.pure] using checked
              subst parts
              have head := (checkPart_conditions artifact request h power axis order remaining part hc).2.2.2
              have tail := ih (remaining-part.visits) tail ht
              exact ⟨by dsimp only; omega,⟨⟨h,power,order,remaining,hh,hp,ho,hc⟩,tail.2⟩⟩

theorem inverseView_bound (artifact : Artifact) (width : Nat) (atom : CircuitTrace.Atom)
    (view : InverseView) (found : inverseView artifact width atom = some view) :
    artifact.definitions[atom.index]? = some view.definition ∧
      view.definition.body = .inverse view.child ∧
      artifact.definitions[view.child]? = some view.forward ∧
      view.definition.interface = atom.interface ∧ sized width view.definition = true := by
  unfold inverseView at found
  simp only [bind,Option.bind] at found
  repeat (split at found <;> (try dsimp only at found) <;> (try contradiction))
  all_goals
    cases Option.some.inj found
    simp only [Bool.and_eq_true,beq_iff_eq] at *
    exact ⟨by assumption,by assumption,by assumption,by simp_all,by simp_all⟩

theorem checkInverse_conditions (artifact : Artifact) (width : Nat) (atom : CircuitTrace.Atom)
    (order : Array Nat) (remaining : Nat) (inverse : Inverse)
    (checked : checkInverse artifact width atom order remaining = .ok inverse) :
    inverseView artifact width atom = some inverse.view ∧
      FourierRoot.inspect (atEntry artifact inverse.view.child) ⟨width,inverse.view.forward.interface⟩
        order remaining = .ok inverse.fourier ∧
      inverse.visits = inverse.fourier.visits ∧ inverse.visits ≤ remaining := by
  unfold checkInverse at checked
  split at checked
  next absent => contradiction
  next view found =>
    split at checked
    next failed => contradiction
    next fourier checkedFourier =>
      cases Except.ok.inj checked
      exact ⟨found,checkedFourier,rfl,(FourierRoot.inspect_conditions _ _ _ _ _ checkedFourier).1⟩

theorem inspect_conditions (artifact : Artifact) (request : Request) (candidate : Candidate)
    (remaining : Nat) (pending : Pending)
    (checked : inspect artifact request candidate remaining = .ok pending) :
    layout request = true ∧ candidate.hadamards.size = request.phase.size ∧
      candidate.powers.size = request.phase.size ∧ candidate.powerOrders.size = request.phase.size ∧
      (∃ d, artifact.definitions[artifact.entry.implementation]? = some d ∧
        d.interface = request.interface ∧ sized (request.phase.size+request.target.size) d = true) ∧
      checkParts artifact request candidate (remaining-workCharge artifact request candidate)
        (List.range request.phase.size) = .ok pending.parts ∧
      checkInverse artifact request.phase.size candidate.inverseFourier candidate.fourierOrder
        (remaining-workCharge artifact request candidate-pending.parts.visits) = .ok pending.inverse ∧
      CircuitTrace.inspect artifact (atoms candidate) candidate.traceOrder
        (remaining-workCharge artifact request candidate-pending.parts.visits-pending.inverse.visits) = .ok pending.trace ∧
      (pending.trace.cache[artifact.entry.implementation]?).bind id = some (expected request candidate) ∧
      pending.visits = workCharge artifact request candidate+pending.parts.visits+pending.inverse.visits+pending.trace.visits ∧
      pending.visits ≤ remaining ∧ remaining ≤ 2000000 := by
  unfold inspect at checked
  split at checked
  next exceeded => contradiction
  next header =>
    split at checked
    next malformed => contradiction
    next shape =>
      dsimp only at checked
      split at checked
      next exceeded => contradiction
      next charged =>
        split at checked
        next invalid => contradiction
        next geometry =>
          split at checked
          next absent => contradiction
          next d found =>
            split at checked
            next invalid => contradiction
            next aligned =>
              split at checked
              next failed => contradiction
              next parts checkedParts =>
                split at checked
                next failed => contradiction
                next inverse checkedInverse =>
                  split at checked
                  next failed => contradiction
                  next trace checkedTrace =>
                    split at checked
                    next mismatch => contradiction
                    next matched =>
                      cases Except.ok.inj checked
                      have pb := (checkParts_conditions _ _ _ _ _ _ checkedParts).1
                      have ib := (checkInverse_conditions _ _ _ _ _ _ checkedInverse).2.2.2
                      have tb := (CircuitTrace.inspect_sound _ _ _ _ _ checkedTrace).2.1
                      simp only [Bool.or_eq_true,Bool.not_eq_true',Bool.not_eq_false,
                        bne_iff_ne,decide_eq_true_eq,not_or,Classical.not_not] at header shape geometry aligned matched
                      exact ⟨geometry,shape.1.1.2,shape.1.2,shape.2,
                        ⟨d,found,aligned.1,aligned.2⟩,checkedParts,checkedInverse,checkedTrace,matched,rfl,
                        by dsimp only; omega,by omega⟩

/-- The actual schedule is reconstructed; no caller trace or submitted success
flag occurs in the conclusion. Its component equations remain explicit. -/
theorem inspect_derives (artifact : Artifact) (request : Request) (candidate : Candidate)
    (remaining : Nat) (pending : Pending)
    (checked : inspect artifact request candidate remaining = .ok pending) :
    CircuitTrace.Derives artifact (atoms candidate) artifact.entry.implementation (expected request candidate) := by
  have facts := inspect_conditions artifact request candidate remaining pending checked
  exact (CircuitTrace.inspect_sound _ _ _ _ _ facts.2.2.2.2.2.2.2.1).1 _ _ facts.2.2.2.2.2.2.2.2.1

end QleisliKernel.Hierarchical.QpeSchedule
