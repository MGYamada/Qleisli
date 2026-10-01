import QleisliKernel.Layout
import QleisliKernel.Hierarchical.Graph

/-! Typed data and dependency/endpoint preparation for the selected hierarchy.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
Preparation is NOT semantic verification. Finite payloads, node typing,
derivations and external requests still require their independent checkers. -/

namespace QleisliKernel.Hierarchical.Artifact

instance : Repr ByteArray where
  reprPrec bytes _ := Std.Format.text s!"<finite-payload {bytes.size} bytes>"

abbrev Basis := Array Layout.TypeAtom

structure QuantumPort where
  owner : Nat
  basis : Basis
  axes : Array Nat
  deriving BEq, DecidableEq, Repr

structure ClassicalPort where
  value : Nat
  /-- At a classical port, Bit/Bits atoms denote CBit/CBits, never quantum data. -/
  basis : Basis
  deriving BEq, DecidableEq, Repr

structure Side where
  quantum : Array QuantumPort
  classical : Array ClassicalPort := #[]
  deriving BEq, DecidableEq, Repr

structure Interface where
  inputs : Side
  outputs : Side
  deriving BEq, DecidableEq, Repr

inductive Effect where
  | unitary | iso | observe
  deriving BEq, DecidableEq, Repr

/-- Maps use ordered port/flattened-axis positions; local IDs are not handles. -/
structure PortMap where
  owners : Array Nat
  axes : Array Nat
  classical : Array Nat
  deriving BEq, DecidableEq, Repr

/-- Explicit consuming/regrouping operations, distinct from type-preserving
port renaming. Empty ports still require their own create/consume operation. -/
inductive StructuralOp where
  | takeBit (width position : Nat) | putBit (width position : Nat)
  | splitTuple | joinTuple | bitToBits | bitsToBit
  | packUnit | unpackUnit | packEmptyBits | unpackEmptyBits
  deriving BEq, DecidableEq, Repr

def StructuralOp.bounded : StructuralOp → Bool
  | .takeBit width position | .putBit width position =>
    1 ≤ width && width ≤ 8 && position < width
  | _ => true

inductive Body where
  /-- Complete canonical finite packet, never an Arc, address, digest or flag.
  The finite adapter must independently reconstruct and check these bytes. -/
  | leaf (program : ByteArray)
  | sequence (children : Array Nat)
  | tensor (left right : Nat)
  | call (definition : Nat) (inputMap outputMap : PortMap)
  | repeatOp (count definition : Nat)
  | inverse (definition : Nat)
  | control (definition : Nat) (polarity : Bool)
  | rewire (permutation : PortMap)
  | structural (operation : StructuralOp)
  | dyadicPhase (target j k : Nat)
  | computed (compute useOp logical encoding : Nat)
  | observeZ (input output : Nat)
  | init0 (output : Nat)
  deriving Repr

structure Definition where
  interface : Interface
  effect : Effect
  body : Body
  deriving Repr

inductive MeaningBody where
  | identity
  | finite (description : ByteArray)
  | sequence (children : Array Nat)
  | tensor (left right : Nat)
  | inverse (child : Nat)
  | control (child : Nat) (polarity : Bool)
  | power (child count : Nat)
  | rewire (permutation : PortMap)
  | structural (operation : StructuralOp)
  | phase (j k : Nat)
  | qft (width : Nat)
  | qpeInstrument (target precision providerMeaning : Nat)
  deriving Repr

structure Meaning where
  interface : Interface
  body : MeaningBody
  deriving Repr

inductive EncodingBody where
  | identity
  | tensor (left right : Nat)
  | rewire (child : Nat) (permutation : PortMap)
  | zeroScratch (scratchBits compute : Nat)
  deriving Repr

structure Encoding where
  logical : Side
  physical : Side
  body : EncodingBody
  deriving Repr

inductive Table where
  | definition | meaning | encoding | proof
  deriving BEq, DecidableEq, Repr

structure Ref where
  table : Table
  index : Nat
  deriving BEq, DecidableEq, Repr

inductive Kind where
  | equation | instrument
  deriving BEq, DecidableEq, Repr

inductive Rule where
  | finite | sequence | tensor | inverse | control | repeatOp | associativity
  | rewire | structural | phase | computed | conjugation
  | schema (id : String)
  deriving BEq, DecidableEq, Repr

/-- Witnesses can only select bounded data, never Lean expressions or code.
Every witness reference is included in the actual dependency graph. -/
structure Witness where
  templateVersion : Nat
  parameters : Array Nat
  references : Array Ref
  deriving Repr

structure Proof where
  kind : Kind
  rule : Rule
  premises : Array Nat
  implementation : Nat
  meaning : Nat
  inputEncoding : Nat
  outputEncoding : Nat
  witness : Witness
  deriving Repr

structure Entry where
  implementation : Nat
  proof : Nat
  deriving Repr

structure Artifact where
  definitions : Array Definition
  meanings : Array Meaning
  encodings : Array Encoding
  proofs : Array Proof
  entry : Entry
  deriving Repr

def tableSize (artifact : Artifact) : Table → Nat
  | .definition => artifact.definitions.size
  | .meaning => artifact.meanings.size
  | .encoding => artifact.encodings.size
  | .proof => artifact.proofs.size

def offset (artifact : Artifact) : Table → Nat
  | .definition => 0
  | .meaning => artifact.definitions.size
  | .encoding => artifact.definitions.size + artifact.meanings.size
  | .proof => artifact.definitions.size + artifact.meanings.size + artifact.encodings.size

/-- Check the referenced table BEFORE adding its offset. An out-of-range
definition cannot alias an in-range meaning at the same flattened position. -/
def index (artifact : Artifact) (ref : Ref) : Option Nat :=
  if ref.index < tableSize artifact ref.table then some (offset artifact ref.table + ref.index)
  else none

theorem index_bound (artifact : Artifact) (ref : Ref) (flat : Nat)
    (found : index artifact ref = some flat) :
    ref.index < tableSize artifact ref.table ∧ flat = offset artifact ref.table + ref.index := by
  unfold index at found
  split at found
  next inside => exact ⟨inside, (Option.some.inj found).symm⟩
  next outside => contradiction

def Body.references : Body → Array Ref
  | .leaf _ | .rewire _ | .structural _ | .dyadicPhase _ _ _ | .observeZ _ _ | .init0 _ => #[]
  | .sequence children => children.map (⟨.definition, ·⟩)
  | .tensor left right => #[⟨.definition, left⟩, ⟨.definition, right⟩]
  | .call child _ _ | .repeatOp _ child | .inverse child | .control child _ => #[⟨.definition, child⟩]
  | .computed compute useOp logical encoding =>
    #[⟨.definition, compute⟩, ⟨.definition, useOp⟩, ⟨.meaning, logical⟩, ⟨.encoding, encoding⟩]

def Body.referenceCount : Body → Nat
  | .sequence children => children.size
  | .tensor _ _ => 2
  | .call _ _ _ | .repeatOp _ _ | .inverse _ | .control _ _ => 1
  | .computed _ _ _ _ => 4
  | _ => 0

def MeaningBody.references : MeaningBody → Array Ref
  | .identity | .finite _ | .rewire _ | .structural _ | .phase _ _ | .qft _ => #[]
  | .sequence children => children.map (⟨.meaning, ·⟩)
  | .tensor left right => #[⟨.meaning, left⟩, ⟨.meaning, right⟩]
  | .inverse child | .control child _ | .power child _ | .qpeInstrument _ _ child => #[⟨.meaning, child⟩]

def MeaningBody.referenceCount : MeaningBody → Nat
  | .sequence children => children.size
  | .tensor _ _ => 2
  | .inverse _ | .control _ _ | .power _ _ | .qpeInstrument _ _ _ => 1
  | _ => 0

def EncodingBody.references : EncodingBody → Array Ref
  | .identity => #[]
  | .tensor left right => #[⟨.encoding, left⟩, ⟨.encoding, right⟩]
  | .rewire child _ => #[⟨.encoding, child⟩]
  | .zeroScratch _ compute => #[⟨.definition, compute⟩]

def EncodingBody.referenceCount : EncodingBody → Nat
  | .identity => 0
  | .tensor _ _ => 2
  | _ => 1

def Proof.references (proof : Proof) : Array Ref :=
  #[⟨.definition, proof.implementation⟩, ⟨.meaning, proof.meaning⟩,
    ⟨.encoding, proof.inputEncoding⟩, ⟨.encoding, proof.outputEncoding⟩] ++
    proof.premises.map (⟨.proof, ·⟩) ++ proof.witness.references

def Proof.referenceCount (proof : Proof) : Nat := 4 + proof.premises.size + proof.witness.references.size

/-- Zero repetitions keep their actual body edge. -/
theorem repeat_references (count definition : Nat) :
    (Body.repeatOp count definition).references = #[⟨.definition, definition⟩] := rfl

def totalNodes (artifact : Artifact) : Nat := offset artifact .proof + artifact.proofs.size

def u32 (value : Nat) : Bool := value ≤ 4294967295

def basisValid (basis : Basis) : Bool :=
  if basis.size > 128 then false else (Layout.basisWidth basis.toList).isSome

def wires (side : Side) : Array Nat := side.quantum.foldl (fun axes port => axes ++ port.axes) #[]

def sideScan (side : Side) : Nat := side.quantum.size + side.classical.size

/-- This cost is charged before the quadratic uniqueness and type comparisons. -/
def sideCharge (side : Side) : Nat :=
  let ports := side.quantum.size + side.classical.size
  1 + 4 * ports * ports + side.quantum.foldl (fun cost p => cost + 4 * p.basis.size + 4 * p.axes.size) 0 +
    side.classical.foldl (fun cost p => cost + 4 * p.basis.size) 0

/-- Complete serialized fields used for equality-only scans. This does not
validate types, uniqueness, permutations or quantum ownership. -/
def sideFields (side : Side) : Nat :=
  1 + side.quantum.foldl (fun n p => n + 3 + 2*p.basis.size + p.axes.size) 0 +
    side.classical.foldl (fun n p => n + 2 + 2*p.basis.size) 0

def sideValid (side : Side) : Bool :=
  if side.quantum.foldl (fun count p => count + p.axes.size) 0 > 16 then false else
  side.quantum.all (fun p => u32 p.owner && p.axes.size ≤ 16 && basisValid p.basis &&
    Layout.basisWidth p.basis.toList == some p.axes.size && p.axes.all u32) &&
  side.classical.all (fun p => u32 p.value && basisValid p.basis) &&
  (wires side).size ≤ 16 && decide (side.quantum.toList.map QuantumPort.owner).Nodup &&
  decide (side.classical.toList.map ClassicalPort.value).Nodup && decide (wires side).toList.Nodup

def Interface.valid (interface : Interface) : Bool :=
  sideValid interface.inputs && sideValid interface.outputs

def Interface.charge (interface : Interface) : Nat :=
  sideCharge interface.inputs + sideCharge interface.outputs

def Interface.scan (interface : Interface) : Nat := sideScan interface.inputs + sideScan interface.outputs

def mapCharge (map : PortMap) : Nat := 1 + map.owners.size + map.axes.size + map.classical.size

def mapBounded (map : PortMap) : Bool := map.owners.all u32 && map.axes.all u32 && map.classical.all u32

def angleValid (j k : Nat) : Bool := if k > 8 then false else j < 2^k

def Body.charge : Body → Nat
  | .call _ input output => 1 + mapCharge input + mapCharge output
  | .rewire permutation => 1 + mapCharge permutation
  | .sequence children => 1 + children.size
  | _ => 1

def Body.bounded : Body → Bool
  | .structural operation => operation.bounded
  | .leaf bytes => !bytes.isEmpty
  | .sequence children => !children.isEmpty
  | .repeatOp count _ => count ≤ 4096
  | .call _ input output => mapBounded input && mapBounded output
  | .rewire permutation => mapBounded permutation
  | .dyadicPhase target j k => u32 target && angleValid j k
  | .observeZ input output => u32 input && u32 output
  | .init0 output => u32 output
  | _ => true

def MeaningBody.charge : MeaningBody → Nat
  | .rewire permutation => 1 + mapCharge permutation
  | .sequence children => 1 + children.size
  | _ => 1

def MeaningBody.bounded : MeaningBody → Bool
  | .structural operation => operation.bounded
  | .finite bytes => !bytes.isEmpty
  | .sequence children => !children.isEmpty
  | .power _ count => count ≤ 4096
  | .rewire permutation => mapBounded permutation
  | .phase j k => angleValid j k
  | .qft width => 1 ≤ width && width ≤ 8
  | .qpeInstrument n m _ => 1 ≤ n && n ≤ 8 && 1 ≤ m && m ≤ 8 && n + m ≤ 16
  | _ => true

def EncodingBody.charge : EncodingBody → Nat
  | .rewire _ permutation => 1 + mapCharge permutation
  | _ => 1

def EncodingBody.bounded : EncodingBody → Bool
  | .zeroScratch scratch _ => scratch ≤ 16
  | .rewire _ permutation => mapBounded permutation
  | _ => true

def Rule.known : Rule → Bool
  | .schema id => id == "qft-dyadic8/1" || id == "controlled-power/1" || id == "qpe-instrument/1"
  | _ => true

def Proof.bounded (proof : Proof) : Bool :=
  proof.rule.known && proof.witness.templateVersion == 1 && proof.witness.parameters.all u32

/-- Shared endpoints are compared per proof, so their cost is not free merely
because the declarations were checked once. All lookups are table-specific. -/
def endpointCost (cost : Side → Nat) (artifact : Artifact) (proof : Proof) : Nat :=
  let definition := artifact.definitions[proof.implementation]?
  let meaning := artifact.meanings[proof.meaning]?
  let input := artifact.encodings[proof.inputEncoding]?
  let output := artifact.encodings[proof.outputEncoding]?
  4 + (definition.map (fun d => cost d.interface.inputs + cost d.interface.outputs)).getD 0 +
    (meaning.map (fun m => cost m.interface.inputs + cost m.interface.outputs)).getD 0 +
    (input.map (fun e => cost e.logical + cost e.physical)).getD 0 +
    (output.map (fun e => cost e.logical + cost e.physical)).getD 0

def BoundEndpoints (implementation : Definition) (meaning : Meaning) (input output : Encoding) : Prop :=
  input.logical = meaning.interface.inputs ∧ input.physical = implementation.interface.inputs ∧
  output.logical = meaning.interface.outputs ∧ output.physical = implementation.interface.outputs

instance (implementation : Definition) (meaning : Meaning) (input output : Encoding) :
    Decidable (BoundEndpoints implementation meaning input output) := by
  unfold BoundEndpoints
  infer_instance

def endpointKind (proof : Proof) (implementation : Definition) (meaning : Meaning)
    (input output : Encoding) : Bool :=
  match proof.kind, meaning.body, input.body, output.body with
  | .instrument, .qpeInstrument _ _ _, .identity, .identity =>
    decide (implementation.effect = .observe ∧ input.logical = input.physical ∧ output.logical = output.physical)
  | .equation, .qpeInstrument _ _ _, _, _ => false
  | .equation, _, _, _ => decide (implementation.effect ≠ .observe)
  | _, _, _, _ => false

/-- Bind every proof endpoint to complete actual interfaces, never dimensions.
This is a necessary precondition, NOT validation of a derivation or witness. -/
def endpoints (artifact : Artifact) (proof : Proof) : Bool :=
  (do
    let implementation ← artifact.definitions[proof.implementation]?
    let meaning ← artifact.meanings[proof.meaning]?
    let input ← artifact.encodings[proof.inputEncoding]?
    let output ← artifact.encodings[proof.outputEncoding]?
    return decide (BoundEndpoints implementation meaning input output) &&
      endpointKind proof implementation meaning input output).getD false

theorem endpoints_bound (artifact : Artifact) (proof : Proof)
    (implementation : Definition) (meaning : Meaning) (input output : Encoding)
    (hd : artifact.definitions[proof.implementation]? = some implementation)
    (hm : artifact.meanings[proof.meaning]? = some meaning)
    (hi : artifact.encodings[proof.inputEncoding]? = some input)
    (ho : artifact.encodings[proof.outputEncoding]? = some output)
    (accepted : endpoints artifact proof = true) :
    BoundEndpoints implementation meaning input output := by
  simp [endpoints, hd, hm, hi, ho, bind, pure] at accepted
  exact accepted.1

inductive Error where
  | limit | invalidIr | contract
  deriving BEq, DecidableEq, Repr

structure Failure where
  kind : Error
  atNode : Option Ref
  deriving Repr

structure Projection where
  nodes : Graph.Nodes := #[]
  visits : Nat := 0
  payloadBytes : Nat := 0
  deriving Repr

/-- A bounded helper returns graph edges in their actual order. The caller
charges list allocation and table lookups; no producer edge list is accepted. -/
def flattenRefs (artifact : Artifact) (refs : Array Ref) : Option (List Nat) :=
  refs.toList.mapM (index artifact)

def add (artifact : Artifact) (atNode : Ref) (state : Projection) (referenceCount scan bytes : Nat)
    (charge : Unit → Nat) (refs : Unit → Array Ref) (valid : Unit → Bool) : Except Failure Projection := do
  if state.visits + scan + 4 * referenceCount + 1 > Limits.maxVisits then throw ⟨.limit, some atNode⟩
  let visits := state.visits + scan + charge () + 4 * referenceCount + 1
  let payloadBytes := state.payloadBytes + bytes
  if visits > Limits.maxVisits || payloadBytes > Limits.maxPayloadBytes then throw ⟨.limit, some atNode⟩
  if !valid () then throw ⟨.invalidIr, some atNode⟩
  let some edges := flattenRefs artifact (refs ()) | throw ⟨.invalidIr, some atNode⟩
  return ⟨state.nodes.push edges, visits, payloadBytes⟩

/-- A total row iterator keeps the original table/index order and shared
budget. It allocates no auxiliary list and does not expand bodies. -/
private def projectRows (step : Projection → Nat → Except Failure Projection)
    (count first : Nat) (state : Projection) : Except Failure Projection :=
  Nat.rec (motive := fun _ => Nat → Projection → Except Failure Projection)
    (fun _ state => .ok state)
    (fun _ rest first state => do
      let next ← step state first
      rest (first + 1) next) count first state

private def projectDefinition (artifact : Artifact) (state : Projection) (i : Nat) :
    Except Failure Projection := do
  let some definition := artifact.definitions[i]? | throw ⟨.invalidIr, some ⟨.definition, i⟩⟩
  let bytes := match definition.body with | .leaf program => program.size | _ => 0
  add artifact ⟨.definition, i⟩ state definition.body.referenceCount definition.interface.scan bytes
    (fun _ => definition.interface.charge + definition.body.charge) (fun _ => definition.body.references)
    (fun _ => definition.interface.valid && definition.body.bounded)

private def projectMeaning (artifact : Artifact) (state : Projection) (i : Nat) :
    Except Failure Projection := do
  let some meaning := artifact.meanings[i]? | throw ⟨.invalidIr, some ⟨.meaning, i⟩⟩
  let bytes := match meaning.body with | .finite description => description.size | _ => 0
  add artifact ⟨.meaning, i⟩ state meaning.body.referenceCount meaning.interface.scan bytes
    (fun _ => meaning.interface.charge + meaning.body.charge) (fun _ => meaning.body.references)
    (fun _ => meaning.interface.valid && meaning.body.bounded)

private def projectEncoding (artifact : Artifact) (state : Projection) (i : Nat) :
    Except Failure Projection := do
  let some encoding := artifact.encodings[i]? | throw ⟨.invalidIr, some ⟨.encoding, i⟩⟩
  add artifact ⟨.encoding, i⟩ state encoding.body.referenceCount
    (sideScan encoding.logical + sideScan encoding.physical) 0
    (fun _ => sideCharge encoding.logical + sideCharge encoding.physical + encoding.body.charge)
    (fun _ => encoding.body.references)
    (fun _ => sideValid encoding.logical && sideValid encoding.physical && encoding.body.bounded)

private def projectProof (artifact : Artifact) (state : Projection) (i : Nat) :
    Except Failure Projection := do
  let some proof := artifact.proofs[i]? | throw ⟨.invalidIr, some ⟨.proof, i⟩⟩
  let state ← add artifact ⟨.proof, i⟩ state proof.referenceCount (endpointCost sideScan artifact proof) 0
    (fun _ => 1 + proof.witness.parameters.size + endpointCost sideCharge artifact proof)
    (fun _ => proof.references) (fun _ => proof.bounded)
  if !endpoints artifact proof then throw ⟨.contract, some ⟨.proof, i⟩⟩
  return state

/-- Projection reads all node constructors and proof fields itself. Definitions
inside count-zero repeats and all finite bytes remain present for later checks. -/
def project (artifact : Artifact) : Except Failure Projection := do
  if totalNodes artifact = 0 || totalNodes artifact > Limits.maxNodes then throw ⟨.limit, none⟩
  let state ← projectRows (projectDefinition artifact) artifact.definitions.size 0 {}
  let state ← projectRows (projectMeaning artifact) artifact.meanings.size 0 state
  let state ← projectRows (projectEncoding artifact) artifact.encodings.size 0 state
  projectRows (projectProof artifact) artifact.proofs.size 0 state

/-- Facts reconstructed by this invocation on the complete immutable artifact.
This is a proposition, never a producer-supplied flag or serialized cache. -/
def Headers (artifact : Artifact) : Prop :=
  (∀ (i : Nat) (d : Definition), artifact.definitions[i]? = some d → d.interface.valid = true) ∧
  (∀ (i : Nat) (m : Meaning), artifact.meanings[i]? = some m → m.interface.valid = true) ∧
  (∀ (i : Nat) (e : Encoding), artifact.encodings[i]? = some e →
    sideValid e.logical = true ∧ sideValid e.physical = true)

private theorem add_valid (artifact : Artifact) (atNode : Ref) (state next : Projection)
    (referenceCount scan bytes : Nat) (charge : Unit → Nat)
    (refs : Unit → Array Ref) (valid : Unit → Bool)
    (accepted : add artifact atNode state referenceCount scan bytes charge refs valid = .ok next) :
    valid () = true := by
  by_cases checked : valid () = true
  · exact checked
  · have rejected : valid () = false := by cases h : valid () <;> simp_all
    simp [add, rejected, bind, Except.bind, pure, Except.pure] at accepted
    split at accepted <;> simp_all
    split at accepted <;> simp_all

private theorem projectRows_conditions
    (step : Projection → Nat → Except Failure Projection) (condition : Nat → Prop)
    (sound : ∀ state index next, step state index = .ok next → condition index)
    (count first : Nat) (state next : Projection)
    (accepted : projectRows step count first state = .ok next) :
    ∀ i, first ≤ i → i < first + count → condition i := by
  induction count generalizing first state with
  | zero => intro i lower upper; omega
  | succ count ih =>
    cases hs : step state first with
    | error failure => simp [projectRows, hs, bind, Except.bind] at accepted
    | ok middle =>
      have rest : projectRows step count (first + 1) middle = .ok next := by
        simpa [projectRows, hs] using accepted
      intro i lower upper
      by_cases equal : i = first
      · subst i; exact sound state first middle hs
      · exact ih (first+1) middle rest i (by omega) (by omega)

private theorem projectDefinition_headers (artifact : Artifact) (state next : Projection) (i : Nat)
    (accepted : projectDefinition artifact state i = .ok next) :
    ∀ d, artifact.definitions[i]? = some d → d.interface.valid = true := by
  intro d found
  have checked := add_valid artifact ⟨.definition,i⟩ state next _ _ _ _ _ _
    (by simpa [projectDefinition, found] using accepted)
  simp only [Bool.and_eq_true] at checked
  exact checked.1

private theorem projectMeaning_headers (artifact : Artifact) (state next : Projection) (i : Nat)
    (accepted : projectMeaning artifact state i = .ok next) :
    ∀ m, artifact.meanings[i]? = some m → m.interface.valid = true := by
  intro m found
  have checked := add_valid artifact ⟨.meaning,i⟩ state next _ _ _ _ _ _
    (by simpa [projectMeaning, found] using accepted)
  simp only [Bool.and_eq_true] at checked
  exact checked.1

private theorem projectEncoding_headers (artifact : Artifact) (state next : Projection) (i : Nat)
    (accepted : projectEncoding artifact state i = .ok next) :
    ∀ e, artifact.encodings[i]? = some e →
      sideValid e.logical = true ∧ sideValid e.physical = true := by
  intro e found
  have checked := add_valid artifact ⟨.encoding,i⟩ state next _ _ _ _ _ _
    (by simpa [projectEncoding, found] using accepted)
  simp only [Bool.and_eq_true] at checked
  exact checked.1

theorem project_headers (artifact : Artifact) (projected : Projection)
    (accepted : project artifact = .ok projected) : Headers artifact := by
  unfold project at accepted
  split at accepted
  next invalid => simp [bind, Except.bind] at accepted
  next bounded =>
    simp only [bind, Except.bind, pure, Except.pure] at accepted
    cases hd : projectRows (projectDefinition artifact) artifact.definitions.size 0 {} with
    | error failure => simp [hd] at accepted
    | ok definitions =>
      simp only [hd] at accepted
      cases hm : projectRows (projectMeaning artifact) artifact.meanings.size 0 definitions with
      | error failure => simp [hm] at accepted
      | ok meanings =>
        simp only [hm] at accepted
        cases he : projectRows (projectEncoding artifact) artifact.encodings.size 0 meanings with
        | error failure => simp [he] at accepted
        | ok encodings =>
          refine ⟨?_,?_,?_⟩
          · intro i d found
            exact projectRows_conditions _ _ (fun state i next => projectDefinition_headers artifact state next i) _ _ _ _ hd i
              (Nat.zero_le _) (by simpa using (Array.getElem?_eq_some_iff.mp found).1) d found
          · intro i m found
            exact projectRows_conditions _ _ (fun state i next => projectMeaning_headers artifact state next i) _ _ _ _ hm i
              (Nat.zero_le _) (by simpa using (Array.getElem?_eq_some_iff.mp found).1) m found
          · intro i e found
            exact projectRows_conditions _ _ (fun state i next => projectEncoding_headers artifact state next i) _ _ _ _ he i
              (Nat.zero_le _) (by simpa using (Array.getElem?_eq_some_iff.mp found).1) e found

structure Prepared where
  projection : Projection
  schedule : Graph.Schedule
  totalVisits : Nat
  deriving Repr

def finish (artifact : Artifact) (projected : Projection) (order : Array Nat) : Except Failure Prepared :=
  match index artifact ⟨.definition, artifact.entry.implementation⟩ with
  | none => .error ⟨.invalidIr, some ⟨.definition, artifact.entry.implementation⟩⟩
  | some implementation =>
    match index artifact ⟨.proof, artifact.entry.proof⟩ with
    | none => .error ⟨.invalidIr, some ⟨.proof, artifact.entry.proof⟩⟩
    | some proofIndex =>
      match artifact.proofs[artifact.entry.proof]? with
      | none => .error ⟨.invalidIr, none⟩
      | some proof =>
        if proof.implementation != artifact.entry.implementation then
          .error ⟨.contract, some ⟨.proof, artifact.entry.proof⟩⟩
        else match Graph.checkWithBudget projected.nodes [implementation, proofIndex] order
            (Limits.maxVisits - projected.visits) with
          | .error failure => .error ⟨if failure.kind == .limit then .limit else .invalidIr, none⟩
          | .ok schedule =>
            let totalVisits := projected.visits + schedule.stats.visits
            if totalVisits > Limits.maxVisits then .error ⟨.limit, none⟩
            else .ok ⟨projected, schedule, totalVisits⟩

/-- Structural preparation only. No function returns semantic evidence here. -/
def prepare (artifact : Artifact) (order : Array Nat) : Except Failure Prepared :=
  match project artifact with
  | .error failure => .error failure
  | .ok projected => finish artifact projected order

theorem finish_conditions (artifact : Artifact) (projected : Projection) (order : Array Nat)
    (prepared : Prepared) (accepted : finish artifact projected order = .ok prepared) :
    prepared.projection = projected ∧ prepared.totalVisits ≤ 2000000 ∧
    ∃ roots, Graph.checkWithBudget projected.nodes roots order (2000000 - projected.visits) = .ok prepared.schedule := by
  unfold finish at accepted
  cases hd : index artifact ⟨.definition, artifact.entry.implementation⟩ with
  | none => simp [hd] at accepted
  | some implementation =>
    simp only [hd] at accepted
    cases hp : index artifact ⟨.proof, artifact.entry.proof⟩ with
    | none => simp [hp] at accepted
    | some proofIndex =>
      simp only [hp] at accepted
      cases hproof : artifact.proofs[artifact.entry.proof]? with
      | none => simp [hproof] at accepted
      | some proof =>
        simp only [hproof] at accepted
        split at accepted
        next invalid => contradiction
        next bound =>
          cases hg : Graph.checkWithBudget projected.nodes [implementation, proofIndex] order
              (2000000 - projected.visits) with
          | error failure => simp [hg] at accepted
          | ok schedule =>
            simp only [hg] at accepted
            split at accepted
            next invalid => contradiction
            next bounded =>
              cases Except.ok.inj accepted
              exact ⟨rfl, Nat.le_of_not_gt bounded, [implementation, proofIndex], hg⟩

theorem prepare_conditions (artifact : Artifact) (order : Array Nat) (prepared : Prepared)
    (accepted : prepare artifact order = .ok prepared) :
    project artifact = .ok prepared.projection ∧ prepared.totalVisits ≤ 2000000 ∧
    ∃ roots, Graph.checkWithBudget prepared.projection.nodes roots order
      (2000000 - prepared.projection.visits) = .ok prepared.schedule := by
  unfold prepare at accepted
  cases hp : project artifact with
  | error failure => simp [hp] at accepted
  | ok projected =>
    have h := finish_conditions artifact projected order prepared (by simpa [hp] using accepted)
    rw [h.1]
    exact ⟨rfl, h.2⟩

theorem prepare_headers (artifact : Artifact) (order : Array Nat) (prepared : Prepared)
    (accepted : prepare artifact order = .ok prepared) : Headers artifact :=
  project_headers artifact prepared.projection
    (prepare_conditions artifact order prepared accepted).1

/-- The checked graph is the projection of this artifact, not a supplied list.
Typed reference bounds and the remaining shared budget precede scheduling. -/
theorem prepare_acyclic (artifact : Artifact) (order : Array Nat) (prepared : Prepared)
    (accepted : prepare artifact order = .ok prepared) (node : Nat) :
    ¬Graph.Path prepared.projection.nodes node node := by
  obtain ⟨_, _, roots, checked⟩ := prepare_conditions artifact order prepared accepted
  exact Graph.checkWithBudget_acyclic _ roots order _ prepared.schedule checked node

end QleisliKernel.Hierarchical.Artifact
