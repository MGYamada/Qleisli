import QleisliKernel.Semantics.Qirf
import QleisliKernel.Raw.BranchFunction
import QleisliKernel.Hierarchical.Graph

/-! Fresh QIRF graph reconstruction. Original table indices, complete raw
bodies and source identity data are retained; no host receipts are inputs.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf
open Semantics.Exact Semantics.Finite Semantics.Observation Semantics.ObservingFunction Finite

def nodes (artifact : Artifact) : Hierarchical.Graph.Nodes :=
  artifact.programs.map (fun program =>
    (references 65 program.operations).map (artifact.programs.size + ·)) ++
  artifact.entries.map (fun entry => entry.implementation :: match entry.target with
    | .circuit index => [index] | _ => [])

def sourceValid (source : String × String) : Bool :=
  !source.1.isEmpty && source.1.utf8ByteSize ≤ 4096 && !source.1.contains '\x00'

def identity (artifact : Artifact) (entry : Entry) : WorkM Semantics.Function.Identity := do
  guard (entry.sources.length ≤ 128) .limit
  guard (Raw.unique entry.sources && entry.sources.all (· < artifact.sources.size))
  let identity : Semantics.Function.Identity := ⟨entry.implementationName,entry.specificationName,
    entry.sources.map (fun index => artifact.sources[index]?.getD ("",""))⟩
  guard (Raw.Function.identityValid identity) .limit
  return identity

/-- The independent meaning is the entire mathematical table, not a name or
producer extraction. Its canonical circuit uses the published low-axis order. -/
def meaningProgram (signature : Basis) (target : Target) : WorkM Program := do
  guard (basisValid signature) .limit
  let bits := width signature
  let (permutation,phases) ← match target with
    | .permutation table => do
      guard (table.length == 2^bits && table.all (· < 2^bits) && Raw.unique table)
      pure (table,List.replicate table.length 0)
    | .phase8 table => do
      guard (table.length == 2^bits && table.all (· < 8))
      pure (List.range table.length,table)
    | .circuit _ => throw .invalid
  let step : Step := ⟨[],.monomial (List.range bits) permutation phases⟩
  return ⟨[⟨0,List.range bits,bits⟩],[],[.pure (.applyUnitary 0 1 [step])],[1],[],.unitary⟩

def input (artifact : Artifact) (entry : Entry) : WorkM Input := do
  let implementation ← lift (readOption artifact.programs[entry.implementation]?)
  let specification ← match entry.target with
    | .circuit index => lift (readOption artifact.programs[index]?)
    | target => meaningProgram entry.signature target
  return ⟨entry.signature,implementation,specification,← identity artifact entry⟩

def emptyReceipt : Receipt :=
  ⟨⟨[],⟨[],[],[],[],[],.unitary⟩,⟨[],[],[],[],[],.unitary⟩,⟨"","",[]⟩⟩,⟨0,0,[]⟩,0,0⟩

/-- Holes retain ORIGINAL evidence indices. Every reference in BOTH arms must
name a fresh receipt before any dependency vector is passed to a raw checker. -/
def ready (receipts : Array (Option Receipt)) (program : Program) : Bool :=
  (references 65 program.operations).all (fun index => (receipts[index]?.join).isSome)

abbrev Slots := Array (Option Receipt)

def before (receipts : Slots) : List Receipt :=
  receipts.toList.map (fun receipt => receipt.getD emptyReceipt)

def checkNode (artifact : Artifact) (receipts : Slots) (node : Nat) : WorkM Slots := do
  exactWork (Exact.charge (1 + receipts.size))
  if node < artifact.programs.size then
    let program ← lift (readOption artifact.programs[node]?)
    guard (ready receipts program)
    let _ ← Raw.Observation.verify ((before receipts).map Receipt.dependency) program
    pure receipts
  else
    let index := node - artifact.programs.size
    let entry ← lift (readOption artifact.entries[index]?)
    let actual ← input artifact entry
    guard (ready receipts actual.implementation && ready receipts actual.specification)
    let receipt ← Raw.BranchFunction.checkEntry (before receipts) actual actual
    pure (receipts.set! index (some receipt))

/-- Execution witnesses retain original indices and the precise freshly built
dependency snapshot at each node. They are propositions, not submitted data. -/
inductive CheckedNode (artifact : Artifact) : Slots → Nat → Slots → Prop
  | program (slots node program checked work left)
      (found : artifact.programs[node]? = some program)
      (ready : ready slots program = true)
      (verified : (Raw.Observation.verify ((before slots).map Receipt.dependency) program).run work =
        (.ok checked,left)) : CheckedNode artifact slots node slots
  | entry (slots node entry actual receipt a b c d)
      (outside : artifact.programs.size ≤ node)
      (found : artifact.entries[node - artifact.programs.size]? = some entry)
      (decoded : (input artifact entry).run a = (.ok actual,b))
      (ready : ready slots actual.implementation = true ∧ ready slots actual.specification = true)
      (verified : (Raw.BranchFunction.checkEntry (before slots) actual actual).run c = (.ok receipt,d)) :
      CheckedNode artifact slots node (slots.set! (node - artifact.programs.size) (some receipt))

inductive CheckedGraph (artifact : Artifact) : Slots → List Nat → Slots → Prop
  | nil (slots) : CheckedGraph artifact slots [] slots
  | cons (slots node rest next final)
      (checked : CheckedNode artifact slots node next)
      (remaining : CheckedGraph artifact next rest final) :
      CheckedGraph artifact slots (node :: rest) final

def checkGraph (artifact : Artifact) (order : Array Nat) : WorkM (List Dependency) := do
  guard ((← get) ≤ 10000000) .limit
  guard (artifact.programs.size + artifact.entries.size ≤ 65536 && artifact.sources.size ≤ 128) .limit
  guard (artifact.sources.all sourceValid && Raw.unique (artifact.sources.toList.map (·.1)))
  guard ((artifact.sources.toList.map (fun source => source.2.utf8ByteSize)).sum ≤ 1048576) .limit
  guard (artifact.entries.all fun entry => entry.sources.length ≤ 128 &&
    entry.sources.all (· < artifact.sources.size))
  exactWork (Exact.charge (artifact.entries.size +
    (artifact.entries.toList.map (fun entry => entry.sources.length)).sum))
  let used := artifact.entries.foldl (fun used entry =>
    entry.sources.foldl (fun used index => used.set! index true) used)
    (Array.replicate artifact.sources.size false)
  guard (used.all id)
  let identityBytes := (artifact.entries.toList.map (fun entry =>
    entry.implementationName.utf8ByteSize + entry.specificationName.utf8ByteSize)).sum +
    ((List.range artifact.sources.size).filter (fun index => used[index]?.getD false) |>.map (fun index =>
      let source := artifact.sources[index]?.getD ("","")
      source.1.utf8ByteSize + source.2.utf8ByteSize)).sum
  guard (identityBytes ≤ 1048576) .limit
  let schedule ← lift (match Hierarchical.Graph.check (nodes artifact) [artifact.root] order with
    | .ok schedule => .ok schedule
    | .error error => .error (if error.kind == .limit then .limit else .invalid))
  guard (schedule.stats.depth ≤ 32) .limit
  exactWork (Exact.charge schedule.stats.visits)
  let receipts ← order.toList.foldlM (checkNode artifact) (Array.replicate artifact.entries.size none)
  guard (receipts.all Option.isSome)
  return receipts.toList.map (fun receipt => (receipt.getD emptyReceipt).dependency)

def reconstruct (artifact : Artifact) (order : Array Nat) (signature : Basis)
    (inputPort outputPort : Semantics.Raw.Port) : WorkM Matrix := do
  let dependencies ← checkGraph artifact order
  guard (basisValid signature) .request
  guard (artifact.rootInterface == some (signature,signature)) .request
  let program ← lift (readOption artifact.programs[artifact.root]?)
  guard (program.inputs == [inputPort] && program.outputs == [outputPort.token] &&
    program.classicalInputs.isEmpty && program.classicalOutputs.isEmpty && program.effect == .unitary) .request
  let checked ← Raw.Observation.verify dependencies program
  guard (checked.state.quantum.live == [outputPort]) .request
  let actual ← Raw.BranchFunction.reconstruct dependencies program
  wholeSpace actual
  return actual

def check (artifact : Artifact) (order : Array Nat) (signature : Basis)
    (inputPort outputPort : Semantics.Raw.Port) (required : Matrix) : WorkM Matrix := do
  let actual ← reconstruct artifact order signature inputPort outputPort
  exactWork (Exact.charge actual.entries.length)
  guard (actual == required) .equation
  return actual

theorem checkNode_fresh (artifact : Artifact) (slots next : Slots) (node work left : Nat)
    (ok : (checkNode artifact slots node).run work = (.ok next,left)) :
    CheckedNode artifact slots node next := by
  obtain ⟨_,w₁,_,h⟩ := bind_success _ _ _ _ _ ok
  change ((if node < artifact.programs.size then _ else _) : WorkM Slots).run w₁ = _ at h
  split at h
  next inside =>
    obtain ⟨program,w₂,hp,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨_,w₃,hr,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨checked,w₄,hv,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    subst next
    have found := (lift_success _ _ _ _ hp).1
    have present : artifact.programs[node]? = some program := by
      cases hf : artifact.programs[node]? <;> simp_all [readOption]
    exact .program slots node program checked w₃ w₄ present (guard_success _ _ _ _ hr).1 hv
  next outside =>
    obtain ⟨entry,w₂,he,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨actual,w₃,hi,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨_,w₄,hr,h⟩ := bind_success _ _ _ _ _ h
    obtain ⟨receipt,w₅,hv,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    subst next
    have found := (lift_success _ _ _ _ he).1
    have present : artifact.entries[node - artifact.programs.size]? = some entry := by
      cases hf : artifact.entries[node - artifact.programs.size]? <;> simp_all [readOption]
    exact .entry slots node entry actual receipt w₂ w₃ w₄ w₅ (Nat.le_of_not_lt outside) present hi
      (by simpa only [Bool.and_eq_true] using (guard_success _ _ _ _ hr).1) hv

theorem fold_fresh (artifact : Artifact) (nodes : List Nat) (slots final : Slots) (work left : Nat)
    (ok : (nodes.foldlM (checkNode artifact) slots).run work = (.ok final,left)) :
    CheckedGraph artifact slots nodes final := by
  induction nodes generalizing slots work with
  | nil =>
    simp only [List.foldlM_nil] at ok
    rw [(pure_success _ _ _ _ ok).1]
    exact .nil _
  | cons node rest ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨next,middle,checked,remaining⟩ := bind_success _ _ _ _ _ ok
    exact .cons _ _ _ _ _ (checkNode_fresh _ _ _ _ _ _ checked) (ih next middle remaining)

theorem checkGraph_fresh (artifact : Artifact) (order : Array Nat) (dependencies : List Dependency)
    (work left : Nat) (ok : (checkGraph artifact order).run work = (.ok dependencies,left)) :
    ∃ slots, CheckedGraph artifact (Array.replicate artifact.entries.size none) order.toList slots ∧
      slots.all Option.isSome = true ∧ dependencies = (before slots).map Receipt.dependency := by
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨slots,middle,hf,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,hg,h⟩ := bind_success _ _ _ _ _ h
  exact ⟨slots,fold_fresh _ _ _ _ _ _ hf,(guard_success _ _ _ _ hg).1,
    by simpa [before,List.map_map,Function.comp_def] using (pure_success _ _ _ _ h).1⟩

theorem checkGraph_schedule (artifact : Artifact) (order : Array Nat) (dependencies : List Dependency)
    (work left : Nat) (ok : (checkGraph artifact order).run work = (.ok dependencies,left)) :
    ∃ schedule, Hierarchical.Graph.check (nodes artifact) [artifact.root] order = .ok schedule ∧
      schedule.stats.depth ≤ 32 := by
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨schedule,_,hs,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,hd,_⟩ := bind_success _ _ _ _ _ h
  have found := (lift_success _ _ _ _ hs).1
  have present : Hierarchical.Graph.check (nodes artifact) [artifact.root] order = .ok schedule := by
    cases hg : Hierarchical.Graph.check (nodes artifact) [artifact.root] order <;> simp_all
  exact ⟨schedule,present,of_decide_eq_true (guard_success _ _ _ _ hd).1⟩

theorem reconstruct_conditions (artifact : Artifact) (order : Array Nat) (signature : Basis)
    (inputPort outputPort : Semantics.Raw.Port) (actual : Matrix) (work left : Nat)
    (ok : (reconstruct artifact order signature inputPort outputPort).run work = (.ok actual,left)) :
    ∃ dependencies program checked a b c d e f g h,
      (checkGraph artifact order).run a = (.ok dependencies,b) ∧
      artifact.rootInterface = some (signature,signature) ∧
      artifact.programs[artifact.root]? = some program ∧
      program.inputs = [inputPort] ∧ program.outputs = [outputPort.token] ∧
      program.classicalInputs = [] ∧ program.classicalOutputs = [] ∧ program.effect = .unitary ∧
      (Raw.Observation.verify dependencies program).run c = (.ok checked,d) ∧
      checked.state.quantum.live = [outputPort] ∧
      (Raw.BranchFunction.reconstruct dependencies program).run e = (.ok actual,f) ∧
      (wholeSpace actual).run g = (.ok (),h) := by
  obtain ⟨dependencies,w₁,hg,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₃,hi,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨program,w₄,hp,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₅,hb,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨checked,w₆,hv,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₇,ho,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨result,w₈,hr,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₉,hu,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst actual
  have header := (guard_success _ _ _ _ hb).1
  simp only [Bool.and_eq_true,beq_iff_eq,List.isEmpty_iff,and_assoc] at header
  have present : artifact.programs[artifact.root]? = some program := by
    have found := (lift_success _ _ _ _ hp).1
    cases hf : artifact.programs[artifact.root]? <;> simp_all [readOption]
  exact ⟨dependencies,program,checked,work,w₁,w₅,w₆,w₇,w₈,w₈,w₉,hg,
    beq_iff_eq.mp (guard_success _ _ _ _ hi).1,present,header.1,header.2.1,
    header.2.2.1,header.2.2.2.1,header.2.2.2.2,hv,
    beq_iff_eq.mp (guard_success _ _ _ _ ho).1,hr,hu⟩

theorem check_reconstruct (artifact : Artifact) (order : Array Nat) (signature : Basis)
    (inputPort outputPort : Semantics.Raw.Port) (required actual : Matrix) (work left : Nat)
    (ok : (check artifact order signature inputPort outputPort required).run work = (.ok actual,left)) :
    actual = required ∧ ∃ middle,
      (reconstruct artifact order signature inputPort outputPort).run work = (.ok actual,middle) := by
  obtain ⟨result,w₁,hr,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₃,hg,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst actual
  exact ⟨beq_iff_eq.mp (guard_success _ _ _ _ hg).1,w₁,hr⟩

theorem check_equation (artifact : Artifact) (order : Array Nat) (signature : Basis)
    (inputPort outputPort : Semantics.Raw.Port) (required actual : Matrix) (work left : Nat)
    (ok : (check artifact order signature inputPort outputPort required).run work = (.ok actual,left)) :
    actual = required ∧ ∃ a b,
      (reconstruct artifact order signature inputPort outputPort).run a = (.ok actual,b) := by
  obtain ⟨same,middle,reconstructed⟩ := check_reconstruct _ _ _ _ _ _ _ _ _ ok
  exact ⟨same,work,middle,reconstructed⟩

end QleisliKernel.Qirf
