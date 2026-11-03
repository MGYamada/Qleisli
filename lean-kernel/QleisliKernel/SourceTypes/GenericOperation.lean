import QleisliKernel.SourceTypes.GenericLexicalNatural
import QleisliKernel.SourceTypes.OperationDescription
import QleisliKernel.SourceTypes.OperationPaths
import QleisliKernel.SourceTypes.SourceMeaning
import QleisliKernel.SourceTypes.StaticApplication
import QleisliKernel.Semantics.SymbolicBasis

/-! Original operation closures before a particular static instantiation.
The existing symbolic source traversal constructs these values; this module
parses no source grammar and certifies no Meaning or implementation path.
Closed conversion produces the existing OperationDescription, retaining actual
children, original mixed formal identities and universally constant Nat proofs.
No chosen value for an unrelated original formal participates in conversion.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.GenericOperation
open Finite Semantics.SourceAffine Semantics.SymbolicBasis

inductive Key where
  | basis (original : Parameter)
  | natural (original : Parameter)
  | operation (original : Parameter)
  deriving BEq, DecidableEq, Repr

/-- The original lexical environment includes alias meanings, helper routes
and guard premises. Its header is never replaced by a selected signature. -/
structure Origin (sources : Sources) where
  state : GenericLexicalNatural.SomeEnvironment sources
  scope : List String
  tokens : List LocatedToken
  offset : Nat
  located : tokens.head?.map (·.span.startByte) = some offset
  rows : List (String × String)

def readOrigin {sources} (state : GenericLexicalNatural.SomeEnvironment sources)
    (scope : List String) (tokens : List LocatedToken) (rows : List (String × String)) :
    WorkM (Origin sources) := do
  exactWork (Exact.charge (8*(tokens.length+scope.length+rows.length+1)))
  match located : tokens.head?.map (·.span.startByte) with
  | none => throw .request
  | some offset => return ⟨state,scope,tokens,offset,located,rows⟩

structure Count where
  form : Form
  powerTwo : Bool := false
  deriving BEq, DecidableEq, Repr

/-- Payloads follow the existing operation description exactly. Symbolic
actuals replace only the closed Basis/Nat fields; every Op edge remains. -/
inductive Node where
  | primitive (kind : OperationDescription.Primitive) (target : Code)
  | provider (moduleName declarationName : String) (bases : List (String × Code))
      (naturals : List (String × Form)) (operations : List (String × Nat))
      (premises : List (String × OperationPaths.Paths))
  | formal (original : Parameter)
  | inverse (child : Nat)
  | thenOp (left right : Nat)
  | tensor (left right : Nat)
  | controlled (child : Nat)
  | power (child : Nat) (count : Count)
  | conjugate (outer middle : Nat)
  | requested (child : Nat) (moduleName declarationName : String)
  deriving BEq, DecidableEq, Repr

def Node.children : Node → List Nat
  | .primitive .. | .formal _ => []
  | .provider _ _ _ _ operations _ => operations.map (·.2)
  | .inverse child | .controlled child | .power child _ | .requested child _ _ => [child]
  | .thenOp left right | .tensor left right | .conjugate left right => [left,right]

def Node.remap (mapping : Nat → Nat) : Node → Node
  | .primitive kind target => .primitive kind target
  | .provider owner name bases naturals operations premises =>
    .provider owner name bases naturals (operations.map fun (name,index) => (name,mapping index)) premises
  | .formal original => .formal original
  | .inverse child => .inverse (mapping child)
  | .controlled child => .controlled (mapping child)
  | .power child count => .power (mapping child) count
  | .thenOp left right => .thenOp (mapping left) (mapping right)
  | .tensor left right => .tensor (mapping left) (mapping right)
  | .conjugate left right => .conjugate (mapping left) (mapping right)
  | .requested child owner name => .requested (mapping child) owner name

structure Description where
  frame : NaturalFrames.Frame
  nodes : List Node
  root : Nat
  nodeFrames : List NaturalFrames.Frame

def Description.singleton (frame : NaturalFrames.Frame) (node : Node) : Description := ⟨frame,[node],0,[frame]⟩

def Description.unary (child : Description) (constructor : Nat → Node) : Description :=
  ⟨child.frame,child.nodes ++ [constructor child.root],child.nodes.length,child.nodeFrames ++ [child.frame]⟩

def Description.binary (left right : Description) (constructor : Nat → Nat → Node) : Description :=
  ⟨left.frame,left.nodes ++ right.nodes.map (Node.remap (·+left.nodes.length)) ++
    [constructor left.root (right.root+left.nodes.length)],left.nodes.length+right.nodes.length,
    left.nodeFrames ++ right.nodeFrames ++ [left.frame]⟩

def provider (frame : NaturalFrames.Frame) (owner name : String) (bases : List (String × Code))
    (naturals : List (String × Form)) (operations : List (String × Description))
    (premises : List (String × OperationPaths.Paths)) : Description :=
  let (nodes,indices,frames) := operations.foldl (fun (nodes,indices,frames) (name,description) =>
    (nodes ++ description.nodes.map (Node.remap (·+nodes.length)),
      indices ++ [(name,description.root+nodes.length)],frames ++ description.nodeFrames)) ([],[],[])
  ⟨frame,nodes ++ [.provider owner name bases naturals indices premises],nodes.length,frames ++ [frame]⟩

namespace Meter

def key (original : Parameter) : Nat :=
  original.moduleName.utf8ByteSize+original.declarationName.utf8ByteSize+3

def frame (original : NaturalFrames.Frame) : Nat :=
  (original.binders.map fun binder =>
    binder.owner.moduleName.utf8ByteSize+binder.owner.declarationName.utf8ByteSize+binder.name.utf8ByteSize+4).sum

def form (value : Form) : Nat := value.coefficients.length+2

def basis (code : Code) : Nat := (code.map fun atom => 1+match atom with
  | .parameter original => key original
  | .bits width => form width
  | .fixed _ => 1).sum

def node : Node → Nat
  | .primitive _ target => basis target+2
  | .provider owner name bases naturals operations premises =>
    owner.utf8ByteSize+name.utf8ByteSize+5+
      (bases.map fun (name,code) => name.utf8ByteSize+basis code+1).sum+
      (naturals.map fun (name,value) => name.utf8ByteSize+form value+1).sum+
      (operations.map fun (name,_) => name.utf8ByteSize+2).sum+
      (premises.map fun (name,_) => name.utf8ByteSize+4).sum
  | .formal original => key original+1
  | .power _ count => form count.form+3
  | .requested _ owner name => owner.utf8ByteSize+name.utf8ByteSize+3
  | other => other.children.length+1

private def basisKeys (code : Code) : Nat := (code.map fun atom => match atom with
  | .parameter _ => 1 | .bits width => width.coefficients.length | .fixed _ => 0).sum

def nodeKeys : Node → Nat
  | .primitive _ target => basisKeys target
  | .provider _ _ bases naturals _ _ =>
    (bases.map fun (_,code) => basisKeys code).sum+
      (naturals.map fun (_,value) => value.coefficients.length).sum
  | .formal _ => 1
  | .power _ count => count.form.coefficients.length
  | _ => 0

private def basisKeyBytes (code : Code) : Nat :=
  (code.map fun atom => match atom with | .parameter original => key original | _ => 0).foldl max 0

def nodeKeyBytes : Node → Nat
  | .primitive _ target => basisKeyBytes target
  | .provider _ _ bases _ _ _ => (bases.map fun (_,code) => basisKeyBytes code).foldl max 0
  | .formal original => key original
  | _ => 0

def payload (original : Description) : Nat :=
  frame original.frame+(original.nodeFrames.map frame).sum+(original.nodes.map node).sum+original.nodes.length+1

/-- Q keys can each scan the exact original frame and eraseDups can compare
Q squared pairs of original string keys. Every visited type-prefix cell and
coefficient is counted. Retained original source snapshots are not traversed
by closure and are not multiplied into this reservation. -/
def freeWork (original : Description) : Nat :=
  let keys := (original.nodes.map nodeKeys).sum
  let bytes := max
    ((original.frame.binders.map fun binder =>
      binder.owner.moduleName.utf8ByteSize+binder.owner.declarationName.utf8ByteSize+3).foldl max 0)
    ((original.nodes.map nodeKeyBytes).foldl max 0)
  16*(payload original+(original.nodes.length+1)*(frame original.frame+1)+
    keys*(original.frame.binders.length+1)+(keys+1)^2*(bytes+1)+1)

def rebuildWork (original : Description) : Nat :=
  let edges := (original.nodes.map fun value => value.children.length).sum
  32*(payload original+1)+64*(original.nodes.length+edges+1)^2

end Meter

private def naturalKeys (frame : NaturalFrames.Frame) (form : Form) : Except String (List Key) := do
  if form.coefficients.length != frame.binders.length then throw "original natural frame differs"
  form.coefficients.zipIdx.foldlM (fun keys (coefficient,index) => do
    if coefficient == 0 then pure keys else
      let some binder := frame.binders[index]? | throw "original natural key is absent"
      pure (keys ++ [.natural ⟨binder.owner.moduleName,binder.owner.declarationName,binder.ordinal⟩])) []

private def basisKeys (frame : NaturalFrames.Frame) (code : Code) : Except String (List Key) :=
  code.foldlM (fun keys atom => do
    match atom with
    | .fixed _ => pure keys
    | .parameter original => pure (keys ++ [.basis original])
    | .bits width => return keys ++ (← naturalKeys frame width)) []

def Node.freeKeys (frame : NaturalFrames.Frame) : Node → Except String (List Key)
  | .primitive _ target => basisKeys frame target
  | .provider _ _ bases naturals _ _ => do
    let bases ← bases.mapM (fun (_,basis) => basisKeys frame basis)
    let naturals ← naturals.mapM (fun (_,natural) => naturalKeys frame natural)
    pure (bases.flatten ++ naturals.flatten)
  | .formal original => pure [.operation original]
  | .power _ count => naturalKeys frame count.form
  | _ => pure []

/-- All retained nodes contribute keys, including unused actual children and
zero-power operands. A convenient closed root type cannot hide a free child. -/
def Description.freeKeys (description : Description) : Except String (List Key) := do
  if description.nodeFrames.length != description.nodes.length ||
      !description.nodeFrames.all (fun frame => frame.binders == description.frame.binders) then
    throw "operation children have different original natural frames"
  pure ((← description.nodes.mapM (Node.freeKeys description.frame)).flatten.eraseDups)

structure Constant (form : Form) where
  value : Nat
  nonnegative : 0 ≤ form.constant
  bounded : value ≤ 4294967295
  same : form.constant = (value : Int)
  coefficients : form.coefficients.all (· == 0) = true
  correct : ∀ values,form.evaluate values = (value : Int)

def readConstant (form : Form) : WorkM (Constant form) := do
  NaturalAffine.valid form
  if coefficients : form.coefficients.all (· == 0) = true then
    if nonnegative : 0 ≤ form.constant then
      let value := form.constant.toNat
      if bounded : value ≤ 4294967295 then
        have same : form.constant = (value : Int) := (Int.toNat_of_nonneg nonnegative).symm
        return ⟨value,nonnegative,bounded,same,coefficients,by
          intro values
          simp only [Form.evaluate,dot_zero _ coefficients,Int.add_zero]
          exact same⟩
      else throw .request
    else throw .request
  else throw .request

structure BasisClosed (code : Code) where
  value : Semantics.FiniteCarrier.Basis
  correct : ∀ parameters values,Semantics.SymbolicBasis.evaluate parameters values code = some value

private def readBasisAtom (atom : Atom) : WorkM (BasisClosed [atom]) := do
  match atom with
  | .fixed fixed =>
    return ⟨[fixed],by intros; rfl⟩
  | .parameter _ => throw .request
  | .bits width =>
    let constant ← readConstant width
    return ⟨[.bits constant.value],by
      intro parameters values
      simp only [Semantics.SymbolicBasis.evaluate_cons,Semantics.SymbolicBasis.evaluate_nil,Atom.evaluate,constant.correct]
      simp⟩

def readBasis (code : Code) : WorkM (BasisClosed code) :=
  (Nat.rec (motive := fun fuel => (code : Code) → code.length ≤ fuel → WorkM (BasisClosed code))
    (fun code bound => match code with
      | [] => pure ⟨[],by intros; rfl⟩
      | _ :: rest => False.elim (Nat.not_succ_le_zero rest.length bound))
    (fun _ next code bound => match code with
      | [] => pure ⟨[],by intros; rfl⟩
      | atom :: rest => do
        let first ← readBasisAtom atom
        let tail ← next rest (Nat.le_of_succ_le_succ bound)
        return ⟨first.value ++ tail.value,by
          intro parameters values
          have same := Semantics.SymbolicBasis.evaluate_append parameters values [atom] rest
          rw [first.correct,tail.correct] at same
          exact same⟩) code.length) code (Nat.le_refl _)

structure NaturalCertificate where
  form : Form
  closed : Constant form

structure BasisCertificate where
  code : Code
  closed : BasisClosed code

structure NodeClosed where
  node : OperationDescription.Node
  naturals : List NaturalCertificate := []
  bases : List BasisCertificate := []

private def readNode : Node → WorkM NodeClosed
  | .formal _ => throw .request
  | .primitive kind target => do
    let basis ← readBasis target
    return ⟨.primitive kind basis.value,[],[⟨target,basis⟩]⟩
  | .provider owner name bases naturals operations _ => do
    let bases ← bases.mapM fun (name,code) => do
      let closed ← readBasis code
      pure (name,(⟨code,closed⟩ : BasisCertificate))
    let naturals ← naturals.mapM fun (name,form) => do
      let closed ← readConstant form
      pure (name,(⟨form,closed⟩ : NaturalCertificate))
    return ⟨.provider owner name (bases.map fun (name,basis) => (name,basis.closed.value))
      (naturals.map fun (name,natural) => (name,natural.closed.value)) operations,
      naturals.map (·.2),bases.map (·.2)⟩
  | .inverse child => pure ⟨.inverse child,[],[]⟩
  | .controlled child => pure ⟨.controlled child,[],[]⟩
  | .thenOp left right => pure ⟨.thenOp left right,[],[]⟩
  | .tensor left right => pure ⟨.tensor left right,[],[]⟩
  | .conjugate outer middle => pure ⟨.conjugate outer middle,[],[]⟩
  | .requested child owner name => pure ⟨.requested child owner name,[],[]⟩
  | .power child count => do
    let natural ← readConstant count.form
    let value ← if count.powerTwo then do
        guard (natural.value ≤ 31) .request
        pure (2^natural.value)
      else pure natural.value
    return ⟨.power child value,[⟨count.form,natural⟩],[]⟩

structure ClosedData where
  description : OperationDescription.Description
  nodes : List NodeClosed
  retained : nodes.map (·.node) = description.nodes

def readClosedData (description : Description) : WorkM ClosedData := do
  exactWork (Exact.charge (Meter.rebuildWork description))
  guard (description.nodeFrames.length == description.nodes.length &&
    description.nodeFrames.all (fun frame => frame.binders == description.frame.binders)) .request
  guard (!description.nodes.isEmpty && description.nodes.length ≤ 4096 &&
    description.root+1 == description.nodes.length &&
    description.nodes.zipIdx.all (fun (node,index) => node.children.all (· < index))) .request
  let nodes ← description.nodes.mapM readNode
  let result : OperationDescription.Description := ⟨nodes.map (·.node),description.root⟩
  let size ← lift ((result.treeSize).mapError fun _ => Error.request)
  let edges := (description.nodes.map fun node => node.children.length).sum
  exactWork (Exact.charge (16*(size+1)*(description.nodes.length+edges+1)))
  let _ ← lift ((result.occurrences).mapError fun _ => Error.request)
  return ⟨result,nodes,rfl⟩

structure Closed (original : Description) where
  data : ClosedData
  noFree : original.freeKeys = .ok []
  computed : ∃ before after,(readClosedData original).run before = (.ok data,after)

inductive Status (original : Description) where
  | conditional (keys : List Key) (nonempty : keys ≠ []) (read : original.freeKeys = .ok keys)
  | closed (checked : Closed original)

def close (original : Description) : WorkM (Status original) := do
  exactWork (Exact.charge (Meter.freeWork original))
  match keys : original.freeKeys with
  | .error _ => throw .request
  | .ok free =>
    if empty : free = [] then
      let data ← NaturalAffine.witness (readClosedData original)
      return .closed ⟨data.val,by simpa only [empty] using keys,by with_reducible exact data.property⟩
    else return .conditional free empty keys

def Node.pathShape : Node → WorkM OperationPaths.Shape
  | .primitive .. => pure .leaf
  | .formal _ => pure (.formal [] none)
  | .provider _ _ _ _ operations premises => do
    let actuals ← operations.mapM fun (name,index) => do
      let some (_,paths) := premises.find? (·.1 == name) | throw .request
      pure (index,paths)
    pure (.provider actuals)
  | .inverse child => pure (.inverse child)
  | .controlled child => pure (.controlled child)
  | .power child _ | .requested child _ _ => pure (.repeat child)
  | .thenOp left right | .tensor left right => pure (.pair left right)
  | .conjugate outer middle => pure (.conjugate outer middle)

structure Selection where
  indices : List Nat
  subject : Description

/-- Select an original node closure, preserving every Op actual edge and its
own retained natural frame. This is a source-metadata operation, not evidence
that any selected provider or requested path has an implementation. -/
def select (original : Description) (root : Nat) : WorkM Selection := do
  exactWork (Exact.charge (Meter.rebuildWork original))
  guard (root < original.nodes.length && original.nodes.length ≤ 4096 &&
    original.nodeFrames.length == original.nodes.length &&
    original.nodes.zipIdx.all (fun (node,index) => node.children.all (· < index))) .request
  let reachable := (original.nodes.zipIdx.reverse.foldl (fun seen (node,index) =>
    if seen.contains index then node.children ++ seen else seen) [root]).eraseDups
  let selected := ((original.nodes.zip original.nodeFrames).zipIdx).filter
    (fun (_,index) => reachable.contains index)
  let indices := selected.map (·.2)
  let nodes := selected.map fun ((node,_),_) => node.remap indices.idxOf
  let frames := selected.map fun ((_,frame),_) => frame
  let subject : Description := ⟨original.frame,nodes,indices.idxOf root,frames⟩
  guard (subject.root < subject.nodes.length) .request
  return ⟨indices,subject⟩

structure Fragment (original : Description) where
  index : Nat
  path : List Nat
  requested : OperationPaths.Paths
  selection : Selection
  selected : ∃ before after,(select original index).run before = (.ok selection,after)
  status : Status selection.subject
  computed : ∃ before after,(close selection.subject).run before = (.ok status,after)

def Fragment.readSuppliers {sources original} (fragment : Fragment original)
    (origins : List (Nat × Origin sources)) : WorkM (List (Nat × Origin sources)) := do
  exactWork (Exact.charge (16*(fragment.selection.indices.length+1)*(origins.length+1)))
  return fragment.selection.indices.zipIdx.flatMap fun (original,selected) =>
    (origins.filter (·.1 == original)).map (fun (_,origin) => (selected,origin))

private def fragments (original : Description) : Nat → Nat → List Nat → OperationPaths.Paths →
    Nat → WorkM (Nat × List (Fragment original)) :=
  Nat.rec (fun _ _ _ _ => throw .limit) (fun _ next index path requested visited => do
    guard (visited < 4096) .limit
    exactWork (Exact.charge (8*(original.nodes.length+path.length+1)))
    let node ← lift (readOption original.nodes[index]?)
    exactWork (Exact.charge (16*(Meter.node node+path.length+1)*(node.children.length+1)))
    let shape ← node.pathShape
    let children := shape.children requested
    let current ← if requested.any then do
        let selection ← NaturalAffine.witness (select original index)
        let status ← NaturalAffine.witness (close selection.val.subject)
        pure [(⟨index,path,requested,selection.val,by with_reducible exact selection.property,
          status.val,by with_reducible exact status.property⟩ : Fragment original)]
      else pure []
    let (visited,rest) ← children.zipIdx.foldlM (fun (visited,previous) ((child,paths),ordinal) => do
      let (visited,entries) ← next child (path ++ [ordinal]) paths visited
      pure (visited,previous ++ entries)) (visited+1,[])
    return (visited,current ++ rest))

/-- Every child occurrence is visited, even with no demand at its parent.
This retains mandatory inverse formation and original prerequisites on unused
actuals. Repetition count and a free sibling never suppress a closed fragment.
The existing 4096 expanded-tree capacity bounds visits; no node deduplication
replaces per-edge source/provider provenance. -/
def readAccessFragments (original : Description) (requested : OperationPaths.Paths) :
    WorkM (List (Fragment original)) := do
  exactWork (Exact.charge (Meter.rebuildWork original))
  guard (!original.nodes.isEmpty && original.nodes.length ≤ 4096 &&
    original.root+1 == original.nodes.length && original.nodeFrames.length == original.nodes.length &&
    original.nodes.zipIdx.all (fun (node,index) => node.children.all (· < index))) .request
  return (← fragments original (original.nodes.length+1) original.root [] requested 0).2

inductive Requirement (sources : Sources) where
  | meaning (request : SourceMeaning.Request sources)
  | access (paths : OperationPaths.Paths)

/-- Every original static actual and its symbolic premise-transfer witness
remain attached to the call occurrence, including unused supplied arguments.
This is not a runtime interval or an accepted provider instance. -/
structure ActualOperation (sources : Sources) where
  original : Parameter
  subject : Description
  suppliers : List (Nat × Origin sources)

structure ApplicationSource (sources : Sources) where
  state : GenericLexicalNatural.SomeEnvironment sources
  scope : List String
  tokens : List LocatedToken
  owner : String
  name : String
  target : StaticHeaders.Original sources owner name
  written : StaticApplication.Syntax tokens
  transfer : StaticCallPremises.InState state scope target written.arguments
  basisActuals : List (Parameter × Code)
  naturalActuals : List Form
  operationActuals : List (ActualOperation sources)

/-- A required formal is paired with the actual original child occurrence.
Its key includes the callee declaration and mixed ordinal. Forwarding retains
this chain instead of rebinding the actual under the callee's module policy. -/
structure Binding (sources : Sources) where
  owner : String
  name : String
  original : StaticHeaders.Original sources owner name
  formal : StaticHeaders.Formal
  actual : Origin sources
  application : Option (ApplicationSource sources) := none

/-- A header premise has one original mixed-formal identity. Written
assertions and executable path demands remain separate source occurrences,
even when they happen to request the same Meaning or access. -/
inductive RequirementKind where
  | formalMeaning (original : Parameter)
  | formalAccess (original : Parameter)
  | checkedMeaning
  | inverseFormation
  | application
  | selectionControl
  | runtimeTransform
  | computedLogical
  deriving BEq, DecidableEq, Repr

def RequirementKind.formal? : RequirementKind → Option Parameter
  | .formalMeaning original | .formalAccess original => some original
  | _ => none

structure Duty (sources : Sources) where
  origin : Origin sources
  subject : Description
  requirement : Requirement sources
  kind : RequirementKind
  bindings : List (Binding sources) := []
  suppliers : List (Nat × Origin sources) := []
  runtimeApplication : Option (ApplicationSource sources) := none

def Duty.sourceRows {sources} (duty : Duty sources) : List (String × String) :=
  (duty.origin.state.owner,duty.origin.state.prepared.original.envelope.source) ::
    duty.origin.rows ++ (match duty.requirement with | .meaning request => request.sourceRows | .access _ => [])

/-- The original traversal supplies one interleaving. A call is expanded at
this point after its argument duties, before the next enclosing expression;
offset sorting or independently concatenated projections cannot recover it. -/
inductive Activity (sources : Sources) where
  | duty (original : Duty sources)
  | application (original : ApplicationSource sources)

def Activity.duty? {sources} : Activity sources → Option (Duty sources)
  | .duty original => some original
  | .application _ => none

def Activity.application? {sources} : Activity sources → Option (ApplicationSource sources)
  | .duty _ => none
  | .application original => some original

end QleisliKernel.SourceTypes.GenericOperation
