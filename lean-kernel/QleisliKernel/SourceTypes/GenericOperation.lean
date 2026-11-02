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

def Description.singleton (frame : NaturalFrames.Frame) (node : Node) : Description := ⟨frame,[node],0⟩

def Description.unary (child : Description) (constructor : Nat → Node) : Description :=
  ⟨child.frame,child.nodes ++ [constructor child.root],child.nodes.length⟩

def Description.binary (left right : Description) (constructor : Nat → Nat → Node) : Description :=
  ⟨left.frame,left.nodes ++ right.nodes.map (Node.remap (·+left.nodes.length)) ++
    [constructor left.root (right.root+left.nodes.length)],left.nodes.length+right.nodes.length⟩

def provider (frame : NaturalFrames.Frame) (owner name : String) (bases : List (String × Code))
    (naturals : List (String × Form)) (operations : List (String × Description))
    (premises : List (String × OperationPaths.Paths)) : Description :=
  let (nodes,indices) := operations.foldl (fun (nodes,indices) (name,description) =>
    (nodes ++ description.nodes.map (Node.remap (·+nodes.length)),
      indices ++ [(name,description.root+nodes.length)])) ([],[])
  ⟨frame,nodes ++ [.provider owner name bases naturals indices premises],nodes.length⟩

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
      simp only [Semantics.SymbolicBasis.evaluate,Atom.evaluate,constant.correct]
      simp⟩

def readBasis : (code : Code) → WorkM (BasisClosed code)
  | [] => pure ⟨[],by intros; rfl⟩
  | atom :: rest => do
    let first ← readBasisAtom atom
    let tail ← readBasis rest
    return ⟨first.value ++ tail.value,by
      intro parameters values
      have same := Semantics.SymbolicBasis.evaluate_append parameters values [atom] rest
      rw [first.correct,tail.correct] at same
      exact same⟩

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
  | .inverse child => pure ⟨.inverse child⟩
  | .controlled child => pure ⟨.controlled child⟩
  | .thenOp left right => pure ⟨.thenOp left right⟩
  | .tensor left right => pure ⟨.tensor left right⟩
  | .conjugate outer middle => pure ⟨.conjugate outer middle⟩
  | .requested child owner name => pure ⟨.requested child owner name⟩
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
  guard (!description.nodes.isEmpty && description.nodes.length ≤ 4096 &&
    description.root+1 == description.nodes.length &&
    description.nodes.zipIdx.all (fun (node,index) => node.children.all (· < index))) .request
  exactWork (Exact.charge (32*(description.nodes.length+1)^2))
  let nodes ← description.nodes.mapM readNode
  let result : OperationDescription.Description := ⟨nodes.map (·.node),description.root⟩
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
  exactWork (Exact.charge (16*(original.nodes.length+original.frame.binders.length+1)))
  match keys : original.freeKeys with
  | .error _ => throw .request
  | .ok free =>
    if empty : free = [] then
      let data ← NaturalAffine.witness (readClosedData original)
      return .closed ⟨data.val,by simpa only [empty] using keys,by with_reducible exact data.property⟩
    else return .conditional free empty keys

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

structure Duty (sources : Sources) where
  origin : Origin sources
  subject : Description
  requirement : Requirement sources
  bindings : List (Binding sources) := []
  suppliers : List (Nat × Origin sources) := []
  runtimeApplication : Option (ApplicationSource sources) := none

def Duty.sourceRows {sources} (duty : Duty sources) : List (String × String) :=
  (duty.origin.state.owner,duty.origin.state.prepared.original.envelope.source) ::
    duty.origin.rows ++ (match duty.requirement with | .meaning request => request.sourceRows | .access _ => [])

end QleisliKernel.SourceTypes.GenericOperation
