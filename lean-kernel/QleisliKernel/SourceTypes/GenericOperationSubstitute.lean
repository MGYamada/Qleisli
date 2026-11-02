import QleisliKernel.SourceTypes.GenericOperation
import QleisliKernel.SourceTypes.SymbolicTypes
import QleisliKernel.SourceTypes.NaturalSubstitute

/-! One simultaneous transport of an original callee operation closure.
The input ApplicationSource retains the original static argument occurrence
and premise-transfer witness. Existing proof-producing Basis/Nat substitution
is reused. An inserted Op actual is not traversed as another callee template.
Original supplier environments and guard scopes remain attached to every node.
This module classifies metadata; it proves no Meaning equation, implementation
path, complete invocation expansion or native admission.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.GenericOperationSubstitute
open Finite GenericOperation Semantics.SymbolicBasis Semantics.SourceAffine

def callerFrame {sources} (application : ApplicationSource sources) : NaturalFrames.Frame :=
  StaticHeaders.frame application.state.prepared.original

def calleeFrame {sources} (application : ApplicationSource sources) : NaturalFrames.Frame :=
  StaticHeaders.frame application.target

structure Subject (sources : Sources) where
  description : Description
  suppliers : List (Nat × Origin sources)

def basisKeys {sources} (application : ApplicationSource sources) : List Parameter :=
  application.target.header.formals.filterMap fun formal => match formal.kind with
    | .basis => some ⟨application.owner,application.name,formal.ordinal⟩
    | _ => none

def operationKeys {sources} (application : ApplicationSource sources) : List Parameter :=
  application.target.header.formals.filterMap fun formal => match formal.kind with
    | .operation _ => some ⟨application.owner,application.name,formal.ordinal⟩
    | _ => none

/-- These equalities authenticate mixed-kind positions and canonical Nat
replacement order. They select no convenient value for an original formal. -/
structure Context {sources} (application : ApplicationSource sources) : Type where
  bases : application.basisActuals.map (·.1) = basisKeys application
  operations : application.operationActuals.map (·.original) = operationKeys application
  naturals : application.naturalActuals =
    NaturalFrames.replacements (StaticHeaders.frame application.transfer.callee.original)
      (application.transfer.forms.map (·.form))
  dimensions : application.naturalActuals.all
    (fun form => form.coefficients.length == (callerFrame application).binders.length) = true
  frames : application.operationActuals.all (fun actual =>
    actual.subject.frame.binders == (callerFrame application).binders &&
      actual.subject.nodeFrames.length == actual.subject.nodes.length &&
      actual.subject.nodeFrames.all (fun frame => frame.binders == (callerFrame application).binders)) = true

private def actualFields {sources} (application : ApplicationSource sources) : Nat :=
  (application.basisActuals.map fun (key,code) => Meter.key key+Meter.basis code+1).sum+
    (application.naturalActuals.map Meter.form).sum+
    (application.operationActuals.map fun actual =>
      Meter.key actual.original+Meter.payload actual.subject+actual.suppliers.length+1).sum

def readContext {sources} (application : ApplicationSource sources) : WorkM (Context application) := do
  let formals := application.target.header.formals.length
  let keyBytes := application.owner.utf8ByteSize+application.name.utf8ByteSize+3
  let frames := (application.operationActuals.map fun actual => actual.subject.nodeFrames.length+1).sum
  exactWork (Exact.charge (16*(actualFields application+formals*formals+
    (application.basisActuals.length+application.operationActuals.length+1)*(keyBytes+1)+
    (frames+1)*(Meter.frame (callerFrame application)+1)+Meter.frame (calleeFrame application)+1)))
  if bases : application.basisActuals.map (·.1) = basisKeys application then
    if operations : application.operationActuals.map (·.original) = operationKeys application then
      if naturals : application.naturalActuals =
          NaturalFrames.replacements (StaticHeaders.frame application.transfer.callee.original)
            (application.transfer.forms.map (·.form)) then
        if dimensions : application.naturalActuals.all
            (fun form => form.coefficients.length == (callerFrame application).binders.length) = true then
          if frames : application.operationActuals.all (fun actual =>
              actual.subject.frame.binders == (callerFrame application).binders &&
                actual.subject.nodeFrames.length == actual.subject.nodes.length &&
                actual.subject.nodeFrames.all (fun frame => frame.binders == (callerFrame application).binders)) = true then
            return ⟨bases,operations,naturals,dimensions,frames⟩
          else throw .request
        else throw .request
      else throw .request
    else throw .request
  else throw .request

structure BasisStep {sources} (application : ApplicationSource sources) where
  original : Code
  checked : SymbolicTypes.Substituted application.basisActuals application.naturalActuals original
  computed : ∃ before after,
    (SymbolicTypes.substitute (callerFrame application).binders.length
      application.basisActuals application.naturalActuals original).run before = (.ok checked,after)

structure NaturalStep {sources} (application : ApplicationSource sources) where
  original : Form
  checked : NaturalSubstitute.Result original application.naturalActuals
  computed : ∃ before after,
    (NaturalSubstitute.substitute (callerFrame application).binders.length original
      application.naturalActuals).run before = (.ok checked,after)

private def basis {sources} (application : ApplicationSource sources) (code : Code) :
    WorkM (BasisStep application) := do
  let checked ← NaturalAffine.witness (SymbolicTypes.substitute (callerFrame application).binders.length
    application.basisActuals application.naturalActuals code)
  return ⟨code,checked.val,by with_reducible exact checked.property⟩

private def natural {sources} (application : ApplicationSource sources) (form : Form) :
    WorkM (NaturalStep application) := do
  let checked ← NaturalAffine.witness (NaturalSubstitute.substitute (callerFrame application).binders.length
    form application.naturalActuals)
  return ⟨form,checked.val,by with_reducible exact checked.property⟩

structure NodeResult {sources} (application : ApplicationSource sources) where
  subject : Subject sources
  bases : List (BasisStep application)
  naturals : List (NaturalStep application)

private def roots {sources} (original : Subject sources) (index root : Nat) : List (Nat × Origin sources) :=
  (original.suppliers.filter (·.1 == index)).map (fun (_,origin) => (root,origin))

private def reserve {sources} (subjects : List (Subject sources)) : WorkM Unit := do
  let count := (subjects.map (·.description.nodes.length)).sum+1
  guard (count ≤ 4096) .limit
  exactWork (Exact.charge (16*(count+(subjects.map fun subject =>
    Meter.payload subject.description+subject.suppliers.length).sum+1)))

private def unary {sources} (application : ApplicationSource sources) (original : Subject sources)
    (index : Nat) (child : Subject sources) (constructor : Nat → Node) : WorkM (Subject sources) := do
  reserve [child]
  guard (child.description.frame.binders == (callerFrame application).binders) .request
  let description := child.description.unary constructor
  return ⟨description,child.suppliers ++ roots original index description.root⟩

private def binary {sources} (original : Subject sources) (index : Nat)
    (left right : Subject sources) (constructor : Nat → Nat → Node) : WorkM (Subject sources) := do
  reserve [left,right]
  guard (left.description.frame.binders == right.description.frame.binders) .request
  let description := left.description.binary right.description constructor
  return ⟨description,left.suppliers ++ right.suppliers.map (fun (index,origin) =>
    (index+left.description.nodes.length,origin)) ++ roots original index description.root⟩

private def readNode {sources} (application : ApplicationSource sources) (original : Subject sources)
    (previous : List (Subject sources)) (index : Nat) (node : Node) : WorkM (NodeResult application) := do
  exactWork (Exact.charge (16*(Meter.node node+actualFields application+
    original.suppliers.length+previous.length+1)*
      ((callerFrame application).binders.length+application.target.header.formals.length+1)))
  let child (index : Nat) := lift (readOption previous[index]?)
  let frame := callerFrame application
  match node with
  | .formal key =>
    match application.operationActuals.find? (·.original == key) with
    | some actual =>
      -- Simultaneous substitution: this is the exact caller closure, including
      -- its own original keys and supplier contexts. Do not recurse into it.
      return ⟨⟨actual.subject,actual.suppliers⟩,[],[]⟩
    | none =>
      let description := Description.singleton frame (.formal key)
      return ⟨⟨description,roots original index 0⟩,[],[]⟩
  | .primitive kind target =>
    let replaced ← basis application target
    let description := Description.singleton frame (.primitive kind replaced.checked.code)
    return ⟨⟨description,roots original index 0⟩,[replaced],[]⟩
  | .provider owner name bases naturals operations premises =>
    let bases ← bases.mapM fun (name,code) => do
      let replaced ← basis application code
      pure (name,replaced)
    let naturals ← naturals.mapM fun (name,form) => do
      let replaced ← natural application form
      pure (name,replaced)
    let operations ← operations.mapM fun (name,index) => do
      let value ← child index
      pure (name,value)
    reserve (operations.map (·.2))
    let description := GenericOperation.provider frame owner name
      (bases.map fun (name,replaced) => (name,replaced.checked.code))
      (naturals.map fun (name,replaced) => (name,replaced.checked.form))
      (operations.map fun (name,value) => (name,value.description)) premises
    let (_,suppliers) := operations.foldl (fun (offset,suppliers) (_,value) =>
      (offset+value.description.nodes.length,
        suppliers ++ value.suppliers.map (fun (index,origin) => (index+offset,origin)))) (0,[])
    return ⟨⟨description,suppliers ++ roots original index description.root⟩,
      bases.map (·.2),naturals.map (·.2)⟩
  | .inverse index' =>
    return ⟨← unary application original index (← child index') .inverse,[],[]⟩
  | .controlled index' =>
    return ⟨← unary application original index (← child index') .controlled,[],[]⟩
  | .requested index' owner name =>
    return ⟨← unary application original index (← child index') (fun child => .requested child owner name),[],[]⟩
  | .power index' count =>
    let replaced ← natural application count.form
    let subject ← unary application original index (← child index')
      (fun child => .power child ⟨replaced.checked.form,count.powerTwo⟩)
    return ⟨subject,[],[replaced]⟩
  | .thenOp left right =>
    return ⟨← binary original index (← child left) (← child right) .thenOp,[],[]⟩
  | .tensor left right =>
    return ⟨← binary original index (← child left) (← child right) .tensor,[],[]⟩
  | .conjugate outer middle =>
    return ⟨← binary original index (← child outer) (← child middle) .conjugate,[],[]⟩

structure Step {sources} (application : ApplicationSource sources) (original : Subject sources) where
  index : Nat
  node : Node
  actual : original.description.nodes[index]? = some node
  previous : List (Subject sources)
  result : NodeResult application
  computed : ∃ before after,(readNode application original previous index node).run before = (.ok result,after)

structure Result {sources} (application : ApplicationSource sources) (original : Subject sources) where
  subject : Subject sources
  steps : List (Step application original)
  every : steps.map (·.index) = List.range original.description.nodes.length
  returned : steps[original.description.root]?.map (·.result.subject) = some subject

private def run {sources} (application : ApplicationSource sources) (original : Subject sources) :
    WorkM (Result application original) := do
  exactWork (Exact.charge (Meter.rebuildWork original.description))
  guard (!original.description.nodes.isEmpty && original.description.nodes.length ≤ 4096 &&
    original.description.root+1 == original.description.nodes.length &&
    original.description.nodeFrames.length == original.description.nodes.length &&
    original.description.nodeFrames.all (fun frame => frame.binders == (calleeFrame application).binders) &&
    original.description.frame.binders == (calleeFrame application).binders &&
    original.description.nodes.zipIdx.all (fun (node,index) => node.children.all (· < index))) .request
  let (_previous,steps) ← (List.range original.description.nodes.length).foldlM
    (fun (previous,steps) index => do
      match actual : original.description.nodes[index]? with
      | none => throw .request
      | some node =>
        let result ← NaturalAffine.witness (readNode application original previous index node)
        have same : original.description.nodes[index]? = some node := by
          first | exact actual | rfl
        let step : Step application original := ⟨index,node,same,previous,
          result.val,by with_reducible exact result.property⟩
        pure (previous ++ [result.val.subject],steps ++ [step])) ([],[])
  if every : steps.map (·.index) = List.range original.description.nodes.length then
    match returned : steps[original.description.root]?.map (·.result.subject) with
    | none => throw .request
    | some returnedSubject =>
      -- Subject contains functions in retained Origins; compare no such data.
      -- Select the exact same Step projection that the executable fold built.
      return ⟨returnedSubject,steps,every,by first | exact returned | rfl⟩
  else throw .request

structure Checked {sources} (application : ApplicationSource sources) (original : Subject sources) where
  context : Context application
  prepared : ∃ before after,(readContext application).run before = (.ok context,after)
  result : Result application original
  computed : ∃ before after,(run application original).run before = (.ok result,after)

/-- One actual setup for this exact original application. The retained
execution authenticates all simultaneous mixed-key maps and original frames;
it contains no translated subject, closure result or native proof. -/
structure Prepared {sources} (application : ApplicationSource sources) : Type where
  context : Context application
  original : ∃ before after,(readContext application).run before = (.ok context,after)

def prepare {sources} (application : ApplicationSource sources) : WorkM (Prepared application) := do
  let context ← NaturalAffine.witness (readContext application)
  return ⟨context.val,by with_reducible exact context.property⟩

def readWithPrepared {sources application} (prepared : @Prepared sources application)
    (description : Description) (suppliers : List (Nat × Origin sources)) :
    WorkM (Checked application ⟨description,suppliers⟩) := do
  let result ← NaturalAffine.witness (run application ⟨description,suppliers⟩)
  return ⟨prepared.context,prepared.original,result.val,by with_reducible exact result.property⟩

def read {sources} (application : ApplicationSource sources) (description : Description)
    (suppliers : List (Nat × Origin sources)) : WorkM (Checked application ⟨description,suppliers⟩) := do
  readWithPrepared (← prepare application) description suppliers

structure DutyChecked {sources} (application : ApplicationSource sources) (original : Duty sources) where
  subject : Checked application ⟨original.subject,original.suppliers⟩

/-- The original assertion, lexical guard environment and binding chain stay
indexed inputs. The result supplies one additional call binding; an enclosing
catalogue expansion must authenticate that call's target original body and
retain this wrapper instead of treating the translated descriptor as evidence. -/
def readDuty {sources} (application : ApplicationSource sources) (original : Duty sources) :
    WorkM (DutyChecked application original) := do
  let subject ← read application original.subject original.suppliers
  return ⟨subject⟩

end QleisliKernel.SourceTypes.GenericOperationSubstitute
