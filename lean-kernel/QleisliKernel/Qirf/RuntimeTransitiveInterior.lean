import QleisliKernel.Qirf.RuntimeInteriorSupply
import QleisliKernel.Qirf.RuntimeInteriorFocus

/-! Continue an interior formal through the remaining named applications.
Each step uses the existing whole substitution. The embedded child records
where its returned subject and supplier rows occur in that whole result.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeTransitiveInterior
open QleisliKernel Finite SourceTypes GenericDutyQueue
open QleisliKernel.SourceTypes.GenericOperationSubstitute (Subject)
open QleisliKernel.Qirf.RuntimeInteriorSupply (Leaf Point)
open RuntimeDutyInvocation (Binding)
open RuntimeInterval (Computed)
open QleisliKernel.Semantics.SymbolicBasis (Parameter)

structure Site {artifact catalogue context description graph implementations references prepared root requested}
    (checked : @RuntimeOperationTree.Checked artifact catalogue context description graph implementations references prepared root requested)
    (native : OperationDescription.Description) where
  caller : String
  event : SourceRuntimeContext.NamedEvent artifact.sources caller
  app : GenericOperation.ApplicationSource artifact.sources
  original : Subject artifact.sources
  transfer : GenericOperationSubstitute.Checked app original
  start : Point checked native
  edges : List SourceOperation.Edge
  key : Parameter
  leaf : Leaf event app transfer start edges key
  ancestors : List Nat

def Site.positions {artifact catalogue context description graph implementations references prepared root requested checked native}
    (site : @Site artifact catalogue context description graph implementations references prepared root requested checked native) :
    List Nat := site.ancestors ++ site.leaf.route.positions

def Site.ofLeaf {artifact catalogue context description graph implementations references prepared root requested checked native
    caller original event app transfer start edges key}
    (ancestors : List Nat)
    (leaf : @Leaf artifact catalogue context description graph implementations references prepared root requested checked native
      caller original event app transfer start edges key) : Site checked native :=
  ⟨caller,event,app,original,transfer,start,edges,key,leaf,ancestors⟩

structure Focused {artifact catalogue context description graph implementations references prepared root requested checked native}
    (site : @Site artifact catalogue context description graph implementations references prepared root requested checked native) where
  focus : RuntimeInteriorFocus.Checked site.transfer site.positions
  focused : Computed (RuntimeInteriorFocus.read site.transfer site.positions) focus
  atLeaf : focus.inputIndex = site.leaf.finish.index
  sameStep : focus.row = site.leaf.supply.step
  returned : focus.row.result.subject = ⟨site.leaf.supply.genericActual.subject,site.leaf.supply.genericActual.suppliers⟩
  source : OperationSourceUses.Checked site.event.target.callerSignature.instantiation site.event.target.naturals.helpers.val
    site.event.target.naturals.environment site.event.scope site.leaf.supply.source.checked.genericState
    site.leaf.supply.source.actual.argument.tokens
  sourced : Computed (OperationSourceUses.readChecked site.leaf.supply.source.checked) source
  expected : List GenericFormalPaths.Occurrence
  enumerated : Computed (GenericFormalPaths.read site.leaf.supply.genericActual.subject) expected

def readFocus {artifact catalogue context description graph implementations references prepared root requested checked native}
    (site : @Site artifact catalogue context description graph implementations references prepared root requested checked native) :
    WorkM (Focused site) := do
  exactWork (Exact.charge (16*(site.ancestors.length+site.edges.length+1)))
  let focus ← NaturalAffine.witness (RuntimeInteriorFocus.read site.transfer site.positions)
  if atLeaf : focus.val.inputIndex = site.leaf.finish.index then
    have same : focus.val.row = site.leaf.supply.step := by
      have atIndex := focus.val.atIndex
      rw [atLeaf] at atIndex
      exact Option.some.inj (atIndex.symm.trans site.leaf.supply.atIndex)
    let source ← NaturalAffine.witness (OperationSourceUses.readChecked site.leaf.supply.source.checked)
    let expected ← NaturalAffine.witness (GenericFormalPaths.read site.leaf.supply.genericActual.subject)
    return ⟨focus.val,by with_reducible exact focus.property,atLeaf,same,
      (congrArg (fun row => row.result.subject) same).trans site.leaf.supply.returnedStep,
      source.val,by with_reducible exact source.property,expected.val,by with_reducible exact expected.property⟩
  else throw .request

def Focused.start {artifact catalogue context description graph implementations references prepared root requested checked native site}
    (f : @Focused artifact catalogue context description graph implementations references prepared root requested checked native site) :
    Point checked native := ⟨f.focus.outputIndex,site.leaf.child⟩

def Focused.expectedAt {artifact catalogue context description graph implementations references prepared root requested checked native site}
    (f : @Focused artifact catalogue context description graph implementations references prepared root requested checked native site) :
    List GenericFormalPaths.Occurrence :=
  f.expected.map fun (path,index,key) => (path,index+f.focus.nodeOffset,key)

structure Children {artifact catalogue context description graph implementations references prepared root requested checked native caller site}
    (f : @Focused artifact catalogue context description graph implementations references prepared root requested checked native site)
    (event : SourceRuntimeContext.NamedEvent artifact.sources caller) (app : GenericOperation.ApplicationSource artifact.sources)
    (transfer : GenericOperationSubstitute.Checked app site.transfer.result.subject) where
  entries : List (RuntimeInteriorSupply.Entry f.source.uses event app transfer f.start)
  read : Computed (RuntimeInteriorSupply.readEntries f.source.uses event app transfer f.start) entries
  ordered : entries.map (·.index) = List.finRange f.source.uses.length
  coverage : entries.map RuntimeInteriorSupply.Entry.signature = f.expectedAt
  compared : Computed (RuntimeInteriorSupply.checkCoverage (entries.map RuntimeInteriorSupply.Entry.signature) f.expectedAt) ⟨coverage⟩

private def readChildren {artifact catalogue context description graph implementations references prepared root requested checked native caller site}
    (f : @Focused artifact catalogue context description graph implementations references prepared root requested checked native site)
    (event : SourceRuntimeContext.NamedEvent artifact.sources caller) (app : GenericOperation.ApplicationSource artifact.sources)
    (transfer : GenericOperationSubstitute.Checked app site.transfer.result.subject) : WorkM (Children f event app transfer) := do
  let rows ← NaturalAffine.witness (RuntimeInteriorSupply.readEntries f.source.uses event app transfer f.start)
  exactWork (Exact.charge (16*(f.expected.length+f.source.uses.length+rows.val.length+
    rows.val.foldl (fun total e => total+e.use.path.length+1) 1)))
  if ordered : rows.val.map (·.index) = List.finRange f.source.uses.length then
    let same ← NaturalAffine.witness (RuntimeInteriorSupply.checkCoverage (rows.val.map RuntimeInteriorSupply.Entry.signature) f.expectedAt)
    return ⟨rows.val,by with_reducible exact rows.property,ordered,same.val.down,by with_reducible exact same.property⟩
  else throw .request

structure Task {artifact catalogue context description graph implementations references prepared root requested}
    (checked : @RuntimeOperationTree.Checked artifact catalogue context description graph implementations references prepared root requested)
    (native : OperationDescription.Description) (queue : GenericDutyQueue.Checked catalogue) (rootOwner rootName : String) where
  site : Site checked native
  owner : String
  name : String
  path : RuntimeOrdinaryBody.CallPath artifact.sources rootOwner rootName owner name
  record : RecordIndex catalogue
  invocation : Invocation catalogue record
  binding : Binding queue path invocation
  result : Subject artifact.sources
  remaining : Transport invocation.applications.reverse site.transfer.result.subject result

def taskOf {artifact catalogue context description graph implementations references prepared root requested checked native
    queue rootOwner rootName owner name path record invocation result}
    (site : @Site artifact catalogue context description graph implementations references prepared root requested checked native)
    (binding : @Binding artifact.sources catalogue queue rootOwner rootName owner name path record invocation)
    (remaining : Transport invocation.applications.reverse site.transfer.result.subject result) : Task checked native queue rootOwner rootName :=
  ⟨site,owner,name,path,record,invocation,binding,result,remaining⟩

def AtOuter {artifact catalogue context description graph implementations references prepared root requested checked native
    queue rootOwner rootName owner name path record invocation result site}
    (f : @Focused artifact catalogue context description graph implementations references prepared root requested checked native site)
    (binding : @Binding artifact.sources catalogue queue rootOwner rootName owner name path record invocation)
    (remaining : Transport invocation.applications.reverse site.transfer.result.subject result) : Type :=
  match binding,remaining with
  | .root ..,_ => Empty
  | .named (event := event) (invocation := previous) (application := supplying) (target := target) _ _,receipt =>
    Children f event supplying.original (RuntimeFormalActual.splitInvocation previous supplying target receipt).transfer

private def readOuter {artifact catalogue context description graph implementations references prepared root requested checked native
    queue rootOwner rootName owner name path record invocation result site}
    (f : @Focused artifact catalogue context description graph implementations references prepared root requested checked native site)
    (binding : @Binding artifact.sources catalogue queue rootOwner rootName owner name path record invocation)
    (remaining : Transport invocation.applications.reverse site.transfer.result.subject result) : WorkM (AtOuter f binding remaining) :=
  match binding,remaining with
  | .root ..,_ => throw .request
  | .named (event := event) (invocation := previous) (application := supplying) (target := target) _ _,receipt =>
    readChildren f event supplying.original (RuntimeFormalActual.splitInvocation previous supplying target receipt).transfer

private def concreteHead : OperationDescription.Node → Bool
  | .formal .. => false
  | _ => true

inductive Next {artifact catalogue context description graph implementations references prepared root requested checked native queue rootOwner rootName}
    (task : @Task artifact catalogue context description graph implementations references prepared root requested checked native queue rootOwner rootName)
    (f : Focused task.site) where
  | terminal (source : f.source.uses.isEmpty = true) (closed : f.expected = [])
      (nativeHead : concreteHead task.site.leaf.child.cursor.node = true)
  | named (needed : f.expected ≠ []) (outer : AtOuter f task.binding task.remaining)
      (read : Computed (readOuter f task.binding task.remaining) outer)

structure Step {artifact catalogue context description graph implementations references prepared root requested checked native queue rootOwner rootName}
    (task : @Task artifact catalogue context description graph implementations references prepared root requested checked native queue rootOwner rootName) where
  focus : Focused task.site
  focused : Computed (readFocus task.site) focus
  next : Next task focus

private def advance {artifact catalogue context description graph implementations references prepared root requested checked native queue rootOwner rootName}
    (task : @Task artifact catalogue context description graph implementations references prepared root requested checked native queue rootOwner rootName) :
    WorkM (Step task) := do
  let focus ← NaturalAffine.witness (readFocus task.site)
  if empty : focus.val.expected = [] then
    if done : focus.val.source.uses.isEmpty = true ∧ concreteHead task.site.leaf.child.cursor.node = true then
      return ⟨focus.val,by with_reducible exact focus.property,.terminal done.1 empty done.2⟩
    else throw .request
  else
    let outer ← NaturalAffine.witness (readOuter focus.val task.binding task.remaining)
    return ⟨focus.val,by with_reducible exact focus.property,.named empty outer.val (by with_reducible exact outer.property)⟩

private def successors {artifact catalogue context description graph implementations references prepared root requested checked native
    queue rootOwner rootName owner name path record invocation result site}
    (f : @Focused artifact catalogue context description graph implementations references prepared root requested checked native site)
    (binding : @Binding artifact.sources catalogue queue rootOwner rootName owner name path record invocation)
    (remaining : Transport invocation.applications.reverse site.transfer.result.subject result) :
    AtOuter f binding remaining → List (Task checked native queue rootOwner rootName) :=
  match binding,remaining with
  | .root ..,_ => fun impossible => nomatch impossible
  | .named (invocation := previous) (application := supplying) (target := target) prior _,receipt => fun outer =>
    let tail := (RuntimeFormalActual.splitInvocation previous supplying target receipt).tail
    let ancestors := site.positions
    outer.entries.map fun entry => taskOf (Site.ofLeaf ancestors entry.leaf) prior tail

def Step.children {artifact catalogue context description graph implementations references prepared root requested checked native queue rootOwner rootName task}
    (step : @Step artifact catalogue context description graph implementations references prepared root requested checked native queue rootOwner rootName task) :
    List (Task checked native queue rootOwner rootName) :=
  match step.next with
  | .terminal .. => []
  | .named _ outer _ => successors step.focus task.binding task.remaining outer

inductive Tree {artifact catalogue context description graph implementations references prepared root requested checked native queue rootOwner rootName} :
    @Task artifact catalogue context description graph implementations references prepared root requested checked native queue rootOwner rootName → Type where
  | node {task} (step : Step task) (read : Computed (advance task) step)
      (children : (i : Fin step.children.length) → Tree step.children[i]) : Tree task

private def allFin : (n : Nat) → {p : Fin n → Type} → ((i : Fin n) → WorkM (p i)) → WorkM ((i : Fin n) → p i) :=
  Nat.rec (motive := fun n => {p : Fin n → Type} → ((i : Fin n) → WorkM (p i)) → WorkM ((i : Fin n) → p i))
    (fun {_} _ => pure fun i => Fin.elim0 i)
    (fun _ next {_} f => do
      let first ← f 0
      let rest ← next (fun i => f i.succ)
      return Fin.cases first rest)

private def visit {artifact catalogue context description graph implementations references prepared root requested checked native queue rootOwner rootName} :
    Nat → (task : @Task artifact catalogue context description graph implementations references prepared root requested checked native queue rootOwner rootName) →
    WorkM (Tree task) :=
  Nat.rec (motive := fun _ => (task : @Task artifact catalogue context description graph implementations references prepared
      root requested checked native queue rootOwner rootName) → WorkM (Tree task))
    (fun _ => throw .limit)
    (fun _ next task => do
      let step ← NaturalAffine.witness (advance task)
      let children := step.val.children
      exactWork (Exact.charge (16*(children.length+1)^2))
      let result ← allFin children.length (fun i => next children[i])
      return .node step.val (by with_reducible exact step.property) result)

def read {artifact : Artifact} {catalogue context description graph implementations references prepared root requested checked native
    caller original sourceOwner sourceName originalHeader helpers environment scope genericState tokens event app start
    queue rootOwner rootName owner name path record invocation result}
    {inst : @StaticInstantiation.Checked artifact.sources sourceOwner sourceName originalHeader}
    {uses : List (OperationSourceUses.Use inst helpers environment scope genericState tokens)}
    {transfer : GenericOperationSubstitute.Checked app original}
    (prior : @Binding artifact.sources catalogue queue rootOwner rootName owner name path record invocation)
    (remaining : Transport invocation.applications.reverse transfer.result.subject result)
    (entries : List (@RuntimeInteriorSupply.Entry artifact catalogue context description graph implementations references prepared root requested checked native caller
      original sourceOwner sourceName originalHeader helpers environment scope genericState tokens inst uses event app transfer start)) :
    WorkM ((i : Fin entries.length) → Tree (taskOf (Site.ofLeaf [] entries[i].leaf) prior remaining)) := do
  exactWork (Exact.charge (16*((entries.length+1)^2+invocation.depth+1)))
  allFin entries.length (fun i => visit (invocation.depth+1) (taskOf (Site.ofLeaf [] entries[i].leaf) prior remaining))

end QleisliKernel.Qirf.RuntimeTransitiveInterior
