import QleisliKernel.SourceTypes.GenericDutyQueue
import QleisliKernel.SourceTypes.QuantumSignatureCore
import QleisliKernel.Raw.OwnerFlow

/-! Internal original-duty slot expectations, without wire or acceptance use.
Canonical header references retain their exact original call and header target.
Every operation child edge is visited in postorder, including unused and zero
children; a free parent does not erase a closed child. Original supplier scopes
and freshly selected Meaning occurrences stay attached to their source duties.
An expectation is not a native ProviderInstance, body/path/Meaning equation or
accepted slot. Those missing bindings remain explicit below. No artifact root,
body request index, producer success or whole-catalogue relevance is accepted.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.SourceDutySlots
open QleisliKernel Finite SourceTypes
open GenericOperation GenericOperationSubstitute GenericDutyQueue

abbrev Computed {α : Type} (action : WorkM α) (value : α) : Prop :=
  ∃ before after,action.run before = (.ok value,after)

private def noPaths : OperationPaths.Paths := ⟨false,false,false⟩

private def tokenFields (tokens : List LocatedToken) : Nat :=
  (tokens.map fun token => token.text.utf8ByteSize+4).sum

private def stringFields (texts : List String) : Nat :=
  (texts.map fun text => text.utf8ByteSize+1).sum

private def rowFields (rows : List (String × String)) : Nat :=
  (rows.map fun (owner,source) => owner.utf8ByteSize+source.utf8ByteSize+2).sum

/-- Flatten original roots once. Equality proofs retain the exact queue, while
the array and finite range avoid repeated root/list traversal at runtime. -/
structure Indexed {sources catalogue} (queue : @GenericDutyQueue.Checked sources catalogue) where
  items : List (Item catalogue)
  original : items = queue.items
  array : Array (Item catalogue)
  converted : array = items.toArray
  indices : List (Fin queue.items.length)
  every : indices = List.finRange queue.items.length

def Indexed.at {sources catalogue queue} (indexed : @Indexed sources catalogue queue)
    (index : Fin queue.items.length) : Item catalogue :=
  indexed.array[index.val]'(by simpa only [indexed.converted,List.size_toArray,indexed.original] using index.isLt)

theorem Indexed.at_original {sources catalogue queue} (indexed : @Indexed sources catalogue queue)
    (index : Fin queue.items.length) : indexed.at index = queue.items[index.val]'index.isLt := by
  simp only [Indexed.at,indexed.converted,List.getElem_toArray,indexed.original]

def Indexed.complete {sources catalogue queue} (indexed : @Indexed sources catalogue queue) : Bool :=
  !indexed.items.any Item.unresolved

theorem Indexed.complete_original {sources catalogue queue} (indexed : @Indexed sources catalogue queue) :
    indexed.complete = queue.complete := by
  simp only [Indexed.complete,indexed.original,GenericDutyQueue.Checked.complete]

private def readIndexed {sources catalogue} (queue : @GenericDutyQueue.Checked sources catalogue) : WorkM (Indexed queue) := do
  -- Root traversal costs R even when most roots have no activity. The next
  -- reservation covers N item cells, one array conversion and one index range.
  exactWork (Exact.charge (16*(queue.roots.length+1)))
  let items := queue.items
  exactWork (Exact.charge (32*(items.length+1)))
  let array := items.toArray
  let indices := List.finRange items.length
  return ⟨items,rfl,array,rfl,indices,rfl⟩

structure View (description : Description) where
  index : Nat
  path : List Nat
  requested : OperationPaths.Paths
  node : GenericOperation.Node
  originalNode : description.nodes[index]? = some node
  selection : GenericOperation.Selection
  selected : Computed (GenericOperation.select description index) selection
  status : GenericOperation.Status selection.subject
  classified : Computed (GenericOperation.close selection.subject) status

/-- Actual recursive child order, not the overlapping preorder fragment views.
All scalar formation checks still run. A signed guarded form without an exact
projection of the existing inactivity receipt refuses here. -/
private def walk (description : Description) : Nat → Nat → List Nat → OperationPaths.Paths →
    Nat → WorkM (Nat × List (View description)) :=
  Nat.rec (fun _ _ _ _ => throw .limit) (fun _ next index path requested visited => do
    guard (visited < 4096) .limit
    exactWork (Exact.charge (8*(description.nodes.length+path.length+1)))
    match originalNode : description.nodes[index]? with
    | none => throw .request
    | some node =>
      exactWork (Exact.charge (16*(Meter.node node+path.length+1)*(node.children.length+1)))
      let shape ← node.pathShape
      let children := shape.children requested
      let (visited,previous) ← children.zipIdx.foldlM
        (fun (visited,previous) ((child,paths),ordinal) => do
          let (visited,entries) ← next child (path ++ [ordinal]) paths visited
          return (visited,previous ++ entries)) (visited+1,[])
      let selection ← NaturalAffine.witness (GenericOperation.select description index)
      let status ← NaturalAffine.witness (GenericOperation.close selection.val.subject)
      let current : View description :=
        ⟨index,path,requested,node,originalNode,selection.val,
          by with_reducible exact selection.property,status.val,by with_reducible exact status.property⟩
      return (visited,previous ++ [current]))

def readViews (description : Description) (requested : OperationPaths.Paths) : WorkM (List (View description)) := do
  exactWork (Exact.charge (Meter.rebuildWork description))
  guard (!description.nodes.isEmpty && description.nodes.length ≤ 4096 &&
    description.root+1 == description.nodes.length && description.nodeFrames.length == description.nodes.length &&
    description.nodes.zipIdx.all (fun (node,index) => node.children.all (· < index))) .request
  return (← walk description (description.nodes.length+1) description.root [] requested 0).2

structure Supplier {sources} (subject : Subject sources) (index : Nat) where
  origin : GenericOperation.Origin sources
  selected : subject.suppliers.filter (·.1 == index) = [(index,origin)]

private def readSupplier {sources} (subject : Subject sources) (index : Nat) : WorkM (Supplier subject index) := do
  exactWork (Exact.charge (16*(subject.suppliers.length+1)))
  match selected : subject.suppliers.filter (·.1 == index) with
  | [(original,origin)] =>
    if same : original = index then
      return ⟨origin,by first | simpa only [same] using selected | rfl⟩
    else throw .request
  | _ => throw .request

structure OperationArgument (parent : OperationDescription.Description) where
  name : String
  root : Nat
  indices : List Nat
  description : OperationDescription.Description
  selected : parent.selection root = some (indices,description)

/-- Forward header expectation only. The exact caller and source query are
retained, but supplier Origin/Transport has not become a native graph argument
receipt. No caller may treat this value as RuntimeProviderHeader.Original. -/
structure Provider {sources catalogue record invocation}
    (demand : @Demand sources catalogue record invocation)
    (view : View demand.transported.subject.description) where
  closed : GenericOperation.Closed view.selection.subject
  originalStatus : view.status = .closed closed
  owner : String
  name : String
  bases : List (String × Semantics.FiniteCarrier.Basis)
  naturals : List (String × Nat)
  operations : List (String × Nat)
  originalProvider : closed.data.description.nodes[closed.data.description.root]? =
    some (.provider owner name bases naturals operations)
  supplier : Supplier demand.transported.subject view.index
  written : StaticApplication.Syntax supplier.origin.tokens
  parsed : StaticApplication.readSyntax supplier.origin.tokens = .ok written
  candidate : CallName.Checked sources supplier.origin.state.owner supplier.origin.scope written.callee
  queried : Computed (CallName.read sources supplier.origin.state.owner supplier.origin.scope written.callee) candidate
  resolution : Resolved
  resolved : CallName.candidateResolution candidate = some resolution
  target : resolution.moduleName = owner ∧ resolution.declaration.name = name
  actuals : List (OperationArgument closed.data.description)
  actualOrder : actuals.map (fun actual => (actual.name,actual.root)) = operations
  signature : QuantumSignatureCore.Checked sources owner name
  signatureRead : Computed (QuantumSignatureCore.prepareWithArguments sources owner name
    ⟨bases,naturals,actuals.map (fun actual => (actual.name,actual.description))⟩
    (some catalogue.originals) (some catalogue.helpers)) signature
  original : signature.original.source = resolution.source ∧ signature.original.declaration = resolution.declaration
  inference : GenericCatalogue.Entry catalogue.toRuntimeChecked signature.original
  inferred : Computed (GenericCatalogue.lookup catalogue.toRuntimeChecked signature.original) inference

def Provider.expectedEffect {sources catalogue record invocation demand view}
    (provider : @Provider sources catalogue record invocation demand view) : Semantics.Raw.Effect :=
  SourceEffect.visible provider.supplier.origin.state.owner provider.owner provider.signature.original.declaration.isPublic
    provider.signature.original.parsedHeader.effect provider.inference.inferred.inferredEffect

private def readProvider {sources catalogue record invocation}
    (demand : @Demand sources catalogue record invocation) (view : View demand.transported.subject.description)
    (closed : GenericOperation.Closed view.selection.subject) (originalStatus : view.status = .closed closed) :
    WorkM (Provider demand view) := do
  match originalProvider : closed.data.description.nodes[closed.data.description.root]? with
  | some (.provider owner name bases naturals operations) =>
    let supplier ← readSupplier demand.transported.subject view.index
    exactWork (Exact.charge (32*(supplier.origin.tokens.length+1)*(tokenFields supplier.origin.tokens+1)))
    match parsed : StaticApplication.readSyntax supplier.origin.tokens with
    | .error _ => throw .request
    | .ok written =>
      let candidate ← NaturalAffine.witness
        (CallName.read sources supplier.origin.state.owner supplier.origin.scope written.callee)
      match resolved : CallName.candidateResolution candidate.val with
      | none => throw .request
      | some resolution =>
        exactWork (Exact.charge (32*(owner.utf8ByteSize+name.utf8ByteSize+resolution.moduleName.utf8ByteSize+
          resolution.declaration.name.utf8ByteSize+operations.length+1)))
        if target : resolution.moduleName = owner ∧ resolution.declaration.name = name then
          let actuals ← operations.mapM fun (argumentName,root) => do
            exactWork (Exact.charge (Meter.rebuildWork view.selection.subject))
            match selected : closed.data.description.selection root with
            | none => throw .request
            | some (indices,description) =>
              return (⟨argumentName,root,indices,description,selected⟩ : OperationArgument closed.data.description)
          exactWork (Exact.charge (16*((operations.map fun (argumentName,_) => argumentName.utf8ByteSize+2).sum+
            operations.length+1)))
          if actualOrder : actuals.map (fun actual => (actual.name,actual.root)) = operations then
            let arguments : StaticTypes.Arguments :=
              ⟨bases,naturals,actuals.map (fun actual => (actual.name,actual.description))⟩
            let signature ← NaturalAffine.witness (QuantumSignatureCore.prepareWithArguments sources owner name arguments
              (some catalogue.originals) (some catalogue.helpers))
            exactWork (Exact.charge (32*(signature.val.original.source.utf8ByteSize+resolution.source.utf8ByteSize+1)))
            if original : signature.val.original.source = resolution.source ∧
                signature.val.original.declaration = resolution.declaration then
              let inference ← NaturalAffine.witness (GenericCatalogue.lookup catalogue.toRuntimeChecked signature.val.original)
              return ⟨closed,originalStatus,owner,name,bases,naturals,operations,originalProvider,supplier,written,parsed,
                candidate.val,by with_reducible exact candidate.property,resolution,resolved,target,actuals,actualOrder,
                signature.val,by with_reducible exact signature.property,original,
                inference.val,by with_reducible exact inference.property⟩
            else throw .request
          else throw .request
        else throw .request
  | _ => throw .request

def MeaningTokens {sources} (duty : GenericOperation.Duty sources) : Except String (List String) := do
  match duty.kind with
  | .checkedMeaning =>
    let call ← CallSyntax.read duty.origin.tokens
    if call.call.callee.map (·.text) != ["checked_op"] then throw "not the original checked_op assertion"
    let [_,meaning] := call.call.arguments | throw "not the original checked_op argument pair"
    return meaning.tokens.map (·.text)
  | .formalMeaning key =>
    if key.moduleName != duty.origin.state.owner || key.declarationName != duty.origin.state.name then
      throw "formal Meaning belongs to another original declaration"
    let some formal := duty.origin.state.prepared.original.header.formals[key.ordinal]?
      | throw "original mixed formal absent"
    if formal.ordinal != key.ordinal then throw "original mixed formal ordinal differs"
    let .operation tokens := formal.kind | throw "original formal is not an operation"
    let parsed ← OperationPorts.read tokens
    let some meaning := parsed.meaning | throw "original formal has no Meaning"
    return meaning
  | _ => throw "unsupported original Meaning occurrence"

structure Meaning {sources catalogue record invocation}
    (demand : @Demand sources catalogue record invocation) (request : SourceMeaning.Request sources) where
  tokens : List String
  extracted : MeaningTokens demand.source.original = .ok tokens
  selected : SourceMeaning.Selected sources demand.source.original.origin.state.owner
    demand.source.original.origin.scope tokens
  queried : Computed (SourceMeaning.select sources demand.source.original.origin.state.owner
    demand.source.original.origin.scope tokens) selected
  -- These metadata equalities do not bind the full fresh graph to the
  -- original request graph under the retained simultaneous substitutions.
  -- Reference bodies, phase and composed nodes still require graph transfer.
  sameRequest : request.caller = some demand.source.original.origin.state.owner ∧
    selected.resolution.moduleName = request.moduleName ∧
    selected.resolution.declaration.name = request.declarationName ∧ selected.queryRows = request.queryRows
  ports : selected.meaning.graph.input = request.meaning.graph.input ∧
    selected.meaning.graph.output = request.meaning.graph.output

private def readMeaning {sources catalogue record invocation}
    (demand : @Demand sources catalogue record invocation) (request : SourceMeaning.Request sources) :
    WorkM (Meaning demand request) := do
  let duty := demand.source.original
  let formalTokens := duty.origin.state.prepared.original.header.formals.foldl (fun fields formal =>
    fields+1+match formal.kind with | .operation tokens => stringFields tokens | _ => 0) 0
  exactWork (Exact.charge (32*(duty.origin.tokens.length+formalTokens+1)*
    (tokenFields duty.origin.tokens+stringFields duty.origin.scope+formalTokens+1)))
  match extracted : MeaningTokens demand.source.original with
  | .error _ => throw .request
  | .ok tokens =>
    let selected ← NaturalAffine.witness (SourceMeaning.select sources demand.source.original.origin.state.owner
      demand.source.original.origin.scope tokens)
    -- Equality below reads the complete original query rows and name bytes.
    -- A row count is insufficient when rows retain original source text.
    exactWork (Exact.charge (16*(duty.origin.state.owner.utf8ByteSize+
      (request.caller.map String.utf8ByteSize).getD 0+
      selected.val.resolution.moduleName.utf8ByteSize+request.moduleName.utf8ByteSize+
      selected.val.resolution.declaration.name.utf8ByteSize+request.declarationName.utf8ByteSize+
      rowFields selected.val.queryRows+rowFields request.queryRows+1)))
    if sameRequest : request.caller = some demand.source.original.origin.state.owner ∧
        selected.val.resolution.moduleName = request.moduleName ∧
        selected.val.resolution.declaration.name = request.declarationName ∧ selected.val.queryRows = request.queryRows then
      exactWork (Exact.charge (32*(Raw.OwnerFlow.fields [⟨0,selected.val.meaning.graph.input⟩,⟨1,selected.val.meaning.graph.output⟩]+
        Raw.OwnerFlow.fields [⟨0,request.meaning.graph.input⟩,⟨1,request.meaning.graph.output⟩]+1)))
      if ports : selected.val.meaning.graph.input = request.meaning.graph.input ∧
          selected.val.meaning.graph.output = request.meaning.graph.output then
        return ⟨tokens,extracted,selected.val,by with_reducible exact selected.property,sameRequest,ports⟩
      else throw .request
    else throw .request

structure QuantumReference {sources catalogue record invocation demand request}
    (meaning : @Meaning sources catalogue record invocation demand request) where
  index : Fin meaning.selected.meaning.graph.nodes.length
  reference : SourceMeaning.QuantumReference sources
  original : (meaning.selected.meaning.graph.nodes[index.val]'index.isLt).action = .reference reference

def readReferences {sources catalogue record invocation demand request}
    (meaning : @Meaning sources catalogue record invocation demand request) :
    WorkM (List (QuantumReference meaning)) := do
  let nodes := meaning.selected.meaning.graph.nodes
  exactWork (Exact.charge (16*(nodes.length+1)^2))
  return (List.finRange nodes.length).filterMap fun index =>
    match original : (nodes[index.val]'index.isLt).action with
    | .reference reference => some ⟨index,reference,original⟩
    | _ => none

inductive ClassicalKind where
  | permutation
  | phase
  deriving BEq, DecidableEq, Repr

def ClassicalKind.action {sources} (kind : ClassicalKind) (reference : SourceMeaning.ClassicalReference sources) :
    SourceMeaning.Action sources :=
  match kind with | .permutation => .permutation reference | .phase => .phase reference

/-- These are original ordinary-source obligations, never quantum body slots.
Their later consumer must run the independent original tree evaluator on every
canonical input and bind each result to the symbolic row and exact ports. -/
structure ClassicalReference {sources catalogue record invocation demand request}
    (meaning : @Meaning sources catalogue record invocation demand request) where
  index : Fin meaning.selected.meaning.graph.nodes.length
  kind : ClassicalKind
  reference : SourceMeaning.ClassicalReference sources
  original : (meaning.selected.meaning.graph.nodes[index.val]'index.isLt).action = kind.action reference

def readClassicalReferences {sources catalogue record invocation demand request}
    (meaning : @Meaning sources catalogue record invocation demand request) :
    WorkM (List (ClassicalReference meaning)) := do
  let nodes := meaning.selected.meaning.graph.nodes
  exactWork (Exact.charge (16*(nodes.length+1)^2))
  return (List.finRange nodes.length).filterMap fun index =>
    match original : (nodes[index.val]'index.isLt).action with
    | .permutation reference => some ⟨index,.permutation,reference,original⟩
    | .phase reference => some ⟨index,.phase,reference,original⟩
    | _ => none

inductive MeaningPlan {sources catalogue record invocation}
    (demand : @Demand sources catalogue record invocation) where
  | access (paths : OperationPaths.Paths) (original : demand.source.original.requirement = .access paths)
  | assertion (request : SourceMeaning.Request sources)
      (original : demand.source.original.requirement = .meaning request)
      (meaning : Meaning demand request) (references : List (QuantumReference meaning))
      (ordered : Computed (readReferences meaning) references)
      (classical : List (ClassicalReference meaning))
      (classicalOrdered : Computed (readClassicalReferences meaning) classical)

private def readMeaningPlan {sources catalogue record invocation}
    (demand : @Demand sources catalogue record invocation) : WorkM (MeaningPlan demand) := do
  match original : demand.source.original.requirement with
  | .access paths => return .access paths (by first | exact original | rfl)
  | .meaning request =>
    let meaning ← readMeaning demand request
    let references ← NaturalAffine.witness (readReferences meaning)
    let classical ← NaturalAffine.witness (readClassicalReferences meaning)
    return .assertion request (by first | exact original | rfl) meaning references.val
      (by with_reducible exact references.property) classical.val (by with_reducible exact classical.property)

def MeaningPlan.referenceIndices {sources catalogue record invocation demand}
    (meaning : @MeaningPlan sources catalogue record invocation demand) : List Nat :=
  match meaning with | .access .. => [] | .assertion _ _ _ references _ _ _ => references.map (·.index.val)

def MeaningPlan.classicalIndices {sources catalogue record invocation demand}
    (meaning : @MeaningPlan sources catalogue record invocation demand) : List Nat :=
  match meaning with | .access .. => [] | .assertion _ _ _ _ _ classical _ => classical.map (·.index.val)

/-- Only forward quantum bodies consume these future slots. Primitives have
zero body slots; ordinary Meaning references have independent source duties.
No numerical body index or accepted body is supplied by this internal plan. -/
inductive BodyRole where
  | provider (path : List Nat)
  | quantumReference (node : Nat)
  deriving BEq, DecidableEq, Repr

/- The remaining source-instance/typed-port and forward-body bindings are
obligations, not facts derived from a fresh name or a closed descriptor. -/
inductive Pending where
  | supplierInstance (path : List Nat)
  | forwardProviderBody (path : List Nat)
  | providerPaths (path : List Nat) (requested : OperationPaths.Paths)
  | meaningInstancePorts
  | meaningGraphBinding
  | meaningEquation
  | forwardReferenceBody (index : Nat)
  | classicalReferenceRows (index : Nat)
  | runtimeGroupInstance
  deriving BEq, DecidableEq, Repr

structure DemandPlan {sources catalogue record invocation}
    (demand : @Demand sources catalogue record invocation) where
  views : List (View demand.transported.subject.description)
  ordered : Computed (readViews demand.transported.subject.description
    (match demand.source.original.requirement with | .access paths => paths | .meaning _ => noPaths)) views
  providers : List (Sigma (Provider demand))
  providerOrder : providers.map (fun provider => provider.1.path) =
    (views.filter fun view => match view.node,view.status with
      | .provider ..,.closed _ => true | _,_ => false).map (·.path)
  meaning : MeaningPlan demand
  pending : List Pending

def DemandPlan.rootClosed {sources catalogue record invocation demand}
    (plan : @DemandPlan sources catalogue record invocation demand) : Bool :=
  plan.views.any fun view => view.path.isEmpty && match view.status with | .closed _ => true | .conditional .. => false

def DemandPlan.bodyRoles {sources catalogue record invocation demand}
    (plan : @DemandPlan sources catalogue record invocation demand) : List BodyRole :=
  plan.providers.map (fun provider => .provider provider.1.path) ++
    (if plan.rootClosed then plan.meaning.referenceIndices.map BodyRole.quantumReference else [])

private def readDemand {sources catalogue record invocation}
    (demand : @Demand sources catalogue record invocation) : WorkM (DemandPlan demand) := do
  let requested := match demand.source.original.requirement with | .access paths => paths | .meaning _ => noPaths
  let views ← NaturalAffine.witness (readViews demand.transported.subject.description requested)
  exactWork (Exact.charge (16*(views.val.length+(views.val.map fun view => view.path.length+1).sum+1)))
  let providerAction : WorkM (List (Sigma (Provider demand))) := views.val.foldlM (fun previous view => do
    match view.node with
    | .provider .. =>
      match originalStatus : view.status with
      | .conditional .. => return previous
      | .closed closed => return ⟨view,← readProvider demand view closed (by first | exact originalStatus | rfl)⟩ :: previous
    | _ => return previous) []
  let providers := (← providerAction).reverse
  if providerOrder : providers.map (fun provider => provider.1.path) =
      (views.val.filter fun view => match view.node,view.status with
        | .provider ..,.closed _ => true | _,_ => false).map (·.path) then
    let meaning ← readMeaningPlan demand
    let rootClosed := views.val.any fun view => view.path.isEmpty &&
      match view.status with | .closed _ => true | .conditional .. => false
    let pending := providers.flatMap (fun provider =>
      [Pending.supplierInstance provider.1.path,.forwardProviderBody provider.1.path] ++
        (if provider.1.requested.any then [.providerPaths provider.1.path provider.1.requested] else [])) ++
      (match demand.source.original.requirement with
        | .meaning _ => [.meaningInstancePorts,.meaningGraphBinding] | .access _ => []) ++
      (if rootClosed then meaning.referenceIndices.map Pending.forwardReferenceBody ++
        meaning.classicalIndices.map Pending.classicalReferenceRows ++
          (match demand.source.original.requirement with | .meaning _ => [.meaningEquation] | .access _ => []) else []) ++
      (if demand.source.original.runtimeApplication.isSome then [.runtimeGroupInstance] else [])
    return ⟨views.val,by with_reducible exact views.property,providers,providerOrder,meaning,pending⟩
  else throw .request

/-- The header's binding and original call are retained in addition to its ID.
The canonical target must be the exact original callee record/header activity
and the complete indexed invocation path reached by that call. -/
private def CallMatches {sources catalogue record invocation}
    (reference : @HeaderReference sources catalogue record invocation) (item : Item catalogue) : Prop :=
  match item with
    | .call parent application target =>
      parent.id = invocation.id ∧ application.id = reference.occurrence.id ∧
      target.entry.index.val = reference.target.entry.index.val
    | _ => False

private def DemandMatches {sources catalogue record invocation}
    (reference : @HeaderReference sources catalogue record invocation) (item : Item catalogue) : Prop :=
  match item with
    | .demand (record := targetRecord) target checked =>
      targetRecord.val = reference.target.entry.index.val ∧
      target.id = (Invocation.call invocation reference.occurrence reference.target).id ∧
      checked.source.index.val = reference.header.index.val ∧ checked.source.original.kind = reference.header.original.kind ∧
      checked.id = reference.id
    | _ => False

private instance {sources catalogue record invocation}
    (reference : @HeaderReference sources catalogue record invocation) (item : Item catalogue) :
    Decidable (CallMatches reference item) := by cases item <;> dsimp [CallMatches] <;> infer_instance

private instance {sources catalogue record invocation}
    (reference : @HeaderReference sources catalogue record invocation) (item : Item catalogue) :
    Decidable (DemandMatches reference item) := by cases item <;> dsimp [DemandMatches] <;> infer_instance

structure HeaderLink {sources catalogue record invocation}
    (queue : GenericDutyQueue.Checked catalogue)
    (reference : @HeaderReference sources catalogue record invocation) where
  callIndex : Fin queue.items.length
  demandIndex : Fin queue.items.length
  callMatches : CallMatches reference (queue.items[callIndex.val]'callIndex.isLt)
  demandMatches : DemandMatches reference (queue.items[demandIndex.val]'demandIndex.isLt)
  uniqueCall : (List.finRange queue.items.length).filter
    (fun index => decide (CallMatches reference (queue.items[index.val]'index.isLt))) = [callIndex]
  uniqueDemand : (List.finRange queue.items.length).filter
    (fun index => decide (DemandMatches reference (queue.items[index.val]'index.isLt))) = [demandIndex]

private def kindFields (kind : RequirementKind) : Nat :=
  match kind.formal? with | none => 1 | some key => Meter.key key+1

private def itemIdentityFields {sources catalogue} : @Item sources catalogue → Nat
  | .demand invocation demand => invocation.id.calls.length+kindFields demand.source.original.kind+5
  | .header invocation reference => invocation.id.calls.length+kindFields reference.header.original.kind+5
  | .call invocation _ _ | .pendingRecursion invocation _ _ _ => invocation.id.calls.length+4

private def readHeader {sources catalogue record invocation}
    {queue : GenericDutyQueue.Checked catalogue} (indexed : Indexed queue)
    (reference : @HeaderReference sources catalogue record invocation) : WorkM (HeaderLink queue reference) := do
  -- The two uniqueness scans compare original indexed paths and mixed-formal
  -- keys. Retain the conservative scan allowance and all key/depth charges;
  -- lookups now use the one retained array. No source snapshot, result matrix
  -- or supplier function is compared.
  let fields := (indexed.items.map itemIdentityFields).sum
  let referenceFields := invocation.id.calls.length+kindFields reference.header.original.kind+5
  exactWork (Exact.charge (32*((indexed.items.length+1)^2+
    (indexed.items.length+1)*(fields+referenceFields+1))))
  let callMatch := fun index : Fin queue.items.length => CallMatches reference (indexed.at index)
  let demandMatch := fun index : Fin queue.items.length => DemandMatches reference (indexed.at index)
  match uniqueCall : indexed.indices.filter (fun index => decide (callMatch index)) with
  | [callIndex] =>
    match uniqueDemand : indexed.indices.filter (fun index => decide (demandMatch index)) with
    | [demandIndex] =>
      if callMatches : callMatch callIndex then
        if demandMatches : demandMatch demandIndex then
          return ⟨callIndex,demandIndex,
            by simpa only [callMatch,Indexed.at_original] using callMatches,
            by simpa only [demandMatch,Indexed.at_original] using demandMatches,
            by simpa only [callMatch,indexed.every,Indexed.at_original] using uniqueCall,
            by simpa only [demandMatch,indexed.every,Indexed.at_original] using uniqueDemand⟩
        else throw .request
      else throw .request
    | _ => throw .request
  | _ => throw .request

def ItemExpectation {sources catalogue} (queue : @GenericDutyQueue.Checked sources catalogue) : Item catalogue → Type
  | .demand _ demand => DemandPlan demand
  | .header _ reference => HeaderLink queue reference
  | .call .. => Unit
  | .pendingRecursion .. => Empty

def ItemPlan {sources catalogue} (queue : @GenericDutyQueue.Checked sources catalogue)
    (index : Fin queue.items.length) : Type :=
  ItemExpectation queue (queue.items[index.val]'index.isLt)

private def readExpectation {sources catalogue queue} (indexed : @Indexed sources catalogue queue)
    (item : Item catalogue) : WorkM (ItemExpectation queue item) := do
  match item with
  | .demand _ demand => readDemand demand
  | .header _ reference => readHeader indexed reference
  | .call .. => pure ()
  | .pendingRecursion .. => throw .request

private def readItem {sources catalogue queue} (indexed : @Indexed sources catalogue queue)
    (index : Fin queue.items.length) : WorkM (ItemPlan queue index) := do
  let expectation ← readExpectation indexed (indexed.at index)
  return (show ItemExpectation queue (queue.items[index.val]'index.isLt) from
    indexed.at_original index ▸ expectation)

structure Entry {sources catalogue queue} (indexed : @Indexed sources catalogue queue) where
  index : Fin queue.items.length
  subject : Item catalogue
  atIndex : subject = queue.items[index.val]'index.isLt
  expectation : ItemPlan queue index
  computed : Computed (readItem indexed index) expectation

def Entry.subjectExpectation {sources catalogue queue indexed} (entry : @Entry sources catalogue queue indexed) :
    ItemExpectation queue entry.subject := entry.atIndex.symm ▸ entry.expectation

structure Plan {sources catalogue} (queue : @GenericDutyQueue.Checked sources catalogue) where
  indexed : Indexed queue
  indexing : Computed (readIndexed queue) indexed
  acyclic : queue.complete = true
  entries : List (Entry indexed)
  every : entries.map (·.index) = List.finRange queue.items.length

structure Address {sources catalogue} (queue : @GenericDutyQueue.Checked sources catalogue) where
  index : Fin queue.items.length
  requirement : RequirementId
  role : BodyRole

private def addresses {sources catalogue} (queue : @GenericDutyQueue.Checked sources catalogue)
    (index : Fin queue.items.length) (item : Item catalogue) : ItemExpectation queue item → List (Address queue) :=
  match item with
  | .demand _ demand => fun plan => plan.bodyRoles.map fun role => ⟨index,demand.id,role⟩
  | .header .. | .call .. | .pendingRecursion .. => fun _ => []

/-- Queue item order, then complete per-child-edge provider postorder, then
the fresh Meaning graph's quantum-reference order for a closed root. Header
references contribute no duplicate slots. Open root Meanings retain their full
reference templates above; their closed provider siblings remain present.
Each address is only a future forward-body expectation, with all pending
instance, port, path and equation obligations retained by its source entry. -/
def Plan.bodyOrder {sources catalogue queue} (plan : @Plan sources catalogue queue) : List (Address queue) :=
  plan.entries.flatMap fun entry =>
    addresses queue entry.index entry.subject entry.subjectExpectation

/-- Internal source-derived preparation only. There is intentionally no
artifact/body-index input, readiness predicate or conversion to acceptance.
Every supplier-instance, full Meaning port-instance and body/path equation is
still a mandatory later binding. Existing withholding is left untouched. -/
def read {sources catalogue} (queue : @GenericDutyQueue.Checked sources catalogue) : WorkM (Plan queue) := do
  let indexed ← NaturalAffine.witness (readIndexed queue)
  exactWork (Exact.charge (32*(indexed.val.items.length+1)^2))
  if acyclic : indexed.val.complete = true then
    let entries ← indexed.val.indices.mapM fun index => do
      let expectation ← NaturalAffine.witness (readItem indexed.val index)
      return (⟨index,indexed.val.at index,indexed.val.at_original index,
        expectation.val,by with_reducible exact expectation.property⟩ : Entry indexed.val)
    if every : entries.map (·.index) = indexed.val.indices then
      return ⟨indexed.val,by with_reducible exact indexed.property,
        by simpa only [Indexed.complete_original] using acyclic,entries,every.trans indexed.val.every⟩
    else throw .request
  else throw .request

end QleisliKernel.Qirf.SourceDutySlots
