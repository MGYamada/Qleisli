import QleisliKernel.Qirf.RuntimeClosedEvaluation
import QleisliKernel.Qirf.SourceDutySlots

/-! A provider slot of the actual native tree and the source occurrence
that supplied a transported provider. The bounded bare-leaf contract is
separate from the identity of a provider with static arguments or premises.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeClosedProvider
open QleisliKernel Finite SourceTypes
open QleisliKernel.SourceTypes.GenericOperationSubstitute (Subject)
open RuntimeNativeSubject (Cursor)
open RuntimeInterval (Computed)

inductive Spelling (tokens : List LocatedToken) : List LocatedToken → List CallSyntax.Argument → Type where
  | expression (written : StaticApplication.Syntax tokens) (parsed : StaticApplication.readSyntax tokens = .ok written) :
      Spelling tokens written.callee written.arguments
  | call (runtime : CallSyntax.Checked tokens) (parsedCall : CallSyntax.read tokens = .ok runtime)
      (written : StaticApplication.Syntax runtime.call.callee) (parsed : StaticApplication.readSyntax runtime.call.callee = .ok written) :
      Spelling tokens written.callee written.arguments

structure Query (tokens : List LocatedToken) where
  callee : List LocatedToken
  arguments : List CallSyntax.Argument
  spelling : Spelling tokens callee arguments

private def spellingBare {tokens callee arguments} : Spelling tokens callee arguments → Bool
  | .expression written _ => match written with | .name _ => true | .application _ => false
  | .call .. => false

def Query.bare {tokens} (query : Query tokens) : Bool := spellingBare query.spelling

private def readQuery (tokens : List LocatedToken) : WorkM (Option (Query tokens)) := do
  exactWork (Exact.charge (16*(tokens.length+1)*(SourceTrace.Meter.tokenFields tokens+1)))
  if tokens.getLast?.map (·.text) == some ")" then
    match outer : CallSyntax.read tokens with
    | .error _ => return none
    | .ok call =>
      match inner : StaticApplication.readSyntax call.call.callee with
      | .error _ => return none
      | .ok written => return some ⟨_,_,.call call outer written inner⟩
  else
    match parsed : StaticApplication.readSyntax tokens with
    | .error _ => return none
    | .ok written => return some ⟨_,_,.expression written parsed⟩

structure Site {sources} (subject : Subject sources) (index : Nat) where
  supplier : SourceDutySlots.Supplier subject index
  bytes : LocatedFacts.OrderedSlices supplier.origin.state.prepared.original.envelope.source.toUTF8
    supplier.origin.state.prepared.original.envelope.occurrence.openBrace.span.endByte supplier.origin.tokens
  inside : supplier.origin.tokens.all (fun token => token.span.endByte ≤
    supplier.origin.state.prepared.original.envelope.occurrence.closeBrace.span.startByte) = true
  query : Query supplier.origin.tokens
  parsed : Computed (readQuery supplier.origin.tokens) (some query)
  modules : SourceModules.Prepared sources
  candidate : CallName.Checked sources supplier.origin.state.owner supplier.origin.scope query.callee
  queried : Computed (CallName.readWithModules sources (some modules) supplier.origin.state.owner supplier.origin.scope query.callee) candidate
  resolution : Resolved
  resolved : CallName.candidateResolution candidate = some resolution

inductive Pending where
  | originRows | sourceBytes | sourceSyntax | resolution | target | context | inference
  | arguments | premises | meaning | body | ports | effects | paths
  deriving BEq, Repr

def readSite {sources} (catalogue : GenericCatalogue.Checked sources) (subject : Subject sources) (index : Nat) :
    WorkM (Except Pending (Site subject index)) := do
  exactWork (Exact.charge (16*(subject.suppliers.length+1)))
  match selected : subject.suppliers.filter (·.1 == index) with
  | [(j,origin)] =>
    if same : j = index then
      let sup : SourceDutySlots.Supplier subject index := ⟨origin,by simpa only [same] using selected⟩
      let env := origin.state.prepared.original.envelope
      exactWork (Exact.charge (16*(env.source.utf8ByteSize+origin.tokens.length+SourceTrace.Meter.tokenFields origin.tokens+1)))
      if bytes : LocatedFacts.checkOrdered env.source.toUTF8 env.occurrence.openBrace.span.endByte origin.tokens = true then
        if inside : origin.tokens.all (fun token => token.span.endByte ≤ env.occurrence.closeBrace.span.startByte) = true then
          let parsed ← NaturalAffine.witness (readQuery origin.tokens)
          match q : parsed.val with
          | none => return .error .sourceSyntax
          | some query =>
            let candidate ← NaturalAffine.witness
              (CallName.readWithModules sources (some catalogue.modulesContext) origin.state.owner origin.scope query.callee)
            match resolved : CallName.candidateResolution candidate.val with
            | none => return .error .resolution
            | some resolution =>
              have held : Computed (readQuery origin.tokens) parsed.val := by with_reducible exact parsed.property
              return .ok ⟨sup,LocatedFacts.checkOrdered_sound _ _ _ bytes,inside,query,q ▸ held,catalogue.modulesContext,candidate.val,
                by with_reducible exact candidate.property,resolution,resolved⟩
        else return .error .sourceBytes
      else return .error .sourceBytes
    else return .error .originRows
  | _ => return .error .originRows

structure Native {artifact catalogue context description graph implementations references prepared root requested checked}
    (cursor : @Cursor artifact catalogue context description graph implementations references prepared root requested checked) where
  provider : RuntimePreparedOperation.Provider artifact graph cursor.binding.record.occurrence.index
  original : cursor.binding.record.occurrence.provider = some provider
  actual : RuntimeProviderAction.Checked provider.header root cursor.binding.record.demand
  read : Computed (RuntimeProviderAction.read provider.header root cursor.binding.record.demand) actual
  retained : cursor.binding.record.checked.provider = .present provider original actual read

def nativeAt {artifact catalogue context description graph implementations references prepared root requested checked}
    (cursor : @Cursor artifact catalogue context description graph implementations references prepared root requested checked) :
    WorkM (Native cursor) := do
  match retained : cursor.binding.record.checked.provider with
  | .absent _ => throw .request
  | .present p original value computed => return ⟨p,original,value,computed,retained⟩

def covers (actual required : OperationPaths.Paths) : Bool :=
  (!required.applicable || actual.applicable) && (!required.adjointable || actual.adjointable) &&
    (!required.controllable || actual.controllable)

structure Identity {artifact catalogue context description graph implementations references prepared root requested checked cursor
    subject index} (site : @Site artifact.sources subject index)
    (slot : @Native artifact catalogue context description graph implementations references prepared root requested checked cursor)
    (owner name : String) : Prop where
  moduleName : site.resolution.moduleName = owner ∧ slot.provider.header.original.supplied.provider.moduleName = owner
  declarationName : site.resolution.declaration.name = name ∧ slot.provider.header.original.supplied.provider.declarationName = name
  source : site.resolution.source = slot.provider.header.original.supplied.provider.signature.original.source
  declaration : site.resolution.declaration = slot.provider.header.original.supplied.provider.signature.original.declaration
  body : site.resolution.source = slot.provider.header.original.body.checked.signature.original.source ∧
    site.resolution.declaration = slot.provider.header.original.body.checked.signature.original.declaration
  context : slot.provider.header.original.supplied.context = .source site.supplier.origin.state.owner

def readIdentity {artifact catalogue context description graph implementations references prepared root requested checked cursor
    subject index} (site : @Site artifact.sources subject index)
    (slot : @Native artifact catalogue context description graph implementations references prepared root requested checked cursor)
    (owner name : String) : WorkM (Except Pending (PLift (Identity site slot owner name))) := do
  let original := slot.provider.header.original
  let provider := original.supplied.provider
  let decl := provider.signature.original
  let r := site.resolution
  exactWork (Exact.charge (16*(r.source.utf8ByteSize+decl.source.utf8ByteSize+owner.utf8ByteSize+name.utf8ByteSize+
    provider.moduleName.utf8ByteSize+provider.declarationName.utf8ByteSize+site.supplier.origin.state.owner.utf8ByteSize+1)))
  if target : r.moduleName = owner ∧ provider.moduleName = owner ∧ r.declaration.name = name ∧
      provider.declarationName = name ∧ r.source = decl.source ∧ r.declaration = decl.declaration then
    if context : original.supplied.context = .source site.supplier.origin.state.owner then
      have bodySource := congrArg (fun sig => sig.original.source) original.body.originalSignature
      have bodyDecl := congrArg (fun sig => sig.original.declaration) original.body.originalSignature
      return .ok ⟨⟨⟨target.1,target.2.1⟩,⟨target.2.2.1,target.2.2.2.1⟩,target.2.2.2.2.1,target.2.2.2.2.2,
        ⟨target.2.2.2.2.1.trans (bodySource.trans original.runtime.source).symm,
         target.2.2.2.2.2.trans (bodyDecl.trans original.runtime.declaration).symm⟩,context⟩⟩
    else return .error .context
  else return .error .target

private def directEvent {sources caller} : SourceRuntimeContext.Event sources caller → Bool
  | .phase _ | .primitive _ => true
  | _ => false

def BareHeader {artifact catalogue context description graph implementations references prepared root requested checked cursor}
    (slot : @Native artifact catalogue context description graph implementations references prepared root requested checked cursor) : Bool :=
  let original := slot.provider.header.original
  let header := original.runtime.signature.checked.environment.numeric.original.header
  let args := original.supplied.provider.signature.staticArguments
  header.formals.isEmpty && header.premises.isEmpty && header.access.isEmpty &&
    args.bases.isEmpty && args.naturals.isEmpty && args.operations.isEmpty

structure Bare {artifact catalogue context description graph implementations references prepared root requested checked cursor
    subject index} (site : @Site artifact.sources subject index)
    (slot : @Native artifact catalogue context description graph implementations references prepared root requested checked cursor)
    (owner name : String) (required : OperationPaths.Paths) where
  identity : Identity site slot owner name
  spelling : site.query.bare = true
  header : BareHeader slot = true
  noMeanings : cursor.binding.record.occurrence.result.requirements.isEmpty = true
  directBody : slot.provider.header.original.body.checked.events.all directEvent = true
  originalNode : subject.description.nodes[index]? = some (.provider owner name [] [] [] [])
  nativeNode : cursor.node = .provider owner name [] [] []
  inference : GenericCatalogue.Entry catalogue.toRuntimeChecked slot.provider.header.original.supplied.provider.signature.original
  inferred : Computed (GenericCatalogue.lookup catalogue.toRuntimeChecked slot.provider.header.original.supplied.provider.signature.original) inference
  input : slot.provider.header.original.supplied.provider.signature.inputs = [cursor.value.input]
  output : slot.provider.header.original.supplied.provider.signature.outputs = [cursor.value.output]
  visible : slot.provider.header.original.supplied.provider.expectedEffect = SourceEffect.visible site.supplier.origin.state.owner owner
    site.resolution.declaration.isPublic slot.provider.header.original.supplied.provider.signature.original.parsedHeader.effect
    inference.inferred.inferredEffect
  effect : cursor.binding.record.occurrence.result.effect = slot.provider.header.original.supplied.provider.expectedEffect
  requestedPaths : covers cursor.binding.record.demand required = true
  availablePaths : covers cursor.binding.record.occurrence.result.paths cursor.binding.record.demand = true
  action : cursor.value.action = slot.actual.action

def readBare {artifact catalogue context description graph implementations references prepared root requested checked cursor
    subject index} (site : @Site artifact.sources subject index)
    (slot : @Native artifact catalogue context description graph implementations references prepared root requested checked cursor)
    (owner name : String) (required : OperationPaths.Paths) (identity : Identity site slot owner name) :
    WorkM (Except Pending (Bare site slot owner name required)) := do
  let native := slot.provider.header.original
  let core := native.supplied.provider.signature
  let metadata := cursor.binding.record.occurrence.result
  exactWork (Exact.charge (16*(subject.description.nodes.length+site.supplier.origin.tokens.length+
    native.body.checked.events.length+GenericOperation.Meter.payload subject.description+
    RuntimeStructuredRoot.argumentFields {operations := [("",⟨[cursor.node],0⟩)]}+
    Raw.OwnerFlow.fields (((core.inputs ++ core.outputs ++ [cursor.value.input,cursor.value.output]).zipIdx).map
      fun (v,i) => ⟨i,v⟩)+1)))
  if spelling : site.query.bare = true then
    if header : BareHeader slot = true then
      if noMeanings : metadata.requirements.isEmpty = true then
        if direct : native.body.checked.events.all directEvent = true then
          if original : subject.description.nodes[index]? = some (.provider owner name [] [] [] []) then
            if tree : cursor.node = .provider owner name [] [] [] then
              let inference ← NaturalAffine.witness (GenericCatalogue.lookup catalogue.toRuntimeChecked core.original)
              if ports : core.inputs = [cursor.value.input] ∧ core.outputs = [cursor.value.output] then
                if effect : native.supplied.provider.expectedEffect = SourceEffect.visible site.supplier.origin.state.owner owner
                    site.resolution.declaration.isPublic core.original.parsedHeader.effect inference.val.inferred.inferredEffect ∧
                    metadata.effect = native.supplied.provider.expectedEffect then
                  if paths : covers cursor.binding.record.demand required = true ∧ covers metadata.paths cursor.binding.record.demand = true then
                    exactWork (Exact.charge (cursor.value.action.entries.length+slot.actual.action.entries.length+1))
                    if action : cursor.value.action = slot.actual.action then
                      return .ok ⟨identity,spelling,header,noMeanings,direct,original,tree,inference.val,
                        by with_reducible exact inference.property,ports.1,ports.2,effect.1,effect.2,paths.1,paths.2,action⟩
                    else throw .equation
                  else return .error .paths
                else return .error .effects
              else return .error .ports
            else return .error .arguments
          else return .error .premises
        else return .error .body
      else return .error .meaning
    else return .error .premises
  else return .error .arguments

end QleisliKernel.Qirf.RuntimeClosedProvider
