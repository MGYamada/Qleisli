import QleisliKernel.SourceTypes.SourceRuntimeContext

/-! Complete typed mixed-runtime traversal for the shared source syntax.
Ordinary copying, explicit owner discharge and allocation remain visible across
calls and qmatch surroundings. Every body is inferred before checking its effect
assertion. Source metadata alone grants neither arm equations nor execution.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.SourceRuntimeTrace
open QleisliKernel QleisliKernel.SourceTypes
open SourceRuntimeValues SourceRuntimeContext

private def adapt {α : Type} (action : Except String α) : Finite.WorkM α :=
  Finite.lift (action.mapError fun _ => .request)

private def environmentCells (environment : Environment) : Nat :=
  (environment.map fun cell => cell.name.utf8ByteSize+valueFields cell.value+2).sum

private def outcome {sources caller} (before : Environment) (value : Value) (remaining : Environment)
    (allocated consumed : List Semantics.SourceOwners.Owner) (nextOrdinal : Nat)
    (events : List (Event sources caller)) (rows : List (String × String) := []) :
    Finite.WorkM (Outcome sources caller before) := do
  let staticRows ← SourceTrace.retainStaticRows (rows ++ events.flatMap Event.staticRows)
  Finite.exactWork (Exact.charge (16*(environmentCells before+environmentCells remaining+valueFields value+
    events.length+1)+
    SourceTrace.Meter.permutationWork (owners before ++ allocated)
      (valueOwners value ++ owners remaining ++ consumed)))
  Finite.guard (value.length ≤ 3*128 && remaining.length ≤ 128) .limit
  if balanced : (owners before ++ allocated).Perm
      (valueOwners value ++ owners remaining ++ consumed) then
    return ⟨value,remaining,allocated,consumed,nextOrdinal,events,balanced,staticRows⟩
  else throw .request

private def boundNames (pattern : List LocatedToken) : Except String (List String) := do
  let term ← QuantumMoves.parse 65 (pattern.map (·.text))
  return term.filterMap fun atom => match atom with | .name name => some name | _ => none

private def move (tokens : List LocatedToken) (environment : Environment) :
    Except String (Value × Environment) := do
  let [token] := tokens | throw "runtime name expression shape"
  SourceRuntimeValues.take token.text environment

private def primitiveAction (kind : CallName.Primitive) (site : Site) (arguments : List Value)
    (nextOrdinal : Nat) : Except String
      (Value × List Semantics.SourceOwners.Owner × List Semantics.SourceOwners.Owner × Nat) := do
  match kind,arguments with
  | .h,[[.owner owner]] =>
    if owner.basis != [.bit] then throw "H runtime source type"
    return ([.owner owner],[],[],nextOrdinal)
  | .globalPhaseEighth,[[.owner owner]] => return ([.owner owner],[],[],nextOrdinal)
  | .measureZ,[[.owner owner]] =>
    if owner.basis != [.bit] then throw "measure_z runtime source type"
    return ([.ordinary [.bit] (.measured site [] owner)],[],[owner],nextOrdinal)
  | .discard,[[.owner owner]] => return ([.ordinary [.unit] .unit],[],[owner],nextOrdinal)
  | .unit,[[.ordinary basis _]] =>
    if basis != [.unit] then throw "unit requires ordinary Unit"
    let owner : Semantics.SourceOwners.Owner := ⟨nextOrdinal,[.unit]⟩
    return ([.owner owner],[owner],[],nextOrdinal+1)
  | .finish,[[.owner owner]] =>
    if owner.basis != [.unit] then throw "finish requires the exact Unit owner type"
    return ([.ordinary [.unit] .unit],[],[owner],nextOrdinal)
  | .join,[[.owner first],[.owner second]] =>
    if first.ordinal == second.ordinal then throw "join aliases owners"
    let owner : Semantics.SourceOwners.Owner := ⟨nextOrdinal,.pair :: first.basis ++ second.basis⟩
    return ([.owner owner],[owner],[first,second],nextOrdinal+1)
  | .split,[[.owner owner]] =>
    let (first,second) ← pairBases owner.basis
    let left : Semantics.SourceOwners.Owner := ⟨nextOrdinal,first⟩
    let right : Semantics.SourceOwners.Owner := ⟨nextOrdinal+1,second⟩
    return ([.tuple 2,.owner left,.owner right],[left,right],[owner],nextOrdinal+2)
  | _,_ => throw "runtime primitive argument or static-application shape"

/-- Every child is evaluated once in source argument order. A callee starts
with its own full original body fuel; this evaluator's fuel bounds only its
current original AST. -/
def evalWithReader {sources owner name} (signature : Signature sources owner name)
    (readCallee : {callee calleeName : String} → (target : Signature sources callee calleeName) →
      Finite.WorkM (Summary target)) : Nat → PhaseApplication.Naturals sources →
    List Semantics.SourceOwners.Owner → List String → Nat → (environment : Environment) →
    {tokens : List LocatedToken} → SourceSyntax.Tree tokens → SourceContext.Context sources owner →
    Finite.WorkM (Outcome sources owner environment × SourceContext.Context sources owner) :=
  Nat.rec (fun _ _ _ _ _ _ _ _ => throw .limit)
    (fun _ recurse naturals held scope nextOrdinal environment tokens tree context => do
      let evaluateChildren (children : List (Sigma SourceSyntax.Tree))
          (startContext : SourceContext.Context sources owner) := children.foldlM
        (fun (values,current,allocated,consumed,ordinal,events,context) child => do
          let holding := held ++ values.flatMap valueOwners
          let (result,context) ← recurse naturals holding scope ordinal current child.2 context
          return (values ++ [result.value],result.remaining,allocated ++ result.allocated,
            consumed ++ result.consumed,result.nextOrdinal,events ++ result.events,context))
        (([] : List Value),environment,[],[],nextOrdinal,([] : List (Event sources owner)),startContext)
      match tree with
      | .empty .. =>
        return (← outcome environment [.ordinary [.unit] .unit] environment [] [] nextOrdinal [],context)
      | .literal _ bit _ =>
        return (← outcome environment [.ordinary [.bit] (.bit bit)] environment [] [] nextOrdinal [],context)
      | .move tokens _ _ =>
        Finite.exactWork (Exact.charge (SourceTrace.Meter.moveWork tokens []+16*environmentCells environment))
        let (value,remaining) ← adapt (move tokens environment)
        return (← outcome environment value remaining [] [] nextOrdinal [],context)
      | .binding statement expression rest =>
        let (first,context) ← recurse naturals held scope nextOrdinal environment expression context
        let pattern := statement.statement.pattern
        Finite.exactWork (Exact.charge (SourceTrace.Meter.syntaxWork pattern+
          16*(environmentCells first.remaining+first.value.length+1)*(pattern.length+1)))
        let names ← adapt (boundNames pattern)
        Finite.guard (names.all fun name => !naturals.staticNames.contains name) .request
        let after ← adapt (SourceRuntimeValues.bind (pattern.map (·.text)) first.value first.remaining)
        let (last,context) ← recurse naturals held (names ++ scope) first.nextOrdinal after rest context
        return (← outcome environment last.value last.remaining (first.allocated ++ last.allocated)
          (first.consumed ++ last.consumed) last.nextOrdinal (first.events ++ last.events)
          (first.staticRows ++ last.staticRows),context)
      | .sequence _ expression rest =>
        let (first,context) ← recurse naturals held scope nextOrdinal environment expression context
        Finite.guard (valueOwners first.value == []) .request
        let (last,context) ← recurse naturals held scope first.nextOrdinal first.remaining rest context
        return (← outcome environment last.value last.remaining (first.allocated ++ last.allocated)
          (first.consumed ++ last.consumed) last.nextOrdinal (first.events ++ last.events)
          (first.staticRows ++ last.staticRows),context)
      | .staticBindings leading _ rest =>
        let (naturals,scope) ← PhaseApplication.extend sources owner leading naturals scope
        let (result,context) ← recurse naturals held scope nextOrdinal environment rest context
        let staticRows ← SourceTrace.retainStaticRows (naturals.sourceRows ++ result.staticRows)
        return ({result with staticRows := staticRows},context)
      | .group group children =>
        let (values,remaining,allocated,consumed,ordinal,events,context) ← evaluateChildren children.trees context
        let value := if values.isEmpty then [.ordinary [.unit] .unit]
          else if values.length == 1 && (group.group.arguments.head?.bind (·.followingComma)).isNone then
            values.flatten else .tuple values.length :: values.flatten
        return (← outcome environment value remaining allocated consumed ordinal events,context)
      | .boolean written children =>
        let (values,remaining,allocated,consumed,ordinal,events,context) ← evaluateChildren children.trees context
        Finite.exactWork (Exact.charge (16*(values.map valueFields).sum+16))
        let expressions ← adapt (values.mapM fun value => do
          let [.ordinary basis expression] := value | throw "ordinary Boolean operand"
          if basis != [.bit] then throw "ordinary Boolean operand type"
          return expression)
        let expression ← adapt (match written.operator,expressions with
          | .not,[value] => pure (.not value)
          | .xor,[first,second] => pure (.xor first second)
          | .and,[first,second] => pure (.and first second)
          | _,_ => throw "ordinary Boolean arity")
        return (← outcome environment [.ordinary [.bit] expression] remaining allocated consumed ordinal events,context)
      | .selection tokens parsed original =>
        let selector ← adapt (SourceSyntax.read (parsed.selector.length+1) 0 false parsed.selector)
        let target ← adapt (SourceSyntax.read (parsed.target.length+1) 0 false parsed.target)
        let (first,context) ← recurse naturals held scope nextOrdinal environment selector context
        let [.owner selector] := first.value | throw .request
        let (last,context) ← recurse naturals (held ++ [selector]) scope first.nextOrdinal first.remaining target context
        let [.owner target] := last.value | throw .request
        Finite.guard (selector.ordinal != target.ordinal &&
          QuantumSequence.armsAllowed scope signature.operationNames parsed.arms) .request
        return (← outcome environment [.tuple 2,.owner selector,.owner target] last.remaining
          (first.allocated ++ last.allocated) (first.consumed ++ last.consumed) last.nextOrdinal
          (first.events ++ last.events ++ [.selection tokens parsed original selector target scope naturals
            held last.remaining]),context)
      | .selectionExpression tokens parsed original selectorTree targetTree =>
        let (first,context) ← recurse naturals held scope nextOrdinal environment selectorTree context
        let [.owner selector] := first.value | throw .request
        let (last,context) ← recurse naturals (held ++ [selector]) scope first.nextOrdinal first.remaining targetTree context
        let [.owner target] := last.value | throw .request
        Finite.guard (selector.ordinal != target.ordinal &&
          QuantumSequence.armsAllowed scope signature.operationNames parsed.arms) .request
        return (← outcome environment [.tuple 2,.owner selector,.owner target] last.remaining
          (first.allocated ++ last.allocated) (first.consumed ++ last.consumed) last.nextOrdinal
          (first.events ++ last.events ++ [.selection tokens parsed original selector target scope naturals
            held last.remaining]),context)
      | .call call children =>
        if SourceOperationApplication.selected signature.operationNames call.call.callee then
          let (values,remaining,allocated,consumed,ordinal,events,context) ← evaluateChildren children.trees context
          let targetBasis ← adapt (SourceOperationApplication.targetBasis call.call.callee values)
          let application ← SourceOperation.readWithInstantiation signature.instantiation naturals.helpers.val
            naturals.environment scope call.call.callee naturals.generic (some targetBasis)
          if applicable : application.graph.root.paths.applicable = true then
            Finite.exactWork (Exact.charge (16*((values.map valueFields).sum+
              Raw.OwnerFlow.fields [⟨0,application.graph.root.input⟩,⟨0,application.graph.root.output⟩]+1)))
            match applied : SourceOperationApplication.apply application.graph.root.input application.graph.root.output
                (SourceOperationApplication.controlled call.call.callee) values ordinal with
            | .error _ => throw .request
            | .ok (value,new,used,after) =>
              let event : SourceOperationApplication.Event sources owner :=
                ⟨tokens,call,name,signature.original,signature.instantiation,naturals,scope,application,applicable,
                  values,ordinal,value,new,used,after,applied,held,owners remaining⟩
              return (← outcome environment value remaining (allocated ++ new) (consumed ++ used) after
                (events ++ [.operation event]),context)
          else throw .request
        let written ← adapt (StaticApplication.readSyntax call.call.callee)
        let lookup ← SourceContext.read sources owner context scope written.callee
        let candidate ← Finite.lift lookup.answer.checked
        let (values,remaining,allocated,consumed,ordinal,events,context) ← evaluateChildren children.trees lookup.context
        match selected : primitive candidate with
        | some .phase =>
          let application ← PhaseApplication.read sources owner naturals scope call
          let [[.owner operand]] := values | throw .request
          if bit : operand.basis = [.bit] then
            let phase : PhaseEvent sources owner :=
              ⟨tokens,call,scope,naturals,application,operand,bit,held,remaining⟩
            return (← outcome environment [.owner operand] remaining allocated consumed ordinal
              (events ++ [.phase phase]),context)
          else throw .request
        | some kind =>
          Finite.guard written.arguments.isEmpty .request
          let (value,new,used,after) ← adapt (primitiveAction kind ⟨owner,name,call.calleeOffset⟩ values ordinal)
          let event : PrimitiveEvent sources owner :=
            ⟨tokens,call,scope,written,candidate,kind,selected,values,value,new,used,after,held,remaining⟩
          return (← outcome environment value remaining (allocated ++ new) (consumed ++ used) after
            (events ++ [.primitive event]),context)
        | none =>
          let target ← readTarget signature naturals written candidate
          if matched : values.map typeOf = target.signature.parameters.map (·.tree) then
            let canonical ← readCallee target.signature
            let inputOwners := values.flatMap valueOwners
            let fresh := canonical.allocated.zipIdx.map fun (owner,index) =>
              (⟨ordinal+index,owner.basis⟩ : Semantics.SourceOwners.Owner)
            let mapping := inputOwners ++ fresh
            Finite.exactWork (Exact.charge (32*(canonical.value.length+1)*
              ((values.map valueFields).sum+valueFields canonical.value+1)))
            match transported : transport ⟨owner,target.callerName,call.calleeOffset⟩ mapping
                (values.flatMap ordinary) canonical.value with
            | .error _ => throw .request
            | .ok value =>
              match consumedRead : canonical.consumed.mapM (mappedOwner mapping) with
              | .error _ => throw .request
              | .ok used =>
                let event : NamedEvent sources owner :=
                  ⟨tokens,call,scope,target,canonical,values,matched,inputOwners,rfl,fresh,mapping,rfl,
                    value,transported,used,consumedRead,held,remaining⟩
                return (← outcome environment value remaining (allocated ++ fresh) (consumed ++ used)
                  (ordinal+fresh.length) (events ++ [.named event]),context)
          else throw .request)

def quantumUse {sources owner name} (signature : Signature sources owner name)
    (events : List (Event sources owner)) : Bool :=
  signature.parameters.any (fun part => !((Semantics.RuntimeType.ownerBases part.tree).getD []).isEmpty) ||
    !((Semantics.RuntimeType.ownerBases signature.result.tree).getD []).isEmpty ||
    events.any Event.quantumUse

/-- Recursion uses the complete source table independently of expression fuel.
Cycles refuse by exact original declaration identity before fuel exhaustion. -/
def readNested (sources : Sources) (fuel : Nat) (active : List (String × String))
    {owner name : String} (signature : Signature sources owner name) : Finite.WorkM (Evaluated signature) :=
  match fuel with
  | 0 => throw .limit
  | fuel+1 => do
    Finite.exactWork (Exact.charge (8*(SourceTrace.Meter.nameFields
      (active.flatMap fun (owner,name) => [owner,name])+owner.utf8ByteSize+name.utf8ByteSize+1)))
    Finite.guard (!(active.contains (owner,name))) .request
    let tokens := signature.original.occurrence.body
    Finite.exactWork (Exact.charge (SourceTrace.Meter.syntaxWork tokens+
      SourceTrace.Meter.syntaxWork signature.original.occurrence.header+
      64*((signature.parameters.map fun part => part.tree.length).sum+1)))
    match parameters : QuantumOperands.parameterPatterns signature.original with
    | .error _ => throw .request
    | .ok patterns =>
      match valuesRead : seedValues signature.parameters with
      | .error _ => throw .request
      | .ok (parameterValues,nextOwner,nextOrdinary) =>
        match seeded : seed patterns parameterValues with
        | .error _ => throw .request
        | .ok initial =>
          Finite.guard (initial.all fun cell => !signature.staticNames.contains cell.name) .request
          match parsed : SourceSyntax.read (tokens.length+1) 0 true tokens with
          | .error _ => throw .request
          | .ok tree =>
            let naturals ← signature.naturals
            let (result,_) ← evalWithReader signature
              (fun callee => do return (← readNested sources fuel ((owner,name) :: active) callee).summary)
              (tokens.length+1) naturals [] (signature.staticNames ++ initial.map (·.name))
              nextOwner initial tree {}
            Finite.exactWork (Exact.charge (32*(result.events.length+1)^2+
              32*(result.allocated.length+1)+SourceTrace.Meter.tokenFields tokens+
              SourceTrace.Meter.permutationWork (owners initial ++ result.allocated)
                (valueOwners result.value ++ result.consumed)+
              16*(SourceTrace.Meter.tokenFields tokens+valueFields result.value+
                (signature.result.tree.map fun atom => match atom with
                  | .quantum => 1
                  | .finite finite => Raw.OwnerFlow.fields [⟨0,[finite]⟩]).sum+1)))
            if complete : owners result.remaining = [] then
              if balanced : (owners initial ++ result.allocated).Perm (valueOwners result.value ++ result.consumed) then
                if typed : typeOf result.value = signature.result.tree then
                  if issued : result.allocated.map (·.ordinal) =
                      (List.range result.allocated.length).map (nextOwner+·) then
                    if ordinalCount : result.nextOrdinal = nextOwner+result.allocated.length then
                      Finite.guard (result.events.filterMap Event.qmatchOffset == QuantumSequence.originalOffsets tokens) .request
                      Finite.guard (decide ((QuantumSequence.originalOffsets tokens).Nodup)) .request
                      Finite.guard ((result.events.filterMap Event.qmatchOffset).length ≤ 128) .limit
                      let calls ← adapt tree.calls
                      Finite.guard (result.events.filterMap Event.callOffset == calls) .request
                      Finite.guard (decide calls.Nodup) .request
                      if asserted : SourceEffect.permits signature.original.parsedHeader.effect
                          (inferredEffect result.events) = true then
                        Finite.guard (!signature.original.parsedHeader.ordinaryOnly ||
                          !quantumUse signature result.events) .request
                        if publicQuantum : signature.original.declaration.isPublic = true →
                            quantumUse signature result.events = true →
                            signature.original.parsedHeader.effect.isSome = true then
                          let summary : Summary signature :=
                            ⟨patterns,parameters,parameterValues,nextOwner,nextOrdinary,valuesRead,
                            initial,seeded,tree,parsed,result.value,result.remaining,result.allocated,
                            result.consumed,result.nextOrdinal,issued,ordinalCount,complete,balanced,typed,
                            inferredEffect result.events,asserted,quantumUse signature result.events,publicQuantum,
                            result.staticRows⟩
                          return ⟨summary,result.events,rfl⟩
                        else throw .request
                      else throw .request
                    else throw .request
                  else throw .request
                else throw .request
              else throw .request
            else throw .request
termination_by fuel

structure Checked (sources : Sources) (owner name : String) where
  signature : Signature sources owner name
  evaluated : Evaluated signature
  traversed : ∃ before after,
    (readNested sources (SourceTrace.sourceFuel sources) [] signature).run before = (.ok evaluated,after)

def Checked.summary {sources owner name} (checked : Checked sources owner name) : Summary checked.signature :=
  checked.evaluated.summary

def Checked.events {sources owner name} (checked : Checked sources owner name) : List (Event sources owner) :=
  checked.evaluated.events

def readWithSignature {sources owner name} (signature : Signature sources owner name) :
    Finite.WorkM (Checked sources owner name) := do
  let summary ← NaturalAffine.witness (readNested sources (SourceTrace.sourceFuel sources) [] signature)
  return ⟨signature,summary.val,by with_reducible exact summary.property⟩

def read (sources : Sources) (owner name : String) (arguments : StaticTypes.Arguments := {}) :
    Finite.WorkM (Checked sources owner name) := do
  readWithSignature (← readSignature sources owner name arguments)

/-- A native continuation must freshly recover each original callee, using this
same reader and its own nested source coordinates. No flattened event list or
caller-supplied history can stand in for that independent traversal. -/
def readNamedSource {sources caller} (event : NamedEvent sources caller) :
    Finite.WorkM (Checked sources event.target.resolution.moduleName event.target.resolution.declaration.name) := do
  let checked ← readWithSignature event.target.signature
  Finite.exactWork (Exact.charge (16*(valueFields checked.summary.value+
    valueFields event.canonical.value+checked.events.length+
    Raw.OwnerFlow.fields (checked.summary.allocated ++ checked.summary.consumed ++
      event.canonical.allocated ++ event.canonical.consumed)+1)))
  Finite.guard (checked.summary.value == event.canonical.value &&
    checked.summary.consumed == event.canonical.consumed &&
    checked.summary.allocated == event.canonical.allocated &&
    checked.summary.inferredEffect == event.canonical.inferredEffect &&
    checked.summary.quantumUse == event.canonical.quantumUse) .request
  return checked

theorem Checked.effectAssertion {sources owner name} (checked : Checked sources owner name) :
    SourceEffect.permits checked.signature.original.parsedHeader.effect checked.summary.inferredEffect = true :=
  checked.summary.asserted

theorem Checked.completeOwnerHistory {sources owner name} (checked : Checked sources owner name) :
    (owners checked.summary.initial ++ checked.summary.allocated).Perm
      (valueOwners checked.summary.value ++ checked.summary.consumed) := checked.summary.balanced

theorem Checked.unitaryNoObservation {sources owner name} (checked : Checked sources owner name)
    (annotation : checked.signature.original.parsedHeader.effect = some .unitary)
    (event : Event sources owner) (member : event ∈ checked.events) : event.effect ≠ .observe := by
  have pureEffect : checked.summary.inferredEffect = .unitary :=
    SourceEffect.unitary_permits _ (by simpa only [annotation] using checked.summary.asserted)
  have bound := SourceEffect.member_accumulate Event.effect checked.events .unitary event member
  change SourceEffect.rank event.effect ≤ SourceEffect.rank (inferredEffect checked.events) at bound
  have inferred : inferredEffect checked.events = checked.summary.inferredEffect := checked.evaluated.inferred
  rw [inferred,pureEffect] at bound
  intro observed
  simp [observed,SourceEffect.rank] at bound

end QleisliKernel.SourceTypes.SourceRuntimeTrace
