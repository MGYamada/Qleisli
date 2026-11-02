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
        (fun (values,current,allocated,consumed,ordinal,events,rows,context) child => do
          let holding := held ++ values.flatMap valueOwners
          let (result,context) ← recurse naturals holding scope ordinal current child.2 context
          return (values ++ [result.value],result.remaining,allocated ++ result.allocated,
            consumed ++ result.consumed,result.nextOrdinal,events ++ result.events,rows ++ result.staticRows,context))
        (([] : List Value),environment,[],[],nextOrdinal,([] : List (Event sources owner)),
          ([] : List (String × String)),startContext)
      match tree with
      | .empty .. =>
        return (← outcome environment [.ordinary [.unit] .unit] environment [] [] nextOrdinal [],context)
      | .literal _ bit _ =>
        return (← outcome environment [.ordinary [.bit] (.bit bit)] environment [] [] nextOrdinal [],context)
      | .staticConditional .. | .variant .. | .record .. | .projection .. | .matching .. => throw .request
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
        let after ← adapt (SourceRuntimeValues.bind (pattern.map (·.text)) first.value first.remaining
          (.letBinding statement.statement.keyword.span.startByte))
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
        let (values,remaining,allocated,consumed,ordinal,events,rows,context) ← evaluateChildren children.trees context
        let value := if values.isEmpty then [.ordinary [.unit] .unit]
          else if values.length == 1 && (group.group.arguments.head?.bind (·.followingComma)).isNone then
            values.flatten else .tuple values.length :: values.flatten
        return (← outcome environment value remaining allocated consumed ordinal events rows,context)
      | .boolean written children =>
        let (values,remaining,allocated,consumed,ordinal,events,rows,context) ← evaluateChildren children.trees context
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
        return (← outcome environment [.ordinary [.bit] expression] remaining allocated consumed ordinal events rows,context)
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
            held last.remaining]) (first.staticRows ++ last.staticRows),context)
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
            held last.remaining]) (first.staticRows ++ last.staticRows),context)
      | .basis written inputTree bodyTree =>
        let (inputResult,context) ← recurse naturals held scope nextOrdinal environment inputTree context
        let [.owner input] := inputResult.value | throw .request
        let (bound,_) ← adapt (SourceBasisFunction.boundValue input.basis)
        let ordinaryBefore := inputResult.remaining.filter (fun cell => (valueOwners cell.value).isEmpty)
        let names ← adapt (boundNames written.parts.pattern)
        Finite.guard (names.all fun name => !naturals.staticNames.contains name) .request
        match bodySeeded : SourceRuntimeValues.bind (written.parts.pattern.map (·.text)) bound ordinaryBefore
            (.basis written.parts.keyword.span.startByte) with
        | .error _ => throw .request
        | .ok bodyInitial =>
          let (body,context) ← recurse naturals (held ++ owners inputResult.remaining)
            (names ++ scope) inputResult.nextOrdinal bodyInitial bodyTree context
          if pureBody : inferredEffect body.events = .unitary then
            if classicalBody : body.events.any Event.quantumUse = false then
              Finite.guard (body.allocated.isEmpty && body.consumed.isEmpty && (valueOwners body.value).isEmpty) .request
              let some shape := Semantics.RuntimeType.shape (typeOf body.value) | throw .request
              let some outputBasis := shape.basis | throw .request
              let (parameters,_,_) ← adapt (seedValues signature.parameters)
              let inputTypes := (parameters.flatMap ordinary).map Prod.fst
              let function ← SourceBasisFunction.read input.basis outputBasis inputTypes body.value
              Finite.exactWork (Exact.charge (8*(valueFields function.bound+valueFields bound+1)))
              let sameBound : PLift (function.bound = bound) ←
                if same : function.bound = bound then pure (⟨same⟩ : PLift (function.bound = bound)) else throw .request
              let bodyCalls ← adapt bodyTree.calls
              Finite.guard (body.events.flatMap Event.callOffsets == bodyCalls) .request
              let output : Semantics.SourceOwners.Owner :=
                if input.basis == outputBasis then input else ⟨inputResult.nextOrdinal,outputBasis⟩
              let fresh := if input.basis == outputBasis then [] else [output]
              let used := if input.basis == outputBasis then [] else [input]
              let after := inputResult.nextOrdinal+fresh.length
              -- The bound value is reconstructed independently by the finite
              -- checker. Transport only its equality into the original pattern.
              have seeded : SourceRuntimeValues.bind (written.parts.pattern.map (·.text)) function.bound ordinaryBefore
                  (.basis written.parts.keyword.span.startByte) = .ok bodyInitial := by
                simpa only [sameBound.down] using bodySeeded
              let staticRows ← SourceTrace.retainStaticRows (naturals.sourceRows ++ body.staticRows)
              match originalCalls : bodyTree.calls with
              | .error _ => throw .request
              | .ok bodyCalls =>
                let event : BasisEvent sources owner :=
                  ⟨tokens,written,name,signature,naturals,scope,input,ordinaryBefore,bodyInitial,inputResult.nextOrdinal,bodyTree,body.value,
                    inputTypes,outputBasis,function,seeded,bodyCalls,originalCalls,inferredEffect body.events,
                    pureBody,body.events.any Event.quantumUse,classicalBody,output,held,inputResult.remaining,staticRows⟩
                return (← outcome environment [.owner output] inputResult.remaining
                  (inputResult.allocated ++ fresh) (inputResult.consumed ++ used) after
                  (inputResult.events ++ [.basis event]) (inputResult.staticRows ++ staticRows),context)
            else throw .request
          else throw .request
      | .conditional written conditionTree thenTree elseTree =>
        let (condition,context) ← recurse naturals held scope nextOrdinal environment conditionTree context
        let [.ordinary conditionType conditionValue] := condition.value | throw .request
        Finite.guard (conditionType == [.bit]) .request
        let (left,context) ← recurse naturals held scope condition.nextOrdinal condition.remaining thenTree context
        let (right,context) ← recurse naturals held scope left.nextOrdinal condition.remaining elseTree context
        let cells := condition.remaining.length+left.remaining.length+right.remaining.length+
          left.value.length+right.value.length
        Finite.exactWork (Exact.charge (32*(cells+1)*(environmentCells condition.remaining+
          environmentCells left.remaining+environmentCells right.remaining+valueFields left.value+
          valueFields right.value+1)))
        match thenOuter : SourceRuntimeBranches.outer condition.remaining left.remaining with
        | .error _ => throw .request
        | .ok remaining =>
          match elseOuter : SourceRuntimeBranches.outer condition.remaining right.remaining with
          | .error _ => throw .request
          | .ok other =>
            let same : PLift (other = remaining) ←
              if same : other = remaining then pure (⟨same⟩ : PLift (other = remaining)) else throw .request
            have elseOuter : SourceRuntimeBranches.outer condition.remaining right.remaining = .ok remaining := by
              simpa only [same.down] using elseOuter
            match merged : SourceRuntimeBranches.merge conditionValue left.value right.value right.nextOrdinal with
            | .error _ => throw .request
            | .ok (value,phis) =>
              match thenCalls : thenTree.calls with
              | .error _ => throw .request
              | .ok leftCalls =>
                match elseCalls : elseTree.calls with
                | .error _ => throw .request
                | .ok rightCalls =>
                  Finite.guard (left.events.flatMap Event.callOffsets == leftCalls &&
                    right.events.flatMap Event.callOffsets == rightCalls &&
                    left.events.flatMap Event.qmatchOffsets == QuantumSequence.originalOffsets written.parts.thenBody &&
                    right.events.flatMap Event.qmatchOffsets == QuantumSequence.originalOffsets written.parts.elseBody) .request
                  let leftArm : Arm sources owner condition.remaining written.parts.thenBody :=
                    ⟨thenTree,left.value,left.remaining,left.allocated,left.consumed,left.nextOrdinal,left.balanced,
                      inferredEffect left.events,left.events.any Event.quantumUse,left.staticRows,leftCalls,thenCalls⟩
                  let rightArm : Arm sources owner condition.remaining written.parts.elseBody :=
                    ⟨elseTree,right.value,right.remaining,right.allocated,right.consumed,right.nextOrdinal,right.balanced,
                      inferredEffect right.events,right.events.any Event.quantumUse,right.staticRows,rightCalls,elseCalls⟩
                  let event : BranchEvent sources owner :=
                    ⟨tokens,written,name,signature,naturals,scope,conditionValue,condition.remaining,condition.nextOrdinal,
                      leftArm,rightArm,remaining,thenOuter,elseOuter,value,phis,merged,held⟩
                  let introduced := left.allocated ++ right.allocated ++ phis.map (·.output)
                  let retired := SourceRuntimeBranches.retired condition.remaining remaining ++
                    left.allocated ++ right.allocated
                  return (← outcome environment value remaining (condition.allocated ++ introduced)
                    (condition.consumed ++ retired) (right.nextOrdinal+phis.length)
                    (condition.events ++ [.conditional event left.events right.events])
                    (condition.staticRows ++ left.staticRows ++ right.staticRows),context)
      | .call call children =>
        if let some written ← adapt (SourceRuntimeTransformSyntax.read call.call.callee) then
          let lookup ← SourceContext.read sources owner context scope written.base.2.callee
          let candidate ← Finite.lift lookup.answer.checked
          -- Classification uses the original resolved name. Primitive and
          -- opaque-formal applications retain their separate unary Op rule.
          if (QuantumSignature.candidateResolution candidate).isSome then
            let target ← readTarget signature naturals written.base.2 candidate
            let sameBase : PLift (target.written = written.base.2) ←
              if same : target.written = written.base.2 then
                pure (⟨same⟩ : PLift (target.written = written.base.2)) else throw .request
            let (values,remaining,allocated,consumed,ordinal,events,rows,context) ←
              evaluateChildren children.trees lookup.context
            -- The child is checked even when one of the original powers is
            -- zero. No selected-body effect is inferred from the prefix.
            let forward ← readCallee target.signature
            if visibleUnitary : SourceEffect.visible owner target.resolution.moduleName
                target.signature.original.declaration.isPublic target.signature.original.parsedHeader.effect
                forward.generic.inferredEffect = .unitary then
              let counts ← written.counts.mapM fun argument => do
                let checked ← SourceOperation.readCount signature.instantiation naturals.helpers.val
                  naturals.environment scope argument.tokens naturals.generic
                pure (⟨argument,checked⟩ : TransformCount signature naturals scope)
              if originalCounts : counts.map (·.argument) = written.counts then
                match multiplied : SourceRuntimeTransformPorts.product (counts.map (·.checked.value)) with
                | .error _ => throw .request
                | .ok copies =>
                  if access : (match written.access with
                      | .forward => true
                      | .adjoint => target.signature.operations.actuals.all (fun actual =>
                          actual.2.graph.root.paths.applicable && actual.2.graph.root.paths.adjointable)
                      | .controlled => target.signature.operations.actuals.all (fun actual =>
                          actual.2.graph.root.paths.applicable && actual.2.graph.root.paths.adjointable &&
                            actual.2.graph.root.paths.controllable)) = true then
                    let fields := (values.map valueFields).sum+
                      (target.signature.parameters.map fun part => SourceRuntimeTransformPorts.typeFields part.tree).sum+
                      SourceRuntimeTransformPorts.typeFields target.signature.result.tree
                    Finite.exactWork (Exact.charge (32*(fields+1)))
                    match portsRead : SourceRuntimeTransformPorts.read (target.signature.parameters.map (·.tree))
                        target.signature.result.tree written.access (!written.counts.isEmpty) with
                    | .error _ => throw .request
                    | .ok ports =>
                      match applied : SourceRuntimeTransformPorts.apply ports written.access values ordinal with
                      | .error _ => throw .request
                      | .ok (value,new,used,after) =>
                        let event : TransformEvent sources owner :=
                          ⟨tokens,call,name,signature,naturals,scope,written,target,sameBase.down,forward,
                            visibleUnitary,counts,originalCounts,copies,multiplied,access,ports,portsRead,
                            values,ordinal,value,new,used,after,applied,held,remaining⟩
                        return (← outcome environment value remaining (allocated ++ new) (consumed ++ used)
                          after (events ++ [.transform event]) rows,context)
                  else throw .request
              else throw .request
            else throw .request
        if SourceOperationApplication.selected signature.operationNames call.call.callee then
          let (values,remaining,allocated,consumed,ordinal,events,rows,context) ← evaluateChildren children.trees context
          let targetBasis ← adapt (SourceOperationApplication.targetBasis call.call.callee values)
          let application ← SourceOperation.readWithInstantiation signature.instantiation naturals.helpers.val
            naturals.environment scope call.call.callee naturals.generic (some targetBasis) (some signature.supply)
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
                (events ++ [.operation event]) rows,context)
          else throw .request
        let written ← adapt (StaticApplication.readSyntax call.call.callee)
        let lookup ← SourceContext.read sources owner context scope written.callee
        let candidate ← Finite.lift lookup.answer.checked
        let (values,remaining,allocated,consumed,ordinal,events,rows,context) ← evaluateChildren children.trees lookup.context
        match selected : primitive candidate with
        | some .phase =>
          let application ← PhaseApplication.read sources owner naturals scope call
          let [[.owner operand]] := values | throw .request
          if bit : operand.basis = [.bit] then
            let phase : PhaseEvent sources owner :=
              ⟨tokens,call,scope,naturals,application,operand,bit,held,remaining⟩
            return (← outcome environment [.owner operand] remaining allocated consumed ordinal
              (events ++ [.phase phase]) rows,context)
          else throw .request
        | some kind =>
          Finite.guard written.arguments.isEmpty .request
          let (value,new,used,after) ← adapt (primitiveAction kind ⟨owner,name,call.calleeOffset⟩ values ordinal)
          let event : PrimitiveEvent sources owner :=
            ⟨tokens,call,scope,written,candidate,kind,selected,values,value,new,used,after,held,remaining⟩
          return (← outcome environment value remaining (allocated ++ new) (consumed ++ used) after
            (events ++ [.primitive event]) rows,context)
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
                  (ordinal+fresh.length) (events ++ [.named event]) rows,context)
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
            let generic ← NaturalAffine.witness (GenericTypeTrace.readWithTree signature.instantiation tree)
            let originalAsserted : PLift (SourceEffect.permits signature.original.parsedHeader.effect generic.val.inferredEffect = true) ←
              if asserted : SourceEffect.permits signature.original.parsedHeader.effect generic.val.inferredEffect = true then
                pure (⟨asserted⟩ : PLift (SourceEffect.permits signature.original.parsedHeader.effect generic.val.inferredEffect = true))
              else throw .request
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
                      Finite.guard (result.events.flatMap Event.qmatchOffsets == QuantumSequence.originalOffsets tokens) .request
                      Finite.guard (decide ((QuantumSequence.originalOffsets tokens).Nodup)) .request
                      Finite.guard ((result.events.flatMap Event.qmatchOffsets).length ≤ 128) .limit
                      let calls ← adapt tree.calls
                      Finite.guard (result.events.flatMap Event.callOffsets == calls) .request
                      Finite.guard (decide calls.Nodup) .request
                      if asserted : SourceEffect.permits signature.original.parsedHeader.effect
                          (inferredEffect result.events) = true then
                        Finite.guard (!signature.original.parsedHeader.ordinaryOnly ||
                          !quantumUse signature result.events) .request
                        if publicQuantum : signature.original.declaration.isPublic = true →
                            quantumUse signature result.events = true →
                            signature.original.parsedHeader.effect.isSome = true then
                          let staticRows ← SourceTrace.retainStaticRows (generic.val.sourceRows ++ result.staticRows)
                          let summary : Summary signature :=
                            ⟨patterns,parameters,parameterValues,nextOwner,nextOrdinary,valuesRead,
                            initial,seeded,tree,parsed,generic.val,by with_reducible exact generic.property,
                            originalAsserted.down,result.value,result.remaining,result.allocated,
                            result.consumed,result.nextOrdinal,issued,ordinalCount,complete,balanced,typed,
                            inferredEffect result.events,asserted,quantumUse signature result.events,publicQuantum,
                            staticRows⟩
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

structure Body {sources owner name} (signature : Signature sources owner name) where
  checked : Checked sources owner name
  originalSignature : checked.signature = signature

/-- The continuation retains the exact already-checked original signature and
its instantiation/supply context. No equal-width replacement is selected. -/
def readBodyWithSignature {sources owner name} (signature : Signature sources owner name) :
    Finite.WorkM (Body signature) := do
  let summary ← NaturalAffine.witness (readNested sources (SourceTrace.sourceFuel sources) [] signature)
  let checked : Checked sources owner name :=
    ⟨signature,summary.val,by with_reducible exact summary.property⟩
  return ⟨checked,rfl⟩

def readWithSignature {sources owner name} (signature : Signature sources owner name) :
    Finite.WorkM (Checked sources owner name) := do
  return (← readBodyWithSignature signature).checked

def read (sources : Sources) (owner name : String) (arguments : StaticTypes.Arguments := {}) :
    Finite.WorkM (Checked sources owner name) := do
  readWithSignature (← readSignature sources owner name arguments)

/-- A native continuation must freshly recover each original callee, using this
same reader and its own nested source coordinates. No flattened event list or
caller-supplied history can stand in for that independent traversal. -/
def readNamedBody {sources caller} (event : NamedEvent sources caller) :
    Finite.WorkM (Body event.target.signature) := do
  let body ← readBodyWithSignature event.target.signature
  let checked := body.checked
  Finite.exactWork (Exact.charge (16*(valueFields checked.summary.value+
    valueFields event.canonical.value+checked.events.length+
    Raw.OwnerFlow.fields (checked.summary.allocated ++ checked.summary.consumed ++
      event.canonical.allocated ++ event.canonical.consumed)+1)))
  Finite.guard (checked.summary.value == event.canonical.value &&
    checked.summary.consumed == event.canonical.consumed &&
    checked.summary.allocated == event.canonical.allocated &&
    checked.summary.inferredEffect == event.canonical.inferredEffect &&
    checked.summary.generic.inferredEffect == event.canonical.generic.inferredEffect &&
    checked.summary.quantumUse == event.canonical.quantumUse) .request
  return body

def readNamedSource {sources caller} (event : NamedEvent sources caller) :
    Finite.WorkM (Checked sources event.target.resolution.moduleName event.target.resolution.declaration.name) := do
  return (← readNamedBody event).checked

/-- The complete original forward body remains mandatory for a direct group
transform, including under zero powers. The continuation must separately bind
its ordered ports and transformed operator to the actual emitted interval. -/
def readTransformBody {sources caller} (event : TransformEvent sources caller) :
    Finite.WorkM (Body event.target.signature) := do
  let body ← readBodyWithSignature event.target.signature
  let checked := body.checked
  Finite.exactWork (Exact.charge (16*(valueFields checked.summary.value+
    valueFields event.forward.value+checked.events.length+
    Raw.OwnerFlow.fields (checked.summary.allocated ++ checked.summary.consumed ++
      event.forward.allocated ++ event.forward.consumed)+1)))
  Finite.guard (checked.summary.value == event.forward.value &&
    checked.summary.consumed == event.forward.consumed &&
    checked.summary.allocated == event.forward.allocated &&
    checked.summary.inferredEffect == event.forward.inferredEffect &&
    checked.summary.generic.inferredEffect == event.forward.generic.inferredEffect &&
    checked.summary.quantumUse == event.forward.quantumUse) .request
  return body

def readTransformSource {sources caller} (event : TransformEvent sources caller) :
    Finite.WorkM (Checked sources event.target.resolution.moduleName event.target.resolution.declaration.name) := do
  return (← readTransformBody event).checked

/-- Coherent body calls are source/reference dependencies, not invented runtime
call intervals. A native basis continuation freshly recovers their original
ordinary evaluation and source rows through this same evaluator. -/
def readBasisSource {sources caller} (event : BasisEvent sources caller) :
    Finite.WorkM (Outcome sources caller event.bodyInitial) := do
  let names ← adapt (boundNames event.written.parts.pattern)
  let (body,_) ← evalWithReader event.signature
    (fun callee => do return (← readNested sources (SourceTrace.sourceFuel sources)
      [(caller,event.callerName)] callee).summary)
    (event.written.parts.body.length+1) event.naturals
    (event.held ++ owners event.remaining) (names ++ event.scope) event.bodyOrdinal
    event.bodyInitial event.bodyTree {}
  Finite.exactWork (Exact.charge (16*(valueFields body.value+valueFields event.bodyValue+body.events.length+1)))
  Finite.guard (body.value == event.bodyValue && inferredEffect body.events == .unitary &&
    !(body.events.any Event.quantumUse) && body.allocated.isEmpty && body.consumed.isEmpty) .request
  return body

structure BranchBodies {sources caller} (event : BranchEvent sources caller) where
  thenResult : Outcome sources caller event.before
  elseResult : Outcome sources caller event.before
  thenValue : thenResult.value = event.thenArm.value
  elseValue : elseResult.value = event.elseArm.value
  thenEffect : inferredEffect thenResult.events = event.thenArm.inferredEffect
  elseEffect : inferredEffect elseResult.events = event.elseArm.inferredEffect
  thenRemaining : thenResult.remaining = event.thenArm.remaining
  elseRemaining : elseResult.remaining = event.elseArm.remaining
  thenAllocated : thenResult.allocated = event.thenArm.allocated
  elseAllocated : elseResult.allocated = event.elseArm.allocated
  thenConsumed : thenResult.consumed = event.thenArm.consumed
  elseConsumed : elseResult.consumed = event.elseArm.consumed
  thenOrdinal : thenResult.nextOrdinal = event.thenArm.nextOrdinal
  elseOrdinal : elseResult.nextOrdinal = event.elseArm.nextOrdinal

/-- Both original branches are recovered under the same original environment.
The second branch uses a disjoint issued-identity interval; no condition value
selects or suppresses an original effect, type check or owner obligation. -/
def readBranchSource {sources caller} (event : BranchEvent sources caller) :
    Finite.WorkM (BranchBodies event) := do
  let readCallee := fun {owner name} (callee : Signature sources owner name) => do
    return (← readNested sources (SourceTrace.sourceFuel sources) [(caller,event.callerName)] callee).summary
  let (left,_) ← evalWithReader event.signature readCallee
    (event.written.parts.thenBody.length+1) event.naturals event.held event.scope event.nextOrdinal
    event.before event.thenArm.tree {}
  let (right,_) ← evalWithReader event.signature readCallee
    (event.written.parts.elseBody.length+1) event.naturals event.held event.scope left.nextOrdinal
    event.before event.elseArm.tree {}
  Finite.exactWork (Exact.charge (32*(valueFields left.value+valueFields right.value+
    valueFields event.thenArm.value+valueFields event.elseArm.value+left.events.length+right.events.length+
    environmentCells left.remaining+environmentCells right.remaining+
    environmentCells event.thenArm.remaining+environmentCells event.elseArm.remaining+
    Raw.OwnerFlow.fields (left.allocated ++ right.allocated ++ left.consumed ++ right.consumed ++
      event.thenArm.allocated ++ event.elseArm.allocated ++ event.thenArm.consumed ++ event.elseArm.consumed)+1)))
  if checked : left.value = event.thenArm.value ∧ right.value = event.elseArm.value ∧
      inferredEffect left.events = event.thenArm.inferredEffect ∧
      inferredEffect right.events = event.elseArm.inferredEffect ∧
      left.remaining = event.thenArm.remaining ∧ right.remaining = event.elseArm.remaining ∧
      left.allocated = event.thenArm.allocated ∧ right.allocated = event.elseArm.allocated ∧
      left.consumed = event.thenArm.consumed ∧ right.consumed = event.elseArm.consumed ∧
      left.nextOrdinal = event.thenArm.nextOrdinal ∧ right.nextOrdinal = event.elseArm.nextOrdinal then
    let ⟨thenValue,elseValue,thenEffect,elseEffect,thenRemaining,elseRemaining,thenAllocated,
      elseAllocated,thenConsumed,elseConsumed,thenOrdinal,elseOrdinal⟩ := checked
    return ⟨left,right,thenValue,elseValue,thenEffect,elseEffect,thenRemaining,elseRemaining,
      thenAllocated,elseAllocated,thenConsumed,elseConsumed,thenOrdinal,elseOrdinal⟩
  else throw .request

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
