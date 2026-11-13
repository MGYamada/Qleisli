import QleisliKernel.SourceTypes.SourceRuntimeContext
import QleisliKernel.SourceTypes.SourceRuntimeNominalValue
import QleisliKernel.SourceTypes.SourceRecursion
import QleisliKernel.SourceTypes.SourceCallStack

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

/-- Original syntax/type setup for one exact checked signature. This retains
only the successful original parser/type-reader evidence, never a closed body
outcome or native result. Instantiation, catalogue and supplier context are
fixed by the signature index and the actual readWithTree witness. -/
structure OriginalSetup {sources owner name} (signature : Signature sources owner name) where
  tree : SourceSyntax.Tree signature.original.occurrence.body
  parsed : SourceSyntax.read (signature.original.occurrence.body.length+1) 0 true
    signature.original.occurrence.body = .ok tree
  generic : RuntimeGenericAnalysis.Checked signature.original
  genericRead : ∃ before after,
    (RuntimeGenericAnalysis.read signature.instantiation tree signature.operations.catalogue).run before = (.ok generic,after)

private def readOriginalSetup {sources owner name} (signature : Signature sources owner name) :
    Finite.WorkM (OriginalSetup signature) := do
  let tokens := signature.original.occurrence.body
  match parsed : SourceSyntax.read (tokens.length+1) 0 true tokens with
  | .error _ => throw .request
  | .ok tree =>
    let generic ← NaturalAffine.witness (RuntimeGenericAnalysis.read signature.instantiation tree signature.operations.catalogue)
    return ⟨tree,parsed,generic.val,by with_reducible exact generic.property⟩

def originalSetup {sources owner name signature} (summary : @Summary sources owner name signature) :
    OriginalSetup signature :=
  ⟨summary.tree,summary.parsed,summary.generic,summary.genericRead⟩

private def callFrame {sources owner name} (signature : Signature sources owner name) : SourceCallStack.Frame :=
  ⟨owner,name,signature.arguments.naturals,!signature.original.parsedHeader.ordinaryOnly⟩

private def outcome {sources caller} (before : Environment) (value : Value) (remaining : Environment)
    (allocated consumed : List Semantics.SourceOwners.Owner) (nextOrdinal : Nat)
    (events : List (Event sources caller)) (rows : List (String × String) := []) :
    Finite.WorkM (Outcome sources caller before) := do
  -- Each evaluated child already retained every row of its events. Callers
  -- add only the rows contributed by their own new event or source operation.
  let staticRows ← SourceTrace.retainStaticRows rows
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
  let term ← QuantumMoves.parsePattern 65 (pattern.map (·.text))
  return term.filterMap fun atom => match atom with | .name name => some name | _ => none

private def move (tokens : List LocatedToken) (environment : Environment) :
    Except String (Value × Environment) := do
  let [token] := tokens | throw "runtime name expression shape"
  SourceRuntimeValues.take token.text environment

private def readComputedPredicate {sources owner name} (signature : Signature sources owner name)
    (naturals : PhaseApplication.Naturals sources) (scope : List String)
    (reference : SourceComputedSyntax.Reference) (basis : Semantics.FiniteCarrier.Basis)
    (readCallee : {callee calleeName : String} → (target : Signature sources callee calleeName) →
      Finite.WorkM (Summary target)) : Finite.WorkM (ComputedPredicate sources owner scope reference basis) := do
  let written ← adapt (StaticApplication.readSyntax reference.argument.tokens)
  let candidate ← CallName.read sources owner scope written.callee
  let target ← readTarget signature naturals written candidate
  if classical : target.signature.original.parsedHeader.ordinaryOnly = true then
    if input : target.signature.parameters.map (·.tree) = [Semantics.RuntimeType.ordinary basis] then
      if output : target.signature.result.tree = Semantics.RuntimeType.ordinary [.bit] then
        let canonical ← readCallee target.signature
        if pure : canonical.generic.quantumUse = false then
          Finite.guard (canonical.allocated.isEmpty && canonical.consumed.isEmpty) .request
          return ⟨target,canonical,classical,input,output,pure⟩
        else throw .request
      else throw .request
    else throw .request
  else throw .request

private def readComputedLogical {sources owner name} (signature : Signature sources owner name)
    (naturals : PhaseApplication.Naturals sources) (scope : List String) (basis : Semantics.FiniteCarrier.Basis) :
    (reference : Option SourceComputedSyntax.Reference) →
      Finite.WorkM (ComputedLogical signature naturals scope basis reference)
  | none => pure .protectedScope
  | some reference => do
    let operation ← SourceOperation.readWithInstantiation signature.instantiation naturals.helpers.val
      naturals.environment scope reference.argument.tokens naturals.generic (some basis) (some signature.supply)
    if applicable : operation.graph.root.paths.applicable = true then
      if input : operation.graph.root.input = basis then
        if output : operation.graph.root.output = basis then
          if unitary : operation.graph.root.effect = .unitary then
            return .certified operation applicable input output unitary
          else throw .request
        else throw .request
      else throw .request
    else throw .request

private def sourceModules {sources owner name} (signature : Signature sources owner name) :
    Option (SourceModules.Prepared sources) :=
  signature.operations.catalogue.map (·.modulesContext)

/-- Every child is evaluated once in source argument order. A callee starts
with its own full original body fuel; this evaluator's fuel bounds only its
current original AST. -/
def evalWithReader {sources owner name} (signature : Signature sources owner name)
    (generic : RuntimeGenericAnalysis.Checked signature.original)
    (basis : SourceBasisBindings.Checked signature.instantiation generic.basisObligations)
    (computed : SourceComputedBindings.Checked signature.instantiation generic.computedObligations)
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
      | .workspace written inputTree dirtyTrees bodyTree =>
        let (values,remaining,allocated,consumed,ordinal,events,rows,context) ←
          evaluateChildren (⟨written.parts.data.tokens,inputTree⟩ :: dirtyTrees.trees) context
        let (input,scratch,fresh) ← match values with
          | [[.owner input]] => pure (input,⟨ordinal,[.bit]⟩,true)
          | [[.owner input],[.owner scratch]] => pure (input,scratch,false)
          | _ => throw .request
        let dataName := written.parts.dataBinder.text
        let scratchName := written.parts.scratchBinder.text
        let offset := written.parts.header.calleeOffset
        Finite.guard (![dataName,scratchName].any signature.staticNames.contains) .request
        Finite.guard (input != scratch && !(held ++ owners remaining).contains scratch) .request
        let logical ← readComputedLogical signature naturals scope input.basis
          (some ⟨written.parts.logical,written.parts.logicalName⟩)
        if freshMode : fresh = !written.parts.dirty.isSome then
          if scratchType : scratch.basis = [.bit] then
            let seed : Except String Environment := do
              let data ← SourceRuntimeValues.bind [dataName] [.owner input] [] (.workspaceData offset)
              SourceRuntimeValues.bind [scratchName] [.owner scratch] data (.workspaceScratch offset)
            match seeded : seed with
            | .error _ => throw .request
            | .ok initial =>
              let (body,context) ← recurse naturals (held ++ owners remaining)
                (dataName :: scratchName :: scope) (if fresh then ordinal+1 else ordinal) initial bodyTree context
              match returned : body.value with
              | [.tuple 2,.owner dataOut,.owner scratchOut] =>
                if valid : inferredEffect body.events = .unitary ∧ owners body.remaining = [] ∧
                    dataOut.basis = input.basis ∧ scratchOut.basis = [.bit] then
                  match callsRead : bodyTree.calls with
                  | .error _ => throw .request
                  | .ok calls =>
                    Finite.guard (body.events.flatMap Event.callOffsets == calls &&
                      body.events.flatMap Event.qmatchOffsets == QuantumSequence.originalOffsets written.parts.body) .request
                    let arm : Arm sources owner initial written.parts.body :=
                      ⟨bodyTree,body.value,body.remaining,body.allocated,body.consumed,body.nextOrdinal,body.balanced,
                        inferredEffect body.events,body.events.any Event.quantumUse,body.staticRows,calls,callsRead,
                        body.events.flatMap Event.basisOffsets,body.events.flatMap Event.computedOffsets⟩
                    let event : WorkspaceEvent sources owner :=
                      ⟨tokens,written,name,signature,naturals,scope,input,scratch,fresh,ordinal,freshMode,scratchType,
                        logical,initial,seeded,arm,valid.1,valid.2.1,dataOut,scratchOut,
                        returned,valid.2.2.1,valid.2.2.2⟩
                    let value := if fresh then [.owner dataOut] else body.value
                    return (← outcome environment value remaining
                      (allocated ++ (if fresh then [scratch] else []) ++ body.allocated)
                      (consumed ++ body.consumed ++ (if fresh then [scratchOut] else [])) body.nextOrdinal
                      (events ++ [.workspace event body.events]) (rows ++ (Event.workspace event body.events).staticRows),context)
                else throw .request
              | _ => throw .request
          else throw .request
        else throw .request
      | .computed written inputTree bodyTree =>
        let (inputResult,context) ← recurse naturals held scope nextOrdinal environment inputTree context
        let [.owner input] := inputResult.value | throw .request
        let binding ← SourceBasisBindings.activeAt computed (SourceRuntimeComputed.offset written)
        if inputType : binding.ports.input = input.basis then
          let predicate ← readComputedPredicate signature naturals scope written.parts.predicate input.basis readCallee
          let logical ← readComputedLogical signature naturals scope input.basis written.parts.logical
          match prepared : SourceRuntimeComputed.prepare written input inputResult.remaining inputResult.nextOrdinal signature.staticNames with
          | .error _ => throw .request
          | .ok initial =>
            let (body,context) ← recurse naturals
              (held ++ owners inputResult.remaining ++ initial.heldData)
              (SourceRuntimeComputed.names written ++ scope) initial.nextOrdinal initial.environment bodyTree context
            if pure : inferredEffect body.events = .unitary then
              if complete : owners body.remaining = [] then
                match returnedRead : SourceRuntimeComputed.returned written input body.value with
                | .error _ => throw .request
                | .ok returned =>
                  match callsRead : bodyTree.calls with
                  | .error _ => throw .request
                  | .ok calls =>
                    Finite.guard (body.events.flatMap Event.callOffsets == calls &&
                      body.events.flatMap Event.qmatchOffsets == QuantumSequence.originalOffsets written.parts.body) .request
                    let arm : Arm sources owner initial.environment written.parts.body :=
                      ⟨bodyTree,body.value,body.remaining,body.allocated,body.consumed,body.nextOrdinal,body.balanced,
                        inferredEffect body.events,body.events.any Event.quantumUse,body.staticRows,calls,callsRead,
                        body.events.flatMap Event.basisOffsets,body.events.flatMap Event.computedOffsets⟩
                    let event : ComputedEvent sources owner :=
                      ⟨tokens,written,name,signature,generic,computed,binding,naturals,scope,input,inputType,
                        predicate,logical,inputResult.remaining,inputResult.nextOrdinal,initial,prepared,arm,pure,
                        complete,returned,returnedRead,held⟩
                    return (← outcome environment [.owner returned.data] inputResult.remaining
                      (inputResult.allocated ++ [initial.auxiliary] ++ body.allocated)
                      (inputResult.consumed ++ body.consumed ++ [returned.auxiliary]) body.nextOrdinal
                      (inputResult.events ++ [.computed event body.events])
                      (inputResult.staticRows ++ body.staticRows ++ (Event.computed event body.events).staticRows),context)
              else throw .request
            else throw .request
        else throw .request
      | .matching written scrutinee children =>
        let (selected,context) ← recurse naturals held scope nextOrdinal environment scrutinee context
        let [.ordinary basis condition] := selected.value | throw .request
        let labels ← SourceMatchLabels.read sources owner naturals.helpers.val scope written basis
        let (arms,armEvents,ordinal,context) ← children.trees.foldlM
          (fun (arms,events,ordinal,context) child => do
            let (result,context) ← recurse naturals held scope ordinal selected.remaining child.2 context
            match callsRead : child.2.calls with
            | .error _ => throw .request
            | .ok calls =>
              Finite.guard (result.events.flatMap Event.callOffsets == calls &&
                result.events.flatMap Event.qmatchOffsets == QuantumSequence.originalOffsets child.1) .request
              let arm : Arm sources owner selected.remaining child.1 :=
                ⟨child.2,result.value,result.remaining,result.allocated,result.consumed,result.nextOrdinal,
                  result.balanced,inferredEffect result.events,result.events.any Event.quantumUse,
                  result.staticRows,calls,callsRead,result.events.flatMap Event.basisOffsets,
                  result.events.flatMap Event.computedOffsets⟩
              return (arms ++ [⟨child.1,arm⟩],events ++ [result.events],result.nextOrdinal,context))
          (([] : List (Sigma (Arm sources owner selected.remaining))),
            ([] : List (List (Event sources owner))),selected.nextOrdinal,context)
        if originalBodies : arms.map (·.1) = written.parts.arms.map (·.body.tokens) then
          let some first := arms.head? | throw .request
          let remaining ← adapt (SourceRuntimeBranches.outer selected.remaining first.2.remaining)
          if projected : arms.all (fun arm =>
              SourceRuntimeBranches.exits selected.remaining arm.2.remaining remaining) = true then
            Finite.exactWork (Exact.charge (64*((arms.map fun arm => valueFields arm.2.value+
              environmentCells arm.2.remaining).sum+environmentCells remaining+1)))
            match merged : SourceRuntimeMatching.merge condition labels.labels.ordinals (arms.map (·.2.value)) ordinal with
            | .error _ => throw .request
            | .ok (value,phis) =>
              have exits : ∀ arm ∈ arms,SourceRuntimeBranches.outer selected.remaining arm.2.remaining = .ok remaining := by
                intro arm member
                exact SourceRuntimeBranches.exits_sound _ _ _ ((List.all_eq_true.mp projected) arm member)
              let event : MatchEvent sources owner :=
                ⟨tokens,written,name,signature,generic,naturals,scope,basis,condition,labels,
                  selected.remaining,selected.nextOrdinal,arms,originalBodies,remaining,exits,ordinal,value,phis,merged,held⟩
              let allocated := arms.flatMap (·.2.allocated)
              let consumed := SourceRuntimeBranches.retired selected.remaining remaining ++ allocated
              return (← outcome environment value remaining
                (selected.allocated ++ allocated ++ phis.map (·.output)) (selected.consumed ++ consumed)
                (ordinal+phis.length) (selected.events ++ [.matching event armEvents])
                (selected.staticRows ++ labels.labels.sourceRows ++ arms.flatMap (·.2.staticRows) ++ naturals.sourceRows),context)
          else throw .request
        else throw .request
      | .staticConditional written thenTree elseTree =>
        let selection ← SourceStaticSelection.read sources owner naturals scope written
        let selected : Sigma SourceSyntax.Tree := if selection.selected then
          ⟨written.parts.thenBody,thenTree⟩ else ⟨written.parts.elseBody,elseTree⟩
        have selectedTokens : selected.1 = if selection.selected then written.parts.thenBody else written.parts.elseBody := by
          dsimp only [selected]
          split <;> rfl
        let (result,context) ← recurse selection.naturals held scope nextOrdinal environment selected.2 context
        Finite.exactWork (Exact.charge (32*(environmentCells environment+environmentCells result.remaining+
          valueFields result.value+1)))
        match projected : SourceRuntimeBranches.outer environment result.remaining with
        | .error _ => throw .request
        | .ok remaining =>
          match thenCallsRead : thenTree.calls with
          | .error _ => throw .request
          | .ok thenCalls =>
            match elseCallsRead : elseTree.calls with
            | .error _ => throw .request
            | .ok elseCalls =>
              match callsRead : selected.2.calls with
              | .error _ => throw .request
              | .ok calls =>
                Finite.guard (result.events.flatMap Event.callOffsets == calls &&
                  result.events.flatMap Event.qmatchOffsets == QuantumSequence.originalOffsets selected.1) .request
                let arm : Arm sources owner environment selected.1 :=
                  ⟨selected.2,result.value,result.remaining,result.allocated,result.consumed,result.nextOrdinal,
                    result.balanced,inferredEffect result.events,result.events.any Event.quantumUse,
                    result.staticRows,calls,callsRead,result.events.flatMap Event.basisOffsets,
                    result.events.flatMap Event.computedOffsets⟩
                let event : StaticEvent sources owner :=
                  ⟨tokens,written,name,signature,generic,naturals,scope,selection,thenTree,elseTree,
                    thenCalls,thenCallsRead,elseCalls,elseCallsRead,environment,nextOrdinal,⟨selected.1,arm⟩,
                    selectedTokens,remaining,projected,held⟩
                return (← outcome environment result.value remaining result.allocated result.consumed
                  result.nextOrdinal [.staticConditional event result.events]
                  (selection.naturals.sourceRows ++ result.staticRows),context)
      | .variant written =>
        let reference ← SourceNominal.readVariant sources owner scope written
        let rows ← NaturalRows.typeRead sources owner naturals.helpers.val scope
          (written.typeTokens.map (·.text)) reference.nominal.query
        return (← outcome environment [.ordinary reference.nominal.query.basis (.ordinal reference.ordinal)]
          environment [] [] nextOrdinal [] rows,context)
      | .record written children =>
        let reference ← SourceNominal.readRecord sources owner scope written
        let (values,remaining,allocated,consumed,ordinal,events,rows,context) ←
          evaluateChildren children.trees context
        Finite.exactWork (Exact.charge (32*((values.map valueFields).sum+
          Raw.OwnerFlow.fields [⟨0,reference.nominal.query.basis⟩]+1)*(reference.fields.length+1)))
        let value ← adapt (SourceRuntimeNominalValue.construct reference values)
        let typeRows ← NaturalRows.typeRead sources owner naturals.helpers.val scope
          (written.typeTokens.map (·.text)) reference.nominal.query
        return (← outcome environment value remaining allocated consumed ordinal events (rows ++ typeRows),context)
      | .projection written receiver =>
        let (result,context) ← recurse naturals held scope nextOrdinal environment receiver context
        let [.ordinary basis expression] := result.value | throw .request
        let reference ← SourceNominal.readProjection sources owner basis written
        Finite.exactWork (Exact.charge (32*(valueFields result.value+
          Raw.OwnerFlow.fields [⟨0,reference.field.basis⟩]+1)*(reference.definition.fields.length+1)))
        let value ← adapt (SourceRuntimeNominalValue.project reference expression)
        let typeRows ← NaturalRows.nominalOrigins sources naturals.helpers.val basis
        return (← outcome environment value result.remaining result.allocated result.consumed
          result.nextOrdinal result.events (result.staticRows ++ typeRows),context)
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
        let _ ← QuantumMatch.checkSelector parsed selector.basis
        Finite.guard (selector.ordinal != target.ordinal &&
          QuantumSequence.armsAllowed scope signature.operationNames parsed.arms) .request
        return (← outcome environment [.tuple 2,.owner selector,.owner target] last.remaining
          (first.allocated ++ last.allocated) (first.consumed ++ last.consumed) last.nextOrdinal
          (first.events ++ last.events ++ [.selection tokens parsed original selector target scope naturals
            held last.remaining]) (first.staticRows ++ last.staticRows ++ naturals.sourceRows),context)
      | .selectionExpression tokens parsed original selectorTree targetTree =>
        let (first,context) ← recurse naturals held scope nextOrdinal environment selectorTree context
        let [.owner selector] := first.value | throw .request
        let (last,context) ← recurse naturals (held ++ [selector]) scope first.nextOrdinal first.remaining targetTree context
        let [.owner target] := last.value | throw .request
        let _ ← QuantumMatch.checkSelector parsed selector.basis
        Finite.guard (selector.ordinal != target.ordinal &&
          QuantumSequence.armsAllowed scope signature.operationNames parsed.arms) .request
        return (← outcome environment [.tuple 2,.owner selector,.owner target] last.remaining
          (first.allocated ++ last.allocated) (first.consumed ++ last.consumed) last.nextOrdinal
          (first.events ++ last.events ++ [.selection tokens parsed original selector target scope naturals
            held last.remaining]) (first.staticRows ++ last.staticRows ++ naturals.sourceRows),context)
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
              let binding ← SourceBasisBindings.activeAt basis written.parts.keyword.span.startByte
              Finite.exactWork (Exact.charge (16*(Raw.OwnerFlow.fields
                [⟨0,binding.ports.input⟩,⟨0,binding.ports.output⟩,input,⟨0,outputBasis⟩]+1)))
              let inputType : PLift (binding.ports.input = input.basis) ←
                if exactInput : binding.ports.input = input.basis then
                  pure (⟨exactInput⟩ : PLift (binding.ports.input = input.basis)) else throw .request
              let outputType : PLift (binding.ports.output = outputBasis) ←
                if exactOutput : binding.ports.output = outputBasis then
                  pure (⟨exactOutput⟩ : PLift (binding.ports.output = outputBasis)) else throw .request
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
                  ⟨tokens,written,name,signature,generic,naturals,scope,input,ordinaryBefore,bodyInitial,inputResult.nextOrdinal,bodyTree,body.value,
                    inputTypes,outputBasis,binding,inputType.down,outputType.down,function,seeded,bodyCalls,originalCalls,inferredEffect body.events,
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
                      inferredEffect left.events,left.events.any Event.quantumUse,left.staticRows,leftCalls,thenCalls,
                      left.events.flatMap Event.basisOffsets,left.events.flatMap Event.computedOffsets⟩
                  let rightArm : Arm sources owner condition.remaining written.parts.elseBody :=
                    ⟨elseTree,right.value,right.remaining,right.allocated,right.consumed,right.nextOrdinal,right.balanced,
                      inferredEffect right.events,right.events.any Event.quantumUse,right.staticRows,rightCalls,elseCalls,
                      right.events.flatMap Event.basisOffsets,right.events.flatMap Event.computedOffsets⟩
                  let event : BranchEvent sources owner :=
                    ⟨tokens,written,name,signature,generic,naturals,scope,conditionValue,condition.remaining,condition.nextOrdinal,
                      leftArm,rightArm,remaining,thenOuter,elseOuter,value,phis,merged,held⟩
                  let introduced := left.allocated ++ right.allocated ++ phis.map (·.output)
                  let retired := SourceRuntimeBranches.retired condition.remaining remaining ++
                    left.allocated ++ right.allocated
                  return (← outcome environment value remaining (condition.allocated ++ introduced)
                    (condition.consumed ++ retired) (right.nextOrdinal+phis.length)
                    (condition.events ++ [.conditional event left.events right.events])
                    (condition.staticRows ++ left.staticRows ++ right.staticRows ++ naturals.sourceRows),context)
      | .call call children =>
        if let some written ← adapt (SourceRuntimeTransformSyntax.read call.call.callee) then
          let lookup ← SourceContext.read sources owner context scope written.base.2.callee (sourceModules signature)
          let candidate ← Finite.lift lookup.answer.checked
          -- Classification uses the original resolved name. Primitive and
          -- opaque-formal applications retain their separate unary Op rule.
          if (QuantumSignature.candidateResolution candidate).isSome then
            let bound ← readTargetWithWritten signature naturals written.base.2 candidate
            let target := bound.target
            let (values,remaining,allocated,consumed,ordinal,events,rows,context) ←
              evaluateChildren children.trees lookup.context
            -- The child is checked even when one of the original powers is
            -- zero. No selected-body effect is inferred from the prefix.
            let _ ← SourceRecursion.read generic scope written.base.1 target.signature.original
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
                          ⟨tokens,call,name,signature,naturals,scope,written,target,bound.originalWritten,forward,
                            visibleUnitary,counts,originalCounts,copies,multiplied,access,ports,portsRead,
                            values,ordinal,value,new,used,after,applied,held,remaining⟩
                        return (← outcome environment value remaining (allocated ++ new) (consumed ++ used)
                          after (events ++ [.transform event]) (rows ++ (Event.transform event).staticRows),context)
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
                (events ++ [.operation event]) (rows ++ (Event.operation event).staticRows),context)
          else throw .request
        let written ← adapt (StaticApplication.readSyntax call.call.callee)
        let lookup ← SourceContext.read sources owner context scope written.callee (sourceModules signature)
        let candidate ← Finite.lift lookup.answer.checked
        let (values,remaining,allocated,consumed,ordinal,events,rows,context) ← evaluateChildren children.trees lookup.context
        match selected : primitive candidate with
        | some .phase =>
          let application ← PhaseApplication.readWithCandidate sources owner naturals scope call candidate
          let [[.owner operand]] := values | throw .request
          if bit : operand.basis = [.bit] then
            let phase : PhaseEvent sources owner :=
              ⟨tokens,call,scope,naturals,application,operand,bit,held,remaining⟩
            return (← outcome environment [.owner operand] remaining allocated consumed ordinal
              (events ++ [.phase phase]) (rows ++ (Event.phase phase).staticRows),context)
          else throw .request
        | some kind =>
          if SourceRegisterApplication.selected kind then
            let application ← SourceRegisterApplication.read sources owner naturals scope written kind
            Finite.exactWork (Exact.charge (64*((values.map valueFields).sum+
              (application.arguments.map (·.value)).sum+1)))
            match applied : SourceRegisterApplication.apply kind (application.arguments.map (·.value)) values ordinal with
            | .error _ => throw .request
            | .ok (value,new,used,after) =>
              let event : RegisterEvent sources owner :=
                ⟨tokens,call,scope,naturals,written,candidate,kind,selected,application,values,ordinal,
                  value,new,used,after,applied,held,remaining⟩
              return (← outcome environment value remaining (allocated ++ new) (consumed ++ used)
                after (events ++ [.registerPrimitive event]) (rows ++ (Event.registerPrimitive event).staticRows),context)
          Finite.guard written.arguments.isEmpty .request
          match applied : SourceRuntimePrimitive.apply kind ⟨owner,name,call.calleeOffset⟩ values ordinal with
          | .error _ => throw .request
          | .ok (value,new,used,after) =>
            let event : PrimitiveEvent sources owner :=
              ⟨tokens,call,scope,written,candidate,kind,selected,values,value,new,used,after,held,remaining,
                ⟨name,ordinal,applied⟩⟩
            return (← outcome environment value remaining (allocated ++ new) (consumed ++ used) after
              (events ++ [.primitive event]) rows,context)
        | none =>
          let target ← readTarget signature naturals written candidate
          if matched : values.map typeOf = target.signature.parameters.map (·.tree) then
            let _ ← SourceRecursion.read generic scope call.call.callee target.signature.original
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
                  (ordinal+fresh.length) (events ++ [.named event]) (rows ++ (Event.named event).staticRows),context)
          else throw .request)

def quantumUse {sources owner name} (signature : Signature sources owner name)
    (events : List (Event sources owner)) : Bool :=
  signature.parameters.any (fun part => !((Semantics.RuntimeType.ownerBases part.tree).getD []).isEmpty) ||
    !((Semantics.RuntimeType.ownerBases signature.result.tree).getD []).isEmpty ||
    events.any Event.quantumUse

/-- Original guarded decrease is checked at each self-call occurrence before
this concrete specialization stack. Mutual and repeated instances refuse;
the existing depth capacity is independent of a caller expression's tokens. -/
def readNestedWithSetup (sources : Sources) : (fuel : Nat) → (active : List SourceCallStack.Frame) →
    {owner name : String} → (signature : Signature sources owner name) →
    Option (OriginalSetup signature) → Finite.WorkM (Evaluated signature) :=
  Nat.rec (fun _ {_ _} _ _ => throw .limit) (fun _ previous active {_ _} signature provided => do
    let frame := callFrame signature
    let _ ← SourceCallStack.read active frame
    let tokens := signature.original.occurrence.body
    -- A retained setup already paid for reading and checking these exact body
    -- tokens. The header, owner environment and closed traversal still run.
    if provided.isNone then Finite.exactWork (Exact.charge (SourceTrace.Meter.syntaxWork tokens))
    Finite.exactWork (Exact.charge (SourceTrace.Meter.syntaxWork signature.original.occurrence.header+
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
          let setup ← match provided with
            | some setup => pure setup
            | none => readOriginalSetup signature
          let tree := setup.tree
          let generic := setup.generic
          Finite.guard (!signature.original.parsedHeader.ordinaryOnly || !generic.quantumUse) .request
          Finite.guard (!signature.original.parsedHeader.ordinaryOnly || generic.recursiveCalls.isEmpty) .request
          Finite.guard (!signature.original.declaration.isPublic || !generic.quantumUse ||
            signature.original.parsedHeader.effect.isSome) .request
          let originalAsserted : PLift (SourceEffect.permits signature.original.parsedHeader.effect generic.inferredEffect = true) ←
            if asserted : SourceEffect.permits signature.original.parsedHeader.effect generic.inferredEffect = true then
              pure (⟨asserted⟩ : PLift (SourceEffect.permits signature.original.parsedHeader.effect generic.inferredEffect = true))
            else throw .request
          let basis ← SourceBasisBindings.prepare signature.instantiation generic.basisObligations
          let computed ← SourceComputedBindings.prepare signature.instantiation generic.computedObligations
          let naturals ← signature.naturals
          let (result,_) ← evalWithReader signature generic basis computed
            (fun callee => do return (← previous (frame :: active) callee none).summary)
            (tokens.length+1) naturals [] (signature.staticNames ++ initial.map (·.name))
            nextOwner initial tree {}
          let basisCovered : PLift (basis.covered (result.events.flatMap Event.basisOffsets) = true) ←
            if covered : basis.covered (result.events.flatMap Event.basisOffsets) = true then
              pure (⟨covered⟩ : PLift (basis.covered (result.events.flatMap Event.basisOffsets) = true))
            else throw .request
          let computedCovered : PLift (computed.covered (result.events.flatMap Event.computedOffsets) = true) ←
            if covered : computed.covered (result.events.flatMap Event.computedOffsets) = true then
              pure (⟨covered⟩ : PLift (computed.covered (result.events.flatMap Event.computedOffsets) = true))
            else throw .request
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
                        let staticRows ← SourceTrace.retainStaticRows (generic.sourceRows ++ result.staticRows)
                        let summary : Summary signature :=
                          ⟨patterns,parameters,parameterValues,nextOwner,nextOrdinary,valuesRead,
                          initial,seeded,tree,setup.parsed,generic,setup.genericRead,
                          originalAsserted.down,basis,computed,result.value,result.remaining,result.allocated,
                          result.consumed,result.nextOrdinal,issued,ordinalCount,complete,balanced,typed,
                          inferredEffect result.events,asserted,quantumUse signature result.events,publicQuantum,
                          staticRows⟩
                        return ⟨summary,result.events,rfl,basisCovered.down,computedCovered.down⟩
                      else throw .request
                    else throw .request
                  else throw .request
                else throw .request
              else throw .request
            else throw .request
          else throw .request)

/-- The fresh public source-body wrapper retains its original action identity.
Only explicitly supplied exact setup evidence takes the separate path above. -/
def readNested (sources : Sources) (fuel : Nat) (active : List SourceCallStack.Frame)
    {owner name : String} (signature : Signature sources owner name) : Finite.WorkM (Evaluated signature) :=
  readNestedWithSetup sources fuel active signature none

inductive Traversal {sources owner name} (signature : Signature sources owner name)
    (evaluated : Evaluated signature) : Type where
  | fresh (original : ∃ before after,
      (readNested sources (SourceTrace.sourceFuel sources) [] signature).run before = (.ok evaluated,after)) :
      Traversal signature evaluated
  | prepared (setup : OriginalSetup signature) (original : ∃ before after,
      (readNestedWithSetup sources (SourceTrace.sourceFuel sources) [] signature (some setup)).run before =
        (.ok evaluated,after)) : Traversal signature evaluated

structure Checked (sources : Sources) (owner name : String) where
  signature : Signature sources owner name
  evaluated : Evaluated signature
  traversed : Traversal signature evaluated

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
    ⟨signature,summary.val,.fresh (by with_reducible exact summary.property)⟩
  return ⟨checked,rfl⟩

/-- Reuse only an actual original setup for this identical signature. Closed
body evaluation, recursion/stack checks, owner history, effects, row relevance
and every finite basis/computed coverage check all run again. The retained
traversal records this real prepared invocation, not a fictitious fresh run. -/
def readBodyWithOriginalSetup {sources owner name} (signature : Signature sources owner name)
    (setup : OriginalSetup signature) : Finite.WorkM (Body signature) := do
  let evaluated ← NaturalAffine.witness
    (readNestedWithSetup sources (SourceTrace.sourceFuel sources) [] signature (some setup))
  let checked : Checked sources owner name :=
    ⟨signature,evaluated.val,.prepared setup (by with_reducible exact evaluated.property)⟩
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
  let body ← readBodyWithOriginalSetup event.target.signature (originalSetup event.canonical)
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
  let body ← readBodyWithOriginalSetup event.target.signature (originalSetup event.forward)
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
  let basis ← SourceBasisBindings.prepare event.signature.instantiation event.generic.basisObligations
  let computed ← SourceComputedBindings.prepare event.signature.instantiation event.generic.computedObligations
  let (body,_) ← evalWithReader event.signature event.generic basis computed
    (fun callee => do return (← readNested sources (SourceTrace.sourceFuel sources)
      [callFrame event.signature] callee).summary)
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
  thenBasis : thenResult.events.flatMap Event.basisOffsets = event.thenArm.basisOffsets
  elseBasis : elseResult.events.flatMap Event.basisOffsets = event.elseArm.basisOffsets
  thenComputed : thenResult.events.flatMap Event.computedOffsets = event.thenArm.computedOffsets
  elseComputed : elseResult.events.flatMap Event.computedOffsets = event.elseArm.computedOffsets

/-- Both original branches are recovered under the same original environment.
The second branch uses a disjoint issued-identity interval; no condition value
selects or suppresses an original effect, type check or owner obligation. -/
def readBranchSource {sources caller} (event : BranchEvent sources caller) :
    Finite.WorkM (BranchBodies event) := do
  let readCallee := fun {owner name} (callee : Signature sources owner name) => do
    return (← readNested sources (SourceTrace.sourceFuel sources) [callFrame event.signature] callee).summary
  let basis ← SourceBasisBindings.prepare event.signature.instantiation event.generic.basisObligations
  let computed ← SourceComputedBindings.prepare event.signature.instantiation event.generic.computedObligations
  let (left,_) ← evalWithReader event.signature event.generic basis computed readCallee
    (event.written.parts.thenBody.length+1) event.naturals event.held event.scope event.nextOrdinal
    event.before event.thenArm.tree {}
  let (right,_) ← evalWithReader event.signature event.generic basis computed readCallee
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
      left.nextOrdinal = event.thenArm.nextOrdinal ∧ right.nextOrdinal = event.elseArm.nextOrdinal ∧
      left.events.flatMap Event.basisOffsets = event.thenArm.basisOffsets ∧
      right.events.flatMap Event.basisOffsets = event.elseArm.basisOffsets ∧
      left.events.flatMap Event.computedOffsets = event.thenArm.computedOffsets ∧
      right.events.flatMap Event.computedOffsets = event.elseArm.computedOffsets then
    let ⟨thenValue,elseValue,thenEffect,elseEffect,thenRemaining,elseRemaining,thenAllocated,
      elseAllocated,thenConsumed,elseConsumed,thenOrdinal,elseOrdinal,thenBasis,elseBasis,thenComputed,elseComputed⟩ := checked
    return ⟨left,right,thenValue,elseValue,thenEffect,elseEffect,thenRemaining,elseRemaining,
      thenAllocated,elseAllocated,thenConsumed,elseConsumed,thenOrdinal,elseOrdinal,thenBasis,elseBasis,thenComputed,elseComputed⟩
  else throw .request

structure StaticBody {sources caller} (event : StaticEvent sources caller) where
  result : Outcome sources caller event.before
  value : result.value = event.selected.2.value
  remaining : result.remaining = event.selected.2.remaining
  allocated : result.allocated = event.selected.2.allocated
  consumed : result.consumed = event.selected.2.consumed
  nextOrdinal : result.nextOrdinal = event.selected.2.nextOrdinal
  effect : inferredEffect result.events = event.selected.2.inferredEffect
  quantumUse : result.events.any Event.quantumUse = event.selected.2.quantumUse
  basis : result.events.flatMap Event.basisOffsets = event.selected.2.basisOffsets
  computed : result.events.flatMap Event.computedOffsets = event.selected.2.computedOffsets

/-- Static selection contributes no runtime condition or phi. Its selected
original child is freshly traversed in the containing block, while the retained
whole original generic judgment checks both source arms independently. -/
def readStaticSource {sources caller} (event : StaticEvent sources caller) :
    Finite.WorkM (StaticBody event) := do
  let basis ← SourceBasisBindings.prepare event.signature.instantiation event.generic.basisObligations
  let computed ← SourceComputedBindings.prepare event.signature.instantiation event.generic.computedObligations
  let (result,_) ← evalWithReader event.signature event.generic basis computed
    (fun callee => do return (← readNested sources (SourceTrace.sourceFuel sources)
      [callFrame event.signature] callee).summary)
    (event.selected.1.length+1) event.selection.naturals event.held event.scope event.nextOrdinal
    event.before event.selected.2.tree {}
  Finite.exactWork (Exact.charge (32*(valueFields result.value+valueFields event.selected.2.value+
    environmentCells result.remaining+environmentCells event.selected.2.remaining+
    result.events.length+Raw.OwnerFlow.fields (result.allocated ++ result.consumed ++
      event.selected.2.allocated ++ event.selected.2.consumed)+1)))
  if checked : result.value = event.selected.2.value ∧ result.remaining = event.selected.2.remaining ∧
      result.allocated = event.selected.2.allocated ∧ result.consumed = event.selected.2.consumed ∧
      result.nextOrdinal = event.selected.2.nextOrdinal ∧
      inferredEffect result.events = event.selected.2.inferredEffect ∧
      result.events.any Event.quantumUse = event.selected.2.quantumUse ∧
      result.events.flatMap Event.basisOffsets = event.selected.2.basisOffsets ∧
      result.events.flatMap Event.computedOffsets = event.selected.2.computedOffsets then
    let ⟨value,remaining,allocated,consumed,nextOrdinal,effect,quantumUse,basis,computed⟩ := checked
    return ⟨result,value,remaining,allocated,consumed,nextOrdinal,effect,quantumUse,basis,computed⟩
  else throw .request

structure MatchBodies {sources caller} (event : MatchEvent sources caller) where
  results : List (Outcome sources caller event.before)
  original : results.map Outcome.description = event.arms.map (fun arm => arm.2.description)

/-- Every ordinary match arm is freshly traversed at its original slice with
the same pre-environment. No known constructor suppresses an inactive arm's
effect, source row, owner, measurement history or native body obligation. -/
def readMatchSource {sources caller} (event : MatchEvent sources caller) :
    Finite.WorkM (MatchBodies event) := do
  let basis ← SourceBasisBindings.prepare event.signature.instantiation event.generic.basisObligations
  let computed ← SourceComputedBindings.prepare event.signature.instantiation event.generic.computedObligations
  let (results,_) ← event.arms.foldlM (fun (results,ordinal) arm => do
    let (result,_) ← evalWithReader event.signature event.generic basis computed
      (fun callee => do return (← readNested sources (SourceTrace.sourceFuel sources)
        [callFrame event.signature] callee).summary)
      (arm.1.length+1) event.naturals event.held event.scope ordinal event.before arm.2.tree {}
    return (results ++ [result],result.nextOrdinal))
    (([] : List (Outcome sources caller event.before)),event.nextOrdinal)
  Finite.exactWork (Exact.charge (64*((results.map fun result => valueFields result.value+
    environmentCells result.remaining+result.events.length+
    Raw.OwnerFlow.fields (result.allocated ++ result.consumed)).sum+1)))
  if original : results.map Outcome.description = event.arms.map (fun arm => arm.2.description) then
    return ⟨results,original⟩
  else throw .request

structure ComputedBody {sources caller} (event : ComputedEvent sources caller) where
  result : Outcome sources caller event.initial.environment
  original : result.description = event.body.description

/-- Recover the exact original scoped use body, including its full owner
frame, ordinary expressions and nested source obligations. This read supplies
no protected diagonal or certified computed-relation equation. -/
def readComputedSource {sources caller} (event : ComputedEvent sources caller) :
    Finite.WorkM (ComputedBody event) := do
  let basis ← SourceBasisBindings.prepare event.signature.instantiation event.generic.basisObligations
  let computed ← SourceComputedBindings.prepare event.signature.instantiation event.generic.computedObligations
  let (result,_) ← evalWithReader event.signature event.generic basis computed
    (fun callee => do return (← readNested sources (SourceTrace.sourceFuel sources)
      [callFrame event.signature] callee).summary)
    (event.written.parts.body.length+1) event.naturals
    (event.held ++ owners event.before ++ event.initial.heldData)
    (SourceRuntimeComputed.names event.written ++ event.scope) event.initial.nextOrdinal
    event.initial.environment event.body.tree {}
  Finite.exactWork (Exact.charge (64*(valueFields result.value+valueFields event.body.value+
    environmentCells result.remaining+environmentCells event.body.remaining+result.events.length+
    Raw.OwnerFlow.fields (result.allocated ++ result.consumed ++ event.body.allocated ++ event.body.consumed)+1)))
  if original : result.description = event.body.description then return ⟨result,original⟩
  else throw .request

/-- The predicate is an original total classical body with one explicit exact
basis parameter. Its complete finite table still needs independent agreement
with the actual native compute/uncompute operation. -/
def readComputedPredicateBody {sources caller} (event : ComputedEvent sources caller) :
    Finite.WorkM (Body event.predicate.target.signature) := do
  let body ← readBodyWithSignature event.predicate.target.signature
  Finite.exactWork (Exact.charge (32*(valueFields body.checked.summary.value+
    valueFields event.predicate.canonical.value+body.checked.events.length+1)))
  Finite.guard (body.checked.summary.value == event.predicate.canonical.value &&
    body.checked.summary.allocated.isEmpty && body.checked.summary.consumed.isEmpty &&
    !body.checked.summary.generic.quantumUse) .request
  return body

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
