import QleisliKernel.SourceTypes.GenericTypeTrace

/-! One whole-original-source audit for one exact Sources value. Runtime body
records are checked once, before any selected source projection. The audit
does not discharge finite injection, Meaning equality, actual provider-body or
inverse/control obligations, and grants no blanket dependency-row coverage.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.GenericCatalogue
open Finite GenericTypeTrace SourceEffectClosure

private def adapt {α : Type} (value : Except String α) : WorkM α :=
  lift (value.mapError fun _ => .request)

private def braceTerminated (tokens : List LocatedToken) : Bool :=
  let tokens := if tokens.head?.map (·.text) == some "pub" then tokens.drop 1 else tokens
  match tokens.map (·.text) with
  | "fn" :: _ | "enum" :: _ | "struct" :: _ => true
  | "static" :: "fn" :: _ | "classical" :: "fn" :: _ |
    "unitary" :: "fn" :: _ | "isometry" :: "fn" :: _ | "observe" :: "fn" :: _ => true
  | _ => false

/-- Split the complete original top level, retaining every token. Imports may
contain brace groups, so only declaration bodies terminate at a closing brace.
Unknown/trailing text cannot disappear through the declaration-name scanner. -/
private def splitPieces : Nat → Nat → List LocatedToken → List LocatedToken →
    List (List LocatedToken) → Except String (List (List LocatedToken)) :=
  Nat.rec (fun _ _ _ _ => throw "original module traversal capacity")
    (fun _ next depth pending tokens previous => do
      match tokens with
      | [] =>
        if depth == 0 && pending.isEmpty then pure previous.reverse
        else throw "incomplete original module item"
      | token :: rest =>
        let current := pending ++ [token]
        if token.text == "{" then next (depth+1) current rest previous
        else if token.text == "}" then
          if depth == 0 then throw "unmatched original module brace"
          else if depth == 1 && braceTerminated current then next 0 [] rest (current :: previous)
          else next (depth-1) current rest previous
        else if token.text == ";" && depth == 0 then next 0 [] rest (current :: previous)
        else next depth current rest previous)

abbrev Key := String × String × Bool

private def pieceKeys (tokens : List LocatedToken) : Except String (List Key) := do
  let isPublic := tokens.head?.map (·.text) == some "pub"
  let tokens := if isPublic then tokens.drop 1 else tokens
  let texts := tokens.map (·.text)
  match texts with
  | "use" :: tail =>
    if tail.getLast? != some ";" then throw "unterminated original import"
    let paths ← Imports.read tail.dropLast
    paths.mapM fun path => do
      let name :: _ := path | throw "empty original import"
      pure (name,"import",isPublic)
  | "static" :: "fn" :: name :: _ =>
    if !identifier name || texts.getLast? != some "}" then throw "invalid original static declaration"
    pure [(name,"static-fn",isPublic)]
  | "classical" :: "fn" :: name :: _ | "unitary" :: "fn" :: name :: _ |
    "isometry" :: "fn" :: name :: _ | "observe" :: "fn" :: name :: _ |
    "fn" :: name :: _ =>
    if !identifier name || texts.getLast? != some "}" then throw "invalid original function declaration"
    pure [(name,"fn",isPublic)]
  | "enum" :: name :: _ | "struct" :: name :: _ =>
    if !identifier name || texts.getLast? != some "}" then throw "invalid original nominal declaration"
    pure [(name,texts.headD "",isPublic)]
  | "meaning" :: name :: _ =>
    if !identifier name || texts.getLast? != some ";" then throw "invalid original Meaning declaration"
    pure [(name,"meaning",isPublic)]
  | _ => throw "unsupported original top-level item"

structure Module where
  owner : String
  source : String
  tokens : List LocatedToken
  lexed : lexLocated source = .ok tokens
  disabled : Bool
  policy : ModuleHeader.policyTokens (tokens.map (·.text)) = .ok disabled
  pieces : List (List LocatedToken)
  partition : splitPieces (tokens.length+1) 0 [] (if disabled then tokens.drop 5 else tokens) [] = .ok pieces
  keys : List Key
  classified : (pieces.mapM pieceKeys).map List.flatten = .ok keys
  catalogue : SourceCatalogue
  scanned : sourceCatalogue source = .ok catalogue
  complete : keys = catalogue.declarations.map (fun decl => (decl.name,decl.kind,decl.isPublic))
  unique : (catalogue.declarations.map (·.name)).eraseDups.length = catalogue.declarations.length

def readModule (row : String × String) : WorkM Module := do
  let (owner,source) := row
  exactWork (Exact.charge (64*(owner.utf8ByteSize+source.utf8ByteSize+1)))
  match lexed : lexLocated source with
  | .error _ => throw .request
  | .ok tokens =>
    match policy : ModuleHeader.policyTokens (tokens.map (·.text)) with
    | .error _ => throw .request
    | .ok disabled =>
      match partition : splitPieces (tokens.length+1) 0 [] (if disabled then tokens.drop 5 else tokens) [] with
      | .error _ => throw .request
      | .ok pieces =>
        match classified : (pieces.mapM pieceKeys).map List.flatten with
        | .error _ => throw .request
        | .ok keys =>
          match scanned : sourceCatalogue source with
          | .error _ => throw .request
          | .ok catalogue =>
            if complete : keys = catalogue.declarations.map (fun decl => (decl.name,decl.kind,decl.isPublic)) then
              if unique : (catalogue.declarations.map (·.name)).eraseDups.length = catalogue.declarations.length then
                pure ⟨owner,source,tokens,lexed,disabled,policy,pieces,partition,keys,classified,catalogue,scanned,complete,unique⟩
              else throw .request
            else throw .request

def runtimeIds (modules : List Module) : List DefId := modules.flatMap fun row =>
  (row.catalogue.declarations.filter (·.kind == "fn")).map fun declaration => (row.owner,declaration.name)

def auxiliaryIds (modules : List Module) : List (String × Declaration) := modules.flatMap fun row =>
  (row.catalogue.declarations.filter (·.kind != "fn")).map (row.owner,·)

inductive Auxiliary (sources : Sources) where
  | helper (key : NaturalCatalog.Key) (entry : NaturalHelpers.Entry)
      (original : entry.original.key = key)
  | nominal (owner name : String) (catalogue : Members.Catalogue)
      (read : ∃ before after,(Members.readOriginal sources owner name).run before = (.ok catalogue,after))
  | record (owner name : String) (fields : MemberFields.Record)
      (read : ∃ before after,(MemberFields.readOriginalFields sources owner name).run before = (.ok fields,after))
  | meaning (owner name : String) (meaning : SourceMeaning.Checked sources (some owner) owner name)
  | imported (owner name : String) (resolved : Resolved)
      (read : ∃ before after,(resolveReference sources owner [name]).run before = (.ok resolved,after))

def Auxiliary.meanings {sources} : Auxiliary sources → List (SourceMeaning.Graph sources)
  | .meaning _ _ specification => [specification.graph]
  | _ => []

def readAuxiliary (sources : Sources) (helpers : NaturalHelpers.Checked sources)
    (item : String × Declaration) : WorkM (Auxiliary sources) := do
  let (owner,declaration) := item
  match declaration.kind with
  | "static-fn" =>
    let key : NaturalCatalog.Key := ⟨owner,declaration.name⟩
    let some entry := helpers.entries.find? (·.original.key == key) | throw .request
    if original : entry.original.key = key then pure (.helper key entry original) else throw .request
  | "enum" =>
    let catalogue ← NaturalAffine.witness (Members.readOriginal sources owner declaration.name)
    pure (.nominal owner declaration.name catalogue.val (by with_reducible exact catalogue.property))
  | "struct" =>
    let fields ← NaturalAffine.witness (MemberFields.readOriginalFields sources owner declaration.name)
    pure (.record owner declaration.name fields.val (by with_reducible exact fields.property))
  | "meaning" => pure (.meaning owner declaration.name (← SourceMeaning.read sources (some owner) owner declaration.name))
  | "import" =>
    let resolved ← NaturalAffine.witness (resolveReference sources owner [declaration.name])
    pure (.imported owner declaration.name resolved.val (by with_reducible exact resolved.property))
  | _ => throw .request

def readModuleOriginals (sources : Sources) (row : Module) : WorkM (OrdinarySignature.Originals sources) := do
  exactWork (Exact.charge (16*((sources.toList.map fun source => source.1.utf8ByteSize+1).sum+row.owner.utf8ByteSize+1)))
  if bound : sources.toList.filter (fun source => source.1 == row.owner) = [(row.owner,row.source)] then
    let known : OrdinarySignature.KnownModule sources row.owner :=
      ⟨row.source,bound,row.tokens,row.lexed,row.disabled,row.policy,row.catalogue,row.scanned,row.source.toUTF8,rfl⟩
    OrdinarySignature.readKnownModule known
  else throw .request

def readOriginals (sources : Sources) (modules : List Module) : WorkM (OrdinarySignature.Originals sources) := do
  pure (← modules.mapM (readModuleOriginals sources)).flatten

def readBodies (sources : Sources) (helpers : NaturalHelpers.Checked sources)
    (originals : OrdinarySignature.Originals sources) (ids : List DefId) : WorkM (List (BodyRecord sources)) :=
  ids.mapM fun (owner,name) => readBody sources owner name (some helpers) (some originals)

structure RuntimeChecked (sources : Sources) where
  modules : List Module
  moduleRead : ∃ before after,(sources.toList.mapM readModule).run before = (.ok modules,after)
  moduleNames : modules.map (·.owner) = sources.toList.map (·.1)
  uniqueModules : (modules.map (·.owner)).eraseDups.length = modules.length
  originals : OrdinarySignature.Originals sources
  originalsRead : ∃ before after,(readOriginals sources modules).run before = (.ok originals,after)
  originalsComplete : originals.map (fun original => (original.owner,original.name)) = runtimeIds modules
  helpers : NaturalHelpers.Checked sources
  records : List (BodyRecord sources)
  bodiesRead : ∃ before after,(readBodies sources helpers originals (runtimeIds modules)).run before = (.ok records,after)
  identified : records.map (·.id) = runtimeIds modules
  cycles : ∃ before after,(checkCycles records).run before = (.ok (),after)
  all : AllInferred records records

def bodyOriginal {sources owner name} (body : BodyRecord sources)
    (sameOwner : body.owner = owner) (sameName : body.name = name) : OrdinarySignature.Original sources owner name := by
  rcases body with ⟨bodyOwner,bodyName,definition,tree,outcome,checked⟩
  cases sameOwner
  cases sameName
  exact definition.original.envelope

theorem bodyOriginal_heq {sources owner name} (body : BodyRecord sources)
    (sameOwner : body.owner = owner) (sameName : body.name = name) :
    HEq body.definition.original.envelope (bodyOriginal body sameOwner sameName) := by
  rcases body with ⟨bodyOwner,bodyName,definition,tree,outcome,checked⟩
  cases sameOwner
  cases sameName
  rfl

structure Entry {sources} (catalogue : RuntimeChecked sources) {owner name}
    (original : OrdinarySignature.Original sources owner name) where
  index : Fin catalogue.records.length
  sameOriginal : HEq (catalogue.records[index.val]'index.isLt).definition.original.envelope original

def Entry.body {sources catalogue owner name original} (entry : @Entry sources catalogue owner name original) :
    BodyRecord sources := catalogue.records[entry.index.val]'entry.index.isLt

def Entry.inferred {sources catalogue owner name original} (entry : @Entry sources catalogue owner name original) :
    Inferred catalogue.records entry.body := catalogue.all.get entry.index

def lookup {sources owner name} (catalogue : RuntimeChecked sources)
    (original : OrdinarySignature.Original sources owner name) : WorkM (Entry catalogue original) := do
  exactWork (Exact.charge (32*(catalogue.records.length+original.source.utf8ByteSize+1)))
  let index := catalogue.records.findIdx fun body => body.owner == owner && body.name == name
  if bounded : index < catalogue.records.length then
    let body := catalogue.records[index]'bounded
    if sameOwner : body.owner = owner then
      if sameName : body.name = name then
        let selected := bodyOriginal body sameOwner sameName
        if envelope : selected.source = original.source ∧ selected.declaration = original.declaration ∧
            selected.occurrence = original.occurrence then
          have same := OrdinarySignature.Original.sameEnvelope selected original envelope.1 envelope.2.1 envelope.2.2
          pure ⟨⟨index,bounded⟩,(bodyOriginal_heq body sameOwner sameName).trans (heq_of_eq same)⟩
        else throw .request
      else throw .request
    else throw .request
  else throw .request

def checkMeaningReferences {sources} (catalogue : RuntimeChecked sources) (graph : SourceMeaning.Graph sources) :
    WorkM Unit := do
  for reference in graph.references do
    let original ← lookup catalogue reference.signature.original
    let effect := if reference.internalInference then original.inferred.inferredEffect
      else reference.signature.original.parsedHeader.effect.getD .observe
    guard (SourceEffect.rank effect ≤ SourceEffect.rank reference.expectedEffect) .request
  for reference in graph.classical do
    let original ← lookup catalogue reference.signature.original
    guard (!original.inferred.quantumUse) .request

def bodyMeanings {sources} (body : BodyRecord sources) : List (SourceMeaning.Graph sources) :=
  (body.definition.operations.flatMap (·.2.meanings) ++ body.outcome.meanings).map (·.meaning.graph)

def bodyReferences {sources} (body : BodyRecord sources) : List DefId :=
  body.outcome.references ++ (bodyMeanings body).flatMap fun graph =>
    (graph.references.map fun reference =>
      (reference.resolution.result.moduleName,reference.resolution.result.declaration.name)) ++
    (graph.classical.map fun reference =>
      (reference.resolution.result.moduleName,reference.resolution.result.declaration.name))

/-- Project exact already-checked records by actual original reference edges.
This operation never rechecks a body and never includes an unrelated validated
declaration merely because it belongs to the same module or catalogue. -/
def selectRecords {sources} (records : List (BodyRecord sources)) :
    Nat → List DefId → List (BodyRecord sources) → WorkM (List (BodyRecord sources)) :=
  Nat.rec (fun pending selected => if pending.isEmpty then pure selected else throw .limit)
    (fun _ next pending selected => do
      exactWork (Exact.charge (16*(records.length+pending.length+selected.length+1)))
      match pending with
      | [] => pure selected
      | id :: rest =>
        if selected.any (·.id == id) then next rest selected else
          let some body := records.find? (·.id == id) | throw .request
          next (rest ++ bodyReferences body) (selected ++ [body]))

def Entry.relevanceFuel {sources catalogue owner name original}
    (_entry : @Entry sources catalogue owner name original) : Nat :=
  catalogue.records.length+(catalogue.records.map fun body => (bodyReferences body).length).sum+1

structure Projection {sources} (catalogue : RuntimeChecked sources) {owner name}
    (original : OrdinarySignature.Original sources owner name) where
  entry : Entry catalogue original
  records : List (BodyRecord sources)
  selected : ∃ before after,
    (selectRecords catalogue.records entry.relevanceFuel [entry.body.id] []).run before = (.ok records,after)

def project {sources owner name} (catalogue : RuntimeChecked sources)
    (original : OrdinarySignature.Original sources owner name) : WorkM (Projection catalogue original) := do
  let entry ← lookup catalogue original
  let records ← NaturalAffine.witness (selectRecords catalogue.records entry.relevanceFuel [entry.body.id] [])
  pure ⟨entry,records.val,by with_reducible exact records.property⟩

def Projection.inferredEffect {sources catalogue owner name original}
    (projection : @Projection sources catalogue owner name original) : Semantics.Raw.Effect :=
  projection.entry.inferred.inferredEffect

def Projection.quantumUse {sources catalogue owner name original}
    (projection : @Projection sources catalogue owner name original) : Bool := projection.entry.inferred.quantumUse

def Projection.sourceRows {sources catalogue owner name original}
    (projection : @Projection sources catalogue owner name original) : List (String × String) :=
  projection.records.flatMap fun body => body.definition.rows ++ body.outcome.rows

structure Checked (sources : Sources) extends RuntimeChecked sources where
  auxiliary : List (Auxiliary sources)
  auxiliaryRead : ∃ before after,
    ((auxiliaryIds modules).mapM (readAuxiliary sources helpers)).run before = (.ok auxiliary,after)
  meaningReferences : ∃ before after,
    ((auxiliary.flatMap (·.meanings) ++ records.flatMap bodyMeanings).forM
      (checkMeaningReferences toRuntimeChecked)).run before = (.ok (),after)

/-- All original declarations are audited before the caller may project a
selected body. Native gates must separately consume the retained concrete
Basis/Meaning/provider obligations, including dormant and unused occurrences. -/
def read (sources : Sources) : WorkM (Checked sources) := do
  guard (sources.size ≤ 128) .limit
  let bytes := (sources.toList.map fun row => row.1.utf8ByteSize+row.2.utf8ByteSize).sum
  guard (bytes ≤ 1048576) .limit
  let modules ← NaturalAffine.witness (sources.toList.mapM readModule)
  if moduleNames : modules.val.map (·.owner) = sources.toList.map (·.1) then
    if uniqueModules : (modules.val.map (·.owner)).eraseDups.length = modules.val.length then
      let originals ← NaturalAffine.witness (readOriginals sources modules.val)
      if originalsComplete : originals.val.map (fun original => (original.owner,original.name)) = runtimeIds modules.val then
        let helpers ← NaturalHelpers.read sources
        let records ← NaturalAffine.witness (readBodies sources helpers originals.val (runtimeIds modules.val))
        if identified : records.val.map (·.id) = runtimeIds modules.val then
          let cycles ← NaturalAffine.witness (checkCycles records.val)
          have cycleUnit : cycles.val = () := by cases cycles.val; rfl
          let all ← inferAll records.val records.val
          let runtime : RuntimeChecked sources :=
            ⟨modules.val,by with_reducible exact modules.property,moduleNames,uniqueModules,
              originals.val,by with_reducible exact originals.property,originalsComplete,helpers,records.val,
              by with_reducible exact records.property,identified,
              by with_reducible simpa only [cycleUnit] using cycles.property,all⟩
          let auxiliary ← NaturalAffine.witness ((auxiliaryIds modules.val).mapM (readAuxiliary sources helpers))
          let meaningReferences ← NaturalAffine.witness
            ((auxiliary.val.flatMap (·.meanings) ++ records.val.flatMap bodyMeanings).forM (checkMeaningReferences runtime))
          have meaningUnit : meaningReferences.val = () := by cases meaningReferences.val; rfl
          pure ⟨runtime,auxiliary.val,by with_reducible exact auxiliary.property,
            by with_reducible simpa only [meaningUnit] using meaningReferences.property⟩
        else throw .request
      else throw .request
    else throw .request
  else throw .request

/-- Provider eligibility may reuse an exact original record from the completed
catalogue. The fresh alternative remains available to component callers; both
retain the actual original body check and neither uses selected type values. -/
inductive Inference {sources owner name} (original : OrdinarySignature.Original sources owner name) where
  | fresh (checked : GenericTypeTrace.Checked original)
  | catalogued (catalogue : Checked sources) (projection : Projection catalogue.toRuntimeChecked original)

def Inference.inferredEffect {sources owner name original}
    (inference : @Inference sources owner name original) : Semantics.Raw.Effect := match inference with
  | .fresh checked => checked.inferredEffect
  | .catalogued _ projection => projection.inferredEffect

def Inference.quantumUse {sources owner name original}
    (inference : @Inference sources owner name original) : Bool := match inference with
  | .fresh checked => checked.quantumUse
  | .catalogued _ projection => projection.quantumUse

def Inference.sourceRows {sources owner name original}
    (inference : @Inference sources owner name original) : List (String × String) := match inference with
  | .fresh checked => checked.sourceRows
  | .catalogued _ projection => projection.sourceRows

def inferOriginal {sources owner name} (original : OrdinarySignature.Original sources owner name)
    (catalogue : Option (Checked sources) := none) : WorkM (Inference original) := do
  match catalogue with
  | none => pure (.fresh (← GenericTypeTrace.readOriginal original))
  | some catalogue => pure (.catalogued catalogue (← project catalogue.toRuntimeChecked original))

end QleisliKernel.SourceTypes.GenericCatalogue
