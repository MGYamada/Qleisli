import QleisliKernel.SourceTypes
import QleisliKernel.SourceTypes.LocatedFacts
import QleisliKernel.SourceTypes.ModuleHeader
import QleisliKernel.Semantics.Raw

/-! Original ordinary parameter/result headers. This component binds the
declared result/effect and complete original envelope; it does not establish
source-body preservation or authorize execution by itself.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.OrdinarySignature
open Semantics.FiniteCarrier Semantics.Raw Finite

inductive Selection where
  | project
  | exported
  | internal
  deriving BEq, DecidableEq, Repr

structure Header where
  effect : Option Effect
  ordinaryOnly : Bool
  parameterTypes : List (List String)
  resultTokens : List LocatedToken
  staticTokens : Option (List LocatedToken)
  requiresTokens : Option (List LocatedToken)

private def expect (text : String) (tokens : List LocatedToken) :
    Except String (LocatedToken × List LocatedToken) := do
  let token :: rest := tokens | throw "missing entry header token"
  if token.text != text then throw "unexpected entry header token"
  return (token,rest)

private def parameterClause : Nat → Nat → List LocatedToken → List LocatedToken →
    Except String (List LocatedToken × List LocatedToken) :=
  Nat.rec (fun _ _ _ => throw "incomplete parameter clause") (fun _ next depth tokens reversed => do
    let token :: rest := tokens | throw "missing parameter closing parenthesis"
    if token.text == ")" && depth == 0 then return (reversed.reverse,rest)
    if token.text == "(" then return ← next (depth+1) rest (token :: reversed)
    if token.text == ")" then return ← next (depth-1) rest (token :: reversed)
    next depth rest (token :: reversed))

-- Retain the exact original binder clause before interpreting its kinds or
-- substitutions. Angle brackets inside Op<A -> B> are not bracket delimiters.
private def staticClause : Nat → Nat → List LocatedToken → List LocatedToken →
    Except String (List LocatedToken × List LocatedToken) :=
  Nat.rec (fun _ _ _ => throw "incomplete static clause") (fun _ next depth tokens reversed => do
    let token :: rest := tokens | throw "missing static closing bracket"
    if token.text == "]" && depth == 0 then return (reversed.reverse,rest)
    if token.text == "[" then return ← next (depth+1) rest (token :: reversed)
    if token.text == "]" then return ← next (depth-1) rest (token :: reversed)
    next depth rest (token :: reversed))

private def parameterTypes (tokens : List LocatedToken) : Except String (List (List String)) := do
  let parts ← splitMembers (tokens.map (·.text))
  if parts.length > 64 then throw "parameter count exceeds existing bound"
  parts.mapM fun part => do
    let pattern := part.takeWhile (· != ":")
    let ":" :: ty := part.drop pattern.length | throw "missing parameter type"
    if pattern.isEmpty || ty.isEmpty then throw "empty parameter pattern or type"
    return ty

private def headerTokens (occurrence : BodyOccurrence) (declarationTokens : List LocatedToken) : Except String Header := do
  let tokens ← if occurrence.declaration.isPublic then do
      let (_,rest) ← expect "pub" declarationTokens
      pure rest
    else pure declarationTokens
  let (effect,ordinaryOnly,tokens) := match tokens with
    | effect :: rest => match effect.text with
      | "unitary" => (some Effect.unitary,false,rest)
      | "isometry" | "iso" => (some Effect.iso,false,rest)
      | "observe" => (some Effect.observe,false,rest)
      | "classical" => (some Effect.unitary,true,rest)
      | _ => (none,false,tokens)
    | [] => (none,false,[])
  let (_,tokens) ← expect "fn" tokens
  let (name,tokens) ← expect occurrence.declaration.name tokens
  if name != occurrence.nameToken then throw "entry name occurrence mismatch"
  let (statics,tokens) ← if tokens.head?.map (·.text) == some "[" then do
      let (clause,rest) ← staticClause (tokens.length+1) 0 tokens.tail []
      pure (some clause,rest)
    else pure (none,tokens)
  let (_,tokens) ← expect "(" tokens
  let (parameters,tokens) ← parameterClause (tokens.length+1) 0 tokens []
  let parameters ← parameterTypes parameters
  let (_,tokens) ← expect "-" tokens
  let (_,tokens) ← expect ">" tokens
  let (result,tail) := tokens.span (·.text != "requires")
  if result.isEmpty then throw "missing ordinary entry result"
  let requirements ← if tail.isEmpty then pure none else do
      if tail.tail.isEmpty then throw "empty entry requires clause"
      pure (some tail.tail)
  return ⟨effect,ordinaryOnly,parameters,result,statics,requirements⟩

private def header (source : String) (occurrence : BodyOccurrence) : Except String Header := do
  let projection ← ModuleHeader.project source occurrence.header
  headerTokens occurrence projection.tokens

def envelope (occurrence : BodyOccurrence) : List LocatedToken :=
  occurrence.header ++ [occurrence.openBrace] ++ occurrence.body ++ [occurrence.closeBrace]

structure Original (sources : Sources) (owner name : String) where
  source : String
  declaration : Declaration
  occurrence : BodyOccurrence
  parsedHeader : Header
  bound : originalBinding sources owner name = .ok (source,declaration)
  function : declaration.kind = "fn"
  catalogue : ∃ scanned, sourceCatalogue source = .ok scanned ∧ occurrence ∈ scanned.bodies
  sameDeclaration : occurrence.declaration = declaration
  parsed : header source occurrence = .ok parsedHeader
  bytes : LocatedFacts.OrderedSlices source.toUTF8 0 (envelope occurrence)

/-- Exact retained data identify the original read. The parsed header is
determined by its actual source/envelope computation; proof fields supply no
extra identity, and no source text or type clause is substituted. -/
theorem Original.sameEnvelope {sources owner name} (first second : Original sources owner name)
    (source : first.source = second.source) (declaration : first.declaration = second.declaration)
    (occurrence : first.occurrence = second.occurrence) : first = second := by
  cases first with
  | mk sourceA declarationA occurrenceA headerA boundA functionA catalogueA sameA parsedA bytesA =>
    cases second with
    | mk sourceB declarationB occurrenceB headerB boundB functionB catalogueB sameB parsedB bytesB =>
      cases source
      cases declaration
      cases occurrence
      have sameHeader : headerA = headerB := Except.ok.inj (parsedA.symm.trans parsedB)
      cases sameHeader
      rfl

/-- Shared original source data, not a producer header table. Canonical source
binding, actual lexer/declaration results and original UTF-8 bytes are retained
so each declaration need not lex the complete module again. -/
structure KnownModule (sources : Sources) (owner : String) where
  source : String
  bound : sources.toList.filter (fun row => row.1 == owner) = [(owner,source)]
  tokens : List LocatedToken
  lexed : lexLocated source = .ok tokens
  disabled : Bool
  policy : ModuleHeader.policyTokens (tokens.map (·.text)) = .ok disabled
  catalogue : SourceCatalogue
  scanned : sourceCatalogue source = .ok catalogue
  bytes : ByteArray
  originalBytes : bytes = source.toUTF8

private theorem knownBinding {sources owner} (known : KnownModule sources owner)
    (declaration : Declaration)
    (selected : known.catalogue.declarations.filter (fun decl => decl.name == declaration.name) = [declaration]) :
    originalBinding sources owner declaration.name = .ok (known.source,declaration) := by
  have readDeclarations : declarations known.source = .ok known.catalogue.declarations := by
    unfold declarations
    rw [known.scanned]
    rfl
  unfold originalBinding
  rw [known.bound]
  change (do
    let declarations : List Declaration ← SourceTypes.declarations known.source
    let [decl] := declarations.filter (fun (decl : Declaration) => decl.name == declaration.name)
      | throw "missing/ambiguous original type declaration"
    pure (known.source,decl)) = .ok (known.source,declaration)
  rw [readDeclarations]
  change (match known.catalogue.declarations.filter (fun decl => decl.name == declaration.name) with
    | [decl] => .ok (known.source,decl)
    | _ => .error "missing/ambiguous original type declaration") = .ok (known.source,declaration)
  rw [selected]

structure PackedOriginal (sources : Sources) where
  owner : String
  name : String
  original : Original sources owner name

abbrev Originals (sources : Sources) := List (PackedOriginal sources)

def readKnownOccurrence {sources owner} (known : KnownModule sources owner)
    (located : {occurrence : BodyOccurrence // occurrence ∈ known.catalogue.bodies}) :
    WorkM (PackedOriginal sources) := do
  let occurrence := located.val
  let declaration := occurrence.declaration
  let tokens := envelope occurrence
  exactWork (Exact.charge (64*((tokens.map fun token => token.text.utf8ByteSize+4).sum+1)+
    32*(occurrence.header.length+1)^2))
  if function : declaration.kind = "fn" then
    if selected : known.catalogue.declarations.filter (fun decl => decl.name == declaration.name) = [declaration] then
      if unique : known.catalogue.bodies.filter (·.declaration == declaration) = [occurrence] then
        match projected : ModuleHeader.projectKnown known.source occurrence.header known.tokens known.lexed known.disabled known.policy with
        | .error _ => throw .request
        | .ok projection =>
          match parsed : headerTokens occurrence projection.tokens with
          | .error _ => throw .request
          | .ok parsedHeader =>
            if bytes : LocatedFacts.checkOrdered known.bytes 0 tokens = true then
              have projectedOriginal : ModuleHeader.project known.source occurrence.header = .ok projection :=
                (ModuleHeader.project_known _ _ _ known.lexed _ known.policy).trans projected
              have parsedOriginal : header known.source occurrence = .ok parsedHeader := by
                unfold header
                rw [projectedOriginal]
                exact parsed
              have originalBytes : LocatedFacts.OrderedSlices known.source.toUTF8 0 (envelope occurrence) := by
                rw [← known.originalBytes]
                exact LocatedFacts.checkOrdered_sound _ _ _ bytes
              let original : Original sources owner declaration.name :=
                ⟨known.source,declaration,occurrence,parsedHeader,knownBinding known declaration selected,function,
                  ⟨known.catalogue,known.scanned,located.property⟩,rfl,parsedOriginal,originalBytes⟩
              pure ⟨owner,declaration.name,original⟩
            else throw .request
      else throw .request
    else throw .request
  else throw .request

def readKnownModule {sources owner} (known : KnownModule sources owner) : WorkM (Originals sources) :=
  (known.catalogue.bodies.attach.filter (fun occurrence => occurrence.val.declaration.kind == "fn")).mapM
    (readKnownOccurrence known)

def PackedOriginal.at {sources owner name} (packed : PackedOriginal sources)
    (sameOwner : packed.owner = owner) (sameName : packed.name = name) : Original sources owner name := by
  rcases packed with ⟨_,_,original⟩
  cases sameOwner
  cases sameName
  exact original

def lookupOriginals {sources} (originals : Originals sources) (owner name : String) :
    WorkM (Original sources owner name) := do
  exactWork (Exact.charge (16*((originals.map fun packed =>
    packed.owner.utf8ByteSize+packed.name.utf8ByteSize+1).sum+owner.utf8ByteSize+name.utf8ByteSize+1)))
  let some packed := originals.find? (fun packed => packed.owner == owner && packed.name == name) | throw .request
  if sameOwner : packed.owner = owner then
    if sameName : packed.name = name then pure (packed.at sameOwner sameName) else throw .request
  else throw .request

private def original (sources : Sources) (owner name : String) :
    Except String (Original sources owner name) := do
  match bound : originalBinding sources owner name with
  | .error message => throw message
  | .ok (source,declaration) =>
    if function : declaration.kind = "fn" then
      match scannedOk : sourceCatalogue source with
      | .error message => throw message
      | .ok scanned =>
        match selected : scanned.bodies.filter (·.declaration == declaration) with
        | [occurrence] =>
          have membership : occurrence ∈ scanned.bodies.filter (·.declaration == declaration) := by
            rw [selected]; exact List.mem_cons_self
          have found := (List.mem_filter.mp membership).1
          have sameDeclaration : occurrence.declaration = declaration :=
            beq_iff_eq.mp (List.mem_filter.mp membership).2
          match parsed : header source occurrence with
          | .error message => throw message
          | .ok parsedHeader =>
            if bytes : LocatedFacts.checkOrdered source.toUTF8 0 (envelope occurrence) = true then
              return ⟨source,declaration,occurrence,parsedHeader,bound,function,
                ⟨scanned,scannedOk,found⟩,sameDeclaration,parsed,
                LocatedFacts.checkOrdered_sound _ _ _ bytes⟩
            else throw "original entry byte envelope mismatch"
        | _ => throw "original entry body multiplicity"
    else throw "ordinary entry requires a runtime function"

private def adapt {α : Type} (value : Except String α) : WorkM α :=
  lift (value.mapError fun _ => .request)

/-- Read each original parameter's complete ordinary finite type. This does
not check parameter-pattern meaning or source-body preservation. -/
def inputTypesWithSources (sources : Sources) (owner : String) (tokens : List (List String)) :
    WorkM (List (TypeRead sources)) := do
  guard (tokens.length ≤ 64) .limit
  let inputs ← tokens.mapM fun ty => do
    let result ← typeExpressionWithSources sources owner ty
    let _ ← FiniteCarrier.read result.basis
    pure result
  guard ((inputs.map fun result => result.basis.length).sum ≤ 128) .limit
  return inputs

def inputTypes (sources : Sources) (owner : String) (tokens : List (List String)) :
    WorkM (List Basis) := do
  return (← inputTypesWithSources sources owner tokens).map (·.basis)

theorem inputTypesWithSources_value (sources : Sources) (owner : String)
    (tokens : List (List String)) (result : List (TypeRead sources)) (work left : Nat)
    (ok : (inputTypesWithSources sources owner tokens).run work = (.ok result,left)) :
    (inputTypes sources owner tokens).run work = (.ok (result.map (·.basis)),left) := by
  unfold inputTypes
  rw [Finite.bind_run,ok]
  rfl

structure Checked (sources : Sources) (owner name : String) where
  original : Original sources owner name
  parameterReads : List (TypeRead sources)
  result : TypeRead sources
  inputsRead : ∃ before after,
    (inputTypesWithSources sources owner original.parsedHeader.parameterTypes).run before =
      (.ok parameterReads,after)
  resultRead : ∃ before after,
    (typeExpressionWithSources sources owner (original.parsedHeader.resultTokens.map (·.text))).run before =
      (.ok result,after)

def Checked.inputs {sources owner name} (checked : Checked sources owner name) : List Basis :=
  checked.parameterReads.map (·.basis)

def Checked.basis {sources owner name} (checked : Checked sources owner name) : Basis :=
  checked.result.basis

/-- Only queries actually made by the selected original signature and recursive
record fields contribute rows. Global unused-helper validation contributes none. -/
def Checked.sourceRows {sources owner name} (checked : Checked sources owner name) :
    List (String × String) :=
  checked.parameterReads.flatMap TypeRead.sourceRows ++ checked.result.sourceRows

def selectionAllowed {sources : Sources} {owner name : String}
    (selection : Selection) (original : Original sources owner name) : Bool :=
  match selection with
  | .project => owner == "main" && name == "main" && !original.parsedHeader.ordinaryOnly &&
      original.parsedHeader.parameterTypes.isEmpty
  | .exported => original.declaration.isPublic
  | .internal => !original.declaration.isPublic && !(owner == "main" && name == "main")

/-- Exact original declaration, including untouched static binders and requires
tokens. Reading this envelope checks neither their substitution nor constraints
and grants no visibility, operation access or execution authority. -/
def readOriginalEnvelope (sources : Sources) (owner name : String) :
    WorkM (Original sources owner name) := do
  guard (sources.size ≤ 128) .limit
  let bytes := (sources.toList.map fun row => row.1.utf8ByteSize + row.2.utf8ByteSize).sum
  guard (bytes ≤ 1048576) .limit
  exactWork (Exact.charge (512*(bytes+1)+owner.utf8ByteSize+name.utf8ByteSize+1))
  adapt (original sources owner name)

/-- The existing closed-header consumers retain their explicit refusal of
static binders/constraints. Only an independent substitution checker may use
readOriginalEnvelope to extend those consumers. -/
def readOriginal (sources : Sources) (owner name : String) :
    WorkM (Original sources owner name) := do
  let original ← readOriginalEnvelope sources owner name
  guard (original.parsedHeader.staticTokens.isNone && original.parsedHeader.requiresTokens.isNone) .request
  pure original

/-- Project main remains closed. Exported declarations may have ordinary
parameters. Quantum/static binders and general source semantics remain separate. -/
def read (sources : Sources) (selection : Selection) (owner name : String) :
    WorkM (Checked sources owner name) := do
  let original ← readOriginal sources owner name
  guard (selectionAllowed selection original) .request
  let inputs ← NaturalAffine.witness (inputTypesWithSources sources owner original.parsedHeader.parameterTypes)
  let basis ← NaturalAffine.witness
    (typeExpressionWithSources sources owner (original.parsedHeader.resultTokens.map (·.text)))
  let _ ← FiniteCarrier.read basis.val.basis
  return ⟨original,inputs.val,basis.val,by with_reducible exact inputs.property,
    by with_reducible exact basis.property⟩

theorem read_selection (sources : Sources) (selection : Selection) (owner name : String)
    (checked : Checked sources owner name) (work left : Nat)
    (ok : (read sources selection owner name).run work = (.ok checked,left)) :
    selectionAllowed selection checked.original = true := by
  unfold read at ok
  obtain ⟨original,d,_,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,e,allowed,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨inputs,f,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨basis,g,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,j,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨rfl,rfl⟩ := pure_success _ _ _ _ h
  exact (guard_success _ _ _ _ allowed).1

theorem Checked.bound {sources owner name} (checked : Checked sources owner name) :
    originalBinding sources owner name = .ok (checked.original.source,checked.original.declaration) :=
  checked.original.bound

theorem Checked.byte_envelope {sources owner name} (checked : Checked sources owner name) :
    LocatedFacts.OrderedSlices checked.original.source.toUTF8 0 (envelope checked.original.occurrence) :=
  checked.original.bytes

theorem Checked.parameter_types {sources owner name} (checked : Checked sources owner name) :
    ∃ before after,
      (inputTypes sources owner checked.original.parsedHeader.parameterTypes).run before =
        (.ok checked.inputs,after) := by
  obtain ⟨before,after,ran⟩ := checked.inputsRead
  exact ⟨before,after,inputTypesWithSources_value _ _ _ _ before after ran⟩

theorem Checked.result_type {sources owner name} (checked : Checked sources owner name) :
    ∃ before after,
      (typeExpression sources owner (checked.original.parsedHeader.resultTokens.map (·.text))).run before =
        (.ok checked.basis,after) := by
  obtain ⟨before,after,ran⟩ := checked.resultRead
  exact ⟨before,after,typeExpressionWithSources_value _ _ _ _ before after ran⟩

end QleisliKernel.SourceTypes.OrdinarySignature
