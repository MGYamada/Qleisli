import QleisliKernel.SourceTypes.SourceLookup
import QleisliKernel.SourceTypes.ResolutionProvenance
import QleisliKernel.SourceTypes.ModuleHeader
import QleisliKernel.SourceTypes.SourceModules

/-! Original-call-name candidates, without standalone acceptance authority.
The supplied lexical scope must retain consumed bindings; authenticating that
scope and the exact caller token occurrence remains the caller's obligation.
Declaration catalogues are not full module validation. Candidate resolution
grants no typing, effect, interval, inverse/control or accepted-handle authority.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.CallName
open QleisliKernel QleisliKernel.SourceTypes

private def adapt {α : Type} (value : Except String α) : Finite.WorkM α :=
  Finite.lift (value.mapError fun _ => .request)

/-- Exact path spelling only: no application, static argument or opaque callee. -/
structure Name (tokens : List LocatedToken) where
  segments : List String
  nonempty : segments ≠ []
  original : segments.intersperse "::" = tokens.map (·.text)

private def allowed (segments : List String) : Bool :=
  segments.zipIdx.all fun (name,index) => identifier name ||
    (index == 1 && segments.head? == some "std" &&
      ["basis","observe","classical"].contains name)

structure TextName (tokens : List String) where
  segments : List String
  nonempty : segments ≠ []
  original : segments.intersperse "::" = tokens

def readTextName (tokens : List String) : Except String (TextName tokens) := do
  let segments := tokens.filter (· != "::")
  if nonempty : segments ≠ [] then
    if !allowed segments then throw "unsupported original call name"
    if original : segments.intersperse "::" = tokens then
      return ⟨segments,nonempty,original⟩
    else throw "original call name is not an exact path"
  else throw "empty original call name"

def readName (tokens : List LocatedToken) : Except String (Name tokens) := do
  let read ← readTextName (tokens.map (·.text))
  return ⟨read.segments,read.nonempty,read.original⟩

/-- Match the actual leading module header, ignoring only what lexLocated
itself discards. Later, repeated and malformed hash directives reject. -/
def policyTokens (tokens : List String) : Except String Bool :=
  ModuleHeader.policyTokens tokens

structure Policy (source : String) where
  tokens : List LocatedToken
  original : lexLocated source = .ok tokens
  disabled : Bool
  header : policyTokens (tokens.map (·.text)) = .ok disabled

def readPolicy (source : String) : Except String (Policy source) :=
  match original : lexLocated source with
  | .error error => .error error
  | .ok tokens =>
    match header : policyTokens (tokens.map (·.text)) with
    | .error error => .error error
    | .ok disabled => .ok ⟨tokens,original,disabled,header⟩

structure Resolution (sources : Sources) (caller : String) (tokens : List String) where
  result : Resolved
  work : Nat
  left : Nat
  executed : (resolveReference sources caller tokens).run work = (.ok result,left)

/-- Retain evidence from the one real resolver execution and its actual work
state; this neither substitutes a second lookup nor changes import depth. -/
private def resolveOriginal (sources : Sources) (caller : String) (tokens : List String) :
    Finite.WorkM (Resolution sources caller tokens) := fun work =>
  match executed : (resolveReference sources caller tokens).run work with
  | (.error error,left) => (.error error,left)
  | (.ok result,left) => (.ok ⟨result,work,left,executed⟩,left)

private def retired (owner name : String) : Bool :=
  owner == "std::quantum" ||
  (owner == "std::observe" && ["measure_z","discard","reset"].contains name) ||
  (owner == "std::registers" && ["take_bit","put_bit","empty","consume_empty"].contains name) ||
  (owner == "std::classical" && ["empty_bits","prepend_bit"].contains name)

/-- The existing generic declaration resolver has no retired call-path policy.
Apply that source-call rule to every qualified selection/import edge, preserving
unqualified local lookup even inside a module whose external path was retired. -/
def resolve (sources : Sources) (caller : String) (tokens : List String) :
    Finite.WorkM (Resolution sources caller tokens) := do
  let resolution ← resolveOriginal sources caller tokens
  Finite.exactWork (Exact.charge (1 + (resolution.result.visited.map fun entry =>
    entry.moduleName.utf8ByteSize + entry.declaration.name.utf8ByteSize + 1).sum))
  let selected := if tokens.length == 1 then resolution.result.visited.drop 1
    else resolution.result.visited
  Finite.guard (!(selected.any fun entry => retired entry.moduleName entry.declaration.name)) .request
  return resolution

theorem Resolution.originalQuery {sources caller tokens}
    (resolution : Resolution sources caller tokens) :
    Semantics.SourceResolution.Query sources caller tokens resolution.result.visited
        (ResolutionTrace.resolvedView resolution.result) ∧
      ResolutionTrace.OriginalLookups sources resolution.result.visited :=
  ResolutionTrace.resolveReference_retained_query _ _ _ _ _ _ resolution.executed

structure Absent (sources : Sources) (caller name : String) where
  lookup : SourceLookup.Checked sources caller name
  missing : lookup.binding = none

theorem Absent.original {sources caller name} (absence : Absent sources caller name) :
    originalBinding sources caller name = .error "missing/ambiguous original type declaration" :=
  absence.lookup.absent_original absence.missing

def exported (binding : Option Declaration) : Bool :=
  binding.any fun declaration => declaration.isPublic && declaration.kind == "import"

/-- The complete current primitive spelling set is used only to reject forbidden
 prelude reexports. Candidate lookup supplies no static-argument meaning. -/
def primitiveSpelling (name : String) : Bool :=
  ["h","phase","global_phase_eighth","unit","finish","split","join",
    "measure_z","discard","take_bit","put_bit","empty_bits","prepend_bit"].contains name

inductive Primitive where
  | h | globalPhaseEighth | phase | measureZ | discard | unit | finish | split | join
  | emptyBits | prependBit | takeBit | putBit
  deriving BEq, DecidableEq, Repr

def Primitive.name : Primitive → String
  | .h => "h"
  | .globalPhaseEighth => "global_phase_eighth"
  | .phase => "phase"
  | .measureZ => "measure_z" | .discard => "discard" | .unit => "unit"
  | .finish => "finish" | .split => "split" | .join => "join"
  | .emptyBits => "empty_bits" | .prependBit => "prepend_bit"
  | .takeBit => "take_bit" | .putBit => "put_bit"

private def primitive (name : String) : Except String Primitive :=
  if name == "h" then .ok .h
  else if name == "global_phase_eighth" then .ok .globalPhaseEighth
  else if name == "phase" then .ok .phase
  else if name == "measure_z" then .ok .measureZ
  else if name == "discard" then .ok .discard
  else if name == "unit" then .ok .unit
  else if name == "finish" then .ok .finish
  else if name == "split" then .ok .split
  else if name == "join" then .ok .join
  else if name == "empty_bits" then .ok .emptyBits
  else if name == "prepend_bit" then .ok .prependBit
  else if name == "take_bit" then .ok .takeBit
  else if name == "put_bit" then .ok .putBit
  else .error "not a supported unbound primitive candidate"

/-- Enabled lookup retains the exact canonical row even when no public export
exists. Local public declarations and private imports are not implicit exports. -/
inductive PreludeMiss (sources : Sources) (name : String) : Bool → Type where
  | disabled : PreludeMiss sources name true
  | enabled (lookup : SourceLookup.Checked sources "std::prelude" name)
      (missing : exported lookup.binding = false) : PreludeMiss sources name false

inductive Decision (sources : Sources) (caller : String) (scope : List String)
    (tokens : List String) where
  | lexical (name : String) (spelling : tokens = [name]) (bound : name ∈ scope)
  | named (resolution : Resolution sources caller tokens)
  | prelude (name : String) (spelling : tokens = [name]) (unbound : name ∉ scope)
      (localMissing : Absent sources caller name) (policy : Policy localMissing.lookup.source)
      (enabled : policy.disabled = false)
      (lookup : SourceLookup.Checked sources "std::prelude" name)
      (publicExport : exported lookup.binding = true)
      (resolution : Resolution sources caller ["std","::","prelude","::",name])
  | primitive (name : String) (spelling : tokens = [name]) (unbound : name ∉ scope)
      (localMissing : Absent sources caller name) (policy : Policy localMissing.lookup.source)
      (preludeMissing : PreludeMiss sources name policy.disabled)
      (candidate : Primitive) (originalName : candidate.name = name)

structure Checked (sources : Sources) (caller : String) (scope : List String)
    (tokens : List LocatedToken) where
  name : Name tokens
  decision : Decision sources caller scope (tokens.map (·.text))

def PreludeMiss.sourceRows {sources name} : {disabled : Bool} →
    PreludeMiss sources name disabled → List (String × String)
  | _,.disabled => []
  | _,.enabled lookup _ => [("std::prelude",lookup.source)]

/-- Complete original resolution dependencies, including caller/prelude scans
which establish absence. A named path and its reexports retain their original
visited order; a primitive spelling alone supplies no source relevance. -/
def sourceRows {sources caller scope tokens} (candidate : Checked sources caller scope tokens) :
    List (String × String) :=
  match candidate.decision with
  | .lexical .. => []
  | .named resolution => ResolutionProvenance.sourceRows resolution.result
  | .prelude _ _ _ localMissing _ _ lookup _ resolution =>
    (caller,localMissing.lookup.source) :: ("std::prelude",lookup.source) ::
      ResolutionProvenance.sourceRows resolution.result
  | .primitive _ _ _ localMissing _ preludeMissing _ _ =>
    (caller,localMissing.lookup.source) :: preludeMissing.sourceRows

def candidateResolution {sources caller scope tokens}
    (candidate : Checked sources caller scope tokens) : Option Resolved :=
  match candidate.decision with
  | .named resolution | .prelude _ _ _ _ _ _ _ _ resolution => some resolution.result
  | _ => none

private def primitiveDecision {sources caller scope tokens name}
    (spelling : tokens = [name]) (unbound : name ∉ scope)
    (localMissing : Absent sources caller name) (policy : Policy localMissing.lookup.source)
    (preludeMissing : PreludeMiss sources name policy.disabled) :
    Finite.WorkM (Decision sources caller scope tokens) := do
  let candidate ← adapt (primitive name)
  if originalName : candidate.name = name then
    return .primitive name spelling unbound localMissing policy preludeMissing candidate originalName
  else throw .request

private structure Lookup (sources : Sources) (owner name : String) where
  checked : SourceLookup.Checked sources owner name
  policy : Option (Policy checked.source)

private def readLookup (sources : Sources) (modules : Option (SourceModules.Prepared sources))
    (owner name : String) : Finite.WorkM (Lookup sources owner name) := do
  match modules with
  | none => pure ⟨← adapt (SourceLookup.read sources owner name),none⟩
  | some modules =>
    let original ← SourceModules.lookup modules owner
    Finite.exactWork (Exact.charge (4*((original.items.map fun item => item.name.utf8ByteSize+1).sum+
      name.utf8ByteSize+1)))
    let selected ← adapt (SourceLookup.select original.items name)
    let checked : SourceLookup.Checked sources owner name :=
      ⟨original.source,original.items,selected.binding,original.originalModule,original.originalItems,selected.matching⟩
    pure ⟨checked,some ⟨original.tokens,original.lexed,original.disabled,original.policy⟩⟩

/-- The fresh path charges full source bytes before scanning. A prepared path
instead charges its actual module/name matching; its exact scans and policy
are retained by the shared original-source preparation. Named/import paths
still execute the original resolver, including every visibility/import gate. -/
private def readTextsUsing (sources : Sources) (modules : Option (SourceModules.Prepared sources))
    (caller : String) (scope : List String)
    (tokens : List String) : Finite.WorkM (Decision sources caller scope tokens) := do
  Finite.exactWork (Exact.charge (1 + caller.utf8ByteSize +
    (if modules.isSome then 0 else
      (sources.toList.map fun row => row.1.utf8ByteSize + row.2.utf8ByteSize + 3).sum * 4) +
    (scope.map fun name => name.utf8ByteSize + 1).sum +
    (tokens.map fun token => token.utf8ByteSize + 4).sum * 4))
  let parsed ← adapt (readTextName tokens)
  let decision ← match single : parsed.segments with
    | [name] => do
      have spelling : tokens = [name] := by
        simpa only [single,List.intersperse_singleton] using parsed.original.symm
      if bound : name ∈ scope then
        pure (.lexical name spelling bound)
      else
        let localRead ← readLookup sources modules caller name
        let lookup := localRead.checked
        match present : lookup.binding with
        | some _ =>
          pure (.named (← resolve sources caller tokens))
        | none =>
          let localMissing : Absent sources caller name := ⟨lookup,present⟩
          let policy ← match localRead.policy with
            | some policy => pure policy
            | none => adapt (readPolicy lookup.source)
          if disabled : policy.disabled = true then
            let miss : PreludeMiss sources name policy.disabled := disabled ▸ .disabled
            primitiveDecision spelling bound localMissing policy miss
          else
            have enabled : policy.disabled = false := by cases h : policy.disabled <;> simp_all
            let preludeRead ← readLookup sources modules "std::prelude" name
            let preludeLookup := preludeRead.checked
            -- Rust's exports::prepare rejects primitive spellings in any
            -- public prelude reexport, even though local public fn is not an export.
            Finite.guard (!(preludeLookup.items.any fun item =>
              item.isPublic && item.kind == "import" && primitiveSpelling item.name)) .request
            if publicExport : exported preludeLookup.binding = true then
              let resolution ← resolve sources caller ["std","::","prelude","::",name]
              pure (.prelude name spelling bound localMissing policy enabled
                preludeLookup publicExport resolution)
            else
              have missing : exported preludeLookup.binding = false := by
                cases h : exported preludeLookup.binding <;> simp_all
              let miss : PreludeMiss sources name policy.disabled :=
                enabled ▸ .enabled preludeLookup missing
              primitiveDecision spelling bound localMissing policy miss
    | _ => pure (.named (← resolve sources caller tokens))
  return decision

def readTexts (sources : Sources) (caller : String) (scope : List String)
    (tokens : List String) : Finite.WorkM (Decision sources caller scope tokens) :=
  readTextsUsing sources none caller scope tokens

/-- Located source calls and original raw header paths use the same candidate
decision. Raw paths never receive synthetic source positions; their enclosing
original header/call reader retains the actual occurrence and byte witness. -/
def read (sources : Sources) (caller : String) (scope : List String)
    (tokens : List LocatedToken) : Finite.WorkM (Checked sources caller scope tokens) := do
  let decision ← readTexts sources caller scope (tokens.map (·.text))
  let parsed ← adapt (readName tokens)
  return ⟨parsed,decision⟩

/-- Same candidate semantics with one exact prepared module table. Lexical
shadowing remains the first lookup tier, before any module is selected. -/
def readWithModules (sources : Sources) (modules : Option (SourceModules.Prepared sources))
    (caller : String) (scope : List String) (tokens : List LocatedToken) :
    Finite.WorkM (Checked sources caller scope tokens) := do
  let decision ← readTextsUsing sources modules caller scope (tokens.map (·.text))
  let parsed ← adapt (readName tokens)
  pure ⟨parsed,decision⟩

end QleisliKernel.SourceTypes.CallName
