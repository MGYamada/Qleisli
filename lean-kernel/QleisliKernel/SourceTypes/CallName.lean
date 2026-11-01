import QleisliKernel.SourceTypes.SourceLookup
import QleisliKernel.SourceTypes.ModuleHeader

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

def readName (tokens : List LocatedToken) : Except String (Name tokens) := do
  let segments := (tokens.map (·.text)).filter (· != "::")
  if nonempty : segments ≠ [] then
    if !allowed segments then throw "unsupported original call name"
    if original : segments.intersperse "::" = tokens.map (·.text) then
      return ⟨segments,nonempty,original⟩
    else throw "original call name is not an exact path"
  else throw "empty original call name"

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
prelude reexports. Only two primitive candidates are implemented below. -/
def primitiveSpelling (name : String) : Bool :=
  ["h","phase","global_phase_eighth","unit","finish","split","join",
    "measure_z","discard","take_bit","put_bit","empty_bits","prepend_bit"].contains name

inductive Primitive where
  | h | globalPhaseEighth
  deriving BEq, DecidableEq, Repr

def Primitive.name : Primitive → String
  | .h => "h"
  | .globalPhaseEighth => "global_phase_eighth"

private def primitive (name : String) : Except String Primitive :=
  if name == "h" then .ok .h
  else if name == "global_phase_eighth" then .ok .globalPhaseEighth
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

private def primitiveDecision {sources caller scope tokens name}
    (spelling : tokens = [name]) (unbound : name ∉ scope)
    (localMissing : Absent sources caller name) (policy : Policy localMissing.lookup.source)
    (preludeMissing : PreludeMiss sources name policy.disabled) :
    Finite.WorkM (Decision sources caller scope tokens) := do
  let candidate ← adapt (primitive name)
  if originalName : candidate.name = name then
    return .primitive name spelling unbound localMissing policy preludeMissing candidate originalName
  else throw .request

/-- Charge original bytes and names before lexing, catalogue scans or path
construction. There is no new expression-count cap. Existing lexing/source and
resolver limits remain in force; the budget is intentionally conservative. -/
def read (sources : Sources) (caller : String) (scope : List String)
    (tokens : List LocatedToken) : Finite.WorkM (Checked sources caller scope tokens) := do
  Finite.exactWork (Exact.charge (1 + caller.utf8ByteSize +
    (sources.toList.map fun row => row.1.utf8ByteSize + row.2.utf8ByteSize + 3).sum * 4 +
    (scope.map fun name => name.utf8ByteSize + 1).sum +
    (tokens.map fun token => token.text.utf8ByteSize + 4).sum * 4))
  let parsed ← adapt (readName tokens)
  let decision ← match single : parsed.segments with
    | [name] => do
      have spelling : tokens.map (·.text) = [name] := by
        simpa only [single,List.intersperse_singleton] using parsed.original.symm
      if bound : name ∈ scope then
        pure (.lexical name spelling bound)
      else
        let lookup ← adapt (SourceLookup.read sources caller name)
        match present : lookup.binding with
        | some _ =>
          pure (.named (← resolve sources caller (tokens.map (·.text))))
        | none =>
          let localMissing : Absent sources caller name := ⟨lookup,present⟩
          let policy ← adapt (readPolicy lookup.source)
          if disabled : policy.disabled = true then
            let miss : PreludeMiss sources name policy.disabled := disabled ▸ .disabled
            primitiveDecision spelling bound localMissing policy miss
          else
            have enabled : policy.disabled = false := by cases h : policy.disabled <;> simp_all
            let preludeLookup ← adapt (SourceLookup.read sources "std::prelude" name)
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
    | _ => pure (.named (← resolve sources caller (tokens.map (·.text))))
  return ⟨parsed,decision⟩

end QleisliKernel.SourceTypes.CallName
