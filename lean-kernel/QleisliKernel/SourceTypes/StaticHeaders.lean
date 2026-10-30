import QleisliKernel.SourceTypes.OrdinarySignature

/-! Original static categories and ordered premises. Operation kinds retain
their untouched type/Meaning tokens; this parser alone does not check those
ports, instantiate providers, grant access or authorize runtime execution.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes.StaticHeaders

inductive Kind where
  | basis
  | natural
  | operation (tokens : List String)
  deriving BEq, DecidableEq, Repr

structure Formal where
  name : String
  ordinal : Nat
  kind : Kind
  deriving BEq, DecidableEq, Repr

inductive Access where
  | applicable
  | adjointable
  | controllable
  deriving BEq, DecidableEq, Repr

structure Parsed where
  formals : List Formal
  premises : List Semantics.SourceNatural.Predicate
  access : List (Access × String)

private structure Groups where
  stack : List String := []
  current : List String := []
  parts : List (List String) := []

private def group (angles : Bool) (state : Groups) (token : String) : Except String Groups := do
  -- The > in an operation arrow is not its enclosing angle delimiter.
  if angles && token == ">" && state.current.head? == some "-" then
    return {state with current := token :: state.current}
  if token == "(" || token == "[" || (angles && token == "<") then
    if state.stack.length ≥ 64 then throw "static header nesting capacity"
    let closing := if token == "(" then ")" else if token == "[" then "]" else ">"
    return {state with stack := closing :: state.stack,current := token :: state.current}
  if token == ")" || token == "]" || (angles && token == ">") then
    let expected :: rest := state.stack | throw "unmatched static header delimiter"
    if token != expected then throw "mismatched static header delimiter"
    return {state with stack := rest,current := token :: state.current}
  if token == "," && state.stack.isEmpty then
    if state.current.isEmpty then throw "empty static header member"
    return {state with current := [],parts := state.current.reverse :: state.parts}
  return {state with current := token :: state.current}

private def groups (angles : Bool) (tokens : List String) : Except String (List (List String)) := do
  let state ← tokens.foldlM (group angles) {}
  if !state.stack.isEmpty then throw "incomplete static header group"
  return (if state.current.isEmpty then state.parts else state.current.reverse :: state.parts).reverse

private def formals (header : OrdinarySignature.Header) : Except String (List Formal) := do
  let some tokens := header.staticTokens | return []
  if header.ordinaryOnly || tokens.isEmpty then throw "invalid static parameter clause"
  let parts ← groups true (tokens.map (·.text))
  if parts.length > 32 then throw "static formal capacity"
  parts.foldlM (fun parsed tokens => do
    let "const" :: name :: ":" :: tokens := tokens | throw "expected const static formal"
    if !identifier name || parsed.any (fun formal => formal.name == name) then
      throw "invalid or duplicate static formal"
    let kind ← match tokens with
      | ["Basis"] => pure Kind.basis
      | ["Nat"] => pure Kind.natural
      | "Op" :: "<" :: rest =>
        if rest.length < 2 || rest.getLast? != some ">" then throw "incomplete operation kind"
        pure (Kind.operation rest.dropLast)
      | _ => throw "unknown static kind"
    return parsed ++ [⟨name,parsed.length,kind⟩]) []

private def requirement (state : Parsed) (tokens : List String) : Except String Parsed := do
  let access ← match tokens with
    | ["Applicable","(",name,")"] => pure (some (Access.applicable,name))
    | ["Adjointable","(",name,")"] => pure (some (Access.adjointable,name))
    | ["Controllable","(",name,")"] => pure (some (Access.controllable,name))
    | _ => pure none
  if let some access := access then
    let [formal] := state.formals.filter (·.name == access.2) | throw "unknown access formal"
    let .operation _ := formal.kind | throw "access requires an operation formal"
    if state.access.contains access then throw "duplicate static access premise"
    return {state with access := state.access ++ [access]}
  return {state with premises := state.premises ++ [← NaturalHeaders.predicate tokens]}

def parse (header : OrdinarySignature.Header) : Except String Parsed := do
  let formals ← formals header
  let requirements ← match header.requiresTokens with
    | none => pure []
    | some tokens =>
      if tokens.isEmpty then throw "empty requires clause"
      groups false (tokens.map (·.text))
  if requirements.length > 64 then throw "static premise capacity"
  requirements.foldlM requirement ⟨formals,[],[]⟩

structure Original (sources : Sources) (owner name : String) where
  envelope : OrdinarySignature.Original sources owner name
  header : Parsed
  parsed : parse envelope.parsedHeader = .ok header

def read (sources : Sources) (owner name : String) : Finite.WorkM (Original sources owner name) := do
  let original ← OrdinarySignature.readOriginalEnvelope sources owner name
  Finite.exactWork (Exact.charge (32*original.occurrence.header.length^2+1))
  match parsed : parse original.parsedHeader with
  | .error _ => throw .request
  | .ok header => pure ⟨original,header,parsed⟩

/-- Original mixed-kind ordinals survive canonical name-first affine order. -/
def frame {sources owner name} (original : Original sources owner name) : NaturalFrames.Frame :=
  let binders := original.header.formals.filterMap fun formal =>
    if formal.kind == .natural then some (⟨⟨owner,name⟩,formal.ordinal,formal.name⟩ : NaturalFrames.Binder)
    else none
  ⟨binders.mergeSort (fun a b => a.name ≤ b.name)⟩

end QleisliKernel.SourceTypes.StaticHeaders
