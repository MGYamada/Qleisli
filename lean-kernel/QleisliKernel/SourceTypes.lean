import QleisliKernel.SourceTypes.Declarations
import QleisliKernel.SourceTypes.ResolutionProvenance
import QleisliKernel.SourceTypes.NaturalSyntax
import QleisliKernel.SourceTypes.NaturalAffine
import QleisliKernel.SourceTypes.NaturalConstraints
import QleisliKernel.SourceTypes.NaturalPredicates
import QleisliKernel.SourceTypes.NaturalHeaders
import QleisliKernel.SourceTypes.NaturalCatalog
import QleisliKernel.SourceTypes.NaturalNormalize
import QleisliKernel.SourceTypes.NaturalFrames
import QleisliKernel.SourceTypes.NaturalSubstitute
import QleisliKernel.SourceTypes.NaturalPrepare
import QleisliKernel.SourceTypes.NaturalHelpers
import QleisliKernel.FiniteCarrier

/-! Reconstruct a nominal carrier from original top-level source declarations.
The independent reader preserves canonical declarations through explicit imports
and public reexports. Existing field Nat expressions use original checked helpers
and exact symbolic arithmetic. It grants no source-function preservation guarantee.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypes
open Semantics.FiniteCarrier

private structure Parts where
  stack : List String := []
  current : List String := []
  parts : List (List String) := []

private def part (s : Parts) (token : String) : Except String Parts := do
  if token == "(" || token == "<" || token == "[" then
    return {s with stack := (if token == "(" then ")" else if token == "[" then "]" else ">") :: s.stack,current := token :: s.current}
  if token == ")" || token == ">" || token == "]" then
    let expected :: rest := s.stack | throw "unmatched type delimiter"
    if token != expected then throw "mismatched type delimiter"
    return {s with stack := rest,current := token :: s.current}
  if token == "," && s.stack.isEmpty then
    if s.current.isEmpty then throw "empty member"
    return {s with current := [],parts := s.current.reverse :: s.parts}
  return {s with current := token :: s.current}

def splitMembers (tokens : List String) : Except String (List (List String)) := do
  let s ← tokens.foldlM part {}
  if !s.stack.isEmpty then throw "incomplete member type"
  return (if s.current.isEmpty then s.parts else s.current.reverse :: s.parts).reverse

/-- Origin lookup is canonical: an alias never becomes a new declaration. -/
def lookup (sources : Sources) (moduleName name : String) : Except String (String × Declaration) := do
  let (source,decl) ← originalBinding sources moduleName name
  if decl.kind != "enum" && decl.kind != "struct" then throw "source name is not a finite type"
  return (source,decl)

private def adapt {α : Type} (value : Except String α) : Finite.WorkM α :=
  Finite.lift (value.mapError fun _ => .request)

private theorem adapt_value {α : Type} (value : Except String α) (result : α) (work left : Nat)
    (ok : (adapt value).run work = (.ok result,left)) : value = .ok result := by
  have bound := (Finite.lift_success _ _ _ _ ok).1
  cases value <;> simp_all [Except.mapError]

private def load (sources : Sources) (moduleName name : String) : Finite.WorkM (String × Declaration) := do
  Finite.exactWork (Exact.charge ((sources.toList.map fun row =>
    row.1.utf8ByteSize + row.2.utf8ByteSize).sum + name.utf8ByteSize + moduleName.utf8ByteSize + 1))
  adapt (lookup sources moduleName name)

/-- One query made while reading an original type, with the actual resolver run.
The enclosing type-read witness supplies its source-occurrence context. -/
structure TypeResolution (sources : Sources) where
  owner : String
  tokens : List String
  result : Resolved
  read : ∃ before after,
    (ResolutionProvenance.read sources owner tokens).run before = (.ok result,after)

theorem TypeResolution.query {sources : Sources} (resolution : TypeResolution sources) :
    Semantics.SourceResolution.Query sources resolution.owner resolution.tokens
      resolution.result.visited (ResolutionTrace.resolvedView resolution.result) ∧
      ResolutionTrace.OriginalLookups sources resolution.result.visited := by
  obtain ⟨before,after,ran⟩ := resolution.read
  exact ResolutionProvenance.read_query sources _ _ _ before after ran

/-- Basis and provenance from the same shared executable type reader. Reading
all unused Nat helpers validates them but contributes no dependency coverage. -/
structure TypeRead (sources : Sources) where
  basis : Basis
  resolutions : List (TypeResolution sources) := []

def TypeRead.sourceRows {sources : Sources} (result : TypeRead sources) : List (String × String) :=
  result.resolutions.flatMap fun resolution => ResolutionProvenance.sourceRows resolution.result

/-- Each retained row comes from an original lookup on one of the actual type
queries. The enclosing read witness ties those queries to the source type. -/
theorem TypeRead.original_rows {sources : Sources} (result : TypeRead sources)
    (row : String × String) (member : row ∈ result.sourceRows) :
    ∃ resolution ∈ result.resolutions, ∃ entry ∈ resolution.result.visited,
      row = (entry.moduleName,entry.source) ∧
      originalBinding sources entry.moduleName entry.declaration.name =
        .ok (entry.source,entry.declaration) := by
  obtain ⟨resolution,present,found⟩ := List.mem_flatMap.mp member
  obtain ⟨before,after,ran⟩ := resolution.read
  obtain ⟨entry,visited,same,bound⟩ :=
    ResolutionProvenance.read_original_rows sources _ _ _ before after ran row found
  exact ⟨resolution,present,entry,visited,same,bound⟩

private def combine {sources : Sources} (first second : TypeRead sources) :
    Finite.WorkM (TypeRead sources) := do
  Finite.guard (first.basis.length + second.basis.length ≤ 128 &&
    first.resolutions.length + second.resolutions.length ≤ 128) .limit
  Finite.exactWork (Exact.charge (first.basis.length+first.resolutions.length+1))
  pure ⟨first.basis ++ second.basis,first.resolutions ++ second.resolutions⟩

/-- Canonical decimal reading for the existing zero-to-six width profile.
The common grammar permits a leading zero only for the literal `0`. Bound every
prefix before extending it; introduce no general Nat-expression or const form. -/
def literalWidth (literal : String) : Finite.WorkM Nat := do
  Finite.guard (!literal.isEmpty) .request
  Finite.exactWork (Exact.charge (literal.utf8ByteSize + 1))
  let chars := literal.toList
  Finite.guard (chars == ['0'] || chars.head? != some '0') .request
  chars.foldlM (fun value char => do
    Finite.guard ('0' ≤ char && char ≤ '9') .request
    let width := value * 10 + (char.toNat - '0'.toNat)
    Finite.guard (width ≤ 6) .limit
    pure width) 0

private structure Readers where
  ty : (sources : Sources) → String → List String → Finite.WorkM (TypeRead sources)
  decl : (sources : Sources) → String → String → Finite.WorkM (TypeRead sources)

private structure WidthExpression (sources : Sources) (helpers : List NaturalHelpers.Entry)
    (moduleName : String) (tokens : List String) where
  expression : Semantics.SourceNatural.Expr
  bindings : List (Semantics.SourceNatural.Path × NaturalCatalog.Key)
  parsed : NaturalSyntax.read tokens = .ok expression
  resolved : ∃ work left,
    (NaturalCatalog.expressionBindings sources (helpers.map (·.original)) moduleName expression).run work = (.ok bindings,left)

private def widthExpression (sources : Sources) (helpers : List NaturalHelpers.Entry)
    (moduleName : String) (tokens : List String) :
    Finite.WorkM (WidthExpression sources helpers moduleName tokens) := do
  Finite.exactWork (Exact.charge ((tokens.map String.utf8ByteSize).sum+tokens.length+1))
  let parsedValue ← NaturalAffine.witness (adapt (NaturalSyntax.read tokens))
  have parsed : NaturalSyntax.read tokens = .ok parsedValue.val := by
    obtain ⟨work,left,ok⟩ := parsedValue.property
    exact adapt_value _ _ _ _ ok
  let bound ← NaturalAffine.witness (NaturalCatalog.expressionBindings sources (helpers.map (·.original)) moduleName parsedValue.val)
  return ({expression := parsedValue.val,bindings := bound.val,parsed := parsed,
           resolved := by with_reducible exact bound.property} : WidthExpression sources helpers moduleName tokens)

private structure CheckedWidth (sources : Sources) (helpers : List NaturalHelpers.Entry)
    (moduleName : String) (tokens : List String) where
  original : WidthExpression sources helpers moduleName tokens
  value : Nat
  meaning : Semantics.SourceNatural.Value (NaturalFrames.names ⟨[]⟩ (fun _ => 0))
    (NaturalHelpers.interpretation helpers original.bindings) original.expression value

private def naturalWidth (sources : Sources) (helpers : List NaturalHelpers.Entry)
    (moduleName : String) (tokens : List String) :
    Finite.WorkM (CheckedWidth sources helpers moduleName tokens) := do
  let original ← widthExpression sources helpers moduleName tokens
  let frame : NaturalFrames.Frame := ⟨[]⟩
  let calls := NaturalHelpers.interpretation helpers original.bindings
  let context ← NaturalFrames.initial frame
  let result ← NaturalNormalize.normalize 0 context
    ⟨NaturalFrames.readName frame calls (fun _ held => held),
      (NaturalHelpers.reader frame helpers original.bindings).read context (fun _ held => held)⟩ 128 original.expression
  if shape : result.form.coefficients = [] then
    if bounds : 0 ≤ result.form.constant ∧ result.form.constant ≤ 4294967295 then
      let width := result.form.constant.toNat
      Finite.guard (width ≤ 6) .limit
      return ⟨original,width,by
        obtain ⟨n,computed,same⟩ := result.correct (fun _ => 0) (by intro _ _; exact Int.le_refl 0)
        have integer : result.form.constant = (n : Int) := by
          simpa only [Semantics.SourceAffine.Form.evaluate,shape,Semantics.SourceAffine.dot_nil,Int.add_zero] using same
        have equal : width = n := by omega
        rw [equal]
        exact Semantics.SourceNatural.evaluate_value _ _ _ _ _ computed⟩
    else throw .limit
  else throw .request

private def readers (helpers : List NaturalHelpers.Entry) : Nat → Readers :=
  Nat.rec ⟨fun _ _ _ => throw .limit,fun _ _ _ => throw .limit⟩
    (fun _ recurse => ⟨fun sources current tokens => do
      match tokens with
      | ["Unit"] => return ⟨[.unit],[]⟩
      | ["Bit"] => return ⟨[.bit],[]⟩
      | "Bits" :: "<" :: rest =>
        Finite.guard (rest.getLast? == some ">") .request
        return ⟨[.bits (← naturalWidth sources helpers current rest.dropLast).value],[]⟩
      | "(" :: rest =>
        if rest.getLast? != some ")" || rest.dropLast.getLast? == some "," then
          throw .request
        let parts ← adapt (splitMembers rest.dropLast)
        Finite.guard (2 ≤ parts.length && parts.length ≤ 64) .limit
        let children ← parts.foldlM (fun acc part => do combine acc (← recurse.ty sources current part)) ⟨[],[]⟩
        combine ⟨[if parts.length == 2 then Atom.pair else .tuple parts.length],[]⟩ children
      | _ =>
        let original ← NaturalAffine.witness (ResolutionProvenance.read sources current tokens)
        let result ← recurse.decl sources original.val.moduleName original.val.declaration.name
        Finite.guard (result.resolutions.length < 128) .limit
        Finite.exactWork (Exact.charge (tokens.length+current.utf8ByteSize+2))
        let resolution : TypeResolution sources :=
          ⟨current,tokens,original.val,by with_reducible exact original.property⟩
        return {result with resolutions := resolution :: result.resolutions},
      fun sources moduleName name => do
        let (source,decl) ← load sources moduleName name
        let origin : Origin := ⟨moduleName,name,source⟩
        let members ← adapt (splitMembers decl.body)
        Finite.guard (members.length ≤ 64) .limit
        if decl.kind == "enum" then
          let names ← members.mapM fun tokens => do
            let [name] := tokens | throw .request
            Finite.guard (identifier name) .request
            return name
          Finite.guard (!names.isEmpty && FiniteCarrier.namesValid names) .request
          return ⟨[.enumeration origin names],[]⟩
        let (names,children) ← members.foldlM (fun (names,children) tokens => do
          let tokens := if tokens.head? == some "pub" then tokens.drop 1 else tokens
          let field :: ":" :: ty := tokens | throw .request
          Finite.guard (identifier field) .request
          return (names ++ [field],← combine children (← recurse.ty sources moduleName ty))) ([],⟨[],[]⟩)
        Finite.guard (FiniteCarrier.namesValid names) .request
        combine ⟨[.record origin names],[]⟩ children⟩)

/-- Reconstruct from actual source, never by finding a matching producer row.
The existing carrier reader separately bounds the complete tree/code. -/
private def readNominal (helpers : List NaturalHelpers.Entry) (sources : Sources)
    (origin : Origin) (nodes : Nat) : Finite.WorkM Basis := do
  let (source,_) ← load sources origin.moduleName origin.declarationName
  Finite.exactWork (Exact.charge (origin.source.utf8ByteSize + 1))
  Finite.guard (source == origin.source) .request
  -- A matching subtree cannot contain more nodes than the supplied complete
  -- tree. Two reader steps per node suffice; the existing depth ceiling remains.
  return (← (readers helpers (min 65 (2*nodes+1))).decl
    sources origin.moduleName origin.declarationName).basis

def nominal (sources : Sources) (origin : Origin) (nodes : Nat := 128) : Finite.WorkM Basis := do
  readNominal (← NaturalHelpers.prepare sources) sources origin nodes

private def checkAtom (helpers : List NaturalHelpers.Entry) (sources : Sources) (nodes : Nat) (remaining : Basis) (atom : Atom) :
    Finite.WorkM Basis := do
  match atom with
  | .enumeration origin _ | .record origin _ =>
    let original ← readNominal helpers sources origin nodes
    Finite.guard (remaining.take original.length == original) .request
  | _ => pure ()
  pure (remaining.drop 1)

/-- Compare every nominal subtree to its independently reconstructed source
tree. Prefix validation occurs first, so a neighbour cannot supply missing nodes. -/
private def sourceHelpers (sources : Sources) : Finite.WorkM (List NaturalHelpers.Entry) := do
  Finite.guard (sources.size ≤ 128 && (sources.toList.map fun row =>
    row.1.utf8ByteSize + row.2.utf8ByteSize).sum ≤ 1048576) .limit
  NaturalHelpers.prepare sources

private def checkBasis (helpers : List NaturalHelpers.Entry) (sources : Sources) (basis : Basis) : Finite.WorkM Unit := do
  let _ ← FiniteCarrier.read basis
  let _ ← basis.foldlM (checkAtom helpers sources basis.length) basis
  pure ()

def check (sources : Sources) (basis : Basis) : Finite.WorkM Unit := do
  checkBasis (← sourceHelpers sources) sources basis

/-- Validate one original helper environment for every ordered owner forest.
No caller-supplied checked template can enter this public source boundary. -/
def checkMany (sources : Sources) (forests : List Basis) : Finite.WorkM Unit := do
  let helpers ← sourceHelpers sources
  forests.forM (checkBasis helpers sources)

private theorem load_value (sources : Sources) (moduleName name : String)
    (result : String × Declaration) (work left : Nat)
    (ok : (load sources moduleName name).run work = (.ok result,left)) :
    lookup sources moduleName name = .ok result := by
  obtain ⟨_,middle,_,bound⟩ := Finite.bind_success _ _ _ _ _ ok
  exact adapt_value _ _ _ _ bound

/-- Success names the original module/declaration lookup and exact source
bytes. It does not assert that the function body has its source meaning. -/
private theorem readNominal_original (helpers : List NaturalHelpers.Entry) (sources : Sources) (origin : Origin) (nodes : Nat)
    (result : Basis) (work left : Nat)
    (ok : (readNominal helpers sources origin nodes).run work = (.ok result,left)) :
    ∃ decl, lookup sources origin.moduleName origin.declarationName = .ok (origin.source,decl) := by
  obtain ⟨entry,a,loaded,h⟩ := Finite.bind_success _ _ _ _ _ ok
  obtain ⟨_,b,_,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨_,c,same,_⟩ := Finite.bind_success _ _ _ _ _ h
  have equal := beq_iff_eq.mp (Finite.guard_success _ _ _ _ same).1
  refine ⟨entry.2,?_⟩
  have sameEntry : (origin.source,entry.2) = entry := by
    apply Prod.ext
    · exact equal.symm
    · rfl
  rw [sameEntry]
  exact load_value _ _ _ _ _ _ loaded

theorem nominal_original (sources : Sources) (origin : Origin) (nodes : Nat)
    (result : Basis) (work left : Nat)
    (ok : (nominal sources origin nodes).run work = (.ok result,left)) :
    ∃ decl, lookup sources origin.moduleName origin.declarationName = .ok (origin.source,decl) := by
  obtain ⟨helpers,middle,_,read⟩ := Finite.bind_success _ _ _ _ _ ok
  exact readNominal_original helpers _ _ _ _ _ _ read

/-- Literal source-declaration identity only, not source-function correctness. -/
def OriginalDeclaration (sources : Sources) : Atom → Prop
  | .enumeration origin _ | .record origin _ =>
    ∃ decl, lookup sources origin.moduleName origin.declarationName = .ok (origin.source,decl)
  | _ => True

private theorem checkAtom_original (helpers : List NaturalHelpers.Entry) (sources : Sources) (nodes : Nat) (remaining : Basis)
    (atom : Atom) (result : Basis) (work left : Nat)
    (ok : (checkAtom helpers sources nodes remaining atom).run work = (.ok result,left)) :
    OriginalDeclaration sources atom := by
  cases atom <;> try trivial
  all_goals
    obtain ⟨original,after,read,_⟩ := Finite.bind_success _ _ _ _ _ ok
    exact readNominal_original helpers _ _ _ _ _ _ read

private theorem fold_original (helpers : List NaturalHelpers.Entry) (sources : Sources) (nodes : Nat) (atoms remaining result : Basis)
    (work left : Nat)
    (ok : (atoms.foldlM (checkAtom helpers sources nodes) remaining).run work = (.ok result,left)) :
    ∀ atom ∈ atoms, OriginalDeclaration sources atom := by
  induction atoms generalizing remaining work with
  | nil => simp
  | cons first rest ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨next,after,head,tail⟩ := Finite.bind_success _ _ _ _ _ ok
    intro atom member
    rcases List.mem_cons.mp member with same | member
    · subst atom
      exact checkAtom_original helpers _ _ _ _ _ _ _ head
    · exact ih next after tail atom member

theorem check_original_declarations (sources : Sources) (basis : Basis) (work left : Nat)
    (ok : (check sources basis).run work = (.ok (),left)) :
    ∀ atom ∈ basis, OriginalDeclaration sources atom := by
  obtain ⟨_,a,_,h⟩ := Finite.bind_success _ _ _ _ _ ok
  unfold checkBasis at h
  obtain ⟨_,b,_,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨remaining,c,fold,_⟩ := Finite.bind_success _ _ _ _ _ h
  exact fold_original _ sources basis.length basis basis remaining b c fold


/-- Read a complete original member type with the existing type grammar and
original helper environment. The caller must separately establish the origin
of these tokens; this function grants neither member access nor acceptance. -/
def typeExpressionWithSources (sources : Sources) (moduleName : String) (tokens : List String) :
    Finite.WorkM (TypeRead sources) := do
  let helpers ← sourceHelpers sources
  (readers helpers 65).ty sources moduleName tokens

/-- Endpoint compatibility for existing carrier/member consumers. Both views
use exactly the same reader; no second type resolver supplies coverage. -/
def typeExpression (sources : Sources) (moduleName : String) (tokens : List String) :
    Finite.WorkM Basis := do
  return (← typeExpressionWithSources sources moduleName tokens).basis

theorem typeExpressionWithSources_value (sources : Sources) (moduleName : String)
    (tokens : List String) (result : TypeRead sources) (work left : Nat)
    (ok : (typeExpressionWithSources sources moduleName tokens).run work = (.ok result,left)) :
    (typeExpression sources moduleName tokens).run work = (.ok result.basis,left) := by
  unfold typeExpression
  rw [Finite.bind_run,ok]
  rfl

/-- A checked field width denotes the actual original Nat expression, under
bindings read from its declaring module and an actually prepared original
helper environment. The value relation is the existing independent semantics;
preparation and name lookup are separately explicit provenance facts. -/
def NaturalWidthMeaning (sources : Sources) (moduleName : String)
    (tokens : List String) (width : Nat) : Prop :=
  ∃ helpers expression bindings,
    (∃ work left, (NaturalHelpers.prepare sources).run work = (.ok helpers,left)) ∧
    NaturalSyntax.read tokens = .ok expression ∧
    (∃ work left, (NaturalCatalog.expressionBindings sources
      (helpers.map (·.original)) moduleName expression).run work = (.ok bindings,left)) ∧
    Semantics.SourceNatural.Value (NaturalFrames.names ⟨[]⟩ (fun _ => 0))
      (NaturalHelpers.interpretation helpers bindings) expression width

private theorem sourceHelpers_prepared (sources : Sources)
    (helpers : List NaturalHelpers.Entry) (work left : Nat)
    (ok : (sourceHelpers sources).run work = (.ok helpers,left)) :
    ∃ before, (NaturalHelpers.prepare sources).run before = (.ok helpers,left) := by
  obtain ⟨_,before,_,prepared⟩ := Finite.bind_success _ _ _ _ _ ok
  exact ⟨before,prepared⟩

theorem typeExpression_unit (sources : Sources) (moduleName : String)
    (result : Basis) (work left : Nat)
    (ok : (typeExpression sources moduleName ["Unit"]).run work = (.ok result,left)) :
    result = [.unit] := by
  obtain ⟨read,a,ran,h⟩ := Finite.bind_success _ _ _ _ _ ok
  have projected := (Finite.pure_success _ _ _ _ h).1
  obtain ⟨helpers,middle,_,body⟩ := Finite.bind_success _ _ _ _ _ ran
  change (pure ⟨[.unit],[]⟩ : Finite.WorkM (TypeRead sources)).run middle = (.ok read,a) at body
  have same := (Finite.pure_success _ _ _ _ body).1
  simpa only [same] using projected

theorem typeExpression_bit (sources : Sources) (moduleName : String)
    (result : Basis) (work left : Nat)
    (ok : (typeExpression sources moduleName ["Bit"]).run work = (.ok result,left)) :
    result = [.bit] := by
  obtain ⟨read,a,ran,h⟩ := Finite.bind_success _ _ _ _ _ ok
  have projected := (Finite.pure_success _ _ _ _ h).1
  obtain ⟨helpers,middle,_,body⟩ := Finite.bind_success _ _ _ _ _ ran
  change (pure ⟨[.bit],[]⟩ : Finite.WorkM (TypeRead sources)).run middle = (.ok read,a) at body
  have same := (Finite.pure_success _ _ _ _ body).1
  simpa only [same] using projected

/-- The Bits leaf is not inferred from a machine width or producer tree.
Its exact source Nat expression has the existing independent value semantics. -/
theorem typeExpression_bits (sources : Sources) (moduleName : String)
    (rest : List String) (result : Basis) (work left : Nat)
    (ok : (typeExpression sources moduleName ("Bits" :: "<" :: rest)).run work =
      (.ok result,left)) :
    ∃ width, result = [.bits width] ∧ rest.getLast? = some ">" ∧
      NaturalWidthMeaning sources moduleName rest.dropLast width := by
  obtain ⟨read,endRead,ran,projected⟩ := Finite.bind_success _ _ _ _ _ ok
  have projected := (Finite.pure_success _ _ _ _ projected).1
  obtain ⟨helpers,middle,prepared,body⟩ := Finite.bind_success _ _ _ _ _ ran
  change ((do
    Finite.guard (rest.getLast? == some ">") .request
    let checked ← naturalWidth sources helpers moduleName rest.dropLast
    pure ⟨[.bits checked.value],[]⟩) : Finite.WorkM (TypeRead sources)).run middle = (.ok read,endRead) at body
  obtain ⟨_,a,closed,h⟩ := Finite.bind_success _ _ _ _ _ body
  obtain ⟨checked,b,_,h⟩ := Finite.bind_success _ _ _ _ _ h
  obtain ⟨before,helperRun⟩ := sourceHelpers_prepared sources helpers work middle prepared
  have same := (Finite.pure_success _ _ _ _ h).1
  refine ⟨checked.value,by simpa only [same] using projected,
    beq_iff_eq.mp (Finite.guard_success _ _ _ _ closed).1,?_⟩
  exact ⟨helpers,checked.original.expression,checked.original.bindings,
    ⟨before,middle,helperRun⟩,checked.original.parsed,checked.original.resolved,checked.meaning⟩

end QleisliKernel.SourceTypes
