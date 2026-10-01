import QleisliKernel.Finite
import Lean.Data.Json.Parser

/-! Unproved transport adapter for the existing experimental profiles.
Inputs remain untrusted until checked by the independently specified pure kernel.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

namespace QleisliKernel.Protocol.FiniteCodec
open Lean QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite

inductive Frame where
  | object (keys : List String) (key : Bool) | array
  deriving Repr
inductive Mode where
  | outside | quote | escape | bare
  deriving BEq, Repr
structure Scan where
  mode : Mode := .outside
  literal : List Char := []
  stack : List Frame := []
  depth : Nat := 0
  count : Nat := 0
  deriving Repr

private def bare (literal : List Char) : Except String Unit := do
  let text := String.ofList literal.reverse
  if text == "true" || text == "false" || text == "null" then return
  if text.isEmpty || !text.toList.all Char.isDigit || text.length > 20 then
    throw "expected bounded unsigned integer"
  let some number := text.toNat? | throw "invalid integer"
  if number > 18446744073709551615 then throw "integer exceeds u64"

private def stringToken (scan : Scan) : Except String Scan := do
  let value ← Json.parse (String.ofList scan.literal.reverse)
  let text ← value.getStr?
  match scan.stack with
  | .object keys true :: rest =>
    if keys.contains text then throw "duplicate JSON field"
    if keys.length ≥ 64 then throw "too many object fields"
    return {scan with mode := .outside,literal := [],stack := .object (text::keys) false :: rest}
  | _ => return {scan with mode := .outside,literal := []}

private def punctuation (scan : Scan) (char : Char) : Except String Scan := do
  if char == '{' || char == '[' then
    if scan.depth ≥ 64 then throw "JSON depth exceeds 64"
    let frame := if char == '{' then Frame.object [] true else .array
    return {scan with stack := frame :: scan.stack,depth := scan.depth+1}
  if char == '}' || char == ']' then
    let _ :: rest := scan.stack | throw "unmatched JSON close"
    return {scan with stack := rest,depth := scan.depth-1}
  if char == ',' then
    match scan.stack with
    | .object keys _ :: rest => return {scan with stack := .object keys true :: rest}
    | _ => return scan
  return scan

private def outside (scan : Scan) (char : Char) : Except String Scan := do
  if char == '"' then return {scan with mode := .quote,literal := ['"']}
  if char == ' ' || char == '\n' || char == '\r' || char == '\t' then return scan
  if char == '{' || char == '}' || char == '[' || char == ']' || char == ',' || char == ':' then
    punctuation scan char
  else return {scan with mode := .bare,literal := [char]}

private def scanChar (scan : Scan) (char : Char) : Except String Scan := do
  if scan.count ≥ 16777216 then throw "JSON exceeds 16 MiB"
  let scan := {scan with count := scan.count+1}
  match scan.mode with
  | .outside => outside scan char
  | .escape => return {scan with mode := .quote,literal := char :: scan.literal}
  | .quote =>
    let scan := {scan with literal := char :: scan.literal}
    if char == '\\' then return {scan with mode := .escape}
    if char == '"' then stringToken scan else return scan
  | .bare =>
    if char == ',' || char == ':' || char == '}' || char == ']' ||
        char == ' ' || char == '\n' || char == '\r' || char == '\t' then
      bare scan.literal
      outside {scan with mode := .outside,literal := []} char
    else return {scan with literal := char :: scan.literal}

/-- Duplicate fields are rejected before Lean.Json's map insertion can erase them.
Numeric spelling, byte/depth bounds and full JSON framing are checked afresh. -/
def parse (text : String) : Except String Json := do
  if text.utf8ByteSize > 16777216 then throw "JSON exceeds 16 MiB"
  let scan ← text.toList.foldlM scanChar {}
  if scan.mode == .bare then bare scan.literal
  else if scan.mode != .outside then throw "unterminated JSON string"
  if !scan.stack.isEmpty then throw "unclosed JSON container"
  Json.parse text

private def fields (value : Json) (names : List String) : Except String Unit := do
  let object ← value.getObj?
  let actual := object.toList.map (·.1)
  if actual.length != names.length || !actual.all names.contains then throw "unexpected/missing JSON fields"

private def array (value : Json) : Except String (List Json) := return (← value.getArr?).toList
private def field (value : Json) (name : String) : Except String Json := value.getObjVal? name
private def nat (value : Json) : Except String Nat := value.getNat?

def matrixDescription (value : Json) : Except String MatrixDescription := do
  fields value ["format","version","domain","rows","cols","entries"]
  if (← (← field value "format").getStr?) != "qleisli.finite-matrix" ||
      (← nat (← field value "version")) != 1 ||
      (← (← field value "domain").getStr?) != "zeta8-dyadic-v1" then throw "unsupported exact matrix profile"
  let entries ← (← array (← field value "entries")).mapM fun entry => do
    (← array entry).mapM fun coefficient => do
      fields coefficient ["numerator","denominator_bits"]
      return ⟨← (← field coefficient "numerator").getStr?,← nat (← field coefficient "denominator_bits")⟩
  return ⟨← nat (← field value "rows"),← nat (← field value "cols"),entries⟩

def decodeMatrix (text : String) : Except String MatrixDescription := do
  matrixDescription (← parse text)

private def adapter {α : Type} (result : Except String α) : QleisliKernel.Finite.WorkM α :=
  QleisliKernel.Finite.lift (result.mapError (fun _ => .invalid))

/-- Read the published description under the same shared work ceiling. Nested
coefficient fields are inspected after the four-per-entry charge, as in Rust. -/
def readMatrixValue (value : Json) : QleisliKernel.Finite.WorkM Matrix := do
  let work ← get
  QleisliKernel.Finite.guard (work ≤ 10000000) .limit
  adapter (fields value ["format","version","domain","rows","cols","entries"])
  let profile ← adapter (do
    return (← (← field value "format").getStr?) == "qleisli.finite-matrix" &&
      (← nat (← field value "version")) == 1 &&
      (← (← field value "domain").getStr?) == "zeta8-dyadic-v1")
  QleisliKernel.Finite.guard profile
  let rows ← adapter (nat (← adapter (field value "rows")))
  let cols ← adapter (nat (← adapter (field value "cols")))
  QleisliKernel.Finite.guard (QleisliKernel.Exact.matrixValid rows cols) .limit
  let entries ← adapter (array (← adapter (field value "entries")))
  QleisliKernel.Finite.guard (entries.length == rows * cols)
  QleisliKernel.Finite.exactWork (QleisliKernel.Exact.charge (4 * entries.length))
  let values ← entries.mapM fun entry => do
    let coefficients ← adapter (array entry)
    QleisliKernel.Finite.guard (coefficients.length == 4)
    let descriptions ← adapter (coefficients.mapM fun coefficient => do
      fields coefficient ["numerator","denominator_bits"]
      return DyadicDescription.mk (← (← field coefficient "numerator").getStr?)
        (← nat (← field coefficient "denominator_bits")))
    QleisliKernel.Finite.lift (QleisliKernel.Finite.scalarRead descriptions)
  QleisliKernel.Finite.lift (QleisliKernel.Finite.arithmetic
    (QleisliKernel.Exact.Matrix.make rows cols values))

def readMatrix (text : String) : QleisliKernel.Finite.WorkM Matrix := do
  let work ← get
  QleisliKernel.Finite.guard (work ≤ 10000000) .limit
  readMatrixValue (← adapter (parse text))

/-- Private experimental prefix bridge; legacy type trees retain all atoms. -/
def basis (value : Json) : Except String Basis := do
  (← array value).mapM fun atom => do
    let text ← atom.getStr?
    if text == "unit" then return .unit
    if text == "bit" then return .bit
    if text == "pair" then return .pair
    let some arity := (text.drop 6).toString.toNat? | throw "invalid basis atom"
    if text != "tuple:" ++ toString arity then throw "invalid basis atom"
    return .tuple arity

private def nats (value : Json) : Except String (List Nat) := do (← array value).mapM nat

def circuit (value : Json) : Except String Circuit := do
  fields value ["basis","steps"]
  let steps ← (← array (← field value "steps")).mapM fun step => do
    fields step ["controls","action"]
    let controls ← (← array (← field step "controls")).mapM fun control => do
      fields control ["index","when_one"]
      return Control.mk (← nat (← field control "index")) (← (← field control "when_one").getBool?)
    let action ← field step "action"
    let tag ← (← field action "tag").getStr?
    let action ← if tag == "hadamard" then do
        fields action ["tag","target"]
        pure (Action.hadamard (← nat (← field action "target")))
      else if tag == "monomial" then do
        fields action ["tag","indices","permutation","phases"]
        pure (Action.monomial (← nats (← field action "indices"))
          (← nats (← field action "permutation")) (← nats (← field action "phases")))
      else if tag == "contract" then do
        fields action ["tag","indices","evidence","adjoint"]
        pure (Action.contract (← nats (← field action "indices"))
          (← nat (← field action "evidence")) (← (← field action "adjoint").getBool?))
      else throw "unknown finite action"
    pure ⟨controls,action⟩
  return ⟨← basis (← field value "basis"),steps⟩

def readEncoding (value : Json) : QleisliKernel.Finite.WorkM Encoding := do
  adapter (fields value ["logical","physical","map"])
  let logical ← adapter (basis (← adapter (field value "logical")))
  let physical ← adapter (basis (← adapter (field value "physical")))
  let map ← readMatrixValue (← adapter (field value "map"))
  pure ⟨logical,physical,map⟩

def readContract (value : Json) : QleisliKernel.Finite.WorkM Contract := do
  adapter (fields value ["input","output","logical"])
  let input ← readEncoding (← adapter (field value "input"))
  let output ← readEncoding (← adapter (field value "output"))
  let logical ← readMatrixValue (← adapter (field value "logical"))
  pure ⟨input,output,logical⟩

/-- Experimental complete finite-component data. This is deliberately not a
QIRF decoder, a source-binding receipt or a public production protocol. -/
def readArtifact (text : String) : QleisliKernel.Finite.WorkM QleisliKernel.Semantics.Finite.Artifact := do
  let value ← adapter (parse text)
  adapter (fields value ["format","version","root","evidence"])
  let profile ← adapter (do
    return (← (← field value "format").getStr?) == "qleisli.finite-component" &&
    (← nat (← field value "version")) == 1)
  QleisliKernel.Finite.guard profile
  let entries ← adapter (array (← adapter (field value "evidence")))
  QleisliKernel.Finite.guard (entries.length ≤ 65536) .limit
  let evidence ← entries.mapM fun entry => do
    adapter (fields entry ["circuit","claim"])
    let body ← adapter (circuit (← adapter (field entry "circuit")))
    let claim ← readContract (← adapter (field entry "claim"))
    pure (Evidence.mk body claim)
  let root ← adapter (nat (← adapter (field value "root")))
  pure ⟨evidence,root⟩

def readRequirement (text : String) : QleisliKernel.Finite.WorkM Contract := do
  readContract (← adapter (parse text))

end QleisliKernel.Protocol.FiniteCodec
