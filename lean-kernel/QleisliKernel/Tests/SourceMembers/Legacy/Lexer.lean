import Std

/-! Bounded lexical data for original finite-type declarations. Comments cannot
provide declarations; words are ASCII and original source bytes remain separate.
This is not a complete source-language checker or source-preservation theorem.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.SourceTypesLegacy

private structure Scan where
  line : Bool := false
  block : Nat := 0
  skip : Bool := false
  word : List Char := []
  numeric : Bool := false
  tokens : List String := []

private def flush (s : Scan) : Scan :=
  if s.word.isEmpty then s
  else {s with word := [],tokens := String.ofList s.word.reverse :: s.tokens}

def asciiLetter (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || c == '_'

def identifier (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: rest => s != "_" && asciiLetter c && rest.all (fun c => asciiLetter c || c.isDigit) &&
    !["use","meaning","static","Op","requires","Apply","Adjoint","Controlled",
      "permutation_by","phase_by","checked_op","bind_op","inverse_op","then_op",
      "tensor_op","controlled_op","repeat_op","conjugate_op","pub","enum","struct",
      "classical","basis","isometry","iso","unitary","observe","fn","let","if","match",
      "else","do","pure","with_computed","apply_contract","adjoint","repeat_static",
      "qif","qfor","true","false","not","xor","and","Unit","Bit","CBit","Q"].contains s

private def character (s : Scan) (pair : Char × Option Char) : Except String Scan := do
  let (c,next) := pair
  let code := c.toNat
  if c == '\r' && next != some '\n' then throw "bare carriage return in source"
  if code == 0 || (code < 32 && !['\t','\r','\n'].contains c) ||
      (127 ≤ code && code ≤ 159) ||
      [0x061c,0x200e,0x200f,0x2028,0x2029,0x202a,0x202b,0x202c,0x202d,0x202e,
       0x2066,0x2067,0x2068,0x2069].contains code then throw "forbidden source character"
  if s.skip then return {s with skip := false}
  if s.line then return {s with line := c != '\n'}
  if s.block > 0 then
    if c == '/' && next == some '*' then return {s with block := s.block+1,skip := true}
    if c == '*' && next == some '/' then return {s with block := s.block-1,skip := true}
    return s
  if c == '/' && next == some '/' then return {flush s with line := true,skip := true}
  if c == '/' && next == some '*' then return {flush s with block := 1,skip := true}
  if asciiLetter c || c.isDigit then
    let s := if !s.word.isEmpty && s.numeric && asciiLetter c then flush s else s
    return {s with word := c :: s.word,numeric := if s.word.isEmpty then c.isDigit else s.numeric}
  let s := flush s
  if [' ','\t','\r','\n'].contains c then return s
  if c == ':' && next == some ':' then return {s with tokens := "::" :: s.tokens,skip := true}
  if "[]{}(),;:<>+-*=^|!.#".toList.contains c then
    return {s with tokens := String.singleton c :: s.tokens}
  throw "unsupported source character"

def lex (source : String) : Except String (List String) := do
  if source.utf8ByteSize > 1048576 then throw "source metadata capacity"
  let chars := source.toList
  let next := chars.drop 1 |>.map some
  let state ← (chars.zip (next ++ [none])).foldlM character {}
  if state.block != 0 then throw "unterminated source comment"
  return (flush state).tokens.reverse

end QleisliKernel.SourceTypesLegacy
