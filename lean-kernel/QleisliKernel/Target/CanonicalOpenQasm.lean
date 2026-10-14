import QleisliKernel.Semantics.CanonicalTerminalQasm

/-! Independent exact byte decoder for the fixed canonical terminal profile.
This reader imports only the target's Raw meaning data. The mathematical
standard-library meaning is explicit; no include path or file is consulted.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Target.CanonicalOpenQasm
open Semantics.CanonicalTerminalQasm

def maxBytes : Nat := 1024
def maxGates : Nat := 8

structure Decoded where
  original : ByteArray
  gates : List Gate
  deriving BEq

private def ascii (text : String) : List UInt8 := text.toUTF8.data.toList

private def gate (line : List UInt8) : Except String Gate :=
  if line == ascii "h q[0];" then .ok .h
  else if line == ascii "x q[0];" then .ok .x
  else if line == ascii "y q[0];" then .ok .y
  else if line == ascii "z q[0];" then .ok .z
  else if line == ascii "s q[0];" then .ok .s
  else if line == ascii "sdg q[0];" then .ok .sdg
  else if line == ascii "t q[0];" then .ok .t
  else if line == ascii "tdg q[0];" then .ok .tdg
  else .error "unsupported canonical gate"

private def word (input : List (List UInt8)) : Except String (List Gate) := do
  match input.reverse with
  | [] :: measurement :: reversedGates =>
    if measurement != ascii "c[0] = measure q[0];" then throw "missing terminal measurement"
    reversedGates.foldlM (fun gates line => do
      let next ← gate line
      return next :: gates) []
  | _ => throw "missing terminal measurement"

private def lines (bytes : List UInt8) : List (List UInt8) :=
  bytes.foldr (fun byte rest =>
    if byte == 10 then [] :: rest else match rest with
    | [] => [[byte]]
    | line :: tail => (byte :: line) :: tail) [[]]

private def header : List (List UInt8) :=
  ["OPENQASM 3.0;","include \"stdgates.inc\";","qubit[1] q;","bit[1] c;","reset q;"].map ascii

/-- Literal ASCII header/include means no file is loaded and no UTF-8 runtime
primitive determines the grammar. Exact byte/line syntax and terminal order
reject all unsupported input. This profile has explicit byte and gate capacities. -/
def decode (bytes : ByteArray) : Except String Decoded :=
  if bytes.size > maxBytes then .error "target byte limit"
  else if !(bytes.data.toList.all fun byte => byte.toNat < 128) then .error "target ASCII"
  else
    let all := lines bytes.data.toList
    if all.take 5 != header then .error "unsupported canonical target header"
    else
      let rest := all.drop 5
      if rest.length > maxGates + 2 then .error "target gate word limit"
      else (word rest).map (fun gates => ⟨bytes,gates⟩)

/-- The retained subject is the literal input bytes, without a reconstructed
text or producer digest replacing the actual target artifact. -/
theorem decode_original (bytes : ByteArray) (decoded : Decoded)
    (ok : decode bytes = .ok decoded) : decoded.original = bytes := by
  unfold decode at ok
  split at ok
  · cases ok
  · split at ok
    · cases ok
    · dsimp only at ok
      split at ok
      · cases ok
      · split at ok
        · cases ok
        · cases value : word (List.drop 5 (lines bytes.data.toList)) with
          | error error => simp [value,Except.map] at ok
          | ok gates =>
            simp only [value,Except.map,Except.ok.injEq] at ok
            subst decoded
            rfl


end QleisliKernel.Target.CanonicalOpenQasm
