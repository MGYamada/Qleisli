import QleisliKernel.Semantics.RawTrace

/-! Literal circuit presentations of original protected uses. The source and
auxiliary labels select target actions or diagonal phases; this module contains
no acceptance, capacities or evidence receipts. Non-dense complex action is
specified separately in the Mathlib model.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Semantics.Protected
open Raw Finite

def phaseExponent : Phase → Nat | .minusOne => 4 | .eighthTurn => 1

def axis (dataBits : Nat) (value : ProtectedBit) : Nat :=
  match value.region with | .source => value.index | .ancilla => dataBits + value.index

def value (source ancilla : Nat) (location : ProtectedBit) : Bool :=
  bit (match location.region with | .source => source | .ancilla => ancilla) location.index == 1

def enabled (source ancilla : Nat) (controls : List ProtectedControl) : Bool :=
  controls.all fun control => value source ancilla control.bit == control.whenOne

def physical (sourceBits dataBits : Nat) : Use → Step
  | .protectedGate location gate => RawTrace.gate gate (axis dataBits location)
  | .targetGate controls target gate => {RawTrace.gate gate (sourceBits+target) with
      controls := controls.map fun control => ⟨axis dataBits control.bit,control.whenOne⟩}
  | .phase controls phase => ⟨controls.map (fun control => ⟨axis dataBits control.bit,control.whenOne⟩),
      .monomial [] [0] [phaseExponent phase]⟩

/-- Finite presentation of the target action selected by the original source
and computed labels. This is a presentation, not a certificate of zero return. -/
def logical (sourceBits : Nat) (function : List Nat) (use : Use) : List Step :=
  let sourceAxes := List.range sourceBits
  match use with
  | .protectedGate location gate => [⟨[],.monomial sourceAxes (List.range function.length)
      ((function.zipIdx).map fun (ancilla,source) =>
        if value source ancilla location then (if gate == .z then 4 else 1) else 0)⟩]
  | .phase controls phase => [⟨[],.monomial sourceAxes (List.range function.length)
      ((function.zipIdx).map fun (ancilla,source) =>
        if enabled source ancilla controls then phaseExponent phase else 0)⟩]
  | .targetGate controls target gate => (function.zipIdx).filterMap fun (ancilla,source) =>
      if enabled source ancilla controls then
        some {RawTrace.gate gate (sourceBits+target) with controls := sourceAxes.map fun index =>
          ⟨index,bit source index == 1⟩}
      else none

end QleisliKernel.Semantics.Protected
