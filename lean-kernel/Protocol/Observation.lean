import Protocol.Raw
import QleisliKernel.Raw.Instrument

/-! Strict experimental VM-26 transport; not production QIRF authority.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.Observation
open Lean QleisliKernel.Semantics.Raw QleisliKernel.Semantics.Observation

private def fields (value : Json) (names : List String) : Except String Unit := do
  let actual := (← value.getObj?).toList.map (·.1)
  if actual.length != names.length || !actual.all names.contains then throw "unexpected/missing observation fields"

private def array (value : Json) : Except String (List Json) := return (← value.getArr?).toList
private def field (value : Json) (key : String) := value.getObjVal? key
private def n (value : Json) (key : String) : Except String Nat := do
  let number ← (← field value key).getNat?
  if number > 4294967295 then throw "raw integer exceeds u32"
  return number
private def ns (value : Json) (key : String) : Except String (List Nat) := do
  (← array (← field value key)).mapM fun value => do
    let number ← value.getNat?
    if number > 4294967295 then throw "raw integer exceeds u32"
    return number

def operation (fuel : Nat) : Json → Except String Semantics.Observation.Op :=
  Nat.rec (fun _ => throw "branch depth exceeds 64") (fun _ recurse value => do
    match ← (← field value "tag").getStr? with
    | "measure_z" =>
      fields value ["tag","input","output"]
      return .measure (← n value "input") (← n value "output")
    | "reset" =>
      fields value ["tag","input","output","fresh_wire"]
      return .reset (← n value "input") (← n value "output") (← n value "fresh_wire")
    | "discard" =>
      fields value ["tag","input"]
      return .discard (← n value "input")
    | "classical_const" =>
      fields value ["tag","value","output"]
      return .constant (← (← field value "value").getBool?) (← n value "output")
    | "classical_not" =>
      fields value ["tag","input","output"]
      return .not (← n value "input") (← n value "output")
    | "classical_xor" =>
      fields value ["tag","left","right","output"]
      return .xor (← n value "left") (← n value "right") (← n value "output")
    | "classical_and" =>
      fields value ["tag","left","right","output"]
      return .and (← n value "left") (← n value "right") (← n value "output")
    | "classical_branch" =>
      fields value ["tag","condition","then_ops","else_ops","quantum_phis","classical_phis"]
      let left ← (← array (← field value "then_ops")).mapM recurse
      let right ← (← array (← field value "else_ops")).mapM recurse
      let quantum ← (← array (← field value "quantum_phis")).mapM fun phi => do
        fields phi ["then_token","else_token","output","output_wires"]
        return QuantumPhi.mk (← n phi "then_token") (← n phi "else_token") (← n phi "output") (← ns phi "output_wires")
      let classical ← (← array (← field value "classical_phis")).mapM fun phi => do
        fields phi ["then_id","else_id","output"]
        return ClassicalPhi.mk (← n phi "then_id") (← n phi "else_id") (← n phi "output")
      return .branch (← n value "condition") left right quantum classical
    | _ => return .pure (← Raw.operation value)) fuel

def program (value : Json) : Except String Semantics.Observation.Program := do
  fields value ["quantum_inputs","classical_inputs","operations","quantum_outputs","classical_outputs","declared_effect"]
  let inputs ← (← array (← field value "quantum_inputs")).mapM fun port => do
    fields port ["token","wires","shape"]
    let shape ← field port "shape"
    fields shape ["bits"]
    let bits ← n shape "bits"
    if bits > 255 then throw "basis shape exceeds u8"
    return Port.mk (← n port "token") (← ns port "wires") bits
  let effect ← match ← (← field value "declared_effect").getStr? with
    | "unitary" => pure Effect.unitary | "iso" => pure Effect.iso | "observe" => pure Effect.observe
    | _ => throw "unknown raw effect"
  return ⟨inputs,← ns value "classical_inputs",← (← array (← field value "operations")).mapM (operation 65),
    ← ns value "quantum_outputs",← ns value "classical_outputs",effect⟩

structure Artifact where
  dependencies : List Semantics.Function.Input
  bindings : List Semantics.Function.Binding
  program : Semantics.Observation.Program

def artifact (value : Json) : Except String Artifact := do
  fields value ["format","version","dependencies","bindings","program"]
  if (← (← field value "format").getStr?) != "qleisli.raw-observing-component" || (← n value "version") != 1 then
    throw "unknown observation profile"
  let dependencies ← (← array (← field value "dependencies")).mapM Raw.functionInput
  let bindings ← (← array (← field value "bindings")).mapM Raw.functionInput
  return ⟨dependencies,bindings,← program (← field value "program")⟩

end QleisliKernel.Protocol.Observation
