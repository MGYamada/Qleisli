import Protocol.FiniteCodec
import QleisliKernel.Raw.Finite
import QleisliKernel.Semantics.Function

/-! Unproved, bounded VM-25 raw-component transport. RawProgram fields retain
QIRF spellings; this envelope is experimental, not the complete QIRF decoder.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.Raw
open Lean QleisliKernel.Semantics.Raw QleisliKernel.Semantics.Finite

private def fields (value : Json) (names : List String) : Except String Unit := do
  let actual := (← value.getObj?).toList.map (·.1)
  if actual.length != names.length || !actual.all names.contains then throw "unexpected/missing raw fields"

private def field (value : Json) (key : String) := value.getObjVal? key
private def array (value : Json) : Except String (List Json) := return (← value.getArr?).toList
private def number (value : Json) : Except String Nat := do
  let n ← value.getNat?
  if n > 4294967295 then throw "raw integer exceeds u32"
  return n
private def n (value : Json) (key : String) := do number (← field value key)
private def numbers (value : Json) : Except String (List Nat) := do (← array value).mapM number
private def ns (value : Json) (key : String) := do numbers (← field value key)
private def text (value : Json) (key : String) := do (← field value key).getStr?

private def gate (value : Json) : Except String Gate := do
  match ← value.getStr? with
  | "h" => pure .h | "x" => pure .x | "z" => pure .z | "t" => pure .t
  | _ => throw "unknown raw gate"

private def phase (value : Json) : Except String Phase := do
  match ← value.getStr? with
  | "minus_one" => pure .minusOne | "eighth_turn" => pure .eighthTurn
  | _ => throw "unknown raw phase"

private def steps (value : Json) : Except String (List Step) := do
  return (← FiniteCodec.circuit (Json.mkObj [("basis",Json.arr #[Json.str "unit"]),("steps",value)])).steps

private def unitary (value : Json) : Except String UnitaryStep := do
  match ← text value "tag" with
  | "gate" =>
    fields value ["tag","gate","target_index"]
    return .gate (← gate (← field value "gate")) (← n value "target_index")
  | "cnot" =>
    fields value ["tag","control_index","target_index"]
    return .cnot (← n value "control_index") (← n value "target_index")
  | "toffoli" =>
    fields value ["tag","control_a_index","control_b_index","target_index"]
    return .toffoli (← n value "control_a_index") (← n value "control_b_index") (← n value "target_index")
  | "scalar_phase" =>
    fields value ["tag","phase"]
    return .phase (← phase (← field value "phase"))
  | _ => throw "unknown raw unitary step"

private def protectedBit (value : Json) : Except String ProtectedBit := do
  fields value ["region","index"]
  let region ← match ← text value "region" with
    | "source" => pure Region.source | "ancilla" => pure Region.ancilla
    | _ => throw "unknown protected region"
  let index ← n value "index"
  if index > 255 then throw "protected index exceeds u8"
  return ⟨region,index⟩

private def controls (value : Json) : Except String (List ProtectedControl) := do
  (← array value).mapM fun c => do
    fields c ["bit","when_one"]
    return ⟨← protectedBit (← field c "bit"),← (← field c "when_one").getBool?⟩

private def usage (value : Json) : Except String Use := do
  match ← text value "tag" with
  | "protected_gate" =>
    fields value ["tag","bit","gate"]
    return .protectedGate (← protectedBit (← field value "bit")) (← gate (← field value "gate"))
  | "controlled_target_gate" =>
    fields value ["tag","controls","target_index","gate"]
    return .targetGate (← controls (← field value "controls")) (← n value "target_index") (← gate (← field value "gate"))
  | "controlled_phase" =>
    fields value ["tag","controls","phase"]
    return .phase (← controls (← field value "controls")) (← phase (← field value "phase"))
  | _ => throw "unknown protected use"

def operation (value : Json) : Except String Op := do
  match ← text value "tag" with
  | "init0" =>
    fields value ["tag","output","wire"]
    return .init0 (← n value "output") (← n value "wire")
  | "gate" =>
    fields value ["tag","gate","input","output"]
    return .gate (← gate (← field value "gate")) (← n value "input") (← n value "output")
  | "cnot" =>
    fields value ["tag","control","target","control_out","target_out"]
    return .cnot (← n value "control") (← n value "target") (← n value "control_out") (← n value "target_out")
  | "toffoli" =>
    fields value ["tag","control_a","control_b","target","control_a_out","control_b_out","target_out"]
    return .toffoli (← n value "control_a") (← n value "control_b") (← n value "target")
      (← n value "control_a_out") (← n value "control_b_out") (← n value "target_out")
  | "quantum_if" =>
    fields value ["tag","control","target","control_out","target_out","zero_ops","one_ops"]
    return .quantumIf (← n value "control") (← n value "target") (← n value "control_out") (← n value "target_out")
      (← (← array (← field value "zero_ops")).mapM unitary) (← (← array (← field value "one_ops")).mapM unitary)
  | "split" =>
    fields value ["tag","input","left","right","left_bits"]
    let count ← n value "left_bits"
    if count > 255 then throw "split width exceeds u8"
    return .split (← n value "input") (← n value "left") (← n value "right") count
  | "join" =>
    fields value ["tag","left","right","output"]
    return .join (← n value "left") (← n value "right") (← n value "output")
  | "lift_basis" =>
    fields value ["tag","input","output","output_wires","table"]
    let table ← ns value "table"
    if !table.all (· ≤ 65535) then throw "lift table exceeds u16"
    return .liftBasis (← n value "input") (← n value "output") (← ns value "output_wires") table
  | "apply_unitary" =>
    fields value ["tag","input","output","steps"]
    return .applyUnitary (← n value "input") (← n value "output") (← steps (← field value "steps"))
  | "certified_compute" =>
    fields value ["tag","source","source_out","ancilla_wires","function","use_steps","logical_steps"]
    return .certifiedCompute (← n value "source") (← n value "source_out") (← ns value "ancilla_wires")
      (← ns value "function") (← steps (← field value "use_steps")) (← steps (← field value "logical_steps"))
  | "compute_use_uncompute" =>
    fields value ["tag","source","source_out","targets","ancilla_wires","function","use_ops"]
    let targets ← (← array (← field value "targets")).mapM fun target => do
      fields target ["input","output"]
      return Target.mk (← n target "input") (← n target "output")
    let function ← ns value "function"
    if !function.all (· ≤ 65535) then throw "computed table exceeds u16"
    return .computeUseUncompute (← n value "source") (← n value "source_out") targets
      (← ns value "ancilla_wires") function (← (← array (← field value "use_ops")).mapM usage)
  | _ => throw "operation requires VM-26 or an unknown raw profile"

def program (value : Json) : Except String Program := do
  fields value ["quantum_inputs","classical_inputs","operations","quantum_outputs","classical_outputs","declared_effect"]
  if !(← array (← field value "classical_inputs")).isEmpty || !(← array (← field value "classical_outputs")).isEmpty then
    throw "classical interfaces require VM-26"
  let inputs ← (← array (← field value "quantum_inputs")).mapM fun port => do
    fields port ["token","wires","shape"]
    let shape ← field port "shape"
    fields shape ["bits"]
    let bits ← n shape "bits"
    if bits > 255 then throw "basis shape exceeds u8"
    return Port.mk (← n port "token") (← ns port "wires") bits
  let effect ← match ← text value "declared_effect" with
    | "unitary" => pure Effect.unitary | "iso" => pure Effect.iso | "observe" => pure Effect.observe
    | _ => throw "unknown raw effect"
  return ⟨inputs,← (← array (← field value "operations")).mapM operation,← ns value "quantum_outputs",effect⟩

structure Artifact where
  evidence : List QleisliKernel.Semantics.Raw.Evidence
  program : Program
  deriving Repr

/-- Private VM-25 attachment reader; the complete binding is checked separately.
Parsing neither issues a receipt nor proves source preservation. -/
def functionInput (value : Json) : Except String QleisliKernel.Semantics.Function.Input := do
  fields value ["signature","implementation","specification","identity"]
  let identity ← field value "identity"
  fields identity ["implementation","specification","sources"]
  let sources ← (← array (← field identity "sources")).mapM fun source => do
    fields source ["name","source"]
    return (← text source "name",← text source "source")
  return ⟨⟨← FiniteCodec.basis (← field value "signature"),← program (← field value "implementation"),
    ← program (← field value "specification")⟩,
    ⟨← text identity "implementation",← text identity "specification",sources⟩⟩

def artifact (value : Json) : Except String Artifact := do
  fields value ["format","version","evidence","program"]
  if (← text value "format") != "qleisli.raw-pure-component" || (← n value "version") != 1 then
    throw "unsupported raw component envelope"
  let evidence ← (← array (← field value "evidence")).mapM fun entry => do
    fields entry ["signature","implementation","specification"]
    return QleisliKernel.Semantics.Raw.Evidence.mk (← FiniteCodec.basis (← field entry "signature"))
      (← program (← field entry "implementation")) (← program (← field entry "specification"))
  return ⟨evidence,← program (← field value "program")⟩

end QleisliKernel.Protocol.Raw
