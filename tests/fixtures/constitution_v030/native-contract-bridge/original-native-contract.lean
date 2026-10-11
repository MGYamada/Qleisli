import Protocol.Validity
import QleisliKernel.Qirf.Contract

/-! Strict bounded request decoding; acceptance is delegated to the pure kernel.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.NativeContract
open Lean QleisliKernel.Finite

private def adapt {α : Type} (value : Except String α) : WorkM α :=
  lift (value.mapError fun _ => .invalid)
private def fields (value : Json) (names : List String) : Except String Unit := do
  let actual := (← value.getObj?).toList.map (·.1)
  if actual.length != names.length || !actual.all names.contains then throw "unexpected request fields"
private def port (value : Json) : Except String Semantics.Raw.Port := do
  fields value ["token","wires","shape"]
  let shape ← value.getObjVal? "shape"
  fields shape ["bits"]
  return ⟨← (← value.getObjVal? "token").getNat?,
    ← (← (← value.getObjVal? "wires").getArr?).toList.mapM Json.getNat?,
    ← (← shape.getObjVal? "bits").getNat?⟩

def check (bytes : ByteArray) : WorkM Bool := do
  let (body,request) ← adapt (Validity.packet bytes)
  let some request := request | throw .request
  let some text := String.fromUTF8? request | throw .invalid
  let value ← adapt (FiniteCodec.parseWithDepth text 128)
  let kind ← adapt ((← adapt (value.getObjVal? "kind")).getStr?)
  let format ← adapt ((← adapt (value.getObjVal? "format")).getStr?)
  let version ← adapt ((← adapt (value.getObjVal? "version")).getNat?)
  guard (format == "qleisli.native-contract" && version == 1) .request
  let (artifact,order) ← Qirf.read body
  if kind == "encoded" then
    adapt (fields value ["format","version","kind","contract"])
    let required ← FiniteCodec.readContract (← adapt (value.getObjVal? "contract"))
    QleisliKernel.Qirf.checkContract artifact order required
  else if kind == "leaf" then
    adapt (fields value ["format","version","kind","signature","input","output","matrix"])
    let signature ← adapt (Qirf.basis 129 (← adapt (value.getObjVal? "signature")))
    let input ← adapt (port (← adapt (value.getObjVal? "input")))
    let output ← adapt (port (← adapt (value.getObjVal? "output")))
    let matrix ← FiniteCodec.readMatrixValue (← adapt (value.getObjVal? "matrix"))
    let _ ← QleisliKernel.Qirf.Validity.checkRoot artifact order
    let _ ← QleisliKernel.Qirf.check artifact order signature input output matrix
    pure ()
  else throw .request
  return true

end QleisliKernel.Protocol.NativeContract
