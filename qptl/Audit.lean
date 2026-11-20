/-
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
-/
import QPTLTests
import Lean.Util.CollectAxioms
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr
import Lean.Compiler.CSimpAttr
import Lean.Elab.Command

open Lean in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked := 0
  for (name, info) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let owner := env.header.moduleNames[index]!
    unless (`QPTL).isPrefixOf owner || (`QPTLTests).isPrefixOf owner do continue
    checked := checked + 1
    if info.isUnsafe then throwError "{name}: unsafe QPTL declaration"
    if info.isPartial then throwError "{name}: partial QPTL declaration"
    if (Compiler.getImplementedBy? env name).isSome then
      throwError "{name}: implemented_by replacement"
    if (getExternAttrData? env name).isSome then
      throwError "{name}: extern implementation"
    if Compiler.hasCSimpAttribute env name then
      throwError "{name}: compiler-simplification replacement"
    if let .axiomInfo _ := info then throwError "{name}: QPTL project axiom"
    for axiomName in ← collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on forbidden axiom {axiomName}"
  if checked == 0 then throwError "No QPTL declarations were audited"
  logInfo m!"Audited {checked} QPTL declarations"
