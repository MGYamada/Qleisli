import QleisliKernel
import Main
import Lean.Util.CollectAxioms
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr
import Lean.Compiler.NoncomputableAttr
import Lean.Elab.Command

/-!
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

Audit the compiled project declarations, including generated and private ones.
This build-time program is outside the executable kernel. Lean's own compiler,
standard library, native primitives and runtime remain trusted dependencies.
-/

open Lean

namespace QleisliKernelAudit

def ownedModule (name : Name) : Bool :=
  (`QleisliKernel).isPrefixOf name || name == `Main || name == `Protocol

def allowedModule (name : Name) (transport : Bool) : Bool :=
  (`Init).isPrefixOf name || (`Std).isPrefixOf name ||
  (`QleisliKernel).isPrefixOf name ||
  (transport && (name == `Main || name == `Protocol || (`Lean).isPrefixOf name))

-- Inspect the compiled import graph, not Audit.lean's own metaprogram imports.
partial def checkImports (env : Environment) (name : Name) (transport : Bool)
    (seen : NameSet := {}) : Except String NameSet := do
  unless allowedModule name transport do
    throw s!"forbidden runtime import {name}"
  if seen.contains name then return seen
  let some idx := env.getModuleIdx? name
    | throw s!"runtime module is not imported: {name}"
  let mut seen := seen.insert name
  for dependency in env.header.moduleData[idx]!.imports do
    seen ← checkImports env dependency.module transport seen
  return seen

def check : CoreM Unit := do
  let env ← getEnv
  let pureModules ← ofExcept (checkImports env `QleisliKernel false)
  let runtimeModules ← ofExcept (checkImports env `Main true)
  let allowedAxioms := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked := 0
  let mut kernelChecked := 0
  let mut used : Array Name := #[]
  let mut present : NameSet := {}
  for (name, info) in env.constants.toList do
    let fromProject := match env.getModuleIdxFor? name with
      | some idx => ownedModule env.header.moduleNames[idx]!
      | none => false
    if fromProject then
      checked := checked + 1
      if let some idx := env.getModuleIdxFor? name then
        present := present.insert env.header.moduleNames[idx]!
        if (`QleisliKernel).isPrefixOf env.header.moduleNames[idx]! then
          kernelChecked := kernelChecked + 1
      if info.isUnsafe then throwError "{name}: unsafe project declaration"
      if info.isPartial then throwError "{name}: partial project declaration"
      if isNoncomputable env name then
        throwError "{name}: noncomputable project declaration"
      if (Compiler.getImplementedBy? env name).isSome then
        throwError "{name}: project implemented_by replacement"
      if (getExternAttrData? env name).isSome then
        throwError "{name}: project extern implementation"
      if let .axiomInfo _ := info then
        throwError "{name}: project axiom"
      for axiomName in ← collectAxioms name do
        unless allowedAxioms.contains axiomName do
          throwError "{name} depends on forbidden axiom {axiomName}"
        unless used.contains axiomName do used := used.push axiomName
  unless kernelChecked > 0 && present.contains `Main do
    throwError "No executable project declarations were audited"
  logInfo m!"Audited {checked} kernel/transport declarations, {pureModules.size} pure import modules and {runtimeModules.size} executable import modules; axioms used: {used}"

end QleisliKernelAudit

run_cmd Lean.Elab.Command.liftCoreM QleisliKernelAudit.check
