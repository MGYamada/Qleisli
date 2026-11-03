import QleisliKernel
import QleisliKernel.Tests.FiniteRestriction
import QleisliKernel.Tests.RawSector
import QleisliKernel.Tests.QirfSector
import QleisliKernel.Tests.ComputedSectors
import QleisliKernel.Tests.NominalSector
import QleisliKernel.Tests.SectorArms
import QleisliKernel.Tests.SourceQuantum
import QleisliKernel.Tests.SourceEntries
import QleisliKernel.Tests.DependencySnapshots
import QleisliKernel.Tests.ArmBody
import QleisliKernel.Tests.QuantumMoves
import QleisliKernel.Tests.QuantumBody
import QleisliKernel.Tests.QuantumSequence
import QleisliKernel.Tests.RawOwnerFlow
import QleisliKernel.Tests.PureInterval
import QleisliKernel.Tests.SourceSequence
import QleisliKernel.Tests.SequenceSector
import QleisliKernel.Tests.CallSyntaxTests
import QleisliKernel.Tests.StatementSyntaxTests
import QleisliKernel.Tests.SourceLookupTests
import QleisliKernel.Tests.CallNameTests
import QleisliKernel.Tests.ModuleHeaderTests
import QleisliKernel.Tests.SourceContextTests
import QleisliKernel.Tests.SourceTraceTests
import QleisliKernel.Tests.SourceTraceCacheTests
import QleisliKernel.Tests.SourceCalls
import QleisliKernel.Tests.SourceRuntimeTrace
import QleisliKernel.Tests.GenericPhase
import QleisliKernel.Tests.MeaningTransfer
import QleisliKernel.Tests.OperationAccess
import QleisliKernel.Tests.OperationIRMeaning
import QleisliKernel.Tests.OperationOccurrences
import QleisliKernel.Tests.OperationReceipts
import QleisliKernel.Tests.QuantumPrimitiveArms
import QleisliKernel.Tests.SourceOperationForwarding
import QleisliKernel.Tests.SourceEffectClosure
import QleisliKernel.Tests.SourceNominalSyntax
import QleisliKernel.Tests.SourceNominal
import QleisliKernel.Tests.SourceRuntimeNominalValue
import QleisliKernel.Tests.SourceRuntimeTransform
import QleisliKernel.Tests.SourceStaticControlSyntax
import QleisliKernel.Tests.SourceStaticSelection
import QleisliKernel.Tests.RuntimeInterval
import QleisliKernel.Tests.RuntimeOwnerPhis
import QleisliKernel.Tests.RuntimeSourceBoundary
import QleisliKernel.Tests.RuntimePrimitiveAction
import QleisliKernel.Tests.RuntimeObservationAction
import QleisliKernel.Tests.GenericTypeTrace
import QleisliKernel.Tests.GenericBasisInstance
import QleisliKernel.Tests.SourceCallStack
import QleisliKernel.Tests.SourceMatchSyntax
import QleisliKernel.Tests.SourceRuntimeBasisBindings
import QleisliKernel.Tests.SourceRuntimeNominal
import QleisliKernel.Tests.SourceRuntimeOrdinary
import QleisliKernel.Tests.RuntimeStructuredRoot
import QleisliKernel.Tests.RuntimeMaterialization
import QleisliKernel.Tests.RuntimePureBody
import QleisliKernel.Tests.RuntimeProviderHeaders
import QleisliKernel.Tests.GenericCatalogue
import QleisliKernel.Tests.GenericDefinitionPrepared
import QleisliKernel.Tests.GenericOperation
import QleisliKernel.Tests.GenericDuties
import QleisliKernel.Tests.GenericActivities
import QleisliKernel.Tests.GenericOperationSubstitute
import QleisliKernel.Tests.GenericDutyQueue
import QleisliKernel.Tests.GenericDutyPrepared
import QleisliKernel.Tests.SourceMeaningOrdinary
import QleisliKernel.Tests.SourceMeaningPrepared
import QleisliKernel.Tests.SourceClassicalExecution
import QleisliKernel.Tests.SourcePendingMeaning
import QleisliKernel.Tests.SourceDutySlots
import QleisliKernel.Tests.SourceDutyProviderFresh
import QleisliKernel.Tests.GenericCatalogueOriginals
import QleisliKernel.Tests.SourceComputedSyntax
import QleisliKernel.Tests.SourceRuntimeMatch
import QleisliKernel.Tests.SourceRuntimeRecursion
import QleisliKernel.Tests.SourceRuntimeStatic
import QleisliKernel.Tests.ContextSectorStages
import QleisliKernel.Tests.ContextSource
import QleisliKernel.Tests.QuantumSelectionSyntax
import QleisliKernel.Tests.SourceRuntimeQif
import QleisliKernel.Tests.SourceRuntimeEmpty
import QleisliKernel.Tests.SourceRuntimeComputed
import QleisliKernel.Tests.SourceRuntimeRegisters
import QleisliKernel.Tests.SourceRuntimePatterns
import QleisliKernel.Tests.NaturalNames
import QleisliKernel.Tests.RuntimeOrdinarySSA
import QleisliKernel.Tests.RuntimeOrdinaryPhis
import QleisliKernel.Tests.RuntimeOrdinaryStreamedPhis
import QleisliKernel.Tests.RuntimeOrdinaryBody
import QleisliKernel.Tests.RuntimeOrdinaryInputs
import QleisliKernel.Tests.RuntimeOrdinaryHistories
import QleisliKernel.Tests.RuntimeBodyMixed
import QleisliKernel.Tests.RuntimeStructuralAction
import QleisliKernel.Tests.SourceMeaning
import QleisliKernel.Tests.StaticBasisActual
import QleisliKernel.Tests.StaticCallPremises
import QleisliKernel.Tests.StaticKinds
import QleisliKernel.Tests.StaticOperation
import QleisliKernel.Tests.SymbolicTypes
import QleisliKernel.Tests.TypeNaturalRows
import QleisliKernel.Tests.SourceBasisFunction
import QleisliKernel.Tests.PrimitiveActionTests
import QleisliKernel.Tests.RawTraceTests
import QleisliKernel.Tests.PhaseSourceContext
import QleisliKernel.Tests.SourceNaturalAliases
import QleisliKernel.Tests.OwnerBoundariesTests
import QleisliKernel.Tests.ContextSectorTests
import QleisliKernel.Tests.ContextSectorCost
import QleisliKernel.Tests.RawTraceCost
import QleisliKernel.Tests.RawTraceMeterTests
import QleisliKernel.Tests.CallCoordinateTests
import QleisliKernel.Tests.PreparedIntervalTests
import QleisliKernel.Tests.SequenceSectorSharingTests
import QleisliKernel.Tests.ContextIntervalContinuity
import QleisliKernel.Tests.OriginalSelectionContinuity
import QleisliKernel.Tests.RawTraceMeterContinuity
import QleisliKernel.Tests.RuntimeSignature
import QleisliKernel.Tests.RuntimeStaticHeader
import QleisliKernel.Tests.RuntimeStorage
import QleisliKernel.Tests.RuntimeCode
import QleisliKernel.Tests.RuntimeFamily
import QleisliKernel.Tests.SourceMembers
import QleisliKernel.Tests.OrdinaryInputs
import Main
import Lean.Util.CollectAxioms
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr
import Lean.Compiler.NoncomputableAttr
import Lean.Elab.Command

/-!
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0

Audit the compiled project declarations, including generated and private ones.
This build-time program is outside the executable kernel. Lean's own compiler,
standard library, native primitives and runtime remain trusted dependencies.
-/

open Lean

namespace QleisliKernelAudit

def transportModule (name : Name) : Bool :=
  name == `Main || (`Protocol).isPrefixOf name || (`Cli).isPrefixOf name

def ownedModule (name : Name) : Bool :=
  (`QleisliKernel).isPrefixOf name || transportModule name

def allowedModule (name : Name) (transport : Bool) : Bool :=
  (`Init).isPrefixOf name || (`Std).isPrefixOf name ||
  (`QleisliKernel).isPrefixOf name ||
  (transport && (transportModule name || (`Lean).isPrefixOf name))

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
