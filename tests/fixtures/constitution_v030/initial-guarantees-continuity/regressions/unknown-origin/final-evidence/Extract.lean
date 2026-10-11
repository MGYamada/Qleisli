import Qleisli.NativeValidity
import Lean

/-! Exact elaborated declaration extraction for the two already admitted
ordinary QLV1 guarantees. This is inspection tooling, not an acceptance rule.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
open Lean Elab Command
namespace QleisliContinuity

def tagged (tag : String) (fields : Array Json := #[]) : Json :=
  Json.arr (#[Json.str tag] ++ fields)

def nameJson : Name → Json
  | .anonymous => tagged "anonymous"
  | .str p s => tagged "str" #[nameJson p, toJson s]
  | .num p n => tagged "num" #[nameJson p, toJson n]

def levelJson : Level → Except String Json
  | .zero => pure (tagged "zero")
  | .succ u => return tagged "succ" #[← levelJson u]
  | .max u v => return tagged "max" #[← levelJson u, ← levelJson v]
  | .imax u v => return tagged "imax" #[← levelJson u, ← levelJson v]
  | .param n => pure (tagged "param" #[nameJson n])
  | .mvar _ => throw "unresolved universe metavariable"

def binderJson : BinderInfo → Json
  | .default => toJson "default"
  | .implicit => toJson "implicit"
  | .strictImplicit => toJson "strictImplicit"
  | .instImplicit => toJson "instImplicit"

abbrev ExtractM := StateT (Array Name) (Except String)
def referenced (n : Name) : ExtractM Json := do
  modify (·.push n)
  return nameJson n

def exprJson : Expr → ExtractM Json
  | .bvar n => pure (tagged "bvar" #[toJson n])
  | .fvar _ => throw "free variable in closed declaration"
  | .mvar _ => throw "unresolved expression metavariable"
  | .sort u => return tagged "sort" #[← levelJson u]
  | .const n us => return tagged "const" #[← referenced n, toJson (← (us.mapM levelJson : Except String (List Json)))]
  | .app f a => return tagged "app" #[← exprJson f, ← exprJson a]
  | .lam n t b bi => return tagged "lam" #[nameJson n, binderJson bi, ← exprJson t, ← exprJson b]
  | .forallE n t b bi => return tagged "forall" #[nameJson n, binderJson bi, ← exprJson t, ← exprJson b]
  | .letE n t v b nondep => return tagged "let" #[nameJson n, toJson nondep, ← exprJson t, ← exprJson v, ← exprJson b]
  | .lit (.natVal n) => pure (tagged "nat" #[toJson (toString n)])
  | .lit (.strVal s) => pure (tagged "string" #[toJson s])
  | .mdata _ e => exprJson e
  | .proj n i e => return tagged "proj" #[← referenced n, toJson i, ← exprJson e]

-- The one varying executable body is the actual native checker. Its exact type,
-- origin, and references from the actual success theorems remain mandatory.
def currentChecker : Name := ``QleisliKernel.Protocol.Validity.check

def roots : Array Name := #[
  ``QleisliKernel.Semantics.Ownership.OwnershipSafe,
  ``QleisliKernel.Semantics.ClassicalScope.ScopeSafe,
  ``QleisliKernel.Semantics.Observation.Program,
  ``QleisliKernel.Qirf.Artifact,
  ``QleisliKernel.Protocol.Validity.Acceptance,
  ``QleisliKernel.Protocol.Validity.check_acceptance,
  ``QleisliKernel.Protocol.Validity.check_ownershipSafe,
  ``Qleisli.NativeValidity.check_scopeSafe,
  currentChecker]

-- Generated from the immutable admitted source archive; no record may select modules.
def historicalProjectModules : List String := [
  "Audit",
  "Cli.Common",
  "Cli.Finite",
  "Cli.Hierarchical",
  "Cli.Validity",
  "Main",
  "Protocol",
  "Protocol.BranchFunction",
  "Protocol.Core",
  "Protocol.FiniteCodec",
  "Protocol.Hierarchical",
  "Protocol.HierarchicalFinite",
  "Protocol.Layout",
  "Protocol.NativeContract",
  "Protocol.Observation",
  "Protocol.Product",
  "Protocol.Qirf",
  "Protocol.Raw",
  "Protocol.StreamedObservation",
  "Protocol.Validity",
  "Qleisli",
  "Qleisli.CallLowering",
  "Qleisli.ControlledPowers",
  "Qleisli.CoordinateOperators",
  "Qleisli.Exact",
  "Qleisli.ExactMatrix",
  "Qleisli.Examples",
  "Qleisli.Finite",
  "Qleisli.HierarchicalAcceptance",
  "Qleisli.HierarchicalCircuitTrace",
  "Qleisli.HierarchicalCircuitTraceEvaluation",
  "Qleisli.HierarchicalDiagonal",
  "Qleisli.HierarchicalEvaluation",
  "Qleisli.HierarchicalFiniteEvaluation",
  "Qleisli.HierarchicalFiniteUnitary",
  "Qleisli.HierarchicalFourier",
  "Qleisli.HierarchicalFourierBase",
  "Qleisli.HierarchicalFourierBody",
  "Qleisli.HierarchicalFourierControl",
  "Qleisli.HierarchicalFourierRoot",
  "Qleisli.HierarchicalFourierStage",
  "Qleisli.HierarchicalGradient",
  "Qleisli.HierarchicalHadamard",
  "Qleisli.HierarchicalInstrument",
  "Qleisli.HierarchicalInstrumentComplete",
  "Qleisli.HierarchicalInstrumentCoordinates",
  "Qleisli.HierarchicalOperators",
  "Qleisli.HierarchicalPower",
  "Qleisli.HierarchicalProvider",
  "Qleisli.HierarchicalQpeCircuit",
  "Qleisli.HierarchicalQpeCoordinates",
  "Qleisli.HierarchicalQpeInstrument",
  "Qleisli.HierarchicalQpeLayout",
  "Qleisli.HierarchicalQpeRoot",
  "Qleisli.HierarchicalQpeSchedule",
  "Qleisli.HierarchicalRoot",
  "Qleisli.HierarchicalRoutedPower",
  "Qleisli.HierarchicalSemantics",
  "Qleisli.HierarchicalTensorCoordinates",
  "Qleisli.HierarchicalTyping",
  "Qleisli.HierarchicalUnitary",
  "Qleisli.HierarchicalWiring",
  "Qleisli.InstrumentCompleteExamples",
  "Qleisli.InstrumentExamples",
  "Qleisli.Interference",
  "Qleisli.Kraus",
  "Qleisli.NativeHierarchy",
  "Qleisli.NativeValidity",
  "Qleisli.Phi",
  "Qleisli.Qft",
  "Qleisli.QftGraph",
  "Qleisli.QftUnitary",
  "Qleisli.Qirf",
  "Qleisli.QirfValidity",
  "Qleisli.Qpe",
  "Qleisli.QpeComplete",
  "Qleisli.Raw",
  "Qleisli.RawBranchFunction",
  "Qleisli.RawCoefficient",
  "Qleisli.RawDenotation",
  "Qleisli.RawFunction",
  "Qleisli.RawInstrument",
  "Qleisli.RawInstrumentDenotation",
  "Qleisli.RawProtected",
  "Qleisli.RawProtectedEvaluation",
  "Qleisli.RawPure",
  "Qleisli.RawStreamedInstrument",
  "Qleisli.Resource",
  "Qleisli.Schema",
  "Qleisli.Scope",
  "Qleisli.SemanticContract",
  "Qleisli.Semantics.CoordinateOperators",
  "Qleisli.Semantics.Exact",
  "Qleisli.Semantics.Finite",
  "Qleisli.Semantics.FreshInitialization",
  "Qleisli.Semantics.Instrument",
  "Qleisli.Semantics.InstrumentComplete",
  "Qleisli.Semantics.InstrumentCoordinates",
  "Qleisli.Semantics.InstrumentPartitions",
  "Qleisli.Semantics.ObservingAction",
  "Qleisli.Semantics.ObservingFunction",
  "Qleisli.Semantics.Protected",
  "Qleisli.Semantics.ProtectedMatrix",
  "Qleisli.Semantics.Qirf",
  "Qleisli.Semantics.QpeFrames",
  "Qleisli.Semantics.Raw",
  "Qleisli.Semantics.RawAction",
  "Qleisli.Semantics.RawFunction",
  "Qleisli.Semantics.RawInstrument",
  "Qleisli.Semantics.RawPure",
  "Qleisli.Transition",
  "QleisliKernel",
  "QleisliKernel.Composition",
  "QleisliKernel.ControlledPowers",
  "QleisliKernel.Dag",
  "QleisliKernel.Exact",
  "QleisliKernel.ExactCapacity",
  "QleisliKernel.ExactMatrix",
  "QleisliKernel.Finite",
  "QleisliKernel.Hierarchical.Artifact",
  "QleisliKernel.Hierarchical.CallLowering",
  "QleisliKernel.Hierarchical.CircuitTrace",
  "QleisliKernel.Hierarchical.Conditional",
  "QleisliKernel.Hierarchical.ContractTyping",
  "QleisliKernel.Hierarchical.Derivation",
  "QleisliKernel.Hierarchical.Finite",
  "QleisliKernel.Hierarchical.FiniteBinding",
  "QleisliKernel.Hierarchical.FourierBase",
  "QleisliKernel.Hierarchical.FourierBody",
  "QleisliKernel.Hierarchical.FourierControl",
  "QleisliKernel.Hierarchical.FourierRoot",
  "QleisliKernel.Hierarchical.FourierStage",
  "QleisliKernel.Hierarchical.Gradient",
  "QleisliKernel.Hierarchical.Graph",
  "QleisliKernel.Hierarchical.Hadamard",
  "QleisliKernel.Hierarchical.Instrument",
  "QleisliKernel.Hierarchical.Limits",
  "QleisliKernel.Hierarchical.NodeTyping",
  "QleisliKernel.Hierarchical.Ports",
  "QleisliKernel.Hierarchical.Power",
  "QleisliKernel.Hierarchical.Preparation",
  "QleisliKernel.Hierarchical.QpeInstrument",
  "QleisliKernel.Hierarchical.QpeRoot",
  "QleisliKernel.Hierarchical.QpeSchedule",
  "QleisliKernel.Hierarchical.Readout",
  "QleisliKernel.Hierarchical.Root",
  "QleisliKernel.Hierarchical.RoutedPower",
  "QleisliKernel.Hierarchical.Rule",
  "QleisliKernel.Hierarchical.Structural",
  "QleisliKernel.Hierarchical.TypedRule",
  "QleisliKernel.Hierarchical.Wiring",
  "QleisliKernel.Hierarchy",
  "QleisliKernel.Interference",
  "QleisliKernel.Layout",
  "QleisliKernel.LayoutDag",
  "QleisliKernel.ObservationBinding",
  "QleisliKernel.PathSum",
  "QleisliKernel.PhaseLayout",
  "QleisliKernel.PhasePolynomial",
  "QleisliKernel.PhasePolynomial.Operations",
  "QleisliKernel.PhaseWord",
  "QleisliKernel.Qft",
  "QleisliKernel.QftGraph",
  "QleisliKernel.Qirf",
  "QleisliKernel.Qirf.Checked",
  "QleisliKernel.Qirf.Contract",
  "QleisliKernel.Qirf.Ownership",
  "QleisliKernel.Qirf.Validity",
  "QleisliKernel.Qpe",
  "QleisliKernel.Raw.BranchFunction",
  "QleisliKernel.Raw.Coefficient",
  "QleisliKernel.Raw.Finite",
  "QleisliKernel.Raw.Function",
  "QleisliKernel.Raw.Instrument",
  "QleisliKernel.Raw.Observation",
  "QleisliKernel.Raw.ObservationOwnership",
  "QleisliKernel.Raw.ObservationScope",
  "QleisliKernel.Raw.Ownership",
  "QleisliKernel.Raw.Protected",
  "QleisliKernel.Raw.ProtectedEvaluation",
  "QleisliKernel.Raw.Pure",
  "QleisliKernel.Raw.StreamedInstrument",
  "QleisliKernel.Raw.Structure",
  "QleisliKernel.Raw.Trace",
  "QleisliKernel.Reshape",
  "QleisliKernel.Schema",
  "QleisliKernel.Semantics.ClassicalScope",
  "QleisliKernel.Semantics.Exact",
  "QleisliKernel.Semantics.Finite",
  "QleisliKernel.Semantics.Function",
  "QleisliKernel.Semantics.Observation",
  "QleisliKernel.Semantics.ObservingFunction",
  "QleisliKernel.Semantics.Ownership",
  "QleisliKernel.Semantics.OwnershipLaws",
  "QleisliKernel.Semantics.PhaseWord",
  "QleisliKernel.Semantics.Preparation",
  "QleisliKernel.Semantics.Protected",
  "QleisliKernel.Semantics.Qirf",
  "QleisliKernel.Semantics.Raw",
  "QleisliKernel.Semantics.RawTrace",
  "QleisliKernel.Semantics.Readout",
  "QleisliKernel.Uniform",
  "SchemaExport",
  "Tests"]

-- External origins actually reached by that historical closure. Lean/Std are
-- pinned separately; unknown origins cannot create a new trusted boundary.
def externalModules : List String := [
  "Init.Control.Basic",
  "Init.Control.Except",
  "Init.Control.Id",
  "Init.Control.State",
  "Init.Core",
  "Init.Data.Array.Basic",
  "Init.Data.Array.Set",
  "Init.Data.ByteArray.Basic",
  "Init.Data.Cast",
  "Init.Data.Char.Basic",
  "Init.Data.Int.Basic",
  "Init.Data.Int.DivMod.Basic",
  "Init.Data.List.Basic",
  "Init.Data.List.Control",
  "Init.Data.Nat.Basic",
  "Init.Data.Nat.Bitwise.Basic",
  "Init.Data.Option.Basic",
  "Init.Data.Ord.Basic",
  "Init.Data.Ord.String",
  "Init.Data.String.Basic",
  "Init.Data.String.Defs",
  "Init.Data.String.Iterate",
  "Init.Data.String.Pattern.Basic",
  "Init.Data.String.Pattern.Char",
  "Init.Data.String.Pattern.Pred",
  "Init.Data.String.Pattern.String",
  "Init.Data.String.Search",
  "Init.Data.String.Slice",
  "Init.Data.String.TakeDrop",
  "Init.Data.ToString.Basic",
  "Init.Data.UInt.BasicAux",
  "Init.Data.Zero",
  "Init.GetElem",
  "Init.Prelude",
  "Lean.Data.Json.Basic",
  "Lean.Data.Json.Parser",
  "Std.Data.DTreeMap.Internal.Def",
  "Std.Data.DTreeMap.Raw.Basic",
  "Std.Data.TreeMap.Raw.Basic"]

def declarationJson (info : ConstantInfo) (project : Bool) : ExtractM Json := do
  let base := #[nameJson info.name, toJson (info.levelParams.map nameJson), ← exprJson info.type]
  if info.isUnsafe || info.isPartial then
    throw s!"unsafe or partial declaration in admitted meaning: {info.name}"
  match info with
  | .defnInfo value =>
    -- Traverse the actual checker implementation dependencies even though
    -- its body can vary. New helper/origin boundaries may not escape closure.
    if project && info.name == currentChecker then
      discard <| exprJson value.value
    let body ← if !project || info.name == currentChecker then
      pure (tagged (if project then "current-checker-body" else "pinned-toolchain-definition"))
    else exprJson value.value
    return tagged "definition" (base.push body)
  | .thmInfo _ => return tagged "theorem" base
  | .inductInfo value =>
    let types ← value.all.toArray.mapM referenced
    let ctors ← value.ctors.toArray.mapM referenced
    return tagged "inductive" (base ++ #[toJson value.numParams, toJson value.numIndices,
      toJson types, toJson ctors, toJson value.numNested, toJson value.isRec, toJson value.isReflexive])
  | .ctorInfo value =>
    return tagged "constructor" (base ++ #[← referenced value.induct, toJson value.cidx,
      toJson value.numParams, toJson value.numFields])
  | .recInfo value =>
    let types ← value.all.toArray.mapM referenced
    let rules ← value.rules.toArray.mapM fun rule => do
      return tagged "rule" #[← referenced rule.ctor, toJson rule.nfields, ← exprJson rule.rhs]
    return tagged "recursor" (base ++ #[toJson types, toJson value.numParams, toJson value.numIndices,
      toJson value.numMotives, toJson value.numMinors, toJson value.k, toJson rules])
  | .axiomInfo _ =>
    if project then throw s!"project axiom in admitted meaning: {info.name}"
    return tagged "pinned-toolchain-axiom" base
  | .opaqueInfo _ =>
    if project then throw s!"opaque project boundary in admitted meaning: {info.name}"
    return tagged "pinned-toolchain-opaque" base
  | .quotInfo value =>
    if project then throw "unexpected project quotient declaration"
    let kind := match value.kind with
      | .type => "type" | .ctor => "ctor" | .lift => "lift" | .ind => "ind"
    return tagged "pinned-toolchain-quotient" (base.push (toJson kind))

elab "#extract_qleisli_continuity" : command => do
  let env := (← getEnv).setExporting false
  let mut pending := roots.toList
  let mut seen : NameSet := {}
  let mut scheduled : NameSet := roots.foldl (fun found name => found.insert name) {}
  let mut entries : Array (String × Json) := #[]
  for _ in [:20000] do
    match pending with
    | [] => break
    | name :: rest =>
      pending := rest
      if seen.contains name then continue
      seen := seen.insert name
      let some info := env.find? name | throwError "missing required constant {name}"
      let some moduleIdx := env.getModuleIdxFor? name | throwError "unattributed declaration {name}"
      let moduleName := env.allImportedModuleNames[moduleIdx.toNat]!
      let project := historicalProjectModules.contains moduleName.toString
      unless project || externalModules.contains moduleName.toString do
        throwError "unrecognized declaration origin {moduleName} for {name}"
      let (decl, references) ← match (declarationJson info project).run #[] with
        | .ok value => pure value
        | .error error => throwError "{error}"
      -- External toolchain types are recorded at the project boundary. Their
      -- transitive implementations belong to the separately pinned Lean/Std.
      if project then
        for dependency in references do
          if !scheduled.contains dependency then
            scheduled := scheduled.insert dependency
            pending := dependency :: pending
      entries := entries.push (name.toString, Json.mkObj [
        ("name", nameJson name), ("module", nameJson moduleName),
        ("project", toJson project), ("declaration", decl)])
  unless pending.isEmpty do throwError "continuity closure exceeds conservative extraction capacity"
  let sorted := entries.qsort fun a b => a.1 < b.1
  let output := Json.mkObj [("format", toJson "qleisli.elaborated-continuity"), ("version", toJson (1 : Nat)),
    ("roots", toJson (roots.map nameJson)), ("declarations", toJson (sorted.map (·.2)))]
  liftIO <| IO.println output.compress
end QleisliContinuity

#extract_qleisli_continuity
