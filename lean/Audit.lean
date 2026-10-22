import Qleisli
import Lean.Util.CollectAxioms
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr
import Lean.Compiler.NoncomputableAttr
import Lean.Compiler.CSimpAttr
import Lean.Elab.Command

/-!
Check transitive dependencies of every declaration in the imported project
modules, including generated declarations and private helpers. The allowlist consists
only of Lean's standard logical axioms; proof holes and native evaluation
axioms are rejected. This command is run separately after the library build.
-/

open Lean in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked := 0
  let mut used : Array Name := #[]
  for (name, _) in env.constants.toList do
    let fromProject := match env.getModuleIdxFor? name with
      | some idx => (`Qleisli).isPrefixOf env.header.moduleNames[idx.toNat]!
      | none => (`Qleisli).isPrefixOf name
    if fromProject then
      checked := checked + 1
      for axiomName in ← collectAxioms name do
        unless allowed.contains axiomName do
          throwError "{name} depends on forbidden axiom {axiomName}"
        unless used.contains axiomName do
          used := used.push axiomName
  if checked == 0 then
    throwError "No Qleisli declarations were audited"
  logInfo m!"Audited {checked} Qleisli declarations; axioms used: {used}"

/-!
Audit the ordinary-value definitions and their examples by compiled module
ownership, including private and generated helpers. Exact direct imports,
executable definitions and the stated theorem premises remain checked.
This audit supplies neither typed replay nor source preservation, semantic
adequacy review or constitutional admission.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
-/

-- Use compiled module ownership, not declaration prefixes: private names and
-- generated deriving helpers need not have a public semantic namespace prefix.
open Lean in
run_cmd do
  let env ← getEnv
  let targetModules := #[`QleisliKernel.Semantics.OrdinaryValue,
    `Qleisli.Semantics.OrdinaryValue, `Qleisli.OrdinaryValueExamples, `Qleisli.OrdinaryValueRawExamples]
  let allowedAxioms := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut present : NameSet := {}
  let mut checked := 0
  let mut failures : Array String := #[]
  let mut rows : Array Json := #[]
  let expectedImports := #[
    (`QleisliKernel.Semantics.OrdinaryValue, #[`QleisliKernel.Semantics.FiniteCarrier]),
    (`Qleisli.Semantics.OrdinaryValue,
      #[`QleisliKernel.Semantics.OrdinaryValue, `Qleisli.Semantics.RawInstrument]),
    (`Qleisli.OrdinaryValueExamples, #[`QleisliKernel.Semantics.OrdinaryValue]),
    (`Qleisli.OrdinaryValueRawExamples, #[`Qleisli.Semantics.OrdinaryValue])]
  for (moduleName, expected) in expectedImports do
    match env.getModuleIdx? moduleName with
    | none => failures := failures.push s!"Missing target module {moduleName}"
    | some idx =>
      let actual := (env.header.moduleData[idx]!.imports.map (·.module)).filter (· != `Init)
      unless actual == expected do
        failures := failures.push s!"{moduleName}: unexpected direct imports {actual}"
  for (name, info) in env.constants.toList do
    let owner := (env.getModuleIdxFor? name).map (fun idx => env.header.moduleNames[idx.toNat]!)
    if let some moduleName := owner then
      if targetModules.contains moduleName then
        checked := checked + 1
        present := present.insert moduleName
        if info.isUnsafe then failures := failures.push s!"{name}: unsafe declaration"
        if info.isPartial then failures := failures.push s!"{name}: partial declaration"
        if isNoncomputable env name then failures := failures.push s!"{name}: noncomputable declaration"
        if (Compiler.getImplementedBy? env name).isSome then
          failures := failures.push s!"{name}: implemented_by replacement"
        if (getExternAttrData? env name).isSome then
          failures := failures.push s!"{name}: extern implementation"
        if Compiler.hasCSimpAttribute env name then
          failures := failures.push s!"{name}: compiler-simplification replacement"
        if let .axiomInfo _ := info then failures := failures.push s!"{name}: project axiom"
        let axioms ← collectAxioms name
        for axiomName in axioms do
          unless allowedAxioms.contains axiomName do
            failures := failures.push s!"{name}: forbidden transitive axiom {axiomName}"
        rows := rows.push (Json.mkObj [
          ("name",toJson name.toString), ("module",toJson moduleName.toString),
          ("unsafe",toJson info.isUnsafe), ("partial",toJson info.isPartial),
          ("axioms",toJson (axioms.toList.map Name.toString))])
  for moduleName in targetModules do
    unless present.contains moduleName do
      failures := failures.push s!"No declarations audited for {moduleName}"
  -- Emit the full observed inventory even if a generated/private helper fails.
  IO.println <| (Json.mkObj [
    ("format",toJson "qleisli.ordinary-value-audit"), ("version",toJson (1 : Nat)),
    ("checked",toJson checked), ("declarations",Json.arr rows),
    ("failures",toJson failures), ("status",toJson (if failures.isEmpty then "pass" else "fail"))]).compress
  unless failures.isEmpty do
    throwError "Ordinary-value declaration audit failed: {failures}"

-- Exact type assertions for every authored core/bridge theorem. These check
-- the compiled statements, including all premises and the actual Raw action;
-- they are not theorem aliases with inferred result types.
section CoreStatements
open QleisliKernel.Semantics.FiniteCarrier
open QleisliKernel.Semantics.OrdinaryValue

example : ∀ {values : Valuation} {ids : List Nat} {bits : List Bool},
    Reads values ids bits → ids.length = bits.length := @Reads.lengths
example : ∀ {values : Valuation} {ids : List Nat} {a b : List Bool},
    Reads values ids a → Reads values ids b → a = b := @Reads.unique
example : ∀ before extra : Valuation, Extends before (before ++ extra) := append_extends
example : ∀ {before : Valuation} {id : Nat} (bit : Bool),
    lookup before id = none → lookup (before ++ [(id,bit)]) id = some bit := @lookup_append_fresh
example : ∀ {before after : Valuation} {ids : List Nat} {bits : List Bool},
    Reads before ids bits → Extends before after → Reads after ids bits := @Reads.extends
example : ∀ {bases : List Basis} {values : List Value},
    ValuesOf bases values → bases.length = values.length := @ValuesOf.lengths
example : ∀ {origin : Origin} {names : List String} {tail : Basis} {fields : List (String × Value)},
    ValueOf (.record origin names :: tail) (.record origin fields) →
      fields.map Prod.fst = names := @ValueOf.record_names
example : ∀ {values : Valuation} {basis : Basis} {value : Value} {storage : Storage},
    Represents values basis value storage → ValueOf basis value := @Represents.typed
example : ∀ {values : Valuation} {bases : List Basis} {items : List Value} {storage : List Storage},
    RepresentsMany values bases items storage → ValuesOf bases items := @RepresentsMany.typed
example : ∀ {before after : Valuation} {basis : Basis} {value : Value} {storage : Storage},
    Represents before basis value storage → Extends before after →
      Represents after basis value storage := @Represents.extends
example : ∀ {before after : Valuation} {bases : List Basis} {items : List Value} {storage : List Storage},
    RepresentsMany before bases items storage → Extends before after →
      RepresentsMany after bases items storage := @RepresentsMany.extends
example : ∀ {values : Valuation} {basis : Basis} {value : Value} {storage : Storage},
    Represents values basis value storage →
      Represents values (.pair :: (basis ++ basis)) (.pair value value) (.pair storage storage) :=
  @Represents.copy
example : ∀ {values : Valuation} {bases : List Basis} {items : List Value} {stores : List Storage},
    RepresentsMany values bases items stores → ∀ index : Nat,
      ∀ {basis : Basis} {value : Value} {storage : Storage},
        bases[index]? = some basis → items[index]? = some value → stores[index]? = some storage →
          Represents values basis value storage := @RepresentsMany.get
example : ∀ {origin : Origin} {variants : List String} {ordinal : Nat},
    ValueOf [.enumeration origin variants] (.enumeration origin ordinal) →
      ordinal < variants.length := @ValueOf.enum_range
example : ∀ {wanted actual : Origin} {variants : List String} {ordinal : Nat},
    ValueOf [.enumeration wanted variants] (.enumeration actual ordinal) →
      wanted = actual := @ValueOf.enum_identity
end CoreStatements

section RawStatements
open QleisliKernel.Semantics
open QleisliKernel.Semantics.FiniteCarrier
open QleisliKernel.Semantics.OrdinaryValue
open Qleisli.Semantics.RawInstrument
open Qleisli.Semantics.OrdinaryValue

example : ∀ (values : Valuation) (id : Nat),
    lookup values id = Qleisli.Semantics.RawInstrument.value values id := lookup_actual
example : ∀ (choice : Bool) (phis : List Observation.ClassicalPhi) (history : History),
    Qleisli.Semantics.RawInstrument.merged choice phis history =
      (phiBindings choice phis history.values).map
        (fun added => {history with values := history.values ++ added}) := merged_actual
example : ∀ {basis : Basis} {logical : Value} {storage : Storage} (initial : History)
    (dependencies : List Finite.Dependency) (expr : Observation.Expr) (output : Nat) (result : Bool),
    Represents initial.values basis logical storage →
    Qleisli.Semantics.RawInstrument.expression initial.values expr = some result →
    lookup initial.values output = none →
    let next := {initial with values := initial.values ++ [(output,result)]}
    Action dependencies (.classical expr output) initial [next] ∧
      Represents next.values basis logical storage ∧
      Represents next.values [.bit] (.bit result) (.bit output) ∧
      next.hidden = initial.hidden ∧ next.operator = initial.operator := @classical_preserves
example : ∀ {basis : Basis} {logical : Value} {storage : Storage} (before after : History)
    (choice : Bool) (phis : List Observation.ClassicalPhi),
    Represents before.values basis logical storage →
    Qleisli.Semantics.RawInstrument.merged choice phis before = some after →
    Represents after.values basis logical storage ∧
      after.hidden = before.hidden ∧ after.operator = before.operator := @merged_preserves
example : ∀ (fuel : Nat) (frame : RawTrace.Interface) (bit : Bool) (id : Nat),
    Observation.readOps (fuel + 1) frame [.constant bit id] =
      some (frame,[.classical (.constant bit) id]) := read_constant_frame
end RawStatements

-- Expose the independent meanings and constructor obligations for review.
set_option pp.universes true
set_option pp.fullNames true
set_option pp.explicit true
set_option pp.proofs false
set_option format.width 120

#print QleisliKernel.Semantics.OrdinaryValue.Valuation
#print QleisliKernel.Semantics.OrdinaryValue.lookup
#print QleisliKernel.Semantics.OrdinaryValue.littleEndian
#print QleisliKernel.Semantics.OrdinaryValue.Value
#print QleisliKernel.Semantics.OrdinaryValue.Storage
#print QleisliKernel.Semantics.OrdinaryValue.Reads
#print QleisliKernel.Semantics.OrdinaryValue.Extends
#print QleisliKernel.Semantics.OrdinaryValue.ValueOf
#print QleisliKernel.Semantics.OrdinaryValue.ValuesOf
#print QleisliKernel.Semantics.OrdinaryValue.Represents
#print QleisliKernel.Semantics.OrdinaryValue.RepresentsMany
#print Qleisli.Semantics.OrdinaryValue.phiBindings
