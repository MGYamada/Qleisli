import Qleisli
import Lean.Util.CollectAxioms

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
