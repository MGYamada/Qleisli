import Qleisli
import QuantumInfo.Measurements.POVM
import Lean.Util.CollectAxioms

/-!
Copyright 2026 Masahiko G. Yamada. Released under Apache-2.0.

Preserved optional probe for the formerly pinned Physlib v4.30.0 environment.
Not part of the current Lean dependency graph, default build, or CI.
See lean/README.md#future-physlib-bridge for reintroduction conditions and reproduction.

Check that the pinned QuantumInfo interfaces coexist with the Qleisli proof
library and that the selected external declarations use only the standard
logical axioms. This is a dependency integration check, not a formalization
of Qleisli source/IR semantics or an audit of all Physlib declarations.
Run separately after building the selected QuantumInfo modules.
-/

open Lean in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let roots := #[
    ``MState.traceLeft_prod_eq,
    ``MatrixMap.conj_isCompletelyPositive,
    ``CPTPMap.id,
    ``CPTPMap.prod,
    ``CPTPMap.traceLeft,
    ``CPTPMap.traceRight,
    ``POVM.measurementMap,
    ``POVM.measurementMap_apply_matrix]
  let mut used : Array Name := #[]
  for name in roots do
    for axiomName in ← collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on forbidden axiom {axiomName}"
      unless used.contains axiomName do
        used := used.push axiomName
  logInfo m!"Audited {roots.size} Physlib declarations; axioms used: {used}"
