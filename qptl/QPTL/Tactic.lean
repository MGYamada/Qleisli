/-
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
-/
import QPTL.Tensor
import Lean.Elab.Tactic.SolveByElim

/-! Bounded proof search for structural isometry and unitarity goals. -/

namespace QPTL

/-- Close a structural goal using local evidence, composition, tensor and dagger
laws. The second branch normalizes equalities of dagger expressions. -/
macro "qptl" : tactic =>
  `(tactic| first
    | solve_by_elim (maxDepth := 12) only [*, @IsIsometry.id, @IsIsometry.comp, @IsIsometry.tensor,
        @IsUnitary.id, @IsUnitary.comp, @IsUnitary.tensor, @IsUnitary.dagger, @IsUnitary.isometry]
    | solve | simp only [DaggerCategory.dagger_id, DaggerCategory.dagger_comp,
        DaggerCategory.dagger_dagger, DaggerMonoidalCategory.dagger_tensor,
        CategoryTheory.Category.id_comp, CategoryTheory.Category.comp_id, CategoryTheory.Category.assoc])

end QPTL
