/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Convergence of finite unions

This file completes Exercise 4.31 by adding the total-convergence clause to
the ordinary-convergence result in `FiniteUnions`.
-/

import RockafellarWets.Chapter4.FiniteUnions
import RockafellarWets.Chapter4.TotalConvergence

open Filter Function Set Topology

namespace RW

section UnionConvergence

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Finite ι]

omit [FiniteDimensional ℝ E] [Finite ι] in
private theorem cosmicSet_iUnion_zero (C : ι → Set E) :
    cosmicSet (⋃ i, C i) ({0} : Set E) =
      ⋃ i, cosmicSet (C i) ({0} : Set E) := by
  simp only [cosmicSet, cosmicDirections_zero, union_empty, image_iUnion]

omit [FiniteDimensional ℝ E] in
/-- **Exercise 4.31 (total convergence).** A finite union of totally
convergent set sequences totally converges to the union of the limits. -/
theorem totalConverges_iUnion {C : ι → ℕ → Set E} {D : ι → Set E}
    (h : ∀ i, TotalConverges (C i) (D i)) :
    TotalConverges (fun n ↦ ⋃ i, C i n) (⋃ i, D i) := by
  have hDclosed : IsClosed (⋃ i, D i) :=
    isClosed_iUnion_of_finite fun i ↦ (h i).1
  refine ⟨hDclosed, ?_⟩
  have hcosmic := pkConverges_iUnion (fun i ↦ (h i).2)
  have hseq :
      ordinaryCosmicSequence (fun n ↦ ⋃ i, C i n) =
        (fun n ↦ ⋃ i, ordinaryCosmicSequence (C i) n) := by
    funext n
    exact cosmicSet_iUnion_zero (fun i ↦ C i n)
  have hlimit :
      closure (cosmicSet (⋃ i, D i) ({0} : Set E)) =
        ⋃ i, closure (cosmicSet (D i) ({0} : Set E)) := by
    rw [cosmicSet_iUnion_zero]
    exact closure_iUnion_of_finite _
  rw [hseq, hlimit]
  exact hcosmic

end UnionConvergence

end RW
