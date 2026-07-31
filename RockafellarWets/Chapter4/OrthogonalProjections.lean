/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Convergence of Orthogonal Projections

This file proves Theorem 4.28 from the total linear-image theorem.
-/

import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import RockafellarWets.Chapter4.TotalConvergenceAutomaticCompletion
import RockafellarWets.Chapter4.TotalLinearImages

open Set

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **Theorem 4.28.** Orthogonal projections preserve convergence of convex
sets when the orthogonal complement of the target subspace meets the horizon
cone of the nonempty limit only at the origin. -/
theorem PKConverges.starProjection_of_convex
    {Cseq : ℕ → Set E} {C : Set E} (hC : PKConverges Cseq C)
    (hCne : C.Nonempty) (hconv : ∀ n, Convex ℝ (Cseq n))
    (M : Submodule ℝ E)
    (htrans : ((Mᗮ : Set E) ∩ horizonCone C) = ({0} : Set E)) :
    PKConverges (fun n ↦ M.starProjection '' Cseq n)
      (M.starProjection '' C) := by
  have htotal : TotalConverges Cseq C :=
    totalConverges_of_convex hC hCne hconv
  have hker : ∀ ⦃v : E⦄,
      v ∈ horizonCone C → M.starProjection.toLinearMap v = 0 → v = 0 := by
    intro v hvC hvProjection
    have hvOrth : v ∈ (Mᗮ : Set E) := by
      rw [← M.ker_starProjection]
      exact hvProjection
    have hvZero : v ∈ ({0} : Set E) := by
      rw [← htrans]
      exact ⟨hvOrth, hvC⟩
    simpa only [Set.mem_singleton_iff] using hvZero
  exact (htotal.linear_image M.starProjection.toLinearMap hker).pkConverges

end RW
