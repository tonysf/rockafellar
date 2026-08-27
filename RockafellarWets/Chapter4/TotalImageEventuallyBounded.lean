/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Total Convergence of Eventually Bounded Images

The total-convergence conclusion in the final paragraph following Theorem 4.26.
-/

import RockafellarWets.Chapter4.ImageLimits
import RockafellarWets.Chapter4.TotalConvergence

open Filter Metric Set Topology

namespace RW

section TotalImageEventuallyBounded

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
/-- Continuous images of an eventually bounded sequence in finite-dimensional
spaces are eventually bounded. -/
theorem EventuallyBounded.image_of_continuous
    {C : ℕ → Set E} {G : E → F} (hC : EventuallyBounded C)
    (hG : Continuous G) : EventuallyBounded (fun n ↦ G '' C n) := by
  rcases hC with ⟨r, N, hC⟩
  have hbdd : Bornology.IsBounded (G '' closedBall (0 : E) r) :=
    ((isCompact_closedBall (0 : E) r).image hG).isBounded
  rcases (Metric.isBounded_iff_subset_closedBall (0 : F)).1 hbdd with ⟨R, hR⟩
  refine ⟨R, N, fun n hn ↦ ?_⟩
  rintro y ⟨x, hx, rfl⟩
  exact hR ⟨x, hC n hn hx, rfl⟩

/-- **Theorem 4.26 (final total-convergence paragraph).** If the source
sequence is eventually bounded, a continuous map preserves its total
convergence. -/
theorem TotalConverges.image_of_eventuallyBounded
    {C : ℕ → Set E} {D : Set E} {G : E → F}
    (hC : TotalConverges C D) (hG : Continuous G)
    (hbdd : EventuallyBounded C) :
    TotalConverges (fun n ↦ G '' C n) (G '' D) := by
  have hImagePK : PKConverges (fun n ↦ G '' C n) (G '' D) :=
    hC.pkConverges.image_of_eventuallyBounded hG hbdd
  have hImageBounded : EventuallyBounded (fun n ↦ G '' C n) :=
    hbdd.image_of_continuous hG
  apply totalConverges_iff_pkConverges_and_horizonOuter_subset.2
  refine ⟨hImagePK, ?_⟩
  rw [(horizonOuterSetLimit_eq_singleton_zero_iff_eventuallyBounded
    (fun n ↦ G '' C n)).2 hImageBounded]
  exact Set.singleton_subset_iff.mpr (zero_mem_horizonCone (G '' D))

end TotalImageEventuallyBounded

end RW
