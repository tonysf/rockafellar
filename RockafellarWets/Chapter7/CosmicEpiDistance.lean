/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 7: Cosmic epi-distance
-/

import RockafellarWets.Chapter4.TotalLinearImages
import RockafellarWets.Chapter4.TotalSetMetric
import RockafellarWets.Chapter7.EpiDistances
import RockafellarWets.Chapter7.TotalEpiConvergence

open Filter Set Topology

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem totalConverges_preimage_linearEquiv_iff {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (T : E ≃ₗ[ℝ] F) {C : ℕ → Set F} {D : Set F} :
    TotalConverges (fun n ↦ T ⁻¹' C n) (T ⁻¹' D) ↔ TotalConverges C D := by
  constructor
  · intro h
    have hi := h.linear_image T.toLinearMap (fun _ _ h0 ↦ T.map_eq_zero_iff.mp h0)
    change TotalConverges (fun n ↦ T '' (T ⁻¹' C n)) (T '' (T ⁻¹' D)) at hi
    simpa only [T.surjective.image_preimage] using hi
  · intro h
    have hi := h.linear_image T.symm.toLinearMap (fun _ _ h0 ↦ T.symm.map_eq_zero_iff.mp h0)
    change TotalConverges (fun n ↦ T.symm '' C n) (T.symm '' D) at hi
    simpa only [LinearEquiv.image_eq_preimage_symm, LinearEquiv.symm_symm] using hi

theorem totalEpiConverges_iff_euclideanEpigraph {f : ℕ → E → EReal} {g : E → EReal} :
    TotalEpiConverges f g ↔
      TotalConverges (fun n ↦ euclideanEpigraph (f n)) (euclideanEpigraph g) :=
  (totalConverges_preimage_linearEquiv_iff
    (WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ).toLinearEquiv).symm

namespace LscFunctionModel

def closedEpigraph (f : LscFunctionModel E) : TopologicalSpace.Closeds (WithLp 2 (E × ℝ)) :=
  ⟨euclideanEpigraph f.toFun, isClosed_euclideanEpigraph f.lowerSemicontinuous⟩

/-- Formula 7(28). The cosmic set distance compares the closed epigraphs
in the cosmic compactification of the Euclidean product. -/
noncomputable def cosmicEpiDistance (f g : LscFunctionModel E) : ℝ :=
  totalSetDistance f.closedEpigraph g.closedEpigraph

/-- **Theorem 7.59**, the metric for total epi-convergence. This is a named
metric because the same functions carry the integrated epi-metric of 7.58. -/
noncomputable def cosmicMetric : MetricSpace (LscFunctionModel E) where
  dist := cosmicEpiDistance
  dist_self f := totalSetDistance_self _
  dist_comm f g := totalSetDistance_comm _ _
  dist_triangle f g h := totalSetDistance_triangle _ _ _
  eq_of_dist_eq_zero {f g} h := by
    apply toSetMetricModel_injective
    apply SetMetricModel.carrier_injective
    exact congrArg (fun S : TopologicalSpace.Closeds (WithLp 2 (E × ℝ)) ↦ (S : Set (WithLp 2 (E × ℝ))))
      (totalSetDistance_eq_zero_iff.mp h)

/-- **Theorem 7.59**, convergence in the cosmic epi-distance. -/
theorem totalEpiConverges_iff_tendsto_cosmicEpiDistance {f : ℕ → LscFunctionModel E}
    {g : LscFunctionModel E} :
    TotalEpiConverges (fun n ↦ (f n).toFun) g.toFun ↔
      Tendsto (fun n ↦ cosmicEpiDistance (f n) g) atTop (𝓝 0) :=
  totalEpiConverges_iff_euclideanEpigraph.trans
    (totalConverges_iff_tendsto_totalSetDistance
      (Cseq := fun n ↦ (f n).closedEpigraph) (C := g.closedEpigraph))

end LscFunctionModel
end RW
