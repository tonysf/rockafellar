/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Subgradients of a subderivative
-/

import RockafellarWets.Chapter8.CalmSubgradients
import RockafellarWets.Chapter8.HorizontalEpigraphNormals
import RockafellarWets.Chapter8.SubderivativeRegularityCriterion

open Set

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {x : E} {c : ℝ}

/-- **Exercise 8.44(b)**, with the finite value needed at the vertex of the
subderivative. The first inclusions fail without this condition, as shown
by the continuous downward cusp. -/
theorem subdifferentials_subderivative_vertex (hx : f x = c) (hl : IsLocallyLscAt f x)
    (h₀ : subderivative f x 0 = 0) (w : E) :
    let h := subderivative f x
    (subdifferential h w ⊆ subdifferential h 0 ∧ subdifferential h 0 ⊆ subdifferential f x) ∧
    (horizonSubdifferential h w ⊆ horizonSubdifferential h 0 ∧
      horizonSubdifferential h 0 ⊆ horizonSubdifferential f x) := by
  let h := subderivative f x
  have hz : h 0 = ((0:ℝ):EReal) := h₀
  have hfinite : WithLp.toLp 2 (x,c) ∈ euclideanEpigraph f := hx.le
  have hclosed : IsClosed (epigraph h) := isClosed_epigraph_of_lsc_ereal _
    (lowerSemicontinuous_positivelyHomogeneous_subderivative hx).1
  have hl₀ := isLocallyLscAt_of_isLocallyClosedAt_epigraph hz (RW.IsClosed.isLocallyClosedAt hclosed _)
  have hcone : IsCone (euclideanEpigraph h) := by rw [euclideanEpigraph_subderivative hx]; exact isCone_tangentCone hfinite
  have hcl : IsClosed (euclideanEpigraph h) := hclosed.preimage (l2ProdEquiv E).continuous
  have hbase : IsLocallyClosedAt (euclideanEpigraph f) (WithLp.toLp 2 (x,c)) := by
    have hc := hl.isLocallyClosedAt_epigraph
    rw [hx,EReal.toReal_coe] at hc
    exact IsLocallyClosedAt.preimage_continuousLinearEquiv (l2ProdEquiv E) hc
  refine ⟨⟨?_,subdifferential_subderivative_subset_of_localLsc hl hz⟩,?_,?_⟩
  · intro v hv
    obtain ⟨b,hb⟩ := hv.1
    have hn := (mem_subdifferential_iff_epigraph_normal hb).mp hv
    apply (mem_subdifferential_iff_epigraph_normal hz).mpr
    exact normalCone_subset_normalCone_zero_of_isCone hcl hcone _ hn
  · intro v hv
    obtain ⟨b,hb⟩ := hv.1
    apply (mem_horizonSubdifferential_iff_epigraph_normal_of_locallyLsc hl₀ hz).mpr
    exact normalCone_subset_normalCone_zero_of_isCone hcl hcone _ (horizontal_normal_of_mem_horizonSubdifferential hb hv)
  · intro v hv
    have hn := horizontal_normal_of_mem_horizonSubdifferential hz hv
    rw [euclideanEpigraph_subderivative hx] at hn
    exact (mem_horizonSubdifferential_iff_epigraph_normal_of_locallyLsc hl hx).mpr
      (normalCone_tangentCone_subset hfinite hbase _ hn)

end RW
