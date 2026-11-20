/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Epigraph normal decompositions and subdifferential regularity

The negative and zero-height slices describe every epigraph normal. When a
regular subgradient exists its recession cone provides the zero-height slice
of the regular normal cone.
-/

import RockafellarWets.Chapter8.HorizontalEpigraphNormals
import RockafellarWets.Chapter8.SupportPolarity
import RockafellarWets.Chapter8.SubderivativeRegularityCriterion

open Filter Set Topology
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {x v : E} {c b : ℝ}

omit [FiniteDimensional ℝ E] in
/-- Scaling a cone slice with negative height back to height −1. -/
private theorem mem_cone_iff_normalized_height {C : Set (WithLp 2 (E × ℝ))} (hC : IsCone C)
    (v : E) {b : ℝ} (hb : b < 0) :
    WithLp.toLp 2 (v,b) ∈ C ↔ WithLp.toLp 2 ((-b)⁻¹ • v,(-1:ℝ)) ∈ C := by
  have hscale : (-b)⁻¹ • WithLp.toLp 2 (v,b) = WithLp.toLp 2 ((-b)⁻¹ • v,(-1:ℝ)) := by
    apply WithLp.ofLp_injective
    ext <;> simp [hb.ne,smul_eq_mul]
  rw [← hscale]
  exact ⟨fun h ↦ hC.smul_mem h (inv_nonneg.mpr (neg_pos.mpr hb).le), fun h ↦ by
    simpa [smul_smul,hb.ne] using hC.smul_mem h (neg_pos.mpr hb).le⟩

/-- When a regular subgradient exists, its horizon cone is the polar of the
subderivative domain. -/
theorem horizonCone_regularSubdifferential_eq_polar (hx : f x = c)
    (hne : (regularSubdifferential f x).Nonempty) :
    horizonCone (regularSubdifferential f x) = polarCone (effectiveDomain (subderivative f x)) := by
  obtain ⟨hclosed,hconv,_⟩ := subdifferential_properties hx
  apply Subset.antisymm
  · rw [(horizonCone_polar_effectiveDomain_supportFunction hclosed hconv hne).1]
    apply polarCone_antitone
    intro w hw
    have hbound : supportFunction (regularSubdifferential f x) w ≤ subderivative f x w := (supportFunction_le_iff _ _ _).mpr fun u hu ↦
      inner_le_subderivative_of_mem_regularSubdifferential hu w
    exact hbound.trans_lt (show subderivative f x w < ⊤ from hw)
  · intro v hv
    obtain ⟨u,hu⟩ := hne
    apply mem_horizonCone_of_forall_smul_add_mem (x := u)
    intro t ht
    apply (mem_regularSubdifferential_iff_inner_le_subderivative hx).mpr
    intro w
    by_cases hw : subderivative f x w = ⊤
    · simp [hw]
    apply (EReal.coe_le_coe_iff.mpr ?_).trans (inner_le_subderivative_of_mem_regularSubdifferential hu w)
    rw [inner_add_left, real_inner_smul_left]
    linarith [mul_nonpos_of_nonneg_of_nonpos ht (hv w (lt_top_iff_ne_top.mpr hw))]

/-- **Theorem 8.9**, regular normal decomposition, in coordinates. -/
theorem mem_regularNormalCone_epigraph_iff_slices (hx : f x = c)
    (hne : (regularSubdifferential f x).Nonempty) :
    WithLp.toLp 2 (v,b) ∈ regularNormalCone (euclideanEpigraph f) (WithLp.toLp 2 (x,c)) ↔
      (b < 0 ∧ (-b)⁻¹ • v ∈ regularSubdifferential f x) ∨
      (b = 0 ∧ v ∈ horizonCone (regularSubdifferential f x)) := by
  have hp : WithLp.toLp 2 (x,c) ∈ euclideanEpigraph f := hx.le
  by_cases hb : b < 0
  · simp only [hb,hb.ne,true_and,false_and,or_false]
    exact (mem_cone_iff_normalized_height (C := regularNormalCone (euclideanEpigraph f)
      (WithLp.toLp 2 (x,c))) (isCone_regularNormalCone hp) v hb).trans
      (mem_regularSubdifferential_iff_epigraph_normal hx).symm
  · rcases eq_or_lt_of_le (le_of_not_gt hb) with h0 | hbpos
    · subst b
      simp [horizontal_regularNormal_iff_polar_subderivative_domain hx,
        horizonCone_regularSubdifferential_eq_polar hx hne]
    · simp only [hb,false_and,hbpos.ne',or_false,iff_false]
      exact fun hn ↦ hbpos.not_ge (vertical_nonpos_of_mem_regularNormalCone_epigraph hn)

/-- **Theorem 8.9**, limiting normal decomposition, in coordinates. -/
theorem mem_normalCone_epigraph_iff_slices (hl : IsLocallyLscAt f x) (hx : f x = c) :
    WithLp.toLp 2 (v,b) ∈ normalCone (euclideanEpigraph f) (WithLp.toLp 2 (x,c)) ↔
      (b < 0 ∧ (-b)⁻¹ • v ∈ subdifferential f x) ∨ (b = 0 ∧ v ∈ horizonSubdifferential f x) := by
  have hp : WithLp.toLp 2 (x,c) ∈ euclideanEpigraph f := hx.le
  by_cases hb : b < 0
  · simp only [hb,hb.ne,true_and,false_and,or_false]
    exact (mem_cone_iff_normalized_height (C := normalCone (euclideanEpigraph f)
      (WithLp.toLp 2 (x,c))) (isCone_normalCone hp) v hb).trans
      (mem_subdifferential_iff_epigraph_normal hx).symm
  · rcases eq_or_lt_of_le (le_of_not_gt hb) with h0 | hbpos
    · subst b
      simp [← mem_horizonSubdifferential_iff_epigraph_normal_of_locallyLsc hl hx]
    · simp only [hb,false_and,hbpos.ne',or_false,iff_false]
      exact fun hn ↦ hbpos.not_ge (vertical_nonpos_of_mem_normalCone_epigraph hn)

theorem IsSubdifferentiallyRegularAt.subdifferential_eq_regularSubdifferential
    (hr : IsSubdifferentiallyRegularAt f x) :
    subdifferential f x = regularSubdifferential f x := by
  have hx := (EReal.coe_toReal hr.2.1 hr.1).symm
  ext v
  rw [mem_subdifferential_iff_epigraph_normal hx, mem_regularSubdifferential_iff_epigraph_normal hx]
  exact hr.2.2.2 ▸ Iff.rfl

theorem IsSubdifferentiallyRegularAt.mem_horizonSubdifferential_iff_regularNormal
    (hr : IsSubdifferentiallyRegularAt f x) (hx : f x = c) :
    v ∈ horizonSubdifferential f x ↔ WithLp.toLp 2 (v,(0:ℝ)) ∈
      regularNormalCone (euclideanEpigraph f) (WithLp.toLp 2 (x,c)) := by
  rw [mem_horizonSubdifferential_iff_epigraph_normal_of_locallyLsc hr.isLocallyLscAt hx]
  have heq := hr.2.2.2
  rw [hx,EReal.toReal_coe] at heq
  exact heq ▸ Iff.rfl

/-- **Corollary 8.11.** At a finite point carrying a limiting subgradient,
regularity is equivalent to local lower semicontinuity and equality of both
subgradient slices. -/
theorem isSubdifferentiallyRegularAt_iff_subgradients (hx : f x = c)
    (hne : (subdifferential f x).Nonempty) :
    IsSubdifferentiallyRegularAt f x ↔ IsLocallyLscAt f x ∧
      subdifferential f x = regularSubdifferential f x ∧
      horizonSubdifferential f x = horizonCone (regularSubdifferential f x) := by
  constructor
  · intro hr
    have he := hr.subdifferential_eq_regularSubdifferential
    refine ⟨hr.isLocallyLscAt,he,?_⟩
    ext v
    rw [hr.mem_horizonSubdifferential_iff_regularNormal hx,
      horizontal_regularNormal_iff_polar_subderivative_domain hx,
      horizonCone_regularSubdifferential_eq_polar hx (he ▸ hne)]
  · rintro ⟨hl,he,heh⟩
    refine ⟨hl.1, hl.2.1, hl.isLocallyClosedAt_epigraph.preimage_continuousLinearEquiv
      (l2ProdEquiv E), ?_⟩
    rw [hx,EReal.toReal_coe]
    ext q
    obtain ⟨⟨v,b⟩,rfl⟩ := (WithLp.toLp_surjective 2) q
    change WithLp.toLp 2 (v,b) ∈ normalCone (euclideanEpigraph f) _ ↔ _ ∈ regularNormalCone (euclideanEpigraph f) _
    rw [mem_normalCone_epigraph_iff_slices hl hx,
      mem_regularNormalCone_epigraph_iff_slices hx (he ▸ hne),he,heh]

end RW
