/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: Exact modulus in terms of subgradients
-/

import RockafellarWets.Chapter9.StrictContinuityCriteria

open Filter Function Metric Set Topology Bornology
open scoped ENNReal NNReal InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {x w : E}

theorem ERealStrictlyContinuousAt.subdifferential_nonempty_compact (h : ERealStrictlyContinuousAt f x) :
    (subdifferential f x).Nonempty ∧ IsCompact (subdifferential f x) :=
  subdifferential_nonempty_compact_of_horizon_eq_zero h.finite h.isLocallyLscAt
    ((eRealStrictlyContinuousAt_iff_horizonSubdifferential_eq_zero h.finite h.isLocallyLscAt).mp h)

theorem ERealStrictlyContinuousAt.regularSubderivative_eq_supportFunction (h : ERealStrictlyContinuousAt f x) (w : E) :
    regularSubderivative f x w = supportFunction (subdifferential f x) w := by
  apply regularSubderivative_eq_supportFunction_of_mem_polar h.finite h.isLocallyLscAt
  rw [(eRealStrictlyContinuousAt_iff_horizonSubdifferential_eq_zero h.finite h.isLocallyLscAt).mp h,
    polarCone_singleton_zero]
  trivial

/-- **Exercise 9.15**, the maximum representation, including attainment. -/
theorem ERealStrictlyContinuousAt.exists_max_inner_subdifferential (h : ERealStrictlyContinuousAt f x) (w : E) :
    ∃ v ∈ subdifferential f x, regularSubderivative f x w = (⟪v,w⟫_ℝ : EReal) ∧
      ∀ z ∈ subdifferential f x, ⟪z,w⟫_ℝ ≤ ⟪v,w⟫_ℝ := by
  obtain ⟨hne, hcomp⟩ := h.subdifferential_nonempty_compact
  obtain ⟨v, hv, hmax⟩ := hcomp.exists_isMaxOn hne
    ((continuous_id.inner continuous_const : Continuous (fun z : E ↦ ⟪z,w⟫_ℝ)).continuousOn)
  rw [h.regularSubderivative_eq_supportFunction]
  exact ⟨v, hv, le_antisymm ((supportFunction_le_iff _ _ _).mpr fun z hz ↦
    EReal.coe_le_coe_iff.mpr (hmax hz)) (inner_le_supportFunction hv w), isMaxOn_iff.mp hmax⟩

theorem ERealStrictlyContinuousAt.regularSubderivative_eq_upperDirectionalSlope (h : ERealStrictlyContinuousAt f x) (w : E) :
    regularSubderivative f x w = upperDirectionalSlope f x w := by
  apply RW.regularSubderivative_eq_upperDirectionalSlope h.finite h.isLocallyLscAt
  rw [← interior_effectiveDomain_regularSubderivative h.finite h.isLocallyLscAt]
  have hdom : effectiveDomain (regularSubderivative f x) = univ := eq_univ_iff_forall.mpr fun v ↦ by
    obtain ⟨r,hr⟩ := ((eRealStrictlyContinuousAt_iff_regularSubderivative_finite h.finite h.isLocallyLscAt).mp h) v
    change regularSubderivative f x v < ⊤
    exact hr ▸ EReal.coe_lt_top _
  rw [hdom, interior_univ]
  trivial

omit [FiniteDimensional ℝ E] in
theorem ERealStrictlyContinuousAt.nnnorm_le_modulus_of_mem_subdifferential (h : ERealStrictlyContinuousAt f x)
    {v : E} (hv : v ∈ subdifferential f x) : (‖v‖₊ : ℝ≥0∞) ≤ lipschitzModulus (fun y ↦ (f y).toReal) x := by
  by_contra! hn
  obtain ⟨k, hk, hk'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hn
  obtain ⟨U, hu, hU, hfin, hL⟩ := h.exists_lipschitzOnWith hk
  have hb := norm_le_of_mem_subdifferential_of_lipschitzOnWith hU hfin hL (mem_of_mem_nhds hu) hv
  exact (ENNReal.coe_lt_coe.mp hk').not_ge (show ‖v‖₊ ≤ k from hb)

/-- Compactness of the unit sphere turns directional strict inequalities
into a uniform local Lipschitz bound. -/
private theorem modulus_le_of_upperDirectionalSlope_lt (h : ERealStrictlyContinuousAt f x) {k : ℝ≥0}
    (hk : ∀ w : E, ‖w‖ = 1 → upperDirectionalSlope f x w < (k : ℝ)) :
    lipschitzModulus (fun y ↦ (f y).toReal) x ≤ (k : ℝ≥0∞) := by
  let S := sphere (0 : E) 1
  let L := attentiveNhds f x ×ˢ 𝓝[>] (0 : ℝ)
  have hall : {p : (E × ℝ) × E | differenceQuotient f p.1.1 p.1.2 p.2 < (k : ℝ)} ∈ L ×ˢ 𝓝ˢ S :=
    (isCompact_sphere (0 : E) 1).mem_prod_nhdsSet_of_forall fun w hw ↦
      eventually_lt_of_limsup_lt (hk w (mem_sphere_zero_iff_norm.mp hw))
  obtain ⟨P, hP, W, hW, hPW⟩ := mem_prod_iff.mp hall
  obtain ⟨Y, hY, T, hT, hYT⟩ := mem_prod_iff.mp hP
  rw [h.attentiveNhds_eq] at hY
  obtain ⟨d, hd, hdT⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hT
  obtain ⟨r, hr, hrY⟩ := Metric.mem_nhds_iff.mp (inter_mem hY h.1)
  let δ := min r (d/2)
  have hδ : 0 < δ := lt_min hr (half_pos hd)
  have hinc {y z : E} (hy : y ∈ ball x δ) (hz : z ∈ ball x δ) :
      (f z).toReal - (f y).toReal ≤ k * dist z y := by
    rcases eq_or_ne z y with rfl | hne
    · simp
    let t := dist z y
    have ht : 0 < t := dist_pos.mpr hne
    have ht' : t < d := by
      have hy' := (mem_ball.mp hy).trans_le (min_le_right r (d/2))
      have hz' := (mem_ball.mp hz).trans_le (min_le_right r (d/2))
      dsimp [t]
      linarith [dist_triangle z x y, dist_comm x y]
    let v := t⁻¹ • (z-y)
    have hv : v ∈ S := by
      apply mem_sphere_zero_iff_norm.mpr
      rw [show ‖v‖ = |t⁻¹| * ‖z-y‖ from norm_smul .., abs_of_pos (inv_pos.mpr ht), ← dist_eq_norm]
      exact inv_mul_cancel₀ ht.ne'
    have hy' := hrY ((mem_ball.mp hy).trans_le (min_le_left r (d/2)))
    have hz' := hrY ((mem_ball.mp hz).trans_le (min_le_left r (d/2)))
    have hq := hPW (a := ((y,t),v)) ⟨hYT ⟨hy'.1, hdT ⟨ht,ht'⟩⟩, subset_of_mem_nhdsSet hW hv⟩
    have hh := (differenceQuotient_le_coe_iff hy'.2 ht).mp hq.le
    rw [show y + t • v = z by simp [v, smul_smul, ht.ne'], hz'.2, EReal.coe_le_coe_iff] at hh
    linarith [mul_comm t (k : ℝ)]
  apply lipschitzModulus_le (ball_mem_nhds x hδ) (LipschitzOnWith.of_dist_le_mul ?_)
  intro y hy z hz
  rw [Real.dist_eq, abs_le]
  have h1 := hinc hy hz
  rw [dist_comm z y] at h1
  exact ⟨by linarith, hinc hz hy⟩

/-- **Theorem 9.13**, the sharp modulus and its attainment by a limiting subgradient. -/
theorem ERealStrictlyContinuousAt.exists_subgradient_norm_eq_modulus (h : ERealStrictlyContinuousAt f x) :
    ∃ v ∈ subdifferential f x, lipschitzModulus (fun y ↦ (f y).toReal) x = (‖v‖₊ : ℝ≥0∞) ∧
      ∀ z ∈ subdifferential f x, ‖z‖ ≤ ‖v‖ := by
  obtain ⟨hne, hcomp⟩ := h.subdifferential_nonempty_compact
  obtain ⟨v, hv, hmax⟩ := hcomp.exists_isMaxOn hne continuous_norm.continuousOn
  refine ⟨v, hv, le_antisymm ?_ (h.nnnorm_le_modulus_of_mem_subdifferential hv), isMaxOn_iff.mp hmax⟩
  by_contra! hn
  obtain ⟨k,hvk,hk⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hn
  apply hk.not_ge (modulus_le_of_upperDirectionalSlope_lt h fun w hw ↦ ?_)
  rw [← h.regularSubderivative_eq_upperDirectionalSlope]
  obtain ⟨z,hz,hval,-⟩ := h.exists_max_inner_subdifferential w
  rw [hval,EReal.coe_lt_coe_iff]
  apply lt_of_le_of_lt _ (show ‖v‖ < (k : ℝ) from ENNReal.coe_lt_coe.mp hvk)
  simpa only [hw, mul_one] using (real_inner_le_norm z w).trans (mul_le_mul_of_nonneg_right (hmax hz) (norm_nonneg w))

/-- **Theorem 9.13**, the maximum on the unit sphere. -/
theorem ERealStrictlyContinuousAt.exists_unit_regularSubderivative_eq_modulus [Nontrivial E]
    (h : ERealStrictlyContinuousAt f x) :
    ∃ w : E, ‖w‖ = 1 ∧ regularSubderivative f x w =
      ((lipschitzModulus (fun y ↦ (f y).toReal) x).toReal : EReal) ∧
      ∀ z : E, ‖z‖ = 1 → regularSubderivative f x z ≤ regularSubderivative f x w := by
  obtain ⟨v, hv, he, hmax⟩ := h.exists_subgradient_norm_eq_modulus
  have hupper {z : E} (hz : ‖z‖ = 1) : regularSubderivative f x z ≤ (‖v‖ : EReal) := by
    obtain ⟨s,hs,hval,-⟩ := h.exists_max_inner_subdifferential z
    rw [hval, EReal.coe_le_coe_iff]
    simpa only [hz, mul_one] using (real_inner_le_norm s z).trans (mul_le_mul_of_nonneg_right (hmax s hs) (norm_nonneg z))
  obtain ⟨w,hw,hi⟩ : ∃ w : E, ‖w‖ = 1 ∧ ⟪v,w⟫_ℝ = ‖v‖ := by
    rcases eq_or_ne v 0 with rfl | hv0
    · obtain ⟨w,hw⟩ := (NormedSpace.sphere_nonempty (E := E) (x := 0)).mpr (zero_le_one : (0:ℝ) ≤ 1)
      exact ⟨w,mem_sphere_zero_iff_norm.mp hw,by simp⟩
    · exact ⟨NormedSpace.normalize v, NormedSpace.norm_normalize hv0, by
        rw [NormedSpace.normalize, real_inner_smul_right, real_inner_self_eq_norm_sq]
        field_simp [norm_ne_zero_iff.mpr hv0]⟩
  have hwval : regularSubderivative f x w = (‖v‖ : EReal) := by
    apply le_antisymm (hupper hw)
    rw [h.regularSubderivative_eq_supportFunction, ← hi]
    exact inner_le_supportFunction hv w
  exact ⟨w, hw, by simpa only [he, ENNReal.coe_toReal, coe_nnnorm] using hwval,
    fun z hz ↦ (hupper hz).trans_eq hwval.symm⟩

end RW
