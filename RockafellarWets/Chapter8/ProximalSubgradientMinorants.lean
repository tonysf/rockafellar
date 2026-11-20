/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Proximal subgradients and `C²` minorants

Proposition 8.46(c) and (d).

* 8.46(c): `v` is a proximal subgradient of `f` at `x̄` exactly when, on some
  neighborhood of `x̄`, there is a `C²` function `h ≤ f` with `h(x̄) = f(x̄)` and
  `∇h(x̄) = v`.  For sufficiency the book bounds the Hessian on a ball; here
  the same second-order estimate comes from the local Lipschitz continuity of
  `∇h` and the mean value inequality, which is all that `C²` is used for.
* 8.46(d): `v` is a proximal normal to `C` at `x̄` exactly when some `C²`
  function `h` with `∇h(x̄) = v` has a local maximum relative to `C` at `x̄`;
  as in the book this is deduced from (b) and (c).
-/

import RockafellarWets.Chapter8.ProximalSubgradients

open Filter Set Topology Metric
open scoped InnerProductSpace NNReal

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The second-order lower estimate behind 8.46(c): a function that is `C²` on
a neighborhood of `x̄` lies above its tangent affine function up to a quadratic
error near `x̄`. -/
theorem exists_quadratic_lower_bound_of_contDiffOn {h : E → ℝ} {U : Set E} {x v : E}
    (hU : U ∈ 𝓝 x) (hh : ContDiffOn ℝ 2 h U) (hgrad : HasGradientAt h v x) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ δ > 0, ∀ y, ‖y - x‖ ≤ δ →
      h x + ⟪v, y - x⟫_ℝ - K * ‖y - x‖ ^ 2 ≤ h y := by
  have hC2 : ContDiffAt ℝ 2 h x := hh.contDiffAt hU
  have hC1 : ContDiffAt ℝ 1 (fderiv ℝ h) x := hC2.fderiv_right (by norm_num)
  obtain ⟨K, t, ht, hLip⟩ := hC1.exists_lipschitzOnWith
  have hdiff : ∀ᶠ z in 𝓝 x, DifferentiableAt ℝ h z := by
    have hC2' : ∀ᶠ z in 𝓝 x, ContDiffAt ℝ 2 h z := hC2.eventually (by norm_num)
    filter_upwards [hC2'] with z hz
    exact hz.differentiableAt (by norm_num)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem ht hdiff)
  refine ⟨K, K.2, δ / 2, half_pos hδ, fun y hy ↦ ?_⟩
  have hsub : closedBall x ‖y - x‖ ⊆ ball x δ :=
    closedBall_subset_ball (lt_of_le_of_lt hy (half_lt_self hδ))
  have hfx : fderiv ℝ h x = InnerProductSpace.toDual ℝ E v :=
    (hasGradientAt_iff_hasFDerivAt.1 hgrad).fderiv
  have hmvt := (convex_closedBall x ‖y - x‖).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (f := h) (f' := fderiv ℝ h) (φ := fderiv ℝ h x) (C := K * ‖y - x‖)
    (fun z hz ↦ ((hball (hsub hz)).2.hasFDerivAt).hasFDerivWithinAt)
    (fun z hz ↦ by
      have h1 := hLip.norm_sub_le (hball (hsub hz)).1 (mem_of_mem_nhds ht)
      have h2 : ‖z - x‖ ≤ ‖y - x‖ := by rwa [mem_closedBall, dist_eq_norm] at hz
      calc ‖fderiv ℝ h z - fderiv ℝ h x‖ ≤ K * ‖z - x‖ := h1
        _ ≤ K * ‖y - x‖ := mul_le_mul_of_nonneg_left h2 K.2)
    (mem_closedBall_self (norm_nonneg _))
    (by rw [mem_closedBall, dist_eq_norm])
  rw [hfx, InnerProductSpace.toDual_apply_apply, Real.norm_eq_abs] at hmvt
  have := neg_abs_le (h y - h x - ⟪v, y - x⟫_ℝ)
  nlinarith [hmvt, this]

/-- **Proposition 8.46(c)**, sufficiency: a `C²` function `h ≤ f` near `x̄`
with `h(x̄) = f(x̄)` has its gradient at `x̄` among the proximal subgradients of
`f` at `x̄`. -/
theorem mem_proximalSubdifferential_of_contDiffOn_minorant {f : E → EReal} {x v : E} {c : ℝ}
    (hxc : f x = c) {h : E → ℝ} {U : Set E} (hU : U ∈ 𝓝 x) (hh : ContDiffOn ℝ 2 h U)
    (hle : ∀ y ∈ U, (h y : EReal) ≤ f y) (hx : h x = c) (hgrad : HasGradientAt h v x) :
    v ∈ proximalSubdifferential f x := by
  obtain ⟨K, hK, δ, hδ, hbound⟩ := exists_quadratic_lower_bound_of_contDiffOn hU hh hgrad
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
  refine ⟨c, hxc, 2 * (K + 1), by positivity, min δ (r / 2), lt_min hδ (half_pos hr),
    fun y hy ↦ ?_⟩
  have hyU : y ∈ U := hrU (by
    rw [mem_ball, dist_eq_norm]
    exact lt_of_le_of_lt (hy.trans (min_le_right _ _)) (half_lt_self hr))
  refine le_trans (EReal.coe_le_coe_iff.2 ?_) (hle y hyU)
  have h1 := hbound y (hy.trans (min_le_left _ _))
  have h2 : 0 ≤ ‖y - x‖ ^ 2 := by positivity
  rw [hx] at h1
  nlinarith

/-- **Proposition 8.46(c)**: `v` is a proximal subgradient of `f` at `x̄` if and
only if on some neighborhood of `x̄` there is a `C²` function `h ≤ f` with
`h(x̄) = f(x̄)` and `∇h(x̄) = v`. -/
theorem mem_proximalSubdifferential_iff_exists_contDiffOn {f : E → EReal} {x v : E} {c : ℝ}
    (hxc : f x = c) :
    v ∈ proximalSubdifferential f x ↔ ∃ U ∈ 𝓝 x, ∃ h : E → ℝ, ContDiffOn ℝ 2 h U ∧
      (∀ y ∈ U, (h y : EReal) ≤ f y) ∧ h x = c ∧ HasGradientAt h v x := by
  constructor
  · intro hv
    obtain ⟨c', hc', h, hC2, hle, hx, hgrad⟩ :=
      exists_contDiff_minorant_of_mem_proximalSubdifferential hv
    have hcc : c' = c := by
      rw [hxc] at hc'
      exact (EReal.coe_injective hc').symm
    subst hcc
    obtain ⟨U, hU, hUle⟩ := Filter.eventually_iff_exists_mem.1 hle
    exact ⟨U, hU, h, hC2.contDiffOn, hUle, hx, hgrad⟩
  · rintro ⟨U, hU, h, hC2, hle, hx, hgrad⟩
    exact mem_proximalSubdifferential_of_contDiffOn_minorant hxc hU hC2 hle hx hgrad

/-- **Proposition 8.46(d)**: `v` is a proximal normal to `C` at `x̄ ∈ C` if and
only if on some neighborhood of `x̄` there is a `C²` function `h` with
`∇h(x̄) = v` attaining a local maximum relative to `C` at `x̄`. -/
theorem mem_proximalNormalCone_iff_exists_contDiffOn_isLocalMaxOn {C : Set E} {x v : E}
    (hx : x ∈ C) :
    v ∈ proximalNormalCone C x ↔ ∃ U ∈ 𝓝 x, ∃ h : E → ℝ, ContDiffOn ℝ 2 h U ∧
      HasGradientAt h v x ∧ ∀ y ∈ C ∩ U, h y ≤ h x := by
  have hx0 : indicatorVA C x = ((0 : ℝ) : EReal) := by
    rw [indicatorVA_apply_mem hx, EReal.coe_zero]
  rw [← mem_proximalSubdifferential_indicatorVA_iff,
    mem_proximalSubdifferential_iff_exists_contDiffOn hx0]
  constructor
  · rintro ⟨U, hU, h, hC2, hle, hhx, hgrad⟩
    refine ⟨U, hU, h, hC2, hgrad, fun y hy ↦ ?_⟩
    have := hle y hy.2
    rw [indicatorVA_apply_mem hy.1, ← EReal.coe_zero, EReal.coe_le_coe_iff] at this
    rw [hhx]
    exact this
  · rintro ⟨U, hU, h, hC2, hgrad, hmax⟩
    refine ⟨U, hU, fun y ↦ h y - h x, hC2.sub contDiffOn_const, fun y hy ↦ ?_, by simp, ?_⟩
    · by_cases hyC : y ∈ C
      · rw [indicatorVA_apply_mem hyC, ← EReal.coe_zero, EReal.coe_le_coe_iff]
        linarith [hmax y ⟨hyC, hy⟩]
      · rw [indicatorVA_apply_not_mem hyC]
        exact le_top
    · exact hasGradientAt_iff_hasFDerivAt.2
        ((hasGradientAt_iff_hasFDerivAt.1 hgrad).sub_const (h x))

end RW
