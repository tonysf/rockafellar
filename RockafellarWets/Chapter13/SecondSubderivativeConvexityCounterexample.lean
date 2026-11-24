/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: the printed claim of Proposition 13.49 for `D(∂f)(x̄ ∣ v̄)`

Proposition 13.49 asserts that `D(∂f)(x̄ ∣ v̄) + ρI` is maximal monotone for some `ρ` when `f` is
prox-regular and properly twice epi-differentiable at `x̄` for `v̄`.  For `f = 0` on `(-∞, 0]` and
`f = 1` on `(0, ∞)` at `x̄ = v̄ = 0` this fails: `f` is prox-regular there, `d²f(0 ∣ 0)` is the
indicator of `(-∞, 0]`, but `gph D(∂f)(0 ∣ 0)` contains `(1, 0)` (the subgradients `0` at points
`1/ν`) and `(0, |ρ| + 1)` (the subgradients `t ≥ 0` at `0`), which violate monotonicity of
`D(∂f)(0 ∣ 0) + ρI` (`printed_1349_counterexample`).  The book's proof works with an `f`-attentive
localization `T` of `∂f`, and `prox_regularity_of_second_subderivatives` proves the claim for `DT`,
and for `D(∂f)` under subdifferential continuity, which the step function lacks.
-/

import RockafellarWets.Chapter13.SecondSubderivativeConvexity

open Filter Set Topology Metric
open scoped InnerProductSpace

namespace RW
namespace SecondSubderivativeConvexityCounterexample

/-- `f = 0` on `(-∞, 0]`, `f = 1` on `(0, ∞)`. -/
noncomputable def stepFn (x : ℝ) : EReal := ((if x ≤ 0 then 0 else 1 : ℝ) : EReal)

theorem stepFn_of_nonpos {x : ℝ} (hx : x ≤ 0) : stepFn x = ((0 : ℝ) : EReal) := by
  simp [stepFn, hx]

theorem stepFn_of_pos {x : ℝ} (hx : 0 < x) : stepFn x = ((1 : ℝ) : EReal) := by
  simp [stepFn, not_le.2 hx]

theorem zero_le_stepFn (x : ℝ) : ((0 : ℝ) : EReal) ≤ stepFn x := by
  by_cases hx : x ≤ 0
  · rw [stepFn_of_nonpos hx]
  · rw [stepFn_of_pos (not_le.1 hx)]; exact EReal.coe_le_coe_iff.2 zero_le_one

theorem lowerSemicontinuous_stepFn : LowerSemicontinuous stepFn := by
  intro x y hy
  by_cases hx : x ≤ 0
  · rw [stepFn_of_nonpos hx] at hy
    exact Eventually.of_forall fun x' ↦ lt_of_lt_of_le hy (zero_le_stepFn x')
  · have hx0 : 0 < x := not_le.1 hx
    filter_upwards [Ioi_mem_nhds hx0] with x' hx'
    rw [stepFn_of_pos hx']
    rwa [stepFn_of_pos hx0] at hy

theorem nonneg_of_mem_regularSubdifferential_stepFn {y v : ℝ} (hy : y ≤ 0)
    (hv : v ∈ regularSubdifferential stepFn y) : 0 ≤ v := by
  obtain ⟨c, hc, h⟩ := hv
  rw [stepFn_of_nonpos hy, EReal.coe_eq_coe_iff] at hc
  rw [← hc] at h
  by_contra hlt
  push_neg at hlt
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (h (-v / 2) (by linarith))
  have h1 := hball (y := y - δ / 2) (by
    rw [Real.dist_eq, show y - δ / 2 - y = -(δ / 2) by ring, abs_neg, abs_of_pos (half_pos hδ)]
    linarith)
  rw [stepFn_of_nonpos (by linarith), EReal.coe_le_coe_iff] at h1
  simp only [RCLike.inner_apply, conj_trivial, Real.norm_eq_abs,
    show y - δ / 2 - y = -(δ / 2) by ring, abs_neg, abs_of_pos (half_pos hδ)] at h1
  nlinarith [mul_pos hδ (neg_pos.2 hlt)]

theorem eq_zero_of_mem_regularSubdifferential_stepFn {y v : ℝ} (hy : y < 0)
    (hv : v ∈ regularSubdifferential stepFn y) : v = 0 := by
  refine le_antisymm ?_ (nonneg_of_mem_regularSubdifferential_stepFn hy.le hv)
  obtain ⟨c, hc, h⟩ := hv
  rw [stepFn_of_nonpos hy.le, EReal.coe_eq_coe_iff] at hc
  rw [← hc] at h
  by_contra hlt
  push_neg at hlt
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (h (v / 2) (by linarith))
  have htpos : 0 < min (δ / 2) (-y / 2) := lt_min (half_pos hδ) (by linarith)
  have htδ : min (δ / 2) (-y / 2) < δ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ)
  have hty : min (δ / 2) (-y / 2) ≤ -y / 2 := min_le_right _ _
  have h1 := hball (y := y + min (δ / 2) (-y / 2)) (by
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos htpos]; exact htδ)
  rw [stepFn_of_nonpos (by linarith), EReal.coe_le_coe_iff] at h1
  simp only [RCLike.inner_apply, conj_trivial, Real.norm_eq_abs, add_sub_cancel_left,
    abs_of_pos htpos] at h1
  nlinarith [mul_pos htpos hlt]

theorem mem_regularSubdifferential_stepFn_zero {t : ℝ} (ht : 0 ≤ t) :
    t ∈ regularSubdifferential stepFn 0 := by
  refine ⟨0, stepFn_of_nonpos le_rfl, fun ε hε ↦ ?_⟩
  filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 / (t + 1) by positivity)] with y hy
  have hy' : y < 1 / (t + 1) := hy
  simp only [RCLike.inner_apply, conj_trivial, Real.norm_eq_abs, sub_zero, zero_add]
  by_cases hy0 : y ≤ 0
  · rw [stepFn_of_nonpos hy0, EReal.coe_le_coe_iff]
    nlinarith [abs_nonneg y, mul_nonneg ht (neg_nonneg.2 hy0), mul_nonneg hε.le (abs_nonneg y)]
  · have hpos : 0 < y := lt_of_not_ge hy0
    rw [stepFn_of_pos hpos, EReal.coe_le_coe_iff]
    have h1 : y * (t + 1) < 1 := by rwa [lt_div_iff₀ (by positivity)] at hy'
    nlinarith [abs_nonneg y, mul_nonneg hε.le (abs_nonneg y), mul_nonneg ht hpos.le]

theorem zero_mem_subdifferential_stepFn (y : ℝ) : (0 : ℝ) ∈ subdifferential stepFn y := by
  by_cases hy : y ≤ 0
  · have hmin : IsLocalMin stepFn y := Eventually.of_forall fun y' ↦ by
      rw [stepFn_of_nonpos hy]; exact zero_le_stepFn y'
    exact regularSubdifferential_subset_subdifferential _ _
      (RW.IsLocalMin.zero_mem_regularSubdifferential hmin (stepFn_of_nonpos hy))
  · have hy0 : 0 < y := not_le.1 hy
    have hmin : IsLocalMin stepFn y := by
      filter_upwards [Ioi_mem_nhds hy0] with y' hy'
      rw [stepFn_of_pos hy0, stepFn_of_pos hy']
    exact regularSubdifferential_subset_subdifferential _ _
      (RW.IsLocalMin.zero_mem_regularSubdifferential hmin (stepFn_of_pos hy0))

theorem eq_zero_of_mem_subdifferential_stepFn {y v : ℝ} (hy : y < 0)
    (hv : v ∈ subdifferential stepFn y) : v = 0 := by
  obtain ⟨-, xs, vs, hxs, -, hvs, hlim⟩ := mem_subdifferential_iff_exists_seq.1 hv
  have hev : ∀ᶠ n in atTop, vs n = 0 := by
    filter_upwards [hxs.eventually (Iio_mem_nhds hy)] with n hn
    exact eq_zero_of_mem_regularSubdifferential_stepFn hn (hvs n)
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hev.mono fun n h ↦ h.symm))

theorem nonneg_of_mem_subdifferential_stepFn_zero {v : ℝ}
    (hv : v ∈ subdifferential stepFn 0) : 0 ≤ v := by
  obtain ⟨-, xs, vs, hxs, hfxs, hvs, hlim⟩ := mem_subdifferential_iff_exists_seq.1 hv
  rw [stepFn_of_nonpos le_rfl] at hfxs
  have hev : ∀ᶠ n in atTop, xs n ≤ 0 := by
    filter_upwards [hfxs.eventually (Iio_mem_nhds
      (show ((0 : ℝ) : EReal) < ((1 / 2 : ℝ) : EReal) from
        EReal.coe_lt_coe_iff.2 (by norm_num)))] with n hfn
    by_contra hpos
    push_neg at hpos
    change stepFn (xs n) < ((1 / 2 : ℝ) : EReal) at hfn
    rw [stepFn_of_pos hpos, EReal.coe_lt_coe_iff] at hfn
    norm_num at hfn
  exact ge_of_tendsto hlim (hev.mono fun n hn ↦
    nonneg_of_mem_regularSubdifferential_stepFn hn (hvs n))

theorem isProxRegularAt_stepFn : IsProxRegularAt stepFn 0 0 := by
  refine ⟨locallyLscAt_of_lowerSemicontinuous_finite lowerSemicontinuous_stepFn
      (stepFn_of_nonpos le_rfl), zero_mem_subdifferential_stepFn 0, 1 / 2, by norm_num, 0, le_rfl,
    fun y v' hv' hvv hyx hfy x' hx' ↦ ?_⟩
  have hy0 : y ≤ 0 := by
    by_contra hpos
    push_neg at hpos
    rw [stepFn_of_pos hpos, stepFn_of_nonpos le_rfl, ← EReal.coe_add, EReal.coe_lt_coe_iff] at hfy
    norm_num at hfy
  rw [sub_zero, Real.norm_eq_abs] at hvv
  rw [mem_closedBall, Real.dist_eq, sub_zero] at hx'
  have hval : (x' - y) * v' ≤ 0 ∨ (0 < x' ∧ (x' - y) * v' ≤ 1) := by
    rcases hy0.lt_or_eq with hlt | heq
    · left
      rw [eq_zero_of_mem_subdifferential_stepFn hlt hv', mul_zero]
    · subst heq
      have hv0 := nonneg_of_mem_subdifferential_stepFn_zero hv'
      by_cases hx0 : x' ≤ 0
      · left
        rw [sub_zero]
        exact mul_nonpos_of_nonpos_of_nonneg hx0 hv0
      · right
        refine ⟨not_le.1 hx0, ?_⟩
        rw [sub_zero]
        nlinarith [mul_le_mul (abs_le.1 hx').2 (abs_lt.1 hvv).2.le hv0
          (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [stepFn_of_nonpos hy0, ← EReal.coe_add]
  have hinner : ⟪v', x' - y⟫_ℝ = (x' - y) * v' := by
    simp only [RCLike.inner_apply, conj_trivial]
  rcases hval with h | ⟨hxpos, h⟩
  · refine le_trans (EReal.coe_le_coe_iff.2 ?_) (zero_le_stepFn x')
    rw [hinner]
    linarith
  · rw [stepFn_of_pos hxpos, EReal.coe_le_coe_iff, hinner]
    linarith

theorem secondDifferenceQuotient_stepFn_of_nonpos {τ w : ℝ} (hτ : 0 < τ) (hw : w ≤ 0) :
    secondDifferenceQuotient stepFn 0 0 τ w = 0 := by
  rw [secondDifferenceQuotient_of_coe (c := 0) (r := 0) (stepFn_of_nonpos le_rfl)
    (by rw [zero_add, smul_eq_mul]
        exact stepFn_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hτ.le hw))]
  simp

theorem secondDifferenceQuotient_stepFn_of_pos {τ w : ℝ} (hτ : 0 < τ) (hw : 0 < w) :
    secondDifferenceQuotient stepFn 0 0 τ w = ((2 / τ ^ 2 : ℝ) : EReal) := by
  rw [secondDifferenceQuotient_of_coe (c := 0) (r := 1) (stepFn_of_nonpos le_rfl)
    (by rw [zero_add, smul_eq_mul]; exact stepFn_of_pos (mul_pos hτ hw))]
  simp

theorem secondSubderivative_stepFn_nonneg (w : ℝ) : 0 ≤ secondSubderivative stepFn 0 0 w := by
  refine le_liminf_of_le (h := ?_)
  filter_upwards [tendsto_fst.eventually self_mem_nhdsWithin] with p hp
  have hp' : (0 : ℝ) < p.1 := hp
  by_cases hw : p.2 ≤ 0
  · rw [secondDifferenceQuotient_stepFn_of_nonpos hp' hw]
  · rw [secondDifferenceQuotient_stepFn_of_pos hp' (not_le.1 hw)]
    exact EReal.coe_nonneg.2 (by positivity)

theorem secondSubderivative_stepFn_of_pos {w : ℝ} (hw : 0 < w) :
    secondSubderivative stepFn 0 0 w = ⊤ := by
  rw [EReal.eq_top_iff_forall_lt]
  intro M
  have hδ : (0 : ℝ) < 1 / (|M| + 1) := by positivity
  refine lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (lt_add_one M)) (le_liminf_of_le (h := ?_))
  filter_upwards [tendsto_fst.eventually self_mem_nhdsWithin,
    tendsto_fst.eventually (nhdsWithin_le_nhds (Iio_mem_nhds hδ)),
    tendsto_snd.eventually (Ioi_mem_nhds hw)] with p hp1 hp2 hp3
  have h1 : (0 : ℝ) < p.1 := hp1
  have h2 : p.1 < 1 / (|M| + 1) := hp2
  have h3 : (0 : ℝ) < p.2 := hp3
  rw [secondDifferenceQuotient_stepFn_of_pos h1 h3, EReal.coe_le_coe_iff,
    le_div_iff₀ (by positivity)]
  have h4 : p.1 * (|M| + 1) < 1 := by rwa [lt_div_iff₀ (by positivity)] at h2
  have h5 := mul_lt_mul_of_pos_left h4 h1
  have h6 : p.1 < 1 := by nlinarith [abs_nonneg M]
  have h7 : (M + 1) * p.1 ^ 2 ≤ (|M| + 1) * p.1 ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self M]) (sq_nonneg _)
  nlinarith

theorem twiceEpiDifferentiableAt_stepFn : TwiceEpiDifferentiableAt stepFn 0 0 := by
  rw [twiceEpiDifferentiableAt_iff_subset]
  refine ⟨by rw [stepFn_of_nonpos le_rfl]; exact EReal.coe_ne_bot _,
    by rw [stepFn_of_nonpos le_rfl]; exact EReal.coe_ne_top _, ?_⟩
  rintro ⟨w, α⟩ hmem
  have hle : secondSubderivative stepFn 0 0 w ≤ (α : EReal) := hmem
  have hw : w ≤ 0 := by
    by_contra hpos
    rw [secondSubderivative_stepFn_of_pos (not_le.1 hpos)] at hle
    exact absurd hle (not_le.2 (EReal.coe_lt_top α))
  have hα : (0 : EReal) ≤ (α : EReal) := (secondSubderivative_stepFn_nonneg w).trans hle
  rw [mem_innerSetLimitAlong]
  intro N hN
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  refine ⟨(w, α), ?_, mem_of_mem_nhds hN⟩
  change secondDifferenceQuotient stepFn 0 0 τ w ≤ (α : EReal)
  rw [secondDifferenceQuotient_stepFn_of_nonpos hτ hw]
  exact hα

theorem not_svMonotone_stepFn (ρ : ℝ) : ¬ SvMonotone (fun w ↦
    (fun z ↦ z + ρ • w) '' graphicalDerivative (subdifferential stepFn) 0 0 w) := by
  intro hmono
  have hτ : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hpos : ∀ n : ℕ, (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := fun n ↦ by positivity
  have h1 : (0 : ℝ) ∈ graphicalDerivative (subdifferential stepFn) 0 0 1 := by
    have h : ((1 : ℝ), (0 : ℝ)) ∈ tangentCone (svGraph (subdifferential stepFn)) (0, 0) := by
      refine mem_tangentCone_of_forall (xs := fun n : ℕ ↦ (((n : ℝ) + 1)⁻¹, (0 : ℝ)))
        (τs := fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) (fun n ↦ zero_mem_subdifferential_stepFn _) hpos hτ ?_
      refine tendsto_const_nhds.congr fun n ↦ ?_
      have hne : (n : ℝ) + 1 ≠ 0 := by positivity
      ext <;> simp [hne]
    rw [← svGraph_graphicalDerivative] at h
    exact h
  have h0 : |ρ| + 1 ∈ graphicalDerivative (subdifferential stepFn) 0 0 0 := by
    have h : ((0 : ℝ), |ρ| + 1) ∈ tangentCone (svGraph (subdifferential stepFn)) (0, 0) := by
      refine mem_tangentCone_of_forall
        (xs := fun n : ℕ ↦ ((0 : ℝ), ((n : ℝ) + 1)⁻¹ * (|ρ| + 1)))
        (τs := fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹)
        (fun n ↦ regularSubdifferential_subset_subdifferential _ _
          (mem_regularSubdifferential_stepFn_zero (by positivity))) hpos hτ ?_
      refine tendsto_const_nhds.congr fun n ↦ ?_
      have hne : (n : ℝ) + 1 ≠ 0 := by positivity
      ext <;> simp [hne]
    rw [← svGraph_graphicalDerivative] at h
    exact h
  have a0 : (|ρ| + 1) + ρ • (0 : ℝ) ∈
      (fun z ↦ z + ρ • (0 : ℝ)) '' graphicalDerivative (subdifferential stepFn) 0 0 0 :=
    ⟨_, h0, rfl⟩
  have a1 : (0 : ℝ) + ρ • (1 : ℝ) ∈
      (fun z ↦ z + ρ • (1 : ℝ)) '' graphicalDerivative (subdifferential stepFn) 0 0 1 :=
    ⟨_, h1, rfl⟩
  have key := hmono a0 a1
  simp only [RCLike.inner_apply, conj_trivial, smul_eq_mul] at key
  nlinarith [le_abs_self ρ]

/-- **Proposition 13.49**, the printed claim for `D(∂f)(x̄ ∣ v̄)`.  The step function `f = 0` on
`(-∞, 0]`, `f = 1` on `(0, ∞)` is prox-regular and properly twice epi-differentiable at `x̄ = 0` for
`v̄ = 0`, but `D(∂f)(0 ∣ 0) + ρI` is not monotone for any `ρ`.  Consistently with the corrected
statement `prox_regularity_of_second_subderivatives`, `f` is not subdifferentially continuous at `0`
for `0`. -/
theorem printed_1349_counterexample :
    IsProxRegularAt stepFn 0 0 ∧ ProperlyTwiceEpiDifferentiableAt stepFn 0 0 ∧
      (∀ ρ : ℝ, ¬ SvMonotone (fun w ↦
        (fun z ↦ z + ρ • w) '' graphicalDerivative (subdifferential stepFn) 0 0 w)) ∧
      ¬ IsSubdifferentiallyContinuousAt stepFn 0 0 := by
  refine ⟨isProxRegularAt_stepFn, ⟨twiceEpiDifferentiableAt_stepFn, ?_⟩, not_svMonotone_stepFn, ?_⟩
  · exact ⟨⟨0, (secondSubderivative_zero_le (stepFn_of_nonpos le_rfl)).trans_lt EReal.zero_lt_top⟩,
      fun w ↦ lt_of_lt_of_le EReal.bot_lt_zero (secondSubderivative_stepFn_nonneg w)⟩
  · intro hsc
    obtain ⟨ρ, -, -, -, -, h4, -⟩ :=
      prox_regularity_of_second_subderivatives isProxRegularAt_stepFn
        twiceEpiDifferentiableAt_stepFn
    exact not_svMonotone_stepFn ρ (h4 hsc).1

end SecondSubderivativeConvexityCounterexample
end RW
