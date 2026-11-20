/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: difference quotients from almost-everywhere derivative bounds

A standalone lemma behind Theorem 9.61 (and the mollifier work of 9.67).  Let
`f` be Lipschitz on an open ball `B` and suppose that, off a null set `A`, `f` is
differentiable on `B` with `f'(x) w ≤ c`.  Then

  `f (x + τ w) - f x ≤ c τ`  whenever `τ ≥ 0` and `x, x + τ w ∈ B`

(`sub_le_mul_of_fderiv_le_off_null`), at every point, including the points
of `A`.  The variant `sub_le_mul_of_ae_fderiv_le` takes the bound as an
almost-everywhere hypothesis.

As in the proof of 9.61: by Tonelli and translation invariance almost every line
in the direction `w` meets `A` in a one-dimensional null set
(`ae_volume_line_inter_null`); along such a line `t ↦ f (x + t w)` is Lipschitz,
hence absolutely continuous, and the fundamental theorem of calculus
(`AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`) gives the bound; good
base points are dense and `f` is continuous.
-/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp

open Filter Set Topology Metric MeasureTheory
open scoped ENNReal NNReal

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Almost every line in the direction `w` meets a null set in a null set. -/
theorem ae_volume_line_inter_null {A : Set E} (hA : volume A = 0) (w : E) :
    ∀ᵐ y ∂(volume : Measure E), volume {t : ℝ | y + t • w ∈ A} = 0 := by
  obtain ⟨B, hAB, hBm, hB0⟩ := exists_measurable_superset_of_null hA
  have hS : MeasurableSet {p : E × ℝ | p.1 + p.2 • w ∈ B} :=
    hBm.preimage (measurable_fst.add (measurable_snd.smul_const w))
  have hprod : ((volume : Measure E).prod (volume : Measure ℝ))
      {p : E × ℝ | p.1 + p.2 • w ∈ B} = 0 := by
    rw [Measure.prod_apply_symm hS]
    have h1 : (fun t : ℝ ↦ (volume : Measure E)
        ((fun x ↦ (x, t)) ⁻¹' {p : E × ℝ | p.1 + p.2 • w ∈ B})) = fun _ ↦ 0 := by
      funext t
      have h2 : (fun x : E ↦ (x, t)) ⁻¹' {p : E × ℝ | p.1 + p.2 • w ∈ B} =
          (fun x ↦ x + t • w) ⁻¹' B := rfl
      rw [h2, measure_preimage_add_right]
      exact hB0
    rw [h1, lintegral_zero]
  rw [Measure.prod_apply hS, lintegral_eq_zero_iff (measurable_measure_prodMk_left hS)] at hprod
  filter_upwards [hprod] with y hy
  exact measure_mono_null (fun t ht ↦ hAB ht) hy

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Along a line meeting `A` in a null set, the bound on `f'(·) w` integrates to a bound on
the increment. -/
private theorem sub_le_mul_of_line {f : E → ℝ} {k : ℝ≥0} {x₀ : E} {r : ℝ}
    (hL : LipschitzOnWith k f (ball x₀ r)) {w : E} {c : ℝ} {A : Set E}
    (hbound : ∀ x ∈ ball x₀ r, x ∉ A → ∃ L : E →L[ℝ] ℝ, HasFDerivAt f L x ∧ L w ≤ c)
    {y : E} (hy0 : volume {t : ℝ | y + t • w ∈ A} = 0) {τ : ℝ} (hτ : 0 ≤ τ)
    (hy : y ∈ ball x₀ r) (hyτ : y + τ • w ∈ ball x₀ r) :
    f (y + τ • w) - f y ≤ c * τ := by
  have hseg : ∀ t ∈ Icc (0 : ℝ) τ, y + t • w ∈ ball x₀ r := by
    intro t ht
    rcases hτ.eq_or_lt with h0 | hpos
    · have ht0 : t = 0 := le_antisymm (h0 ▸ ht.2) ht.1
      rw [ht0, zero_smul, add_zero]
      exact hy
    · have h1 := (convex_ball x₀ r).add_smul_mem hy hyτ
        (t := t / τ) ⟨div_nonneg ht.1 hpos.le, div_le_one_of_le₀ ht.2 hpos.le⟩
      rwa [smul_smul, div_mul_cancel₀ t hpos.ne'] at h1
  have hφL : LipschitzOnWith (k * ‖w‖₊) (fun t : ℝ ↦ f (y + t • w)) (uIcc 0 τ) := by
    rw [uIcc_of_le hτ]
    refine LipschitzOnWith.of_dist_le_mul fun s hs t ht ↦ ?_
    calc dist (f (y + s • w)) (f (y + t • w)) ≤ k * dist (y + s • w) (y + t • w) :=
          hL.dist_le_mul _ (hseg s hs) _ (hseg t ht)
      _ = (k * ‖w‖₊ : ℝ≥0) * dist s t := by
          rw [dist_eq_norm, show y + s • w - (y + t • w) = (s - t) • w by rw [sub_smul]; abel,
            norm_smul, Real.norm_eq_abs, Real.dist_eq, NNReal.coe_mul, coe_nnnorm]
          ring
  have hac := hφL.absolutelyContinuousOnInterval
  have hFTC := hac.integral_deriv_eq_sub
  have hint := hac.intervalIntegrable_deriv
  have hae : (fun t ↦ deriv (fun t : ℝ ↦ f (y + t • w)) t) ≤ᵐ[volume.restrict (Icc 0 τ)]
      fun _ ↦ c := by
    have h1 : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ {t : ℝ | y + t • w ∈ A} :=
      measure_eq_zero_iff_ae_notMem.1 hy0
    filter_upwards [ae_restrict_of_ae h1, ae_restrict_mem measurableSet_Icc] with t ht1 ht2
    obtain ⟨L, hLd, hLw⟩ := hbound _ (hseg t ht2) ht1
    have hline : HasDerivAt (fun t : ℝ ↦ y + t • w) w t := by
      simpa using ((hasDerivAt_id t).smul_const w).const_add y
    have hd : HasDerivAt (fun t : ℝ ↦ f (y + t • w)) (L w) t :=
      HasFDerivAt.comp_hasDerivAt t hLd hline
    rw [hd.deriv]
    exact hLw
  have hmono := intervalIntegral.integral_mono_ae_restrict hτ hint intervalIntegrable_const hae
  rw [hFTC, intervalIntegral.integral_const, smul_eq_mul, zero_smul, add_zero, sub_zero] at hmono
  linarith

/-- **Lemma for Theorem 9.61.** If `f` is Lipschitz on the open ball `B = ball x₀ r` and,
off a null set `A`, differentiable on `B` with `f'(x) w ≤ c`, then
`f (x + τ w) - f x ≤ c τ` for every `τ ≥ 0` and every `x` with `x, x + τ w ∈ B`. -/
theorem sub_le_mul_of_fderiv_le_off_null {f : E → ℝ} {k : ℝ≥0} {x₀ : E} {r : ℝ}
    (hL : LipschitzOnWith k f (ball x₀ r)) {w : E} {c : ℝ} {A : Set E} (hA : volume A = 0)
    (hbound : ∀ x ∈ ball x₀ r, x ∉ A → ∃ L : E →L[ℝ] ℝ, HasFDerivAt f L x ∧ L w ≤ c)
    {x : E} {τ : ℝ} (hτ : 0 ≤ τ) (hx : x ∈ ball x₀ r) (hxτ : x + τ • w ∈ ball x₀ r) :
    f (x + τ • w) - f x ≤ c * τ := by
  have hae := ae_volume_line_inter_null hA w
  have hx' : ‖x - x₀‖ < r := mem_ball_iff_norm.1 hx
  have hxτ' : ‖x + τ • w - x₀‖ < r := mem_ball_iff_norm.1 hxτ
  obtain ⟨m, hm_def⟩ : ∃ m : ℝ, m = max ‖x - x₀‖ ‖x + τ • w - x₀‖ := ⟨_, rfl⟩
  have hm : m < r := by rw [hm_def]; exact max_lt hx' hxτ'
  have hseq : ∀ n : ℕ, ∃ y : E, ‖y - x‖ < min (r - m) (1 / ((n : ℝ) + 1)) ∧
      volume {t : ℝ | y + t • w ∈ A} = 0 := by
    intro n
    have hε : 0 < min (r - m) (1 / ((n : ℝ) + 1)) := lt_min (sub_pos.2 hm) (by positivity)
    have h1 : ∀ᵐ y ∂(volume.restrict (ball x (min (r - m) (1 / ((n : ℝ) + 1))))),
        y ∈ ball x (min (r - m) (1 / ((n : ℝ) + 1))) ∧ volume {t : ℝ | y + t • w ∈ A} = 0 :=
      (ae_restrict_mem measurableSet_ball).and (ae_restrict_of_ae hae)
    have hne : (volume.restrict (ball x (min (r - m) (1 / ((n : ℝ) + 1))))) ≠ 0 := by
      rw [Ne, Measure.restrict_eq_zero]
      exact (measure_ball_pos volume x hε).ne'
    haveI := ae_neBot.2 hne
    obtain ⟨y, hy1, hy2⟩ := h1.exists
    exact ⟨y, by rwa [mem_ball, dist_eq_norm] at hy1, hy2⟩
  choose y hy hy0 using hseq
  have hyB : ∀ n, y n ∈ ball x₀ r := fun n ↦ by
    rw [mem_ball_iff_norm]
    have h1 := (hy n).trans_le (min_le_left _ _)
    have h2 : ‖y n - x₀‖ ≤ ‖y n - x‖ + ‖x - x₀‖ := by
      rw [show y n - x₀ = (y n - x) + (x - x₀) by abel]
      exact norm_add_le _ _
    have h3 : ‖x - x₀‖ ≤ m := hm_def ▸ le_max_left _ _
    linarith
  have hyτB : ∀ n, y n + τ • w ∈ ball x₀ r := fun n ↦ by
    rw [mem_ball_iff_norm]
    have h1 := (hy n).trans_le (min_le_left _ _)
    have h2 : ‖y n + τ • w - x₀‖ ≤ ‖y n - x‖ + ‖x + τ • w - x₀‖ := by
      rw [show y n + τ • w - x₀ = (y n - x) + (x + τ • w - x₀) by abel]
      exact norm_add_le _ _
    have h3 : ‖x + τ • w - x₀‖ ≤ m := hm_def ▸ le_max_right _ _
    linarith
  have hylim : Tendsto y atTop (𝓝 x) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n ↦ norm_nonneg _)
      (fun n ↦ ((hy n).trans_le (min_le_right _ _)).le) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hcont : ContinuousOn f (ball x₀ r) := hL.continuousOn
  have h1 : Tendsto (fun n ↦ f (y n + τ • w) - f (y n)) atTop (𝓝 (f (x + τ • w) - f x)) := by
    have hx1 : ContinuousAt f x := hcont.continuousAt (isOpen_ball.mem_nhds hx)
    have hx2 : ContinuousAt f (x + τ • w) := hcont.continuousAt (isOpen_ball.mem_nhds hxτ)
    exact (hx2.tendsto.comp (hylim.add_const (τ • w))).sub (hx1.tendsto.comp hylim)
  exact le_of_tendsto' h1 fun n ↦
    sub_le_mul_of_line hL hbound (hy0 n) hτ (hyB n) (hyτB n)

/-- **Lemma for Theorem 9.61**, with an almost-everywhere hypothesis: if `f` is Lipschitz
on `B = ball x₀ r` and, for almost every `x ∈ B`, `f` is differentiable at `x` with
`f'(x) w ≤ c`, then `f (x + τ w) - f x ≤ c τ` for every `τ ≥ 0` and every `x` with
`x, x + τ w ∈ B`. -/
theorem sub_le_mul_of_ae_fderiv_le {f : E → ℝ} {k : ℝ≥0} {x₀ : E} {r : ℝ}
    (hL : LipschitzOnWith k f (ball x₀ r)) {w : E} {c : ℝ}
    (hbound : ∀ᵐ x ∂(volume : Measure E),
      x ∈ ball x₀ r → ∃ L : E →L[ℝ] ℝ, HasFDerivAt f L x ∧ L w ≤ c)
    {x : E} {τ : ℝ} (hτ : 0 ≤ τ) (hx : x ∈ ball x₀ r) (hxτ : x + τ • w ∈ ball x₀ r) :
    f (x + τ • w) - f x ≤ c * τ := by
  refine sub_le_mul_of_fderiv_le_off_null hL
    (A := {x | ¬ (x ∈ ball x₀ r → ∃ L : E →L[ℝ] ℝ, HasFDerivAt f L x ∧ L w ≤ c)})
    (measure_eq_zero_iff_ae_notMem.2 (hbound.mono fun z hz hz' ↦ hz' hz)) ?_ hτ hx hxτ
  intro z hz hzA
  by_contra hne
  exact hzA fun h ↦ hne (h hz)

end RW
