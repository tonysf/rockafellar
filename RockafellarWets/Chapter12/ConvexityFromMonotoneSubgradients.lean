/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: convexity from monotone subgradient mappings

This file supplies the analytic core of the converse half of Theorem 12.17:
a proper lower semicontinuous function whose subgradient mapping is monotone
is convex.

The book first treats a prox-bounded function through its Moreau envelopes and
then removes prox-boundedness with the barrier `(ρ² - |x|²)⁻¹`.  We follow the
same two steps with two simplifications.

* For a proper lsc function `h` bounded below, every proximal point `p` of `x`
  gives `λ⁻¹(x - p) ∈ ∂h(p)` (10.2).  The resulting slope field `v` of the
  envelope `eλh` is monotone when `∂h` is, and `eλh` has the quadratic upper
  model `eλh(x') ≤ eλh(x) + ⟪v x, x' - x⟫ + (2λ)⁻¹|x' - x|²`.  A telescoping
  sum along a subdivided segment turns these two facts into the affine support
  inequality `eλh(y) ≥ eλh(x) + ⟪v x, y - x⟫`.  No differentiability of the
  envelope and no single-valuedness of `Pλh` is needed.  Since `eλh ↗ h`, the
  function `h` is a supremum of affine functions, hence convex.
* The barrier `s(r² - |x - c|²)⁻¹` on an open ball is used with a vanishing
  factor `s ↘ 0` instead of a growing radius.  This localizes the argument:
  monotonicity of `∂f` on the ball already makes `f` convex on the ball, which
  is also the form needed for hypomonotone mappings in 12.28.
-/

import RockafellarWets.Chapter12.MonotoneMappings
import RockafellarWets.Chapter10.SubsmoothMoreauEnvelopes
import RockafellarWets.Chapter10.ProximalStationarity
import RockafellarWets.Chapter3.Coercivity
import RockafellarWets.Chapter8.ConvexSubgradients
import RockafellarWets.Chapter8.SubgradientsAndGradients
import RockafellarWets.Chapter9.LipschitzSubgradientLimits

open Set Filter Topology Metric
open scoped InnerProductSpace

namespace RW

section Telescoping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A real function with a quadratic upper model along a monotone slope field
satisfies the affine support inequality.  The proof telescopes the upper model
along a subdivided segment; monotonicity compares every slope with the slope at
the base point, and the quadratic error is of order `1/N`. -/
theorem affine_support_of_quadratic_upper_of_monotone {e : E → ℝ} {v : E → E} {c : ℝ}
    (hup : ∀ x x', e x' ≤ e x + ⟪v x, x' - x⟫_ℝ + c * ‖x' - x‖ ^ 2)
    (hmono : ∀ x₀ x₁, 0 ≤ ⟪v x₁ - v x₀, x₁ - x₀⟫_ℝ) (x y : E) :
    e x + ⟪v x, y - x⟫_ℝ ≤ e y := by
  set d := y - x with hd
  have key : ∀ N : ℕ, 0 < N → e x + ⟪v x, d⟫_ℝ - c * ‖d‖ ^ 2 / N ≤ e y := by
    intro N hN
    have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    let p : ℕ → E := fun k ↦ x + ((k : ℝ) / N) • d
    have hp0 : p 0 = x := by simp [p]
    have hpN : p N = y := by
      simp only [p, div_self hNr.ne', one_smul, hd]
      abel
    have hstep : ∀ k : ℕ, ⟪v x, d⟫_ℝ / N - c * ‖d‖ ^ 2 / N ^ 2 ≤ e (p (k + 1)) - e (p k) := by
      intro k
      have h1 := hup (p (k + 1)) (p k)
      have hdiff : p k - p (k + 1) = (-(1 / (N : ℝ))) • d := by
        simp only [p, Nat.cast_add, Nat.cast_one]
        rw [add_sub_add_left_eq_sub, ← sub_smul]
        congr 1
        ring
      rw [hdiff, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at h1
      have h2 := hmono x (p (k + 1))
      have hpx : p (k + 1) - x = (((k + 1 : ℕ) : ℝ) / N) • d := by
        simp only [p]
        abel
      rw [hpx, inner_smul_right] at h2
      have hpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) / N := by positivity
      have h3 : ⟪v x, d⟫_ℝ ≤ ⟪v (p (k + 1)), d⟫_ℝ := by
        have := nonneg_of_mul_nonneg_right h2 hpos
        rw [inner_sub_left] at this
        linarith
      have hN2 : (-(1 / (N : ℝ))) ^ 2 = 1 / (N : ℝ) ^ 2 := by ring
      rw [hN2] at h1
      have h4 : ⟪v x, d⟫_ℝ / N ≤ ⟪v (p (k + 1)), d⟫_ℝ / N :=
        div_le_div_of_nonneg_right h3 hNr.le
      have h5 : c * (1 / (N : ℝ) ^ 2 * ‖d‖ ^ 2) = c * ‖d‖ ^ 2 / N ^ 2 := by ring
      have h6 : -(1 / (N : ℝ)) * ⟪v (p (k + 1)), d⟫_ℝ = -(⟪v (p (k + 1)), d⟫_ℝ / N) := by ring
      rw [h5, h6] at h1
      linarith
    have hsum := Finset.sum_range_sub (fun k ↦ e (p k)) N
    simp only [hp0, hpN] at hsum
    have hle : ∑ _k ∈ Finset.range N, (⟪v x, d⟫_ℝ / N - c * ‖d‖ ^ 2 / N ^ 2) ≤
        ∑ k ∈ Finset.range N, (e (p (k + 1)) - e (p k)) :=
      Finset.sum_le_sum fun k _ ↦ hstep k
    rw [hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
    have hcalc : (N : ℝ) * (⟪v x, d⟫_ℝ / N - c * ‖d‖ ^ 2 / N ^ 2) =
        ⟪v x, d⟫_ℝ - c * ‖d‖ ^ 2 / N := by
      field_simp
    linarith
  have hlim : Tendsto (fun N : ℕ ↦ e x + ⟪v x, d⟫_ℝ - c * ‖d‖ ^ 2 / N) atTop
      (𝓝 (e x + ⟪v x, d⟫_ℝ - 0)) :=
    tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat _)
  rw [sub_zero] at hlim
  exact le_of_tendsto hlim (eventually_atTop.2 ⟨1, fun N hN ↦ key N hN⟩)

end Telescoping

section Core

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- For a lower semicontinuous function bounded below, the Moreau envelopes
exceed every level below the function value once the parameter is small. -/
theorem exists_lt_moreauEnvelopeEReal_of_lt {h : E → EReal} (hl : LowerSemicontinuous h)
    {m : ℝ} (hm : ∀ x, (m : EReal) ≤ h x) {z : E} {α : ℝ} (hα : (α : EReal) < h z) :
    ∃ lam : ℝ, 0 < lam ∧ (α : EReal) < moreauEnvelopeEReal h lam z := by
  obtain ⟨α', hαα', hα'⟩ := EReal.lt_iff_exists_real_btwn.1 hα
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hl z α' hα')
  set K : ℝ := |α' - m| + 1 with hKdef
  have hK : 0 < K := by positivity
  refine ⟨δ ^ 2 / (2 * K), by positivity, lt_of_lt_of_le hαα' ?_⟩
  rw [moreauEnvelopeEReal]
  refine le_iInf fun w ↦ ?_
  have hq0 : 0 ≤ (1 / (2 * (δ ^ 2 / (2 * K)))) * ‖w - z‖ ^ 2 := by positivity
  by_cases hw : dist w z < δ
  · calc (α' : EReal) ≤ h w := (hball hw).le
      _ ≤ h w + (((1 / (2 * (δ ^ 2 / (2 * K)))) * ‖w - z‖ ^ 2 : ℝ) : EReal) :=
        le_add_of_nonneg_right (EReal.coe_nonneg.2 hq0)
  · push_neg at hw
    have hwz : δ ≤ ‖w - z‖ := by rwa [← dist_eq_norm]
    have h1 : 1 / (2 * (δ ^ 2 / (2 * K))) = K / δ ^ 2 := by field_simp
    have hq : α' - m ≤ (1 / (2 * (δ ^ 2 / (2 * K)))) * ‖w - z‖ ^ 2 := by
      rw [h1]
      have h3 : K / δ ^ 2 * δ ^ 2 = K := by field_simp
      have h4 : α' - m ≤ K := by
        have := le_abs_self (α' - m)
        linarith
      calc α' - m ≤ K := h4
        _ = K / δ ^ 2 * δ ^ 2 := h3.symm
        _ ≤ K / δ ^ 2 * ‖w - z‖ ^ 2 := by gcongr
    calc (α' : EReal) = ((m + (α' - m) : ℝ) : EReal) := by rw [add_sub_cancel]
      _ ≤ (m : EReal) + (((1 / (2 * (δ ^ 2 / (2 * K)))) * ‖w - z‖ ^ 2 : ℝ) : EReal) := by
          rw [← EReal.coe_add]
          exact EReal.coe_le_coe_iff.2 (by linarith)
      _ ≤ h w + (((1 / (2 * (δ ^ 2 / (2 * K)))) * ‖w - z‖ ^ 2 : ℝ) : EReal) :=
          add_le_add (hm w) le_rfl

/-- **Core of Theorem 12.17.** A proper lower semicontinuous function that is
bounded below and has a monotone subgradient mapping is convex.

For each `λ > 0` choose proximal points `p(x) ∈ Pλh(x)`, which exist since the
prox-threshold is infinite.  The slopes `v(x) = λ⁻¹(x - p(x)) ∈ ∂h(p(x))` form
a monotone field, and the real envelope values satisfy the quadratic upper
model, so they satisfy the affine support inequality.  Hence `eλh` is a
supremum of affine functions touching it, and `h = sup_λ eλh` is convex. -/
theorem convex_epigraph_of_svMonotone_subdifferential_of_bddBelow {h : E → EReal}
    (hp : IsProper h) (hl : LowerSemicontinuous h) {m : ℝ} (hm : ∀ x, (m : EReal) ≤ h x)
    (hmono : SvMonotone (subdifferential h)) : Convex ℝ (epigraph h) := by
  have hthr : proxThreshold h = ⊤ :=
    proxThreshold_eq_top_of_affineNormLowerBound (γ := 0) (β := m) fun x ↦ by simpa using hm x
  have hne : ∀ lam : ℝ, 0 < lam → ∀ x, (proximalMappingEReal h lam x).Nonempty :=
    fun lam hlam x ↦ proximalMappingEReal_nonempty_of_lt_proxThreshold hp hl hlam
      (by rw [hthr]; exact EReal.coe_lt_top lam) x
  choose! P hP using hne
  let e : ℝ → E → ℝ := fun lam x ↦ (h (P lam x)).toReal + (1 / (2 * lam)) * ‖P lam x - x‖ ^ 2
  have he : ∀ lam, 0 < lam → ∀ x, moreauEnvelopeEReal h lam x = (e lam x : EReal) :=
    fun lam hlam x ↦ (moreauEnvelope_eq_of_mem_proximalMapping hp (hP lam hlam x)).2
  have hhP : ∀ lam, 0 < lam → ∀ x, h (P lam x) = ((h (P lam x)).toReal : EReal) :=
    fun lam hlam x ↦ (moreauEnvelope_eq_of_mem_proximalMapping hp (hP lam hlam x)).1
  let v : ℝ → E → E := fun lam x ↦ lam⁻¹ • (x - P lam x)
  have hv : ∀ lam, 0 < lam → ∀ x, v lam x ∈ subdifferential h (P lam x) := by
    intro lam hlam x
    obtain ⟨u, hu, hux⟩ :=
      proximalMappingEReal_subset_inverse_subgradientShift hp hlam x (hP lam hlam x)
    have hvu : v lam x = u := by
      have hux' : P lam x + lam • u = x := hux
      have hxP : x - P lam x = lam • u := (eq_sub_of_add_eq' hux').symm
      simp only [v]
      rw [hxP, smul_smul, inv_mul_cancel₀ hlam.ne', one_smul]
    rw [hvu]
    exact hu
  have hup : ∀ lam, 0 < lam → ∀ x x', e lam x' ≤
      e lam x + ⟪v lam x, x' - x⟫_ℝ + (1 / (2 * lam)) * ‖x' - x‖ ^ 2 := by
    intro lam hlam x x'
    have h1 : moreauEnvelopeEReal h lam x' ≤
        h (P lam x) + (((1 / (2 * lam)) * ‖P lam x - x'‖ ^ 2 : ℝ) : EReal) :=
      moreauEnvelope_le x' (P lam x)
    rw [he lam hlam x', hhP lam hlam x, ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
    have hid : ‖P lam x - x'‖ ^ 2 =
        ‖P lam x - x‖ ^ 2 - 2 * ⟪P lam x - x, x' - x⟫_ℝ + ‖x' - x‖ ^ 2 := by
      rw [show P lam x - x' = (P lam x - x) - (x' - x) by abel, norm_sub_sq_real]
    have hinner : ⟪v lam x, x' - x⟫_ℝ = -lam⁻¹ * ⟪P lam x - x, x' - x⟫_ℝ := by
      simp only [v, real_inner_smul_left]
      rw [show x - P lam x = -(P lam x - x) by abel, inner_neg_left]
      ring
    have hcoef : 1 / (2 * lam) * (‖P lam x - x‖ ^ 2 - 2 * ⟪P lam x - x, x' - x⟫_ℝ + ‖x' - x‖ ^ 2)
        = 1 / (2 * lam) * ‖P lam x - x‖ ^ 2 + -lam⁻¹ * ⟪P lam x - x, x' - x⟫_ℝ +
          1 / (2 * lam) * ‖x' - x‖ ^ 2 := by
      field_simp
      ring
    rw [hid, hcoef] at h1
    simp only [e]
    rw [hinner]
    linarith
  have hvmono : ∀ lam, 0 < lam → ∀ x₀ x₁, 0 ≤ ⟪v lam x₁ - v lam x₀, x₁ - x₀⟫_ℝ := by
    intro lam hlam x₀ x₁
    have hm' := hmono (hv lam hlam x₀) (hv lam hlam x₁)
    have hx : ∀ x, P lam x + lam • v lam x = x := by
      intro x
      simp only [v, smul_smul, mul_inv_cancel₀ hlam.ne', one_smul]
      abel
    have hdiff : x₁ - x₀ = (P lam x₁ - P lam x₀) + lam • (v lam x₁ - v lam x₀) := by
      calc x₁ - x₀ = (P lam x₁ + lam • v lam x₁) - (P lam x₀ + lam • v lam x₀) := by
            rw [hx x₁, hx x₀]
        _ = _ := by rw [smul_sub]; abel
    rw [hdiff, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    have : 0 ≤ lam * ‖v lam x₁ - v lam x₀‖ ^ 2 := by positivity
    linarith
  have hsupp : ∀ lam, 0 < lam → ∀ x y, e lam x + ⟪v lam x, y - x⟫_ℝ ≤ e lam y :=
    fun lam hlam ↦ affine_support_of_quadratic_upper_of_monotone (hup lam hlam) (hvmono lam hlam)
  have hle : ∀ lam, 0 < lam → ∀ x, (e lam x : EReal) ≤ h x := by
    intro lam hlam x
    rw [← he lam hlam x]
    calc moreauEnvelopeEReal h lam x ≤ h x + (((1 / (2 * lam)) * ‖x - x‖ ^ 2 : ℝ) : EReal) :=
          moreauEnvelope_le x x
      _ = h x := by simp
  rintro ⟨x₁, β₁⟩ hp₁ ⟨x₂, β₂⟩ hp₂ a b ha hb hab
  change h x₁ ≤ (β₁ : EReal) at hp₁
  change h x₂ ≤ (β₂ : EReal) at hp₂
  change h (a • x₁ + b • x₂) ≤ ((a * β₁ + b * β₂ : ℝ) : EReal)
  by_contra hcon
  push_neg at hcon
  obtain ⟨lam, hlam, hlt⟩ := exists_lt_moreauEnvelopeEReal_of_lt hl hm hcon
  rw [he lam hlam, EReal.coe_lt_coe_iff] at hlt
  set z := a • x₁ + b • x₂ with hz
  have h1 := hsupp lam hlam z x₁
  have h2 := hsupp lam hlam z x₂
  have h1' : e lam x₁ ≤ β₁ := EReal.coe_le_coe_iff.1 ((hle lam hlam x₁).trans hp₁)
  have h2' : e lam x₂ ≤ β₂ := EReal.coe_le_coe_iff.1 ((hle lam hlam x₂).trans hp₂)
  have hcomb : a * ⟪v lam z, x₁ - z⟫_ℝ + b * ⟪v lam z, x₂ - z⟫_ℝ = 0 := by
    rw [← real_inner_smul_right, ← real_inner_smul_right, ← inner_add_right]
    have h0 : a • (x₁ - z) + b • (x₂ - z) = 0 := by
      rw [smul_sub, smul_sub]
      calc a • x₁ - a • z + (b • x₂ - b • z) = (a • x₁ + b • x₂) - (a + b) • z := by
            rw [add_smul]; abel
        _ = 0 := by rw [hab, one_smul, ← hz, sub_self]
    rw [h0, inner_zero_right]
  have hez : a * e lam z + b * e lam z = e lam z := by rw [← add_mul, hab, one_mul]
  have i1 := mul_le_mul_of_nonneg_left (h1.trans h1') ha
  have i2 := mul_le_mul_of_nonneg_left (h2.trans h2') hb
  rw [mul_add] at i1 i2
  linarith

end Core

section Barrier

/-- The one-dimensional profile of the ball barrier: `s / (r² - t)` for
`t < r²` and `⊤` beyond. -/
noncomputable def ballBarrierProfile (r s t : ℝ) : EReal :=
  if t < r ^ 2 then ((s / (r ^ 2 - t) : ℝ) : EReal) else ⊤

theorem ballBarrierProfile_of_lt {r s t : ℝ} (ht : t < r ^ 2) :
    ballBarrierProfile r s t = ((s / (r ^ 2 - t) : ℝ) : EReal) := if_pos ht

theorem ballBarrierProfile_of_le {r s t : ℝ} (ht : r ^ 2 ≤ t) :
    ballBarrierProfile r s t = ⊤ := if_neg (not_lt.2 ht)

theorem ballBarrierProfile_nonneg {r s : ℝ} (hs : 0 ≤ s) (t : ℝ) :
    0 ≤ ballBarrierProfile r s t := by
  by_cases ht : t < r ^ 2
  · rw [ballBarrierProfile_of_lt ht]
    exact EReal.coe_nonneg.2 (div_nonneg hs (by linarith))
  · rw [ballBarrierProfile_of_le (not_lt.1 ht)]
    exact le_top

/-- The barrier profile is lower semicontinuous: it blows up at `t = r²`. -/
theorem lowerSemicontinuous_ballBarrierProfile {r s : ℝ} (hs : 0 < s) :
    LowerSemicontinuous (ballBarrierProfile r s) := by
  intro t α hα
  by_cases ht : t < r ^ 2
  · have hne : r ^ 2 - t ≠ 0 := by linarith
    have hcont : ContinuousAt (fun t' : ℝ ↦ ((s / (r ^ 2 - t') : ℝ) : EReal)) t :=
      continuous_coe_real_ereal.continuousAt.comp
        (continuousAt_const.div (continuousAt_const.sub continuousAt_id) hne)
    rw [ballBarrierProfile_of_lt ht] at hα
    filter_upwards [Iio_mem_nhds ht, hcont.eventually (lt_mem_nhds hα)] with t' ht' hlt
    rw [ballBarrierProfile_of_lt ht']
    exact hlt
  · push_neg at ht
    induction α using EReal.rec with
    | bot =>
      exact Eventually.of_forall fun t' ↦
        (EReal.bot_lt_zero).trans_le (ballBarrierProfile_nonneg hs.le t')
    | top =>
      rw [ballBarrierProfile_of_le ht] at hα
      exact absurd hα (lt_irrefl _)
    | coe a =>
      set ε := s / (|a| + 1) with hεdef
      have hε : 0 < ε := by positivity
      filter_upwards [Ioi_mem_nhds (show r ^ 2 - ε < t by linarith)] with t' ht'
      rw [mem_Ioi] at ht'
      by_cases h' : t' < r ^ 2
      · rw [ballBarrierProfile_of_lt h']
        change (a : EReal) < ((s / (r ^ 2 - t') : ℝ) : EReal)
        rw [EReal.coe_lt_coe_iff]
        have hpos : 0 < r ^ 2 - t' := by linarith
        have hlt : r ^ 2 - t' < ε := by linarith
        calc a < |a| + 1 := by linarith [le_abs_self a]
          _ = s / ε := by rw [hεdef]; field_simp
          _ < s / (r ^ 2 - t') := div_lt_div_of_pos_left hs hpos hlt
      · rw [ballBarrierProfile_of_le (not_lt.1 h')]
        exact EReal.coe_lt_top a

variable {E : Type*} [NormedAddCommGroup E]

/-- The barrier `s (r² - ‖y - c‖²)⁻¹` of the open ball `B(c, r)`, equal to `⊤`
off the ball. -/
noncomputable def ballBarrier (c : E) (r s : ℝ) (y : E) : EReal :=
  ballBarrierProfile r s (‖y - c‖ ^ 2)

theorem lowerSemicontinuous_ballBarrier (c : E) {r s : ℝ} (hs : 0 < s) :
    LowerSemicontinuous (ballBarrier c r s) :=
  (lowerSemicontinuous_ballBarrierProfile hs).comp (by fun_prop)

theorem ballBarrier_nonneg (c : E) {r s : ℝ} (hs : 0 ≤ s) (y : E) : 0 ≤ ballBarrier c r s y :=
  ballBarrierProfile_nonneg hs _

theorem norm_sub_sq_lt_iff_mem_ball {c y : E} {r : ℝ} (hr : 0 ≤ r) :
    ‖y - c‖ ^ 2 < r ^ 2 ↔ y ∈ ball c r := by
  rw [sq_lt_sq₀ (norm_nonneg _) hr, mem_ball, dist_eq_norm]

variable [InnerProductSpace ℝ E]

/-- The real barrier formula has the explicit gradient
`2s (r² - ‖y - c‖²)⁻² (y - c)`. -/
theorem hasGradientAt_ballBarrierFormula [CompleteSpace E] (c : E) {r s : ℝ} {y : E}
    (hy : r ^ 2 - ‖y - c‖ ^ 2 ≠ 0) :
    HasGradientAt (fun y' ↦ s / (r ^ 2 - ‖y' - c‖ ^ 2))
      ((2 * s / (r ^ 2 - ‖y - c‖ ^ 2) ^ 2) • (y - c)) y := by
  have hq : HasFDerivAt (fun y' : E ↦ ‖y' - c‖ ^ 2)
      (2 • (innerSL ℝ (y - c)).comp (ContinuousLinearMap.id ℝ E)) y :=
    ((hasFDerivAt_id y).sub_const c).norm_sq
  have hφ : HasDerivAt (fun t : ℝ ↦ s / (r ^ 2 - t)) (s / (r ^ 2 - ‖y - c‖ ^ 2) ^ 2)
      (‖y - c‖ ^ 2) := by
    have h := (hasDerivAt_const (‖y - c‖ ^ 2) s).div
      ((hasDerivAt_id (‖y - c‖ ^ 2)).const_sub (r ^ 2)) hy
    convert h using 1
    simp
  have hcomp := hφ.comp_hasFDerivAt y hq
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hcomp using 1
  ext w
  simp only [InnerProductSpace.toDual_apply_apply, real_inner_smul_left,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.coe_id', id_eq, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul,
    Nat.cast_ofNat]
  ring

theorem contDiffAt_ballBarrierFormula (c : E) {r s : ℝ} {y : E}
    (hy : r ^ 2 - ‖y - c‖ ^ 2 ≠ 0) :
    ContDiffAt ℝ 1 (fun y' ↦ s / (r ^ 2 - ‖y' - c‖ ^ 2)) y :=
  contDiffAt_const.div (contDiffAt_const.sub ((contDiffAt_id.sub contDiffAt_const).norm_sq ℝ)) hy

/-- The barrier gradient is monotone on the open ball. -/
theorem inner_ballBarrierGradient_sub_nonneg {c y₀ y₁ : E} {r s : ℝ} (hs : 0 ≤ s)
    (h₀ : ‖y₀ - c‖ ^ 2 < r ^ 2) (h₁ : ‖y₁ - c‖ ^ 2 < r ^ 2) :
    0 ≤ ⟪(2 * s / (r ^ 2 - ‖y₁ - c‖ ^ 2) ^ 2) • (y₁ - c) -
      (2 * s / (r ^ 2 - ‖y₀ - c‖ ^ 2) ^ 2) • (y₀ - c), y₁ - y₀⟫_ℝ := by
  have hy : y₁ - y₀ = (y₁ - c) - (y₀ - c) := by abel
  rw [hy]
  set u₀ := y₀ - c
  set u₁ := y₁ - c
  set α₀ := 2 * s / (r ^ 2 - ‖u₀‖ ^ 2) ^ 2 with hα₀def
  set α₁ := 2 * s / (r ^ 2 - ‖u₁‖ ^ 2) ^ 2 with hα₁def
  have hexp : ⟪α₁ • u₁ - α₀ • u₀, u₁ - u₀⟫_ℝ =
      α₁ * ‖u₁‖ ^ 2 + α₀ * ‖u₀‖ ^ 2 - (α₀ + α₁) * ⟪u₀, u₁⟫_ℝ := by
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_self_eq_norm_sq, real_inner_comm u₀ u₁]
    ring
  rw [hexp]
  have hcs : ⟪u₀, u₁⟫_ℝ ≤ ‖u₀‖ * ‖u₁‖ := real_inner_le_norm u₀ u₁
  have hd₀ : 0 < r ^ 2 - ‖u₀‖ ^ 2 := by linarith
  have hd₁ : 0 < r ^ 2 - ‖u₁‖ ^ 2 := by linarith
  have hα₀ : 0 ≤ α₀ := by positivity
  have hα₁ : 0 ≤ α₁ := by positivity
  have hmonoα : ∀ {d₀ d₁ : ℝ}, 0 < d₁ → d₁ ≤ d₀ → 2 * s / d₀ ^ 2 ≤ 2 * s / d₁ ^ 2 :=
    fun hd₁ hle ↦ div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ hd₁.le hle 2)
  have key : 0 ≤ (α₁ * ‖u₁‖ - α₀ * ‖u₀‖) * (‖u₁‖ - ‖u₀‖) := by
    rcases le_total ‖u₀‖ ‖u₁‖ with hle | hle
    · have hα : α₀ ≤ α₁ := hmonoα hd₁ (by nlinarith [norm_nonneg u₀])
      exact mul_nonneg (by nlinarith [norm_nonneg u₀, mul_le_mul hα hle (norm_nonneg _) hα₁])
        (by linarith)
    · have hα : α₁ ≤ α₀ := hmonoα hd₀ (by nlinarith [norm_nonneg u₁])
      exact mul_nonneg_of_nonpos_of_nonpos
        (by nlinarith [norm_nonneg u₁, mul_le_mul hα hle (norm_nonneg _) hα₀]) (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hcs (add_nonneg hα₀ hα₁)]

end Barrier

section Localization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem indicatorVA_nonneg (C : Set E) (y : E) : 0 ≤ indicatorVA C y := by
  unfold indicatorVA
  split_ifs <;> simp

/-- Subgradients of `f + s(r² - ‖· - c‖²)⁻¹` live on the open ball, where they
are the subgradients of `f` translated by the barrier gradient (8.8(c)). -/
theorem mem_subdifferential_add_ballBarrier {f : E → EReal} (hf : ∀ y, ⊥ < f y) {c : E}
    {r s : ℝ} {y w : E} (hw : w ∈ subdifferential (fun y ↦ f y + ballBarrier c r s y) y) :
    ‖y - c‖ ^ 2 < r ^ 2 ∧ ∃ u ∈ subdifferential f y,
      w = u + (2 * s / (r ^ 2 - ‖y - c‖ ^ 2) ^ 2) • (y - c) := by
  obtain ⟨a, ha⟩ := hw.1
  have ha' : f y + ballBarrier c r s y = (a : EReal) := ha
  have hin : ‖y - c‖ ^ 2 < r ^ 2 := by
    by_contra hout
    rw [ballBarrier, ballBarrierProfile_of_le (not_lt.1 hout),
      EReal.add_top_of_ne_bot (hf y).ne'] at ha'
    exact EReal.coe_ne_top a ha'.symm
  refine ⟨hin, ?_⟩
  have hb : ballBarrier c r s y = ((s / (r ^ 2 - ‖y - c‖ ^ 2) : ℝ) : EReal) :=
    ballBarrierProfile_of_lt hin
  have hfy_top : f y ≠ ⊤ := by
    intro htop
    rw [htop, hb, EReal.top_add_coe] at ha'
    exact EReal.coe_ne_top a ha'.symm
  have hfy : f y = ((f y).toReal : EReal) := (EReal.coe_toReal hfy_top (hf y).ne').symm
  have hopen : IsOpen {y' : E | ‖y' - c‖ ^ 2 < r ^ 2} :=
    isOpen_lt (by fun_prop) continuous_const
  have heq : (fun y' ↦ f y' + ballBarrier c r s y') =ᶠ[𝓝 y]
      fun y' ↦ f y' + ((s / (r ^ 2 - ‖y' - c‖ ^ 2) : ℝ) : EReal) := by
    filter_upwards [hopen.mem_nhds hin] with y' hy'
    rw [ballBarrier, ballBarrierProfile_of_lt hy']
  have hval : (fun y' ↦ f y' + ballBarrier c r s y') y =
      (((f y).toReal + s / (r ^ 2 - ‖y - c‖ ^ 2) : ℝ) : EReal) := by
    change f y + ballBarrier c r s y = _
    rw [hfy, hb, ← EReal.coe_add, EReal.toReal_coe]
  rw [subdifferential_congr_nhds_of_finite (f := fun y' ↦ f y' + ballBarrier c r s y')
    (g := fun y' ↦ f y' + ((s / (r ^ 2 - ‖y' - c‖ ^ 2) : ℝ) : EReal)) (x := y) hval heq] at hw
  have hne : r ^ 2 - ‖y - c‖ ^ 2 ≠ 0 := by linarith
  rw [(subdifferentials_add_smooth hfy (contDiffAt_ballBarrierFormula c (s := s) hne)).2.1] at hw
  obtain ⟨u, hu, rfl⟩ := hw
  refine ⟨u, hu, ?_⟩
  rw [(hasGradientAt_ballBarrierFormula c (s := s) hne).gradient]

/-- **Localization for Theorem 12.17.** If `f` is lower semicontinuous, never
`-∞`, and `∂f` is monotone on an open ball, then `f` is convex on that ball,
that is, `f + δ_B` is convex for the ball `B`.

For `s > 0` the function `f + s(r² - ‖· - c‖²)⁻¹` is proper (when `f` is finite
somewhere in the ball), lsc, bounded below and has a monotone subgradient
mapping, so it is convex by the core lemma.  Letting `s ↘ 0` gives the
convexity inequality for `f` on the ball. -/
theorem convex_epigraph_add_indicator_ball_of_monotoneOn {f : E → EReal} (hf : ∀ y, ⊥ < f y)
    (hl : LowerSemicontinuous f) (c : E) {r : ℝ} (hr : 0 < r)
    (hmono : ∀ ⦃x₀ v₀ : E⦄, x₀ ∈ ball c r → v₀ ∈ subdifferential f x₀ →
      ∀ ⦃x₁ v₁ : E⦄, x₁ ∈ ball c r → v₁ ∈ subdifferential f x₁ → 0 ≤ ⟪v₁ - v₀, x₁ - x₀⟫_ℝ) :
    Convex ℝ (epigraph fun y ↦ f y + indicatorVA (ball c r) y) := by
  obtain ⟨x₀, -, hx₀⟩ := (hl.lowerSemicontinuousOn (closedBall c r)).exists_isMinOn
    (nonempty_closedBall.2 hr.le) (isCompact_closedBall c r)
  obtain ⟨m, -, hm₀⟩ := EReal.lt_iff_exists_real_btwn.1 (hf x₀)
  have hmB : ∀ y ∈ closedBall c r, (m : EReal) ≤ f y := fun y hy ↦ hm₀.le.trans (hx₀ hy)
  have hmem : ∀ {x : E} {β : ℝ}, f x + indicatorVA (ball c r) x ≤ (β : EReal) →
      x ∈ ball c r ∧ f x ≤ β := by
    intro x β h
    by_cases hx : x ∈ ball c r
    · rw [indicatorVA, if_pos hx, add_zero] at h
      exact ⟨hx, h⟩
    · rw [indicatorVA, if_neg hx, EReal.add_top_of_ne_bot (hf x).ne'] at h
      exact absurd h (not_le.2 (EReal.coe_lt_top β))
  rintro ⟨x₁, β₁⟩ hp₁ ⟨x₂, β₂⟩ hp₂ a b ha hb hab
  obtain ⟨hx₁, hf₁⟩ := hmem (β := β₁) hp₁
  obtain ⟨hx₂, hf₂⟩ := hmem (β := β₂) hp₂
  have hz : a • x₁ + b • x₂ ∈ ball c r := (convex_ball c r) hx₁ hx₂ ha hb hab
  change f (a • x₁ + b • x₂) + indicatorVA (ball c r) (a • x₁ + b • x₂) ≤
    ((a * β₁ + b * β₂ : ℝ) : EReal)
  rw [indicatorVA, if_pos hz, add_zero]
  have hin₁ : ‖x₁ - c‖ ^ 2 < r ^ 2 := (norm_sub_sq_lt_iff_mem_ball hr.le).2 hx₁
  have hin₂ : ‖x₂ - c‖ ^ 2 < r ^ 2 := (norm_sub_sq_lt_iff_mem_ball hr.le).2 hx₂
  have hg₁ : 0 ≤ 1 / (r ^ 2 - ‖x₁ - c‖ ^ 2) := div_nonneg zero_le_one (by linarith)
  have hg₂ : 0 ≤ 1 / (r ^ 2 - ‖x₂ - c‖ ^ 2) := div_nonneg zero_le_one (by linarith)
  set K := a * (1 / (r ^ 2 - ‖x₁ - c‖ ^ 2)) + b * (1 / (r ^ 2 - ‖x₂ - c‖ ^ 2)) with hKdef
  have hK0 : 0 ≤ K := add_nonneg (mul_nonneg ha hg₁) (mul_nonneg hb hg₂)
  have hbound : ∀ s : ℝ, 0 < s →
      f (a • x₁ + b • x₂) ≤ ((a * β₁ + b * β₂ + s * K : ℝ) : EReal) := by
    intro s hs
    have hbnd : ∀ y, ⊥ < ballBarrier c r s y :=
      fun y ↦ EReal.bot_lt_zero.trans_le (ballBarrier_nonneg c hs.le y)
    have hHp : IsProper fun y ↦ f y + ballBarrier c r s y := by
      refine ⟨⟨x₁, ?_⟩, fun y ↦ EReal.bot_lt_add_iff.2 ⟨hf y, hbnd y⟩⟩
      change f x₁ + ballBarrier c r s x₁ < ⊤
      rw [ballBarrier, ballBarrierProfile_of_lt hin₁]
      exact EReal.add_lt_top (ne_top_of_le_ne_top (EReal.coe_ne_top β₁) hf₁) (EReal.coe_ne_top _)
    have hHl : LowerSemicontinuous fun y ↦ f y + ballBarrier c r s y :=
      hl.add' (lowerSemicontinuous_ballBarrier c hs) fun y ↦
        EReal.continuousAt_add (Or.inr (hbnd y).ne') (Or.inl (hf y).ne')
    have hHm : ∀ y, (m : EReal) ≤ f y + ballBarrier c r s y := by
      intro y
      by_cases hy : ‖y - c‖ ^ 2 < r ^ 2
      · have hyB : y ∈ closedBall c r :=
          ball_subset_closedBall ((norm_sub_sq_lt_iff_mem_ball hr.le).1 hy)
        exact (hmB y hyB).trans (le_add_of_nonneg_right (ballBarrier_nonneg c hs.le y))
      · rw [ballBarrier, ballBarrierProfile_of_le (not_lt.1 hy),
          EReal.add_top_of_ne_bot (hf y).ne']
        exact le_top
    have hHmono : SvMonotone (subdifferential fun y ↦ f y + ballBarrier c r s y) := by
      intro y₀ w₀ hw₀ y₁ w₁ hw₁
      obtain ⟨hy₀, u₀, hu₀, rfl⟩ := mem_subdifferential_add_ballBarrier hf hw₀
      obtain ⟨hy₁, u₁, hu₁, rfl⟩ := mem_subdifferential_add_ballBarrier hf hw₁
      have h1 := hmono ((norm_sub_sq_lt_iff_mem_ball hr.le).1 hy₀) hu₀
        ((norm_sub_sq_lt_iff_mem_ball hr.le).1 hy₁) hu₁
      have h2 := inner_ballBarrierGradient_sub_nonneg (c := c) hs.le hy₀ hy₁
      rw [add_sub_add_comm, inner_add_left]
      linarith
    have hconv :=
      convex_epigraph_of_svMonotone_subdifferential_of_bddBelow hHp hHl hHm hHmono
    have hq : ∀ {x : E} {β : ℝ}, ‖x - c‖ ^ 2 < r ^ 2 → f x ≤ (β : EReal) →
        (x, β + s * (1 / (r ^ 2 - ‖x - c‖ ^ 2))) ∈
          epigraph fun y ↦ f y + ballBarrier c r s y := by
      intro x β hin hfx
      change f x + ballBarrier c r s x ≤ ((β + s * (1 / (r ^ 2 - ‖x - c‖ ^ 2)) : ℝ) : EReal)
      rw [ballBarrier, ballBarrierProfile_of_lt hin, EReal.coe_add, mul_one_div]
      exact add_le_add hfx le_rfl
    have hqz := hconv (hq hin₁ hf₁) (hq hin₂ hf₂) ha hb hab
    change f (a • x₁ + b • x₂) + ballBarrier c r s (a • x₁ + b • x₂) ≤
      ((a * (β₁ + s * (1 / (r ^ 2 - ‖x₁ - c‖ ^ 2))) +
        b * (β₂ + s * (1 / (r ^ 2 - ‖x₂ - c‖ ^ 2))) : ℝ) : EReal) at hqz
    calc f (a • x₁ + b • x₂) ≤ f (a • x₁ + b • x₂) + ballBarrier c r s (a • x₁ + b • x₂) :=
          le_add_of_nonneg_right (ballBarrier_nonneg c hs.le _)
      _ ≤ _ := hqz
      _ = ((a * β₁ + b * β₂ + s * K : ℝ) : EReal) := by
          rw [hKdef]
          congr 1
          ring
  by_contra hcon
  push_neg at hcon
  obtain ⟨γ, hγ₁, hγ₂⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
  rw [EReal.coe_lt_coe_iff] at hγ₁
  set s := (γ - (a * β₁ + b * β₂)) / (K + 1) with hsdef
  have hs : 0 < s := div_pos (by linarith) (by linarith)
  have hsK : s * K < γ - (a * β₁ + b * β₂) := by
    rw [hsdef, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  have hlt := (hbound s hs).trans_lt
    (EReal.coe_lt_coe_iff.2 (show a * β₁ + b * β₂ + s * K < γ by linarith))
  exact absurd (hlt.trans hγ₂) (lt_irrefl _)

/-- **Theorem 12.17**, converse half: a proper lsc function with a monotone
subgradient mapping is convex. -/
theorem convex_epigraph_of_svMonotone_subdifferential {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hmono : SvMonotone (subdifferential f)) :
    Convex ℝ (epigraph f) := by
  rintro ⟨x₁, β₁⟩ hp₁ ⟨x₂, β₂⟩ hp₂ a b ha hb hab
  have hr : (0 : ℝ) < ‖x₁‖ + ‖x₂‖ + 1 := by positivity
  have hball := convex_epigraph_add_indicator_ball_of_monotoneOn hp.2 hl 0 hr
    (fun _ _ _ h₀ _ _ _ h₁ ↦ hmono h₀ h₁)
  have hx₁ : x₁ ∈ ball (0 : E) (‖x₁‖ + ‖x₂‖ + 1) := by
    rw [mem_ball_zero_iff]
    linarith [norm_nonneg x₂]
  have hx₂ : x₂ ∈ ball (0 : E) (‖x₁‖ + ‖x₂‖ + 1) := by
    rw [mem_ball_zero_iff]
    linarith [norm_nonneg x₁]
  have hq : ∀ {x : E} {β : ℝ}, x ∈ ball (0 : E) (‖x₁‖ + ‖x₂‖ + 1) → f x ≤ (β : EReal) →
      (x, β) ∈ epigraph fun y ↦ f y + indicatorVA (ball (0 : E) (‖x₁‖ + ‖x₂‖ + 1)) y := by
    intro x β hx hfx
    change f x + indicatorVA _ x ≤ (β : EReal)
    rw [indicatorVA, if_pos hx, add_zero]
    exact hfx
  have hqz := hball (hq hx₁ hp₁) (hq hx₂ hp₂) ha hb hab
  change f (a • x₁ + b • x₂) + indicatorVA _ (a • x₁ + b • x₂) ≤
    ((a * β₁ + b * β₂ : ℝ) : EReal) at hqz
  change f (a • x₁ + b • x₂) ≤ ((a * β₁ + b * β₂ : ℝ) : EReal)
  exact (le_add_of_nonneg_right (indicatorVA_nonneg _ _)).trans hqz

end Localization

end RW
