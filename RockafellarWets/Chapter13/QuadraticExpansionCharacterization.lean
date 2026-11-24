/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Second derivatives and quadratic expansions of prox-regular functions

Corollary 13.42 (`second_derivatives_and_quadratic_expansions`).  For `f` prox-regular at `x̄` for
`v̄ = ∇f(x̄)`: (a) twice differentiability in the extended sense, (b) differentiability of `∂f` at
`x̄`, and (c) a quadratic expansion at `x̄` are equivalent; then `∇²f(x̄)` is symmetric and `f` is
lower-`C²` around `x̄`.

(a) ⇔ (b) is 13.2(c) and (a) ⇒ (c) is 13.2(b).  For (c) ⇒ (b): by 13.8 `f` is twice
epi-differentiable at `x̄` for `v̄` with `d²f(x̄ | v̄)(w) = ⟪w, Aw⟫`.  In the reduction of Theorem
13.40 (`IsProxRegularAt.exists_proxCore`) the rescaled gradients `Gτ` of `G = ∇e_λ f₁` converge to
`G₀` with `G₀(u) = A_s(u - λG₀(u))`, `A_s = ½(A + A*)` (`ProxCore.eq_symmPart_of_tendsto`), uniformly
on bounded sets, so `G(x̄ + h) = G₀(h) + o(‖h‖)` (`ProxCore.exists_norm_G_sub_le`).  Then
`⟪P(x̄ + h) - x̄, h⟫ ≥ m‖h‖²` near `x̄` for `P = P_λ f₁` (`ProxCore.exists_P_G_expansion`), and since
`P = ∇(½‖·‖² - λe_λ f₁)` minimizing `½‖u‖² - λe_λ f₁(u) - ⟪y, u⟫` over a small ball shows that `P`
maps a neighborhood of `x̄` onto a neighborhood of `x̄` (`ProxCore.exists_P_eq`).  Every point near
`x̄` thus has a subgradient near `v̄`; prox-regularity makes it a regular subgradient, and convexity
of the regular subdifferential excludes subgradients far from `v̄`.  The expansion of `G` and `P`
then gives `∂f(y) ⊂ v̄ + A_s(y - x̄) + o(‖y - x̄‖)IB`, i.e. (b), with `∇²f(x̄) = A_s`.
-/

import RockafellarWets.Chapter13.HessianSymmetry
import RockafellarWets.Chapter13.LowerC2ProxRegularity
import RockafellarWets.Chapter13.DerivativeCoderivativeInclusion

open Filter Set Topology Metric
open scoped InnerProductSpace RealInnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### Auxiliary facts -/

/-- The symmetric part `A_s = ½(A + A*)` of `A`. -/
noncomputable def symmPart (A : E →L[ℝ] E) : E →L[ℝ] E :=
  (1 / 2 : ℝ) • (A + ContinuousLinearMap.adjoint A)

theorem inner_symmPart_left (A : E →L[ℝ] E) (u w : E) :
    ⟪symmPart A u, w⟫_ℝ = (⟪A u, w⟫_ℝ + ⟪u, A w⟫_ℝ) / 2 := by
  simp only [symmPart, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    real_inner_smul_left, inner_add_left, ContinuousLinearMap.adjoint_inner_left]
  ring

theorem inner_self_symmPart (A : E →L[ℝ] E) (w : E) : ⟪w, symmPart A w⟫_ℝ = ⟪w, A w⟫_ℝ := by
  rw [real_inner_comm, inner_symmPart_left, real_inner_comm (A w) w]; ring

/-- A function `t ↦ αt + βt²` that is nonnegative on `ℝ` has `α = 0`. -/
theorem eq_zero_of_forall_mul_add_sq_nonneg {α β : ℝ} (h : ∀ t : ℝ, 0 ≤ α * t + β * t ^ 2) :
    α = 0 := by
  by_contra hα
  set s := 1 / (|β| + 1) with hs_def
  have hs : 0 < s := by positivity
  have hβs : β * s < 1 := by
    have : β < |β| + 1 := by linarith [le_abs_self β]
    rw [hs_def, mul_one_div, div_lt_one (by positivity)]
    exact this
  have h1 := h (-α * s)
  have hα2 : 0 < α ^ 2 := by positivity
  nlinarith [mul_lt_mul_of_pos_left hβs (mul_pos hα2 hs)]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Pointwise convergence of eventually equi-Lipschitz maps on a compact set is uniform there. -/
theorem eventually_uniform_of_lipschitzOn {ι : Type*} {l : Filter ι} {G : ι → E → E} {g : E → E}
    {B : Set E} (hB : IsCompact B) {L : ℝ} (hL0 : 0 ≤ L)
    (hG : ∀ᶠ i in l, ∀ u ∈ B, ∀ u' ∈ B, ‖G i u - G i u'‖ ≤ L * ‖u - u'‖)
    (hg : ∀ u ∈ B, ∀ u' ∈ B, ‖g u - g u'‖ ≤ L * ‖u - u'‖)
    (h : ∀ u ∈ B, Tendsto (fun i ↦ G i u) l (𝓝 (g u))) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ i in l, ∀ u ∈ B, ‖G i u - g u‖ ≤ η := by
  set δ := η / (3 * (L + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨t, htB, ht, hcover⟩ := finite_cover_balls_of_compact hB hδ0
  have hall : ∀ᶠ i in l, ∀ c ∈ t, ‖G i c - g c‖ < η / 3 := by
    refine (ht.eventually_all).2 fun c hc ↦ ?_
    filter_upwards [Metric.tendsto_nhds.1 (h c (htB hc)) (η / 3) (by positivity)] with i hi
    rwa [dist_eq_norm] at hi
  have hLδ : L * δ ≤ η / 3 := by
    have e : L * δ = η / 3 * (L / (L + 1)) := by rw [hδ]; field_simp
    rw [e]
    have : L / (L + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    nlinarith
  filter_upwards [hG, hall] with i hGi hi u hu
  obtain ⟨c, hct, hc⟩ : ∃ c ∈ t, u ∈ ball c δ := by
    simpa only [mem_iUnion, exists_prop] using hcover hu
  rw [mem_ball, dist_eq_norm] at hc
  have h1 := hGi u hu c (htB hct)
  have h2 := hg c (htB hct) u hu
  have h3 := hi c hct
  rw [norm_sub_rev c u] at h2
  have h4 : L * ‖u - c‖ ≤ L * δ := mul_le_mul_of_nonneg_left hc.le hL0
  calc ‖G i u - g u‖ = ‖(G i u - G i c) + (G i c - g c) + (g c - g u)‖ := by congr 1; abel
    _ ≤ ‖G i u - G i c‖ + ‖G i c - g c‖ + ‖g c - g u‖ := norm_add₃_le
    _ ≤ η := by linarith

/-! ### The core of Theorem 13.40 when `d²f(x̄ | 0)` is quadratic -/

namespace ProxCore

variable {f : E → EReal} {x : E} {ε : ℝ} (K : ProxCore f x ε) {A : E →L[ℝ] E} {G₀ : E → E}

omit [FiniteDimensional ℝ E] in
theorem P_eq_sub (u : E) : K.P u = u - K.lam • K.G u := eq_sub_of_add_eq (K.P_add_G u)

/-- When `d²f(x̄ | 0)(w) = ⟪w, Aw⟫`, a limit `z` of `Gτ(u)` solves `z = A_s(u - λz)`. -/
theorem eq_symmPart_of_tendsto (hte : TwiceEpiDifferentiableAt f x 0)
    (hq : ∀ w, secondSubderivative f x 0 w = ((⟪w, A w⟫_ℝ : ℝ) : EReal)) {u z : E}
    (hz : Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 z)) :
    z = symmPart A (u - K.lam • z) := by
  have hseq : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n ↦ mem_Ioi.2 (by positivity)⟩
  obtain ⟨a, ha, hle⟩ := K.limitChar_of_tendsto hte hseq (hz.comp hseq)
  set w := u - K.lam • z with hw
  rw [hq, EReal.coe_eq_coe_iff] at ha
  refine ext_inner_right ℝ fun h ↦ ?_
  have key : ∀ t : ℝ, 0 ≤ (⟪w, A h⟫_ℝ + ⟪h, A w⟫_ℝ - 2 * ⟪z, h⟫_ℝ) * t +
      (⟪h, A h⟫_ℝ + K.mu * ‖h‖ ^ 2) * t ^ 2 := by
    intro t
    have h1 := hle (w + t • h)
    rw [hq, EReal.coe_le_coe_iff, ← ha] at h1
    simp only [add_sub_cancel_left, map_add, map_smul, inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right, norm_smul, Real.norm_eq_abs, RCLike.conj_to_real,
      mul_pow, sq_abs] at h1
    nlinarith
  have h0 := eq_zero_of_forall_mul_add_sq_nonneg key
  rw [inner_symmPart_left]
  rw [real_inner_comm (A w) h] at h0
  linarith

omit [FiniteDimensional ℝ E] in
/-- `G₀ 0 = 0`. -/
theorem G₀_zero (hG₀ : ∀ u, Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 (G₀ u))) : G₀ 0 = 0 :=
  tendsto_nhds_unique (hG₀ 0) (tendsto_const_nhds.congr fun τ ↦ (K.Gs_zero τ).symm)

/-- `G(x̄ + h) = G₀(h) + o(‖h‖)`: the convergence of `Gτ` is uniform on the unit ball. -/
theorem exists_norm_G_sub_le (hG₀ : ∀ u, Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 (G₀ u)))
    {η : ℝ} (hη : 0 < η) :
    ∃ ρ > 0, ∀ h : E, ‖h‖ ≤ ρ → ‖K.G (x + h) - G₀ h‖ ≤ η * ‖h‖ := by
  have hlam := K.hlam
  have hL0 : (0 : ℝ) ≤ 3 / K.lam := by positivity
  have hlipev : ∀ᶠ τ in 𝓝[>] (0 : ℝ), ∀ u ∈ closedBall (0 : E) 1, ∀ u' ∈ closedBall (0 : E) 1,
      ‖K.Gs τ u - K.Gs τ u'‖ ≤ 3 / K.lam * ‖u - u'‖ := by
    filter_upwards [self_mem_nhdsWithin, K.eventually_closedBall_subset 1] with τ hτ hsub
    exact fun u hu u' hu' ↦ K.Gs_lip hτ (hsub hu) (hsub hu')
  have hunif := eventually_uniform_of_lipschitzOn (l := 𝓝[>] (0 : ℝ)) (G := K.Gs) (g := G₀)
    (isCompact_closedBall (0 : E) 1) hL0 hlipev
    (fun u _ u' _ ↦ K.G₀_lip hG₀ u u') (fun u _ ↦ hG₀ u) hη
  obtain ⟨τ₀, hτ₀, hI⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hunif
  refine ⟨τ₀ / 2, half_pos (mem_Ioi.1 hτ₀), fun h hh ↦ ?_⟩
  rcases eq_or_ne h 0 with rfl | h0
  · simp [K.G_x, K.G₀_zero hG₀]
  have hn : 0 < ‖h‖ := norm_pos_iff.2 h0
  have hmem : ‖h‖ ∈ Ioo 0 τ₀ := ⟨hn, by linarith [mem_Ioi.1 hτ₀]⟩
  have hu : ‖h‖⁻¹ • h ∈ closedBall (0 : E) 1 := by
    rw [mem_closedBall, dist_zero_right, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have h1 := hI hmem _ hu
  have e1 : K.Gs ‖h‖ (‖h‖⁻¹ • h) = ‖h‖⁻¹ • K.G (x + h) := by
    simp only [Gs, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  have e2 : G₀ (‖h‖⁻¹ • h) = ‖h‖⁻¹ • G₀ h := K.G₀_smul hG₀ (inv_pos.2 hn) h
  rw [e1, e2, ← smul_sub, norm_smul, norm_inv, norm_norm, inv_mul_le_iff₀ hn] at h1
  linarith

/-- `⟪h - λG₀(h), h⟫ ≥ m‖h‖²` with `m = 1/(2(1 + λ‖A_s‖)²)`. -/
theorem inner_sub_G₀_ge (hte : TwiceEpiDifferentiableAt f x 0)
    (hq : ∀ w, secondSubderivative f x 0 w = ((⟪w, A w⟫_ℝ : ℝ) : EReal))
    (hG₀ : ∀ u, Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 (G₀ u))) (h : E) :
    1 / (2 * (1 + K.lam * ‖symmPart A‖) ^ 2) * ‖h‖ ^ 2 ≤ ⟪h - K.lam • G₀ h, h⟫_ℝ := by
  have hlam := K.hlam
  have hz := K.eq_symmPart_of_tendsto hte hq (hG₀ h)
  set w := h - K.lam • G₀ h with hw
  have hh : h = w + K.lam • symmPart A w := by rw [← hz, hw]; abel
  have hlow : -(K.mu * ‖w‖ ^ 2) ≤ ⟪w, A w⟫_ℝ := by
    have := K.neg_le_secondSubderivative w
    rwa [hq, EReal.coe_le_coe_iff] at this
  have hinner : ⟪w, h⟫_ℝ = ‖w‖ ^ 2 + K.lam * ⟪w, A w⟫_ℝ := by
    conv_lhs => rw [hh]
    rw [inner_add_right, real_inner_self_eq_norm_sq, real_inner_smul_right, inner_self_symmPart]
  have hc : 0 < 1 + K.lam * ‖symmPart A‖ := by positivity
  have hnorm : ‖h‖ ≤ (1 + K.lam * ‖symmPart A‖) * ‖w‖ := by
    calc ‖h‖ = ‖w + K.lam • symmPart A w‖ := by rw [← hh]
      _ ≤ ‖w‖ + ‖K.lam • symmPart A w‖ := norm_add_le _ _
      _ ≤ ‖w‖ + K.lam * (‖symmPart A‖ * ‖w‖) := by
          rw [norm_smul, Real.norm_of_nonneg hlam.le]
          gcongr
          exact (symmPart A).le_opNorm w
      _ = (1 + K.lam * ‖symmPart A‖) * ‖w‖ := by ring
  have hsq : ‖h‖ ^ 2 ≤ (1 + K.lam * ‖symmPart A‖) ^ 2 * ‖w‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hw2 : ‖w‖ ^ 2 / 2 ≤ ⟪w, h⟫_ℝ := by
    rw [hinner]
    nlinarith [mul_le_mul_of_nonneg_left hlow hlam.le,
      mul_le_mul_of_nonneg_right K.hlammu (sq_nonneg ‖w‖)]
  calc 1 / (2 * (1 + K.lam * ‖symmPart A‖) ^ 2) * ‖h‖ ^ 2 ≤
        1 / (2 * (1 + K.lam * ‖symmPart A‖) ^ 2) *
          ((1 + K.lam * ‖symmPart A‖) ^ 2 * ‖w‖ ^ 2) := by gcongr
    _ = ‖w‖ ^ 2 / 2 := by field_simp
    _ ≤ ⟪w, h⟫_ℝ := hw2

/-- The expansions of `P` and `G` at `x̄`: for some `m > 0` and every `η > 0`, for `‖h‖` small,
`⟪P(x̄ + h) - x̄, h⟫ ≥ m‖h‖²` and `‖G(x̄ + h) - A_s(P(x̄ + h) - x̄)‖ ≤ η‖h‖`. -/
theorem exists_P_G_expansion (hte : TwiceEpiDifferentiableAt f x 0)
    (hq : ∀ w, secondSubderivative f x 0 w = ((⟪w, A w⟫_ℝ : ℝ) : EReal))
    (hG₀ : ∀ u, Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 (G₀ u))) :
    ∃ m > 0, ∀ η > 0, ∃ ρ > 0, ρ < K.δ₀ ∧ ∀ h : E, ‖h‖ ≤ ρ →
      m * ‖h‖ ^ 2 ≤ ⟪K.P (x + h) - x, h⟫_ℝ ∧
      ‖K.G (x + h) - symmPart A (K.P (x + h) - x)‖ ≤ η * ‖h‖ := by
  have hlam := K.hlam
  set m₀ := 1 / (2 * (1 + K.lam * ‖symmPart A‖) ^ 2) with hm₀
  have hm₀0 : 0 < m₀ := by positivity
  have hc : 0 < 1 + K.lam * ‖symmPart A‖ := by positivity
  refine ⟨m₀ / 2, by positivity, fun η hη ↦ ?_⟩
  set η' := min (m₀ / (2 * K.lam)) (η / (1 + K.lam * ‖symmPart A‖)) with hη'
  have hη'0 : 0 < η' := lt_min (by positivity) (by positivity)
  obtain ⟨ρ, hρ, hest⟩ := K.exists_norm_G_sub_le hG₀ hη'0
  refine ⟨min ρ (K.δ₀ / 2), lt_min hρ (by have := K.hδ₀; positivity),
    lt_of_le_of_lt (min_le_right _ _) (by have := K.hδ₀; linarith), fun h hh ↦ ?_⟩
  have hhρ : ‖h‖ ≤ ρ := hh.trans (min_le_left _ _)
  set r := K.G (x + h) - G₀ h with hr
  have hrle : ‖r‖ ≤ η' * ‖h‖ := hest h hhρ
  have hz := K.eq_symmPart_of_tendsto hte hq (hG₀ h)
  have hP : K.P (x + h) - x = (h - K.lam • G₀ h) - K.lam • r := by
    rw [K.P_eq_sub, hr, smul_sub]; abel
  constructor
  · have h1 := K.inner_sub_G₀_ge hte hq hG₀ h
    have h2 : ⟪r, h⟫_ℝ ≤ η' * ‖h‖ * ‖h‖ :=
      (real_inner_le_norm r h).trans (mul_le_mul_of_nonneg_right hrle (norm_nonneg _))
    have h3 : K.lam * η' ≤ m₀ / 2 := by
      have : η' ≤ m₀ / (2 * K.lam) := min_le_left _ _
      calc K.lam * η' ≤ K.lam * (m₀ / (2 * K.lam)) := mul_le_mul_of_nonneg_left this hlam.le
        _ = m₀ / 2 := by field_simp
    rw [hP, inner_sub_left, real_inner_smul_left]
    nlinarith [mul_le_mul_of_nonneg_right h3 (sq_nonneg ‖h‖), mul_le_mul_of_nonneg_left h2 hlam.le]
  · have heq : K.G (x + h) - symmPart A (K.P (x + h) - x) = r + K.lam • symmPart A r := by
      rw [hP, map_sub, map_smul, ← hz, hr]; abel
    rw [heq]
    calc ‖r + K.lam • symmPart A r‖ ≤ ‖r‖ + K.lam * (‖symmPart A‖ * ‖r‖) := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, Real.norm_of_nonneg hlam.le]
          gcongr
          exact (symmPart A).le_opNorm r
      _ = (1 + K.lam * ‖symmPart A‖) * ‖r‖ := by ring
      _ ≤ (1 + K.lam * ‖symmPart A‖) * (η' * ‖h‖) := by gcongr
      _ ≤ (1 + K.lam * ‖symmPart A‖) * (η / (1 + K.lam * ‖symmPart A‖) * ‖h‖) := by
          gcongr; exact min_le_right _ _
      _ = η * ‖h‖ := by field_simp

/-- **Local surjectivity of `P`**: if `⟪P(x̄ + h) - x̄, h⟫ ≥ m‖h‖²` for `‖h‖ ≤ ρ`, then every `y`
with `‖y - x̄‖ < mρ/4` is `P(u)` for some `u` with `‖u - x̄‖ < ρ`.  The function
`φ(u) = ½‖u‖² - λe(u) - ⟪y, u⟫` has gradient `P(u) - y` and attains its minimum over `IB(x̄, ρ)`
in the interior. -/
theorem exists_P_eq {ρ m : ℝ} (hρ : 0 < ρ) (hρδ : ρ < K.δ₀) (hm : 0 < m)
    (hpos : ∀ h : E, ‖h‖ ≤ ρ → m * ‖h‖ ^ 2 ≤ ⟪K.P (x + h) - x, h⟫_ℝ) {y : E}
    (hy : ‖y - x‖ < m * ρ / 4) : ∃ u, ‖u - x‖ < ρ ∧ K.P u = y := by
  have hU : closedBall x ρ ⊆ proxRange f x ε K.lam := (closedBall_subset_ball hρδ).trans K.hball
  set φ : E → ℝ := fun u ↦ 1 / 2 * ‖u‖ ^ 2 - K.lam * K.e u - ⟪y, u⟫_ℝ with hφ
  have hφd : ∀ u ∈ proxRange f x ε K.lam, HasFDerivAt φ (innerSL ℝ (K.P u - y)) u := by
    intro u hu
    have h1 : HasFDerivAt (fun u : E ↦ 1 / 2 * ‖u‖ ^ 2) ((1 / 2 : ℝ) • (2 • innerSL ℝ u)) u :=
      ((hasStrictFDerivAt_norm_sq u).hasFDerivAt).const_mul (1 / 2)
    have he : HasFDerivAt K.e (innerSL ℝ (K.G u)) u := K.hderiv u hu
    have h2 := he.const_mul K.lam
    have h3 : HasFDerivAt (fun u ↦ ⟪y, u⟫_ℝ) (innerSL ℝ y) u := (innerSL ℝ y).hasFDerivAt
    have := (h1.sub h2).sub h3
    convert this using 1
    ext v
    simp only [innerSL_apply_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, K.P_eq_sub u, inner_sub_left, real_inner_smul_left]
    ring
  have hcont : ContinuousOn φ (closedBall x ρ) := fun u hu ↦
    (hφd u (hU hu)).continuousAt.continuousWithinAt
  obtain ⟨u, hu, hmin⟩ := (isCompact_closedBall x ρ).exists_isMinOn
    (nonempty_closedBall.2 hρ.le) hcont
  have hux : ‖u - x‖ ≤ ρ := by rwa [mem_closedBall, dist_eq_norm] at hu
  have hlt : ‖u - x‖ < ρ := by
    by_contra hnot
    have hρu : ‖u - x‖ = ρ := le_antisymm hux (not_lt.1 hnot)
    set h := u - x with hh
    have hmem : ∀ t ∈ Icc (0 : ℝ) 1, x + t • h ∈ proxRange f x ε K.lam := by
      intro t ht
      apply hU
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1,
        hρu]
      exact mul_le_of_le_one_left hρ.le ht.2
    set g : ℝ → ℝ := fun t ↦ φ (x + t • h) with hg
    have hgd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt g ⟪K.P (x + t • h) - y, h⟫_ℝ t := by
      intro t ht
      have hp : HasDerivAt (fun t : ℝ ↦ x + t • h) h t := by
        simpa using ((hasDerivAt_id t).smul_const h).const_add x
      have := (hφd _ (hmem t ht)).comp_hasDerivAt t hp
      rw [innerSL_apply_apply] at this
      exact this
    have hgc : ContinuousOn g (Icc 0 1) := fun t ht ↦ (hgd t ht).continuousAt.continuousWithinAt
    -- the derivative bound
    have hd : ∀ c ∈ Ioo (0 : ℝ) 1,
        m * c * ρ ^ 2 - ‖y - x‖ * ρ ≤ ⟪K.P (x + c • h) - y, h⟫_ℝ := by
      intro c hc
      have hch : ‖c • h‖ ≤ ρ := by
        rw [norm_smul, Real.norm_of_nonneg hc.1.le, hρu]
        exact mul_le_of_le_one_left hρ.le hc.2.le
      have h1 := hpos (c • h) hch
      rw [norm_smul, Real.norm_of_nonneg hc.1.le, hρu, real_inner_smul_right] at h1
      have h2 : m * c * ρ ^ 2 ≤ ⟪K.P (x + c • h) - x, h⟫_ℝ := by
        have : c * (m * c * ρ ^ 2) ≤ c * ⟪K.P (x + c • h) - x, h⟫_ℝ := by nlinarith
        exact le_of_mul_le_mul_left this hc.1
      have h3 : ⟪y - x, h⟫_ℝ ≤ ‖y - x‖ * ρ := by
        rw [← hρu]; exact real_inner_le_norm _ _
      have e : ⟪K.P (x + c • h) - y, h⟫_ℝ = ⟪K.P (x + c • h) - x, h⟫_ℝ - ⟪y - x, h⟫_ℝ := by
        rw [← inner_sub_left]; congr 1; abel
      rw [e]; linarith
    obtain ⟨c₀, hc₀, hs₀⟩ := exists_hasDerivAt_eq_slope g (fun t ↦ ⟪K.P (x + t • h) - y, h⟫_ℝ)
      (by norm_num : (0 : ℝ) < 1 / 2) (hgc.mono (Icc_subset_Icc le_rfl (by norm_num)))
      (fun t ht ↦ hgd t ⟨ht.1.le, by linarith [ht.2]⟩)
    obtain ⟨c₁, hc₁, hs₁⟩ := exists_hasDerivAt_eq_slope g (fun t ↦ ⟪K.P (x + t • h) - y, h⟫_ℝ)
      (by norm_num : (1 / 2 : ℝ) < 1) (hgc.mono (Icc_subset_Icc (by norm_num) le_rfl))
      (fun t ht ↦ hgd t ⟨by linarith [ht.1], ht.2.le⟩)
    have hd₀ := hd c₀ ⟨hc₀.1, by linarith [hc₀.2]⟩
    have hd₁ := hd c₁ ⟨by linarith [hc₁.1], hc₁.2⟩
    rw [hs₀] at hd₀
    rw [hs₁] at hd₁
    have hg1 : g 1 = φ u := by simp only [hg, one_smul, hh, add_sub_cancel]
    have hg0 : g 0 = φ x := by simp only [hg, zero_smul, add_zero]
    have hmx := hmin (mem_closedBall_self hρ.le)
    simp only [mem_setOf_eq] at hmx
    have hc₀m : 0 ≤ m * c₀ * ρ ^ 2 := by have := hc₀.1; positivity
    have hc₁m : m / 2 * ρ ^ 2 ≤ m * c₁ * ρ ^ 2 := by
      have := hc₁.1
      have : m / 2 ≤ m * c₁ := by nlinarith
      exact mul_le_mul_of_nonneg_right this (sq_nonneg ρ)
    have hyρ : ‖y - x‖ * ρ < m * ρ ^ 2 / 4 := by
      have := mul_lt_mul_of_pos_right hy hρ; nlinarith
    rw [div_eq_mul_inv] at hd₀ hd₁
    norm_num at hd₀ hd₁
    linarith
  have hloc : IsLocalMin φ u := hmin.isLocalMin (mem_of_superset
    (isOpen_ball.mem_nhds (by rwa [mem_ball, dist_eq_norm])) ball_subset_closedBall)
  have h0 := hloc.hasFDerivAt_eq_zero (hφd u (hU hu))
  refine ⟨u, hlt, ?_⟩
  have h1 := congrArg (fun L : E →L[ℝ] ℝ ↦ L (K.P u - y)) h0
  simp only [innerSL_apply_apply, ContinuousLinearMap.zero_apply] at h1
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h1)

end ProxCore

/-! ### Corollary 13.42 -/

/-- A quadratic expansion at `x̄` with gradient `v` makes `f` twice epi-differentiable at `x̄` for
`v` with `d²f(x̄ | v)(w) = ⟪w, Aw⟫` (as in 13.8). -/
theorem twiceEpi_of_quadratic_expansion {f : E → EReal} {x : E} {A : E →L[ℝ] E} {v : E}
    (hv : HasERealGradientAt f x (innerSL ℝ v))
    (ho : (fun y ↦ (f y).toReal - (f x).toReal - ⟪v, y - x⟫_ℝ - 1 / 2 * ⟪y - x, A (y - x)⟫_ℝ)
      =o[𝓝 x] (fun y ↦ ‖y - x‖ ^ 2)) :
    TwiceEpiDifferentiableAt f x v ∧
      ∀ w, secondSubderivative f x v w = ((⟪w, A w⟫_ℝ : ℝ) : EReal) := by
  obtain ⟨-, htw, hq⟩ := hasQuadraticExpansionAt_iff.1 ⟨v, hv, ho⟩
  have heq : secondSubderivativeAt f x = secondSubderivative f x v :=
    secondSubderivativeAt_eq_secondSubderivative_of_hasERealGradientAt hv
  have hlim : ∀ w, Tendsto (fun p : ℝ × E ↦ secondDifferenceQuotientAt f x p.1 p.2)
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 ((⟪w, A w⟫_ℝ : ℝ) : EReal)) := fun w ↦ by
    rw [← hq w]
    exact htw.2 w
  have hsub : ∀ w, subderivative f x w = ((⟪v, w⟫_ℝ : ℝ) : EReal) := fun w ↦ by
    rw [(hv.hasSemiderivative w).subderivative_eq, innerSL_apply_apply]
  have hlim' : ∀ w, Tendsto (fun p : ℝ × E ↦ secondDifferenceQuotient f x v p.1 p.2)
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 ((⟪w, A w⟫_ℝ : ℝ) : EReal)) := fun w ↦
    (hlim w).congr fun p ↦ secondDifferenceQuotientAt_eq_of_subderivative_eq (hsub p.2)
  have hd2 : ∀ w, secondSubderivative f x v w = ((⟪w, A w⟫_ℝ : ℝ) : EReal) := fun w ↦ by
    rw [← heq]
    exact hq w
  refine ⟨twiceEpiDifferentiableAt_iff_subset.2 ⟨hv.1, hv.2.1, ?_⟩, hd2⟩
  rw [show secondSubderivative f x v = fun w ↦ ((⟪w, A w⟫_ℝ : ℝ) : EReal) from funext hd2]
  exact epigraph_subset_innerSetLimitAlong_of_tendsto fun w ↦ by
    have h2 := (hlim' w).comp (tendsto_pair_const w)
    exact h2

/-- Under a gradient in the sense of 7(16), `f` is continuous at `x̄` and `∇f(x̄) = v`. -/
theorem HasERealGradientAt.tendsto_and_gradient {f : E → EReal} {x v : E}
    (hv : HasERealGradientAt f x (innerSL ℝ v)) :
    Tendsto f (𝓝 x) (𝓝 (f x)) ∧ gradient (fun z ↦ (f z).toReal) x = v := by
  obtain ⟨hx1, hx2, hfin, ho⟩ := hv
  have hfd : HasFDerivAt (fun z ↦ (f z).toReal) (innerSL ℝ v) x := HasFDerivAtFilter.of_isLittleO ho
  have hgrad : HasGradientAt (fun z ↦ (f z).toReal) v x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert hfd using 1
  refine ⟨?_, hgrad.gradient⟩
  have hc : Tendsto (fun z ↦ (((f z).toReal : ℝ) : EReal)) (𝓝 x) (𝓝 (((f x).toReal : ℝ) : EReal)) :=
    (continuous_coe_real_ereal.tendsto _).comp hfd.continuousAt
  rw [EReal.coe_toReal hx2 hx1] at hc
  refine hc.congr' ?_
  filter_upwards [hfin] with z hz
  exact EReal.coe_toReal hz.2 hz.1

/-- **Corollary 13.42**, (c) ⇒ (b): for `f` prox-regular at `x̄` for `v̄ = ∇f(x̄)` with a quadratic
expansion at `x̄` with matrix `A`, the subgradient mapping has the first-order expansion
`∅ ≠ ∂f(y) ⊂ v̄ + A_s(y - x̄) + o(‖y - x̄‖)IB` near `x̄`, `A_s = ½(A + A*)`. -/
theorem hasMappingFirstOrderExpansion_of_quadratic {f : E → EReal} {x : E} {A : E →L[ℝ] E}
    (hpr : IsProxRegularAt f x (gradient (fun z ↦ (f z).toReal) x))
    (hA : HasQuadraticExpansionAt f x A) :
    HasMappingFirstOrderExpansion (subdifferential f) x (gradient (fun z ↦ (f z).toReal) x)
      (symmPart A) := by
  obtain ⟨v, hv, ho⟩ := hA
  obtain ⟨hcont, hgv⟩ := hv.tendsto_and_gradient
  rw [hgv] at hpr ⊢
  obtain ⟨hte, hd2⟩ := twiceEpi_of_quadratic_expansion hv ho
  have hsc : IsSubdifferentiallyContinuousAt f x v := ⟨hpr.2.1, fun xs _ hxs _ _ ↦ hcont.comp hxs⟩
  obtain ⟨f₁, ε, K, hd2₁, hte₁, hsc_agree, -⟩ := hpr.exists_proxCore
  have hagree := hsc_agree hsc
  have hte' : TwiceEpiDifferentiableAt f₁ x 0 := hte₁.2 hte
  have hq : ∀ w, secondSubderivative f₁ x 0 w = ((⟪w, A w⟫_ℝ : ℝ) : EReal) := fun w ↦ by
    rw [hd2₁]; exact hd2 w
  choose G₀ hG₀ using K.tendsto_Gs_of_twiceEpi hte'
  obtain ⟨m, hm, hexp⟩ := K.exists_P_G_expansion hte' hq hG₀
  have hlam := K.hlam
  set T := proxLocalization f₁ x ε with hT
  set As := symmPart A with hAs
  -- the agreement of `∂f` with `T + v̄` near `(x̄, v̄)`
  obtain ⟨δa, hδa, hball⟩ := Metric.mem_nhds_iff.1 hagree
  have hag : ∀ y w, ‖y - x‖ < δa → ‖w - v‖ < δa → (w ∈ subdifferential f y ↔ w - v ∈ T y) := by
    intro y w hy hw
    have : ((y, w) : E × E) ∈ ball (x, v) δa := by
      rw [mem_ball, Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm]; exact ⟨hy, hw⟩
    exact hball this
  -- elements of `T` through `G` and `P`
  have hTmem : ∀ y w, w ∈ T y → K.P (y + K.lam • w) = y ∧ K.G (y + K.lam • w) = w := by
    intro y w hw
    obtain ⟨-, hG⟩ := (K.hgraph y w).1 hw
    refine ⟨?_, hG⟩
    rw [K.P_eq_sub, show K.G (y + K.lam • w) = w from hG]; abel
  have hGmem : ∀ u ∈ proxRange f₁ x ε K.lam, K.G u ∈ T (K.P u) := by
    intro u hu
    refine (K.hgraph (K.P u) (K.G u)).2 ⟨by rw [K.P_add_G]; exact hu, ?_⟩
    rw [K.P_add_G]; rfl
  -- prox-regularity makes nearby subgradients regular
  obtain ⟨-, -, εp, hεp, ρp, hρp, hprox⟩ := hpr
  have hreg : ∀ y w, w ∈ subdifferential f y → ‖w - v‖ < εp → ‖y - x‖ < εp → f y < f x + εp →
      w ∈ regularSubdifferential f y := by
    intro y w hw hwv hyx hfy
    obtain ⟨⟨c, hc⟩, -⟩ := id hw
    refine proximalSubdifferential_subset_regularSubdifferential f y
      ⟨c, hc, ρp + 1, by positivity, εp - ‖y - x‖, by linarith, fun y' hy' ↦ ?_⟩
    have hy'x : y' ∈ closedBall x εp := by
      rw [mem_closedBall, dist_eq_norm]
      calc ‖y' - x‖ = ‖(y' - y) + (y - x)‖ := by congr 1; abel
        _ ≤ ‖y' - y‖ + ‖y - x‖ := norm_add_le _ _
        _ ≤ εp := by linarith
    have h1 := hprox y w hw hwv hyx hfy y' hy'x
    rw [hc, ← EReal.coe_add] at h1
    refine le_trans (EReal.coe_le_coe_iff.2 ?_) h1
    nlinarith [sq_nonneg ‖y' - y‖]
  -- continuity of `f` at `x̄`
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, f x = c₀ := ⟨_, (EReal.coe_toReal hv.2.1 hv.1).symm⟩
  have hfev : ∀ᶠ y in 𝓝 x, f y < f x + εp := by
    have hlt : f x < f x + εp := by
      rw [hc₀, ← EReal.coe_add]; exact EReal.coe_lt_coe_iff.2 (by linarith)
    exact hcont.eventually (gt_mem_nhds hlt)
  obtain ⟨rf, hrf, hrfb⟩ := Metric.mem_nhds_iff.1 hfev
  -- the expansion with `η = 1`
  obtain ⟨ρ₁, hρ₁, hρ₁δ, hest₁⟩ := hexp 1 one_pos
  set C₁ := ‖As‖ + m⁻¹ with hC₁
  have hC₁0 : 0 < C₁ := by positivity
  have hbound : ∀ u, ‖u - x‖ ≤ ρ₁ → ‖u - x‖ ≤ m⁻¹ * ‖K.P u - x‖ ∧ ‖K.G u‖ ≤ C₁ * ‖K.P u - x‖ := by
    intro u hu
    obtain ⟨h1, h2⟩ := hest₁ (u - x) hu
    rw [add_sub_cancel] at h1 h2
    have h3 : m * ‖u - x‖ ^ 2 ≤ ‖K.P u - x‖ * ‖u - x‖ := h1.trans (real_inner_le_norm _ _)
    have h4 : ‖u - x‖ ≤ m⁻¹ * ‖K.P u - x‖ := by
      rcases eq_or_lt_of_le (norm_nonneg (u - x)) with h0 | hpos
      · rw [← h0]; positivity
      · rw [le_inv_mul_iff₀ hm]
        nlinarith
    refine ⟨h4, ?_⟩
    calc ‖K.G u‖ = ‖(K.G u - As (K.P u - x)) + As (K.P u - x)‖ := by congr 1; abel
      _ ≤ ‖K.G u - As (K.P u - x)‖ + ‖As (K.P u - x)‖ := norm_add_le _ _
      _ ≤ 1 * ‖u - x‖ + ‖As‖ * ‖K.P u - x‖ := add_le_add h2 (As.le_opNorm _)
      _ ≤ 1 * (m⁻¹ * ‖K.P u - x‖) + ‖As‖ * ‖K.P u - x‖ := by gcongr
      _ = C₁ * ‖K.P u - x‖ := by rw [hC₁]; ring
  -- surjectivity of `P`
  set ρ₀ := min ρ₁ (K.lam * δa / 3) with hρ₀
  have hρ₀0 : 0 < ρ₀ := lt_min hρ₁ (by positivity)
  have hρ₀ρ₁ : ρ₀ ≤ ρ₁ := min_le_left _ _
  have hsurj : ∀ y, ‖y - x‖ < m * ρ₀ / 4 → ∃ u, ‖u - x‖ < ρ₀ ∧ K.P u = y :=
    fun y hy ↦ K.exists_P_eq hρ₀0 (lt_of_le_of_lt hρ₀ρ₁ hρ₁δ) hm
      (fun h hh ↦ (hest₁ h (hh.trans hρ₀ρ₁)).1) hy
  have hGlip : ∀ u ∈ proxRange f₁ x ε K.lam, ‖K.G u‖ ≤ 3 / K.lam * ‖u - x‖ := by
    intro u hu
    have h := K.hGLip _ (K.hball (mem_ball_self K.hδ₀)) _ hu
    simpa [K.hPx] using h
  have hUρ : ∀ u, ‖u - x‖ ≤ ρ₁ → u ∈ proxRange f₁ x ε K.lam := fun u hu ↦
    K.hball (by rw [mem_ball, dist_eq_norm]; exact lt_of_le_of_lt hu hρ₁δ)
  -- the threshold `θ`
  set θ := min (min δa εp / 2) (ρ₁ / (2 * K.lam)) with hθ
  have hθ0 : 0 < θ := lt_min (by positivity) (by positivity)
  have hθδa : θ < δa := lt_of_le_of_lt ((min_le_left _ _).trans
    (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))) (by linarith)
  have hθεp : θ < εp := lt_of_le_of_lt ((min_le_left _ _).trans
    (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))) (by linarith)
  have hlamθ : K.lam * θ ≤ ρ₁ / 2 := by
    have : θ ≤ ρ₁ / (2 * K.lam) := min_le_right _ _
    calc K.lam * θ ≤ K.lam * (ρ₁ / (2 * K.lam)) := mul_le_mul_of_nonneg_left this hlam.le
      _ = ρ₁ / 2 := by field_simp
  -- the base neighborhood
  set r₀ := min (min (min δa εp) (min rf (m * ρ₀ / 4))) (min (θ / C₁) (ρ₁ / 2)) with hr₀
  have hr₀0 : 0 < r₀ := by positivity
  have hr₀δa : r₀ ≤ δa := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hr₀εp : r₀ ≤ εp := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hr₀f : r₀ ≤ rf := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr₀s : r₀ ≤ m * ρ₀ / 4 :=
    (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hr₀θ : r₀ ≤ θ / C₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hr₀ρ : r₀ ≤ ρ₁ / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hfy : ∀ y, ‖y - x‖ < r₀ → f y < f x + εp := fun y hy ↦
    hrfb (by rw [mem_ball, dist_eq_norm]; linarith)
  -- (N) a subgradient near `v̄`
  have hN : ∀ y, ‖y - x‖ < r₀ → ∃ g ∈ regularSubdifferential f y, ‖g - v‖ < θ := by
    intro y hy
    obtain ⟨u, hu, hPu⟩ := hsurj y (lt_of_lt_of_le hy hr₀s)
    have huU := hUρ u (hu.le.trans hρ₀ρ₁)
    have hGT : K.G u ∈ T y := hPu ▸ hGmem u huU
    have hGsmall : ‖K.G u‖ < θ := by
      have h1 := (hbound u (hu.le.trans hρ₀ρ₁)).2
      rw [hPu] at h1
      calc ‖K.G u‖ ≤ C₁ * ‖y - x‖ := h1
        _ < C₁ * (θ / C₁) := by gcongr; linarith
        _ = θ := by field_simp
    have hmem : K.G u + v ∈ subdifferential f y :=
      (hag y _ (by linarith) (by rw [add_sub_cancel_right]; linarith)).2
        (by rw [add_sub_cancel_right]; exact hGT)
    refine ⟨K.G u + v, hreg y _ hmem (by rw [add_sub_cancel_right]; linarith) (by linarith)
      (hfy y hy), by rw [add_sub_cancel_right]; exact hGsmall⟩
  -- a subgradient near `v̄` and with `‖y - x̄‖` small is controlled by `G`
  have hctrl : ∀ y w, ‖y - x‖ < r₀ → w ∈ subdifferential f y → ‖w - v‖ ≤ θ →
      ‖(y + K.lam • (w - v)) - x‖ ≤ ρ₁ ∧ K.P (y + K.lam • (w - v)) = y ∧
        K.G (y + K.lam • (w - v)) = w - v ∧ ‖w - v‖ ≤ C₁ * ‖y - x‖ := by
    intro y w hy hw hwθ
    have hT' := (hag y w (by linarith) (by linarith)).1 hw
    obtain ⟨hP, hG⟩ := hTmem y _ hT'
    have hnorm : ‖(y + K.lam • (w - v)) - x‖ ≤ ρ₁ := by
      calc ‖(y + K.lam • (w - v)) - x‖ = ‖(y - x) + K.lam • (w - v)‖ := by congr 1; abel
        _ ≤ ‖y - x‖ + K.lam * ‖w - v‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_smul, Real.norm_of_nonneg hlam.le]
        _ ≤ ρ₁ / 2 + K.lam * θ := by gcongr; linarith
        _ ≤ ρ₁ := by linarith
    have h1 := (hbound _ hnorm).2
    rw [hP, hG] at h1
    exact ⟨hnorm, hP, hG, h1⟩
  -- (B) all regular subgradients near `x̄` lie near `v̄`
  have hB : ∀ y, ‖y - x‖ < r₀ → ∀ w ∈ regularSubdifferential f y, ‖w - v‖ < θ := by
    intro y hy w hw
    by_contra hge
    push_neg at hge
    obtain ⟨g, hg, hgv⟩ := hN y hy
    obtain ⟨c, hc, -⟩ := id hg
    have hconv := (subdifferential_properties (f := f) hc).2.1
    set φ : ℝ → ℝ := fun t ↦ ‖(g + t • (w - g)) - v‖ with hφ
    have hφc : ContinuousOn φ (Icc 0 1) := by
      have : Continuous φ := by fun_prop
      exact this.continuousOn
    have hθmem : θ ∈ Icc (φ 0) (φ 1) := by
      simp only [hφ, zero_smul, add_zero, one_smul, add_sub_cancel]
      exact ⟨hgv.le, hge⟩
    obtain ⟨t, ht, hφt⟩ := intermediate_value_Icc zero_le_one hφc hθmem
    have hwt : g + t • (w - g) ∈ regularSubdifferential f y := by
      have := hconv hg hw (by linarith [ht.2] : 0 ≤ 1 - t) ht.1 (by ring : (1 - t) + t = 1)
      convert this using 1
      rw [smul_sub, sub_smul, one_smul]; abel
    have hwt' := regularSubdifferential_subset_subdifferential f y hwt
    obtain ⟨-, -, -, hle⟩ := hctrl y _ hy hwt' (by rw [← hφt])
    rw [show ‖(g + t • (w - g)) - v‖ = θ from hφt] at hle
    have : C₁ * ‖y - x‖ < θ := by
      calc C₁ * ‖y - x‖ < C₁ * (θ / C₁) := by gcongr; linarith
        _ = θ := by field_simp
    linarith
  -- (L) all subgradients near `x̄` lie near `v̄`
  have hL : ∀ y, ‖y - x‖ < r₀ → ∀ w ∈ subdifferential f y, ‖w - v‖ ≤ θ := by
    intro y hy w hw
    obtain ⟨-, ys, ws, hys, -, hws, hwlim⟩ := mem_subdifferential_iff_exists_seq.1 hw
    have hev : ∀ᶠ n in atTop, ‖ys n - x‖ < r₀ := by
      have hc : Tendsto (fun n ↦ ‖ys n - x‖) atTop (𝓝 ‖y - x‖) :=
        ((hys.sub tendsto_const_nhds).norm)
      exact hc.eventually (gt_mem_nhds hy)
    have hlim : Tendsto (fun n ↦ ‖ws n - v‖) atTop (𝓝 ‖w - v‖) :=
      (hwlim.sub tendsto_const_nhds).norm
    refine le_of_tendsto hlim ?_
    filter_upwards [hev] with n hn
    exact (hB (ys n) hn (ws n) (hws n)).le
  -- the first-order expansion
  intro η hη
  obtain ⟨ρη, hρη, -, hestη⟩ := hexp (η * m) (by positivity)
  set r := min r₀ (ρη / (1 + K.lam * C₁)) with hr
  have hr0 : 0 < r := lt_min hr₀0 (by positivity)
  filter_upwards [ball_mem_nhds x hr0] with y hy
  rw [mem_ball, dist_eq_norm] at hy
  have hyr₀ : ‖y - x‖ < r₀ := lt_of_lt_of_le hy (min_le_left _ _)
  refine ⟨?_, fun w hw ↦ ?_⟩
  · obtain ⟨g, hg, -⟩ := hN y hyr₀
    exact ⟨g, regularSubdifferential_subset_subdifferential f y hg⟩
  obtain ⟨hux1, hP, hG, hwC⟩ := hctrl y w hyr₀ hw (hL y hyr₀ w hw)
  set u := y + K.lam • (w - v) with hu
  have hux : ‖u - x‖ ≤ ρη := by
    have h1 : ‖u - x‖ ≤ (1 + K.lam * C₁) * ‖y - x‖ := by
      calc ‖u - x‖ = ‖(y - x) + K.lam • (w - v)‖ := by rw [hu]; congr 1; abel
        _ ≤ ‖y - x‖ + K.lam * ‖w - v‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_smul, Real.norm_of_nonneg hlam.le]
        _ ≤ ‖y - x‖ + K.lam * (C₁ * ‖y - x‖) := by gcongr
        _ = (1 + K.lam * C₁) * ‖y - x‖ := by ring
    have h2 : ‖y - x‖ < ρη / (1 + K.lam * C₁) := lt_of_lt_of_le hy (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at h2
    nlinarith
  have h1 := (hestη (u - x) hux).2
  rw [add_sub_cancel, hP, hG] at h1
  have h2 := (hbound u hux1).1
  rw [hP] at h2
  calc ‖w - v - As (y - x)‖ ≤ η * m * ‖u - x‖ := h1
    _ ≤ η * m * (m⁻¹ * ‖y - x‖) := by gcongr
    _ = η * ‖y - x‖ := by field_simp
/-- **Corollary 13.42** (second derivatives and quadratic expansions).  Let `f` be prox-regular
at `x̄` for `v̄ = ∇f(x̄)`.  Then (a) twice differentiability of `f` at `x̄` in the extended sense,
(b) differentiability of `∂f` at `x̄`, and (c) the existence of a quadratic expansion of `f` at `x̄`
are equivalent.  A quadratic expansion with matrix `A` gives `∇²f(x̄) = A_s = ½(A + A*)`; under (a),
`∇²f(x̄)` is symmetric, `f` has the quadratic expansion with matrix `∇²f(x̄)`, and `f` is lower-`C²`
around `x̄`.  (Differentiability of `f` at `x̄`, assumed in the book, follows from each of (a)-(c).)
-/
theorem second_derivatives_and_quadratic_expansions {f : E → EReal} {x : E}
    (hpr : IsProxRegularAt f x (gradient (fun z ↦ (f z).toReal) x)) :
    ((∃ A, HasExtendedHessianAt f x A) ↔ SvDifferentiableAt (subdifferential f) x) ∧
    ((∃ A, HasExtendedHessianAt f x A) ↔ ∃ A, HasQuadraticExpansionAt f x A) ∧
    (∀ A, HasQuadraticExpansionAt f x A → HasExtendedHessianAt f x (symmPart A)) ∧
    ∀ A, HasExtendedHessianAt f x A →
      HasQuadraticExpansionAt f x A ∧ (∀ u w, ⟪A u, w⟫_ℝ = ⟪u, A w⟫_ℝ) ∧ IsLowerC2Around f x := by
  have hl := hpr.1
  have hca : ∀ A, HasQuadraticExpansionAt f x A → HasExtendedHessianAt f x (symmPart A) := by
    intro A hA
    have hx : f x = (((f x).toReal : ℝ) : EReal) := by
      obtain ⟨v, hv, -⟩ := hA
      exact (EReal.coe_toReal hv.2.1 hv.1).symm
    exact (hasExtendedHessianAt_of_hasMappingFirstOrderExpansion hx hl
      (hasMappingFirstOrderExpansion_of_quadratic hpr hA)).1
  refine ⟨?_, ⟨fun ⟨A, hA⟩ ↦ ⟨A, hA.hasQuadraticExpansionAt⟩, fun ⟨A, hA⟩ ↦ ⟨_, hca A hA⟩⟩, hca,
    fun A hA ↦ ⟨hA.hasQuadraticExpansionAt, hA.inner_map_comm_of_isProxRegularAt hpr,
    (prox_regularity_versus_subsmoothness isOpen_univ).2.2 x _ hpr hA.hasStrictGradientAt⟩⟩
  rw [exists_hasExtendedHessianAt_iff]
  exact ⟨fun h ↦ h.2.2, fun h ↦ ⟨⟨(f x).toReal, (EReal.coe_toReal hl.2.1 hl.1).symm⟩, hl, h⟩⟩

end RW
