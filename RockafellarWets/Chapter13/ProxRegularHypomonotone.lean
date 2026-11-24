/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Subdifferential characterization of prox-regularity

Theorem 13.36.  For `f` finite and locally lsc at `x̄` and a proximal subgradient `v̄ ∈ ∂f(x̄)`,
`f` is prox-regular at `x̄` for `v̄` if and only if `∂f` has an `f`-attentive localization `T`
around `(x̄, v̄)` with `T + ρI` monotone.

The direction `(a) ⇒ (b)` adds the two prox-regularity inequalities.  For `(b) ⇒ (a)` we avoid the
global reductions of the printed proof and argue directly with the localized proximal problems
`minimize f(y) + ψ_u(y)` over the compact set `K = 𝔹(x̄, η) ∩ {f ≤ f(x̄) + ε₀}`, where
`ψ_u(y) = -⟪v̄, y - x̄⟫ + (κ/2)‖y - x̄‖² + ½‖y - x̄ - u‖²`.  Its minimizer `x_u` satisfies
`‖x_u - x̄‖ ≤ ‖u‖`, minimizes `f + ψ_u` on the whole ball, and carries the proximal subgradient
`w_u = v̄ - κ(x_u - x̄) - (x_u - x̄ - u)`.  For a localized pair `(y, v)` with `u` chosen so that
`v = v̄ - κ(y - x̄) - (y - x̄ - u)`, hypomonotonicity forces `y = x_u` (as `κ + 1 > ρ`), which is
the prox-regularity inequality with constant `κ + 1`.  This replaces the use of proximal
mappings and nonexpansive resolvents (1.25, 12.12) in the printed argument.
-/

import RockafellarWets.Chapter13.ProxRegularity
import RockafellarWets.Chapter8.ProximalSubgradients

open Filter Set Topology Metric
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Theorem 13.36(b)**: `∂f` has an `f`-attentive localization around `(x̄, v̄)`, consisting of
the pairs `(x, v) ∈ gph ∂f` with `‖x - x̄‖ < ε`, `|f(x) - f(x̄)| < ε` and `‖v - v̄‖ < ε`, on which
`∂f + ρI` is monotone for some `ρ ≥ 0`. -/
def HasHypomonotoneAttentiveLocalization (f : E → EReal) (x v : E) : Prop :=
  ∃ ε > 0, ∃ ρ ≥ 0, ∀ x₀ v₀ x₁ v₁, v₀ ∈ subdifferential f x₀ → v₁ ∈ subdifferential f x₁ →
    ‖x₀ - x‖ < ε → ‖x₁ - x‖ < ε → ‖v₀ - v‖ < ε → ‖v₁ - v‖ < ε →
    f x - ε < f x₀ → f x₀ < f x + ε → f x - ε < f x₁ → f x₁ < f x + ε →
    -ρ * ‖x₁ - x₀‖ ^ 2 ≤ ⟪v₁ - v₀, x₁ - x₀⟫_ℝ

/-- **Theorem 13.36**, `(a) ⇒ (b)`. -/
theorem IsProxRegularAt.hasHypomonotoneAttentiveLocalization {f : E → EReal} {x v : E}
    (h : IsProxRegularAt f x v) : HasHypomonotoneAttentiveLocalization f x v := by
  obtain ⟨-, -, ε, hε, ρ, hρ, hineq⟩ := h
  refine ⟨ε, hε, ρ, hρ, fun x₀ v₀ x₁ v₁ hv₀ hv₁ hx₀ hx₁ hv₀' hv₁' _ hf₀ _ hf₁ ↦ ?_⟩
  have h01 := hineq x₀ v₀ hv₀ hv₀' hx₀ hf₀ x₁ (by rw [mem_closedBall, dist_eq_norm]; exact hx₁.le)
  have h10 := hineq x₁ v₁ hv₁ hv₁' hx₁ hf₁ x₀ (by rw [mem_closedBall, dist_eq_norm]; exact hx₀.le)
  obtain ⟨a₀, ha₀⟩ := hv₀.1
  obtain ⟨a₁, ha₁⟩ := hv₁.1
  rw [ha₀, ha₁, ← EReal.coe_add, EReal.coe_le_coe_iff] at h01 h10
  have e1 : ‖x₀ - x₁‖ = ‖x₁ - x₀‖ := norm_sub_rev _ _
  have e2 : ⟪v₁ - v₀, x₁ - x₀⟫_ℝ = ⟪v₁, x₁ - x₀⟫_ℝ - ⟪v₀, x₁ - x₀⟫_ℝ := inner_sub_left _ _ _
  have e3 : ⟪v₁, x₀ - x₁⟫_ℝ = -⟪v₁, x₁ - x₀⟫_ℝ := by rw [← inner_neg_right, neg_sub]
  rw [e1, e3] at h10
  rw [e2]
  linarith

omit [InnerProductSpace ℝ E] in
/-- Closed truncated sublevel sets make a function lsc relative to its truncation. -/
theorem lowerSemicontinuousOn_of_isClosed_inter_sublevel {f : E → EReal} {K : Set E} {M : ℝ}
    (hK : ∀ y ∈ K, f y ≤ M) (hcl : ∀ α : ℝ, α < M → IsClosed (K ∩ {y | f y ≤ α})) :
    LowerSemicontinuousOn f K := by
  intro x hx y hy
  obtain ⟨α, hyα, hαx⟩ := EReal.exists_between_coe_real hy
  have hαM : α < M := EReal.coe_lt_coe_iff.1 (hαx.trans_le (hK x hx))
  have hxS : x ∉ K ∩ {y | f y ≤ α} := fun h ↦ (not_le.2 hαx) h.2
  filter_upwards [nhdsWithin_le_nhds ((hcl α hαM).isOpen_compl.mem_nhds hxS),
    self_mem_nhdsWithin] with x' h1 h2
  have h3 : ¬ f x' ≤ α := fun h ↦ h1 ⟨h2, h⟩
  exact hyα.trans (not_le.1 h3)

/-- The quadratic `ψ(y) = -⟪v, y - x̄⟫ + (κ/2)‖y - x̄‖² + ½‖y - x̄ - u‖²` of the localized proximal
problems: `ψ(x̄ + a + h) - ψ(x̄ + a) = -⟪v - κa - (a - u), h⟫ + ((κ + 1)/2)‖h‖²`. -/
theorem localProx_quadratic_identity (v a h u : E) (κ : ℝ) :
    (-⟪v, a + h⟫_ℝ + κ / 2 * ‖a + h‖ ^ 2 + 1 / 2 * ‖a + h - u‖ ^ 2) -
      (-⟪v, a⟫_ℝ + κ / 2 * ‖a‖ ^ 2 + 1 / 2 * ‖a - u‖ ^ 2) =
    -⟪v - κ • a - (a - u), h⟫_ℝ + (κ + 1) / 2 * ‖h‖ ^ 2 := by
  have e1 : ‖a + h‖ ^ 2 = ‖a‖ ^ 2 + 2 * ⟪a, h⟫_ℝ + ‖h‖ ^ 2 := norm_add_sq_real a h
  have e2 : ‖a + h - u‖ ^ 2 = ‖a - u‖ ^ 2 + 2 * ⟪a - u, h⟫_ℝ + ‖h‖ ^ 2 := by
    rw [show a + h - u = (a - u) + h by abel]
    exact norm_add_sq_real _ _
  rw [e1, e2]
  simp only [inner_add_right, inner_sub_left, real_inner_smul_left]
  ring

variable [FiniteDimensional ℝ E]

/-- **Theorem 13.36**, `(b) ⇒ (a)`. -/
theorem IsProxRegularAt.of_hasHypomonotoneAttentiveLocalization {f : E → EReal} {x v : E}
    (hl : IsLocallyLscAt f x) (hv : v ∈ proximalSubdifferential f x)
    (hb : HasHypomonotoneAttentiveLocalization f x v) : IsProxRegularAt f x v := by
  have hv' : v ∈ subdifferential f x := regularSubdifferential_subset_subdifferential f x
    (proximalSubdifferential_subset_regularSubdifferential f x hv)
  refine ⟨hl, hv', ?_⟩
  obtain ⟨c, hc, r, hr, δp, hδp, hprox⟩ := hv
  obtain ⟨-, -, ε₀, hε₀, hclosed⟩ := hl
  obtain ⟨ε₁, hε₁, ρ, hρ, hmono⟩ := hb
  have hcx : (f x).toReal = c := by rw [hc, EReal.toReal_coe]
  set κ : ℝ := max r ρ + 1 with hκ
  have hκr : 1 ≤ κ - r := by have := le_max_left r ρ; linarith
  have hκρ : ρ ≤ κ := by have := le_max_right r ρ; linarith
  have hκ0 : 0 < κ := by have := le_max_left r ρ; linarith
  set η : ℝ := min (min ε₀ δp) (ε₀ / (2 * (‖v‖ + 1))) with hη
  have hη0 : 0 < η := lt_min (lt_min hε₀ hδp) (by positivity)
  have hηε₀ : η ≤ ε₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hηδp : η ≤ δp := (min_le_left _ _).trans (min_le_right _ _)
  have hηv : η * ‖v‖ ≤ ε₀ / 2 := by
    have h1 : η ≤ ε₀ / (2 * (‖v‖ + 1)) := min_le_right _ _
    have h2 : η * (‖v‖ + 1) ≤ ε₀ / 2 := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (‖v‖ + 1))] at h1
      linarith
    nlinarith [norm_nonneg v]
  -- the compact set `K`
  set K : Set E := closedBall x η ∩ {y | f y ≤ ((c + ε₀ : ℝ) : EReal)} with hK
  have hKcl : ∀ α : ℝ, α ≤ c + ε₀ → IsClosed (closedBall x η ∩ {y | f y ≤ α}) := by
    intro α hα
    have h1 := hclosed α (by rw [hcx]; exact hα)
    have heq : closedBall x η ∩ {y | f y ≤ α} =
        closedBall x η ∩ (closedBall x ε₀ ∩ {y | f y ≤ α}) := by
      ext y
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, closedBall_subset_closedBall hηε₀ h1, h2⟩
      · rintro ⟨h1, -, h2⟩
        exact ⟨h1, h2⟩
    rw [heq]
    exact isClosed_closedBall.inter h1
  have hKcompact : IsCompact K :=
    (isCompact_closedBall x η).of_isClosed_subset (hKcl _ le_rfl) inter_subset_left
  have hxK : x ∈ K := by
    refine ⟨mem_closedBall_self hη0.le, ?_⟩
    show f x ≤ _
    rw [hc]
    exact EReal.coe_le_coe_iff.2 (by linarith)
  have hflsc : LowerSemicontinuousOn f K := by
    refine lowerSemicontinuousOn_of_isClosed_inter_sublevel (M := c + ε₀) (fun y hy ↦ hy.2)
      fun α hα ↦ ?_
    have heq : K ∩ {y | f y ≤ α} = closedBall x η ∩ {y | f y ≤ α} := by
      ext y
      constructor
      · rintro ⟨⟨h1, -⟩, h2⟩
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, h2.trans (EReal.coe_le_coe_iff.2 hα.le)⟩, h2⟩
    rw [heq]
    exact hKcl α hα.le
  -- finiteness on the ball
  have hlow : ∀ y, ‖y - x‖ ≤ η →
      ((c + ⟪v, y - x⟫_ℝ - r / 2 * ‖y - x‖ ^ 2 : ℝ) : EReal) ≤ f y :=
    fun y hy ↦ hprox y (hy.trans hηδp)
  have hnebot : ∀ y, ‖y - x‖ ≤ η → f y ≠ ⊥ := fun y hy h ↦ by
    have := hlow y hy
    rw [h] at this
    exact EReal.coe_ne_bot _ (le_bot_iff.1 this)
  have hfinK : ∀ y ∈ K, f y = ((f y).toReal : EReal) := fun y hy ↦
    (EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) hy.2)
      (hnebot y (by rw [← dist_eq_norm]; exact hy.1))).symm
  -- the localized proximal problems
  set ψ : E → E → ℝ := fun u y ↦
    -⟪v, y - x⟫_ℝ + κ / 2 * ‖y - x‖ ^ 2 + 1 / 2 * ‖y - x - u‖ ^ 2 with hψ
  have hψc : ∀ u, Continuous (ψ u) := fun u ↦ by
    have h1 : Continuous fun y : E ↦ ⟪v, y - x⟫_ℝ :=
      continuous_const.inner (continuous_id.sub continuous_const)
    have h2 : Continuous fun y : E ↦ ‖y - x‖ ^ 2 := (continuous_id.sub continuous_const).norm.pow 2
    have h3 : Continuous fun y : E ↦ ‖y - x - u‖ ^ 2 :=
      ((continuous_id.sub continuous_const).sub continuous_const).norm.pow 2
    exact (h1.neg.add (continuous_const.mul h2)).add (continuous_const.mul h3)
  have hψid : ∀ u y x', ψ u x' - ψ u y =
      -⟪v - κ • (y - x) - ((y - x) - u), x' - y⟫_ℝ + (κ + 1) / 2 * ‖x' - y‖ ^ 2 := by
    intro u y x'
    have h := localProx_quadratic_identity v (y - x) (x' - y) u κ
    have e : y - x + (x' - y) = x' - x := by abel
    rw [e] at h
    exact h
  have hψx : ∀ u, ψ u x = 1 / 2 * ‖u‖ ^ 2 := fun u ↦ by simp [hψ]
  have hmin : ∀ u : E, ∃ xu ∈ K, ∀ y ∈ K,
      f xu + ((ψ u xu : ℝ) : EReal) ≤ f y + ((ψ u y : ℝ) : EReal) := by
    intro u
    have hg : LowerSemicontinuousOn (fun y ↦ f y + ((ψ u y : ℝ) : EReal)) K :=
      hflsc.add' ((continuous_coe_real_ereal.comp (hψc u)).lowerSemicontinuous.lowerSemicontinuousOn
        K) fun y _ ↦ EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _))
          (Or.inr (EReal.coe_ne_top _))
    obtain ⟨xu, hxu, hxumin⟩ := hg.exists_isMinOn ⟨x, hxK⟩ hKcompact
    exact ⟨xu, hxu, fun y hy ↦ isMinOn_iff.1 hxumin y hy⟩
  -- the choice of `ε`
  have t1 : Tendsto (fun e : ℝ ↦ (2 + κ) * e) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun e : ℝ ↦ (2 + κ) * e) (𝓝 0) (𝓝 ((2 + κ) * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have c1 := t1.eventually (gt_mem_nhds (half_pos hη0))
  have c2 : ∀ᶠ e in 𝓝[>] (0 : ℝ), ((2 + κ) * e) ^ 2 < ε₀ := by
    have h := t1.pow 2
    rw [zero_pow two_ne_zero] at h
    exact h.eventually (gt_mem_nhds hε₀)
  have c3 : ∀ᶠ e in 𝓝[>] (0 : ℝ), (κ + 2) * ((2 + κ) * e) < ε₁ := by
    have h := t1.const_mul (κ + 2)
    rw [mul_zero] at h
    exact h.eventually (gt_mem_nhds hε₁)
  have c4 : ∀ᶠ e in 𝓝[>] (0 : ℝ),
      ‖v‖ * ((2 + κ) * e) + (r + 1) / 2 * ((2 + κ) * e) ^ 2 < ε₁ := by
    have h := (t1.const_mul ‖v‖).add ((t1.pow 2).const_mul ((r + 1) / 2))
    simp only [mul_zero, zero_pow two_ne_zero, add_zero] at h
    exact h.eventually (gt_mem_nhds hε₁)
  obtain ⟨ε, ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, hε⟩ := ((((c1.and c2).and c3).and c4).and
    self_mem_nhdsWithin).exists
  have hε0 : (0 : ℝ) < ε := hε
  set U := (2 + κ) * ε with hU
  have hεU : ε ≤ U := by nlinarith
  have hU0 : 0 < U := by positivity
  refine ⟨ε, hε0, κ + 1, by positivity, fun y v' hv' hvv hyx hfy x' hx' ↦ ?_⟩
  -- the point `y`
  have hyη : ‖y - x‖ ≤ η := by linarith
  have hfy_ne_top : f y ≠ ⊤ := ne_top_of_lt hfy
  have hfyc : f y = ((f y).toReal : EReal) := (EReal.coe_toReal hfy_ne_top (hnebot y hyη)).symm
  have hfy_low := hlow y hyη
  rw [hfyc, EReal.coe_le_coe_iff] at hfy_low
  have hfy_up : (f y).toReal < c + ε := by
    rw [hfyc, hc, ← EReal.coe_add, EReal.coe_lt_coe_iff] at hfy
    exact hfy
  -- the parameter `u` and the minimizer `x_u`
  set u : E := (1 + κ) • (y - x) + (v' - v) with hu
  have hun : ‖u‖ < U := by
    calc ‖u‖ ≤ ‖(1 + κ) • (y - x)‖ + ‖v' - v‖ := norm_add_le _ _
      _ = (1 + κ) * ‖y - x‖ + ‖v' - v‖ := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      _ < (1 + κ) * ε + ε := by
        have : (1 + κ) * ‖y - x‖ < (1 + κ) * ε := mul_lt_mul_of_pos_left hyx (by positivity)
        linarith
      _ = U := by rw [hU]; ring
  obtain ⟨xu, hxuK, hxumin⟩ := hmin u
  set d := xu - x with hd
  have hfxu := hfinK xu hxuK
  have hdη : ‖d‖ ≤ η := by rw [hd, ← dist_eq_norm]; exact hxuK.1
  have hxu_low := hlow xu hdη
  rw [hfxu, EReal.coe_le_coe_iff] at hxu_low
  have hcmp := hxumin x hxK
  rw [hfxu, hc, hψx, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at hcmp
  have hψxu : ψ u xu = -⟪v, d⟫_ℝ + κ / 2 * ‖d‖ ^ 2 + 1 / 2 * ‖d - u‖ ^ 2 := rfl
  rw [hψxu] at hcmp
  have hsq : 0 ≤ ‖d - u‖ ^ 2 := by positivity
  have hdsq : 1 / 2 * ‖d‖ ^ 2 ≤ (κ - r) / 2 * ‖d‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg ‖d‖)
  have hdu : ‖d‖ ≤ ‖u‖ := by
    have : ‖d‖ ^ 2 ≤ ‖u‖ ^ 2 := by linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this
  have hvd : |⟪v, d⟫_ℝ| ≤ ‖v‖ * ‖u‖ :=
    (abs_real_inner_le_norm v d).trans (mul_le_mul_of_nonneg_left hdu (norm_nonneg v))
  have hfxu_up : (f xu).toReal ≤ c + 1 / 2 * ‖u‖ ^ 2 + ‖v‖ * ‖u‖ := by
    have := (abs_le.1 hvd).2
    have hκd : 0 ≤ κ / 2 * ‖d‖ ^ 2 := by positivity
    linarith
  have hfxu_low : c - ‖v‖ * ‖u‖ - r / 2 * ‖u‖ ^ 2 ≤ (f xu).toReal := by
    have := (abs_le.1 hvd).1
    have : r / 2 * ‖d‖ ^ 2 ≤ r / 2 * ‖u‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hdu 2) (by positivity)
    linarith
  -- `x_u` minimizes `f + ψ_u` on the whole ball `𝔹(x̄, η)`
  have hG : ∀ z ∈ closedBall x η,
      f xu + ((ψ u xu : ℝ) : EReal) ≤ f z + ((ψ u z : ℝ) : EReal) := by
    intro z hz
    by_cases hzK : z ∈ K
    · exact hxumin z hzK
    · have hfz : ((c + ε₀ : ℝ) : EReal) < f z := by
        by_contra hcon
        exact hzK ⟨hz, not_lt.1 hcon⟩
      have hψz : -(η * ‖v‖) ≤ ψ u z := by
        have hzη : ‖z - x‖ ≤ η := by rw [← dist_eq_norm]; exact hz
        have h1 : ⟪v, z - x⟫_ℝ ≤ ‖v‖ * ‖z - x‖ := real_inner_le_norm _ _
        have h2 : ‖v‖ * ‖z - x‖ ≤ η * ‖v‖ := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right hzη (norm_nonneg v)
        have h3 : 0 ≤ κ / 2 * ‖z - x‖ ^ 2 := by positivity
        have h4 : 0 ≤ 1 / 2 * ‖z - x - u‖ ^ 2 := by positivity
        show -(η * ‖v‖) ≤ -⟪v, z - x⟫_ℝ + κ / 2 * ‖z - x‖ ^ 2 + 1 / 2 * ‖z - x - u‖ ^ 2
        linarith only [h1, h2, h3, h4]
      calc f xu + ((ψ u xu : ℝ) : EReal) = (((f xu).toReal + ψ u xu : ℝ) : EReal) := by
            rw [EReal.coe_add (f xu).toReal (ψ u xu), ← hfxu]
        _ ≤ ((c + ε₀ + -(η * ‖v‖) : ℝ) : EReal) := by
            rw [EReal.coe_le_coe_iff, hψxu]
            have hu2 : ‖u‖ ^ 2 < ε₀ := by
              have := pow_lt_pow_left₀ hun (norm_nonneg u) two_ne_zero
              linarith only [this, h2]
            linarith only [hcmp, hηv, hu2]
        _ ≤ f z + ((ψ u z : ℝ) : EReal) := by
            rw [EReal.coe_add]
            exact add_le_add hfz.le (EReal.coe_le_coe_iff.2 hψz)
  -- the proximal subgradient `w_u`
  set wu : E := v - κ • d - (d - u) with hwu
  have hwu_mem : wu ∈ subdifferential f xu := by
    refine regularSubdifferential_subset_subdifferential f xu
      (proximalSubdifferential_subset_regularSubdifferential f xu ?_)
    refine ⟨(f xu).toReal, hfxu, κ + 1, by positivity, η / 2, half_pos hη0, fun z hz ↦ ?_⟩
    have hzball : z ∈ closedBall x η := by
      rw [mem_closedBall, dist_eq_norm]
      calc ‖z - x‖ = ‖(z - xu) + d‖ := by rw [hd]; congr 1; abel
        _ ≤ ‖z - xu‖ + ‖d‖ := norm_add_le _ _
        _ ≤ η := by
          have : ‖u‖ < η / 2 := hun.trans h1
          linarith
    have hGz := hG z hzball
    have hid := hψid u xu z
    by_cases hzt : f z = ⊤
    · rw [hzt]
      exact le_top
    · have hfz : f z = ((f z).toReal : EReal) :=
        (EReal.coe_toReal hzt (hnebot z (by rw [← dist_eq_norm]; exact hzball))).symm
      rw [hfz, hfxu, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at hGz
      rw [hfz, EReal.coe_le_coe_iff]
      have hwz : ⟪wu, z - xu⟫_ℝ = ⟪v - κ • (xu - x) - ((xu - x) - u), z - xu⟫_ℝ := rfl
      linarith only [hGz, hid, hwz]
  -- localization memberships
  have hκ2 : 1 ≤ κ + 2 := by linarith
  have hxux : ‖xu - x‖ < ε₁ := by
    calc ‖xu - x‖ = ‖d‖ := rfl
      _ < U := hdu.trans_lt hun
      _ ≤ (κ + 2) * U := le_mul_of_one_le_left hU0.le hκ2
      _ < ε₁ := h3
  have hwuv : ‖wu - v‖ < ε₁ := by
    have e : wu - v = -(κ • d) - (d - u) := by rw [hwu]; abel
    have hw1 : ‖wu - v‖ ≤ κ * ‖d‖ + ‖d‖ + ‖u‖ := by
      rw [e]
      have h5 : ‖-(κ • d) - (d - u)‖ ≤ ‖-(κ • d)‖ + ‖d - u‖ := norm_sub_le _ _
      have h6 : ‖d - u‖ ≤ ‖d‖ + ‖u‖ := norm_sub_le _ _
      rw [norm_neg, norm_smul, Real.norm_of_nonneg hκ0.le] at h5
      linarith only [h5, h6]
    have hw2 : κ * ‖d‖ ≤ κ * ‖u‖ := mul_le_mul_of_nonneg_left hdu hκ0.le
    have hw3 : (κ + 2) * ‖u‖ < (κ + 2) * U := mul_lt_mul_of_pos_left hun (by positivity)
    linarith only [hw1, hw2, hdu, hw3, h3]
  have hUsq : ‖u‖ ^ 2 ≤ U ^ 2 := pow_le_pow_left₀ (norm_nonneg u) hun.le 2
  have hvu : ‖v‖ * ‖u‖ ≤ ‖v‖ * U := mul_le_mul_of_nonneg_left hun.le (norm_nonneg v)
  have hrU : 0 ≤ r / 2 * U ^ 2 := by positivity
  have hU2 : 0 ≤ U ^ 2 := sq_nonneg U
  have hUk : U ≤ (κ + 2) * U := le_mul_of_one_le_left hU0.le hκ2
  have hfxu_lt : f xu < f x + ε₁ := by
    rw [hfxu, hc, ← EReal.coe_add, EReal.coe_lt_coe_iff]
    linarith only [hfxu_up, hUsq, hvu, h4, hrU, hU2]
  have hfxu_gt : f x - ε₁ < f xu := by
    rw [hfxu, hc, ← EReal.coe_sub, EReal.coe_lt_coe_iff]
    have hru : r / 2 * ‖u‖ ^ 2 ≤ r / 2 * U ^ 2 := mul_le_mul_of_nonneg_left hUsq (by positivity)
    linarith only [hfxu_low, hvu, hru, h4, hU2]
  have hyx₁ : ‖y - x‖ < ε₁ := by linarith only [hyx, hεU, hUk, h3]
  have hvv₁ : ‖v' - v‖ < ε₁ := by linarith only [hvv, hεU, hUk, h3]
  have hfy_lt : f y < f x + ε₁ := by
    rw [hfyc, hc, ← EReal.coe_add, EReal.coe_lt_coe_iff]
    linarith only [hfy_up, hεU, hUk, h3]
  have hfy_gt : f x - ε₁ < f y := by
    rw [hfyc, hc, ← EReal.coe_sub, EReal.coe_lt_coe_iff]
    have hvy : |⟪v, y - x⟫_ℝ| ≤ ‖v‖ * ε :=
      (abs_real_inner_le_norm v (y - x)).trans
        (mul_le_mul_of_nonneg_left hyx.le (norm_nonneg v))
    have hvy' := (abs_le.1 hvy).1
    have hyε : ‖y - x‖ ^ 2 ≤ U ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hyx.le.trans hεU) 2
    have hry : r / 2 * ‖y - x‖ ^ 2 ≤ r / 2 * U ^ 2 := mul_le_mul_of_nonneg_left hyε (by positivity)
    have hvε : ‖v‖ * ε ≤ ‖v‖ * U := mul_le_mul_of_nonneg_left hεU (norm_nonneg v)
    linarith only [hfy_low, hvy', hry, hvε, h4, hU2]
  -- the stationarity of `y` for the same parameter, and `y = x_u`
  have hv'eq : v' = v - κ • (y - x) - ((y - x) - u) := by
    rw [hu]
    module
  have hmono' := hmono xu wu y v' hwu_mem hv' hxux hyx₁ hwuv hvv₁ hfxu_gt hfxu_lt hfy_gt hfy_lt
  have hdiff : v' - wu = -(κ + 1) • (y - xu) := by
    rw [hv'eq, hwu, hd]
    module
  rw [hdiff, real_inner_smul_left, real_inner_self_eq_norm_sq] at hmono'
  have hyxu : y = xu := by
    have h5 : ‖y - xu‖ ^ 2 ≤ (κ + 1 - ρ) * ‖y - xu‖ ^ 2 :=
      le_mul_of_one_le_left (sq_nonneg _) (by linarith only [hκρ])
    have hsq0 : ‖y - xu‖ ^ 2 ≤ 0 := by linarith only [hmono', h5]
    have h6 : ‖y - xu‖ ^ 2 = 0 := le_antisymm hsq0 (sq_nonneg _)
    exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h6))
  -- the prox-regularity inequality
  have hx'ball : x' ∈ closedBall x η := closedBall_subset_closedBall (by linarith) hx'
  have hGx' := hG x' hx'ball
  rw [← hyxu] at hGx'
  have hid := hψid u y x'
  rw [← hv'eq] at hid
  by_cases hx't : f x' = ⊤
  · rw [hx't]
    exact le_top
  · have hfx' : f x' = ((f x').toReal : EReal) := (EReal.coe_toReal hx't
      (hnebot x' (by rw [← dist_eq_norm]; exact hx'ball))).symm
    rw [hfx', hfyc, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at hGx'
    rw [hfx', hfyc, ← EReal.coe_add, EReal.coe_le_coe_iff]
    linarith only [hGx', hid]

/-- **Theorem 13.36** (subdifferential characterization of prox-regularity). -/
theorem subdifferential_characterization_of_prox_regularity {f : E → EReal} {x v : E}
    (hl : IsLocallyLscAt f x) (hv : v ∈ proximalSubdifferential f x) :
    IsProxRegularAt f x v ↔ HasHypomonotoneAttentiveLocalization f x v :=
  ⟨IsProxRegularAt.hasHypomonotoneAttentiveLocalization,
    IsProxRegularAt.of_hasHypomonotoneAttentiveLocalization hl hv⟩

end RW
