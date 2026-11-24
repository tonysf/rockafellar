/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Proximal mappings and Moreau envelopes of prox-regular functions

Proposition 13.37.  For `f` prox-regular at `x̄` for `vb = 0` and prox-bounded, the
prox-regularity inequality holds globally (13(30)) on an `f`-attentive localization `T` of `∂f`.
For small `λ > 0` this makes `P_λ f(y + λv) = {y}` for `v ∈ T(y)`, and a localized minimization
over the compact set `𝔹(x̄, η) ∩ {f ≤ f(x̄) + ε₀}` shows that `U_λ = rge(I + λT)` is an open
neighborhood of `x̄`.  On `U_λ` the proximal mapping is single-valued, monotone and Lipschitz
with `P_λ f = (I + λT)⁻¹`, and `e_λ f` is differentiable with `∇e_λ f = λ⁻¹(I - P_λ f)`, a
Lipschitz mapping; hence `e_λ f` is of class `C¹⁺` on `U_λ`.
-/

import RockafellarWets.Chapter13.ProxRegularHypomonotone
import RockafellarWets.Chapter10.ProximalStationarity

open Filter Set Topology Metric
open scoped InnerProductSpace NNReal

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
/-- Prox-boundedness as a global quadratic minorant. -/
theorem IsProxBounded.exists_quadratic_minorant {f : E → EReal} (h : IsProxBounded f) :
    ∃ lb > 0, ∃ x₀ : E, ∃ m : ℝ, ∀ w, ((m - 1 / (2 * lb) * ‖w - x₀‖ ^ 2 : ℝ) : EReal) ≤ f w := by
  obtain ⟨lb, hlb, x₀, hinf⟩ := h
  obtain ⟨m, -, hm⟩ := EReal.exists_between_coe_real hinf
  refine ⟨lb, hlb, x₀, m, fun w ↦ ?_⟩
  have h1 : (m : EReal) ≤ f w + ((1 / (2 * lb) * ‖w - x₀‖ ^ 2 : ℝ) : EReal) :=
    hm.le.trans (iInf_le (fun w ↦ f w + ((1 / (2 * lb) * ‖w - x₀‖ ^ 2 : ℝ) : EReal)) w)
  rcases ereal_trichotomy (f w) with hfw | hfw | ⟨a, ha⟩
  · rw [hfw, EReal.bot_add] at h1
    exact absurd (le_bot_iff.1 h1) (EReal.coe_ne_bot m)
  · rw [hfw]
    exact le_top
  · rw [ha, ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
    rw [ha, EReal.coe_le_coe_iff]
    linarith

/-- **Proposition 13.37**, formula 13(30): for a prox-bounded function, the prox-regularity
inequality holds for all `x'`, uniformly over a localization of `∂f`. -/
theorem IsProxRegularAt.exists_global_inequality {f : E → EReal} {x vb : E}
    (hpr : IsProxRegularAt f x vb) (hpb : IsProxBounded f) :
    ∃ ε > 0, ∃ μ > 0, ∀ y v, v ∈ subdifferential f y → ‖v - vb‖ < ε → ‖y - x‖ < ε →
      f y < f x + ε → ∀ x', f y + ((⟪v, x' - y⟫_ℝ - μ / 2 * ‖x' - y‖ ^ 2 : ℝ) : EReal) ≤ f x' := by
  obtain ⟨⟨hx1, hx2, -⟩, -, ε, hε, ρ, hρ, hineq⟩ := hpr
  obtain ⟨lb, hlb, x₀, m, hm⟩ := hpb.exists_quadratic_minorant
  set c := (f x).toReal with hc_def
  have hc : f x = (c : EReal) := (EReal.coe_toReal hx2 hx1).symm
  set V := ‖vb‖ + 1
  set D := ‖x - x₀‖ + 1
  set M := c + 1 - m + D ^ 2 / lb
  set A := 2 / ε * (V + 2 * |M| / ε)
  set μ := max ρ (2 * (A + 1 / lb)) + 1
  have hμ : 0 < μ := by have := le_max_left ρ (2 * (A + 1 / lb)); linarith
  have hμρ : ρ ≤ μ := by have := le_max_left ρ (2 * (A + 1 / lb)); linarith
  have hμA : A + 1 / lb ≤ μ / 2 := by
    have := le_max_right ρ (2 * (A + 1 / lb)); linarith
  refine ⟨min (ε / 2) 1, lt_min (half_pos hε) one_pos, μ, hμ,
    fun y v hv hvv hyx hfy x' ↦ ?_⟩
  have hε2 : min (ε / 2) 1 ≤ ε / 2 := min_le_left _ _
  have hε1 : min (ε / 2) 1 ≤ 1 := min_le_right _ _
  obtain ⟨b, hb⟩ := hv.1
  rw [hb]
  have hby : b < c + 1 := by
    rw [hb, hc, ← EReal.coe_add, EReal.coe_lt_coe_iff] at hfy
    linarith
  by_cases hx'x : ‖x' - x‖ ≤ ε
  · have h1 := hineq y v hv (by linarith) (by linarith) (by
      rw [hb, hc, ← EReal.coe_add, EReal.coe_lt_coe_iff]
      rw [hb, hc, ← EReal.coe_add, EReal.coe_lt_coe_iff] at hfy
      linarith) x' (by rwa [mem_closedBall, dist_eq_norm])
    rw [hb] at h1
    refine le_trans (add_le_add le_rfl (EReal.coe_le_coe_iff.2 ?_)) h1
    have : ρ / 2 * ‖x' - y‖ ^ 2 ≤ μ / 2 * ‖x' - y‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    linarith
  · push_neg at hx'x
    set t := ‖x' - y‖
    have ht : ε / 2 ≤ t := by
      have h1 : ‖x' - x‖ ≤ t + ‖y - x‖ := by
        calc ‖x' - x‖ = ‖(x' - y) + (y - x)‖ := by congr 1; abel
          _ ≤ t + ‖y - x‖ := norm_add_le _ _
      linarith
    have ht0 : 0 < t := by linarith
    have hm' := hm x'
    rcases ereal_trichotomy (f x') with hfx' | hfx' | ⟨a, ha⟩
    · rw [hfx'] at hm'
      exact absurd (le_bot_iff.1 hm') (EReal.coe_ne_bot _)
    · rw [hfx']
      exact le_top
    · rw [ha, EReal.coe_le_coe_iff] at hm'
      rw [ha, ← EReal.coe_add, EReal.coe_le_coe_iff]
      have hvn : ‖v‖ ≤ V := by
        have := norm_le_insert' v vb
        linarith [norm_sub_rev v vb]
      have hinner : ⟪v, x' - y⟫_ℝ ≤ V * t :=
        (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hvn (norm_nonneg _))
      have hyx₀ : ‖y - x₀‖ ≤ D := by
        calc ‖y - x₀‖ = ‖(y - x) + (x - x₀)‖ := by congr 1; abel
          _ ≤ ‖y - x‖ + ‖x - x₀‖ := norm_add_le _ _
          _ ≤ D := by linarith
      have hx'x₀ : ‖x' - x₀‖ ≤ t + D := by
        calc ‖x' - x₀‖ = ‖(x' - y) + (y - x₀)‖ := by congr 1; abel
          _ ≤ t + ‖y - x₀‖ := norm_add_le _ _
          _ ≤ t + D := by linarith
      have hsq : ‖x' - x₀‖ ^ 2 ≤ 2 * t ^ 2 + 2 * D ^ 2 := by
        have h0 : 0 ≤ ‖x' - x₀‖ := norm_nonneg _
        nlinarith [sq_nonneg (t - D)]
      have hq : 1 / (2 * lb) * ‖x' - x₀‖ ^ 2 ≤ t ^ 2 / lb + D ^ 2 / lb := by
        have h1 : 1 / (2 * lb) * ‖x' - x₀‖ ^ 2 ≤ 1 / (2 * lb) * (2 * t ^ 2 + 2 * D ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
        have h2 : 1 / (2 * lb) * (2 * t ^ 2 + 2 * D ^ 2) = t ^ 2 / lb + D ^ 2 / lb := by
          field_simp
        linarith
      -- the quadratic growth `A t² ≥ V t + M` for `t ≥ ε/2`
      have h2t : 1 ≤ 2 / ε * t := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hε]
        linarith
      have hgrow : V * t + M ≤ A * t ^ 2 := by
        have hM : M ≤ |M| := le_abs_self M
        have hA : A * t ^ 2 = (2 / ε * t) * (V * t) + (2 / ε * t) * (2 * |M| / ε * t) := by
          simp only [A]
          ring
        have h3 : V * t ≤ (2 / ε * t) * (V * t) :=
          le_mul_of_one_le_left (by positivity) h2t
        have h4 : |M| ≤ 2 * |M| / ε * t := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hε]
          nlinarith [abs_nonneg M]
        have h5 : 2 * |M| / ε * t ≤ (2 / ε * t) * (2 * |M| / ε * t) :=
          le_mul_of_one_le_left (by positivity) h2t
        linarith
      have hμt : (A + 1 / lb) * t ^ 2 ≤ μ / 2 * t ^ 2 :=
        mul_le_mul_of_nonneg_right hμA (sq_nonneg t)
      have hexp : (A + 1 / lb) * t ^ 2 = A * t ^ 2 + t ^ 2 / lb := by ring
      simp only [M] at hgrow
      linarith

/-- The proximal objective is minimized exactly at `y` when the global prox-regularity
inequality holds at `(y, v)` with constant `μ < 1/λ`. -/
theorem proximalMappingEReal_eq_singleton_of_global {f : E → EReal} {y v : E} {b μ lam : ℝ}
    (hb : f y = b) (hlam : 0 < lam) (hμ : lam * μ < 1)
    (hglob : ∀ x', f y + ((⟪v, x' - y⟫_ℝ - μ / 2 * ‖x' - y‖ ^ 2 : ℝ) : EReal) ≤ f x') :
    proximalMappingEReal f lam (y + lam • v) = {y} ∧
      moreauEnvelopeEReal f lam (y + lam • v) = ((b + lam / 2 * ‖v‖ ^ 2 : ℝ) : EReal) := by
  have hobj : ∀ w, proximalObjectiveEReal f lam (y + lam • v) w =
      f w + ((1 / (2 * lam) * ‖w - y‖ ^ 2 - ⟪v, w - y⟫_ℝ + lam / 2 * ‖v‖ ^ 2 : ℝ) : EReal) := by
    intro w
    simp only [proximalObjectiveEReal]
    congr 2
    have e : w - (y + lam • v) = (w - y) - lam • v := by abel
    rw [e, norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_of_nonneg hlam.le,
      real_inner_comm v (w - y)]
    field_simp
  have hy : proximalObjectiveEReal f lam (y + lam • v) y =
      ((b + lam / 2 * ‖v‖ ^ 2 : ℝ) : EReal) := by
    rw [hobj, hb, sub_self, norm_zero, inner_zero_right, ← EReal.coe_add]
    congr 1
    ring
  have hgap : ∀ w, ((b + lam / 2 * ‖v‖ ^ 2 + (1 / (2 * lam) - μ / 2) * ‖w - y‖ ^ 2 : ℝ) : EReal) ≤
      proximalObjectiveEReal f lam (y + lam • v) w := by
    intro w
    rw [hobj]
    have h1 := hglob w
    rw [hb, ← EReal.coe_add] at h1
    rcases ereal_trichotomy (f w) with hfw | hfw | ⟨a, ha⟩
    · rw [hfw] at h1
      exact absurd (le_bot_iff.1 h1) (EReal.coe_ne_bot _)
    · rw [hfw, EReal.top_add_coe]
      exact le_top
    · rw [ha, EReal.coe_le_coe_iff] at h1
      rw [ha, ← EReal.coe_add, EReal.coe_le_coe_iff]
      linarith
  have hpos : 0 < 1 / (2 * lam) - μ / 2 := by
    rw [sub_pos, div_lt_div_iff₀ two_pos (by positivity)]
    linarith
  have henv : moreauEnvelopeEReal f lam (y + lam • v) = ((b + lam / 2 * ‖v‖ ^ 2 : ℝ) : EReal) := by
    apply le_antisymm
    · rw [moreauEnvelopeEReal_eq_iInf_proximalObjectiveEReal, ← hy]
      exact iInf_le _ y
    · rw [moreauEnvelopeEReal_eq_iInf_proximalObjectiveEReal]
      refine le_iInf fun w ↦ (EReal.coe_le_coe_iff.2 ?_).trans (hgap w)
      have : 0 ≤ (1 / (2 * lam) - μ / 2) * ‖w - y‖ ^ 2 := by positivity
      linarith
  refine ⟨?_, henv⟩
  ext w
  simp only [mem_proximalMappingEReal_iff, mem_singleton_iff, henv]
  constructor
  · rintro ⟨hw, -⟩
    by_contra hne
    have h1 := hgap w
    rw [hw, EReal.coe_le_coe_iff] at h1
    have h2 : 0 < ‖w - y‖ ^ 2 := by
      have := norm_pos_iff.2 (sub_ne_zero.2 hne)
      positivity
    nlinarith
  · rintro rfl
    exact ⟨hy, EReal.coe_lt_top _⟩

/-- The lower estimate behind the localized proximal problems: with the global inequality at
`(y, v)` and `u = y + λv`, the proximal objective at `u'` grows away from `y`. -/
theorem proximal_gap_of_global {f : E → EReal} {y v u' w : E} {b μ lam : ℝ} (hb : f y = b)
    (hlam : 0 < lam) (hlamμ : 2 * lam * μ ≤ 1)
    (hglob : ∀ x', f y + ((⟪v, x' - y⟫_ℝ - μ / 2 * ‖x' - y‖ ^ 2 : ℝ) : EReal) ≤ f x')
    (hw : f w ≠ ⊤) :
    b + 1 / (2 * lam) * ‖y - u'‖ ^ 2 + 1 / (4 * lam) * ‖w - y‖ ^ 2 -
        1 / lam * (‖w - y‖ * ‖u' - (y + lam • v)‖) ≤
      (f w).toReal + 1 / (2 * lam) * ‖w - u'‖ ^ 2 := by
  have h1 := hglob w
  have hwb : f w ≠ ⊥ := fun h ↦ by
    rw [h, hb, ← EReal.coe_add] at h1
    exact EReal.coe_ne_bot _ (le_bot_iff.1 h1)
  rw [hb, ← EReal.coe_toReal hw hwb, ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
  have e1 : ‖w - u'‖ ^ 2 = ‖w - y‖ ^ 2 + 2 * ⟪w - y, y - u'⟫_ℝ + ‖y - u'‖ ^ 2 := by
    rw [show w - u' = (w - y) + (y - u') by abel]
    exact norm_add_sq_real _ _
  have e2 : ⟪w - y, y - u'⟫_ℝ = -lam * ⟪v, w - y⟫_ℝ - ⟪w - y, u' - (y + lam • v)⟫_ℝ := by
    rw [show y - u' = -(lam • v) - (u' - (y + lam • v)) by abel, inner_sub_right, inner_neg_right,
      real_inner_smul_right, real_inner_comm v (w - y)]
    ring
  have hcs : ⟪w - y, u' - (y + lam • v)⟫_ℝ ≤ ‖w - y‖ * ‖u' - (y + lam • v)‖ :=
    real_inner_le_norm _ _
  have hμ : μ / 2 * ‖w - y‖ ^ 2 ≤ (1 / (2 * lam) - 1 / (4 * lam)) * ‖w - y‖ ^ 2 := by
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    rw [show 1 / (2 * lam) - 1 / (4 * lam) = 1 / (4 * lam) by field_simp; ring]
    rw [div_le_div_iff₀ two_pos (by positivity)]
    linarith
  have hexp : 1 / (2 * lam) * ‖w - u'‖ ^ 2 = 1 / (2 * lam) * ‖w - y‖ ^ 2 - ⟪v, w - y⟫_ℝ -
      1 / lam * ⟪w - y, u' - (y + lam • v)⟫_ℝ + 1 / (2 * lam) * ‖y - u'‖ ^ 2 := by
    rw [e1, e2]
    field_simp
    ring
  have hcs' : 1 / lam * ⟪w - y, u' - (y + lam • v)⟫_ℝ ≤
      1 / lam * (‖w - y‖ * ‖u' - (y + lam • v)‖) :=
    mul_le_mul_of_nonneg_left hcs (by positivity)
  have hsplit : 1 / (2 * lam) * ‖w - y‖ ^ 2 = 1 / (4 * lam) * ‖w - y‖ ^ 2 +
      (1 / (2 * lam) - 1 / (4 * lam)) * ‖w - y‖ ^ 2 := by ring
  linarith

variable [FiniteDimensional ℝ E]

/-- **Proposition 13.37**, the localized proximal problems: near `u = y + λv` for `v` in the
localization `T(y)`, proximal points exist and every one of them stays in the localization with
the subgradient `λ⁻¹(u' - p)`. -/
theorem exists_ball_localized_prox {f : E → EReal} {x : E} {c ε₀ ε μ lam : ℝ}
    (hx : f x = c) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1)
    (hcl : ∀ α : ℝ, α ≤ c + ε₀ → IsClosed (closedBall x ε₀ ∩ {w | f w ≤ α}))
    (hbot : ∀ w, f w ≠ ⊥) (hε : 0 < ε) (hεε₀ : ε ≤ ε₀ / 4)
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hlamμ : 2 * lam * μ ≤ 1)
    (hglob : ∀ y v, v ∈ subdifferential f y → ‖v‖ < ε → ‖y - x‖ < ε → f y < f x + ε →
      ∀ x', f y + ((⟪v, x' - y⟫_ℝ - μ / 2 * ‖x' - y‖ ^ 2 : ℝ) : EReal) ≤ f x')
    {y v : E} (hv : v ∈ subdifferential f y) (hvε : ‖v‖ < ε) (hyx : ‖y - x‖ < ε)
    (hfy : f y < f x + ε) :
    ∃ r > 0, ∀ u' ∈ ball (y + lam • v) r, (proximalMappingEReal f lam u').Nonempty ∧
      ∀ p ∈ proximalMappingEReal f lam u', lam⁻¹ • (u' - p) ∈ subdifferential f p ∧
        ‖lam⁻¹ • (u' - p)‖ < ε ∧ ‖p - x‖ < ε ∧ f p < f x + ε := by
  have hproper : IsProper f :=
    ⟨⟨x, by rw [hx]; exact EReal.coe_lt_top c⟩, fun w ↦ bot_lt_iff_ne_bot.2 (hbot w)⟩
  have hgy := hglob y v hv hvε hyx hfy
  set b := (f y).toReal with hb_def
  have hb : f y = b := (EReal.coe_toReal (ne_top_of_lt hfy) (hbot y)).symm
  have hbc : b < c + ε := by
    rw [hb, hx, ← EReal.coe_add, EReal.coe_lt_coe_iff] at hfy
    exact hfy
  set u := y + lam • v with hu
  set K : Set E := closedBall x ε₀ ∩ {w | f w ≤ ((c + ε₀ : ℝ) : EReal)} with hK
  have hKcl : IsClosed K := hcl _ le_rfl
  have hKc : IsCompact K := (isCompact_closedBall x ε₀).of_isClosed_subset hKcl inter_subset_left
  have hyK : y ∈ K := ⟨by rw [mem_closedBall, dist_eq_norm]; linarith,
    show f y ≤ _ by rw [hb]; exact EReal.coe_le_coe_iff.2 (by linarith)⟩
  have hflsc : LowerSemicontinuousOn f K := by
    refine lowerSemicontinuousOn_of_isClosed_inter_sublevel (M := c + ε₀) (fun w hw ↦ hw.2)
      fun α hα ↦ ?_
    have heq : K ∩ {w | f w ≤ α} = closedBall x ε₀ ∩ {w | f w ≤ α} := by
      ext w
      constructor
      · rintro ⟨⟨h1, -⟩, h2⟩
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, h2.trans (EReal.coe_le_coe_iff.2 hα.le)⟩, h2⟩
    rw [heq]
    exact hcl α hα.le
  set r := min (min (min (ε₀ / 16) (lam * ε₀ / 4)) (min ((ε - ‖y - x‖) / 4)
    (lam * (ε - ‖v‖) / 5))) (min ((c + ε - b) / 16) lam) with hr
  have hr0 : 0 < r := by
    refine lt_min (lt_min (lt_min (by positivity) (by positivity)) (lt_min ?_ ?_))
      (lt_min ?_ hlam)
    · linarith
    · nlinarith
    · linarith
  refine ⟨r, hr0, fun u' hu' ↦ ?_⟩
  set s := ‖u' - u‖ with hs
  have hsr : s < r := by rw [hs, ← dist_eq_norm]; exact hu'
  have hs1 : s < ε₀ / 16 := hsr.trans_le ((min_le_left _ _).trans ((min_le_left _ _).trans
    (min_le_left _ _)))
  have hs2 : s < lam * ε₀ / 4 := hsr.trans_le ((min_le_left _ _).trans ((min_le_left _ _).trans
    (min_le_right _ _)))
  have hs3 : s < (ε - ‖y - x‖) / 4 :=
    hsr.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hs4 : s < lam * (ε - ‖v‖) / 5 := hsr.trans_le ((min_le_left _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hs5 : s < (c + ε - b) / 16 := hsr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hs6 : s < lam := hsr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hs0 : 0 ≤ s := norm_nonneg _
  -- the proximal objective
  set φ : E → EReal := proximalObjectiveEReal f lam u' with hφ
  have hφy : φ y = ((b + 1 / (2 * lam) * ‖y - u'‖ ^ 2 : ℝ) : EReal) := by
    simp only [hφ, proximalObjectiveEReal, hb, ← EReal.coe_add]
  have hyu' : ‖y - u'‖ ≤ lam * ε + s := by
    have e : y - u' = -(lam • v) - (u' - u) := by rw [hu]; abel
    rw [e]
    calc ‖-(lam • v) - (u' - u)‖ ≤ ‖-(lam • v)‖ + ‖u' - u‖ := norm_sub_le _ _
      _ = lam * ‖v‖ + s := by rw [norm_neg, norm_smul, Real.norm_of_nonneg hlam.le]
      _ ≤ lam * ε + s := by
        have := mul_le_mul_of_nonneg_left hvε.le hlam.le
        linarith
  have hφy_lt : b + 1 / (2 * lam) * ‖y - u'‖ ^ 2 < c + ε₀ := by
    have h1 : ‖y - u'‖ ^ 2 ≤ (lam * ε + s) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hyu' 2
    have h2 : 1 / (2 * lam) * (lam * ε + s) ^ 2 ≤ lam * ε ^ 2 + s ^ 2 / lam := by
      have : (lam * ε + s) ^ 2 ≤ 2 * (lam * ε) ^ 2 + 2 * s ^ 2 := by
        nlinarith [sq_nonneg (lam * ε - s)]
      calc 1 / (2 * lam) * (lam * ε + s) ^ 2 ≤ 1 / (2 * lam) * (2 * (lam * ε) ^ 2 + 2 * s ^ 2) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = lam * ε ^ 2 + s ^ 2 / lam := by field_simp
    have h3 : lam * ε ^ 2 ≤ ε / 4 := by
      have hε4 : ε ≤ 1 / 4 := by linarith
      calc lam * ε ^ 2 ≤ 1 * ε ^ 2 := mul_le_mul_of_nonneg_right hlam1 (sq_nonneg ε)
        _ = ε * ε := by ring
        _ ≤ ε * (1 / 4) := mul_le_mul_of_nonneg_left hε4 hε.le
        _ = ε / 4 := by ring
    have h4 : s ^ 2 / lam ≤ s * (ε₀ / 4) := by
      rw [div_le_iff₀ hlam]
      calc s ^ 2 = s * s := by ring
        _ ≤ s * (lam * ε₀ / 4) := mul_le_mul_of_nonneg_left hs2.le hs0
        _ = s * (ε₀ / 4) * lam := by ring
    have h5 : 1 / (2 * lam) * ‖y - u'‖ ^ 2 ≤ 1 / (2 * lam) * (lam * ε + s) ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h6 : s * (ε₀ / 4) ≤ ε₀ / 16 := by
      calc s * (ε₀ / 4) ≤ (ε₀ / 16) * (ε₀ / 4) :=
            mul_le_mul_of_nonneg_right hs1.le (by positivity)
        _ ≤ ε₀ / 16 := by nlinarith only [hε₀1, hε₀]
    linarith only [hbc, h2, h3, h4, h5, h6, hεε₀, hε₀]
  -- points outside `K` are worse than `y`
  have hgap := fun w (hw : f w ≠ ⊤) ↦ proximal_gap_of_global (u' := u') hb hlam hlamμ hgy hw
  have hout : ∀ w, w ∉ K → φ y < φ w := by
    intro w hwK
    by_cases hwt : f w = ⊤
    · rw [hφy]
      simp only [hφ, proximalObjectiveEReal, hwt, EReal.top_add_coe]
      exact EReal.coe_lt_top _
    have hwc : f w = ((f w).toReal : EReal) := (EReal.coe_toReal hwt (hbot w)).symm
    have hφw : φ w = (((f w).toReal + 1 / (2 * lam) * ‖w - u'‖ ^ 2 : ℝ) : EReal) := by
      simp only [hφ, proximalObjectiveEReal]
      rw [EReal.coe_add, ← hwc]
    rw [hφy, hφw, EReal.coe_lt_coe_iff]
    by_cases hwx : ‖w - x‖ ≤ ε₀
    · have hfw : c + ε₀ < (f w).toReal := by
        by_contra hcon
        push_neg at hcon
        exact hwK ⟨by rwa [mem_closedBall, dist_eq_norm], show f w ≤ _ by
          rw [hwc]; exact EReal.coe_le_coe_iff.2 hcon⟩
      have : 0 ≤ 1 / (2 * lam) * ‖w - u'‖ ^ 2 := by positivity
      linarith
    · push_neg at hwx
      have hwy : 3 * ε₀ / 4 < ‖w - y‖ := by
        have : ‖w - x‖ ≤ ‖w - y‖ + ‖y - x‖ := by
          calc ‖w - x‖ = ‖(w - y) + (y - x)‖ := by congr 1; abel
            _ ≤ _ := norm_add_le _ _
        linarith
      have h1 := hgap w hwt
      have h2 : 1 / lam * (‖w - y‖ * s) < 1 / (4 * lam) * ‖w - y‖ ^ 2 := by
        have h3 : 4 * s < ‖w - y‖ := by linarith
        have h4 : 0 < ‖w - y‖ := by linarith
        rw [show 1 / (4 * lam) * ‖w - y‖ ^ 2 = 1 / lam * (‖w - y‖ * (‖w - y‖ / 4)) by
          field_simp]
        exact mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left (by linarith) h4) (by positivity)
      linarith
  -- a global minimizer
  have hφK : LowerSemicontinuousOn φ K :=
    hflsc.add' ((continuous_coe_real_ereal.comp ((continuous_const.mul
      ((continuous_id.sub continuous_const).norm.pow 2)))).lowerSemicontinuous.lowerSemicontinuousOn
        K) fun w _ ↦ EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))
  obtain ⟨p₀, hp₀K, hp₀min⟩ := hφK.exists_isMinOn ⟨y, hyK⟩ hKc
  have hp₀le : ∀ w, φ p₀ ≤ φ w := by
    intro w
    by_cases hwK : w ∈ K
    · exact isMinOn_iff.1 hp₀min w hwK
    · exact (isMinOn_iff.1 hp₀min y hyK).trans (hout w hwK).le
  have henv : moreauEnvelopeEReal f lam u' = φ p₀ :=
    le_antisymm (iInf_le _ p₀) (le_iInf hp₀le)
  have hp₀y : φ p₀ ≤ φ y := hp₀le y
  have hφy_top : φ y < ⊤ := by rw [hφy]; exact EReal.coe_lt_top _
  refine ⟨⟨p₀, henv.symm, (le_of_eq henv).trans_lt (hp₀y.trans_lt hφy_top)⟩, fun p hp ↦ ?_⟩
  -- properties of every proximal point
  obtain ⟨hpφ, hpt⟩ := hp
  have hpφy : φ p ≤ φ y := by
    have : φ p = moreauEnvelopeEReal f lam u' := hpφ
    rw [this, henv]
    exact hp₀y
  have hfpt : f p ≠ ⊤ := by
    intro h
    have : φ p = ⊤ := by simp only [hφ, proximalObjectiveEReal, h, EReal.top_add_coe]
    rw [this] at hpφy
    exact (not_le.2 hφy_top) hpφy
  have hpc : f p = ((f p).toReal : EReal) := (EReal.coe_toReal hfpt (hbot p)).symm
  have hφp : φ p = (((f p).toReal + 1 / (2 * lam) * ‖p - u'‖ ^ 2 : ℝ) : EReal) := by
    simp only [hφ, proximalObjectiveEReal]
    rw [EReal.coe_add, ← hpc]
  rw [hφp, hφy, EReal.coe_le_coe_iff] at hpφy
  have hpy : ‖p - y‖ ≤ 4 * s := by
    by_contra hcon
    push_neg at hcon
    have h1 := hgap p hfpt
    have h4 : 0 < ‖p - y‖ := by linarith
    have h2 : 1 / lam * (‖p - y‖ * s) < 1 / (4 * lam) * ‖p - y‖ ^ 2 := by
      rw [show 1 / (4 * lam) * ‖p - y‖ ^ 2 = 1 / lam * (‖p - y‖ * (‖p - y‖ / 4)) by
        field_simp]
      exact mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left (by linarith) h4) (by positivity)
    linarith
  -- the subgradient `λ⁻¹(u' - p)`
  have hsub : lam⁻¹ • (u' - p) ∈ subdifferential f p := by
    have h1 := proximalMappingEReal_subset_inverse_subgradientShift hproper hlam u' ⟨hpφ, hpt⟩
    obtain ⟨v'', hv'', he⟩ := h1
    have : v'' = lam⁻¹ • (u' - p) := by
      rw [← he, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hlam.ne', one_smul]
    rwa [← this]
  refine ⟨hsub, ?_, ?_, ?_⟩
  · have e : lam⁻¹ • (u' - p) = v + lam⁻¹ • ((u' - u) - (p - y)) := by
      rw [hu]
      simp only [smul_sub, smul_add, smul_smul, inv_mul_cancel₀ hlam.ne', one_smul]
      abel
    rw [e]
    calc ‖v + lam⁻¹ • ((u' - u) - (p - y))‖ ≤ ‖v‖ + lam⁻¹ * (s + 4 * s) := by
          refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hlam.le)]
          exact mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add le_rfl hpy))
            (inv_nonneg.2 hlam.le)
      _ < ε := by
        have : lam⁻¹ * (s + 4 * s) < ε - ‖v‖ := by
          rw [inv_mul_lt_iff₀ hlam]
          linarith
        linarith
  · calc ‖p - x‖ = ‖(p - y) + (y - x)‖ := by congr 1; abel
      _ ≤ ‖p - y‖ + ‖y - x‖ := norm_add_le _ _
      _ < ε := by linarith
  · rw [hpc, hx, ← EReal.coe_add, EReal.coe_lt_coe_iff]
    -- `f(p) ≤ b + (‖y - u'‖² - ‖p - u'‖²)/(2λ)`
    have hdiff : ‖y - u'‖ ^ 2 - ‖p - u'‖ ^ 2 ≤ ‖p - y‖ * (‖y - u'‖ + ‖p - u'‖) := by
      have e : ‖y - u'‖ ^ 2 - ‖p - u'‖ ^ 2 = ⟪y - p, (y - u') + (p - u')⟫_ℝ := by
        rw [show y - p = (y - u') - (p - u') by abel, inner_sub_left, inner_add_right,
          inner_add_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
          real_inner_comm (p - u') (y - u')]
        ring
      rw [e, norm_sub_rev p y]
      exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (norm_add_le _ _)
        (norm_nonneg _))
    have hpu' : ‖p - u'‖ ≤ ‖p - y‖ + ‖y - u'‖ := by
      calc ‖p - u'‖ = ‖(p - y) + (y - u')‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    have hyu'' : ‖y - u'‖ ≤ lam + s := by
      have : lam * ε ≤ lam := mul_le_of_le_one_right hlam.le (by linarith)
      linarith
    have hbound : ‖p - y‖ * (‖y - u'‖ + ‖p - u'‖) ≤ 4 * s * (2 * lam + 6 * s) := by
      have h1 : ‖y - u'‖ + ‖p - u'‖ ≤ 2 * lam + 6 * s := by linarith
      calc ‖p - y‖ * (‖y - u'‖ + ‖p - u'‖) ≤ 4 * s * (‖y - u'‖ + ‖p - u'‖) :=
            mul_le_mul_of_nonneg_right hpy (by positivity)
        _ ≤ 4 * s * (2 * lam + 6 * s) := mul_le_mul_of_nonneg_left h1 (by positivity)
    have hfp : (f p).toReal ≤ b + 1 / (2 * lam) * (4 * s * (2 * lam + 6 * s)) := by
      have h1 : 1 / (2 * lam) * (‖y - u'‖ ^ 2 - ‖p - u'‖ ^ 2) ≤
          1 / (2 * lam) * (4 * s * (2 * lam + 6 * s)) :=
        mul_le_mul_of_nonneg_left (hdiff.trans hbound) (by positivity)
      have h2 : 1 / (2 * lam) * (‖y - u'‖ ^ 2 - ‖p - u'‖ ^ 2) =
          1 / (2 * lam) * ‖y - u'‖ ^ 2 - 1 / (2 * lam) * ‖p - u'‖ ^ 2 := by ring
      linarith
    have h3 : 1 / (2 * lam) * (4 * s * (2 * lam + 6 * s)) ≤ 16 * s := by
      rw [show 1 / (2 * lam) * (4 * s * (2 * lam + 6 * s)) = 4 * s + 12 * s * (s / lam) by
        field_simp; ring]
      have h7 : s / lam ≤ 1 := (div_le_one hlam).2 hs6.le
      have h8 := mul_le_mul_of_nonneg_left h7 (by positivity : (0 : ℝ) ≤ 12 * s)
      linarith
    linarith

/-- The `f`-attentive localization `T` of `∂f` around `(x̄, 0)` used in Proposition 13.37. -/
def proxLocalization (f : E → EReal) (x : E) (ε : ℝ) (y : E) : Set E :=
  {v | v ∈ subdifferential f y ∧ ‖y - x‖ < ε ∧ f y < f x + ε ∧ ‖v‖ < ε}

/-- The range `U_λ = rge(I + λT)` of Proposition 13.37. -/
def proxRange (f : E → EReal) (x : E) (ε lam : ℝ) : Set E :=
  {u | ∃ y, ∃ v ∈ proxLocalization f x ε y, u = y + lam • v}

omit [FiniteDimensional ℝ E] in
/-- Hypomonotonicity of the localization turns `I + λT` into a strongly monotone mapping. -/
theorem half_sq_le_inner_of_global {f : E → EReal} {y₀ v₀ y₁ v₁ : E} {μ lam : ℝ}
    (h0 : f y₀ ≠ ⊥ ∧ f y₀ ≠ ⊤) (h1 : f y₁ ≠ ⊥ ∧ f y₁ ≠ ⊤) (hlam : 0 ≤ lam)
    (hlamμ : 2 * lam * μ ≤ 1)
    (hg0 : f y₀ + ((⟪v₀, y₁ - y₀⟫_ℝ - μ / 2 * ‖y₁ - y₀‖ ^ 2 : ℝ) : EReal) ≤ f y₁)
    (hg1 : f y₁ + ((⟪v₁, y₀ - y₁⟫_ℝ - μ / 2 * ‖y₀ - y₁‖ ^ 2 : ℝ) : EReal) ≤ f y₀) :
    1 / 2 * ‖y₁ - y₀‖ ^ 2 ≤ ⟪y₁ - y₀, (y₁ + lam • v₁) - (y₀ + lam • v₀)⟫_ℝ := by
  rw [← EReal.coe_toReal h0.2 h0.1, ← EReal.coe_toReal h1.2 h1.1, ← EReal.coe_add,
    EReal.coe_le_coe_iff] at hg0 hg1
  have e1 : ‖y₀ - y₁‖ = ‖y₁ - y₀‖ := norm_sub_rev _ _
  have e2 : ⟪v₁, y₀ - y₁⟫_ℝ = -⟪v₁, y₁ - y₀⟫_ℝ := by rw [← inner_neg_right, neg_sub]
  rw [e1, e2] at hg1
  have hmono : -μ * ‖y₁ - y₀‖ ^ 2 ≤ ⟪v₁ - v₀, y₁ - y₀⟫_ℝ := by
    rw [inner_sub_left]
    linarith
  have e3 : ⟪y₁ - y₀, (y₁ + lam • v₁) - (y₀ + lam • v₀)⟫_ℝ =
      ‖y₁ - y₀‖ ^ 2 + lam * ⟪v₁ - v₀, y₁ - y₀⟫_ℝ := by
    rw [show (y₁ + lam • v₁) - (y₀ + lam • v₀) = (y₁ - y₀) + lam • (v₁ - v₀) by
      rw [smul_sub]; abel, inner_add_right, real_inner_self_eq_norm_sq, real_inner_smul_right,
      real_inner_comm]
  rw [e3]
  have h2 : lam * (-μ * ‖y₁ - y₀‖ ^ 2) ≤ lam * ⟪v₁ - v₀, y₁ - y₀⟫_ℝ :=
    mul_le_mul_of_nonneg_left hmono hlam
  have h3 : lam * μ * ‖y₁ - y₀‖ ^ 2 ≤ 1 / 2 * ‖y₁ - y₀‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  nlinarith

/-- **Proposition 13.37** (proximal mappings and Moreau envelopes): for `f` prox-regular at `x̄`
for `v̄ = 0` and prox-bounded there are an `f`-attentive localization `T` of `∂f` and `λ₀ > 0`
such that for every `λ ∈ (0, λ₀)` the set `U_λ = rge(I + λT)` is an open neighborhood of `x̄` on
which (a) `P_λ f` is single-valued, monotone and Lipschitz with `P_λ f(x̄) = x̄`, and (b) `e_λ f`
is differentiable with `∇e_λ f = λ⁻¹(I - P_λ f)`, a Lipschitz mapping (so `e_λ f` is `C¹⁺`
there, with `∇e_λ f(x̄) = 0`), and `∇e_λ f = (λI + T⁻¹)⁻¹`. -/
theorem proximal_mappings_and_moreau_envelopes {f : E → EReal} {x : E}
    (hpr : IsProxRegularAt f x 0) (hpb : IsProxBounded f) :
    ∃ ε > 0, ∃ lam₀ > 0, ∀ lam, 0 < lam → lam < lam₀ → ∃ P : E → E,
      IsOpen (proxRange f x ε lam) ∧ x ∈ proxRange f x ε lam ∧ P x = x ∧
      (∀ u ∈ proxRange f x ε lam, proximalMappingEReal f lam u = {P u}) ∧
      (∀ u ∈ proxRange f x ε lam, ∀ u' ∈ proxRange f x ε lam,
        0 ≤ ⟪P u' - P u, u' - u⟫_ℝ ∧ ‖P u' - P u‖ ≤ 2 * ‖u' - u‖) ∧
      (∀ u ∈ proxRange f x ε lam, moreauEnvelopeEReal f lam u ≠ ⊥ ∧
        moreauEnvelopeEReal f lam u ≠ ⊤ ∧
        HasFDerivAt (fun z ↦ (moreauEnvelopeEReal f lam z).toReal)
          (innerSL ℝ (lam⁻¹ • (u - P u))) u) ∧
      (∀ u ∈ proxRange f x ε lam, ∀ u' ∈ proxRange f x ε lam,
        ‖lam⁻¹ • (u' - P u') - lam⁻¹ • (u - P u)‖ ≤ 3 / lam * ‖u' - u‖) ∧
      (∀ u ∈ proxRange f x ε lam, ∀ w,
        lam⁻¹ • (u - P u) = w ↔ ∃ y, w ∈ proxLocalization f x ε y ∧ u = y + lam • w) := by
  obtain ⟨ε₂, hε₂, μ, hμ, hglob₂⟩ := hpr.exists_global_inequality hpb
  obtain ⟨⟨hx1, hx2, ε₀', hε₀', hcl'⟩, h0, -⟩ := hpr
  obtain ⟨lb, hlb, x₀, m, hm⟩ := hpb.exists_quadratic_minorant
  have hbot : ∀ w, f w ≠ ⊥ := fun w h ↦ by
    have := hm w
    rw [h] at this
    exact EReal.coe_ne_bot _ (le_bot_iff.1 this)
  set c := (f x).toReal with hc_def
  have hx : f x = (c : EReal) := (EReal.coe_toReal hx2 hx1).symm
  set ε₀ := min ε₀' 1 with hε₀_def
  have hε₀ : 0 < ε₀ := lt_min hε₀' one_pos
  have hε₀1 : ε₀ ≤ 1 := min_le_right _ _
  have hcl : ∀ α : ℝ, α ≤ c + ε₀ → IsClosed (closedBall x ε₀ ∩ {w | f w ≤ α}) := by
    intro α hα
    have h1 := hcl' α (by linarith [min_le_left ε₀' 1])
    have heq : closedBall x ε₀ ∩ {w | f w ≤ α} =
        closedBall x ε₀ ∩ (closedBall x ε₀' ∩ {w | f w ≤ α}) := by
      ext w
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, closedBall_subset_closedBall (min_le_left _ _) h1, h2⟩
      · rintro ⟨h1, -, h2⟩
        exact ⟨h1, h2⟩
    rw [heq]
    exact isClosed_closedBall.inter h1
  set ε := min ε₂ (ε₀ / 4) with hε_def
  have hε : 0 < ε := lt_min hε₂ (by positivity)
  have hεε₂ : ε ≤ ε₂ := min_le_left _ _
  have hεε₀ : ε ≤ ε₀ / 4 := min_le_right _ _
  have hglob : ∀ y v, v ∈ subdifferential f y → ‖v‖ < ε → ‖y - x‖ < ε → f y < f x + ε →
      ∀ x', f y + ((⟪v, x' - y⟫_ℝ - μ / 2 * ‖x' - y‖ ^ 2 : ℝ) : EReal) ≤ f x' := by
    intro y v hv hvε hyx hfy
    refine hglob₂ y v hv (by rw [sub_zero]; linarith) (by linarith) (lt_of_lt_of_le hfy ?_)
    rw [hx, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
    linarith
  set lam₀ := min 1 (1 / (2 * μ)) with hlam₀
  have hlam₀0 : 0 < lam₀ := lt_min one_pos (by positivity)
  refine ⟨ε, hε, lam₀, hlam₀0, fun lam hlam hlamlt ↦ ?_⟩
  have hlam1 : lam ≤ 1 := (hlamlt.trans_le (min_le_left _ _)).le
  have hlamμ : 2 * lam * μ ≤ 1 := by
    have h1 : lam < 1 / (2 * μ) := hlamlt.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at h1
    linarith
  have hlamμ' : lam * μ < 1 := by nlinarith
  -- membership in the localization gives unique proximal points
  have hfin : ∀ y v, v ∈ proxLocalization f x ε y → f y ≠ ⊥ ∧ f y ≠ ⊤ := fun y v hv ↦
    ⟨hbot y, ne_top_of_lt hv.2.2.1⟩
  have hprox : ∀ y v, v ∈ proxLocalization f x ε y →
      proximalMappingEReal f lam (y + lam • v) = {y} ∧
        moreauEnvelopeEReal f lam (y + lam • v) =
          (((f y).toReal + lam / 2 * ‖v‖ ^ 2 : ℝ) : EReal) := by
    intro y v hv
    exact proximalMappingEReal_eq_singleton_of_global
      (EReal.coe_toReal (hfin y v hv).2 (hfin y v hv).1).symm hlam hlamμ'
      (hglob y v hv.1 hv.2.2.2 hv.2.1 hv.2.2.1)
  -- the proximal selection
  classical
  set P : E → E := fun u ↦ if h : (proximalMappingEReal f lam u).Nonempty then h.some else u
    with hP
  have hPU : ∀ y v, v ∈ proxLocalization f x ε y → P (y + lam • v) = y := by
    intro y v hv
    have h1 := (hprox y v hv).1
    have hne : (proximalMappingEReal f lam (y + lam • v)).Nonempty := by rw [h1]; simp
    simp only [hP, dif_pos hne]
    exact (Set.eq_singleton_iff_unique_mem.1 h1).2 _ hne.some_mem
  have hmemU : ∀ u ∈ proxRange f x ε lam, ∃ y v, v ∈ proxLocalization f x ε y ∧
      u = y + lam • v ∧ P u = y := by
    rintro u ⟨y, v, hv, rfl⟩
    exact ⟨y, v, hv, rfl, hPU y v hv⟩
  have hx0 : (0 : E) ∈ proxLocalization f x ε x :=
    ⟨h0, by simpa using hε, by rw [hx, ← EReal.coe_add, EReal.coe_lt_coe_iff]; linarith,
      by simpa using hε⟩
  -- openness of `U_λ`
  have hopen : IsOpen (proxRange f x ε lam) := by
    rw [isOpen_iff_mem_nhds]
    rintro u ⟨y, v, hv, rfl⟩
    obtain ⟨r, hr, hball⟩ := exists_ball_localized_prox hx hε₀ hε₀1 hcl hbot hε hεε₀ hlam
      hlam1 hlamμ hglob hv.1 hv.2.2.2 hv.2.1 hv.2.2.1
    refine Filter.mem_of_superset (ball_mem_nhds _ hr) fun u' hu' ↦ ?_
    obtain ⟨⟨p, hp⟩, hall⟩ := hball u' hu'
    obtain ⟨h1, h2, h3, h4⟩ := hall p hp
    refine ⟨p, lam⁻¹ • (u' - p), ⟨h1, h3, h4, h2⟩, ?_⟩
    rw [smul_smul, mul_inv_cancel₀ hlam.ne', one_smul, add_sub_cancel]
  have hxU : x ∈ proxRange f x ε lam := ⟨x, 0, hx0, by simp⟩
  have hPx : P x = x := by
    have := hPU x 0 hx0
    simpa using this
  -- monotonicity and Lipschitz continuity of `P`
  have hmono : ∀ u ∈ proxRange f x ε lam, ∀ u' ∈ proxRange f x ε lam,
      1 / 2 * ‖P u' - P u‖ ^ 2 ≤ ⟪P u' - P u, u' - u⟫_ℝ := by
    intro u hu u' hu'
    obtain ⟨y₀, v₀, hv₀, rfl, hP₀⟩ := hmemU u hu
    obtain ⟨y₁, v₁, hv₁, rfl, hP₁⟩ := hmemU u' hu'
    rw [hP₀, hP₁]
    exact half_sq_le_inner_of_global (hfin y₀ v₀ hv₀) (hfin y₁ v₁ hv₁) hlam.le hlamμ
      (hglob y₀ v₀ hv₀.1 hv₀.2.2.2 hv₀.2.1 hv₀.2.2.1 y₁)
      (hglob y₁ v₁ hv₁.1 hv₁.2.2.2 hv₁.2.1 hv₁.2.2.1 y₀)
  have hlip : ∀ u ∈ proxRange f x ε lam, ∀ u' ∈ proxRange f x ε lam,
      ‖P u' - P u‖ ≤ 2 * ‖u' - u‖ := by
    intro u hu u' hu'
    have h1 := hmono u hu u' hu'
    have h2 : ⟪P u' - P u, u' - u⟫_ℝ ≤ ‖P u' - P u‖ * ‖u' - u‖ := real_inner_le_norm _ _
    rcases (norm_nonneg (P u' - P u)).eq_or_lt with h3 | h3
    · rw [← h3]
      positivity
    · nlinarith
  -- the envelope values
  have henvU : ∀ u ∈ proxRange f x ε lam, moreauEnvelopeEReal f lam u =
      (((f (P u)).toReal + 1 / (2 * lam) * ‖P u - u‖ ^ 2 : ℝ) : EReal) := by
    intro u hu
    obtain ⟨y, v, hv, rfl, hPy⟩ := hmemU u hu
    rw [(hprox y v hv).2, hPy]
    congr 1
    rw [show y - (y + lam • v) = -(lam • v) by abel, norm_neg, norm_smul,
      Real.norm_of_nonneg hlam.le]
    field_simp
  have hfinP : ∀ u ∈ proxRange f x ε lam, f (P u) = ((f (P u)).toReal : EReal) := by
    intro u hu
    obtain ⟨y, v, hv, rfl, hPy⟩ := hmemU u hu
    rw [hPy]
    exact (EReal.coe_toReal (hfin y v hv).2 (hfin y v hv).1).symm
  set Ef : E → ℝ := fun z ↦ (moreauEnvelopeEReal f lam z).toReal with hEf
  have hEU : ∀ u ∈ proxRange f x ε lam,
      Ef u = (f (P u)).toReal + 1 / (2 * lam) * ‖P u - u‖ ^ 2 := by
    intro u hu
    simp only [hEf, henvU u hu, EReal.toReal_coe]
  -- the comparison `e(u') ≤ f(p) + ‖p - u'‖²/(2λ)` for any `p`
  have hupper : ∀ u' ∈ proxRange f x ε lam, ∀ p, f p ≠ ⊤ →
      Ef u' ≤ (f p).toReal + 1 / (2 * lam) * ‖p - u'‖ ^ 2 := by
    intro u' hu' p hp
    have h1 : moreauEnvelopeEReal f lam u' ≤ f p + ((1 / (2 * lam) * ‖p - u'‖ ^ 2 : ℝ) : EReal) :=
      iInf_le (fun w ↦ f w + ((1 / (2 * lam) * ‖w - u'‖ ^ 2 : ℝ) : EReal)) p
    rw [henvU u' hu', ← EReal.coe_toReal hp (hbot p), ← EReal.coe_add,
      EReal.coe_le_coe_iff] at h1
    rw [hEU u' hu']
    exact h1
  have hquad : ∀ p u u' : E, 1 / (2 * lam) * ‖p - u'‖ ^ 2 =
      1 / (2 * lam) * ‖p - u‖ ^ 2 + ⟪lam⁻¹ • (u - p), u' - u⟫_ℝ +
        1 / (2 * lam) * ‖u' - u‖ ^ 2 := by
    intro p u u'
    rw [show p - u' = (p - u) - (u' - u) by abel, norm_sub_sq_real, real_inner_smul_left,
      show u - p = -(p - u) by abel, inner_neg_left]
    field_simp
    ring
  have hgradLip : ∀ u ∈ proxRange f x ε lam, ∀ u' ∈ proxRange f x ε lam,
      ‖lam⁻¹ • (u' - P u') - lam⁻¹ • (u - P u)‖ ≤ 3 / lam * ‖u' - u‖ := by
    intro u hu u' hu'
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hlam.le),
      show u' - P u' - (u - P u) = (u' - u) - (P u' - P u) by abel]
    have h1 := norm_sub_le (u' - u) (P u' - P u)
    have h2 := hlip u hu u' hu'
    rw [show 3 / lam * ‖u' - u‖ = lam⁻¹ * (3 * ‖u' - u‖) by field_simp]
    exact mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 hlam.le)
  have hderiv : ∀ u ∈ proxRange f x ε lam, HasFDerivAt Ef (innerSL ℝ (lam⁻¹ • (u - P u))) u := by
    intro u hu
    refine HasFDerivAtFilter.of_isLittleO (Asymptotics.isLittleO_iff.2 fun δ hδ ↦ ?_)
    have hball : ball u (δ * lam / 4) ∈ 𝓝 u := ball_mem_nhds u (by positivity)
    filter_upwards [hopen.mem_nhds hu, hball] with u' hu' hu'b
    rw [mem_ball, dist_eq_norm] at hu'b
    have hup := hupper u' hu' (P u) (by rw [hfinP u hu]; exact EReal.coe_ne_top _)
    have hlow := hupper u hu (P u') (by rw [hfinP u' hu']; exact EReal.coe_ne_top _)
    rw [hquad (P u) u u'] at hup
    rw [hquad (P u') u' u] at hlow
    have e1 := hEU u hu
    have e2 := hEU u' hu'
    have hg' : ⟪lam⁻¹ • (u' - P u'), u - u'⟫_ℝ ≤
        -⟪lam⁻¹ • (u - P u), u' - u⟫_ℝ + 3 / lam * ‖u' - u‖ ^ 2 := by
      have e : ⟪lam⁻¹ • (u' - P u'), u - u'⟫_ℝ = -⟪lam⁻¹ • (u - P u), u' - u⟫_ℝ -
          ⟪lam⁻¹ • (u' - P u') - lam⁻¹ • (u - P u), u' - u⟫_ℝ := by
        rw [show u - u' = -(u' - u) by abel, inner_neg_right, inner_sub_left]
        ring
      rw [e]
      have h1 : -⟪lam⁻¹ • (u' - P u') - lam⁻¹ • (u - P u), u' - u⟫_ℝ ≤
          ‖lam⁻¹ • (u' - P u') - lam⁻¹ • (u - P u)‖ * ‖u' - u‖ := by
        have := neg_le_abs (⟪lam⁻¹ • (u' - P u') - lam⁻¹ • (u - P u), u' - u⟫_ℝ)
        exact this.trans (abs_real_inner_le_norm _ _)
      have h2 := mul_le_mul_of_nonneg_right (hgradLip u hu u' hu') (norm_nonneg (u' - u))
      nlinarith
    have hnu : 1 / (2 * lam) * ‖u - u'‖ ^ 2 = 1 / (2 * lam) * ‖u' - u‖ ^ 2 := by
      rw [norm_sub_rev]
    simp only [innerSL_apply_apply, Real.norm_eq_abs]
    rw [abs_le]
    have hδ' : 4 / lam * ‖u' - u‖ ^ 2 ≤ δ * ‖u' - u‖ := by
      have h1 : 4 / lam * ‖u' - u‖ ≤ δ := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hlam]
        linarith
      calc 4 / lam * ‖u' - u‖ ^ 2 = (4 / lam * ‖u' - u‖) * ‖u' - u‖ := by ring
        _ ≤ δ * ‖u' - u‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    have hsq : 0 ≤ 1 / (2 * lam) * ‖u' - u‖ ^ 2 := by positivity
    have h3n : 0 ≤ 3 / lam * ‖u' - u‖ ^ 2 := by positivity
    have hsplit : 4 / lam * ‖u' - u‖ ^ 2 = 3 / lam * ‖u' - u‖ ^ 2 +
        2 * (1 / (2 * lam) * ‖u' - u‖ ^ 2) := by field_simp; ring
    constructor <;> linarith
  refine ⟨P, hopen, hxU, hPx, ?_, fun u hu u' hu' ↦ ⟨?_, hlip u hu u' hu'⟩, ?_, hgradLip, ?_⟩
  · intro u hu
    obtain ⟨y, v, hv, rfl, hPy⟩ := hmemU u hu
    rw [hPy]
    exact (hprox y v hv).1
  · have h1 := hmono u hu u' hu'
    have h2 : 0 ≤ 1 / 2 * ‖P u' - P u‖ ^ 2 := by positivity
    linarith
  · intro u hu
    rw [henvU u hu]
    exact ⟨EReal.coe_ne_bot _, EReal.coe_ne_top _, hderiv u hu⟩
  · intro u hu w
    obtain ⟨y, v, hv, rfl, hPy⟩ := hmemU u hu
    rw [hPy, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hlam.ne', one_smul]
    constructor
    · rintro rfl
      exact ⟨y, hv, rfl⟩
    · rintro ⟨y', hw, he⟩
      have h1 := hPU y' w hw
      rw [← he, hPy] at h1
      rw [h1] at he
      exact smul_right_injective E hlam.ne' (add_left_cancel he)

end RW
