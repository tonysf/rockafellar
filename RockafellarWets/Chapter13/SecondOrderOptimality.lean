/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Second-order conditions for optimality

Theorem 13.24.  Local optimality of `x̄` for the minimization of `f` is
`IsLocalMin f x̄` at a point where `f(x̄)` is finite, as in Theorem 10.1.  The
properness of `f` assumed in the book is not needed.  The quadratic growth
condition of 13.24(c) is `f(x) ≥ f(x̄) + ε‖x - x̄‖²` for `‖x - x̄‖ ≤ δ`.
-/

import RockafellarWets.Chapter13.SecondSubderivatives
import RockafellarWets.Chapter10.FermatRule

open Filter Set Topology Metric
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The quotient 13(5) for `v = 0`. -/
theorem secondDifferenceQuotient_zero_vec {f : E → EReal} {x : E} {c : ℝ} (hx : f x = c)
    (τ : ℝ) (w : E) :
    secondDifferenceQuotient f x 0 τ w = ((2 / τ ^ 2 : ℝ) : EReal) * (f (x + τ • w) - c) := by
  rw [secondDifferenceQuotient, hx, inner_zero_left, mul_zero, EReal.coe_zero, sub_zero]

/-- **Theorem 13.24(a)**: at a finite local minimum, `0 ∈ ∂̂f(x̄)` and
`d²f(x̄ | 0)(w) ≥ 0` for all `w`. -/
theorem IsLocalMin.secondOrder_necessary {f : E → EReal} {x : E} {c : ℝ} (hm : IsLocalMin f x)
    (hx : f x = c) :
    (0 : E) ∈ regularSubdifferential f x ∧ ∀ w, 0 ≤ secondSubderivative f x 0 w := by
  refine ⟨RW.IsLocalMin.zero_mem_regularSubdifferential hm hx,
    fun w ↦ le_liminf_of_le (h := ?_)⟩
  have hpath := tendsto_add_smul_nhds x w
  filter_upwards [hpath.eventually hm, tendsto_fst.eventually self_mem_nhdsWithin] with p hp hτ
  change 0 < p.1 at hτ
  rw [secondDifferenceQuotient_zero_vec hx]
  rw [hx] at hp
  rcases ereal_trichotomy (f (x + p.1 • p.2)) with h | h | ⟨r, h⟩
  · rw [h] at hp
    exact absurd (le_bot_iff.1 hp) (EReal.coe_ne_bot c)
  · rw [h, EReal.top_sub_coe, EReal.coe_mul_top_of_pos (by positivity)]
    exact le_top
  · rw [h] at hp ⊢
    rw [← EReal.coe_sub, ← EReal.coe_mul]
    exact EReal.coe_nonneg.2 (mul_nonneg (by positivity)
      (sub_nonneg.2 (EReal.coe_le_coe_iff.1 hp)))

/-- The proof of **Theorem 13.24(c)**: quadratic growth with constant `ε` gives
`d²f(x̄ | 0)(w) ≥ 2ε‖w‖²`. -/
theorem secondSubderivative_zero_ge_of_growth {f : E → EReal} {x : E} {c ε δ : ℝ}
    (hx : f x = c) (hδ : 0 < δ)
    (hg : ∀ y, ‖y - x‖ ≤ δ → ((c + ε * ‖y - x‖ ^ 2 : ℝ) : EReal) ≤ f y) (w : E) :
    ((2 * ε * ‖w‖ ^ 2 : ℝ) : EReal) ≤ secondSubderivative f x 0 w := by
  have hpath := tendsto_add_smul_nhds x w
  have hnorm : Tendsto (fun p : ℝ × E ↦ 2 * ε * ‖p.2‖ ^ 2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w)
      (𝓝 (2 * ε * ‖w‖ ^ 2)) :=
    ((continuous_norm.tendsto w).comp tendsto_snd).pow 2 |>.const_mul (2 * ε)
  have hev : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w,
      ((2 * ε * ‖p.2‖ ^ 2 : ℝ) : EReal) ≤ secondDifferenceQuotient f x 0 p.1 p.2 := by
    filter_upwards [hpath.eventually (closedBall_mem_nhds x hδ),
      tendsto_fst.eventually self_mem_nhdsWithin] with p hp hτ
    change 0 < p.1 at hτ
    rw [dist_eq_norm] at hp
    have hgy := hg _ hp
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hτ.le] at hgy
    rw [secondDifferenceQuotient_zero_vec hx]
    rcases ereal_trichotomy (f (x + p.1 • p.2)) with h | h | ⟨r, h⟩
    · rw [h] at hgy
      exact absurd (le_bot_iff.1 hgy) (EReal.coe_ne_bot _)
    · rw [h, EReal.top_sub_coe, EReal.coe_mul_top_of_pos (by positivity)]
      exact le_top
    · rw [h] at hgy ⊢
      rw [← EReal.coe_sub, ← EReal.coe_mul, EReal.coe_le_coe_iff]
      have hgy' := EReal.coe_le_coe_iff.1 hgy
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith
  calc ((2 * ε * ‖w‖ ^ 2 : ℝ) : EReal)
      = liminf (fun p : ℝ × E ↦ ((2 * ε * ‖p.2‖ ^ 2 : ℝ) : EReal)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) :=
        ((EReal.tendsto_coe.2 hnorm).liminf_eq).symm
    _ ≤ secondSubderivative f x 0 w := liminf_le_liminf hev

variable [FiniteDimensional ℝ E]

/-- The compactness step in the proof of **Theorem 13.24(c)**: if
`d²f(x̄ | 0)(w) > 0` for all `w ≠ 0`, there is quadratic growth. -/
theorem exists_growth_of_secondSubderivative_pos {f : E → EReal} {x : E} {c : ℝ}
    (hx : f x = c) (hpos : ∀ w, w ≠ 0 → 0 < secondSubderivative f x 0 w) :
    ∃ ε > 0, ∃ δ > 0, ∀ y, ‖y - x‖ ≤ δ → ((c + ε * ‖y - x‖ ^ 2 : ℝ) : EReal) ≤ f y := by
  set S : Set E := sphere (0 : E) 1
  have hS : IsCompact S := isCompact_sphere 0 1
  -- a uniform positive lower bound on the unit sphere
  obtain ⟨m, hm, hmS⟩ : ∃ m : ℝ, 0 < m ∧ ∀ w ∈ S, (m : EReal) < secondSubderivative f x 0 w := by
    rcases S.eq_empty_or_nonempty with hSe | hSne
    · exact ⟨1, one_pos, fun w hw ↦ by rw [hSe] at hw; exact absurd hw (notMem_empty w)⟩
    · obtain ⟨w₀, hw₀, hmin⟩ :=
        (lowerSemicontinuous_secondSubderivative f x 0).lowerSemicontinuousOn S
          |>.exists_isMinOn hSne hS
      have hw₀ne : w₀ ≠ 0 := by
        intro h
        rw [h] at hw₀
        simp [S] at hw₀
      obtain ⟨m, hm0, hm1⟩ := EReal.exists_between_coe_real (hpos w₀ hw₀ne)
      exact ⟨m, EReal.coe_pos.1 hm0, fun w hw ↦ hm1.trans_le (hmin hw)⟩
  have hev : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝ˢ S, (m : EReal) < secondDifferenceQuotient f x 0 p.1 p.2 :=
    hS.mem_prod_nhdsSet_of_forall fun w hw ↦ eventually_lt_of_lt_liminf (hmS w hw)
  have hU : ∀ᶠ τ in 𝓝[>] (0 : ℝ), ∀ w ∈ S, (m : EReal) < secondDifferenceQuotient f x 0 τ w := by
    filter_upwards [hev.curry] with τ hτ w hw
    exact hτ.self_of_nhdsSet w hw
  obtain ⟨δ, hδ, hδU⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hU
  refine ⟨m / 2, half_pos hm, δ / 2, half_pos hδ, fun y hy ↦ ?_⟩
  rcases eq_or_ne y x with rfl | hyx
  · rw [hx, sub_self, norm_zero]
    simp
  · have hτ : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hyx)
    set τ := ‖y - x‖ with hτdef
    set z : E := τ⁻¹ • (y - x) with hzdef
    have hz : z ∈ S := by
      simp only [S, mem_sphere_zero_iff_norm, hzdef, norm_smul, Real.norm_of_nonneg
        (inv_nonneg.2 hτ.le), ← hτdef, inv_mul_cancel₀ hτ.ne']
    have hτz : x + τ • z = y := by
      rw [hzdef, smul_smul, mul_inv_cancel₀ hτ.ne', one_smul, add_sub_cancel]
    have hmem := hδU ⟨hτ, by linarith⟩ z hz
    rw [secondDifferenceQuotient_zero_vec hx, hτz] at hmem
    rcases ereal_trichotomy (f y) with h | h | ⟨r, h⟩
    · rw [h, EReal.bot_sub, EReal.coe_mul_bot_of_pos (by positivity)] at hmem
      exact absurd hmem not_lt_bot
    · rw [h]
      exact le_top
    · rw [h] at hmem ⊢
      rw [← EReal.coe_sub, ← EReal.coe_mul, EReal.coe_lt_coe_iff] at hmem
      rw [EReal.coe_le_coe_iff]
      rw [div_mul_eq_mul_div, lt_div_iff₀ (by positivity)] at hmem
      nlinarith

/-- **Theorem 13.24(c)**: `0 ∈ ∂̂f(x̄)` with `d²f(x̄ | 0)(w) > 0` for all `w ≠ 0` is
equivalent to quadratic growth: `f(x) ≥ f(x̄) + ε‖x - x̄‖²` when `‖x - x̄‖ ≤ δ`, for
some `ε > 0` and `δ > 0`. -/
theorem secondOrder_growth_iff {f : E → EReal} {x : E} {c : ℝ} (hx : f x = c) :
    ((0 : E) ∈ regularSubdifferential f x ∧ ∀ w, w ≠ 0 → 0 < secondSubderivative f x 0 w) ↔
      ∃ ε > 0, ∃ δ > 0, ∀ y, ‖y - x‖ ≤ δ → ((c + ε * ‖y - x‖ ^ 2 : ℝ) : EReal) ≤ f y := by
  constructor
  · rintro ⟨-, hpos⟩
    exact exists_growth_of_secondSubderivative_pos hx hpos
  · rintro ⟨ε, hε, δ, hδ, hg⟩
    have hmin : IsLocalMin f x := by
      filter_upwards [closedBall_mem_nhds x hδ] with y hy
      rw [mem_closedBall, dist_eq_norm] at hy
      rw [hx]
      exact (EReal.coe_le_coe_iff.2 (le_add_of_nonneg_right (by positivity))).trans (hg y hy)
    refine ⟨RW.IsLocalMin.zero_mem_regularSubdifferential hmin hx, fun w hw ↦ ?_⟩
    refine lt_of_lt_of_le ?_ (secondSubderivative_zero_ge_of_growth hx hδ hg w)
    exact EReal.coe_pos.2 (by have := norm_pos_iff.2 hw; positivity)

/-- **Theorem 13.24(c)** with the limiting subdifferential: since quadratic growth
gives `0 ∈ ∂̂f(x̄) ⊂ ∂f(x̄)`, the equivalence also holds with `0 ∈ ∂f(x̄)`. -/
theorem secondOrder_growth_iff' {f : E → EReal} {x : E} {c : ℝ} (hx : f x = c) :
    ((0 : E) ∈ subdifferential f x ∧ ∀ w, w ≠ 0 → 0 < secondSubderivative f x 0 w) ↔
      ∃ ε > 0, ∃ δ > 0, ∀ y, ‖y - x‖ ≤ δ → ((c + ε * ‖y - x‖ ^ 2 : ℝ) : EReal) ≤ f y := by
  constructor
  · rintro ⟨-, hpos⟩
    exact exists_growth_of_secondSubderivative_pos hx hpos
  · intro h
    obtain ⟨h0, hpos⟩ := (secondOrder_growth_iff hx).2 h
    exact ⟨regularSubdifferential_subset_subdifferential f x h0, hpos⟩

/-- **Theorem 13.24(b)**: if `d²f(x̄ | 0)(w) > 0` for all `w ≠ 0` (in the book together
with `0 ∈ ∂̂f(x̄)`, which is not needed), then `x̄` is locally optimal. -/
theorem isLocalMin_of_secondSubderivative_pos {f : E → EReal} {x : E} {c : ℝ} (hx : f x = c)
    (hpos : ∀ w, w ≠ 0 → 0 < secondSubderivative f x 0 w) : IsLocalMin f x := by
  obtain ⟨ε, hε, δ, hδ, hg⟩ := exists_growth_of_secondSubderivative_pos hx hpos
  filter_upwards [closedBall_mem_nhds x hδ] with y hy
  rw [mem_closedBall, dist_eq_norm] at hy
  rw [hx]
  exact (EReal.coe_le_coe_iff.2 (le_add_of_nonneg_right (by positivity))).trans (hg y hy)

/-- **Theorem 13.24**, all three parts.  Part (a) gives `0 ∈ ∂̂f(x̄) ⊂ ∂f(x̄)`, part (b)
needs no first-order hypothesis, and part (c) holds with either subdifferential. -/
theorem second_order_conditions_for_optimality {f : E → EReal} {x : E} {c : ℝ} (hx : f x = c) :
    (IsLocalMin f x →
      (0 : E) ∈ regularSubdifferential f x ∧ (0 : E) ∈ subdifferential f x ∧
        ∀ w, 0 ≤ secondSubderivative f x 0 w) ∧
    ((∀ w, w ≠ 0 → 0 < secondSubderivative f x 0 w) → IsLocalMin f x) ∧
    (((0 : E) ∈ regularSubdifferential f x ∧ ∀ w, w ≠ 0 → 0 < secondSubderivative f x 0 w) ↔
      ∃ ε > 0, ∃ δ > 0, ∀ y, ‖y - x‖ ≤ δ → ((c + ε * ‖y - x‖ ^ 2 : ℝ) : EReal) ≤ f y) ∧
    (((0 : E) ∈ subdifferential f x ∧ ∀ w, w ≠ 0 → 0 < secondSubderivative f x 0 w) ↔
      ∃ ε > 0, ∃ δ > 0, ∀ y, ‖y - x‖ ≤ δ → ((c + ε * ‖y - x‖ ^ 2 : ℝ) : EReal) ≤ f y) := by
  refine ⟨fun hm ↦ ?_, isLocalMin_of_secondSubderivative_pos hx, secondOrder_growth_iff hx,
    secondOrder_growth_iff' hx⟩
  obtain ⟨h0, h2⟩ := RW.IsLocalMin.secondOrder_necessary hm hx
  exact ⟨h0, regularSubdifferential_subset_subdifferential f x h0, h2⟩

end RW
