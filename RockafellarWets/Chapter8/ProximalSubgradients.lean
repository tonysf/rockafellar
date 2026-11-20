/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Proximal subgradients

Definition 8.45 and parts (b), (c) (necessity) and (e) of Proposition 8.46.

* `proximalSubdifferential f x̄` is the set of proximal subgradients 8(30).
* 8.46(b): for the indicator of a set the proximal subgradients are exactly
  the proximal normals; the local quadratic support near `x̄` extends to a
  global one as in the book's proof, the linear term being dominated by a
  quadratic one away from `x̄`.
* 8.46(c), necessity: a proximal subgradient is the gradient at `x̄` of the
  smooth quadratic minorant from 8(30).
* 8.46(e): the proximal subgradients form a convex subset of `∂̂f(x̄)`.
-/

import RockafellarWets.Chapter8.SubderivativeFormulas
import RockafellarWets.Chapter6.ProximalNormals
import Mathlib.Analysis.InnerProductSpace.Calculus

open Filter Set Topology Metric
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Definition 8.45**, formula 8(30): `v` is a proximal subgradient of `f` at
`x̄`, a point where `f(x̄)` is finite, if for some `ρ > 0` and `δ > 0`,
`f(x) ≥ f(x̄) + ⟪v, x - x̄⟫ - (ρ/2)|x - x̄|²` whenever `|x - x̄| ≤ δ`. -/
def proximalSubdifferential (f : E → EReal) (x : E) : Set E :=
  {v | ∃ c : ℝ, f x = c ∧ ∃ ρ > 0, ∃ δ > 0, ∀ y, ‖y - x‖ ≤ δ →
    ((c + ⟪v, y - x⟫_ℝ - ρ / 2 * ‖y - x‖ ^ 2 : ℝ) : EReal) ≤ f y}

/-! ### Proposition 8.46(e) -/

/-- **Proposition 8.46(e)**: every proximal subgradient is a regular
subgradient. -/
theorem proximalSubdifferential_subset_regularSubdifferential (f : E → EReal) (x : E) :
    proximalSubdifferential f x ⊆ regularSubdifferential f x := by
  rintro v ⟨c, hxc, ρ, hρ, δ, hδ, hle⟩
  refine ⟨c, hxc, fun ε hε ↦ ?_⟩
  have hr : 0 < min δ (2 * ε / ρ) := lt_min hδ (by positivity)
  filter_upwards [ball_mem_nhds x hr] with y hy
  rw [mem_ball, dist_eq_norm, lt_min_iff] at hy
  refine le_trans (EReal.coe_le_coe_iff.2 ?_) (hle y hy.1.le)
  have h1 : ρ / 2 * ‖y - x‖ ^ 2 ≤ ε * ‖y - x‖ := by
    have hn := norm_nonneg (y - x)
    have h2 : ρ * ‖y - x‖ ≤ 2 * ε := by
      have := hy.2
      rw [lt_div_iff₀ hρ] at this
      linarith
    nlinarith
  linarith

/-- **Proposition 8.46(e)**: the proximal subgradients form a convex set. -/
theorem convex_proximalSubdifferential (f : E → EReal) (x : E) :
    Convex ℝ (proximalSubdifferential f x) := by
  rintro v₁ ⟨c, hxc, ρ₁, hρ₁, δ₁, hδ₁, h₁⟩ v₂ ⟨c', hxc', ρ₂, hρ₂, δ₂, hδ₂, h₂⟩ a b ha hb hab
  have hcc : c' = c := by
    rw [hxc] at hxc'
    exact (EReal.coe_injective hxc').symm
  subst hcc
  refine ⟨c', hxc, max ρ₁ ρ₂, lt_max_of_lt_left hρ₁, min δ₁ δ₂, lt_min hδ₁ hδ₂, fun y hy ↦ ?_⟩
  have hy₁ := h₁ y (hy.trans (min_le_left _ _))
  have hy₂ := h₂ y (hy.trans (min_le_right _ _))
  by_cases htop : f y = ⊤
  · rw [htop]
    exact le_top
  have hbot : f y ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hy₁
  have hfy : f y = (((f y).toReal : ℝ) : EReal) := (EReal.coe_toReal htop hbot).symm
  rw [hfy, EReal.coe_le_coe_iff] at hy₁ hy₂ ⊢
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have hq : 0 ≤ ‖y - x‖ ^ 2 := by positivity
  have hm₁ : ρ₁ / 2 * ‖y - x‖ ^ 2 ≤ max ρ₁ ρ₂ / 2 * ‖y - x‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith [le_max_left ρ₁ ρ₂]) hq
  have hm₂ : ρ₂ / 2 * ‖y - x‖ ^ 2 ≤ max ρ₁ ρ₂ / 2 * ‖y - x‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith [le_max_right ρ₁ ρ₂]) hq
  have k₁ : c' + ⟪v₁, y - x⟫_ℝ - max ρ₁ ρ₂ / 2 * ‖y - x‖ ^ 2 ≤ (f y).toReal := by linarith
  have k₂ : c' + ⟪v₂, y - x⟫_ℝ - max ρ₁ ρ₂ / 2 * ‖y - x‖ ^ 2 ≤ (f y).toReal := by linarith
  have e1 := mul_le_mul_of_nonneg_left k₁ ha
  have e2 := mul_le_mul_of_nonneg_left k₂ hb
  have hb' : b = 1 - a := by linarith
  subst hb'
  linarith [e1, e2]

/-! ### Proposition 8.46(b) -/

/-- **Proposition 8.46(b)**: `v` is a proximal subgradient of `δ_C` at `x̄` if
and only if `v` is a proximal normal to `C` at `x̄`. -/
theorem mem_proximalSubdifferential_indicatorVA_iff {C : Set E} {x v : E} :
    v ∈ proximalSubdifferential (indicatorVA C) x ↔ v ∈ proximalNormalCone C x := by
  rw [mem_proximalNormalCone_iff_quadratic_support]
  constructor
  · rintro ⟨c, hxc, ρ, hρ, δ, hδ, hle⟩
    have hxC : x ∈ C := by
      by_contra hx
      rw [indicatorVA_apply_not_mem hx] at hxc
      exact EReal.coe_ne_top c hxc.symm
    have hc : c = 0 := by
      rw [indicatorVA_apply_mem hxC] at hxc
      exact_mod_cast hxc.symm
    subst hc
    refine ⟨hxC, max (ρ / 2) (‖v‖ / δ), lt_max_of_lt_left (by positivity), fun y hy ↦ ?_⟩
    have hq : 0 ≤ ‖y - x‖ ^ 2 := by positivity
    rcases le_or_gt ‖y - x‖ δ with hyδ | hyδ
    · have h := hle y hyδ
      rw [indicatorVA_apply_mem hy, ← EReal.coe_zero, EReal.coe_le_coe_iff] at h
      have : ρ / 2 * ‖y - x‖ ^ 2 ≤ max (ρ / 2) (‖v‖ / δ) * ‖y - x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hq
      linarith
    · have h1 : ⟪v, y - x⟫_ℝ ≤ ‖v‖ * ‖y - x‖ := real_inner_le_norm v (y - x)
      have h2 : ‖v‖ * ‖y - x‖ ≤ ‖v‖ / δ * ‖y - x‖ ^ 2 := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hδ, pow_two]
        have hv := norm_nonneg v
        have hn := norm_nonneg (y - x)
        nlinarith [mul_nonneg (mul_nonneg hv hn) (sub_nonneg.2 hyδ.le)]
      have h3 : ‖v‖ / δ * ‖y - x‖ ^ 2 ≤ max (ρ / 2) (‖v‖ / δ) * ‖y - x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hq
      linarith
  · rintro ⟨hxC, ε, hε, hquad⟩
    refine ⟨0, by rw [indicatorVA_apply_mem hxC, EReal.coe_zero], 2 * ε, by positivity, 1,
      one_pos, fun y _ ↦ ?_⟩
    by_cases hy : y ∈ C
    · rw [indicatorVA_apply_mem hy, ← EReal.coe_zero, EReal.coe_le_coe_iff]
      have := hquad y hy
      linarith
    · rw [indicatorVA_apply_not_mem hy]
      exact le_top

/-! ### Proposition 8.46(c), necessity -/

/-- **Proposition 8.46(c)**, necessity: a proximal subgradient is the gradient
at `x̄` of a smooth (indeed quadratic) function `h ≤ f` near `x̄` with
`h(x̄) = f(x̄)`. -/
theorem exists_contDiff_minorant_of_mem_proximalSubdifferential [CompleteSpace E]
    {f : E → EReal} {x v : E} (hv : v ∈ proximalSubdifferential f x) :
    ∃ c : ℝ, f x = c ∧ ∃ h : E → ℝ, ContDiff ℝ 2 h ∧ (∀ᶠ y in 𝓝 x, (h y : EReal) ≤ f y) ∧
      h x = c ∧ HasGradientAt h v x := by
  obtain ⟨c, hxc, ρ, hρ, δ, hδ, hle⟩ := hv
  refine ⟨c, hxc, fun y ↦ c + ⟪v, y - x⟫_ℝ - ρ / 2 * ‖y - x‖ ^ 2, ?_, ?_, by simp, ?_⟩
  · have hlin : ContDiff ℝ 2 (fun y : E ↦ ⟪v, y - x⟫_ℝ) :=
      ContDiff.inner ℝ contDiff_const (contDiff_id.sub contDiff_const)
    have hsq : ContDiff ℝ 2 (fun y : E ↦ ‖y - x‖ ^ 2) :=
      ContDiff.norm_sq ℝ (contDiff_id.sub contDiff_const)
    exact (contDiff_const.add hlin).sub (contDiff_const.mul hsq)
  · filter_upwards [closedBall_mem_nhds x hδ] with y hy
    exact hle y (by rwa [mem_closedBall, dist_eq_norm] at hy)
  · rw [hasGradientAt_iff_hasFDerivAt]
    have h1 : HasFDerivAt (fun y : E ↦ ⟪v, y - x⟫_ℝ) (InnerProductSpace.toDual ℝ E v) x := by
      have := ((InnerProductSpace.toDual ℝ E v).hasFDerivAt (x := x)).sub_const
        (InnerProductSpace.toDual ℝ E v x)
      refine this.congr_of_eventuallyEq (Eventually.of_forall fun y ↦ ?_)
      simp [InnerProductSpace.toDual_apply_apply, inner_sub_right]
    have h2 : HasFDerivAt (fun y : E ↦ ‖y - x‖ ^ 2) (0 : E →L[ℝ] ℝ) x := by
      have := HasFDerivAt.norm_sq ((hasFDerivAt_id x).sub_const x)
      simpa using this
    have := ((hasFDerivAt_const c x).add h1).sub (h2.const_mul (ρ / 2))
    simpa using this

end RW
