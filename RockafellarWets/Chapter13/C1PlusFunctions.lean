/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Functions with strictly continuous gradient

Proposition 13.34.  A function is of class `C¹⁺` on an open set `O` (differentiable with `∇f`
strictly continuous) if and only if it is both lower-`C²` and upper-`C²` on `O`; such functions are
prox-regular and subdifferentially continuous on `O`.

For `⇒`, a locally Lipschitz gradient gives the quadratic minorants
`f(z) ≥ f(y) + ⟪∇f(y), z - y⟫ - L‖z - y‖²` (as in 13.35), so `f` and `-f` are lower-`C²`.  For `⇐`,
`f` is `C¹` by 10.30, and the local convexity of `f + ρ‖·‖²` and `-f + ρ‖·‖²` (10.33) yields the
two-sided bound `|f(z) - f(y) - ⟪∇f(y), z - y⟫| ≤ ρ‖z - y‖²`.  Evaluating it at the three points
`y₂`, `y₁` and `z = y₁ + ‖y₁ - y₂‖ d/‖d‖` with `d = ∇f(y₁) - ∇f(y₂)` gives
`‖d‖ ≤ 6ρ‖y₁ - y₂‖`.  This replaces the conjugate-function argument of the printed proof.
-/

import RockafellarWets.Chapter13.LowerC2ProxRegularity
import RockafellarWets.Chapter13.ProxRegularPerturbations
import RockafellarWets.Chapter2.Operations

open Filter Set Topology Metric
open scoped InnerProductSpace NNReal

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- `f` is of class `C¹⁺` on `O`: it is differentiable at every point of `O` and `∇f` is strictly
continuous at every point of `O`. -/
def IsC1PlusOn (f : E → ℝ) (O : Set E) : Prop :=
  ∀ x ∈ O, DifferentiableAt ℝ f x ∧ StrictlyContinuousAt (gradient f) x

/-- The negative of a `C¹⁺` function is `C¹⁺`. -/
theorem IsC1PlusOn.neg {f : E → ℝ} {O : Set E} (hO : IsOpen O) (hf : IsC1PlusOn f O) :
    IsC1PlusOn (fun y ↦ -f y) O := by
  have hg : ∀ y ∈ O, gradient (fun y ↦ -f y) y = -gradient f y := fun y hy ↦ by
    apply HasGradientAt.gradient
    rw [hasGradientAt_iff_hasFDerivAt, map_neg]
    exact (hf y hy).1.hasGradientAt.hasFDerivAt.neg
  intro x hx
  refine ⟨(hf x hx).1.neg, ?_⟩
  obtain ⟨k, V, hV, hlip⟩ := strictlyContinuousAt_iff.1 (hf x hx).2
  refine strictlyContinuousAt_iff.2 ⟨k, V ∩ O, inter_mem hV (hO.mem_nhds hx), fun y hy z hz ↦ ?_⟩
  rw [hg y hy.2, hg z hz.2, edist_neg_neg]
  exact hlip hy.1 hz.1

/-- **Proposition 13.34** (`⇒`, lower part): a `C¹⁺` function is lower-`C²`. -/
theorem IsC1PlusOn.isLowerCOn_two {f : E → ℝ} {O : Set E} (hO : IsOpen O) (hf : IsC1PlusOn f O) :
    IsLowerCOn 2 f O := by
  refine isLowerCOn_of_local fun x hx ↦ ?_
  obtain ⟨k, V, hV, hlip⟩ := strictlyContinuousAt_iff.1 (hf x hx).2
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.1 (inter_mem hV (hO.mem_nhds hx))
  refine ⟨ball x δ, isOpen_ball, mem_ball_self hδ, fun y hy ↦ (hδsub hy).2,
    isLowerCOn_two_of_forall_quadratic_minorant isOpen_ball (convex_ball x δ) (ρ := 2 * k)
      fun y hy ↦ ⟨gradient f y, fun z hz ↦ ?_⟩⟩
  have h := quadratic_lower_bound_of_lipschitz_gradient (g := f) (G := gradient f) k.coe_nonneg
    (fun y hy ↦ (hf y (hδsub hy).2).1.hasGradientAt)
    (fun y hy z hz ↦ hlip.norm_sub_le (hδsub hy).1 (hδsub hz).1) hy hz
  linarith

/-- **Proposition 13.34** (`⇒`, upper part): a `C¹⁺` function is upper-`C²`. -/
theorem IsC1PlusOn.isUpperCOn_two {f : E → ℝ} {O : Set E} (hO : IsOpen O) (hf : IsC1PlusOn f O) :
    IsUpperCOn 2 f O :=
  (hf.neg hO).isLowerCOn_two hO

/-- First-order consequence of convexity of `g + c‖·‖²` for a differentiable `g`. -/
theorem le_of_convexOn_add_sq {g : E → ℝ} {S : Set E} (hS : IsOpen S) (hSc : Convex ℝ S) {c : ℝ}
    (hg : ∀ y ∈ S, DifferentiableAt ℝ g y) (hconv : ConvexOn ℝ S (fun y ↦ g y + c * ‖y‖ ^ 2))
    {y z : E} (hy : y ∈ S) (hz : z ∈ S) :
    g y + fderiv ℝ g y (z - y) - c * ‖z - y‖ ^ 2 ≤ g z := by
  have hd : ∀ u ∈ S, HasFDerivAt (fun y ↦ g y + c * ‖y‖ ^ 2)
      (fderiv ℝ g u + c • (2 • innerSL ℝ u)) u := fun u hu ↦
    (hg u hu).hasFDerivAt.add ((hasStrictFDerivAt_norm_sq u).hasFDerivAt.const_mul c)
  have hfo := (convexOn_iff_firstOrder hSc hS
    fun u hu ↦ (hd u hu).differentiableAt.differentiableWithinAt).1 hconv y hy z hz
  rw [(hd y hy).fderiv] at hfo
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, innerSL_apply_apply,
    smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat] at hfo
  have e1 : ‖z - y‖ ^ 2 = ‖z‖ ^ 2 - 2 * ⟪y, z⟫_ℝ + ‖y‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_comm]
  have e2 : ⟪y, z - y⟫_ℝ = ⟪y, z⟫_ℝ - ‖y‖ ^ 2 := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq]
  rw [e2] at hfo
  have e1' : c * ‖z - y‖ ^ 2 = c * (‖z‖ ^ 2 - 2 * ⟪y, z⟫_ℝ + ‖y‖ ^ 2) := by rw [e1]
  nlinarith

/-- **Proposition 13.34** (`⇐`): a function both lower-`C²` and upper-`C²` on `O` is `C¹⁺` there. -/
theorem isC1PlusOn_of_isLowerCOn_isUpperCOn {f : E → ℝ} {O : Set E} (hO : IsOpen O)
    (hl : IsLowerCOn 2 f O) (hu : IsUpperCOn 2 f O) : IsC1PlusOn f O := by
  have hC1 : ContDiffOn ℝ 1 f O :=
    (contDiffOn_one_iff_isLowerCOn_isUpperCOn hO).2 ⟨hl.mono (by norm_num), hu.mono (by norm_num)⟩
  have hdiff : ∀ y ∈ O, DifferentiableAt ℝ f y := fun y hy ↦
    (hC1.differentiableOn one_ne_zero y hy).differentiableAt (hO.mem_nhds hy)
  intro x hx
  refine ⟨hdiff x hx, ?_⟩
  obtain ⟨δ₁, hδ₁, hδ₁O, ρ₁, hρ₁, hc₁⟩ := hl.exists_convex_sub_quadratic x hx
  obtain ⟨δ₂, hδ₂, hδ₂O, ρ₂, hρ₂, hc₂⟩ := IsLowerCOn.exists_convex_sub_quadratic hu x hx
  set δ := min δ₁ δ₂
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  set ρ := max ρ₁ ρ₂
  have hρ : 0 ≤ ρ := le_max_of_le_left hρ₁
  have hB₁ : ball x δ ⊆ ball x δ₁ := ball_subset_ball (min_le_left _ _)
  have hB₂ : ball x δ ⊆ ball x δ₂ := ball_subset_ball (min_le_right _ _)
  have hdB : ∀ y ∈ ball x δ, DifferentiableAt ℝ f y := fun y hy ↦ hdiff y (hδ₁O (hB₁ hy))
  -- the two-sided quadratic bound on `𝔹(x, δ)`
  have hR : ∀ y ∈ ball x δ, ∀ z ∈ ball x δ,
      |f z - f y - ⟪gradient f y, z - y⟫_ℝ| ≤ ρ * ‖z - y‖ ^ 2 := by
    intro y hy z hz
    have h1 := le_of_convexOn_add_sq isOpen_ball (convex_ball x δ) hdB
      (hc₁.subset hB₁ (convex_ball x δ)) hy hz
    have h2 := le_of_convexOn_add_sq (g := fun y ↦ -f y) isOpen_ball (convex_ball x δ)
      (fun y hy ↦ (hdB y hy).neg) (hc₂.subset hB₂ (convex_ball x δ)) hy hz
    have hneg : fderiv ℝ (fun y ↦ -f y) y = -fderiv ℝ f y := ((hdB y hy).hasFDerivAt.neg).fderiv
    have hfg : fderiv ℝ f y (z - y) = ⟪gradient f y, z - y⟫_ℝ := by
      rw [gradient, InnerProductSpace.toDual_symm_apply]
    rw [hneg, ContinuousLinearMap.neg_apply, hfg] at h2
    rw [hfg] at h1
    simp only at h2
    have hq : 0 ≤ ‖z - y‖ ^ 2 := by positivity
    have hρ₁' : ρ₁ * ‖z - y‖ ^ 2 ≤ ρ * ‖z - y‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hq
    have hρ₂' : ρ₂ * ‖z - y‖ ^ 2 ≤ ρ * ‖z - y‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hq
    rw [abs_le]
    constructor <;> linarith
  -- the Lipschitz estimate on `𝔹(x, δ/4)`
  refine strictlyContinuousAt_iff.2 ⟨⟨6 * ρ, by positivity⟩, ball x (δ / 4),
    ball_mem_nhds x (by positivity), LipschitzOnWith.of_dist_le_mul fun y₁ hy₁ y₂ hy₂ ↦ ?_⟩
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_mk]
  set d := gradient f y₁ - gradient f y₂
  set r := ‖y₁ - y₂‖
  rcases eq_or_ne d 0 with hd0 | hd0
  · rw [hd0, norm_zero]
    positivity
  have hdn : 0 < ‖d‖ := norm_pos_iff.2 hd0
  have hy₁x : ‖y₁ - x‖ < δ / 4 := by rwa [mem_ball, dist_eq_norm] at hy₁
  have hy₂x : ‖y₂ - x‖ < δ / 4 := by rwa [mem_ball, dist_eq_norm] at hy₂
  have hr : r < δ / 2 := by
    calc r = ‖(y₁ - x) - (y₂ - x)‖ := by rw [sub_sub_sub_cancel_right]
      _ ≤ ‖y₁ - x‖ + ‖y₂ - x‖ := norm_sub_le _ _
      _ < δ / 2 := by linarith
  set z := y₁ + (r / ‖d‖) • d
  have hzy₁ : ‖z - y₁‖ = r := by
    simp only [z, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ r / ‖d‖)]
    field_simp
  have hzy₂ : ‖z - y₂‖ ≤ 2 * r := by
    calc ‖z - y₂‖ = ‖(z - y₁) + (y₁ - y₂)‖ := by congr 1; abel
      _ ≤ ‖z - y₁‖ + ‖y₁ - y₂‖ := norm_add_le _ _
      _ = 2 * r := by rw [hzy₁]; ring
  have hball1 : y₁ ∈ ball x δ := ball_subset_ball (by linarith) hy₁
  have hball2 : y₂ ∈ ball x δ := ball_subset_ball (by linarith) hy₂
  have hballz : z ∈ ball x δ := by
    rw [mem_ball, dist_eq_norm]
    calc ‖z - x‖ = ‖(z - y₁) + (y₁ - x)‖ := by congr 1; abel
      _ ≤ ‖z - y₁‖ + ‖y₁ - x‖ := norm_add_le _ _
      _ < δ := by rw [hzy₁]; linarith
  have hkey : ⟪d, z - y₁⟫_ℝ = r * ‖d‖ := by
    simp only [z, add_sub_cancel_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hident : ⟪d, z - y₁⟫_ℝ =
      (f z - f y₂ - ⟪gradient f y₂, z - y₂⟫_ℝ) - (f z - f y₁ - ⟪gradient f y₁, z - y₁⟫_ℝ) -
        (f y₁ - f y₂ - ⟪gradient f y₂, y₁ - y₂⟫_ℝ) := by
    simp only [d, inner_sub_left, inner_sub_right]
    ring
  have b1 := (abs_le.1 (hR y₂ hball2 z hballz)).2
  have b2 := (abs_le.1 (hR y₁ hball1 z hballz)).1
  have b3 := (abs_le.1 (hR y₂ hball2 y₁ hball1)).1
  have hsq : ‖z - y₂‖ ^ 2 ≤ (2 * r) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hzy₂ 2
  have hmain : r * ‖d‖ ≤ 6 * ρ * r ^ 2 := by
    rw [← hkey, hident]
    rw [hzy₁] at b2
    have : ρ * ‖z - y₂‖ ^ 2 ≤ ρ * (2 * r) ^ 2 := mul_le_mul_of_nonneg_left hsq hρ
    nlinarith
  have hrpos : 0 < r := by
    rcases (norm_nonneg (y₁ - y₂)).eq_or_lt with h0 | h0
    · exfalso
      have hy : y₁ = y₂ := sub_eq_zero.1 (norm_eq_zero.1 h0.symm)
      exact hd0 (by simp [d, hy])
    · exact h0
  nlinarith

/-- **Proposition 13.34** (functions with strictly continuous gradient). -/
theorem functions_with_strictly_continuous_gradient {f : E → ℝ} {O : Set E} (hO : IsOpen O) :
    (IsC1PlusOn f O ↔ IsLowerCOn 2 f O ∧ IsUpperCOn 2 f O) ∧
    (IsC1PlusOn f O → ∀ x ∈ O, IsProxRegularAtPoint (fun y ↦ (f y : EReal)) x ∧
      IsSubdifferentiallyContinuousAtPoint (fun y ↦ (f y : EReal)) x) := by
  refine ⟨⟨fun hf ↦ ⟨hf.isLowerCOn_two hO, hf.isUpperCOn_two hO⟩,
    fun h ↦ isC1PlusOn_of_isLowerCOn_isUpperCOn hO h.1 h.2⟩, fun hf x hx ↦ ?_⟩
  have hlow : IsLowerCOn 2 (fun y ↦ ((f y : EReal)).toReal) O :=
    (hf.isLowerCOn_two hO).congr fun y _ ↦ (EReal.toReal_coe _).symm
  obtain ⟨h1, h2, -⟩ := isProxRegular_of_isLowerCOn_two hO
    (fun y _ ↦ ⟨EReal.coe_ne_bot _, EReal.coe_ne_top _⟩) hlow hx
  exact ⟨h1, h2⟩

end RW
