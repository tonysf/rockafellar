/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 2C: Derivative tests for convexity

This file formalizes Section C of Chapter 2 of Rockafellar–Wets.

* Lemma 2.12: the slope inequality 2(7) and monotone difference quotients.
* Theorem 2.13: the one-dimensional derivative tests on an open interval.
* Theorem 2.14: the higher-dimensional tests with gradients and Hessians.
* Example 2.15: quadratic (linear-quadratic) functions.

The gradient condition `⟨∇f(x), y - x⟩` is written with the Fréchet
derivative `fderiv ℝ f x (y - x)`, and the Hessian quadratic form
`⟨z, ∇²f(x) z⟩` with the second Fréchet derivative
`fderiv ℝ (fderiv ℝ f) x z z`.
-/

import RockafellarWets.Chapter2.ConvexFunctions
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Calculus

open Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RW

/-! ## Lemma 2.12 -/

section Slope

variable {C : Set ℝ} {f : ℝ → ℝ}

theorem mem_of_mem_of_lt_of_lt (hC : Convex ℝ C) {x₀ x₁ y : ℝ} (h₀ : x₀ ∈ C) (h₁ : x₁ ∈ C)
    (hy₀ : x₀ < y) (hy₁ : y < x₁) : y ∈ C :=
  hC.segment_subset h₀ h₁ (by rw [segment_eq_Icc (hy₀.trans hy₁).le]; exact ⟨hy₀.le, hy₁.le⟩)

theorem slope_symm_div (f : ℝ → ℝ) (a b : ℝ) : (f a - f b) / (a - b) = (f b - f a) / (b - a) := by
  rw [← neg_sub (f b), ← neg_sub b, neg_div_neg_eq]

/-- **Lemma 2.12 (slope inequality)**: a real-valued function on an interval
`C` is convex if and only if the three difference quotients 2(7) are ordered
for all `x₀ < y < x₁` in `C`. -/
theorem convexOn_iff_slope_inequality (hC : Convex ℝ C) :
    ConvexOn ℝ C f ↔ ∀ ⦃x₀⦄, x₀ ∈ C → ∀ ⦃x₁⦄, x₁ ∈ C → ∀ ⦃y⦄, x₀ < y → y < x₁ →
      (f y - f x₀) / (y - x₀) ≤ (f x₁ - f x₀) / (x₁ - x₀) ∧
        (f x₁ - f x₀) / (x₁ - x₀) ≤ (f x₁ - f y) / (x₁ - y) := by
  constructor
  · intro hf x₀ h₀ x₁ h₁ y hy₀ hy₁
    have hy := mem_of_mem_of_lt_of_lt hC h₀ h₁ hy₀ hy₁
    refine ⟨hf.secant_mono h₀ hy h₁ hy₀.ne' (hy₀.trans hy₁).ne' hy₁.le, ?_⟩
    have h := hf.secant_mono h₁ h₀ hy (hy₀.trans hy₁).ne hy₁.ne hy₀.le
    rwa [slope_symm_div f x₀ x₁, slope_symm_div f y x₁] at h
  · intro h
    rw [convexOn_iff_slope_mono_adjacent]
    exact ⟨hC, fun x y z hx hz hxy hyz ↦ (h hx hz hxy hyz).1.trans (h hx hz hxy hyz).2⟩

/-- **Lemma 2.12**, strict form: strict convexity is characterized by strict
inequalities between the difference quotients. -/
theorem strictConvexOn_iff_slope_inequality (hC : Convex ℝ C) :
    StrictConvexOn ℝ C f ↔ ∀ ⦃x₀⦄, x₀ ∈ C → ∀ ⦃x₁⦄, x₁ ∈ C → ∀ ⦃y⦄, x₀ < y → y < x₁ →
      (f y - f x₀) / (y - x₀) < (f x₁ - f x₀) / (x₁ - x₀) ∧
        (f x₁ - f x₀) / (x₁ - x₀) < (f x₁ - f y) / (x₁ - y) := by
  constructor
  · intro hf x₀ h₀ x₁ h₁ y hy₀ hy₁
    have hy := mem_of_mem_of_lt_of_lt hC h₀ h₁ hy₀ hy₁
    refine ⟨hf.secant_strict_mono h₀ hy h₁ hy₀.ne' (hy₀.trans hy₁).ne' hy₁, ?_⟩
    have h := hf.secant_strict_mono h₁ h₀ hy (hy₀.trans hy₁).ne hy₁.ne hy₀
    rwa [slope_symm_div f x₀ x₁, slope_symm_div f y x₁] at h
  · intro h
    rw [strictConvexOn_iff_slope_strict_mono_adjacent]
    exact ⟨hC, fun x y z hx hz hxy hyz ↦ (h hx hz hxy hyz).1.trans (h hx hz hxy hyz).2⟩

/-- **Lemma 2.12**: for convex `f`, the difference quotient
`Δₓ(y) = (f y - f x)/(y - x)` is nondecreasing on `C \ {x}`. -/
theorem ConvexOn.monotoneOn_differenceQuotient (hf : ConvexOn ℝ C f) {x : ℝ} (hx : x ∈ C) :
    MonotoneOn (fun y ↦ (f y - f x) / (y - x)) (C \ {x}) :=
  fun _ hy₀ _ hy₁ hle ↦ hf.secant_mono hx hy₀.1 hy₁.1 hy₀.2 hy₁.2 hle

/-- **Lemma 2.12**: for strictly convex `f`, the difference quotient is
increasing on `C \ {x}`. -/
theorem StrictConvexOn.strictMonoOn_differenceQuotient (hf : StrictConvexOn ℝ C f) {x : ℝ}
    (hx : x ∈ C) : StrictMonoOn (fun y ↦ (f y - f x) / (y - x)) (C \ {x}) :=
  fun _ hy₀ _ hy₁ hlt ↦ hf.secant_strict_mono hx hy₀.1 hy₁.1 hy₀.2 hy₁.2 hlt

end Slope

/-! ## Theorem 2.13 -/

section OneDimensional

variable {O : Set ℝ} {f : ℝ → ℝ}

theorem differentiableAt_of_differentiableOn_isOpen (hO : IsOpen O)
    (hf : DifferentiableOn ℝ f O) {x : ℝ} (hx : x ∈ O) : DifferentiableAt ℝ f x :=
  hf.differentiableAt (hO.mem_nhds hx)

/-- **Theorem 2.13(a)**: a differentiable function on an open interval is convex
if and only if its derivative is nondecreasing. -/
theorem convexOn_iff_monotoneOn_deriv (hO : IsOpen O) (hOc : Convex ℝ O)
    (hf : DifferentiableOn ℝ f O) : ConvexOn ℝ O f ↔ MonotoneOn (deriv f) O := by
  constructor
  · exact fun h ↦ h.monotoneOn_deriv fun x hx ↦ differentiableAt_of_differentiableOn_isOpen hO hf hx
  · intro h
    exact MonotoneOn.convexOn_of_deriv hOc hf.continuousOn (by rwa [hO.interior_eq])
      (by rwa [hO.interior_eq])

/-- **Theorem 2.13(b)**: a differentiable function on an open interval is convex
if and only if `f(y) ≥ f(x) + f'(x)(y - x)` for all `x, y` in the interval. -/
theorem convexOn_iff_tangent_le (hO : IsOpen O) (hOc : Convex ℝ O)
    (hf : DifferentiableOn ℝ f O) :
    ConvexOn ℝ O f ↔ ∀ x ∈ O, ∀ y ∈ O, f x + deriv f x * (y - x) ≤ f y := by
  constructor
  · intro hconv x hx y hy
    rcases lt_trichotomy x y with hxy | rfl | hxy
    · have h := hconv.deriv_le_slope hx hy hxy
        (differentiableAt_of_differentiableOn_isOpen hO hf hx)
      rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hxy)] at h
      linarith
    · simp
    · have h := hconv.slope_le_deriv hy hx hxy
        (differentiableAt_of_differentiableOn_isOpen hO hf hx)
      rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hxy)] at h
      linarith
  · intro h
    refine ⟨hOc, fun x hx y hy a b ha hb hab ↦ ?_⟩
    set z := a • x + b • y with hz
    have hzO : z ∈ O := hOc hx hy ha hb hab
    have h1 := h z hzO x hx
    have h2 := h z hzO y hy
    simp only [smul_eq_mul] at hz ⊢
    have hza : a * (x - z) + b * (y - z) = 0 := by
      rw [hz]
      have : b = 1 - a := by linarith
      subst this
      ring
    have e1 := mul_le_mul_of_nonneg_left h1 ha
    have e2 := mul_le_mul_of_nonneg_left h2 hb
    have e3 : a * (f z + deriv f z * (x - z)) + b * (f z + deriv f z * (y - z)) = f z := by
      have : a * (f z + deriv f z * (x - z)) + b * (f z + deriv f z * (y - z)) =
          (a + b) * f z + deriv f z * (a * (x - z) + b * (y - z)) := by ring
      rw [this, hab, hza]
      ring
    linarith

/-- **Theorem 2.13(c)**: a twice differentiable function on an open interval is
convex if and only if `f''(x) ≥ 0` throughout. -/
theorem convexOn_iff_deriv2_nonneg_of_isOpen (hO : IsOpen O) (hOc : Convex ℝ O)
    (hf : DifferentiableOn ℝ f O) (hf2 : DifferentiableOn ℝ (deriv f) O) :
    ConvexOn ℝ O f ↔ ∀ x ∈ O, 0 ≤ deriv^[2] f x := by
  constructor
  · intro hconv x hx
    have hmono := (convexOn_iff_monotoneOn_deriv hO hOc hf).mp hconv
    have h := hmono.derivWithin_nonneg (x := x)
    rwa [derivWithin_of_isOpen hO hx] at h
  · intro h
    exact convexOn_of_deriv2_nonneg hOc hf.continuousOn (by rwa [hO.interior_eq])
      (by rwa [hO.interior_eq]) (by rwa [hO.interior_eq])

/-- **Theorem 2.13(a')**: a differentiable function on an open interval is
strictly convex if and only if its derivative is increasing. -/
theorem strictConvexOn_iff_strictMonoOn_deriv (hO : IsOpen O) (hOc : Convex ℝ O)
    (hf : DifferentiableOn ℝ f O) : StrictConvexOn ℝ O f ↔ StrictMonoOn (deriv f) O := by
  constructor
  · exact fun h ↦ h.strictMonoOn_deriv fun x hx ↦
      differentiableAt_of_differentiableOn_isOpen hO hf hx
  · intro h
    exact StrictMonoOn.strictConvexOn_of_deriv hOc hf.continuousOn (by rwa [hO.interior_eq])

/-- **Theorem 2.13(b')**: a differentiable function on an open interval is
strictly convex if and only if `f(y) > f(x) + f'(x)(y - x)` for `y ≠ x`. -/
theorem strictConvexOn_iff_tangent_lt (hO : IsOpen O) (hOc : Convex ℝ O)
    (hf : DifferentiableOn ℝ f O) :
    StrictConvexOn ℝ O f ↔ ∀ x ∈ O, ∀ y ∈ O, y ≠ x → f x + deriv f x * (y - x) < f y := by
  constructor
  · intro hs x hx y hy hyx
    have htan := (convexOn_iff_tangent_le hO hOc hf).mp hs.convexOn
    set m := (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y with hm
    have hmO : m ∈ O := hOc hx hy (by norm_num) (by norm_num) (by norm_num)
    have hlt := hs.2 hx hy hyx.symm (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num)
    have hle := htan x hx m hmO
    simp only [smul_eq_mul] at hm hlt
    rw [← hm] at hlt
    have hmx : m - x = (y - x) / 2 := by rw [hm]; ring
    rw [hmx] at hle
    linarith
  · intro h
    refine ⟨hOc, fun x hx y hy hxy a b ha hb hab ↦ ?_⟩
    set z := a • x + b • y with hz
    have hzO : z ∈ O := hOc hx hy ha.le hb.le hab
    have hb' : b = 1 - a := by linarith
    have hzx : x ≠ z := by
      intro hzx
      apply hxy
      simp only [smul_eq_mul] at hz
      have : b * (y - x) = 0 := by rw [hb'] at hz ⊢; nlinarith
      rcases mul_eq_zero.mp this with h0 | h0
      · linarith
      · linarith
    have hzy : y ≠ z := by
      intro hzy
      apply hxy
      simp only [smul_eq_mul] at hz
      have : a * (y - x) = 0 := by rw [hb'] at hz; nlinarith
      rcases mul_eq_zero.mp this with h0 | h0
      · linarith
      · linarith
    have h1 := h z hzO x hx hzx
    have h2 := h z hzO y hy hzy
    simp only [smul_eq_mul] at hz ⊢
    have hza : a * (x - z) + b * (y - z) = 0 := by
      rw [hz, hb']
      ring
    have e1 := mul_lt_mul_of_pos_left h1 ha
    have e2 := mul_lt_mul_of_pos_left h2 hb
    have e3 : a * (f z + deriv f z * (x - z)) + b * (f z + deriv f z * (y - z)) = f z := by
      have : a * (f z + deriv f z * (x - z)) + b * (f z + deriv f z * (y - z)) =
          (a + b) * f z + deriv f z * (a * (x - z) + b * (y - z)) := by ring
      rw [this, hab, hza]
      ring
    linarith

/-- **Theorem 2.13(c')**: `f''(x) > 0` on an open interval is sufficient for
strict convexity. -/
theorem strictConvexOn_of_deriv2_pos_of_isOpen (hO : IsOpen O) (hOc : Convex ℝ O)
    (hf : ContinuousOn f O) (h : ∀ x ∈ O, 0 < deriv^[2] f x) : StrictConvexOn ℝ O f :=
  strictConvexOn_of_deriv2_pos hOc hf (by rwa [hO.interior_eq])

/-- **Theorem 2.13(c')** is not necessary: `x ↦ x⁴` is strictly convex on `ℝ`
although its second derivative vanishes at `0`. -/
theorem strictConvexOn_pow_four_and_deriv2_zero :
    StrictConvexOn ℝ univ (fun x : ℝ ↦ x ^ 4) ∧ deriv^[2] (fun x : ℝ ↦ x ^ 4) 0 = 0 := by
  refine ⟨Even.strictConvexOn_pow (by decide) (by decide), ?_⟩
  simp

end OneDimensional

/-! ## Theorem 2.14 -/

section HigherDimensional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {O : Set E} {f : E → ℝ}

theorem line_combo (x z : E) {s t a b : ℝ} (hab : a + b = 1) :
    x + (a • s + b • t) • z = a • (x + s • z) + b • (x + t • z) := by
  simp only [smul_eq_mul]
  calc x + (a * s + b * t) • z = (a + b) • x + (a * s + b * t) • z := by rw [hab, one_smul]
    _ = a • (x + s • z) + b • (x + t • z) := by module

theorem isOpen_lineSet (hO : IsOpen O) (x z : E) : IsOpen {t : ℝ | x + t • z ∈ O} :=
  hO.preimage (by fun_prop)

theorem convex_lineSet (hOc : Convex ℝ O) (x z : E) : Convex ℝ {t : ℝ | x + t • z ∈ O} := by
  intro s hs t ht a b ha hb hab
  change x + (a • s + b • t) • z ∈ O
  rw [line_combo x z hab]
  exact hOc hs ht ha hb hab

/-- A convex function is convex along every line. -/
theorem ConvexOn.comp_line (hf : ConvexOn ℝ O f) (x z : E) :
    ConvexOn ℝ {t : ℝ | x + t • z ∈ O} (fun t ↦ f (x + t • z)) := by
  refine ⟨convex_lineSet hf.1 x z, fun s hs t ht a b ha hb hab ↦ ?_⟩
  change f (x + (a • s + b • t) • z) ≤ _
  rw [line_combo x z hab]
  exact hf.2 hs ht ha hb hab

theorem hasDerivAt_line (hO : IsOpen O) (hf : DifferentiableOn ℝ f O) {x z : E} {t : ℝ}
    (ht : x + t • z ∈ O) :
    HasDerivAt (fun s : ℝ ↦ f (x + s • z)) (fderiv ℝ f (x + t • z) z) t := by
  have hfx : HasFDerivAt f (fderiv ℝ f (x + t • z)) (x + t • z) :=
    (hf.differentiableAt (hO.mem_nhds ht)).hasFDerivAt
  have hpath : HasDerivAt (fun s : ℝ ↦ x + s • z) z t := by
    simpa using ((hasDerivAt_id t).smul_const z).const_add x
  exact hfx.comp_hasDerivAt t hpath

theorem differentiableOn_line (hO : IsOpen O) (hf : DifferentiableOn ℝ f O) (x z : E) :
    DifferentiableOn ℝ (fun s : ℝ ↦ f (x + s • z)) {t | x + t • z ∈ O} :=
  fun _ ht ↦ (hasDerivAt_line hO hf ht).differentiableAt.differentiableWithinAt

theorem deriv_line (hO : IsOpen O) (hf : DifferentiableOn ℝ f O) {x z : E} {t : ℝ}
    (ht : x + t • z ∈ O) : deriv (fun s : ℝ ↦ f (x + s • z)) t = fderiv ℝ f (x + t • z) z :=
  (hasDerivAt_line hO hf ht).deriv

theorem hasDerivAt_fderiv_line (hO : IsOpen O) (hf2 : DifferentiableOn ℝ (fderiv ℝ f) O)
    {x z : E} {t : ℝ} (ht : x + t • z ∈ O) :
    HasDerivAt (fun s : ℝ ↦ fderiv ℝ f (x + s • z) z)
      (fderiv ℝ (fderiv ℝ f) (x + t • z) z z) t := by
  have hD : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) (x + t • z)) (x + t • z) :=
    (hf2.differentiableAt (hO.mem_nhds ht)).hasFDerivAt
  have hpath : HasDerivAt (fun s : ℝ ↦ x + s • z) z t := by
    simpa using ((hasDerivAt_id t).smul_const z).const_add x
  have hc1 : HasDerivAt (fun s : ℝ ↦ fderiv ℝ f (x + s • z))
      (fderiv ℝ (fderiv ℝ f) (x + t • z) z) t :=
    hD.comp_hasDerivAt t hpath
  refine (hc1.clm_apply (hasDerivAt_const t z)).congr_deriv ?_
  simp only [map_zero, add_zero]

theorem deriv_eventuallyEq_line (hO : IsOpen O) (hf : DifferentiableOn ℝ f O) {x z : E}
    {t : ℝ} (ht : x + t • z ∈ O) :
    deriv (fun s : ℝ ↦ f (x + s • z)) =ᶠ[𝓝 t] fun s ↦ fderiv ℝ f (x + s • z) z := by
  filter_upwards [(isOpen_lineSet hO x z).mem_nhds ht] with s hs
  exact deriv_line hO hf hs

theorem differentiableOn_deriv_line (hO : IsOpen O) (hf : DifferentiableOn ℝ f O)
    (hf2 : DifferentiableOn ℝ (fderiv ℝ f) O) (x z : E) :
    DifferentiableOn ℝ (deriv (fun s : ℝ ↦ f (x + s • z))) {t | x + t • z ∈ O} := by
  intro t ht
  exact ((hasDerivAt_fderiv_line hO hf2 ht).differentiableAt.congr_of_eventuallyEq
    (deriv_eventuallyEq_line hO hf ht)).differentiableWithinAt

theorem deriv2_line (hO : IsOpen O) (hf : DifferentiableOn ℝ f O)
    (hf2 : DifferentiableOn ℝ (fderiv ℝ f) O) {x z : E} {t : ℝ} (ht : x + t • z ∈ O) :
    deriv^[2] (fun s : ℝ ↦ f (x + s • z)) t = fderiv ℝ (fderiv ℝ f) (x + t • z) z z := by
  change deriv (deriv (fun s : ℝ ↦ f (x + s • z))) t = _
  rw [(deriv_eventuallyEq_line hO hf ht).deriv_eq]
  exact (hasDerivAt_fderiv_line hO hf2 ht).deriv

theorem tangent_le_of_convexOn_line (hO : IsOpen O) (hf : DifferentiableOn ℝ f O) {x y : E}
    (hx : x ∈ O) (hy : y ∈ O)
    (hg : ConvexOn ℝ {t : ℝ | x + t • (y - x) ∈ O} (fun t ↦ f (x + t • (y - x)))) :
    f x + fderiv ℝ f x (y - x) ≤ f y := by
  have h0 : (0 : ℝ) ∈ {t : ℝ | x + t • (y - x) ∈ O} := by simpa using hx
  have h1 : (1 : ℝ) ∈ {t : ℝ | x + t • (y - x) ∈ O} := by simpa using hy
  have h := (convexOn_iff_tangent_le (isOpen_lineSet hO x (y - x))
    (hg.1) (differentiableOn_line hO hf x (y - x))).mp hg 0 h0 1 h1
  rw [deriv_line hO hf h0] at h
  simpa using h

theorem tangent_lt_of_strictConvexOn_line (hO : IsOpen O) (hf : DifferentiableOn ℝ f O)
    {x y : E} (hx : x ∈ O) (hy : y ∈ O)
    (hg : StrictConvexOn ℝ {t : ℝ | x + t • (y - x) ∈ O} (fun t ↦ f (x + t • (y - x)))) :
    f x + fderiv ℝ f x (y - x) < f y := by
  have h0 : (0 : ℝ) ∈ {t : ℝ | x + t • (y - x) ∈ O} := by simpa using hx
  have h1 : (1 : ℝ) ∈ {t : ℝ | x + t • (y - x) ∈ O} := by simpa using hy
  have h := (strictConvexOn_iff_tangent_lt (isOpen_lineSet hO x (y - x))
    (hg.1) (differentiableOn_line hO hf x (y - x))).mp hg 0 h0 1 h1 one_ne_zero
  rw [deriv_line hO hf h0] at h
  simpa using h

theorem combo_sub_eq_zero {x y : E} {a b : ℝ} (hab : a + b = 1) :
    a • (x - (a • x + b • y)) + b • (y - (a • x + b • y)) = 0 := by
  calc a • (x - (a • x + b • y)) + b • (y - (a • x + b • y))
      = (a • x + b • y) - (a + b) • (a • x + b • y) := by module
    _ = 0 := by rw [hab, one_smul, sub_self]

/-- **Theorem 2.14(b)**: a differentiable function on an open convex set is
convex if and only if `f(y) ≥ f(x) + ⟨∇f(x), y - x⟩` for all `x, y` there. -/
theorem convexOn_iff_fderiv_tangent_le (hO : IsOpen O) (hOc : Convex ℝ O)
    (hf : DifferentiableOn ℝ f O) :
    ConvexOn ℝ O f ↔ ∀ x ∈ O, ∀ y ∈ O, f x + fderiv ℝ f x (y - x) ≤ f y := by
  constructor
  · intro hconv x hx y hy
    exact tangent_le_of_convexOn_line hO hf hx hy (ConvexOn.comp_line hconv x (y - x))
  · intro h
    refine ⟨hOc, fun x hx y hy a b ha hb hab ↦ ?_⟩
    have hzO : a • x + b • y ∈ O := hOc hx hy ha hb hab
    have h1 := h _ hzO x hx
    have h2 := h _ hzO y hy
    have hlin : a * fderiv ℝ f (a • x + b • y) (x - (a • x + b • y)) +
        b * fderiv ℝ f (a • x + b • y) (y - (a • x + b • y)) = 0 := by
      rw [← smul_eq_mul, ← smul_eq_mul, ← map_smul, ← map_smul, ← map_add,
        combo_sub_eq_zero hab, map_zero]
    have e1 := mul_le_mul_of_nonneg_left h1 ha
    have e2 := mul_le_mul_of_nonneg_left h2 hb
    simp only [smul_eq_mul]
    have hsum : a * f (a • x + b • y) + b * f (a • x + b • y) = f (a • x + b • y) := by
      rw [← add_mul, hab, one_mul]
    nlinarith

/-- **Theorem 2.14(a)**: a differentiable function on an open convex set is
convex if and only if `⟨x₁ - x₀, ∇f(x₁) - ∇f(x₀)⟩ ≥ 0` for all `x₀, x₁` there. -/
theorem convexOn_iff_fderiv_monotone (hO : IsOpen O) (hOc : Convex ℝ O)
    (hf : DifferentiableOn ℝ f O) :
    ConvexOn ℝ O f ↔ ∀ x₀ ∈ O, ∀ x₁ ∈ O, 0 ≤ (fderiv ℝ f x₁ - fderiv ℝ f x₀) (x₁ - x₀) := by
  rw [convexOn_iff_fderiv_tangent_le hO hOc hf]
  constructor
  · intro h x₀ h₀ x₁ h₁
    have e1 := h x₀ h₀ x₁ h₁
    have e2 := h x₁ h₁ x₀ h₀
    have hneg : fderiv ℝ f x₁ (x₀ - x₁) = -fderiv ℝ f x₁ (x₁ - x₀) := by
      rw [← map_neg, neg_sub]
    rw [ContinuousLinearMap.sub_apply]
    linarith
  · intro h x hx y hy
    apply tangent_le_of_convexOn_line hO hf hx hy
    rw [convexOn_iff_monotoneOn_deriv (isOpen_lineSet hO x (y - x)) (convex_lineSet hOc x (y - x))
      (differentiableOn_line hO hf x (y - x))]
    intro s hs t ht hst
    rw [deriv_line hO hf hs, deriv_line hO hf ht]
    have h' := h _ hs _ ht
    have hdiff : (x + t • (y - x)) - (x + s • (y - x)) = (t - s) • (y - x) := by module
    rw [hdiff, map_smul, smul_eq_mul, ContinuousLinearMap.sub_apply] at h'
    rcases hst.eq_or_lt with rfl | hlt
    · exact le_rfl
    · have := nonneg_of_mul_nonneg_right (by linarith : 0 ≤ (t - s) *
        (fderiv ℝ f (x + t • (y - x)) (y - x) - fderiv ℝ f (x + s • (y - x)) (y - x)))
        (sub_pos.mpr hlt)
      linarith

/-- **Theorem 2.14(c)**: a twice differentiable function on an open convex set
is convex if and only if its Hessian is positive-semidefinite throughout. -/
theorem convexOn_iff_hessian_nonneg (hO : IsOpen O) (hOc : Convex ℝ O)
    (hf : DifferentiableOn ℝ f O) (hf2 : DifferentiableOn ℝ (fderiv ℝ f) O) :
    ConvexOn ℝ O f ↔ ∀ x ∈ O, ∀ z : E, 0 ≤ fderiv ℝ (fderiv ℝ f) x z z := by
  constructor
  · intro hconv x hx z
    have h0 : (0 : ℝ) ∈ {t : ℝ | x + t • z ∈ O} := by simpa using hx
    have h := (convexOn_iff_deriv2_nonneg_of_isOpen (isOpen_lineSet hO x z) (convex_lineSet hOc x z)
      (differentiableOn_line hO hf x z) (differentiableOn_deriv_line hO hf hf2 x z)).mp
      (ConvexOn.comp_line hconv x z) 0 h0
    rwa [deriv2_line hO hf hf2 h0, zero_smul, add_zero] at h
  · intro h
    rw [convexOn_iff_fderiv_tangent_le hO hOc hf]
    intro x hx y hy
    apply tangent_le_of_convexOn_line hO hf hx hy
    rw [convexOn_iff_deriv2_nonneg_of_isOpen (isOpen_lineSet hO x (y - x))
      (convex_lineSet hOc x (y - x)) (differentiableOn_line hO hf x (y - x))
      (differentiableOn_deriv_line hO hf hf2 x (y - x))]
    intro t ht
    rw [deriv2_line hO hf hf2 ht]
    exact h _ ht _

/-- **Theorem 2.14**, strict form of (b): strict convexity is equivalent to the
strict gradient inequality for `x ≠ y`. -/
theorem strictConvexOn_iff_fderiv_tangent_lt (hO : IsOpen O) (hOc : Convex ℝ O)
    (hf : DifferentiableOn ℝ f O) :
    StrictConvexOn ℝ O f ↔ ∀ x ∈ O, ∀ y ∈ O, y ≠ x → f x + fderiv ℝ f x (y - x) < f y := by
  constructor
  · intro hs x hx y hy hyx
    have htan := (convexOn_iff_fderiv_tangent_le hO hOc hf).mp hs.convexOn
    have hmO : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y ∈ O :=
      hOc hx hy (by norm_num) (by norm_num) (by norm_num)
    have hlt := hs.2 hx hy hyx.symm (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    have hle := htan x hx _ hmO
    have hmx : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y - x = (1 / 2 : ℝ) • (y - x) := by module
    rw [hmx, map_smul, smul_eq_mul] at hle
    simp only [smul_eq_mul] at hlt
    linarith
  · intro h
    refine ⟨hOc, fun x hx y hy hxy a b ha hb hab ↦ ?_⟩
    have hzO : a • x + b • y ∈ O := hOc hx hy ha.le hb.le hab
    have hzx : x ≠ a • x + b • y := by
      intro he
      apply hxy
      have : b • (y - x) = 0 := by
        calc b • (y - x) = (a • x + b • y) - (a + b) • x := by module
          _ = 0 := by rw [hab, one_smul, ← he, sub_self]
      rcases smul_eq_zero.mp this with h0 | h0
      · exact absurd h0 hb.ne'
      · exact (sub_eq_zero.mp h0).symm
    have hzy : y ≠ a • x + b • y := by
      intro he
      apply hxy
      have : a • (x - y) = 0 := by
        calc a • (x - y) = (a • x + b • y) - (a + b) • y := by module
          _ = 0 := by rw [hab, one_smul, ← he, sub_self]
      rcases smul_eq_zero.mp this with h0 | h0
      · exact absurd h0 ha.ne'
      · exact sub_eq_zero.mp h0
    have h1 := h _ hzO x hx hzx
    have h2 := h _ hzO y hy hzy
    have hlin : a * fderiv ℝ f (a • x + b • y) (x - (a • x + b • y)) +
        b * fderiv ℝ f (a • x + b • y) (y - (a • x + b • y)) = 0 := by
      rw [← smul_eq_mul, ← smul_eq_mul, ← map_smul, ← map_smul, ← map_add,
        combo_sub_eq_zero hab, map_zero]
    have e1 := mul_lt_mul_of_pos_left h1 ha
    have e2 := mul_lt_mul_of_pos_left h2 hb
    simp only [smul_eq_mul]
    have hsum : a * f (a • x + b • y) + b * f (a • x + b • y) = f (a • x + b • y) := by
      rw [← add_mul, hab, one_mul]
    nlinarith

/-- **Theorem 2.14**, strict form of (a): strict convexity is equivalent to
`⟨x₁ - x₀, ∇f(x₁) - ∇f(x₀)⟩ > 0` for `x₀ ≠ x₁`. -/
theorem strictConvexOn_iff_fderiv_strictMonotone (hO : IsOpen O) (hOc : Convex ℝ O)
    (hf : DifferentiableOn ℝ f O) :
    StrictConvexOn ℝ O f ↔
      ∀ x₀ ∈ O, ∀ x₁ ∈ O, x₀ ≠ x₁ → 0 < (fderiv ℝ f x₁ - fderiv ℝ f x₀) (x₁ - x₀) := by
  rw [strictConvexOn_iff_fderiv_tangent_lt hO hOc hf]
  constructor
  · intro h x₀ h₀ x₁ h₁ hne
    have e1 := h x₀ h₀ x₁ h₁ hne.symm
    have e2 := h x₁ h₁ x₀ h₀ hne
    have hneg : fderiv ℝ f x₁ (x₀ - x₁) = -fderiv ℝ f x₁ (x₁ - x₀) := by
      rw [← map_neg, neg_sub]
    rw [ContinuousLinearMap.sub_apply]
    linarith
  · intro h x hx y hy hyx
    apply tangent_lt_of_strictConvexOn_line hO hf hx hy
    rw [strictConvexOn_iff_strictMonoOn_deriv (isOpen_lineSet hO x (y - x))
      (convex_lineSet hOc x (y - x)) (differentiableOn_line hO hf x (y - x))]
    intro s hs t ht hst
    rw [deriv_line hO hf hs, deriv_line hO hf ht]
    have hne : x + s • (y - x) ≠ x + t • (y - x) := by
      intro he
      have : (t - s) • (y - x) = 0 := by
        calc (t - s) • (y - x) = (x + t • (y - x)) - (x + s • (y - x)) := by module
          _ = 0 := by rw [he, sub_self]
      rcases smul_eq_zero.mp this with h0 | h0
      · linarith
      · exact hyx (sub_eq_zero.mp h0)
    have h' := h _ hs _ ht hne
    have hdiff : (x + t • (y - x)) - (x + s • (y - x)) = (t - s) • (y - x) := by module
    rw [hdiff, map_smul, smul_eq_mul, ContinuousLinearMap.sub_apply] at h'
    have := pos_of_mul_pos_right h' (sub_pos.mpr hst).le
    linarith

/-- **Theorem 2.14**: positive definiteness of the Hessian throughout an open
convex set is sufficient for strict convexity. -/
theorem strictConvexOn_of_hessian_pos (hO : IsOpen O) (hOc : Convex ℝ O)
    (hf : DifferentiableOn ℝ f O) (hf2 : DifferentiableOn ℝ (fderiv ℝ f) O)
    (h : ∀ x ∈ O, ∀ z : E, z ≠ 0 → 0 < fderiv ℝ (fderiv ℝ f) x z z) :
    StrictConvexOn ℝ O f := by
  rw [strictConvexOn_iff_fderiv_tangent_lt hO hOc hf]
  intro x hx y hy hyx
  apply tangent_lt_of_strictConvexOn_line hO hf hx hy
  apply strictConvexOn_of_deriv2_pos_of_isOpen (isOpen_lineSet hO x (y - x))
    (convex_lineSet hOc x (y - x)) (differentiableOn_line hO hf x (y - x)).continuousOn
  intro t ht
  rw [deriv2_line hO hf hf2 ht]
  exact h _ ht _ (sub_ne_zero.mpr hyx)

end HigherDimensional

/-! ## Example 2.15 -/

section Quadratic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The linear-quadratic function `x ↦ ½⟪x, A x⟫ + ⟪a, x⟫ + c` of Example 2.15. -/
def linearQuadratic (A : E →L[ℝ] E) (a : E) (c : ℝ) (x : E) : ℝ :=
  (1 / 2 : ℝ) * ⟪x, A x⟫_ℝ + ⟪a, x⟫_ℝ + c

/-- The exact convexity defect of a quadratic function along a segment. -/
theorem linearQuadratic_combo {A : E →L[ℝ] E} (hA : ∀ x y, ⟪A x, y⟫_ℝ = ⟪x, A y⟫_ℝ) (a : E)
    (c : ℝ) (x y : E) (τ : ℝ) :
    linearQuadratic A a c ((1 - τ) • x + τ • y) =
      (1 - τ) * linearQuadratic A a c x + τ * linearQuadratic A a c y -
        (1 / 2) * τ * (1 - τ) * ⟪x - y, A (x - y)⟫_ℝ := by
  have hyx : ⟪y, A x⟫_ℝ = ⟪x, A y⟫_ℝ := by rw [real_inner_comm, hA]
  simp only [linearQuadratic, map_add, map_smul, map_sub, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, hyx]
  ring

/-- **Example 2.15**: a quadratic function with symmetric `A` is convex if and
only if `A` is positive-semidefinite. -/
theorem convexOn_linearQuadratic_iff {A : E →L[ℝ] E} (hA : ∀ x y, ⟪A x, y⟫_ℝ = ⟪x, A y⟫_ℝ)
    (a : E) (c : ℝ) : ConvexOn ℝ univ (linearQuadratic A a c) ↔ ∀ z, 0 ≤ ⟪z, A z⟫_ℝ := by
  constructor
  · intro h z
    have h' := h.2 (mem_univ z) (mem_univ 0) (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    rw [linearQuadratic_combo hA a c z 0 (1 / 2)] at h'
    simp only [smul_eq_mul, sub_zero] at h'
    nlinarith
  · intro h
    refine ⟨convex_univ, fun x _ y _ p q hp hq hpq ↦ ?_⟩
    obtain rfl : p = 1 - q := by linarith
    rw [linearQuadratic_combo hA a c x y q]
    have := h (x - y)
    simp only [smul_eq_mul]
    nlinarith [mul_nonneg hq hp]

/-- **Example 2.15**: a quadratic function with symmetric `A` is strictly convex
if and only if `A` is positive-definite. -/
theorem strictConvexOn_linearQuadratic_iff {A : E →L[ℝ] E}
    (hA : ∀ x y, ⟪A x, y⟫_ℝ = ⟪x, A y⟫_ℝ) (a : E) (c : ℝ) :
    StrictConvexOn ℝ univ (linearQuadratic A a c) ↔ ∀ z, z ≠ 0 → 0 < ⟪z, A z⟫_ℝ := by
  constructor
  · intro h z hz
    have h' := h.2 (mem_univ z) (mem_univ 0) hz (by norm_num : (0 : ℝ) < 1 - 1 / 2)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    rw [linearQuadratic_combo hA a c z 0 (1 / 2)] at h'
    simp only [smul_eq_mul, sub_zero] at h'
    nlinarith
  · intro h
    refine ⟨convex_univ, fun x _ y _ hxy p q hp hq hpq ↦ ?_⟩
    obtain rfl : p = 1 - q := by linarith
    rw [linearQuadratic_combo hA a c x y q]
    have := h (x - y) (sub_ne_zero.mpr hxy)
    simp only [smul_eq_mul]
    nlinarith [mul_pos hq hp]

/-- **Example 2.15**: the gradient of a quadratic function is `∇f(x) = Ax + a`. -/
theorem hasGradientAt_linearQuadratic [CompleteSpace E] {A : E →L[ℝ] E}
    (hA : ∀ x y, ⟪A x, y⟫_ℝ = ⟪x, A y⟫_ℝ) (a : E) (c : ℝ) (x : E) :
    HasGradientAt (linearQuadratic A a c) (A x + a) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h1 : HasFDerivAt (fun t : E ↦ ⟪t, A t⟫_ℝ)
      ((fderivInnerCLM ℝ (x, A x)).comp ((ContinuousLinearMap.id ℝ E).prod A)) x :=
    (hasFDerivAt_id x).inner ℝ A.hasFDerivAt
  have h2 := ((h1.const_mul (1 / 2 : ℝ)).add ((innerSL ℝ a).hasFDerivAt)).add_const c
  refine h2.congr_fderiv ?_
  ext h
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, fderivInnerCLM_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply, InnerProductSpace.toDual_apply_apply,
    smul_eq_mul, inner_add_left]
  rw [(real_inner_comm (A h) x).trans (hA h x), real_inner_comm (A x) h]
  ring

/-- **Example 2.15**: the gradient mapping of a quadratic function is `x ↦ Ax + a`
and its derivative, the Hessian `∇²f(x)`, is the constant map `A`. -/
theorem hasFDerivAt_gradient_linearQuadratic [CompleteSpace E] {A : E →L[ℝ] E}
    (hA : ∀ x y, ⟪A x, y⟫_ℝ = ⟪x, A y⟫_ℝ) (a : E) (c : ℝ) (x : E) :
    gradient (linearQuadratic A a c) = (fun y ↦ A y + a) ∧
      HasFDerivAt (gradient (linearQuadratic A a c)) A x := by
  have hg : gradient (linearQuadratic A a c) = fun y ↦ A y + a :=
    funext fun y ↦ (hasGradientAt_linearQuadratic hA a c y).gradient
  refine ⟨hg, ?_⟩
  rw [hg]
  exact A.hasFDerivAt.add_const a

end Quadratic

end RW
