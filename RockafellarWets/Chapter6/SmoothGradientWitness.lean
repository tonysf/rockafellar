/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: The smooth witness in Theorem 6.11

`GradientNormals.lean` proves that a regular normal `v ∈ regularNormalCone C x` is the gradient
at `x` of a function having a unique global maximum relative to `C`, but the witness produced
there is differentiable only at `x`.  Theorem 6.11 strengthens this: the witness may be taken
`C¹` on the whole ambient space.

The construction is the one in the book.  The radial modulus

```
θ₀ r = sup {⟪v, y - x⟫ : y ∈ C, ‖y - x‖ ≤ r} ∪ {0}
```

is nondecreasing, vanishes at the origin, and is `o(r)` by the defining inequality of a regular
normal.  `SmoothMajorant.lean` upgrades it to an everywhere `C¹` function `θ` with `θ 0 = 0`,
`θ' 0 = 0` and `θ₀ r < θ r` for `r > 0`.  The witness is then

```
h y = ⟪v, y - x⟫ - θ ‖y - x‖.
```

The analytic bridge is `RW.contDiff_one_comp_norm_sub`: composing a scalar `C¹` function whose
derivative vanishes at the origin with the norm of a real inner product space again gives a `C¹`
function.  Away from the centre this is the chain rule; at the centre the vanishing derivative
absorbs the corner of the norm.
-/

import RockafellarWets.Chapter6.GradientNormals
import RockafellarWets.Chapter6.SmoothMajorant
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Asymptotics Filter Metric Set Topology
open scoped InnerProductSpace

noncomputable section

namespace RW

section RadialComposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Away from the origin the norm of a real inner product space is Fréchet differentiable, with
derivative the linear functional `z ↦ ⟪‖y‖⁻¹ • y, z⟫`. -/
theorem hasFDerivAt_norm_of_ne_zero {y : E} (hy : y ≠ 0) :
    HasFDerivAt (fun z : E ↦ ‖z‖) (‖y‖⁻¹ • innerSL ℝ y) y := by
  have hpos : (0 : ℝ) < ‖y‖ := norm_pos_iff.mpr hy
  have hsq : HasFDerivAt (fun z : E ↦ ‖z‖ ^ 2) ((2 : ℝ) • innerSL ℝ y) y := by
    refine (hasFDerivAt_id y).norm_sq.congr_fderiv ?_
    ext z
    simp
  have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (‖y‖ ^ 2))) (‖y‖ ^ 2) :=
    Real.hasDerivAt_sqrt (by positivity)
  have hcomp := hsqrt.comp_hasFDerivAt y hsq
  have hfun : (Real.sqrt ∘ fun z : E ↦ ‖z‖ ^ 2) = fun z : E ↦ ‖z‖ := by
    funext z
    simp [Function.comp, Real.sqrt_sq (norm_nonneg z)]
  rw [hfun] at hcomp
  refine hcomp.congr_fderiv ?_
  rw [Real.sqrt_sq (norm_nonneg y), smul_smul]
  congr 1
  field_simp

/-- Candidate derivative field of `y ↦ theta ‖y‖`.  Division by `‖y‖` and the vanishing of
`innerSL ℝ 0` make the formula valid at the origin as well, where it evaluates to `0`. -/
private def radialFDeriv (theta : ℝ → ℝ) (y : E) : E →L[ℝ] ℝ :=
  (deriv theta ‖y‖ / ‖y‖) • innerSL ℝ y

private theorem radialFDeriv_zero (theta : ℝ → ℝ) :
    radialFDeriv theta (0 : E) = 0 := by
  change (deriv theta ‖(0 : E)‖ / ‖(0 : E)‖) • (innerSL ℝ (0 : E)) = 0
  simp

private theorem norm_radialFDeriv_le (theta : ℝ → ℝ) (y : E) :
    ‖radialFDeriv theta y‖ ≤ |deriv theta ‖y‖| := by
  rcases eq_or_ne y 0 with rfl | hy
  · rw [radialFDeriv_zero]
    simp
  · have hne : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
    refine le_of_eq ?_
    change ‖(deriv theta ‖y‖ / ‖y‖) • (innerSL ℝ y)‖ = |deriv theta ‖y‖|
    rw [norm_smul, innerSL_apply_norm, Real.norm_eq_abs, abs_div,
      abs_of_nonneg (norm_nonneg y), div_mul_cancel₀ _ hne]

private theorem hasFDerivAt_radialFDeriv {theta : ℝ → ℝ} (htheta : ContDiff ℝ 1 theta)
    (htheta0 : HasDerivAt theta 0 0) (y : E) :
    HasFDerivAt (fun z : E ↦ theta ‖z‖) (radialFDeriv theta y) y := by
  rcases eq_or_ne y 0 with rfl | hy
  · rw [radialFDeriv_zero]
    have hlo : (fun t : ℝ ↦ theta t - theta 0) =o[𝓝 (0 : ℝ)] fun t : ℝ ↦ t := by
      simpa using hasDerivAt_iff_isLittleO.mp htheta0
    have htend : Tendsto (fun z : E ↦ ‖z‖) (𝓝 (0 : E)) (𝓝 (0 : ℝ)) := by
      simpa using (continuous_norm (E := E)).tendsto (0 : E)
    have hcomp : (fun z : E ↦ theta ‖z‖ - theta 0) =o[𝓝 (0 : E)] fun z : E ↦ ‖z‖ := by
      simpa [Function.comp_def] using hlo.comp_tendsto htend
    change HasFDerivAtFilter (fun z : E ↦ theta ‖z‖) (0 : E →L[ℝ] ℝ) 0 (𝓝 0)
    rw [hasFDerivAtFilter_iff_isLittleO]
    simpa using isLittleO_norm_right.mp hcomp
  · have hd : HasDerivAt theta (deriv theta ‖y‖) ‖y‖ :=
      ((contDiff_one_iff_deriv.mp htheta).1 ‖y‖).hasDerivAt
    have hcomp := hd.comp_hasFDerivAt y (hasFDerivAt_norm_of_ne_zero hy)
    have hfun : (theta ∘ fun z : E ↦ ‖z‖) = fun z : E ↦ theta ‖z‖ := rfl
    rw [hfun] at hcomp
    refine hcomp.congr_fderiv ?_
    change deriv theta ‖y‖ • (‖y‖⁻¹ • innerSL ℝ y) = (deriv theta ‖y‖ / ‖y‖) • innerSL ℝ y
    rw [smul_smul, div_eq_mul_inv]

private theorem continuous_radialFDeriv {theta : ℝ → ℝ} (htheta : ContDiff ℝ 1 theta)
    (htheta0 : HasDerivAt theta 0 0) :
    Continuous (radialFDeriv theta : E → E →L[ℝ] ℝ) := by
  have hderiv : Continuous (deriv theta) := (contDiff_one_iff_deriv.mp htheta).2
  rw [continuous_iff_continuousAt]
  intro y
  rcases eq_or_ne y 0 with rfl | hy
  · rw [ContinuousAt, radialFDeriv_zero]
    refine squeeze_zero_norm (fun z ↦ norm_radialFDeriv_le theta z) ?_
    have hcont : Continuous fun z : E ↦ |deriv theta ‖z‖| :=
      continuous_abs.comp (hderiv.comp continuous_norm)
    simpa [htheta0.deriv] using hcont.tendsto (0 : E)
  · have hquot : ContinuousAt (fun z : E ↦ deriv theta ‖z‖ / ‖z‖) y :=
      (hderiv.comp continuous_norm).continuousAt.div continuous_norm.continuousAt
        (norm_ne_zero_iff.mpr hy)
    have hinner : ContinuousAt (fun z : E ↦ (innerSL ℝ z : E →L[ℝ] ℝ)) y :=
      (innerSL ℝ (E := E)).continuous.continuousAt
    exact hquot.smul hinner

/-- **Radial composition lemma.**  A scalar `C¹` function whose derivative vanishes at the
origin stays `C¹` after composition with the norm of a real inner product space.  No evenness,
polynomial form, or second-order regularity is assumed. -/
theorem contDiff_one_comp_norm {theta : ℝ → ℝ} (htheta : ContDiff ℝ 1 theta)
    (htheta0 : HasDerivAt theta 0 0) :
    ContDiff ℝ 1 fun y : E ↦ theta ‖y‖ :=
  contDiff_one_iff_hasFDerivAt.mpr
    ⟨radialFDeriv theta, continuous_radialFDeriv htheta htheta0,
      hasFDerivAt_radialFDeriv htheta htheta0⟩

/-- The version of `RW.contDiff_one_comp_norm` centred at an arbitrary point. -/
theorem contDiff_one_comp_norm_sub {theta : ℝ → ℝ} (htheta : ContDiff ℝ 1 theta)
    (htheta0 : HasDerivAt theta 0 0) (x : E) :
    ContDiff ℝ 1 fun y : E ↦ theta ‖y - x‖ := by
  have hshift : ContDiff ℝ 1 fun y : E ↦ y - x := contDiff_id.sub contDiff_const
  simpa [Function.comp_def] using (contDiff_one_comp_norm htheta htheta0).comp hshift

end RadialComposition

section Modulus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The first-order gains `⟪v, y - x⟫` available at feasible points within radius `max r 0`,
together with `0`.  Adjoining `0` keeps the set nonempty at every radius and makes the
supremum below globally defined and nonnegative. -/
private def modulusValues (C : Set E) (x v : E) (r : ℝ) : Set ℝ :=
  {t : ℝ | t = 0 ∨ ∃ y ∈ C, ‖y - x‖ ≤ max r 0 ∧ t = ⟪v, y - x⟫_ℝ}

private theorem mem_modulusValues {C : Set E} {x v : E} {r t : ℝ} :
    t ∈ modulusValues C x v r ↔
      t = 0 ∨ ∃ y ∈ C, ‖y - x‖ ≤ max r 0 ∧ t = ⟪v, y - x⟫_ℝ := Iff.rfl

private theorem zero_mem_modulusValues (C : Set E) (x v : E) (r : ℝ) :
    (0 : ℝ) ∈ modulusValues C x v r := Or.inl rfl

private theorem modulusValues_nonempty (C : Set E) (x v : E) (r : ℝ) :
    (modulusValues C x v r).Nonempty :=
  ⟨0, zero_mem_modulusValues C x v r⟩

/-- Cauchy--Schwarz bounds every gain within radius `max r 0` by `‖v‖ * max r 0`. -/
private theorem modulusValues_bddAbove (C : Set E) (x v : E) (r : ℝ) :
    BddAbove (modulusValues C x v r) := by
  refine ⟨‖v‖ * max r 0, ?_⟩
  intro t ht
  rcases mem_modulusValues.mp ht with rfl | ⟨y, _, hle, rfl⟩
  · exact mul_nonneg (norm_nonneg v) (le_max_right r 0)
  · exact (real_inner_le_norm v (y - x)).trans
      (mul_le_mul_of_nonneg_left hle (norm_nonneg v))

/-- The radial modulus of Theorem 6.11: the largest first-order gain attainable at feasible
points within radius `r`.  It is extended by its value at the origin on negative radii. -/
private def modulus (C : Set E) (x v : E) (r : ℝ) : ℝ := sSup (modulusValues C x v r)

private theorem modulus_nonneg (C : Set E) (x v : E) (r : ℝ) : 0 ≤ modulus C x v r :=
  le_csSup (modulusValues_bddAbove C x v r) (zero_mem_modulusValues C x v r)

private theorem monotone_modulus (C : Set E) (x v : E) : Monotone (modulus C x v) := by
  intro a b hab
  refine csSup_le_csSup (modulusValues_bddAbove C x v b) (modulusValues_nonempty C x v a) ?_
  intro t ht
  rcases mem_modulusValues.mp ht with rfl | ⟨y, hy, hle, rfl⟩
  · exact zero_mem_modulusValues C x v b
  · exact mem_modulusValues.mpr
      (Or.inr ⟨y, hy, hle.trans (max_le_max hab le_rfl), rfl⟩)

/-- The monotonicity hypothesis in the form required by
`RW.exists_contDiff_one_strict_majorant`. -/
private theorem monotoneOn_modulus (C : Set E) (x v : E) :
    MonotoneOn (modulus C x v) (Ici 0) := (monotone_modulus C x v).monotoneOn _

private theorem modulus_zero (C : Set E) (x v : E) : modulus C x v 0 = 0 := by
  refine le_antisymm ?_ (modulus_nonneg C x v 0)
  refine csSup_le (modulusValues_nonempty C x v 0) ?_
  intro t ht
  rcases mem_modulusValues.mp ht with rfl | ⟨y, _, hle, rfl⟩
  · exact le_rfl
  · rw [max_self] at hle
    rw [norm_le_zero_iff.mp hle]
    simp

/-- The defining domination property: the gain at a feasible point is bounded by the modulus
evaluated at its distance to the base point. -/
private theorem inner_le_modulus {C : Set E} {x v y : E} (hy : y ∈ C) :
    ⟪v, y - x⟫_ℝ ≤ modulus C x v ‖y - x‖ :=
  le_csSup (modulusValues_bddAbove C x v ‖y - x‖)
    (mem_modulusValues.mpr (Or.inr ⟨y, hy, le_max_left _ _, rfl⟩))

/-- Domination in the positive-part form: since the modulus is nonnegative it dominates
`max ⟪v, y - x⟫ 0` as well. -/
private theorem max_inner_zero_le_modulus {C : Set E} {x v y : E} (hy : y ∈ C) :
    max ⟪v, y - x⟫_ℝ 0 ≤ modulus C x v ‖y - x‖ :=
  max_le (inner_le_modulus hy) (modulus_nonneg C x v ‖y - x‖)

/-- The regular-normal inequality is exactly first-order decay of the modulus at the origin. -/
private theorem tendsto_modulus_div {C : Set E} {x v : E} (hv : v ∈ regularNormalCone C x) :
    Tendsto (fun r : ℝ ↦ modulus C x v r / r) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := (mem_regularNormalCone_iff.mp hv).2 (ε / 2) (by positivity)
  refine ⟨δ, hδ, fun r hr hrd ↦ ?_⟩
  have hr0 : 0 < r := hr
  have hrlt : r < δ := by
    rwa [Real.dist_eq, sub_zero, abs_of_pos hr0] at hrd
  have hub : modulus C x v r ≤ ε / 2 * r := by
    refine csSup_le (modulusValues_nonempty C x v r) ?_
    intro t ht
    rcases mem_modulusValues.mp ht with rfl | ⟨y, hyC, hle, rfl⟩
    · positivity
    · rw [max_eq_left hr0.le] at hle
      exact (hbound y hyC (lt_of_le_of_lt hle hrlt)).trans
        (mul_le_mul_of_nonneg_left hle (by positivity))
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (div_nonneg (modulus_nonneg C x v r) hr0.le)]
  calc
    modulus C x v r / r ≤ ε / 2 * r / r := by
      exact div_le_div_of_nonneg_right hub hr0.le
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

end Modulus

section SmoothWitness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {C : Set E} {x v : E}

/-- **Theorem 6.11**, smooth form of the forward implication.  A regular normal `v` is the
gradient at `x` of a function that is `C¹` on all of `E` and attains its maximum relative to
`C` uniquely at `x`. -/
theorem exists_contDiff_one_hasGradientAt_unique_isMaxOn_of_mem_regularNormalCone
    (hv : v ∈ regularNormalCone C x) :
    ∃ h : E → ℝ,
      ContDiff ℝ 1 h ∧
      HasGradientAt h v x ∧
      IsMaxOn h C x ∧
      ∀ y ∈ C, h y = h x → y = x := by
  obtain ⟨θ, hθC1, hθ0, hθderiv, hθstrict, -, -⟩ :=
    exists_contDiff_one_strict_majorant (θ₀ := modulus C x v)
      (monotoneOn_modulus C x v) (modulus_zero C x v) (tendsto_modulus_div hv)
  set h : E → ℝ := fun y ↦ ⟪v, y - x⟫_ℝ - θ ‖y - x‖ with hdef
  have hhx : h x = 0 := by simp [hdef, hθ0]
  have hlt : ∀ y ∈ C, y ≠ x → h y < h x := by
    intro y hyC hyx
    have hpos : 0 < ‖y - x‖ := by
      rw [norm_pos_iff, sub_ne_zero]
      exact hyx
    have hgain : ⟪v, y - x⟫_ℝ ≤ modulus C x v ‖y - x‖ :=
      (le_max_left _ (0 : ℝ)).trans (max_inner_zero_le_modulus hyC)
    have hstrict : modulus C x v ‖y - x‖ < θ ‖y - x‖ := hθstrict _ hpos
    rw [hhx, hdef]
    simp only
    linarith
  refine ⟨h, ?_, ?_, ?_, ?_⟩
  · have hlinear : ContDiff ℝ 1 fun y : E ↦ ⟪v, y - x⟫_ℝ :=
      ContDiff.inner ℝ contDiff_const (contDiff_id.sub contDiff_const)
    exact hlinear.sub (contDiff_one_comp_norm_sub hθC1 hθderiv x)
  · rw [hasGradientAt_iff_isLittleO]
    have hlo : (fun t : ℝ ↦ θ t) =o[𝓝 (0 : ℝ)] fun t : ℝ ↦ t := by
      simpa [hθ0] using hasDerivAt_iff_isLittleO.mp hθderiv
    have htend : Tendsto (fun y : E ↦ ‖y - x‖) (𝓝 x) (𝓝 (0 : ℝ)) := by
      have hcont : Continuous fun y : E ↦ ‖y - x‖ :=
        (continuous_id.sub continuous_const).norm
      simpa using hcont.tendsto x
    have hcomp : (fun y : E ↦ θ ‖y - x‖) =o[𝓝 x] fun y : E ↦ ‖y - x‖ := by
      simpa [Function.comp_def] using hlo.comp_tendsto htend
    refine (isLittleO_norm_right.mp hcomp).neg_left.congr_left ?_
    intro y
    rw [hhx, hdef]
    ring
  · rw [isMaxOn_iff]
    intro y hyC
    rcases eq_or_ne y x with rfl | hyx
    · exact le_rfl
    · exact (hlt y hyC hyx).le
  · intro y hyC heq
    by_contra hyx
    exact absurd heq (hlt y hyC hyx).ne

/-- **Theorem 6.11**, smooth characterization of the regular normal cone: `v` is a regular
normal to `C` at `x` exactly when it is the gradient at `x` of a globally `C¹` function whose
maximum relative to `C` is attained uniquely at `x`. -/
theorem mem_regularNormalCone_iff_exists_contDiff_one_unique_isMaxOn_hasGradientAt
    (hx : x ∈ C) :
    v ∈ regularNormalCone C x ↔
      ∃ h : E → ℝ,
        ContDiff ℝ 1 h ∧
        IsMaxOn h C x ∧
        (∀ y ∈ C, h y = h x → y = x) ∧
        HasGradientAt h v x := by
  constructor
  · intro hv
    obtain ⟨h, hc1, hgrad, hmax, huniq⟩ :=
      exists_contDiff_one_hasGradientAt_unique_isMaxOn_of_mem_regularNormalCone hv
    exact ⟨h, hc1, hmax, huniq, hgrad⟩
  · rintro ⟨h, -, hmax, -, hgrad⟩
    exact mem_regularNormalCone_of_isLocalMaxOn_hasGradientAt hx hmax.localize hgrad

end SmoothWitness

end RW
