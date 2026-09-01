/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Basic First-Order Optimality Conditions

Theorem 6.12 relates four first-order conditions for minimizing a
differentiable real-valued function on a set: nonnegativity of the gradient
on the tangent cone, membership of the negative gradient in the regular and
limiting normal cones, and, for a convex feasible set, the global
variational inequality.  When the objective is convex on the feasible set,
the variational inequality is also sufficient for global optimality.
-/

import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Deriv
import RockafellarWets.Chapter6.ConvexSets

open Filter Set Topology
open scoped InnerProductSpace

namespace RW

section FirstOrderOptimality

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {C : Set E} {f : E → ℝ} {x g : E}

omit [FiniteDimensional ℝ E] in
/-- Every tangent vector in the sense of Definition 6.1 belongs to Mathlib's
positive tangent cone.  This bridge lets the general local-extremum theorem
be applied to the sequential tangent cone used in Chapter 6. -/
theorem tangentCone_subset_posTangentConeAt (C : Set E) (x : E) :
    tangentCone C x ⊆ posTangentConeAt C x := by
  rintro w ⟨xs, τs, hxC, hxto, hτpos, -, hq⟩
  apply mem_tangentConeAt_of_seq atTop
      (fun n ↦ ⟨(τs n)⁻¹, (inv_pos.2 (hτpos n)).le⟩)
      (fun n ↦ xs n - x)
  · have hzero : Tendsto (fun n ↦ xs n - x) atTop (nhds (x - x)) :=
      hxto.sub tendsto_const_nhds
    simpa using hzero
  · exact Filter.Eventually.of_forall fun n ↦ by simpa using hxC n
  · simpa only [NNReal.smul_def] using hq

/-- **Theorem 6.12**, necessary tangent condition 6(10): the gradient at a
local minimizer is nonnegative on every tangent direction. -/
theorem IsLocalMinOn.inner_gradient_nonneg_on_tangentCone
    (hx : x ∈ C) (hmin : IsLocalMinOn f C x) (hf : HasGradientAt f g x) :
    ∀ w ∈ tangentCone C x, 0 ≤ ⟪g, w⟫_ℝ := by
  intro w hw
  have hmin' : IsLocalMinOn f C x :=
    hmin.congr (Filter.Eventually.of_forall fun _ ↦ rfl) hx
  have h := hmin'.hasFDerivWithinAt_nonneg
    hf.hasFDerivAt.hasFDerivWithinAt
    (tangentCone_subset_posTangentConeAt C x hw)
  simpa [InnerProductSpace.toDual_apply_apply] using h

/-- Formula 6(10) is equivalent to the regular-normal condition 6(11).
Finite dimensionality is used by the reverse-polar characterization of the
regular normal cone. -/
theorem inner_nonneg_on_tangentCone_iff_neg_mem_regularNormalCone
    (hx : x ∈ C) :
    (∀ w ∈ tangentCone C x, 0 ≤ ⟪g, w⟫_ℝ) ↔
      -g ∈ regularNormalCone C x := by
  constructor
  · intro h
    apply mem_regularNormalCone_of_forall_inner_nonpos hx
    intro w hw
    simpa only [inner_neg_left, neg_nonpos] using h w hw
  · intro hg w hw
    have h := inner_nonpos_of_mem_regularNormalCone hg hw
    simpa only [inner_neg_left, neg_nonpos] using h

/-- **Theorem 6.12**, stronger form of the normal necessary condition: the
negative gradient at a local minimizer is a regular normal. -/
theorem IsLocalMinOn.neg_gradient_mem_regularNormalCone
    (hx : x ∈ C) (hmin : IsLocalMinOn f C x) (hf : HasGradientAt f g x) :
    -g ∈ regularNormalCone C x :=
  (inner_nonneg_on_tangentCone_iff_neg_mem_regularNormalCone hx).1
    (IsLocalMinOn.inner_gradient_nonneg_on_tangentCone hx hmin hf)

/-- **Theorem 6.12**, normal necessary condition 6(11): the negative gradient
at a local minimizer belongs to the limiting normal cone. -/
theorem IsLocalMinOn.neg_gradient_mem_normalCone
    (hx : x ∈ C) (hmin : IsLocalMinOn f C x) (hf : HasGradientAt f g x) :
    -g ∈ normalCone C x :=
  regularNormalCone_subset_normalCone C x
    (IsLocalMinOn.neg_gradient_mem_regularNormalCone hx hmin hf)

omit [FiniteDimensional ℝ E] in
/-- For a convex feasible set, nonnegativity on the tangent cone is
equivalent to the global linearized inequality against every feasible
point. -/
theorem inner_nonneg_on_tangentCone_iff_forall_inner_nonneg_of_convex
    (hC : Convex ℝ C) (hx : x ∈ C) :
    (∀ w ∈ tangentCone C x, 0 ≤ ⟪g, w⟫_ℝ) ↔
      (∀ y ∈ C, 0 ≤ ⟪g, y - x⟫_ℝ) := by
  constructor
  · intro h y hy
    apply h (y - x)
    exact derivableCone_subset_tangentCone hx
      (mem_derivableCone_of_convex hC hx ⟨1, one_pos, by simpa⟩)
  · intro h w hw
    have hn : -g ∈ regularNormalCone C x := by
      rw [regularNormalCone_eq_of_convex hC hx]
      intro y hy
      simpa only [inner_neg_left, neg_nonpos] using h y hy
    have hi := inner_nonpos_of_mem_regularNormalCone hn hw
    simpa only [inner_neg_left, neg_nonpos] using hi

omit [FiniteDimensional ℝ E] in
/-- For a convex feasible set, regular-normal membership of the negative
gradient is equivalent to the global linearized inequality. -/
theorem neg_mem_regularNormalCone_iff_forall_inner_nonneg_of_convex
    (hC : Convex ℝ C) (hx : x ∈ C) :
    -g ∈ regularNormalCone C x ↔
      (∀ y ∈ C, 0 ≤ ⟪g, y - x⟫_ℝ) := by
  rw [regularNormalCone_eq_of_convex hC hx]
  constructor
  · intro h y hy
    simpa only [inner_neg_left, neg_nonpos] using h y hy
  · intro h y hy
    simpa only [inner_neg_left, neg_nonpos] using h y hy

omit [FiniteDimensional ℝ E] in
/-- For a convex feasible set, normal-cone membership of the negative
gradient is equivalent to the global linearized inequality. -/
theorem neg_mem_normalCone_iff_forall_inner_nonneg_of_convex
    (hC : Convex ℝ C) (hx : x ∈ C) :
    -g ∈ normalCone C x ↔
      (∀ y ∈ C, 0 ≤ ⟪g, y - x⟫_ℝ) := by
  rw [normalCone_eq_of_convex hC hx]
  constructor
  · intro h y hy
    simpa only [inner_neg_left, neg_nonpos] using h y hy
  · intro h y hy
    simpa only [inner_neg_left, neg_nonpos] using h y hy

/-- The supporting inequality for a convex function, requiring
differentiability only at the base point.  The proof restricts the function
to the segment from `x` to `y` and compares its right derivative at zero
with the secant slope. -/
theorem supporting_inequality_of_convexOn_of_hasGradientAt
    (hC : Convex ℝ C) (hx : x ∈ C) (hfconv : ConvexOn ℝ C f)
    (hgrad : HasGradientAt f g x) :
    ∀ y ∈ C, f x + ⟪g, y - x⟫_ℝ ≤ f y := by
  intro y hy
  let γ : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y
  have hmaps : MapsTo γ (Icc (0 : ℝ) 1) C := by
    intro t ht
    change AffineMap.lineMap x y t ∈ C
    rw [AffineMap.lineMap_apply_module]
    exact hC hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hconv : ConvexOn ℝ (Icc (0 : ℝ) 1) (f ∘ γ) :=
    (hfconv.comp_affineMap γ).subset hmaps (convex_Icc 0 1)
  have hγ : HasDerivAt (γ : ℝ → E) (y - x) 0 := by
    simpa only [γ, AffineMap.lineMap_apply_module', zero_smul, zero_add, one_smul]
      using ((hasDerivAt_id' (0 : ℝ)).smul_const (y - x)).add_const x
  have hgradγ : HasFDerivAt f (InnerProductSpace.toDual ℝ E g) (γ 0) := by
    simpa only [γ, AffineMap.lineMap_apply_zero] using hgrad.hasFDerivAt
  have hder : HasDerivAt (f ∘ γ) ⟪g, y - x⟫_ℝ 0 := by
    simpa only [InnerProductSpace.toDual_apply_apply]
      using hgradγ.comp_hasDerivAt 0 hγ
  have hslope := hconv.le_slope_of_hasDerivAt
    (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one) zero_lt_one hder
  have hslope' : ⟪g, y - x⟫_ℝ ≤ f y - f x := by
    simpa only [slope_def_field, sub_zero, div_one, Function.comp_apply, γ,
      AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using hslope
  linarith

/-- **Theorem 6.12**, convex sufficiency: for a convex objective on a convex
feasible set, the global first-order inequality makes `x` a global
minimizer. -/
theorem isMinOn_of_convexOn_of_firstOrder
    (hC : Convex ℝ C) (hx : x ∈ C) (hfconv : ConvexOn ℝ C f)
    (hgrad : HasGradientAt f g x)
    (hfirst : ∀ y ∈ C, 0 ≤ ⟪g, y - x⟫_ℝ) :
    IsMinOn f C x := by
  intro y hy
  have hsupp := supporting_inequality_of_convexOn_of_hasGradientAt
    hC hx hfconv hgrad y hy
  exact (le_add_of_nonneg_right (hfirst y hy)).trans hsupp

/-- A compact form of the necessary part of Theorem 6.12. -/
theorem IsLocalMinOn.firstOrder_optimality_conditions
    (hx : x ∈ C) (hmin : IsLocalMinOn f C x) (hf : HasGradientAt f g x) :
    (∀ w ∈ tangentCone C x, 0 ≤ ⟪g, w⟫_ℝ) ∧
      -g ∈ regularNormalCone C x ∧ -g ∈ normalCone C x := by
  have ht := IsLocalMinOn.inner_gradient_nonneg_on_tangentCone hx hmin hf
  have hr := (inner_nonneg_on_tangentCone_iff_neg_mem_regularNormalCone hx).1 ht
  exact ⟨ht, hr, regularNormalCone_subset_normalCone C x hr⟩

/-- On a convex feasible set, the three cone conditions and the global
linearized inequality in Theorem 6.12 are pairwise equivalent. -/
theorem firstOrder_optimality_conditions_iff_of_convex
    (hC : Convex ℝ C) (hx : x ∈ C) :
    ((∀ w ∈ tangentCone C x, 0 ≤ ⟪g, w⟫_ℝ) ↔
      -g ∈ regularNormalCone C x) ∧
    (-g ∈ regularNormalCone C x ↔ -g ∈ normalCone C x) ∧
    (-g ∈ normalCone C x ↔
      ∀ y ∈ C, 0 ≤ ⟪g, y - x⟫_ℝ) := by
  refine ⟨inner_nonneg_on_tangentCone_iff_neg_mem_regularNormalCone hx, ?_,
    neg_mem_normalCone_iff_forall_inner_nonneg_of_convex hC hx⟩
  rw [normalCone_eq_regularNormalCone_of_convex hC hx]

end FirstOrderOptimality

end RW
