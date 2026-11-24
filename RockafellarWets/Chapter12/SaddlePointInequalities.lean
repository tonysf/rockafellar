/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: Variational inequalities for saddle points

Example 12.50.  Let `X ⊂ ℝⁿ`, `Y ⊂ ℝᵐ` be nonempty closed convex sets and let
`L : ℝⁿ × ℝᵐ → ℝ` be `C¹`, convex in `x ∈ X` for each `y ∈ Y` and concave in
`y ∈ Y` for each `x ∈ X`.  The saddle point condition

`x̄ ∈ X, ȳ ∈ Y, L(x, ȳ) ≥ L(x̄, ȳ) ≥ L(x̄, y) for all x ∈ X, y ∈ Y`

is the variational inequality for `C = X × Y` and
`F(x, y) = (∇ₓL(x, y), -∇_yL(x, y))`, that is `T(x̄, ȳ) ∋ (0, 0)` for the maximal
monotone mapping `T(x, y) = (∇ₓL(x, y) + N_X(x)) × (-∇_yL(x, y) + N_Y(y))`.

The product `ℝⁿ × ℝᵐ` carries its Euclidean structure `WithLp 2 (E × F)`, so
that `N_C(x, y) = N_X(x) × N_Y(y)` is the product normal cone formula of 6.41
(`normalCone_l2ProdSet`), while `C¹` is the usual condition on `E × F`.  The
partial gradients are continuous because the derivative of `L` is.  The
monotonicity of `F` relative to `C` is the sum of the four gradient
inequalities, the extension of 2.14 mentioned in the book; maximality comes
from Example 12.48, and the two coordinate conditions are the first-order
conditions of 6.12 for the convex problems in `x` and in `y`.
-/

import RockafellarWets.Chapter12.MonotoneVariationalInequalities
import RockafellarWets.Chapter6.ProductCones

open Set Filter Topology
open scoped InnerProductSpace Pointwise

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The mapping `F(x, y) = (∇ₓL(x, y), -∇_yL(x, y))` of Example 12.50 on the
Euclidean product. -/
noncomputable def saddleGradientMap (L : E × F → ℝ) (z : WithLp 2 (E × F)) : WithLp 2 (E × F) :=
  WithLp.toLp 2 (gradient (fun x ↦ L (x, z.snd)) z.fst, -gradient (fun y ↦ L (z.fst, y)) z.snd)

omit [FiniteDimensional ℝ F] in
/-- The partial gradient in `x` is read off the derivative of `L`. -/
theorem hasGradientAt_partial_fst {L : E × F → ℝ} (hL : ContDiff ℝ 1 L) (x : E) (y : F) :
    HasGradientAt (fun x' ↦ L (x', y))
      ((InnerProductSpace.toDual ℝ E).symm ((fderiv ℝ L (x, y)).comp
        (ContinuousLinearMap.inl ℝ E F))) x := by
  rw [hasGradientAt_iff_hasFDerivAt, LinearIsometryEquiv.apply_symm_apply]
  exact ((hL.differentiable one_ne_zero) (x, y)).hasFDerivAt.comp x (hasFDerivAt_prodMk_left x y)

omit [FiniteDimensional ℝ E] in
theorem hasGradientAt_partial_snd {L : E × F → ℝ} (hL : ContDiff ℝ 1 L) (x : E) (y : F) :
    HasGradientAt (fun y' ↦ L (x, y'))
      ((InnerProductSpace.toDual ℝ F).symm ((fderiv ℝ L (x, y)).comp
        (ContinuousLinearMap.inr ℝ E F))) y := by
  rw [hasGradientAt_iff_hasFDerivAt, LinearIsometryEquiv.apply_symm_apply]
  exact ((hL.differentiable one_ne_zero) (x, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right x y)

omit [FiniteDimensional ℝ F] in
theorem continuous_partial_fst {L : E × F → ℝ} (hL : ContDiff ℝ 1 L) :
    Continuous fun p : E × F ↦ gradient (fun x' ↦ L (x', p.2)) p.1 := by
  have h : (fun p : E × F ↦ gradient (fun x' ↦ L (x', p.2)) p.1) = fun p ↦
      (InnerProductSpace.toDual ℝ E).symm ((fderiv ℝ L p).comp (ContinuousLinearMap.inl ℝ E F)) :=
    funext fun p ↦ (hasGradientAt_partial_fst hL p.1 p.2).gradient
  rw [h]
  exact (InnerProductSpace.toDual ℝ E).symm.continuous.comp
    ((hL.continuous_fderiv one_ne_zero).clm_comp continuous_const)

omit [FiniteDimensional ℝ E] in
theorem continuous_partial_snd {L : E × F → ℝ} (hL : ContDiff ℝ 1 L) :
    Continuous fun p : E × F ↦ gradient (fun y' ↦ L (p.1, y')) p.2 := by
  have h : (fun p : E × F ↦ gradient (fun y' ↦ L (p.1, y')) p.2) = fun p ↦
      (InnerProductSpace.toDual ℝ F).symm ((fderiv ℝ L p).comp (ContinuousLinearMap.inr ℝ E F)) :=
    funext fun p ↦ (hasGradientAt_partial_snd hL p.1 p.2).gradient
  rw [h]
  exact (InnerProductSpace.toDual ℝ F).symm.continuous.comp
    ((hL.continuous_fderiv one_ne_zero).clm_comp continuous_const)

omit [FiniteDimensional ℝ E] in
theorem hasGradientAt_neg' {G : F → ℝ} {g : F} {y : F} (h : HasGradientAt G g y) :
    HasGradientAt (fun y ↦ -G y) (-g) y := by
  rw [hasGradientAt_iff_hasFDerivAt, map_neg]
  exact h.hasFDerivAt.neg

/-- `F` is continuous. -/
theorem continuous_saddleGradientMap {L : E × F → ℝ} (hL : ContDiff ℝ 1 L) :
    Continuous (saddleGradientMap L) := by
  have hp : Continuous fun z : WithLp 2 (E × F) ↦ (z.fst, z.snd) :=
    (WithLp.continuous_fst 2 E F).prodMk (WithLp.continuous_snd 2 E F)
  exact (WithLp.prod_continuous_toLp 2 E F).comp
    (((continuous_partial_fst hL).comp hp).prodMk (((continuous_partial_snd hL).comp hp).neg))

/-- `F` is monotone relative to `X × Y`: the sum of the four gradient
inequalities of the convex functions `L(·, y)` and `-L(x, ·)`. -/
theorem monotoneRelativeTo_saddleGradientMap {X : Set E} {Y : Set F} (hX : Convex ℝ X)
    (hY : Convex ℝ Y) {L : E × F → ℝ} (hL : ContDiff ℝ 1 L)
    (hconv : ∀ y ∈ Y, ConvexOn ℝ X fun x ↦ L (x, y))
    (hconc : ∀ x ∈ X, ConcaveOn ℝ Y fun y ↦ L (x, y)) :
    MonotoneRelativeTo (saddleGradientMap L) (l2ProdSet X Y) := by
  intro z₀ hz₀ z₁ hz₁
  obtain ⟨hx₀, hy₀⟩ := hz₀
  obtain ⟨hx₁, hy₁⟩ := hz₁
  set x₀ := z₀.fst
  set y₀ := z₀.snd
  set x₁ := z₁.fst
  set y₁ := z₁.snd
  have gx : ∀ x y, HasGradientAt (fun x' ↦ L (x', y)) (gradient (fun x' ↦ L (x', y)) x) x :=
    fun x y ↦ (hasGradientAt_partial_fst hL x y).differentiableAt.hasGradientAt
  have gy : ∀ x y, HasGradientAt (fun y' ↦ -L (x, y')) (-gradient (fun y' ↦ L (x, y')) y) y :=
    fun x y ↦ hasGradientAt_neg' (hasGradientAt_partial_snd hL x y).differentiableAt.hasGradientAt
  have i1 := supporting_inequality_of_convexOn_of_hasGradientAt hX hx₁ (hconv y₁ hy₁) (gx x₁ y₁)
    x₀ hx₀
  have i2 := supporting_inequality_of_convexOn_of_hasGradientAt hX hx₀ (hconv y₀ hy₀) (gx x₀ y₀)
    x₁ hx₁
  have i3 := supporting_inequality_of_convexOn_of_hasGradientAt hY hy₁ (hconc x₁ hx₁).neg
    (gy x₁ y₁) y₀ hy₀
  have i4 := supporting_inequality_of_convexOn_of_hasGradientAt hY hy₀ (hconc x₀ hx₀).neg
    (gy x₀ y₀) y₁ hy₁
  simp only [Pi.neg_apply, inner_neg_left] at i3 i4
  rw [WithLp.prod_inner_apply]
  simp only [saddleGradientMap, WithLp.ofLp_sub, Prod.fst_sub, Prod.snd_sub]
  change 0 ≤ ⟪gradient (fun x ↦ L (x, y₁)) x₁ - gradient (fun x ↦ L (x, y₀)) x₀, x₁ - x₀⟫_ℝ +
    ⟪-gradient (fun y ↦ L (x₁, y)) y₁ - -gradient (fun y ↦ L (x₀, y)) y₀, y₁ - y₀⟫_ℝ
  have e1 : ⟪gradient (fun x ↦ L (x, y₁)) x₁ - gradient (fun x ↦ L (x, y₀)) x₀, x₁ - x₀⟫_ℝ =
      -⟪gradient (fun x ↦ L (x, y₁)) x₁, x₀ - x₁⟫_ℝ -
        ⟪gradient (fun x ↦ L (x, y₀)) x₀, x₁ - x₀⟫_ℝ := by
    simp only [inner_sub_left, inner_sub_right]
    ring
  have e2 : ⟪-gradient (fun y ↦ L (x₁, y)) y₁ - -gradient (fun y ↦ L (x₀, y)) y₀, y₁ - y₀⟫_ℝ =
      ⟪gradient (fun y ↦ L (x₁, y)) y₁, y₀ - y₁⟫_ℝ +
        ⟪gradient (fun y ↦ L (x₀, y)) y₀, y₁ - y₀⟫_ℝ := by
    simp only [inner_sub_left, inner_sub_right, inner_neg_left]
    ring
  rw [e1, e2]
  linarith

theorem mem_singleton_add_iff {G : Type*} [AddCommGroup G] {a v : G} {s : Set G} :
    v ∈ ({a} : Set G) + s ↔ v - a ∈ s := by
  rw [singleton_add, mem_image]
  constructor
  · rintro ⟨b, hb, rfl⟩
    rwa [add_sub_cancel_left]
  · intro h
    exact ⟨v - a, h, add_sub_cancel _ _⟩

/-- The mapping `T = F + N_{X×Y}` of Example 12.50 is the product
`(∇ₓL(x, y) + N_X(x)) × (-∇_yL(x, y) + N_Y(y))`. -/
theorem viMapping_saddleGradientMap_apply (X : Set E) (Y : Set F) (L : E × F → ℝ) (x : E) (y : F) :
    viMapping (l2ProdSet X Y) (saddleGradientMap L) (WithLp.toLp 2 (x, y)) =
      l2ProdSet (({gradient (fun x' ↦ L (x', y)) x} : Set E) + normalCone X x)
        (({-gradient (fun y' ↦ L (x, y')) y} : Set F) + normalCone Y y) := by
  ext v
  rw [mem_viMapping, normalCone_l2ProdSet, mem_l2ProdSet, mem_l2ProdSet, mem_singleton_add_iff,
    mem_singleton_add_iff]
  rfl

/-- The saddle point condition in each variable is a first-order condition of
6.12 for a convex problem. -/
theorem isMinOn_iff_neg_mem_normalCone_of_hasGradientAt {X : Set E} (hX : Convex ℝ X)
    {f : E → ℝ}
    (hf : ConvexOn ℝ X f) {x : E} (hx : x ∈ X) {g : E} (hg : HasGradientAt f g x) :
    IsMinOn f X x ↔ -g ∈ normalCone X x := by
  constructor
  · intro h
    exact IsLocalMinOn.neg_gradient_mem_normalCone hx h.localize hg
  · intro h
    exact isMinOn_of_convexOn_of_firstOrder hX hx hf hg
      ((neg_mem_normalCone_iff_forall_inner_nonneg_of_convex hX hx).1 h)

/-- **Example 12.50 (variational inequalities for saddle points)**: for
nonempty closed convex `X`, `Y` and a `C¹` function `L` convex in `x ∈ X` and
concave in `y ∈ Y`, the mapping `F = (∇ₓL, -∇_yL)` is continuous and monotone
relative to `C = X × Y`, `T = F + N_C` is maximal monotone and equals
`(∇ₓL + N_X) × (-∇_yL + N_Y)`, and `(x̄, ȳ)` is a saddle point exactly when it
solves the variational inequality for `C` and `F`, exactly when
`T(x̄, ȳ) ∋ (0, 0)`, exactly when `∇ₓL(x̄, ȳ) + N_X(x̄) ∋ 0` and
`-∇_yL(x̄, ȳ) + N_Y(ȳ) ∋ 0`. -/
theorem saddle_point_variational_inequality {X : Set E} {Y : Set F} (hXc : IsClosed X)
    (hX : Convex ℝ X) (hXne : X.Nonempty) (hYc : IsClosed Y) (hY : Convex ℝ Y)
    (hYne : Y.Nonempty) {L : E × F → ℝ} (hL : ContDiff ℝ 1 L)
    (hconv : ∀ y ∈ Y, ConvexOn ℝ X fun x ↦ L (x, y))
    (hconc : ∀ x ∈ X, ConcaveOn ℝ Y fun y ↦ L (x, y)) :
    ContinuousOn (saddleGradientMap L) (l2ProdSet X Y) ∧
      MonotoneRelativeTo (saddleGradientMap L) (l2ProdSet X Y) ∧
      SvMaximalMonotone (viMapping (l2ProdSet X Y) (saddleGradientMap L)) ∧
      (∀ x y, viMapping (l2ProdSet X Y) (saddleGradientMap L) (WithLp.toLp 2 (x, y)) =
        l2ProdSet (({gradient (fun x' ↦ L (x', y)) x} : Set E) + normalCone X x)
          (({-gradient (fun y' ↦ L (x, y')) y} : Set F) + normalCone Y y)) ∧
      ∀ xbar ybar,
        ((xbar ∈ X ∧ ybar ∈ Y ∧ (∀ x ∈ X, L (xbar, ybar) ≤ L (x, ybar)) ∧
            ∀ y ∈ Y, L (xbar, y) ≤ L (xbar, ybar)) ↔
          IsVariationalSolution (l2ProdSet X Y) (saddleGradientMap L)
            (WithLp.toLp 2 (xbar, ybar))) ∧
        (IsVariationalSolution (l2ProdSet X Y) (saddleGradientMap L) (WithLp.toLp 2 (xbar, ybar)) ↔
          (0 : WithLp 2 (E × F)) ∈
            viMapping (l2ProdSet X Y) (saddleGradientMap L) (WithLp.toLp 2 (xbar, ybar))) ∧
        ((0 : WithLp 2 (E × F)) ∈
            viMapping (l2ProdSet X Y) (saddleGradientMap L) (WithLp.toLp 2 (xbar, ybar)) ↔
          (0 : E) ∈ ({gradient (fun x' ↦ L (x', ybar)) xbar} : Set E) + normalCone X xbar ∧
            (0 : F) ∈ ({-gradient (fun y' ↦ L (xbar, y')) ybar} : Set F) + normalCone Y ybar) := by
  have hCc : IsClosed (l2ProdSet X Y) := isClosed_l2ProdSet hXc hYc
  have hC : Convex ℝ (l2ProdSet X Y) := by
    intro z₀ hz₀ z₁ hz₁ a b ha hb hab
    exact ⟨hX hz₀.1 hz₁.1 ha hb hab, hY hz₀.2 hz₁.2 ha hb hab⟩
  have hCne : (l2ProdSet X Y).Nonempty := by
    obtain ⟨x, hx⟩ := hXne
    obtain ⟨y, hy⟩ := hYne
    exact ⟨WithLp.toLp 2 (x, y), hx, hy⟩
  have hFc := (continuous_saddleGradientMap hL).continuousOn (s := l2ProdSet X Y)
  have hFm := monotoneRelativeTo_saddleGradientMap hX hY hL hconv hconc
  refine ⟨hFc, hFm, svMaximalMonotone_viMapping hCc hC hCne hFc hFm,
    viMapping_saddleGradientMap_apply X Y L, fun xbar ybar ↦ ⟨?_, ?_, ?_⟩⟩
  · rw [isVariationalSolution_iff_zero_mem_viMapping, viMapping_saddleGradientMap_apply,
      mem_l2ProdSet, mem_singleton_add_iff, mem_singleton_add_iff]
    simp only [WithLp.zero_fst, WithLp.zero_snd, zero_sub, neg_neg]
    constructor
    · rintro ⟨hx, hy, hmin, hmax⟩
      refine ⟨(isMinOn_iff_neg_mem_normalCone_of_hasGradientAt hX (hconv ybar hy) hx
        (hasGradientAt_partial_fst hL xbar ybar).differentiableAt.hasGradientAt).1
          (fun x hx' ↦ hmin x hx'), ?_⟩
      have h := (isMinOn_iff_neg_mem_normalCone_of_hasGradientAt hY (hconc xbar hx).neg hy
        (hasGradientAt_neg'
          (hasGradientAt_partial_snd hL xbar ybar).differentiableAt.hasGradientAt)).1
          (fun y hy' ↦ by simpa using hmax y hy')
      rwa [neg_neg] at h
    · rintro ⟨h₁, h₂⟩
      have hx : xbar ∈ X := by
        by_contra hx
        rw [normalCone_eq_empty hx] at h₁
        exact h₁
      have hy : ybar ∈ Y := by
        by_contra hy
        rw [normalCone_eq_empty hy] at h₂
        exact h₂
      refine ⟨hx, hy, fun x hx' ↦ (isMinOn_iff_neg_mem_normalCone_of_hasGradientAt hX
        (hconv ybar hy) hx
        (hasGradientAt_partial_fst hL xbar ybar).differentiableAt.hasGradientAt).2 h₁ hx',
        fun y hy' ↦ ?_⟩
      have h := (isMinOn_iff_neg_mem_normalCone_of_hasGradientAt hY (hconc xbar hx).neg hy
        (hasGradientAt_neg'
          (hasGradientAt_partial_snd hL xbar ybar).differentiableAt.hasGradientAt)).2
          (by rwa [neg_neg]) hy'
      simp only [Pi.neg_apply, mem_setOf_eq, neg_le_neg_iff] at h
      exact h
  · exact isVariationalSolution_iff_zero_mem_viMapping
  · rw [viMapping_saddleGradientMap_apply, mem_l2ProdSet]
    rfl

end RW
