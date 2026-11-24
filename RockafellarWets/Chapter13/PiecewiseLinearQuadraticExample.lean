/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: A convex piecewise linear-quadratic function with nonconvex `d²f(x̄)`

The discussion after Proposition 13.9 shows that `d²f(x̄)` need not be convex.  We use the
function `f(x) = ½x₀² + ½x₁² + (1 - x₀)|x₁|` on the half-plane `x₀ ≤ 1` (and `∞` elsewhere), a
variant of the printed example with `D` replaced by the half-plane.  There
`f = max{g₊, g₋}` with `g₊(x) = ½(x₀ - x₁)² + x₁` and `g₋(x) = ½(x₀ + x₁)² - x₁`, which agree with
the two quadratic formulas on `x₁ ≥ 0` and `x₁ ≤ 0`.  So `f` is convex and piecewise
linear-quadratic, and `d²f(0)(w) = w₀² + w₁² - 2w₀|w₁|` takes the values `1` at `(1, 0)` and `0` at
`(1, ±1)`.
-/

import RockafellarWets.Chapter13.PiecewiseLinearQuadraticSecondOrder
import Mathlib.Analysis.InnerProductSpace.PiL2

open Filter Set Topology
open scoped InnerProductSpace

namespace RW

noncomputable section

/-- `g₊(x) = ½(x₀ - x₁)² + x₁`. -/
def exampleGPlus (x : EuclideanSpace ℝ (Fin 2)) : ℝ := 1 / 2 * (x 0 - x 1) ^ 2 + x 1

/-- `g₋(x) = ½(x₀ + x₁)² - x₁`. -/
def exampleGMinus (x : EuclideanSpace ℝ (Fin 2)) : ℝ := 1 / 2 * (x 0 + x 1) ^ 2 - x 1

/-- The example after Proposition 13.9: `½x₀² + ½x₁² + (1 - x₀)|x₁|` for `x₀ ≤ 1`, `∞` otherwise. -/
def nonconvexSecondExample (x : EuclideanSpace ℝ (Fin 2)) : EReal :=
  if x 0 ≤ 1 then ((max (exampleGPlus x) (exampleGMinus x) : ℝ) : EReal) else ⊤

theorem nonconvexSecondExample_eq_formula {x : EuclideanSpace ℝ (Fin 2)} (hx : x 0 ≤ 1) :
    max (exampleGPlus x) (exampleGMinus x) =
      1 / 2 * x 0 ^ 2 + 1 / 2 * x 1 ^ 2 + (1 - x 0) * |x 1| := by
  unfold exampleGPlus exampleGMinus
  rcases le_total 0 (x 1) with h | h
  · rw [abs_of_nonneg h, max_eq_left (by nlinarith)]; ring
  · rw [abs_of_nonpos h, max_eq_right (by nlinarith)]; ring

/-- The rank-one symmetric map `x ↦ ⟪a, x⟫ a`. -/
def rankOne (a : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (innerSL ℝ a).smulRight a

theorem rankOne_apply (a x : EuclideanSpace ℝ (Fin 2)) : rankOne a x = ⟪a, x⟫_ℝ • a := rfl

theorem rankOne_symm (a x y : EuclideanSpace ℝ (Fin 2)) :
    ⟪rankOne a x, y⟫_ℝ = ⟪x, rankOne a y⟫_ℝ := by
  simp only [rankOne_apply, real_inner_smul_left, real_inner_smul_right, real_inner_comm a x]
  ring

/-- `e₀ - e₁` and `e₀ + e₁`. -/
def exampleA : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1 - EuclideanSpace.single 1 1
def exampleB : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1

theorem inner_exampleA (x : EuclideanSpace ℝ (Fin 2)) : ⟪exampleA, x⟫_ℝ = x 0 - x 1 := by
  simp [exampleA, inner_sub_left, EuclideanSpace.inner_single_left]

theorem inner_exampleB (x : EuclideanSpace ℝ (Fin 2)) : ⟪exampleB, x⟫_ℝ = x 0 + x 1 := by
  simp [exampleB, inner_add_left, EuclideanSpace.inner_single_left]

/-- The quadratic piece of `g₊`. -/
def examplePiecePlus : QuadraticPiece (EuclideanSpace ℝ (Fin 2)) where
  matrix := rankOne exampleA
  symmetric := rankOne_symm exampleA
  linear := EuclideanSpace.single 1 1
  constant := 0

/-- The quadratic piece of `g₋`. -/
def examplePieceMinus : QuadraticPiece (EuclideanSpace ℝ (Fin 2)) where
  matrix := rankOne exampleB
  symmetric := rankOne_symm exampleB
  linear := -EuclideanSpace.single 1 1
  constant := 0

theorem examplePiecePlus_eval (x : EuclideanSpace ℝ (Fin 2)) :
    examplePiecePlus.eval x = exampleGPlus x := by
  simp only [QuadraticPiece.eval, examplePiecePlus, rankOne_apply, real_inner_smul_right,
    real_inner_comm exampleA x, inner_exampleA, EuclideanSpace.inner_single_left, exampleGPlus]
  simp
  ring

theorem examplePieceMinus_eval (x : EuclideanSpace ℝ (Fin 2)) :
    examplePieceMinus.eval x = exampleGMinus x := by
  simp only [QuadraticPiece.eval, examplePieceMinus, rankOne_apply, real_inner_smul_right,
    real_inner_comm exampleB x, inner_exampleB, inner_neg_left, EuclideanSpace.inner_single_left,
    exampleGMinus]
  simp
  ring

/-- The two pieces `{x₀ ≤ 1, x₁ ≥ 0}` and `{x₀ ≤ 1, x₁ ≤ 0}`. -/
def examplePieces : Fin 2 → Set (EuclideanSpace ℝ (Fin 2)) :=
  ![{x | x 0 ≤ 1} ∩ {x | -x 1 ≤ 0}, {x | x 0 ≤ 1} ∩ {x | x 1 ≤ 0}]

theorem isPolyhedral_examplePieces (i : Fin 2) : IsPolyhedral (examplePieces i) := by
  have h0 : IsPolyhedral {x : EuclideanSpace ℝ (Fin 2) | x 0 ≤ 1} := by
    simpa using isPolyhedral_linearHalfspace (EuclideanSpace.proj (0 : Fin 2) :
      EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) 1
  have h1 : IsPolyhedral {x : EuclideanSpace ℝ (Fin 2) | -x 1 ≤ 0} := by
    simpa using isPolyhedral_linearHalfspace (-(EuclideanSpace.proj (1 : Fin 2) :
      EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)) 0
  have h2 : IsPolyhedral {x : EuclideanSpace ℝ (Fin 2) | x 1 ≤ 0} := by
    simpa using isPolyhedral_linearHalfspace (EuclideanSpace.proj (1 : Fin 2) :
      EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) 0
  fin_cases i
  · exact h0.inter h1
  · exact h0.inter h2

/-- The example is piecewise linear-quadratic. -/
theorem isPiecewiseLinearQuadratic_nonconvexSecondExample :
    IsPiecewiseLinearQuadratic nonconvexSecondExample := by
  refine ⟨2, examplePieces, ![examplePiecePlus, examplePieceMinus], isPolyhedral_examplePieces,
    ?_, ?_⟩
  · ext x
    simp only [mem_effectiveDomain_iff, nonconvexSecondExample, mem_iUnion, Fin.exists_fin_two,
      examplePieces, Matrix.cons_val_zero, Matrix.cons_val_one, mem_inter_iff, mem_setOf_eq]
    split_ifs with h
    · simp only [EReal.coe_lt_top, true_iff, h, true_and]
      rcases le_total 0 (x 1) with h' | h'
      · left; linarith
      · right; exact h'
    · simp [h]
  · intro i x hx
    fin_cases i
    · obtain ⟨h0, h1⟩ := hx
      simp only [mem_setOf_eq] at h0 h1
      simp only [nonconvexSecondExample, if_pos h0, Fin.zero_eta, Matrix.cons_val_zero,
        examplePiecePlus_eval]
      congr 1
      exact max_eq_left (by unfold exampleGPlus exampleGMinus; nlinarith)
    · obtain ⟨h0, h1⟩ := hx
      simp only [mem_setOf_eq] at h0 h1
      simp only [nonconvexSecondExample, if_pos h0, Fin.mk_one, Matrix.cons_val_one,
        Matrix.cons_val_zero, examplePieceMinus_eval]
      congr 1
      exact max_eq_right (by unfold exampleGPlus exampleGMinus; nlinarith)

theorem exampleGPlus_convex {x y : EuclideanSpace ℝ (Fin 2)} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : exampleGPlus (a • x + b • y) ≤ a * exampleGPlus x + b * exampleGPlus y := by
  simp only [exampleGPlus, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hb' : b = 1 - a := by linarith
  subst hb'
  nlinarith [sq_nonneg ((x 0 - x 1) - (y 0 - y 1)), mul_nonneg ha hb]

theorem exampleGMinus_convex {x y : EuclideanSpace ℝ (Fin 2)} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) :
    exampleGMinus (a • x + b • y) ≤ a * exampleGMinus x + b * exampleGMinus y := by
  simp only [exampleGMinus, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hb' : b = 1 - a := by linarith
  subst hb'
  nlinarith [sq_nonneg ((x 0 + x 1) - (y 0 + y 1)), mul_nonneg ha hb]

/-- The example is convex. -/
theorem convex_epigraph_nonconvexSecondExample : Convex ℝ (epigraph nonconvexSecondExample) := by
  rintro ⟨x, α⟩ hx ⟨y, β⟩ hy a b ha hb hab
  change (α : EReal) ≥ nonconvexSecondExample x at hx
  change (β : EReal) ≥ nonconvexSecondExample y at hy
  have hx0 : x 0 ≤ 1 := by
    by_contra h; simp [nonconvexSecondExample, h] at hx
  have hy0 : y 0 ≤ 1 := by
    by_contra h; simp [nonconvexSecondExample, h] at hy
  simp only [nonconvexSecondExample, if_pos hx0, if_pos hy0, ge_iff_le, EReal.coe_le_coe_iff,
    max_le_iff] at hx hy
  show ((a * α + b * β : ℝ) : EReal) ≥ nonconvexSecondExample (a • x + b • y)
  have hz0 : (a • x + b • y) 0 ≤ 1 := by
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    nlinarith
  simp only [nonconvexSecondExample, if_pos hz0, ge_iff_le, EReal.coe_le_coe_iff, max_le_iff]
  constructor
  · calc exampleGPlus (a • x + b • y) ≤ a * exampleGPlus x + b * exampleGPlus y :=
          exampleGPlus_convex ha hb hab
      _ ≤ a * α + b * β := by nlinarith [hx.1, hy.1]
  · calc exampleGMinus (a • x + b • y) ≤ a * exampleGMinus x + b * exampleGMinus y :=
          exampleGMinus_convex ha hb hab
      _ ≤ a * α + b * β := by nlinarith [hx.2, hy.2]

theorem nonconvexSecondExample_zero : nonconvexSecondExample 0 = 0 := by
  simp [nonconvexSecondExample, exampleGPlus, exampleGMinus]

theorem zero_mem_effectiveDomain_nonconvexSecondExample :
    (0 : EuclideanSpace ℝ (Fin 2)) ∈ effectiveDomain nonconvexSecondExample := by
  rw [mem_effectiveDomain_iff, nonconvexSecondExample_zero]; exact EReal.zero_lt_top

/-- The value of `d²f(0)` along a direction where `f(τw) = α τ + β τ²` for small `τ > 0`. -/
theorem secondSubderivativeAt_nonconvexSecondExample_of_ray {w : EuclideanSpace ℝ (Fin 2)}
    {α β : ℝ}
    (hray : ∀ᶠ τ in 𝓝[>] (0 : ℝ),
      nonconvexSecondExample (τ • w) = ((α * τ + β * τ ^ 2 : ℝ) : EReal)) :
    secondSubderivativeAt nonconvexSecondExample 0 w = ((2 * β : ℝ) : EReal) := by
  have hf := isPiecewiseLinearQuadratic_nonconvexSecondExample
  have hx := zero_mem_effectiveDomain_nonconvexSecondExample
  have hc0 : nonconvexSecondExample 0 = ((0 : ℝ) : EReal) := by
    rw [nonconvexSecondExample_zero]; rfl
  -- the subderivative along the ray
  have hd : subderivative nonconvexSecondExample 0 w = (α : EReal) := by
    refine tendsto_nhds_unique (hf.hasOneSidedDirDeriv hx w).2.2 ?_
    have hr : Tendsto (fun τ : ℝ ↦ α + β * τ) (𝓝[>] (0 : ℝ)) (𝓝 α) := by
      have : Tendsto (fun τ : ℝ ↦ α + β * τ) (𝓝 (0 : ℝ)) (𝓝 (α + β * 0)) :=
        (continuous_const.add (continuous_const.mul continuous_id)).tendsto 0
      rw [mul_zero, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine ((continuous_coe_real_ereal.tendsto _).comp hr).congr' ?_
    filter_upwards [hray, self_mem_nhdsWithin] with τ hτ hτpos
    have hτ' : (0 : ℝ) < τ := hτpos
    rw [Function.comp_apply, differenceQuotient_eq_coe hc0 (by rw [zero_add]; exact hτ)]
    congr 1
    field_simp
    ring
  have hlim := ((piecewise_linear_quadratic_second_order hf
    convex_epigraph_nonconvexSecondExample hx).1.2.2 w).2
  refine tendsto_nhds_unique hlim (tendsto_const_nhds.congr' ?_)
  filter_upwards [hray, self_mem_nhdsWithin] with τ hτ hτpos
  have hτ' : (0 : ℝ) < τ := hτpos
  rw [secondDifferenceQuotientAt, zero_add, hτ, hc0, hd, ← EReal.coe_sub, ← EReal.coe_mul,
    ← EReal.coe_neg, infAddition_coe_right, ← EReal.coe_add, ← EReal.coe_mul]
  congr 1
  field_simp
  ring

theorem isProper_nonconvexSecondExample : IsProper nonconvexSecondExample := by
  refine ⟨⟨0, zero_mem_effectiveDomain_nonconvexSecondExample⟩, fun x ↦ ?_⟩
  unfold nonconvexSecondExample
  split_ifs
  · exact EReal.bot_lt_coe _
  · exact bot_lt_top

/-- **Proposition 13.9**, "not necessarily convex": the example is proper, convex and piecewise
linear-quadratic, but `d²f(0)` is not convex, with `d²f(0)(1, 0) = 1` and `d²f(0)(1, ±1) = 0`. -/
theorem not_convex_secondSubderivativeAt_nonconvexSecondExample :
    IsProper nonconvexSecondExample ∧ Convex ℝ (epigraph nonconvexSecondExample) ∧
    IsPiecewiseLinearQuadratic nonconvexSecondExample ∧
    secondSubderivativeAt nonconvexSecondExample 0 (EuclideanSpace.single 0 1) = 1 ∧
    secondSubderivativeAt nonconvexSecondExample 0 exampleB = 0 ∧
    secondSubderivativeAt nonconvexSecondExample 0 exampleA = 0 ∧
    ¬ Convex ℝ (epigraph (secondSubderivativeAt nonconvexSecondExample 0)) := by
  have hsmall : ∀ᶠ τ in 𝓝[>] (0 : ℝ), 0 < τ ∧ τ < 1 := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds one_pos)] with τ h1 h2
    exact ⟨h1, h2⟩
  have h0 : secondSubderivativeAt nonconvexSecondExample 0 (EuclideanSpace.single 0 1) = 1 := by
    have := secondSubderivativeAt_nonconvexSecondExample_of_ray (α := 0) (β := 1 / 2)
      (w := EuclideanSpace.single 0 1) (by
        filter_upwards [hsmall] with τ ⟨h1, h2⟩
        have hle : (τ • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) 0 ≤ 1 := by simp; linarith
        rw [nonconvexSecondExample, if_pos hle]
        congr 1
        simp [exampleGPlus, exampleGMinus])
    rw [this]; norm_num
  have hB : secondSubderivativeAt nonconvexSecondExample 0 exampleB = 0 := by
    have := secondSubderivativeAt_nonconvexSecondExample_of_ray (α := 1) (β := 0)
      (w := exampleB) (by
        filter_upwards [hsmall] with τ ⟨h1, h2⟩
        have hle : (τ • exampleB) 0 ≤ 1 := by simp [exampleB]; linarith
        rw [nonconvexSecondExample, if_pos hle]
        congr 1
        simp only [exampleGPlus, exampleGMinus, exampleB]
        simp
        nlinarith)
    rw [this]; norm_num
  have hA : secondSubderivativeAt nonconvexSecondExample 0 exampleA = 0 := by
    have := secondSubderivativeAt_nonconvexSecondExample_of_ray (α := 1) (β := 0)
      (w := exampleA) (by
        filter_upwards [hsmall] with τ ⟨h1, h2⟩
        have hle : (τ • exampleA) 0 ≤ 1 := by simp [exampleA]; linarith
        rw [nonconvexSecondExample, if_pos hle]
        congr 1
        simp only [exampleGPlus, exampleGMinus, exampleA]
        simp
        nlinarith)
    rw [this]; norm_num
  refine ⟨isProper_nonconvexSecondExample, convex_epigraph_nonconvexSecondExample,
    isPiecewiseLinearQuadratic_nonconvexSecondExample, h0, hB, hA, fun hconv ↦ ?_⟩
  have hBm : (exampleB, (0 : ℝ)) ∈ epigraph (secondSubderivativeAt nonconvexSecondExample 0) := by
    show ((0 : ℝ) : EReal) ≥ _; rw [hB]; rfl
  have hAm : (exampleA, (0 : ℝ)) ∈ epigraph (secondSubderivativeAt nonconvexSecondExample 0) := by
    show ((0 : ℝ) : EReal) ≥ _; rw [hA]; rfl
  have hmid := hconv hBm hAm (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  have he : (1 / 2 : ℝ) • (exampleB, (0 : ℝ)) + (1 / 2 : ℝ) • (exampleA, (0 : ℝ)) =
      (EuclideanSpace.single 0 1, (0 : ℝ)) := by
    ext i
    · fin_cases i <;> norm_num [exampleA, exampleB]
    · simp
  rw [he] at hmid
  have hmid' : secondSubderivativeAt nonconvexSecondExample 0 (EuclideanSpace.single 0 1) ≤
      ((0 : ℝ) : EReal) := hmid
  rw [h0] at hmid'
  exact absurd hmid' (by norm_num)

end

end RW
