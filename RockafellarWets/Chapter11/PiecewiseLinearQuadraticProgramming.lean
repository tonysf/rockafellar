/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 11: linear and extended linear-quadratic programming

**Example 11.43**:
* when `k` and `h` are proper, convex and piecewise linear-quadratic, the Fenchel scheme of
  11.41 fits Theorem 11.42: if either optimal value is finite, both are finite, equal and attained,
  and the optimal pairs are characterized by `ȳ ∈ ∂h(b - Ax̄)`, `A*ȳ - c ∈ ∂k(x̄)`
  (`piecewiseLinearQuadratic_fenchel_duality`);
* extended linear-quadratic programming is the case `k = δ_X + j_C`, `h = θ_{Y,B}`, whose dual
  objective is `⟪b, y⟫ - ½⟪y, By⟫ - θ_{X,C}(A*y - c)` on `Y` (`fenchelDual_elqp`,
  `elqp_duality`);
* for `C = 0`, `B = 0` and cones `X`, `Y` these are the linear programming problems
  `min ⟪c, x⟫` over `x ∈ X`, `b - Ax ∈ Y*` and `max ⟪b, y⟫` over `y ∈ Y`, `A*y - c ∈ X*`
  (`fenchelPrimal_lp`, `fenchelDual_lp`), which for nonnegative orthants read
  `x ≥ 0, Ax ≥ b` and `y ≥ 0, A*y ≤ c` (`fenchelPrimal_lp_orthant`, `fenchelDual_lp_orthant`).
-/

import RockafellarWets.Chapter11.PiecewiseLinearQuadraticOptimization
import RockafellarWets.Chapter11.PiecewiseLinearQuadraticPenalties
import RockafellarWets.Chapter11.FenchelDuality
import RockafellarWets.Chapter11.SupportConjugates

open Set Classical
open scoped InnerProductSpace

namespace RW

variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]

/-- A linear form `x ↦ ⟪c, x⟫` is piecewise linear-quadratic. -/
theorem isPiecewiseLinearQuadratic_inner (c : E) :
    IsPiecewiseLinearQuadratic (fun x : E ↦ ((⟪c, x⟫_ℝ : ℝ) : EReal)) := by
  refine IsPiecewiseLinear.isPiecewiseLinearQuadratic
    ⟨1, fun _ ↦ univ, fun _ ↦ c, fun _ ↦ 0, fun _ ↦ IsPolyhedral.univ, ?_, ?_⟩
  · ext x
    simp [effectiveDomain]
  · intro _ x _
    simp

/-- The perturbation integrand of the Fenchel scheme is piecewise linear-quadratic when `k` and
`h` are (10.22). -/
theorem isPiecewiseLinearQuadratic_fenchelIntegrand {k : E → EReal} {h : P → EReal}
    (A : E →L[ℝ] P) (b : P) (c : E) (hk : IsPiecewiseLinearQuadratic k)
    (hh : IsPiecewiseLinearQuadratic h) :
    IsPiecewiseLinearQuadratic (fenchelIntegrand k h A b c) := by
  have h1 : IsPiecewiseLinearQuadratic
      (fun q : WithLp 2 (E × P) ↦ ((⟪c, q.fst⟫_ℝ : ℝ) : EReal)) := by
    simpa using (isPiecewiseLinearQuadratic_inner c).compAffine (WithLp.fstL 2 ℝ E P) 0
  have h2 : IsPiecewiseLinearQuadratic (fun q : WithLp 2 (E × P) ↦ k q.fst) := by
    simpa using hk.compAffine (WithLp.fstL 2 ℝ E P) 0
  have h3 : IsPiecewiseLinearQuadratic (fun q : WithLp 2 (E × P) ↦ h (b - A q.fst + q.snd)) := by
    have h := hh.compAffine (-(A.comp (WithLp.fstL 2 ℝ E P)) + WithLp.sndL 2 ℝ E P) b
    convert h using 2 with q
    congr 1
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.comp_apply, WithLp.fstL_apply, WithLp.sndL_apply]
    abel
  exact (h1.add h2).add h3

section FenchelPLQ

variable {k : E → EReal} {h : P → EReal} (A : E →L[ℝ] P) (b : P) (c : E)
  (hk : IsPiecewiseLinearQuadratic k) (hkp : IsProper k) (hkc : Convex ℝ (epigraph k))
  (hh : IsPiecewiseLinearQuadratic h) (hhp : IsProper h) (hhc : Convex ℝ (epigraph h))
include hk hkp hkc hh hhp hhc

/-- **Example 11.43**, the Fenchel scheme with piecewise linear-quadratic `k` and `h` fits
Theorem 11.42. -/
theorem piecewiseLinearQuadratic_fenchel_duality
    (hfin : (∃ a : ℝ, (⨅ x, fenchelPrimal k h A b c x) = a) ∨
      ∃ a : ℝ, (⨆ y, fenchelDual k h A b c y) = a) :
    (∃ a : ℝ, (⨅ x, fenchelPrimal k h A b c x) = a ∧ (⨆ y, fenchelDual k h A b c y) = a) ∧
      (argmin (fenchelPrimal k h A b c)).Nonempty ∧
      (argmax (fenchelDual k h A b c)).Nonempty ∧
      ∀ x y, (x ∈ argmin (fenchelPrimal k h A b c) ∧ y ∈ argmax (fenchelDual k h A b c)) ↔
        (y ∈ subdifferential h (b - A x) ∧ A.adjoint y - c ∈ subdifferential k x) := by
  have hkl := hk.lowerSemicontinuous
  have hhl := hh.lowerSemicontinuous
  obtain ⟨hfp, -, hfc, hφ, hψ, -, -⟩ := fenchel_scheme_fits_duality A b c hkp hkl hkc hhp hhl hhc
  have hfplq := isPiecewiseLinearQuadratic_fenchelIntegrand A b c hk hh
  have hfin' : (∃ a : ℝ, (⨅ x, primalObjective (fenchelIntegrand k h A b c) x) = a) ∨
      ∃ a : ℝ, (⨆ y, dualObjective (fenchelIntegrand k h A b c) y) = a := by
    rw [hφ, hψ]
    exact hfin
  obtain ⟨⟨a, ha₁, ha₂⟩, hφne, hψne, -⟩ :=
    piecewiseLinearQuadratic_optimization hfplq hfp hfc hfin'
  rw [hφ] at ha₁ hφne
  rw [hψ] at ha₂ hψne
  refine ⟨⟨a, ha₁, ha₂⟩, hφne, hψne, fun x y ↦ ?_⟩
  rw [← (fenchel_optimality A b c hkp hkl hkc hhp hhl hhc x y).1]
  exact ⟨fun h ↦ ⟨h.1, h.2, ha₁.trans ha₂.symm⟩, fun h ↦ ⟨h.1, h.2.1⟩⟩

end FenchelPLQ

section ELQP

variable {X : Set E} {Y : Set P} {C : E →L[ℝ] E} {B : P →L[ℝ] P}
  (hX : IsPolyhedral X) (hXne : X.Nonempty) (hC : ∀ x y, ⟪C x, y⟫_ℝ = ⟪x, C y⟫_ℝ)
  (hCpos : ∀ x, 0 ≤ ⟪x, C x⟫_ℝ)
  (hY : IsPolyhedral Y) (hYne : Y.Nonempty) (hB : ∀ x y, ⟪B x, y⟫_ℝ = ⟪x, B y⟫_ℝ)
  (hBpos : ∀ y, 0 ≤ ⟪y, B y⟫_ℝ)

include hY hYne hB hBpos in
/-- **Example 11.43**, the extended linear-quadratic dual objective
`ψ(y) = ⟪b, y⟫ - (δ_Y + j_B)(y) - θ_{X,C}(A*y - c)`. -/
theorem fenchelDual_elqp (A : E →L[ℝ] P) (b : P) (c : E) :
    fenchelDual (plqPenaltyPrimal X C) (plqPenalty Y B) A b c = fun y ↦
      (⟪b, y⟫_ℝ : EReal) - plqPenaltyPrimal Y B y - plqPenalty X C (A.adjoint y - c) := by
  have hplq := isPiecewiseLinearQuadratic_plqPenaltyPrimal hY hB
  have hp := isProper_plqPenaltyPrimal (B := B) hYne
  have hc := convex_epigraph_plqPenaltyPrimal hY.convex hB hBpos
  funext y
  simp only [fenchelDual]
  rw [← plqPenalty_eq_fenchelConjugate X C, plqPenalty_eq_fenchelConjugate Y B,
    fenchelConjugate_fenchelConjugate_eq hp hplq.lowerSemicontinuous hc]

include hX hXne hC hCpos hY hYne hB hBpos in
/-- **Example 11.43**, extended linear-quadratic programming: minimize
`⟪c, x⟫ + ½⟪x, Cx⟫ + θ_{Y,B}(b - Ax)` over `X` and maximize
`⟪b, y⟫ - ½⟪y, By⟫ - θ_{X,C}(A*y - c)` over `Y`.  If either optimal value is finite, both are
finite, equal and attained, with optimal pairs characterized by the subgradient conditions. -/
theorem elqp_duality (A : E →L[ℝ] P) (b : P) (c : E)
    (hfin : (∃ a : ℝ, (⨅ x, fenchelPrimal (plqPenaltyPrimal X C) (plqPenalty Y B) A b c x) = a) ∨
      ∃ a : ℝ, (⨆ y, fenchelDual (plqPenaltyPrimal X C) (plqPenalty Y B) A b c y) = a) :
    (∃ a : ℝ, (⨅ x, fenchelPrimal (plqPenaltyPrimal X C) (plqPenalty Y B) A b c x) = a ∧
        (⨆ y, fenchelDual (plqPenaltyPrimal X C) (plqPenalty Y B) A b c y) = a) ∧
      (argmin (fenchelPrimal (plqPenaltyPrimal X C) (plqPenalty Y B) A b c)).Nonempty ∧
      (argmax (fenchelDual (plqPenaltyPrimal X C) (plqPenalty Y B) A b c)).Nonempty ∧
      ∀ x y, (x ∈ argmin (fenchelPrimal (plqPenaltyPrimal X C) (plqPenalty Y B) A b c) ∧
          y ∈ argmax (fenchelDual (plqPenaltyPrimal X C) (plqPenalty Y B) A b c)) ↔
        (y ∈ subdifferential (plqPenalty Y B) (b - A x) ∧
          A.adjoint y - c ∈ subdifferential (plqPenaltyPrimal X C) x) := by
  obtain ⟨-, -, -, hθ⟩ := plqPenalty_properties hY hYne hB hBpos
  obtain ⟨hθp, -, hθc, -⟩ := plqPenalty_properties hY hYne hB hBpos
  exact piecewiseLinearQuadratic_fenchel_duality A b c
    (isPiecewiseLinearQuadratic_plqPenaltyPrimal hX hC) (isProper_plqPenaltyPrimal hXne)
    (convex_epigraph_plqPenaltyPrimal hX.convex hC hCpos) hθ hθp hθc hfin

end ELQP

section LP

omit [FiniteDimensional ℝ E] in
theorem plqPenaltyPrimal_zero (X : Set E) : plqPenaltyPrimal X 0 = indicatorVA X := by
  funext x
  simp [plqPenaltyPrimal]

omit [FiniteDimensional ℝ P] in
theorem plqPenalty_zero_cone {Y : Set P} (hYc : IsCone Y) :
    plqPenalty Y 0 = indicatorVA (polarCone Y) := by
  rw [plqPenalty_zero, supportFunction_cone hYc]

variable {X : Set E} {Y : Set P} (hXc : IsCone X) (hY : IsPolyhedral Y) (hYc : IsCone Y)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
include hYc in
/-- **Example 11.43**, the linear programming primal problem:
`⟪c, x⟫` subject to `x ∈ X` and `b - Ax ∈ Y*`. -/
theorem fenchelPrimal_lp (A : E →L[ℝ] P) (b : P) (c : E) (x : E) :
    fenchelPrimal (plqPenaltyPrimal X 0) (plqPenalty Y 0) A b c x =
      if x ∈ X ∧ b - A x ∈ polarCone Y then (⟪c, x⟫_ℝ : EReal) else ⊤ := by
  rw [plqPenaltyPrimal_zero, plqPenalty_zero_cone hYc]
  simp only [fenchelPrimal, indicatorVA]
  by_cases hx : x ∈ X <;> by_cases hy : b - A x ∈ polarCone Y <;> simp [hx, hy]

include hXc hY hYc in
/-- **Example 11.43**, the linear programming dual problem:
`⟪b, y⟫` subject to `y ∈ Y` and `A*y - c ∈ X*`. -/
theorem fenchelDual_lp (A : E →L[ℝ] P) (b : P) (c : E) (y : P) :
    fenchelDual (plqPenaltyPrimal X 0) (plqPenalty Y 0) A b c y =
      if y ∈ Y ∧ A.adjoint y - c ∈ polarCone X then (⟪b, y⟫_ℝ : EReal) else ⊥ := by
  rw [plqPenaltyPrimal_zero, plqPenalty_zero_cone hYc]
  simp only [fenchelDual]
  rw [fenchelConjugate_indicatorVA_cone hXc, fenchelConjugate_indicatorVA_cone (isCone_polarCone Y),
    polarCone_bipolar_eq_self hY.isClosed hY.convex hYc]
  simp only [indicatorVA]
  by_cases hy : y ∈ Y <;> by_cases hx : A.adjoint y - c ∈ polarCone X <;> simp [hx, hy]

end LP

section Orthant

variable {n m : ℕ}

/-- The nonnegative orthant of `ℝⁿ`. -/
def nonnegOrthant (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) := {x | ∀ i, 0 ≤ x i}

theorem isCone_nonnegOrthant : IsCone (nonnegOrthant n) :=
  ⟨fun i ↦ le_rfl, fun x hx c hc i ↦ by
    simpa using mul_nonneg hc.le (hx i)⟩

theorem polarCone_nonnegOrthant :
    polarCone (nonnegOrthant n) = {v | ∀ i, v i ≤ 0} := by
  ext v
  constructor
  · intro hv i
    have h := hv (EuclideanSpace.single i 1) (fun j ↦ by
      by_cases hij : j = i <;> simp [EuclideanSpace.single_apply, hij])
    simpa [EuclideanSpace.inner_single_right] using h
  · intro hv x hx
    rw [PiLp.inner_apply]
    exact Finset.sum_nonpos fun i _ ↦ by
      simpa [mul_comm] using mul_nonpos_of_nonneg_of_nonpos (hx i) (hv i)

theorem isPolyhedral_nonnegOrthant : IsPolyhedral (nonnegOrthant n) := by
  have h := isHPolyhedral_setOf_inner_le (fun i : Fin n ↦ -EuclideanSpace.single i (1 : ℝ))
    (fun _ ↦ 0)
  convert h.isPolyhedral using 1
  ext x
  simp [nonnegOrthant, EuclideanSpace.inner_single_left]

/-- **Example 11.43**, orthant form of the linear programming primal problem:
`⟪c, x⟫` subject to `x ≥ 0` and `Ax ≥ b`. -/
theorem fenchelPrimal_lp_orthant
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (b : EuclideanSpace ℝ (Fin m))
    (c x : EuclideanSpace ℝ (Fin n)) :
    fenchelPrimal (plqPenaltyPrimal (nonnegOrthant n) 0) (plqPenalty (nonnegOrthant m) 0) A b c x =
      if (∀ i, 0 ≤ x i) ∧ ∀ j, b j ≤ A x j then (⟪c, x⟫_ℝ : EReal) else ⊤ := by
  rw [fenchelPrimal_lp isCone_nonnegOrthant, polarCone_nonnegOrthant]
  congr 1
  simp [nonnegOrthant]

/-- **Example 11.43**, orthant form of the linear programming dual problem:
`⟪b, y⟫` subject to `y ≥ 0` and `A*y ≤ c`. -/
theorem fenchelDual_lp_orthant
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (b : EuclideanSpace ℝ (Fin m))
    (c : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)) :
    fenchelDual (plqPenaltyPrimal (nonnegOrthant n) 0) (plqPenalty (nonnegOrthant m) 0) A b c y =
      if (∀ j, 0 ≤ y j) ∧ ∀ i, A.adjoint y i ≤ c i then (⟪b, y⟫_ℝ : EReal) else ⊥ := by
  rw [fenchelDual_lp isCone_nonnegOrthant isPolyhedral_nonnegOrthant isCone_nonnegOrthant,
    polarCone_nonnegOrthant]
  congr 1
  simp [nonnegOrthant]

end Orthant

end RW
