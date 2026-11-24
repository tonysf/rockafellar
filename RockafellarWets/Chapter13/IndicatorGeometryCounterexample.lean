/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: the printed qualification of Exercise 13.17 is too weak

Exercise 13.17 prints the qualification `y ∈ N_D(F(x̄)), ∇(yF)(x̄) = 0 ⇒ y = 0` for
`C = {x ∈ X | F(x) ∈ D}`. Its guide represents `δ_C = δ_{X × D} ∘ (I, F)`, for which the
qualification of Theorem 13.14 reads `y ∈ N_D(F(x̄)), -∇(yF)(x̄) ∈ N_X(x̄) ⇒ y = 0`, the form
used in `indicators_and_geometry` (and printed in 13.25). In the plane take the line
`X = {x | x₁ = 0}`, `D = (-∞, 0]` and `F(x) = x₀² - x₁`. Then `C = {0}`, the printed qualification
holds at `0`, and `N_C(0)` is the whole plane, yet `e₀ - ∇(yF)(0) ∉ N_X(0)` for every `y ≥ 0`.
-/

import RockafellarWets.Chapter13.IndicatorSecondOrder

open Filter Set Topology
open scoped InnerProductSpace RealInnerProductSpace

namespace RW
namespace IndicatorGeometryCounterexample

/-- The line `X = {x | x₁ = 0}` in the plane. -/
def X : Set (EuclideanSpace ℝ (Fin 2)) := {x | x 1 = 0}

/-- The half-line `D = (-∞, 0]`. -/
def D : Set ℝ := Iic 0

/-- The mapping `F(x) = x₀² - x₁`. -/
noncomputable def F (x : EuclideanSpace ℝ (Fin 2)) : ℝ := x 0 ^ 2 - x 1

/-- The first axis direction. -/
noncomputable def e₀ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1

theorem isPolyhedral_X : IsPolyhedral X := by
  have h := (isPolyhedral_linearHalfspace (EuclideanSpace.proj (1 : Fin 2) :
      EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) 0).inter
    (isPolyhedral_linearHalfspace (-(EuclideanSpace.proj (1 : Fin 2) :
      EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)) 0)
  convert h using 1
  ext x
  simp only [X, mem_setOf_eq, mem_inter_iff, ContinuousLinearMap.neg_apply]
  simp only [PiLp.proj_apply]
  constructor
  · intro h; rw [h]; simp
  · rintro ⟨h1, h2⟩; linarith

theorem isPolyhedral_D : IsPolyhedral D := by
  have h := isPolyhedral_linearHalfspace (ContinuousLinearMap.id ℝ ℝ) 0
  convert h using 1

theorem contDiff_F : ContDiff ℝ 2 F := by
  unfold F
  have h0 := (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff
    (n := 2)
  have h1 := (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff
    (n := 2)
  exact (h0.pow 2).sub h1

theorem fderiv_F : fderiv ℝ F 0 = -(EuclideanSpace.proj (1 : Fin 2) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) := by
  have h0 := (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).hasFDerivAt
    (x := 0)
  have h1 := (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).hasFDerivAt
    (x := 0)
  have h := (h0.mul h0).sub h1
  refine HasFDerivAt.fderiv ?_
  convert h using 1
  · funext x; simp [F, sq]
  · ext u; simp

theorem inner_adjoint_fderiv_F (y : ℝ) (u : EuclideanSpace ℝ (Fin 2)) :
    ⟪(fderiv ℝ F 0).adjoint y, u⟫_ℝ = -(y * u 1) := by
  rw [ContinuousLinearMap.adjoint_inner_left, fderiv_F]
  simp [mul_comm]

theorem C_eq : {x | x ∈ X ∧ F x ∈ D} = ({0} : Set (EuclideanSpace ℝ (Fin 2))) := by
  ext x
  simp only [mem_setOf_eq, X, D, F, mem_Iic, mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : x 0 ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
    have h0 : x 0 = 0 := pow_eq_zero_iff two_ne_zero |>.1 h3
    ext i
    fin_cases i <;> simp [h0, h1]
  · rintro rfl
    simp

/-- **Exercise 13.17**, the printed qualification is too weak. Here `X = {x | x₁ = 0}` and
`D = (-∞, 0]` are polyhedral, `F(x) = x₀² - x₁` is `C²`, and `x̄ = 0` satisfies the printed
qualification `y ∈ N_D(F(x̄)), ∇(yF)(x̄) = 0 ⇒ y = 0`, while `y = 1` violates the qualification
`y ∈ N_D(F(x̄)), -∇(yF)(x̄) ∈ N_X(x̄) ⇒ y = 0` used in `indicators_and_geometry`. The set
`C = {x ∈ X | F(x) ∈ D}` is `{0}`, so `N_C(0)` is the whole plane, but the first axis vector
`e₀ ∈ N_C(0)` admits no `y ∈ N_D(F(x̄))` with `e₀ - ∇(yF)(x̄) ∈ N_X(x̄)`: the printed
characterization of `N_C(x̄)` fails, and the printed formula for `d²δ_C(x̄ ∣ e₀)` would be a
maximum over the empty set. -/
theorem printed_qualification_counterexample :
    IsPolyhedral X ∧ IsPolyhedral D ∧ ContDiff ℝ 2 F ∧ (0 : EuclideanSpace ℝ (Fin 2)) ∈ X ∧
      F 0 ∈ D ∧
      (∀ y ∈ normalCone D (F 0), (fderiv ℝ F 0).adjoint y = 0 → y = 0) ∧
      (∃ y ∈ normalCone D (F 0), y ≠ 0 ∧ -((fderiv ℝ F 0).adjoint y) ∈ normalCone X 0) ∧
      e₀ ∈ normalCone {x | x ∈ X ∧ F x ∈ D} 0 ∧
      ¬ ∃ y ∈ normalCone D (F 0), e₀ - (fderiv ℝ F 0).adjoint y ∈ normalCone X 0 := by
  have hX0 : (0 : EuclideanSpace ℝ (Fin 2)) ∈ X := by simp [X]
  have hF0 : F 0 = 0 := by simp [F]
  have hD0 : F 0 ∈ D := by rw [hF0]; simp [D]
  have hNX : normalCone X 0 = {u | ∀ z ∈ X, ⟪u, z - 0⟫_ℝ ≤ 0} :=
    normalCone_eq_of_convex isPolyhedral_X.convex hX0
  refine ⟨isPolyhedral_X, isPolyhedral_D, contDiff_F, hX0, hD0, ?_, ?_, ?_, ?_⟩
  · intro y _ hy
    have h := inner_adjoint_fderiv_F y (EuclideanSpace.single 1 1)
    rw [hy, inner_zero_left] at h
    simpa using h
  · refine ⟨1, ?_, one_ne_zero, ?_⟩
    · rw [hF0, show D = Iic 0 from rfl, normalCone_eq_of_convex (convex_Iic 0) (by simp)]
      intro t ht
      simp only [mem_Iic] at ht
      simpa using ht
    · rw [hNX]
      intro z hz
      rw [sub_zero, inner_neg_left, inner_adjoint_fderiv_F, show z 1 = 0 from hz]
      simp
  · rw [C_eq, normalCone_singleton]
    exact mem_univ _
  · rintro ⟨y, -, hy⟩
    rw [hNX] at hy
    have h := hy e₀ (by simp [X, e₀])
    rw [sub_zero, inner_sub_left, inner_adjoint_fderiv_F] at h
    simp [e₀] at h
    linarith

end IndicatorGeometryCounterexample
end RW
