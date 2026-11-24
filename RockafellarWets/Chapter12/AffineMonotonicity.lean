/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: Monotonicity of affine mappings

Example 12.2: an affine mapping `L(x) = Ax + a`, with `A` not necessarily
symmetric, is monotone if and only if `A` is positive semidefinite,
`⟪x, Ax⟫ ≥ 0` for all `x`, and strictly monotone if and only if `A` is positive
definite, `⟪x, Ax⟫ > 0` for all `x ≠ 0`.  In particular the identity is strictly
monotone.

The statements are given for a linear map `A` on a real inner product space,
and for a square matrix acting on `ℝⁿ = EuclideanSpace ℝ (Fin n)`, where
`⟪x, Ax⟫` is `x ⬝ᵥ A *ᵥ x`.  The sidelight 12(1) after the example is also
recorded: `⟪x, Ax⟫ = ⟪x, Aₛx⟫` for the symmetric part `Aₛ = ½(A + A*)`, the
antisymmetric part `Aₐ = ½(A - A*)` contributes nothing, and antisymmetric
linear maps are monotone.
-/

import RockafellarWets.Chapter12.MonotoneOperations
import Mathlib.Analysis.InnerProductSpace.PiL2

open Set
open scoped InnerProductSpace Matrix

namespace RW

section Affine

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem inner_affine_sub (A : E →ₗ[ℝ] E) (a x₀ x₁ : E) :
    ⟪(A x₁ + a) - (A x₀ + a), x₁ - x₀⟫_ℝ = ⟪x₁ - x₀, A (x₁ - x₀)⟫_ℝ := by
  rw [add_sub_add_right_eq_sub, ← map_sub, real_inner_comm]

/-- **Example 12.2.** An affine mapping `x ↦ Ax + a` is monotone if and only
if `A` is positive semidefinite. -/
theorem svMonotone_affine_iff (A : E →ₗ[ℝ] E) (a : E) :
    SvMonotone (fun x ↦ ({A x + a} : Set E)) ↔ ∀ x, 0 ≤ ⟪x, A x⟫_ℝ := by
  rw [svMonotone_singleton_iff]
  simp only [inner_affine_sub]
  constructor
  · intro h x
    simpa using h 0 x
  · intro h x₀ x₁
    exact h _

/-- **Example 12.2.** An affine mapping `x ↦ Ax + a` is strictly monotone if
and only if `A` is positive definite. -/
theorem svStrictlyMonotone_affine_iff (A : E →ₗ[ℝ] E) (a : E) :
    SvStrictlyMonotone (fun x ↦ ({A x + a} : Set E)) ↔ ∀ x, x ≠ 0 → 0 < ⟪x, A x⟫_ℝ := by
  rw [svStrictlyMonotone_singleton_iff]
  simp only [inner_affine_sub]
  constructor
  · intro h x hx
    simpa using h 0 x (Ne.symm hx)
  · intro h x₀ x₁ hne
    exact h _ (sub_ne_zero.2 (Ne.symm hne))

/-- **Example 12.2.** The identity mapping is strictly monotone. -/
theorem svStrictlyMonotone_id : SvStrictlyMonotone (fun x : E ↦ ({x} : Set E)) := by
  have h := (svStrictlyMonotone_affine_iff (LinearMap.id : E →ₗ[ℝ] E) 0).2 fun x hx ↦ by
    rw [LinearMap.id_apply, real_inner_self_eq_norm_sq]
    exact pow_pos (norm_pos_iff.2 hx) 2
  simpa using h

/-- The identity mapping is monotone. -/
theorem svMonotone_id : SvMonotone (fun x : E ↦ ({x} : Set E)) :=
  svStrictlyMonotone_id.svMonotone

section Parts

variable [CompleteSpace E]

/-- **12(1).** The quadratic form of `A` is that of its symmetric part
`Aₛ = ½(A + A*)`. -/
theorem inner_self_apply_eq_symmetricPart (A : E →L[ℝ] E) (x : E) :
    ⟪x, A x⟫_ℝ = ⟪x, ((2 : ℝ)⁻¹ • (A + A.adjoint)) x⟫_ℝ := by
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, inner_smul_right,
    inner_add_right, ContinuousLinearMap.adjoint_inner_right, real_inner_comm (A x) x]
  ring

/-- **12(1).** The decomposition `A = Aₛ + Aₐ` into a symmetric and an
antisymmetric part. -/
theorem symmetricPart_add_antisymmetricPart (A : E →L[ℝ] E) :
    (2 : ℝ)⁻¹ • (A + A.adjoint) + (2 : ℝ)⁻¹ • (A - A.adjoint) = A ∧
      ((2 : ℝ)⁻¹ • (A + A.adjoint)).adjoint = (2 : ℝ)⁻¹ • (A + A.adjoint) ∧
      ((2 : ℝ)⁻¹ • (A - A.adjoint)).adjoint = -((2 : ℝ)⁻¹ • (A - A.adjoint)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← smul_add, show A + A.adjoint + (A - A.adjoint) = (2 : ℝ) • A by
      rw [two_smul]; abel, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
  · rw [map_smulₛₗ, map_add, ContinuousLinearMap.adjoint_adjoint, add_comm]
    simp
  · rw [map_smulₛₗ, map_sub, ContinuousLinearMap.adjoint_adjoint, ← smul_neg, neg_sub]
    simp

/-- **12(1).** An antisymmetric linear map has vanishing quadratic form. -/
theorem inner_self_apply_eq_zero_of_adjoint_eq_neg {A : E →L[ℝ] E} (hA : A.adjoint = -A)
    (x : E) : ⟪x, A x⟫_ℝ = 0 := by
  have h := ContinuousLinearMap.adjoint_inner_right A x x
  rw [hA, ContinuousLinearMap.neg_apply, inner_neg_right] at h
  have hc := real_inner_comm x (A x)
  linarith

/-- **12(1).** The linear mapping of an antisymmetric operator is monotone. -/
theorem svMonotone_of_adjoint_eq_neg {A : E →L[ℝ] E} (hA : A.adjoint = -A) :
    SvMonotone (fun x ↦ ({A x} : Set E)) := by
  have h := (svMonotone_affine_iff (A : E →ₗ[ℝ] E) 0).2 fun x ↦
    (inner_self_apply_eq_zero_of_adjoint_eq_neg hA x).symm.le
  simpa using h

/-- **12(1).** `A` is positive semidefinite exactly when its symmetric part
is. -/
theorem posSemidef_iff_symmetricPart (A : E →L[ℝ] E) :
    (∀ x, 0 ≤ ⟪x, A x⟫_ℝ) ↔ ∀ x, 0 ≤ ⟪x, ((2 : ℝ)⁻¹ • (A + A.adjoint)) x⟫_ℝ := by
  simp only [← inner_self_apply_eq_symmetricPart]

end Parts

end Affine

section Matrices

variable {n : ℕ}

/-- The quadratic form of a square matrix on `ℝⁿ`. -/
theorem inner_toEuclideanLin_self (A : Matrix (Fin n) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    ⟪x, Matrix.toEuclideanLin A x⟫_ℝ = WithLp.ofLp x ⬝ᵥ A *ᵥ WithLp.ofLp x := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]
  rfl

private theorem forall_euclidean_iff (P : (Fin n → ℝ) → Prop) :
    (∀ x : EuclideanSpace ℝ (Fin n), P (WithLp.ofLp x)) ↔ ∀ x : Fin n → ℝ, P x :=
  ⟨fun h x ↦ by simpa using h (WithLp.toLp 2 x), fun h x ↦ h _⟩

/-- **Example 12.2** for a matrix `A ∈ ℝⁿˣⁿ`, not necessarily symmetric:
`x ↦ Ax + a` is monotone if and only if `x ⬝ Ax ≥ 0` for all `x`. -/
theorem svMonotone_matrix_affine_iff (A : Matrix (Fin n) (Fin n) ℝ) (a : EuclideanSpace ℝ (Fin n)) :
    SvMonotone (fun x ↦ ({Matrix.toEuclideanLin A x + a} : Set (EuclideanSpace ℝ (Fin n)))) ↔
      ∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ A *ᵥ x := by
  rw [svMonotone_affine_iff, ← forall_euclidean_iff (fun x ↦ 0 ≤ x ⬝ᵥ A *ᵥ x)]
  simp only [inner_toEuclideanLin_self]

/-- **Example 12.2** for a matrix `A ∈ ℝⁿˣⁿ`: `x ↦ Ax + a` is strictly monotone
if and only if `x ⬝ Ax > 0` for all `x ≠ 0`. -/
theorem svStrictlyMonotone_matrix_affine_iff (A : Matrix (Fin n) (Fin n) ℝ)
    (a : EuclideanSpace ℝ (Fin n)) :
    SvStrictlyMonotone
        (fun x ↦ ({Matrix.toEuclideanLin A x + a} : Set (EuclideanSpace ℝ (Fin n)))) ↔
      ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ A *ᵥ x := by
  rw [svStrictlyMonotone_affine_iff]
  constructor
  · intro h x hx
    have := h (WithLp.toLp 2 x) (by simpa using hx)
    rw [inner_toEuclideanLin_self] at this
    simpa using this
  · intro h x hx
    rw [inner_toEuclideanLin_self]
    exact h _ (by simpa using hx)

end Matrices

end RW
