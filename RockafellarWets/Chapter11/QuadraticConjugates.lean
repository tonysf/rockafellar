/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Conjugates of linear-quadratic functions
-/

import RockafellarWets.Chapter11.FenchelConjugate
import RockafellarWets.Chapter11.QuadraticPseudoinverse
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef

open scoped InnerProductSpace
open Set

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The real affine-quadratic objective in Example 11.10. -/
noncomputable def affineQuadratic (A : E →ₗ[ℝ] E) (a : E) (c : ℝ) (x : E) : EReal :=
  ((⟪x,A x⟫_ℝ / 2 + ⟪a,x⟫_ℝ + c : ℝ) : EReal)

/-- On the translated range, completing the square gives the conjugate
value at any solution of the stationary equation. -/
theorem fenchelConjugate_affineQuadratic_of_preimage {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric)
    (hpos : ∀ x, 0 ≤ ⟪x,A x⟫_ℝ) (a : E) (c : ℝ) {v y : E} (hy : A y = v - a) :
    fenchelConjugate (affineQuadratic A a c) v = ((⟪v - a,y⟫_ℝ / 2 - c : ℝ) : EReal) := by
  have hv : v = A y + a := eq_add_of_sub_eq hy.symm
  apply le_antisymm
  · refine (fenchelConjugate_le_iff _ _ _).mpr fun x ↦ ?_
    rw [affineQuadratic, ← EReal.coe_sub, EReal.coe_le_coe_iff, ← hy, hv, inner_add_left]
    have hn := hpos (x-y)
    rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right] at hn
    linarith only [hn,hA x y,hA y x,real_inner_comm (A y) y,real_inner_comm (A y) x]
  · have hl := le_fenchelConjugate (affineQuadratic A a c) y v
    rw [affineQuadratic, ← EReal.coe_sub] at hl
    convert hl using 2
    rw [← hy, hv,inner_add_left,real_inner_comm (A y) y]
    ring

variable [FiniteDimensional ℝ E]

/-- Outside the translated range the dual objective is unbounded along a
line in the kernel of the quadratic form. -/
theorem fenchelConjugate_affineQuadratic_of_not_mem {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric)
    (a : E) (c : ℝ) {v : E} (hv : v - a ∉ A.range) :
    fenchelConjugate (affineQuadratic A a c) v = ⊤ := by
  have hz : ∃ z ∈ A.rangeᗮ, ⟪z,v-a⟫_ℝ ≠ 0 := by
    by_contra! h
    exact hv (A.range.orthogonal_orthogonal ▸ ((A.rangeᗮ).mem_orthogonal _).mpr h)
  obtain ⟨z,hz,hn⟩ := hz
  have hAz : A z = 0 := (show z ∈ A.ker from hA.orthogonal_range ▸ hz)
  rw [real_inner_comm] at hn
  apply (EReal.eq_top_iff_forall_lt _).mpr
  intro r
  let t := (r+c+1) / ⟪v-a,z⟫_ℝ
  have he : t * ⟪v-a,z⟫_ℝ = r+c+1 := div_mul_cancel₀ _ hn
  have hl := le_fenchelConjugate (affineQuadratic A a c) (t • z) v
  rw [affineQuadratic,map_smul,hAz,smul_zero,inner_zero_right,zero_div,zero_add,
    real_inner_smul_right,real_inner_smul_right, ← EReal.coe_sub] at hl
  apply lt_of_lt_of_le _ hl
  rw [EReal.coe_lt_coe_iff]
  rw [inner_sub_left,mul_sub] at he
  linarith

/-- **Example 11.10** for a positive semidefinite symmetric operator,
including its singular case. The range constraint selects the unique
Moore–Penrose inverse as in `existsUnique_range_pseudoinverse`. -/
theorem fenchelConjugate_affineQuadratic {A B : E →ₗ[ℝ] E} (hA : A.IsSymmetric)
    (hpos : ∀ x, 0 ≤ ⟪x,A x⟫_ℝ) (hAB : ∀ x, A (B x) = A.range.starProjection x)
    (a v : E) (c : ℝ) [Decidable (v - a ∈ A.range)] :
    fenchelConjugate (affineQuadratic A a c) v =
      if v-a ∈ A.range then ((⟪v-a,B (v-a)⟫_ℝ / 2 - c : ℝ) : EReal) else ⊤ := by
  split_ifs with hv
  · exact fenchelConjugate_affineQuadratic_of_preimage hA hpos a c
      ((hAB _).trans (Submodule.starProjection_eq_self_iff.mpr hv))
  · exact fenchelConjugate_affineQuadratic_of_not_mem hA a c hv

omit [FiniteDimensional ℝ E] in
/-- The nonsingular case of Example 11.10. -/
theorem fenchelConjugate_invertible_affineQuadratic (A : E ≃ₗ[ℝ] E)
    (hs : A.toLinearMap.IsSymmetric) (hp : ∀ x, 0 ≤ ⟪x,A x⟫_ℝ) (a v : E) (c : ℝ) :
    fenchelConjugate (affineQuadratic A.toLinearMap a c) v =
      ((⟪v-a,A.symm (v-a)⟫_ℝ / 2 - c : ℝ) : EReal) :=
  fenchelConjugate_affineQuadratic_of_preimage hs hp a c (A.apply_symm_apply _)

/-- The affine case has a single dual point in its effective domain. -/
theorem fenchelConjugate_affine (a v : E) (c : ℝ) :
    fenchelConjugate (fun x ↦ ((⟪a,x⟫_ℝ + c : ℝ) : EReal)) v = indicatorVA {a} v - (c : EReal) := by
  classical
  have h : (fun x ↦ ((⟪a,x⟫_ℝ + c : ℝ) : EReal)) = affineQuadratic 0 a c := by
    funext x
    simp [affineQuadratic]
  rw [h]
  by_cases hv : v = a
  · subst v
    have hh := fenchelConjugate_affineQuadratic_of_preimage (A := 0) (by simp [LinearMap.IsSymmetric])
      (by simp) a c (v := a) (y := 0) (by simp)
    simpa [indicatorVA] using hh
  · rw [fenchelConjugate_affineQuadratic_of_not_mem (A := 0) (by simp [LinearMap.IsSymmetric])
      a c (by simpa [sub_eq_zero] using hv),indicatorVA_apply_not_mem (by simpa using hv)]
    simp [sub_eq_add_neg]

open Classical in
/-- Matrix version, including positive semidefinite matrices of deficient rank.
The canonical pseudoinverse and the range condition are expressed on Euclidean
coordinate vectors. -/
theorem fenchelConjugate_matrix_quadratic {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hM : M.PosSemidef) :
    ∃ B : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι,
      B.IsSymmetric ∧ (∀ x, 0 ≤ ⟪x,B x⟫_ℝ) ∧
      (∀ x, M.toEuclideanLin (B x) = M.toEuclideanLin.range.starProjection x ∧
        B (M.toEuclideanLin x) = M.toEuclideanLin.range.starProjection x) ∧
      ∀ (a v : EuclideanSpace ℝ ι) (c : ℝ), fenchelConjugate (affineQuadratic M.toEuclideanLin a c) v =
        if v-a ∈ M.toEuclideanLin.range then ((⟪v-a,B (v-a)⟫_ℝ / 2 - c : ℝ) : EReal) else ⊤ := by
  classical
  have hs := Matrix.isHermitian_iff_isSymmetric.mp hM.isHermitian
  have hp (x : EuclideanSpace ℝ ι) : 0 ≤ ⟪x,M.toEuclideanLin x⟫_ℝ := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simpa [dotProduct, mul_comm] using hM.dotProduct_mulVec_nonneg (WithLp.ofLp x)
  obtain ⟨B,⟨hBr,hAB⟩,_⟩ := existsUnique_range_pseudoinverse hs
  obtain ⟨hbs,hbp,hBA⟩ := range_pseudoinverse_properties hs hp hBr hAB
  exact ⟨B,hbs,hbp,fun x ↦ ⟨hAB x,hBA x⟩,fun a v c ↦ fenchelConjugate_affineQuadratic hs hp hAB a v c⟩

end RW
