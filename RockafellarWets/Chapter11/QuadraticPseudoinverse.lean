/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The pseudoinverse of a symmetric operator
-/

import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The pseudoinverse is the inverse on the range and zero on its orthogonal
complement. The range condition gives uniqueness even when `A` is singular. -/
theorem existsUnique_range_pseudoinverse {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric) :
    ∃! B : E →ₗ[ℝ] E, (∀ x, B x ∈ A.range) ∧
      ∀ x, A (B x) = A.range.starProjection x := by
  let stable (x : E) (_ : x ∈ A.range) : A x ∈ A.range := ⟨x,rfl⟩
  have hi : Function.Injective (A.restrict stable) :=
    (LinearMap.injective_restrict_iff_disjoint stable).mpr (hA.orthogonal_range ▸ A.range.orthogonal_disjoint)
  let e := LinearEquiv.ofInjectiveEndo (A.restrict stable) hi
  let B := A.range.subtype.comp (e.symm.toLinearMap.comp A.range.orthogonalProjection.toLinearMap)
  have hBr (x : E) : B x ∈ A.range := (e.symm (A.range.orthogonalProjection x)).property
  have hAB (x : E) : A (B x) = A.range.starProjection x :=
    congrArg Subtype.val (e.apply_symm_apply (A.range.orthogonalProjection x))
  refine ⟨B,⟨hBr,hAB⟩,?_⟩
  rintro C ⟨hCr,hAC⟩
  ext x
  exact congrArg Subtype.val (hi (a₁ := ⟨C x,hCr x⟩) (a₂ := ⟨B x,hBr x⟩)
    (Subtype.ext ((hAC x).trans (hAB x).symm)))

/-- The canonical pseudoinverse is symmetric and positive semidefinite when
`A` is, and both products are the orthogonal projector onto the range. -/
theorem range_pseudoinverse_properties {A B : E →ₗ[ℝ] E} (hA : A.IsSymmetric)
    (hpos : ∀ x, 0 ≤ ⟪x,A x⟫_ℝ) (hBr : ∀ x, B x ∈ A.range)
    (hAB : ∀ x, A (B x) = A.range.starProjection x) :
    B.IsSymmetric ∧ (∀ x, 0 ≤ ⟪x,B x⟫_ℝ) ∧ ∀ x, B (A x) = A.range.starProjection x := by
  have hlin (x y : E) : ⟪B x,y⟫_ℝ = ⟪B x,A (B y)⟫_ℝ := by
    rw [hAB, ← Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr (hBr x)]
  have hsym : B.IsSymmetric := by
    intro x y
    calc ⟪B x,y⟫_ℝ = ⟪B x,A (B y)⟫_ℝ := hlin x y
         _ = ⟪B y,A (B x)⟫_ℝ := (hA _ _).symm.trans (real_inner_comm _ _)
         _ = ⟪x,B y⟫_ℝ := (hlin y x).symm.trans (real_inner_comm _ _)
  refine ⟨hsym,fun x ↦ ?_,fun x ↦ ?_⟩
  · rw [real_inner_comm,hlin]
    exact hpos _
  · let z := B (A x) - A.range.starProjection x
    have hz : z ∈ A.range := A.range.sub_mem (hBr _) (A.range.starProjection_apply_mem _)
    have hk : x - A.range.starProjection x ∈ LinearMap.ker A :=
      hA.orthogonal_range ▸ A.range.sub_starProjection_mem_orthogonal x
    have hz' : z ∈ LinearMap.ker A := by
      change A (B (A x) - A.range.starProjection x) = 0
      rw [map_sub,hAB,Submodule.starProjection_eq_self_iff.mpr (LinearMap.mem_range_self A x)]
      simpa only [LinearMap.mem_ker,map_sub] using hk
    have he : z ∈ A.range ⊓ A.rangeᗮ := ⟨hz,hA.orthogonal_range.symm ▸ hz'⟩
    rw [Submodule.inf_orthogonal_eq_bot] at he
    exact sub_eq_zero.mp (show z = 0 from he)

/-- The two projection identities alone in 11.10 do not characterize the
Moore–Penrose pseudoinverse. For the zero operator both zero and the identity
satisfy those identities, are symmetric, and are positive semidefinite. -/
theorem projection_product_nonuniqueness :
    ∃ A B C : ℝ →ₗ[ℝ] ℝ, A.IsSymmetric ∧ B.IsSymmetric ∧ C.IsSymmetric ∧
      (∀ x, 0 ≤ ⟪x,A x⟫_ℝ) ∧ (∀ x, 0 ≤ ⟪x,B x⟫_ℝ) ∧ (∀ x, 0 ≤ ⟪x,C x⟫_ℝ) ∧
      (∀ x, A (B x) = A.range.starProjection x ∧ B (A x) = A.range.starProjection x) ∧
      (∀ x, A (C x) = A.range.starProjection x ∧ C (A x) = A.range.starProjection x) ∧ B ≠ C := by
  refine ⟨0,0,LinearMap.id,by simp [LinearMap.IsSymmetric],by simp [LinearMap.IsSymmetric],
    by simp [LinearMap.IsSymmetric],by simp,by simp,?_,by simp,by simp,?_⟩
  · intro x
    simpa [real_inner_self_eq_norm_sq] using sq_nonneg ‖x‖
  · intro h
    have := LinearMap.congr_fun h 1
    norm_num at this

end RW
