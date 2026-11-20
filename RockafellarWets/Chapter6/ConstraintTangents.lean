/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Tangents to sets with constraint structure

Theorem 6.31: the normal-cone rule of 6.14 gives the reverse regular-tangent
inclusion by polarity. Under Clarke regularity all the tangent formulas agree.
-/

import RockafellarWets.Chapter6.ConstraintNormals

open Set
open scoped InnerProductSpace

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- **Theorem 6.31**, the regular-tangent inclusion under the normal
constraint qualification. -/
theorem regularTangentCone_constraints_superset
    {X : Set E} {D : Set F} (hX : IsClosed X) (hD : IsClosed D)
    {f : E → F} (hf : ContDiff ℝ 1 f) {x : E} (hx : x ∈ X ∩ f ⁻¹' D)
    (hCQ : NormalConstraintQualification X D (fderiv ℝ f x) x (f x)) :
    regularTangentCone X x ∩ (fderiv ℝ f x) ⁻¹' regularTangentCone D (f x) ⊆
      regularTangentCone (X ∩ f ⁻¹' D) x := by
  rintro w ⟨hwX, hwD⟩
  rw [regularTangentCone_eq_polarCone_normalCone hx
    (RW.IsClosed.isLocallyClosedAt (hX.inter (hD.preimage hf.continuous)) x)]
  intro v hv
  obtain ⟨y, hy, z, hz, rfl⟩ :=
    exists_normal_multipliers_of_mem_normalCone hX hD hf hCQ hv
  rw [inner_add_right, ContinuousLinearMap.adjoint_inner_right,
    real_inner_comm y, real_inner_comm z]
  exact add_nonpos
    (inner_nonpos_of_mem_normalCone_of_mem_regularTangentCone (show f x ∈ D from hx.2)
      (RW.IsClosed.isLocallyClosedAt hD (f x)) hy hwD)
    (inner_nonpos_of_mem_normalCone_of_mem_regularTangentCone hx.1
      (RW.IsClosed.isLocallyClosedAt hX x) hz hwX)

/-- **Theorem 6.31**, both tangent equalities for regular component sets. -/
theorem tangentCone_constraints_of_isClarkeRegularAt
    {X : Set E} {D : Set F} (hX : IsClosed X) (hD : IsClosed D)
    {f : E → F} (hf : ContDiff ℝ 1 f) {x : E} (hx : x ∈ X ∩ f ⁻¹' D)
    (hCQ : NormalConstraintQualification X D (fderiv ℝ f x) x (f x))
    (hXreg : IsClarkeRegularAt X x) (hDreg : IsClarkeRegularAt D (f x)) :
    tangentCone (X ∩ f ⁻¹' D) x =
        tangentCone X x ∩ (fderiv ℝ f x) ⁻¹' tangentCone D (f x) ∧
      regularTangentCone (X ∩ f ⁻¹' D) x =
        tangentCone X x ∩ (fderiv ℝ f x) ⁻¹' tangentCone D (f x) := by
  have hreg := (clarkeRegularity_constraints hX hD hf hx hCQ hXreg hDreg).1
  have heq := tangentCone_eq_regularTangentCone_of_isClarkeRegularAt hx hreg
  have hlow := regularTangentCone_constraints_superset hX hD hf hx hCQ
  rw [← tangentCone_eq_regularTangentCone_of_isClarkeRegularAt hx.1 hXreg,
    ← tangentCone_eq_regularTangentCone_of_isClarkeRegularAt (show f x ∈ D from hx.2) hDreg,
    ← heq] at hlow
  have h := Subset.antisymm
    (tangentCone_constraints_subset
      ((hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt)) hlow
  exact ⟨h, heq.symm.trans h⟩

end RW
