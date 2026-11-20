/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Tangents and normals to intersections

Theorem 6.42, derived as the book indicates from Theorems 6.14 and 6.31 with
`X` the whole space, `D` the finite Euclidean product of the factors, and the
diagonal map `x ↦ (x, …, x)`. The diagonal map is the adjoint of coordinate
summation, so the multiplier representation of 6.14 is a decomposition of a
normal vector into a sum of factor normals. The finite index type may be
empty, in which case the intersection is the whole space.
-/

import RockafellarWets.Chapter6.ConstraintTangents
import RockafellarWets.Chapter6.SetAdditionCones

open Filter Metric Set Topology
open scoped BigOperators InnerProductSpace Pointwise

namespace RW

noncomputable section

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The diagonal embedding of `E` into its finite Euclidean power, the adjoint
of coordinate summation. -/
def l2PiDiag : E →L[ℝ] PiLp 2 (fun _ : ι ↦ E) :=
  (l2PiSum (ι := ι) (E := E)).adjoint

theorem l2PiDiag_apply (v : E) :
    l2PiDiag (ι := ι) v = WithLp.toLp 2 (fun _ ↦ v) :=
  l2PiSum_adjoint_apply v

@[simp]
theorem l2PiDiag_apply_coord (v : E) (i : ι) : (l2PiDiag (ι := ι) v) i = v := by
  rw [l2PiDiag_apply]

theorem l2PiDiag_adjoint : (l2PiDiag (ι := ι) (E := E)).adjoint = l2PiSum :=
  ContinuousLinearMap.adjoint_adjoint _

/-- Smoothness of the diagonal map, with field and order fixed in advance. -/
theorem l2PiDiag_contDiff : ContDiff ℝ 1 (⇑(l2PiDiag (ι := ι) (E := E))) :=
  ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := 1) _

/-- An intersection of finitely many sets is the diagonal preimage of their
Euclidean product. -/
theorem iInter_eq_preimage_l2PiSet (C : ι → Set E) :
    (⋂ i, C i) = univ ∩ l2PiDiag ⁻¹' l2PiSet C := by
  ext x
  simp only [mem_iInter, univ_inter, mem_preimage, mem_l2PiSet, l2PiDiag_apply_coord]

/-- **Theorem 6.42**, the constraint qualification: the only way to write
`0` as a sum of limiting normals to the factors is with all summands zero. -/
def IntersectionConstraintQualification (C : ι → Set E) (x : E) : Prop :=
  ∀ v : ι → E, (∀ i, v i ∈ normalCone (C i) x) → ∑ i, v i = 0 → ∀ i, v i = 0

/-- The intersection qualification is the normal constraint qualification of
Theorem 6.14 for the diagonal representation. -/
theorem intersectionConstraintQualification_iff_normalConstraintQualification
    (C : ι → Set E) (x : E) :
    IntersectionConstraintQualification C x ↔
      NormalConstraintQualification univ (l2PiSet C) l2PiDiag x (l2PiDiag x) := by
  unfold IntersectionConstraintQualification NormalConstraintQualification
  rw [normalCone_univ, normalCone_l2PiSet, l2PiDiag_adjoint]
  simp only [mem_l2PiSet, l2PiDiag_apply_coord, mem_singleton_iff, neg_eq_zero,
    l2PiSum_apply]
  constructor
  · intro h y hy hsum
    ext i
    exact h (fun i ↦ y i) hy hsum i
  · intro h v hv hsum i
    have := h (WithLp.toLp 2 v) hv hsum
    exact congrArg (fun y : PiLp 2 (fun _ : ι ↦ E) ↦ y i) this

omit [Fintype ι] [FiniteDimensional ℝ E] in
/-- **Theorem 6.42**, the unconditional tangent inclusion. -/
theorem tangentCone_iInter_subset (C : ι → Set E) (x : E) :
    tangentCone (⋂ i, C i) x ⊆ ⋂ i, tangentCone (C i) x :=
  subset_iInter fun i ↦ tangentCone_mono (iInter_subset C i) x

omit [FiniteDimensional ℝ E] in
/-- Images of the summation map applied to the finite product of cones are
exactly the finite set sums. -/
theorem l2PiSum_image_l2PiSet (K : ι → Set E) :
    l2PiSum '' l2PiSet K = finiteSetSum K :=
  (finiteSetSum_eq_l2PiSum_image K).symm

/-- **Theorem 6.42**, the unconditional regular-normal inclusion. -/
theorem finiteSetSum_regularNormalCone_subset_iInter {C : ι → Set E} {x : E}
    (hx : x ∈ ⋂ i, C i) :
    finiteSetSum (fun i ↦ regularNormalCone (C i) x) ⊆
      regularNormalCone (⋂ i, C i) x := by
  have hx' : x ∈ univ ∩ l2PiDiag ⁻¹' l2PiSet C := by
    rwa [← iInter_eq_preimage_l2PiSet]
  have h := adjoint_regularNormalCone_add_subset_constraints hx' l2PiDiag.hasFDerivAt
  rw [regularNormalCone_univ, l2PiDiag_adjoint, regularNormalCone_l2PiSet,
    ← iInter_eq_preimage_l2PiSet] at h
  intro v hv
  apply h
  refine ⟨v, ?_, 0, rfl, add_zero v⟩
  rw [l2PiSum_image_l2PiSet]
  simpa only [l2PiDiag_apply_coord] using hv

/-- **Theorem 6.42**, the limiting-normal inclusion under the constraint
qualification. -/
theorem normalCone_iInter_subset_finiteSetSum {C : ι → Set E} {x : E}
    (hC : ∀ i, IsClosed (C i))
    (hCQ : IntersectionConstraintQualification C x) :
    normalCone (⋂ i, C i) x ⊆ finiteSetSum (fun i ↦ normalCone (C i) x) := by
  rw [intersectionConstraintQualification_iff_normalConstraintQualification] at hCQ
  have hcq : NormalConstraintQualification univ (l2PiSet C)
      (fderiv ℝ (⇑l2PiDiag) x) x (l2PiDiag x) := by
    rwa [ContinuousLinearMap.fderiv]
  have h := normalCone_constraints_subset isClosed_univ (isClosed_l2PiSet hC)
    l2PiDiag_contDiff hcq
  rw [ContinuousLinearMap.fderiv, normalCone_univ, l2PiDiag_adjoint, normalCone_l2PiSet,
    ← iInter_eq_preimage_l2PiSet, l2PiSum_image_l2PiSet] at h
  intro v hv
  obtain ⟨w, hw, z, hz, rfl⟩ := h hv
  simp only [mem_singleton_iff.1 hz, add_zero]
  simpa only [l2PiDiag_apply_coord] using hw

/-- **Theorem 6.42**, the regular-tangent inclusion under the constraint
qualification. -/
theorem iInter_regularTangentCone_subset {C : ι → Set E} {x : E}
    (hC : ∀ i, IsClosed (C i)) (hx : x ∈ ⋂ i, C i)
    (hCQ : IntersectionConstraintQualification C x) :
    ⋂ i, regularTangentCone (C i) x ⊆ regularTangentCone (⋂ i, C i) x := by
  rw [intersectionConstraintQualification_iff_normalConstraintQualification] at hCQ
  have hcq : NormalConstraintQualification univ (l2PiSet C)
      (fderiv ℝ (⇑l2PiDiag) x) x (l2PiDiag x) := by
    rwa [ContinuousLinearMap.fderiv]
  have hx' : x ∈ univ ∩ l2PiDiag ⁻¹' l2PiSet C := by
    rwa [← iInter_eq_preimage_l2PiSet]
  have h := regularTangentCone_constraints_superset isClosed_univ (isClosed_l2PiSet hC)
    l2PiDiag_contDiff hx' hcq
  rw [ContinuousLinearMap.fderiv, regularTangentCone_eq_tangentCone_of_convex convex_univ
    (mem_univ x), tangentCone_univ, univ_inter, ← iInter_eq_preimage_l2PiSet,
    regularTangentCone_l2PiSet hx'.2] at h
  intro w hw
  apply h
  simp only [mem_preimage, mem_l2PiSet, l2PiDiag_apply_coord]
  exact mem_iInter.1 hw

/-- **Theorem 6.42**, the regular case: the intersection is Clarke regular
and both cone formulas are equalities. -/
theorem clarkeRegularity_iInter {C : ι → Set E} {x : E}
    (hC : ∀ i, IsClosed (C i)) (hx : x ∈ ⋂ i, C i)
    (hCQ : IntersectionConstraintQualification C x)
    (hreg : ∀ i, IsClarkeRegularAt (C i) x) :
    IsClarkeRegularAt (⋂ i, C i) x ∧
      tangentCone (⋂ i, C i) x = ⋂ i, tangentCone (C i) x ∧
      regularTangentCone (⋂ i, C i) x = ⋂ i, tangentCone (C i) x ∧
      normalCone (⋂ i, C i) x = finiteSetSum (fun i ↦ normalCone (C i) x) := by
  rw [intersectionConstraintQualification_iff_normalConstraintQualification] at hCQ
  have hcq : NormalConstraintQualification univ (l2PiSet C)
      (fderiv ℝ (⇑l2PiDiag) x) x (l2PiDiag x) := by
    rwa [ContinuousLinearMap.fderiv]
  have hx' : x ∈ univ ∩ l2PiDiag ⁻¹' l2PiSet C := by
    rwa [← iInter_eq_preimage_l2PiSet]
  have hDreg : IsClarkeRegularAt (l2PiSet C) (l2PiDiag x) := by
    rw [isClarkeRegularAt_l2PiSet_iff hC hx'.2]
    simpa only [l2PiDiag_apply_coord] using hreg
  have hN := clarkeRegularity_constraints isClosed_univ (isClosed_l2PiSet hC)
    l2PiDiag_contDiff hx' hcq (isClarkeRegularAt_univ x) hDreg
  have hT := tangentCone_constraints_of_isClarkeRegularAt isClosed_univ (isClosed_l2PiSet hC)
    l2PiDiag_contDiff hx' hcq (isClarkeRegularAt_univ x) hDreg
  rw [ContinuousLinearMap.fderiv, normalCone_univ, l2PiDiag_adjoint, normalCone_l2PiSet,
    ← iInter_eq_preimage_l2PiSet, l2PiSum_image_l2PiSet] at hN
  rw [ContinuousLinearMap.fderiv, ← iInter_eq_preimage_l2PiSet, tangentCone_univ, univ_inter,
    tangentCone_l2PiSet_of_isClarkeRegularAt hx'.2
      (by simpa only [l2PiDiag_apply_coord] using hreg)] at hT
  have hpre : l2PiDiag ⁻¹' l2PiSet (fun i ↦ tangentCone (C i) ((l2PiDiag x) i)) =
      ⋂ i, tangentCone (C i) x := by
    ext w
    simp only [mem_preimage, mem_l2PiSet, l2PiDiag_apply_coord, mem_iInter]
  have hsum : finiteSetSum (fun i ↦ normalCone (C i) ((l2PiDiag x) i)) + {0} =
      finiteSetSum (fun i ↦ normalCone (C i) x) := by
    simp only [l2PiDiag_apply_coord, Set.singleton_zero, add_zero]
  rw [hpre] at hT
  rw [hsum] at hN
  exact ⟨hN.1, hT.1, hT.2, hN.2⟩

omit [FiniteDimensional ℝ E] in
/-- **Theorem 6.42**, the parenthetical binary convex case: two convex sets
that cannot be separated by a hyperplane satisfy the constraint
qualification at every common point. Separation here means a nonzero vector
whose pairing is at most as large on the first set as on the second. -/
theorem intersectionConstraintQualification_of_not_separated
    {C₁ C₂ : Set E} (h₁ : Convex ℝ C₁) (h₂ : Convex ℝ C₂) {x : E}
    (hx₁ : x ∈ C₁) (hx₂ : x ∈ C₂)
    (hsep : ¬ ∃ v : E, v ≠ 0 ∧ ∀ y ∈ C₁, ∀ z ∈ C₂, ⟪v, y⟫_ℝ ≤ ⟪v, z⟫_ℝ) :
    IntersectionConstraintQualification ![C₁, C₂] x := by
  intro v hv hsum
  have hv0 := hv 0
  have hv1 := hv 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hv0 hv1
  rw [normalCone_eq_of_convex h₁ hx₁] at hv0
  rw [normalCone_eq_of_convex h₂ hx₂] at hv1
  rw [Fin.sum_univ_two] at hsum
  have hv1eq : v 1 = -(v 0) := eq_neg_of_add_eq_zero_right hsum
  have hzero : v 0 = 0 := by
    by_contra hne
    apply hsep
    refine ⟨v 0, hne, fun y hy z hz ↦ ?_⟩
    have hy' := hv0 y hy
    have hz' := hv1 z hz
    rw [hv1eq, inner_neg_left, inner_sub_right] at hz'
    rw [inner_sub_right] at hy'
    linarith
  intro i
  fin_cases i
  · exact hzero
  · simpa only [hzero, neg_zero] using hv1eq

end

end RW
