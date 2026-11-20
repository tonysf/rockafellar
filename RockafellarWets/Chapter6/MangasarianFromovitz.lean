/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Mangasarian--Fromovitz Constraint Qualification

The mixed inequality/equality constraint set in Example 6.40. The disjoint
finite index types `I` and `J` name the inequality and equality constraints,
respectively; this includes the printed consecutive index ranges and permits
either family to be empty.
-/

import RockafellarWets.Chapter6.ConstraintQualifications
import RockafellarWets.Chapter6.RelativeInteriorQualification
import RockafellarWets.Chapter6.FiniteBoxes

open Set
open scoped BigOperators InnerProductSpace Pointwise

namespace RW

section MixedConstraintSet

variable (I J : Type*) [Fintype I] [Fintype J]

/-- The target set for inequality constraints followed by equality constraints. -/
def mixedConstraintSet : Set (EuclideanSpace ℝ (I ⊕ J)) :=
  {u | (∀ i, u (Sum.inl i) ≤ 0) ∧ ∀ j, u (Sum.inr j) = 0}

omit [Fintype I] [Fintype J] in
theorem mixedConstraintSet_eq_finiteBox :
    mixedConstraintSet I J = finiteBox
      (Sum.elim (fun _ : I ↦ Iic (0 : ℝ)) (fun _ : J ↦ ({0} : Set ℝ))) := by
  ext u
  constructor
  · intro hu k
    cases k with
    | inl i => exact hu.1 i
    | inr j => exact mem_singleton_iff.2 (hu.2 j)
  · intro hu
    exact ⟨fun i ↦ hu (Sum.inl i), fun j ↦ mem_singleton_iff.1 (hu (Sum.inr j))⟩

theorem convex_mixedConstraintSet : Convex ℝ (mixedConstraintSet I J) := by
  rw [mixedConstraintSet_eq_finiteBox]
  apply finiteBox_convex
  intro k
  cases k with
  | inl i => exact convex_Iic 0
  | inr j => exact convex_singleton 0

omit [Fintype I] [Fintype J] in
theorem isClosed_mixedConstraintSet : IsClosed (mixedConstraintSet I J) := by
  rw [mixedConstraintSet_eq_finiteBox]
  apply finiteBox_isClosed
  intro k
  cases k with
  | inl i => exact isClosed_Iic
  | inr j => exact isClosed_singleton

variable {I J}

/-- **Example 6.40**, the normal multipliers: inequality multipliers are
nonnegative and vanish at inactive inequalities; equality multipliers are free. -/
theorem normalCone_mixedConstraintSet {u : EuclideanSpace ℝ (I ⊕ J)}
    (hu : u ∈ mixedConstraintSet I J) :
    normalCone (mixedConstraintSet I J) u =
      {y | ∀ i, 0 ≤ y (Sum.inl i) ∧ (u (Sum.inl i) ≠ 0 → y (Sum.inl i) = 0)} := by
  have hbox : u ∈ finiteBox
      (Sum.elim (fun _ : I ↦ Iic (0 : ℝ)) (fun _ : J ↦ ({0} : Set ℝ))) := by
    rwa [← mixedConstraintSet_eq_finiteBox]
  rw [mixedConstraintSet_eq_finiteBox,
    normalCone_finiteBox (by intro k; cases k <;> simp [convex_Iic, convex_singleton]) hbox]
  ext y
  constructor
  · intro hy i
    have hi := hy (Sum.inl i)
    change y (Sum.inl i) ∈ normalCone (Iic 0) (u (Sum.inl i)) at hi
    by_cases hui : u (Sum.inl i) = 0
    · rw [hui, normalCone_Iic_endpoint] at hi
      exact ⟨hi, fun h ↦ (h hui).elim⟩
    · rw [normalCone_Iic_interior (lt_of_le_of_ne (hu.1 i) hui)] at hi
      have hi0 := mem_singleton_iff.1 hi
      exact ⟨by rw [hi0], fun _ ↦ hi0⟩
  · intro hy k
    cases k with
    | inl i =>
        change y (Sum.inl i) ∈ normalCone (Iic 0) (u (Sum.inl i))
        by_cases hui : u (Sum.inl i) = 0
        · rw [hui, normalCone_Iic_endpoint]
          exact (hy i).1
        · rw [normalCone_Iic_interior (lt_of_le_of_ne (hu.1 i) hui)]
          exact mem_singleton_iff.2 ((hy i).2 hui)
    | inr j =>
        change y (Sum.inr j) ∈ normalCone ({0} : Set ℝ) (u (Sum.inr j))
        rw [hu.2 j, normalCone_singleton]
        trivial

/-- **Example 6.40**, the tangent directions: active inequalities impose
nonpositive coordinates and equality constraints impose zero coordinates. -/
theorem tangentCone_mixedConstraintSet {u : EuclideanSpace ℝ (I ⊕ J)}
    (hu : u ∈ mixedConstraintSet I J) :
    tangentCone (mixedConstraintSet I J) u =
      {z | (∀ i, u (Sum.inl i) = 0 → z (Sum.inl i) ≤ 0) ∧
        ∀ j, z (Sum.inr j) = 0} := by
  have hbox : u ∈ finiteBox
      (Sum.elim (fun _ : I ↦ Iic (0 : ℝ)) (fun _ : J ↦ ({0} : Set ℝ))) := by
    rwa [← mixedConstraintSet_eq_finiteBox]
  have hder : ∀ k, IsGeometricallyDerivable
      (Sum.elim (fun _ : I ↦ Iic (0 : ℝ)) (fun _ : J ↦ ({0} : Set ℝ)) k) (u k) := by
    intro k
    apply isGeometricallyDerivable_of_convex _ (hbox k)
    cases k with
    | inl i => exact convex_Iic 0
    | inr j => exact convex_singleton 0
  rw [mixedConstraintSet_eq_finiteBox, tangentCone_finiteBox hbox hder]
  ext z
  constructor
  · intro hz
    constructor
    · intro i hui
      have hi := hz (Sum.inl i)
      change z (Sum.inl i) ∈ tangentCone (Iic 0) (u (Sum.inl i)) at hi
      rwa [hui, tangentCone_Iic_endpoint] at hi
    · intro j
      have hj := hz (Sum.inr j)
      change z (Sum.inr j) ∈ tangentCone ({0} : Set ℝ) (u (Sum.inr j)) at hj
      rw [hu.2 j, tangentCone_singleton] at hj
      exact mem_singleton_iff.1 hj
  · rintro ⟨hineq, heq⟩ k
    cases k with
    | inl i =>
        change z (Sum.inl i) ∈ tangentCone (Iic 0) (u (Sum.inl i))
        by_cases hui : u (Sum.inl i) = 0
        · rw [hui, tangentCone_Iic_endpoint]
          exact hineq i hui
        · rw [tangentCone_Iic_interior (lt_of_le_of_ne (hu.1 i) hui)]
          trivial
    | inr j =>
        change z (Sum.inr j) ∈ tangentCone ({0} : Set ℝ) (u (Sum.inr j))
        rw [hu.2 j, tangentCone_singleton]
        exact mem_singleton_iff.2 (heq j)

theorem isClarkeRegularAt_mixedConstraintSet {u : EuclideanSpace ℝ (I ⊕ J)}
    (hu : u ∈ mixedConstraintSet I J) : IsClarkeRegularAt (mixedConstraintSet I J) u :=
  isClarkeRegularAt_of_convex (convex_mixedConstraintSet I J) hu
    (RW.IsClosed.isLocallyClosedAt (isClosed_mixedConstraintSet I J) u)

/-- The coordinate subspace carrying the equality constraints. -/
def equalitySubspace : Submodule ℝ (EuclideanSpace ℝ (I ⊕ J)) where
  carrier := {z | ∀ j, z (Sum.inr j) = 0}
  add_mem' ha hb j := by simp [ha j, hb j]
  zero_mem' j := rfl
  smul_mem' c a ha j := by simp [ha j]

/-- **Example 6.40**, the explanatory formula: the relative interior of the
tangent cone to the mixed constraint set is described by the same
inequalities made strict. The affine span of the tangent cone is the
equality-constraint subspace. -/
theorem intrinsicInterior_tangentCone_mixedConstraintSet {u : EuclideanSpace ℝ (I ⊕ J)}
    (hu : u ∈ mixedConstraintSet I J) :
    intrinsicInterior ℝ (tangentCone (mixedConstraintSet I J) u) =
      {z | (∀ i, u (Sum.inl i) = 0 → z (Sum.inl i) < 0) ∧
        ∀ j, z (Sum.inr j) = 0} := by
  classical
  set T := tangentCone (mixedConstraintSet I J) u with hT
  have hTeq := tangentCone_mixedConstraintSet hu
  rw [← hT] at hTeq
  ext z
  constructor
  · intro hz
    have hzT : z ∈ T := intrinsicInterior_subset hz
    rw [hTeq] at hzT
    refine ⟨fun i hui ↦ ?_, hzT.2⟩
    by_contra hlt
    have hzero : z (Sum.inl i) = 0 := le_antisymm (hzT.1 i hui) (not_lt.1 hlt)
    have hl : z - EuclideanSpace.single (Sum.inl i) (1 : ℝ) ∈ T := by
      rw [hTeq]
      refine ⟨fun i' hui' ↦ ?_, fun j ↦ ?_⟩
      · rw [PiLp.sub_apply, EuclideanSpace.single_apply]
        split_ifs with h
        · rw [h, hzero]
          norm_num
        · simpa using hzT.1 i' hui'
      · rw [PiLp.sub_apply, EuclideanSpace.single_apply, hzT.2 j]
        simp
    obtain ⟨ε, hε, hmem⟩ := exists_pos_add_smul_sub_mem_of_mem_intrinsicInterior hz hl
    rw [hTeq] at hmem
    have := hmem.1 i hui
    simp [hzero] at this
    linarith
  · rintro ⟨hstrict, heq⟩
    have hzT : z ∈ T := by
      rw [hTeq]
      exact ⟨fun i hui ↦ (hstrict i hui).le, heq⟩
    have hTW : T ⊆ (equalitySubspace (I := I) (J := J)).toAffineSubspace := by
      intro w hw
      rw [hTeq] at hw
      exact hw.2
    have hspan : affineSpan ℝ T ≤ (equalitySubspace (I := I) (J := J)).toAffineSubspace :=
      affineSpan_le_of_subset_coe hTW
    refine mem_intrinsicInterior.2 ⟨⟨z, subset_affineSpan ℝ T hzT⟩, ?_, rfl⟩
    apply mem_interior_iff_mem_nhds.2
    let U : Set (affineSpan ℝ T) :=
      ⋂ i, {q | u (Sum.inl i) = 0 → (q : EuclideanSpace ℝ (I ⊕ J)) (Sum.inl i) < 0}
    have hU : IsOpen U := by
      apply isOpen_iInter_of_finite
      intro i
      by_cases hui : u (Sum.inl i) = 0
      · simp only [hui, true_implies]
        exact isOpen_lt ((PiLp.continuous_apply 2 _ (Sum.inl i)).comp continuous_subtype_val)
          continuous_const
      · simp only [hui, false_implies, setOf_true]
        exact isOpen_univ
    have hzU : (⟨z, subset_affineSpan ℝ T hzT⟩ : affineSpan ℝ T) ∈ U :=
      mem_iInter.2 fun i hui ↦ hstrict i hui
    apply Filter.mem_of_superset (hU.mem_nhds hzU)
    intro q hq
    have hqW : (q : EuclideanSpace ℝ (I ⊕ J)) ∈ equalitySubspace (I := I) (J := J) :=
      hspan q.2
    exact (Set.ext_iff.1 hTeq (q : EuclideanSpace ℝ (I ⊕ J))).2
      ⟨fun i hui ↦ (mem_iInter.1 hq i hui).le, fun j ↦ hqW j⟩

/-- The same relative-interior formula for the regular tangent cone, which
coincides with the tangent cone for this convex closed set. -/
theorem intrinsicInterior_regularTangentCone_mixedConstraintSet
    {u : EuclideanSpace ℝ (I ⊕ J)} (hu : u ∈ mixedConstraintSet I J) :
    intrinsicInterior ℝ (regularTangentCone (mixedConstraintSet I J) u) =
      {z | (∀ i, u (Sum.inl i) = 0 → z (Sum.inl i) < 0) ∧
        ∀ j, z (Sum.inr j) = 0} := by
  rw [← tangentCone_eq_regularTangentCone_of_isClarkeRegularAt hu
    (isClarkeRegularAt_mixedConstraintSet hu)]
  exact intrinsicInterior_tangentCone_mixedConstraintSet hu

end MixedConstraintSet

section JacobianRows

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A row of a Jacobian as a gradient vector, identified through the adjoint. -/
noncomputable def jacobianRow (A : E →L[ℝ] EuclideanSpace ℝ ι) (i : ι) : E :=
  A.adjoint (EuclideanSpace.single i 1)

theorem inner_jacobianRow (A : E →L[ℝ] EuclideanSpace ℝ ι) (i : ι) (w : E) :
    ⟪jacobianRow A i, w⟫_ℝ = (A w) i := by
  rw [jacobianRow, ContinuousLinearMap.adjoint_inner_left,
    EuclideanSpace.inner_single_left]
  simp

theorem adjoint_eq_sum_jacobianRow (A : E →L[ℝ] EuclideanSpace ℝ ι)
    (y : EuclideanSpace ℝ ι) :
    A.adjoint y = ∑ i, y i • jacobianRow A i := by
  apply ext_inner_right ℝ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_left, sum_inner, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_smul_left, inner_jacobianRow]
  simp only [RCLike.inner_apply, conj_trivial, mul_comm]

end JacobianRows

section MixedJacobians

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem equality_jacobianRows_linearIndependent_iff
    (A : E →L[ℝ] EuclideanSpace ℝ (I ⊕ J)) :
    LinearIndependent ℝ (fun j : J ↦ jacobianRow A (Sum.inr j)) ↔
      ∀ y : EuclideanSpace ℝ (I ⊕ J), (∀ i, y (Sum.inl i) = 0) →
        A.adjoint y = 0 → y = 0 := by
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro h y hy hAy
    have hsum : (∑ j : J, y (Sum.inr j) • jacobianRow A (Sum.inr j)) = 0 := by
      rw [adjoint_eq_sum_jacobianRow, Fintype.sum_sum_type] at hAy
      simpa only [hy, zero_smul, Finset.sum_const_zero, zero_add] using hAy
    have heq := h (fun j ↦ y (Sum.inr j)) hsum
    ext k
    cases k with
    | inl i => exact hy i
    | inr j => exact heq j
  · intro h c hc j
    let y : EuclideanSpace ℝ (I ⊕ J) :=
      WithLp.toLp 2 (Sum.elim (fun _ : I ↦ (0 : ℝ)) c)
    have hy : ∀ i, y (Sum.inl i) = 0 := fun _ ↦ rfl
    have hAy : A.adjoint y = 0 := by
      rw [adjoint_eq_sum_jacobianRow, Fintype.sum_sum_type]
      simpa [y] using hc
    have hy0 := h y hy hAy
    have hj := congrArg (fun v : EuclideanSpace ℝ (I ⊕ J) ↦ v (Sum.inr j)) hy0
    simpa [y] using hj

/-- The printed Mangasarian--Fromovitz condition: equality gradients are
linearly independent, and one direction strictly decreases every active
inequality while preserving every equality to first order. -/
def MangasarianFromovitzConstraintQualification
    (A : E →L[ℝ] EuclideanSpace ℝ (I ⊕ J)) (u : EuclideanSpace ℝ (I ⊕ J)) : Prop :=
  LinearIndependent ℝ (fun j : J ↦ jacobianRow A (Sum.inr j)) ∧
    ∃ w : E, (∀ i, u (Sum.inl i) = 0 → (A w) (Sum.inl i) < 0) ∧
      ∀ j, (A w) (Sum.inr j) = 0

omit [DecidableEq I] [DecidableEq J] in
theorem normalConstraintQualification_mixedConstraintSet_iff
    (A : E →L[ℝ] EuclideanSpace ℝ (I ⊕ J)) (x : E)
    {u : EuclideanSpace ℝ (I ⊕ J)} (hu : u ∈ mixedConstraintSet I J) :
    NormalConstraintQualification univ (mixedConstraintSet I J) A x u ↔
      ∀ y : EuclideanSpace ℝ (I ⊕ J),
        (∀ i, 0 ≤ y (Sum.inl i) ∧ (u (Sum.inl i) ≠ 0 → y (Sum.inl i) = 0)) →
        A.adjoint y = 0 → y = 0 := by
  unfold NormalConstraintQualification
  rw [normalCone_univ, normalCone_mixedConstraintSet hu]
  simp only [mem_setOf_eq, mem_singleton_iff, neg_eq_zero]

/-- **Example 6.40**, sufficiency: the Mangasarian--Fromovitz condition
excludes every nonzero abnormal normal multiplier. -/
theorem MangasarianFromovitzConstraintQualification.normalConstraintQualification
    {A : E →L[ℝ] EuclideanSpace ℝ (I ⊕ J)} {u : EuclideanSpace ℝ (I ⊕ J)}
    (h : MangasarianFromovitzConstraintQualification A u)
    (hu : u ∈ mixedConstraintSet I J) (x : E) :
    NormalConstraintQualification univ (mixedConstraintSet I J) A x u := by
  rw [normalConstraintQualification_mixedConstraintSet_iff A x hu]
  intro y hy hAy
  obtain ⟨hli, w, hwI, hwJ⟩ := h
  have hinner : ⟪y, A w⟫_ℝ = 0 := by
    rw [← ContinuousLinearMap.adjoint_inner_left, hAy, inner_zero_left]
  have hsum : (∑ i : I, (A w) (Sum.inl i) * y (Sum.inl i)) = 0 := by
    rw [PiLp.inner_apply, Fintype.sum_sum_type] at hinner
    simpa only [RCLike.inner_apply, conj_trivial, hwJ, zero_mul,
      Finset.sum_const_zero, add_zero] using hinner
  have hnonpos : ∀ i : I, (A w) (Sum.inl i) * y (Sum.inl i) ≤ 0 := by
    intro i
    by_cases hui : u (Sum.inl i) = 0
    · exact mul_nonpos_of_nonpos_of_nonneg (hwI i hui).le (hy i).1
    · rw [(hy i).2 hui, mul_zero]
  have hIz : ∀ i : I, y (Sum.inl i) = 0 := by
    intro i
    by_cases hui : u (Sum.inl i) = 0
    · have hterm := (Finset.sum_eq_zero_iff_of_nonpos
        (fun j _ ↦ hnonpos j)).1 hsum i (Finset.mem_univ i)
      exact (mul_eq_zero.1 hterm).resolve_left (ne_of_lt (hwI i hui))
    · exact (hy i).2 hui
  exact (equality_jacobianRows_linearIndependent_iff A).1 hli y hIz hAy

variable [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- The normal constraint qualification forces independence of all equality
gradients, without any requirement on the inequality gradients. -/
theorem equality_jacobianRows_linearIndependent_of_normalConstraintQualification
    {A : E →L[ℝ] EuclideanSpace ℝ (I ⊕ J)} {u : EuclideanSpace ℝ (I ⊕ J)} {x : E}
    (hu : u ∈ mixedConstraintSet I J)
    (h : NormalConstraintQualification univ (mixedConstraintSet I J) A x u) :
    LinearIndependent ℝ (fun j : J ↦ jacobianRow A (Sum.inr j)) := by
  rw [equality_jacobianRows_linearIndependent_iff]
  intro y hy hAy
  apply (normalConstraintQualification_mixedConstraintSet_iff A x hu).1 h y _ hAy
  intro i
  exact ⟨by rw [hy i], fun _ ↦ hy i⟩

omit [CompleteSpace E] [DecidableEq I] [DecidableEq J] [FiniteDimensional ℝ E] in
/-- Tangent surjectivity supplies a direction strictly decreasing every
active inequality and preserving all equalities to first order. -/
theorem exists_strict_direction_of_regularTangentConstraintQualification
    {A : E →L[ℝ] EuclideanSpace ℝ (I ⊕ J)} {u : EuclideanSpace ℝ (I ⊕ J)} {x : E}
    (hu : u ∈ mixedConstraintSet I J)
    (h : RegularTangentConstraintQualification univ (mixedConstraintSet I J) A x u) :
    ∃ w : E, (∀ i, u (Sum.inl i) = 0 → (A w) (Sum.inl i) < 0) ∧
      ∀ j, (A w) (Sum.inr j) = 0 := by
  let b : EuclideanSpace ℝ (I ⊕ J) :=
    WithLp.toLp 2 (Sum.elim (fun _ : I ↦ (1 : ℝ)) (fun _ : J ↦ (0 : ℝ)))
  have hb : b ∈ regularTangentCone (mixedConstraintSet I J) u +
      -(A '' regularTangentCone (univ : Set E) x) := by
    rw [show regularTangentCone (mixedConstraintSet I J) u +
      -(A '' regularTangentCone (univ : Set E) x) = univ from h]
    trivial
  obtain ⟨t, ht, v, hv, htv⟩ := hb
  rw [Set.mem_neg] at hv
  obtain ⟨w, -, hAw⟩ := hv
  have htT := regularTangentCone_subset_tangentCone hu ht
  rw [tangentCone_mixedConstraintSet hu] at htT
  refine ⟨w, ?_, ?_⟩
  · intro i hui
    have h1 := congrArg (fun z : EuclideanSpace ℝ (I ⊕ J) ↦ z (Sum.inl i)) htv
    have h2 := congrArg (fun z : EuclideanSpace ℝ (I ⊕ J) ↦ z (Sum.inl i)) hAw
    have ht0 := htT.1 i hui
    simp only [PiLp.add_apply, PiLp.neg_apply] at h1 h2
    change t (Sum.inl i) + v (Sum.inl i) = 1 at h1
    linarith
  · intro j
    have h1 := congrArg (fun z : EuclideanSpace ℝ (I ⊕ J) ↦ z (Sum.inr j)) htv
    have h2 := congrArg (fun z : EuclideanSpace ℝ (I ⊕ J) ↦ z (Sum.inr j)) hAw
    have ht0 := htT.2 j
    simp only [PiLp.add_apply, PiLp.neg_apply] at h1 h2
    change t (Sum.inr j) + v (Sum.inr j) = 0 at h1
    linarith

/-- **Example 6.40**: the normal constraint qualification is equivalent to
the printed equality-gradient independence and strict feasible direction. -/
theorem normalConstraintQualification_iff_mangasarianFromovitz
    (A : E →L[ℝ] EuclideanSpace ℝ (I ⊕ J)) (x : E)
    {u : EuclideanSpace ℝ (I ⊕ J)} (hu : u ∈ mixedConstraintSet I J) :
    NormalConstraintQualification univ (mixedConstraintSet I J) A x u ↔
      MangasarianFromovitzConstraintQualification A u := by
  constructor
  · intro h
    refine ⟨equality_jacobianRows_linearIndependent_of_normalConstraintQualification hu h, ?_⟩
    apply exists_strict_direction_of_regularTangentConstraintQualification hu
    exact (regularTangentConstraintQualification_iff_normalConstraintQualification
      (mem_univ x) hu (isClarkeRegularAt_univ x) (isClarkeRegularAt_mixedConstraintSet hu)).2 h
  · intro h
    exact h.normalConstraintQualification hu x

/-- **Example 6.40**: tangent-surjectivity qualification 6.39(a) is exactly
the Mangasarian--Fromovitz condition for the mixed constraint set. -/
theorem regularTangentConstraintQualification_iff_mangasarianFromovitz
    (A : E →L[ℝ] EuclideanSpace ℝ (I ⊕ J)) (x : E)
    {u : EuclideanSpace ℝ (I ⊕ J)} (hu : u ∈ mixedConstraintSet I J) :
    RegularTangentConstraintQualification univ (mixedConstraintSet I J) A x u ↔
      MangasarianFromovitzConstraintQualification A u := by
  rw [regularTangentConstraintQualification_iff_normalConstraintQualification
    (mem_univ x) hu (isClarkeRegularAt_univ x) (isClarkeRegularAt_mixedConstraintSet hu),
    normalConstraintQualification_iff_mangasarianFromovitz A x hu]

/-- **Example 6.40**: relative-interior qualification 6.39(b) is exactly
the Mangasarian--Fromovitz condition for the mixed constraint set. -/
theorem relativeInteriorConstraintQualification_iff_mangasarianFromovitz
    (A : E →L[ℝ] EuclideanSpace ℝ (I ⊕ J)) (x : E)
    {u : EuclideanSpace ℝ (I ⊕ J)} (hu : u ∈ mixedConstraintSet I J) :
    RelativeInteriorConstraintQualification univ (mixedConstraintSet I J) A x u ↔
      MangasarianFromovitzConstraintQualification A u := by
  rw [← regularTangentConstraintQualification_iff_relativeInteriorConstraintQualification
    (mem_univ x) hu, regularTangentConstraintQualification_iff_mangasarianFromovitz A x hu]

/-- **Example 6.40**: convexified-normal qualification 6.39(c) is exactly
the Mangasarian--Fromovitz condition for the mixed constraint set. -/
theorem convexifiedNormalConstraintQualification_iff_mangasarianFromovitz
    (A : E →L[ℝ] EuclideanSpace ℝ (I ⊕ J)) (x : E)
    {u : EuclideanSpace ℝ (I ⊕ J)} (hu : u ∈ mixedConstraintSet I J) :
    ConvexifiedNormalConstraintQualification univ (mixedConstraintSet I J) A x u ↔
      MangasarianFromovitzConstraintQualification A u := by
  rw [convexifiedNormalConstraintQualification_iff_normalConstraintQualification
    (isClarkeRegularAt_univ x) (isClarkeRegularAt_mixedConstraintSet hu),
    normalConstraintQualification_iff_mangasarianFromovitz A x hu]

end MixedJacobians

end RW
