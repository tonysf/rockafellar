/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Tangents and Normals to Intersections

Theorem 6.42.  The book proves it by embedding the intersection in a product,
`D := C₁ × ⋯ × C_m` with the diagonal map, and reading normals and tangents to
`D` off 6.41.  For two sets no product is needed at all: `constrainedPreimage`
with `G = id` *is* the intersection, `∇id = id`, and `id* = id`, so the binary
case of 6.42 is Theorem 6.14 instantiated, with the printed constraint
qualification falling out verbatim.  The general case is then induction on the
index set, the qualification for a subfamily being the printed one with the
missing multipliers set to zero.
-/

import RockafellarWets.Chapter6.ConstraintTangents

open Filter Metric Set Topology
open scoped InnerProductSpace Pointwise

namespace RW

section Intersections

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {C₁ C₂ : Set E} {x : E}

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The constraint set of Theorem 6.14 for the identity map is the
intersection. -/
theorem constrainedPreimage_id (C₁ C₂ : Set E) :
    constrainedPreimage C₁ id C₂ = C₁ ∩ C₂ := rfl

/-- The multiplier set of Theorem 6.14 for the identity map is the sum of the
normal cones. -/
theorem constraintNormals_id (C₁ C₂ : Set E) (x : E) :
    constraintNormals C₁ id C₂ x = normalCone C₁ x + normalCone C₂ x := by
  ext u
  simp only [constraintNormals, mem_setOf_eq, fderiv_id, ContinuousLinearMap.adjoint_id,
    ContinuousLinearMap.coe_id', id_eq, Set.mem_add]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    exact ⟨z, hz, y, hy, add_comm z y⟩
  · rintro ⟨z, hz, y, hy, rfl⟩
    exact ⟨y, hy, z, hz, add_comm y z⟩

/-- The constraint qualification of Theorem 6.14 for the identity map is the
transversality condition printed in 6.42. -/
theorem constraintQualification_id_iff (C₁ C₂ : Set E) (x : E) :
    ConstraintQualification C₁ id C₂ x ↔
      ∀ v ∈ normalCone C₁ x, ∀ w ∈ normalCone C₂ x, v + w = 0 → v = 0 ∧ w = 0 := by
  simp only [ConstraintQualification, fderiv_id, ContinuousLinearMap.adjoint_id,
    ContinuousLinearMap.coe_id', id_eq]
  constructor
  · intro hCQ v hv w hw hsum
    have hneg : -w ∈ normalCone C₁ x := by
      have : -w = v := by
        rw [neg_eq_iff_add_eq_zero, add_comm]
        exact hsum
      rwa [this]
    have hw0 : w = 0 := hCQ w hw hneg
    refine ⟨?_, hw0⟩
    rw [hw0, add_zero] at hsum
    exact hsum
  · intro htrans y hy hneg
    have hsum : -y + y = 0 := by abel
    exact ((htrans (-y) hneg y hy hsum).2)

/-- **Theorem 6.42** for two sets, normal cones: under the transversality
condition every limiting normal to an intersection splits. -/
theorem normalCone_inter_subset_add (hC₁ : IsClosed C₁) (hC₂ : IsClosed C₂)
    (htrans : ∀ v ∈ normalCone C₁ x, ∀ w ∈ normalCone C₂ x, v + w = 0 → v = 0 ∧ w = 0) :
    normalCone (C₁ ∩ C₂) x ⊆ normalCone C₁ x + normalCone C₂ x := by
  have hmain := normalCone_subset_constraintNormals (X := C₁) (G := id) (D := C₂)
    contDiff_id hC₁ hC₂ ((constraintQualification_id_iff C₁ C₂ x).mpr htrans)
  rwa [constrainedPreimage_id, constraintNormals_id] at hmain

/-- **Theorem 6.42** for two sets, regular tangent cones. -/
theorem regularTangentCone_inter_subset_inter (hC₁ : IsClosed C₁) (hC₂ : IsClosed C₂)
    (hx : x ∈ C₁ ∩ C₂)
    (htrans : ∀ v ∈ normalCone C₁ x, ∀ w ∈ normalCone C₂ x, v + w = 0 → v = 0 ∧ w = 0) :
    regularTangentCone C₁ x ∩ regularTangentCone C₂ x ⊆ regularTangentCone (C₁ ∩ C₂) x := by
  have hxC : x ∈ constrainedPreimage C₁ id C₂ := hx
  have hmain := regularTangentCone_inter_subset_constrainedPreimage (X := C₁) (G := id)
    (D := C₂) contDiff_id hC₁ hC₂ ((constraintQualification_id_iff C₁ C₂ x).mpr htrans) hxC
  rw [constrainedPreimage_id] at hmain
  intro w hw
  refine hmain ?_
  simp only [mem_setOf_eq, fderiv_id, ContinuousLinearMap.coe_id', id_eq]
  exact ⟨hw.1, hw.2⟩

/-- **Theorem 6.42** for two sets, Clarke regularity and the two equations. -/
theorem isClarkeRegularAt_inter (hC₁ : IsClosed C₁) (hC₂ : IsClosed C₂)
    (hx : x ∈ C₁ ∩ C₂)
    (htrans : ∀ v ∈ normalCone C₁ x, ∀ w ∈ normalCone C₂ x, v + w = 0 → v = 0 ∧ w = 0)
    (h₁ : IsClarkeRegularAt C₁ x) (h₂ : IsClarkeRegularAt C₂ x) :
    IsClarkeRegularAt (C₁ ∩ C₂) x ∧
      normalCone (C₁ ∩ C₂) x = normalCone C₁ x + normalCone C₂ x ∧
      tangentCone (C₁ ∩ C₂) x = tangentCone C₁ x ∩ tangentCone C₂ x := by
  have hxC : x ∈ constrainedPreimage C₁ id C₂ := hx
  have hCQ := (constraintQualification_id_iff C₁ C₂ x).mpr htrans
  obtain ⟨hreg, hnormal⟩ :=
    isClarkeRegularAt_constrainedPreimage (X := C₁) (G := id) (D := C₂)
      contDiff_id hC₁ hC₂ hCQ h₁ h₂
  have htangent := tangentCone_constrainedPreimage_eq (X := C₁) (G := id) (D := C₂)
    contDiff_id hC₁ hC₂ hCQ hxC h₁ h₂
  rw [constrainedPreimage_id] at hreg hnormal htangent
  rw [constraintNormals_id] at hnormal
  refine ⟨hreg, hnormal, ?_⟩
  rw [htangent]
  ext w
  simp only [mem_setOf_eq, mem_inter_iff, fderiv_id, ContinuousLinearMap.coe_id', id_eq]

end Intersections

section FiniteIntersections

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} {C : ι → Set E} {x : E}

omit [FiniteDimensional ℝ E] in
/-- The transversality condition of 6.42 restricts to a subfamily: extend a
combination by zeros. -/
theorem transversal_of_insert [DecidableEq ι] (hx : ∀ i, x ∈ C i)
    {a : ι} {T : Finset ι} (ha : a ∉ T)
    (htrans : ∀ v : ι → E, (∀ i ∈ insert a T, v i ∈ normalCone (C i) x) →
      ∑ i ∈ insert a T, v i = 0 → ∀ i ∈ insert a T, v i = 0) :
    ∀ v : ι → E, (∀ i ∈ T, v i ∈ normalCone (C i) x) →
      ∑ i ∈ T, v i = 0 → ∀ i ∈ T, v i = 0 := by
  intro v hv hsum i hi
  have hupd : ∀ j ∈ T, Function.update v a 0 j = v j := by
    intro j hj
    have hne : j ≠ a := fun hje ↦ ha (hje ▸ hj)
    exact Function.update_of_ne hne _ _
  have hmem : ∀ j ∈ insert a T, Function.update v a 0 j ∈ normalCone (C j) x := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hjT
    · rw [Function.update_self]
      exact (isCone_normalCone (hx j)).1
    · rw [hupd j hjT]
      exact hv j hjT
  have hsum' : ∑ j ∈ insert a T, Function.update v a 0 j = 0 := by
    rw [Finset.sum_insert ha, Function.update_self, Finset.sum_congr rfl hupd]
    simp [hsum]
  have hzero := htrans _ hmem hsum' i (Finset.mem_insert_of_mem hi)
  rwa [hupd i hi] at hzero

/-- **Theorem 6.42**, the multiplier representation for a finite intersection.
The induction step is the binary case, whose transversality hypothesis comes
from the representation already proved for the smaller family. -/
theorem normalCone_biInter_subset_sum (hC : ∀ i, IsClosed (C i)) (hx : ∀ i, x ∈ C i)
    (S : Finset ι)
    (htrans : ∀ v : ι → E, (∀ i ∈ S, v i ∈ normalCone (C i) x) →
      ∑ i ∈ S, v i = 0 → ∀ i ∈ S, v i = 0) :
    normalCone (⋂ i ∈ S, C i) x ⊆
      {u : E | ∃ v : ι → E, (∀ i ∈ S, v i ∈ normalCone (C i) x) ∧ ∑ i ∈ S, v i = u} := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      intro u hu
      simp only [Finset.notMem_empty, iInter_of_empty, iInter_univ, normalCone_univ,
        mem_singleton_iff] at hu
      exact ⟨fun _ ↦ 0, by simp, by simp [hu]⟩
  | insert a T ha ih =>
      have hTclosed : IsClosed (⋂ i ∈ T, C i) :=
        isClosed_iInter fun i ↦ isClosed_iInter fun _ ↦ hC i
      have hTmem : x ∈ ⋂ i ∈ T, C i := mem_iInter₂.2 fun i _ ↦ hx i
      have htransT := transversal_of_insert hx ha htrans
      have ihT := ih htransT
      have hbin : ∀ v ∈ normalCone (C a) x, ∀ w ∈ normalCone (⋂ i ∈ T, C i) x,
          v + w = 0 → v = 0 ∧ w = 0 := by
        intro p hp q hq hsum
        obtain ⟨z, hz, hzsum⟩ := ihT hq
        have hupd : ∀ j ∈ T, Function.update z a p j = z j := by
          intro j hj
          have hne : j ≠ a := fun hje ↦ ha (hje ▸ hj)
          exact Function.update_of_ne hne _ _
        have hmem : ∀ j ∈ insert a T, Function.update z a p j ∈ normalCone (C j) x := by
          intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hjT
          · rw [Function.update_self]
            exact hp
          · rw [hupd j hjT]
            exact hz j hjT
        have hsum' : ∑ j ∈ insert a T, Function.update z a p j = 0 := by
          rw [Finset.sum_insert ha, Function.update_self, Finset.sum_congr rfl hupd,
            hzsum]
          exact hsum
        have hall := htrans _ hmem hsum'
        have hpa : p = 0 := by
          have := hall a (Finset.mem_insert_self a T)
          rwa [Function.update_self] at this
        refine ⟨hpa, ?_⟩
        rw [hpa, zero_add] at hsum
        exact hsum
      intro u hu
      rw [Finset.set_biInter_insert] at hu
      obtain ⟨p, hp, q, hq, hpq⟩ := normalCone_inter_subset_add (hC a) hTclosed hbin hu
      obtain ⟨z, hz, hzsum⟩ := ihT hq
      have hupd : ∀ j ∈ T, Function.update z a p j = z j := by
        intro j hj
        have hne : j ≠ a := fun hje ↦ ha (hje ▸ hj)
        exact Function.update_of_ne hne _ _
      refine ⟨Function.update z a p, ?_, ?_⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hjT
        · rw [Function.update_self]
          exact hp
        · rw [hupd j hjT]
          exact hz j hjT
      · rw [Finset.sum_insert ha, Function.update_self, Finset.sum_congr rfl hupd,
          hzsum]
        exact hpq

/-- The whole space has every vector as a regular tangent. -/
theorem regularTangentCone_univ (x : E) :
    regularTangentCone (Set.univ : Set E) x = Set.univ := by
  rw [regularTangentCone_eq_polarCone_normalCone (mem_univ x)
    (RW.IsClosed.isLocallyClosedAt isClosed_univ x), normalCone_univ]
  ext w
  simp [polarCone]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem biInter_coe_finset (C : ι → Set E) (S : Finset ι) :
    ⋂ i ∈ (S : Set ι), C i = ⋂ i ∈ S, C i := by
  ext z
  simp

/-- The transversality condition of 6.42 splits one set off the family, the
remaining multipliers being assembled by the representation just proved. -/
theorem normalTransversal_insert [DecidableEq ι] (hC : ∀ i, IsClosed (C i))
    (hx : ∀ i, x ∈ C i) {a : ι} {T : Finset ι} (ha : a ∉ T)
    (htrans : ∀ v : ι → E, (∀ i ∈ insert a T, v i ∈ normalCone (C i) x) →
      ∑ i ∈ insert a T, v i = 0 → ∀ i ∈ insert a T, v i = 0) :
    ∀ p ∈ normalCone (C a) x, ∀ q ∈ normalCone (⋂ i ∈ T, C i) x,
      p + q = 0 → p = 0 ∧ q = 0 := by
  intro p hp q hq hsum
  obtain ⟨z, hz, hzsum⟩ :=
    normalCone_biInter_subset_sum hC hx T (transversal_of_insert hx ha htrans) hq
  have hupd : ∀ j ∈ T, Function.update z a p j = z j := by
    intro j hj
    have hne : j ≠ a := fun hje ↦ ha (hje ▸ hj)
    exact Function.update_of_ne hne _ _
  have hmem : ∀ j ∈ insert a T, Function.update z a p j ∈ normalCone (C j) x := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hjT
    · rw [Function.update_self]
      exact hp
    · rw [hupd j hjT]
      exact hz j hjT
  have hsum' : ∑ j ∈ insert a T, Function.update z a p j = 0 := by
    rw [Finset.sum_insert ha, Function.update_self, Finset.sum_congr rfl hupd, hzsum]
    exact hsum
  have hall := htrans _ hmem hsum'
  have hpa : p = 0 := by
    have hval := hall a (Finset.mem_insert_self a T)
    rwa [Function.update_self] at hval
  refine ⟨hpa, ?_⟩
  rw [hpa, zero_add] at hsum
  exact hsum

/-- **Theorem 6.42**, the regular tangent inclusion for a finite
intersection. -/
theorem regularTangentCone_biInter_subset (hC : ∀ i, IsClosed (C i)) (hx : ∀ i, x ∈ C i)
    (S : Finset ι)
    (htrans : ∀ v : ι → E, (∀ i ∈ S, v i ∈ normalCone (C i) x) →
      ∑ i ∈ S, v i = 0 → ∀ i ∈ S, v i = 0) :
    (⋂ i ∈ S, regularTangentCone (C i) x) ⊆ regularTangentCone (⋂ i ∈ S, C i) x := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.notMem_empty, iInter_of_empty, iInter_univ, regularTangentCone_univ]
      exact Subset.rfl
  | insert a T ha ih =>
      have hTclosed : IsClosed (⋂ i ∈ T, C i) :=
        isClosed_iInter fun i ↦ isClosed_iInter fun _ ↦ hC i
      have hTmem : x ∈ ⋂ i ∈ T, C i := mem_iInter₂.2 fun i _ ↦ hx i
      have ihT := ih (transversal_of_insert hx ha htrans)
      have hbin := normalTransversal_insert hC hx ha htrans
      intro w hw
      rw [Finset.set_biInter_insert] at hw
      have hstep : regularTangentCone (C a) x ∩ regularTangentCone (⋂ i ∈ T, C i) x ⊆
          regularTangentCone (C a ∩ ⋂ i ∈ T, C i) x :=
        regularTangentCone_inter_subset_inter (hC a) hTclosed ⟨hx a, hTmem⟩ hbin
      have hmem : w ∈ regularTangentCone (C a ∩ ⋂ i ∈ T, C i) x :=
        hstep ⟨hw.1, ihT hw.2⟩
      rwa [Finset.set_biInter_insert]

/-- **Theorem 6.42**, third group: a finite intersection of sets Clarke regular
at `x̄` is Clarke regular there. -/
theorem isClarkeRegularAt_biInter (hC : ∀ i, IsClosed (C i)) (hx : ∀ i, x ∈ C i)
    (hreg : ∀ i, IsClarkeRegularAt (C i) x) (S : Finset ι)
    (htrans : ∀ v : ι → E, (∀ i ∈ S, v i ∈ normalCone (C i) x) →
      ∑ i ∈ S, v i = 0 → ∀ i ∈ S, v i = 0) :
    IsClarkeRegularAt (⋂ i ∈ S, C i) x := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simpa only [Finset.notMem_empty, iInter_of_empty, iInter_univ] using
        isClarkeRegularAt_univ x
  | insert a T ha ih =>
      have hTclosed : IsClosed (⋂ i ∈ T, C i) :=
        isClosed_iInter fun i ↦ isClosed_iInter fun _ ↦ hC i
      have hTmem : x ∈ ⋂ i ∈ T, C i := mem_iInter₂.2 fun i _ ↦ hx i
      have ihT := ih (transversal_of_insert hx ha htrans)
      have hbin := normalTransversal_insert hC hx ha htrans
      rw [Finset.set_biInter_insert]
      exact (isClarkeRegularAt_inter (hC a) hTclosed ⟨hx a, hTmem⟩ hbin (hreg a) ihT).1

/-- **Theorem 6.42**, third group: the normal cone equation under regularity. -/
theorem normalCone_biInter_eq_sum (hC : ∀ i, IsClosed (C i)) (hx : ∀ i, x ∈ C i)
    (hreg : ∀ i, IsClarkeRegularAt (C i) x) (S : Finset ι)
    (htrans : ∀ v : ι → E, (∀ i ∈ S, v i ∈ normalCone (C i) x) →
      ∑ i ∈ S, v i = 0 → ∀ i ∈ S, v i = 0) :
    normalCone (⋂ i ∈ S, C i) x =
      {u : E | ∃ v : ι → E, (∀ i ∈ S, v i ∈ normalCone (C i) x) ∧ ∑ i ∈ S, v i = u} := by
  classical
  refine Subset.antisymm (normalCone_biInter_subset_sum hC hx S htrans) ?_
  rintro u ⟨v, hv, rfl⟩
  have hv' : ∀ i ∈ S, v i ∈ regularNormalCone (C i) x := by
    intro i hi
    rw [← (hreg i).2]
    exact hv i hi
  have hsum := sum_mem_regularNormalCone_biInter (C := C) S hv'
  rw [biInter_coe_finset] at hsum
  exact regularNormalCone_subset_normalCone _ x hsum

/-- **Theorem 6.42**, third group: the tangent cone equation under
regularity. -/
theorem tangentCone_biInter_eq (hC : ∀ i, IsClosed (C i)) (hx : ∀ i, x ∈ C i)
    (hreg : ∀ i, IsClarkeRegularAt (C i) x) (S : Finset ι)
    (htrans : ∀ v : ι → E, (∀ i ∈ S, v i ∈ normalCone (C i) x) →
      ∑ i ∈ S, v i = 0 → ∀ i ∈ S, v i = 0) :
    tangentCone (⋂ i ∈ S, C i) x = ⋂ i ∈ S, tangentCone (C i) x := by
  classical
  have hTmem : x ∈ ⋂ i ∈ S, C i := mem_iInter₂.2 fun i _ ↦ hx i
  refine Subset.antisymm ?_ ?_
  · have hsub := tangentCone_biInter_subset C (S : Set ι) x
    rw [biInter_coe_finset] at hsub
    refine hsub.trans ?_
    exact subset_iInter₂ fun i hi ↦ biInter_subset_of_mem (by simpa using hi)
  · have hreg' : ∀ i ∈ S, tangentCone (C i) x = regularTangentCone (C i) x := fun i _ ↦
      (isClarkeRegularAt_iff_tangentCone_eq (hx i) (hreg i).1).1 (hreg i)
    intro w hw
    have hw' : w ∈ ⋂ i ∈ S, regularTangentCone (C i) x := by
      refine mem_iInter₂.2 fun i hi ↦ ?_
      rw [← hreg' i hi]
      exact mem_iInter₂.1 hw i hi
    exact regularTangentCone_subset_tangentCone hTmem
      (regularTangentCone_biInter_subset hC hx S htrans hw')

end FiniteIntersections

end RW
