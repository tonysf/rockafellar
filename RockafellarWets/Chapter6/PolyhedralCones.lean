/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Tangents and Normals to Polyhedral Sets

Theorem 6.46 and Exercise 6.47.  Near a feasible point, the inactive
inequalities remain strict, so only the active inequalities constrain the
displacement.  This gives the tangent formula and local exactness.  Farkas'
lemma then gives the normal formula with nonnegative active multipliers and
zero inactive multipliers.
-/

import RockafellarWets.Chapter6.ElementaryCones
import RockafellarWets.Chapter6.FarkasPolarCones

open Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {m : ℕ}

/-- A finite system of affine inner-product inequalities is H-polyhedral. -/
theorem isHPolyhedral_setOf_inner_le (a : Fin m → E) (b : Fin m → ℝ) :
    IsHPolyhedral {y : E | ∀ i, ⟪a i, y⟫_ℝ ≤ b i} := by
  refine ⟨m, fun i ↦ innerSL ℝ (a i), b, ?_⟩
  rfl

/-- Near a feasible point, membership in a polyhedron depends only on its
active inequalities. -/
theorem eventually_mem_setOf_inner_le_iff_active {a : Fin m → E} {b : Fin m → ℝ}
    {x : E} (hx : ∀ i, ⟪a i, x⟫_ℝ ≤ b i) :
    ∀ᶠ y in nhds x, (∀ i, ⟪a i, y⟫_ℝ ≤ b i) ↔
      ∀ i, ⟪a i, x⟫_ℝ = b i → ⟪a i, y - x⟫_ℝ ≤ 0 := by
  have hnear : ∀ i, ∀ᶠ y in nhds x,
      ⟪a i, x⟫_ℝ ≠ b i → ⟪a i, y⟫_ℝ < b i := by
    intro i
    by_cases hi : ⟪a i, x⟫_ℝ = b i
    · exact Eventually.of_forall fun _ h ↦ (h hi).elim
    · have hopen : IsOpen {y : E | ⟪a i, y⟫_ℝ < b i} :=
        isOpen_lt (by fun_prop) continuous_const
      have hevent : ∀ᶠ y in nhds x, ⟪a i, y⟫_ℝ < b i :=
        hopen.mem_nhds (lt_of_le_of_ne (hx i) hi)
      exact hevent.mono fun _ hy _ ↦ hy
  filter_upwards [Filter.eventually_all.2 hnear] with y hy
  constructor
  · intro hyC i hi
    rw [inner_sub_right, hi]
    exact sub_nonpos.2 (hyC i)
  · intro hyA i
    by_cases hi : ⟪a i, x⟫_ℝ = b i
    · have h := hyA i hi
      rwa [inner_sub_right, hi, sub_nonpos] at h
    · exact (hy i hi).le

/-- **Theorem 6.46**, tangent formula: precisely the active inequalities
constrain a tangent direction.  This part is dimension-free. -/
theorem tangentCone_setOf_inner_le {a : Fin m → E} {b : Fin m → ℝ}
    {x : E} (hx : ∀ i, ⟪a i, x⟫_ℝ ≤ b i) :
    tangentCone {y : E | ∀ i, ⟪a i, y⟫_ℝ ≤ b i} x =
      {w : E | ∀ i, ⟪a i, x⟫_ℝ = b i → ⟪a i, w⟫_ℝ ≤ 0} := by
  have hconv := (isHPolyhedral_setOf_inner_le a b).convex
  ext w
  constructor
  · intro hw i hi
    apply inner_nonpos_of_mem_regularNormalCone (v := a i) ?_ hw
    rw [regularNormalCone_eq_of_convex hconv hx]
    intro y hy
    rw [inner_sub_right, hi]
    exact sub_nonpos.2 (hy i)
  · intro hw
    apply derivableCone_subset_tangentCone
      (C := {y : E | ∀ i, ⟪a i, y⟫_ℝ ≤ b i}) hx
    apply mem_derivableCone_of_convex hconv hx
    have hline : Tendsto (fun t : ℝ ↦ x + t • w)
        (nhdsWithin 0 (Ioi 0)) (nhds x) := by
      have h : ContinuousAt (fun t : ℝ ↦ x + t • w) 0 := by fun_prop
      simpa using h.tendsto.mono_left nhdsWithin_le_nhds
    have hevent : ∀ᶠ t in nhdsWithin 0 (Ioi (0 : ℝ)),
        0 < t ∧ ∀ i, ⟪a i, x + t • w⟫_ℝ ≤ b i := by
      filter_upwards [self_mem_nhdsWithin,
        hline (eventually_mem_setOf_inner_le_iff_active hx)] with t ht hlocal
      refine ⟨ht, hlocal.2 fun i hi ↦ ?_⟩
      rw [add_sub_cancel_left, real_inner_smul_right]
      exact mul_nonpos_of_nonneg_of_nonpos ht.le (hw i hi)
    obtain ⟨t, ht, hmem⟩ := hevent.exists
    exact ⟨t, ht, hmem⟩

private noncomputable def activeNormalFamily (a : Fin m → E) (b : Fin m → ℝ)
    (x : E) (i : Fin m) : E :=
  if ⟪a i, x⟫_ℝ = b i then a i else 0

private theorem activeCone_eq (a : Fin m → E) (b : Fin m → ℝ) (x : E) :
    {w : E | ∀ i, ⟪a i, x⟫_ℝ = b i → ⟪a i, w⟫_ℝ ≤ 0} =
      {w : E | ∀ i, ⟪activeNormalFamily a b x i, w⟫_ℝ ≤ 0} := by
  ext w
  simp only [mem_setOf_eq]
  apply forall_congr'
  intro i
  by_cases hi : ⟪a i, x⟫_ℝ = b i <;> simp [activeNormalFamily, hi]

/-- The tangent cone of an inequality-defined polyhedron is H-polyhedral. -/
theorem isHPolyhedralCone_tangentCone_setOf_inner_le
    {a : Fin m → E} {b : Fin m → ℝ} {x : E} (hx : ∀ i, ⟪a i, x⟫_ℝ ≤ b i) :
    IsHPolyhedralCone (tangentCone {y : E | ∀ i, ⟪a i, y⟫_ℝ ≤ b i} x) := by
  rw [tangentCone_setOf_inner_le hx, activeCone_eq]
  exact isHPolyhedralCone_setOf_inner_nonpos _

/-- **Theorem 6.46**, normal formula: only active constraints can have a
nonzero multiplier, and those multipliers are nonnegative. -/
theorem normalCone_setOf_inner_le [FiniteDimensional ℝ E]
    {a : Fin m → E} {b : Fin m → ℝ} {x : E} (hx : ∀ i, ⟪a i, x⟫_ℝ ≤ b i) :
    normalCone {y : E | ∀ i, ⟪a i, y⟫_ℝ ≤ b i} x =
      {v : E | ∃ c : Fin m → ℝ,
        (∀ i, ⟪a i, x⟫_ℝ = b i → 0 ≤ c i) ∧
        (∀ i, ⟪a i, x⟫_ℝ ≠ b i → c i = 0) ∧ (∑ i, c i • a i) = v} := by
  classical
  rw [normalCone_eq_polarCone_tangentCone (isHPolyhedral_setOf_inner_le a b).convex hx,
    tangentCone_setOf_inner_le hx, activeCone_eq]
  ext v
  rw [mem_polarCone_setOf_inner_nonpos_iff]
  constructor
  · rintro ⟨c, hc, hsum⟩
    refine ⟨fun i ↦ if ⟪a i, x⟫_ℝ = b i then c i else 0,
      fun i hi ↦ by simpa [hi] using hc i, fun i hi ↦ by simp [hi], ?_⟩
    convert hsum using 1
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : ⟪a i, x⟫_ℝ = b i <;> simp [activeNormalFamily, hi]
  · rintro ⟨c, hc, hinactive, hsum⟩
    refine ⟨c, fun i ↦ ?_, ?_⟩
    · by_cases hi : ⟪a i, x⟫_ℝ = b i
      · exact hc i hi
      · simp [hinactive i hi]
    · convert hsum using 1
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : ⟪a i, x⟫_ℝ = b i
      · simp [activeNormalFamily, hi]
      · simp [activeNormalFamily, hi, hinactive i hi]

/-- **Exercise 6.47**, membership form for a finite inequality system. -/
theorem eventually_mem_setOf_inner_le_iff_sub_mem_tangentCone
    {a : Fin m → E} {b : Fin m → ℝ} {x : E} (hx : ∀ i, ⟪a i, x⟫_ℝ ≤ b i) :
    ∀ᶠ y in nhds x, y ∈ {z : E | ∀ i, ⟪a i, z⟫_ℝ ≤ b i} ↔
      y - x ∈ tangentCone {z : E | ∀ i, ⟪a i, z⟫_ℝ ≤ b i} x := by
  simpa only [tangentCone_setOf_inner_le hx, mem_setOf_eq] using
    eventually_mem_setOf_inner_le_iff_active hx

section GeneralPolyhedra

/-- Riesz representation puts every H-polyhedral set in the inner-product
form used in Theorem 6.46. -/
theorem IsHPolyhedral.exists_inner_representation [CompleteSpace E]
    {C : Set E} (hC : IsHPolyhedral C) :
    ∃ (n : ℕ) (a : Fin n → E) (b : Fin n → ℝ),
      C = {y : E | ∀ i, ⟪a i, y⟫_ℝ ≤ b i} := by
  obtain ⟨n, A, b, rfl⟩ := hC
  refine ⟨n, fun i ↦ (InnerProductSpace.toDual ℝ E).symm (A i), b, ?_⟩
  ext y
  simp [mem_linearInequalitySet]

variable [FiniteDimensional ℝ E]

/-- **Theorem 6.46**: the tangent cone to a polyhedral set is H-polyhedral. -/
theorem IsPolyhedral.isHPolyhedralCone_tangentCone {C : Set E} (hC : IsPolyhedral C)
    {x : E} (hx : x ∈ C) : IsHPolyhedralCone (tangentCone C x) := by
  obtain ⟨m, a, b, rfl⟩ := hC.isHPolyhedral.exists_inner_representation
  exact isHPolyhedralCone_tangentCone_setOf_inner_le hx

/-- **Theorem 6.46**: the normal cone to a polyhedral set is H-polyhedral. -/
theorem IsPolyhedral.isHPolyhedralCone_normalCone {C : Set E} (hC : IsPolyhedral C)
    {x : E} (hx : x ∈ C) : IsHPolyhedralCone (normalCone C x) := by
  rw [normalCone_eq_polarCone_tangentCone hC.isHPolyhedral.convex hx]
  exact (hC.isHPolyhedralCone_tangentCone hx).isHPolyhedralCone_polarCone

/-- The tangent cone is polyhedral in the Chapter 3 generator sense too. -/
theorem IsPolyhedral.isPolyhedral_tangentCone {C : Set E} (hC : IsPolyhedral C)
    {x : E} (hx : x ∈ C) : IsPolyhedral (tangentCone C x) :=
  (hC.isHPolyhedralCone_tangentCone hx).isHPolyhedral.isPolyhedral

/-- The normal cone is polyhedral in the Chapter 3 generator sense too. -/
theorem IsPolyhedral.isPolyhedral_normalCone {C : Set E} (hC : IsPolyhedral C)
    {x : E} (hx : x ∈ C) : IsPolyhedral (normalCone C x) :=
  (hC.isHPolyhedralCone_normalCone hx).isHPolyhedral.isPolyhedral

/-- **Exercise 6.47**: near a point of a polyhedral set, membership is
exactly membership of the displacement in the tangent cone. -/
theorem IsPolyhedral.eventually_mem_iff_sub_mem_tangentCone {C : Set E}
    (hC : IsPolyhedral C) {x : E} (hx : x ∈ C) :
    ∀ᶠ y in nhds x, y ∈ C ↔ y - x ∈ tangentCone C x := by
  obtain ⟨m, a, b, rfl⟩ := hC.isHPolyhedral.exists_inner_representation
  exact eventually_mem_setOf_inner_le_iff_sub_mem_tangentCone hx

/-- **Exercise 6.47**, the printed local set equality: the polyhedron and
its translated tangent cone agree in a neighborhood of the base point. -/
theorem IsPolyhedral.exists_nhds_eq_tangentCone {C : Set E} (hC : IsPolyhedral C)
    {x : E} (hx : x ∈ C) :
    ∃ V ∈ nhds x, C ∩ V = ((fun w ↦ x + w) '' tangentCone C x) ∩ V := by
  obtain ⟨V, hV, hlocal⟩ := (hC.eventually_mem_iff_sub_mem_tangentCone hx).exists_mem
  refine ⟨V, hV, ?_⟩
  ext y
  constructor
  · rintro ⟨hy, hyV⟩
    exact ⟨⟨y - x, (hlocal y hyV).1 hy, by simp⟩, hyV⟩
  · rintro ⟨⟨w, hw, rfl⟩, hyV⟩
    exact ⟨(hlocal (x + w) hyV).2 (by simpa using hw), hyV⟩

end GeneralPolyhedra

end RW
