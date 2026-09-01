/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Supporting Halfspaces

Theorem 6.20: a nonempty closed convex set in a finite-dimensional real
inner-product space is the intersection of the closed halfspaces supporting
it.  Conversely, arbitrary intersections of closed halfspaces are closed and
convex.  The homogeneous specialization gives the corresponding description
of closed convex cones.
-/

import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import RockafellarWets.Chapter3.Cones
import RockafellarWets.Chapter5.ProjectionMappings
import RockafellarWets.Chapter6.ConvexSets

open Set Topology
open scoped InnerProductSpace

namespace RW

section SupportingHalfspaces

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The closed halfspace through `x` with outward normal `v`. -/
def supportingHalfspace (x v : E) : Set E :=
  {y | ⟪v, y - x⟫_ℝ ≤ 0}

@[simp]
theorem mem_supportingHalfspace {x v y : E} :
    y ∈ supportingHalfspace x v ↔ ⟪v, y - x⟫_ℝ ≤ 0 :=
  Iff.rfl

@[simp]
theorem supportPoint_mem_supportingHalfspace (x v : E) :
    x ∈ supportingHalfspace x v := by
  simp

/-- The point defining a supporting halfspace lies on its boundary hyperplane. -/
@[simp]
theorem supportingHalfspace_boundary_eq (x v : E) :
    ⟪v, x - x⟫_ℝ = 0 := by
  simp

/-- Every halfspace given by an inner-product inequality is closed. -/
theorem isClosed_supportingHalfspace (x v : E) :
    IsClosed (supportingHalfspace x v) := by
  change IsClosed {y : E | (fun z : E ↦ ⟪v, z - x⟫_ℝ) y ≤ (fun _ : E ↦ (0 : ℝ)) y}
  exact isClosed_le (by fun_prop) (by fun_prop)

/-- Every halfspace given by an inner-product inequality is convex. -/
theorem convex_supportingHalfspace (x v : E) :
    Convex ℝ (supportingHalfspace x v) := by
  intro y hy z hz a b ha hb hab
  change ⟪v, a • y + b • z - x⟫_ℝ ≤ 0
  have heq : a • y + b • z - x = a • (y - x) + b • (z - x) := by
    calc
      a • y + b • z - x = a • y + b • z - (a + b) • x := by
        rw [hab, one_smul]
      _ = a • (y - x) + b • (z - x) := by module
  rw [heq, inner_add_right, inner_smul_right, inner_smul_right]
  exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hy)
    (mul_nonpos_of_nonneg_of_nonpos hb hz)

/-- `supportingHalfspace x v` supports `C` when `x` belongs to `C`, `v` is
nonzero, and the whole set lies in the halfspace. -/
def IsSupportingHalfspace (C : Set E) (x v : E) : Prop :=
  x ∈ C ∧ v ≠ 0 ∧ C ⊆ supportingHalfspace x v

/-- The family of all halfspaces supporting `C` at one of its points. -/
def supportingHalfspaces (C : Set E) : Set (Set E) :=
  {H | ∃ x v, IsSupportingHalfspace C x v ∧ H = supportingHalfspace x v}

@[simp]
theorem mem_supportingHalfspaces {C : Set E} {H : Set E} :
    H ∈ supportingHalfspaces C ↔
      ∃ x v, IsSupportingHalfspace C x v ∧ H = supportingHalfspace x v :=
  Iff.rfl

theorem IsSupportingHalfspace.supportPoint_mem {C : Set E} {x v : E}
    (h : IsSupportingHalfspace C x v) : x ∈ C :=
  h.1

theorem IsSupportingHalfspace.normal_ne_zero {C : Set E} {x v : E}
    (h : IsSupportingHalfspace C x v) : v ≠ 0 :=
  h.2.1

/-- Every supporting halfspace contains the set it supports. -/
theorem IsSupportingHalfspace.subset {C : Set E} {x v : E}
    (h : IsSupportingHalfspace C x v) : C ⊆ supportingHalfspace x v :=
  h.2.2

/-- A member of `supportingHalfspaces C` contains `C`. -/
theorem subset_of_mem_supportingHalfspaces {C H : Set E}
    (hH : H ∈ supportingHalfspaces C) : C ⊆ H := by
  obtain ⟨x, v, hv, rfl⟩ := hH
  exact hv.subset

/-- The variational inequality satisfied by a nearest point of a convex set,
in the spelling used for supporting halfspaces. -/
private theorem projection_inner_le_zero {C : Set E} (hC : Convex ℝ C)
    {z x : E} (hx : x ∈ projMapping C z) :
    ∀ y ∈ C, ⟪z - x, y - x⟫_ℝ ≤ 0 := by
  have hxC : x ∈ C := hx.1
  letI : Nonempty C := ⟨⟨x, hxC⟩⟩
  have hEq : ‖z - x‖ = ⨅ w : C, ‖z - (w : E)‖ := by
    apply le_antisymm
    · refine le_ciInf fun w ↦ ?_
      simpa [norm_sub_rev] using hx.2 (w : E) w.2
    · refine ciInf_le ?_ (⟨x, hxC⟩ : C)
      refine ⟨0, ?_⟩
      rintro _ ⟨w, rfl⟩
      exact norm_nonneg (z - (w : E))
  exact (norm_eq_iInf_iff_real_inner_le_zero hC hxC).1 hEq

/-- Point separation by a genuinely supporting halfspace.  The support point
is a nearest point of `C` to the point being separated. -/
theorem exists_supportingHalfspace_separating [FiniteDimensional ℝ E]
    {C : Set E} (hne : C.Nonempty) (hclosed : IsClosed C) (hconv : Convex ℝ C)
    {z : E} (hz : z ∉ C) :
    ∃ x v, IsSupportingHalfspace C x v ∧ z ∉ supportingHalfspace x v := by
  obtain ⟨x, hx⟩ := projMapping_nonempty hclosed hne z
  let v : E := z - x
  have hv : v ≠ 0 := by
    intro hv0
    apply hz
    have hzx : z = x := sub_eq_zero.mp (by simpa [v] using hv0)
    simpa [hzx] using hx.1
  have hs : IsSupportingHalfspace C x v := by
    refine ⟨hx.1, hv, ?_⟩
    intro y hy
    exact projection_inner_le_zero hconv hx y hy
  refine ⟨x, v, hs, ?_⟩
  rw [mem_supportingHalfspace, not_le]
  change 0 < ⟪z - x, z - x⟫_ℝ
  rw [real_inner_self_eq_norm_sq]
  exact sq_pos_of_pos (norm_pos_iff.mpr (by simpa [v] using hv))

/-- **Theorem 6.20 (supporting-halfspace envelope).** A nonempty closed
convex set is exactly the intersection of the halfspaces supporting it at
points of the set. -/
theorem eq_sInter_supportingHalfspaces [FiniteDimensional ℝ E]
    {C : Set E} (hne : C.Nonempty) (hclosed : IsClosed C) (hconv : Convex ℝ C) :
    C = ⋂₀ supportingHalfspaces C := by
  apply Subset.antisymm
  · intro y hy
    rw [mem_sInter]
    intro H hH
    exact subset_of_mem_supportingHalfspaces hH hy
  · intro z hz
    by_contra hzC
    obtain ⟨x, v, hs, hzout⟩ :=
      exists_supportingHalfspace_separating hne hclosed hconv hzC
    exact hzout (mem_sInter.mp hz (supportingHalfspace x v) ⟨x, v, hs, rfl⟩)

/-! ### Arbitrary intersections of closed halfspaces -/

/-- An arbitrary set-indexed intersection of closed halfspaces is closed. -/
theorem isClosed_sInter_halfspaces {A : Set (Set E)}
    (hA : ∀ H ∈ A, ∃ x v, H = supportingHalfspace x v) :
    IsClosed (⋂₀ A) := by
  refine isClosed_sInter fun H hH ↦ ?_
  obtain ⟨x, v, rfl⟩ := hA H hH
  exact isClosed_supportingHalfspace x v

/-- An arbitrary set-indexed intersection of closed halfspaces is convex. -/
theorem convex_sInter_halfspaces {A : Set (Set E)}
    (hA : ∀ H ∈ A, ∃ x v, H = supportingHalfspace x v) :
    Convex ℝ (⋂₀ A) := by
  refine convex_sInter fun H hH ↦ ?_
  obtain ⟨x, v, rfl⟩ := hA H hH
  exact convex_supportingHalfspace x v

/-- The indexed version of closedness of arbitrary halfspace intersections. -/
theorem isClosed_iInter_supportingHalfspace {I : Sort*} (x v : I → E) :
    IsClosed (⋂ i, supportingHalfspace (x i) (v i)) :=
  isClosed_iInter fun i ↦ isClosed_supportingHalfspace (x i) (v i)

/-- The indexed version of convexity of arbitrary halfspace intersections. -/
theorem convex_iInter_supportingHalfspace {I : Sort*} (x v : I → E) :
    Convex ℝ (⋂ i, supportingHalfspace (x i) (v i)) :=
  convex_iInter fun i ↦ convex_supportingHalfspace (x i) (v i)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- The intersection of the empty family of halfspaces is the whole space. -/
@[simp]
theorem sInter_empty_halfspaces :
    ⋂₀ (∅ : Set (Set E)) = (univ : Set E) := by
  simp

/-! ### Homogeneous halfspaces and cones -/

/-- The supporting halfspaces through the origin. -/
def homogeneousSupportingHalfspaces (C : Set E) : Set (Set E) :=
  {H | ∃ v, IsSupportingHalfspace C 0 v ∧ H = supportingHalfspace 0 v}

@[simp]
theorem mem_homogeneousSupportingHalfspaces {C H : Set E} :
    H ∈ homogeneousSupportingHalfspaces C ↔
      ∃ v, IsSupportingHalfspace C 0 v ∧ H = supportingHalfspace 0 v :=
  Iff.rfl

/-- A halfspace through the origin is a cone. -/
theorem isCone_supportingHalfspace_zero (v : E) :
    IsCone (supportingHalfspace (0 : E) v) := by
  constructor
  · simp
  · intro y hy c hc
    change ⟪v, c • y - 0⟫_ℝ ≤ 0
    have hy' : ⟪v, y⟫_ℝ ≤ 0 := by
      simpa using hy
    simpa [inner_smul_right] using
      (mul_nonpos_of_nonneg_of_nonpos hc.le hy')

/-- If an affine halfspace contains a cone, translating its boundary to the
origin (without changing its normal) still leaves a halfspace containing the
cone. -/
theorem IsCone.subset_supportingHalfspace_zero {C : Set E} (hcone : IsCone C)
    {x v : E} (hsub : C ⊆ supportingHalfspace x v) :
    C ⊆ supportingHalfspace 0 v := by
  have hzero := hsub hcone.1
  have hxnonneg : 0 ≤ ⟪v, x⟫_ℝ := by
    change ⟪v, (0 : E) - x⟫_ℝ ≤ 0 at hzero
    rw [zero_sub, inner_neg_right] at hzero
    linarith
  intro y hy
  change ⟪v, y - 0⟫_ℝ ≤ 0
  simp only [sub_zero]
  by_contra hynonpos
  have hypos : 0 < ⟪v, y⟫_ℝ := lt_of_not_ge hynonpos
  let c : ℝ := ⟪v, x⟫_ℝ / ⟪v, y⟫_ℝ + 1
  have hc : 0 < c := by
    have hquot : 0 ≤ ⟪v, x⟫_ℝ / ⟪v, y⟫_ℝ :=
      div_nonneg hxnonneg hypos.le
    dsimp [c]
    linarith
  have hcy := hsub (hcone.2 hy hc)
  change ⟪v, c • y - x⟫_ℝ ≤ 0 at hcy
  rw [inner_sub_right, inner_smul_right] at hcy
  have hcval : c * ⟪v, y⟫_ℝ = ⟪v, x⟫_ℝ + ⟪v, y⟫_ℝ := by
    dsimp [c]
    field_simp
  rw [hcval] at hcy
  linarith

/-- A supporting halfspace of a cone can be replaced by a homogeneous one
with the same normal. -/
theorem IsCone.homogeneousSupportingHalfspace {C : Set E} (hcone : IsCone C)
    {x v : E} (hs : IsSupportingHalfspace C x v) :
    IsSupportingHalfspace C 0 v :=
  ⟨hcone.1, hs.normal_ne_zero, hcone.subset_supportingHalfspace_zero hs.subset⟩

/-- At a support point of a cone, the affine threshold is necessarily zero. -/
theorem IsCone.inner_supportPoint_eq_zero {C : Set E} (hcone : IsCone C)
    {x v : E} (hs : IsSupportingHalfspace C x v) :
    ⟪v, x⟫_ℝ = 0 := by
  have hnonneg : 0 ≤ ⟪v, x⟫_ℝ := by
    have hzero := hs.subset hcone.1
    change ⟪v, (0 : E) - x⟫_ℝ ≤ 0 at hzero
    rw [zero_sub, inner_neg_right] at hzero
    linarith
  have hnonpos : ⟪v, x⟫_ℝ ≤ 0 := by
    have hx := (hcone.homogeneousSupportingHalfspace hs).subset hs.supportPoint_mem
    simpa using hx
  exact le_antisymm hnonpos hnonneg

/-- The intersection of all homogeneous supporting halfspaces is closed. -/
theorem isClosed_sInter_homogeneousSupportingHalfspaces (C : Set E) :
    IsClosed (⋂₀ homogeneousSupportingHalfspaces C) := by
  apply isClosed_sInter_halfspaces
  intro H hH
  obtain ⟨v, -, rfl⟩ := hH
  exact ⟨0, v, rfl⟩

/-- The intersection of all homogeneous supporting halfspaces is convex. -/
theorem convex_sInter_homogeneousSupportingHalfspaces (C : Set E) :
    Convex ℝ (⋂₀ homogeneousSupportingHalfspaces C) := by
  apply convex_sInter_halfspaces
  intro H hH
  obtain ⟨v, -, rfl⟩ := hH
  exact ⟨0, v, rfl⟩

/-- The intersection of all homogeneous supporting halfspaces is a cone,
also when the family is empty (in which case the intersection is `univ`). -/
theorem isCone_sInter_homogeneousSupportingHalfspaces (C : Set E) :
    IsCone (⋂₀ homogeneousSupportingHalfspaces C) := by
  constructor
  · rw [mem_sInter]
    intro H hH
    obtain ⟨v, hs, rfl⟩ := hH
    exact (isCone_supportingHalfspace_zero v).1
  · intro y hy c hc
    rw [mem_sInter] at hy ⊢
    intro H hH
    obtain ⟨v, hs, rfl⟩ := hH
    exact (isCone_supportingHalfspace_zero v).2
      (hy (supportingHalfspace 0 v) ⟨v, hs, rfl⟩) hc

/-- The homogeneous envelope is always a closed convex cone. -/
theorem sInter_homogeneousSupportingHalfspaces_is_closed_convex_cone (C : Set E) :
    IsClosed (⋂₀ homogeneousSupportingHalfspaces C) ∧
      Convex ℝ (⋂₀ homogeneousSupportingHalfspaces C) ∧
        IsCone (⋂₀ homogeneousSupportingHalfspaces C) :=
  ⟨isClosed_sInter_homogeneousSupportingHalfspaces C,
    convex_sInter_homogeneousSupportingHalfspaces C,
    isCone_sInter_homogeneousSupportingHalfspaces C⟩

/-- **Theorem 6.20, homogeneous specialization.** A nonempty closed convex
cone is the intersection of its supporting halfspaces through the origin. -/
theorem eq_sInter_homogeneousSupportingHalfspaces [FiniteDimensional ℝ E]
    {C : Set E} (hne : C.Nonempty) (hclosed : IsClosed C) (hconv : Convex ℝ C)
    (hcone : IsCone C) :
    C = ⋂₀ homogeneousSupportingHalfspaces C := by
  apply Subset.antisymm
  · intro y hy
    rw [mem_sInter]
    intro H hH
    obtain ⟨v, hs, rfl⟩ := hH
    exact hs.subset hy
  · intro z hz
    by_contra hzC
    obtain ⟨x, v, hs, hzout⟩ :=
      exists_supportingHalfspace_separating hne hclosed hconv hzC
    have hs0 := hcone.homogeneousSupportingHalfspace hs
    have hzout0 : z ∉ supportingHalfspace 0 v := by
      intro hzin
      apply hzout
      have hzle : ⟪v, z⟫_ℝ ≤ 0 := by
        simpa using hzin
      change ⟪v, z - x⟫_ℝ ≤ 0
      rw [inner_sub_right, hcone.inner_supportPoint_eq_zero hs, sub_zero]
      exact hzle
    exact hzout0
      (mem_sInter.mp hz (supportingHalfspace 0 v) ⟨v, hs0, rfl⟩)

/-! ### Clarke regularity -/

/-- **Theorem 6.20 (regularity clause).** Every point of a closed convex set
is a point of Clarke regularity. -/
theorem isClarkeRegularAt_of_closed_convex {C : Set E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) {x : E} (hx : x ∈ C) :
    IsClarkeRegularAt C x := by
  apply isClarkeRegularAt_of_convex hconv hx
  exact ⟨univ, Filter.univ_mem, isClosed_univ, by simpa using hclosed⟩

end SupportingHalfspaces

end RW
