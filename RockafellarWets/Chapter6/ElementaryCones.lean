/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Locality and Elementary Cone Formulas

The four elementary cones depend only on the germ of the underlying set at
the base point.  This file records that locality, the corresponding eventual
congruence lemmas, and the basic formulas for the whole space, a singleton,
and an interior point.
-/

import RockafellarWets.Chapter6.ChangeOfCoordinates
import RockafellarWets.Chapter6.ConvexSets

open Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

section TangentLocality

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivable cone is local: a path may be restricted to the part of its
domain on which it lies in a prescribed neighborhood of the base point. -/
theorem derivableCone_inter_nhds {C U : Set E} {x : E} (hU : U ∈ nhds x) :
    derivableCone (C ∩ U) x = derivableCone C x := by
  ext w
  constructor
  · rintro ⟨ε, hε, ξ, hξ0, hξCU, hξt⟩
    exact ⟨ε, hε, ξ, hξ0, fun t ht ↦ (hξCU t ht).1, hξt⟩
  · rintro ⟨ε, hε, ξ, hξ0, hξC, hξt⟩
    have hzero : Tendsto (fun t : ℝ ↦ t) (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hdiff : Tendsto (fun t ↦ ξ t - x) (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := by
      have hmul := hzero.smul hξt
      rw [zero_smul] at hmul
      apply hmul.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    have hξ : Tendsto ξ (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds x) := by
      have hadd := hdiff.const_add x
      simpa using hadd
    have hξU : ∀ᶠ t in nhdsWithin 0 (Ioi (0 : ℝ)), ξ t ∈ U := hξ hU
    obtain ⟨δ, hδ, hδU⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1 hξU
    refine ⟨min ε δ, lt_min hε hδ, ξ, hξ0, ?_, hξt⟩
    intro t ht
    refine ⟨hξC t ⟨ht.1, ht.2.trans (min_le_left _ _)⟩, ?_⟩
    by_cases ht0 : t = 0
    · simpa [ht0, hξ0] using mem_of_mem_nhds hU
    · exact hδU ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),
        ht.2.trans (min_le_right _ _)⟩

end TangentLocality

section NormalLocality

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The regular normal cone is local.  Near the base point, restricting the
set to a neighborhood leaves the relative-neighborhood filter in its
definition unchanged; at points off the set both sides are empty. -/
theorem regularNormalCone_inter_nhds {C U : Set E} {x : E} (hU : U ∈ nhds x) :
    regularNormalCone (C ∩ U) x = regularNormalCone C x := by
  have hxU : x ∈ U := mem_of_mem_nhds hU
  by_cases hxC : x ∈ C
  · have hfilter : nhdsWithin x (C ∩ U) = nhdsWithin x C :=
      nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds hU)
    ext v
    simp only [regularNormalCone, mem_setOf_eq, mem_inter_iff, hxC, hxU,
      true_and, hfilter]
  · have hxCU : x ∉ C ∩ U := fun hx ↦ hxC hx.1
    rw [regularNormalCone_eq_empty hxCU, regularNormalCone_eq_empty hxC]

/-- The limiting normal cone is local.  On a smaller open neighborhood the
regular-normal mappings agree pointwise; tails of the defining sequences can
therefore be transported in either direction. -/
theorem normalCone_inter_nhds {C U : Set E} {x : E} (hU : U ∈ nhds x) :
    normalCone (C ∩ U) x = normalCone C x := by
  have hxU : x ∈ U := mem_of_mem_nhds hU
  have hreg : regularNormalCone (C ∩ U) =ᶠ[nhds x] regularNormalCone C := by
    obtain ⟨V, hVU, hVopen, hxV⟩ := _root_.mem_nhds_iff.1 hU
    filter_upwards [hVopen.mem_nhds hxV] with y hyV
    exact regularNormalCone_inter_nhds
      (mem_of_superset (hVopen.mem_nhds hyV) hVU)
  refine Subset.antisymm ?_ ?_
  · rintro v ⟨hxCU, xs, vs, -, hxto, hvs, hvto⟩
    have hmap : ∀ᶠ n in atTop,
        regularNormalCone (C ∩ U) (xs n) = regularNormalCone C (xs n) := hxto hreg
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hmap
    refine mem_normalCone_of_forall hxCU.1
      (hxto.comp (tendsto_add_atTop_nat N)) ?_
      (hvto.comp (tendsto_add_atTop_nat N))
    intro n
    change vs (n + N) ∈ regularNormalCone C (xs (n + N))
    rw [← hN _ (Nat.le_add_left N n)]
    exact hvs _
  · rintro v ⟨hxC, xs, vs, -, hxto, hvs, hvto⟩
    have hmap : ∀ᶠ n in atTop,
        regularNormalCone (C ∩ U) (xs n) = regularNormalCone C (xs n) := hxto hreg
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hmap
    refine mem_normalCone_of_forall ⟨hxC, hxU⟩
      (hxto.comp (tendsto_add_atTop_nat N)) ?_
      (hvto.comp (tendsto_add_atTop_nat N))
    intro n
    change vs (n + N) ∈ regularNormalCone (C ∩ U) (xs (n + N))
    rw [hN _ (Nat.le_add_left N n)]
    exact hvs _

end NormalLocality

section GermCongruence

private theorem exists_inter_nhds_eq_of_eventuallyEq
    {α : Type*} [TopologicalSpace α] {C D : Set α} {x : α}
    (h : C =ᶠ[nhds x] D) : ∃ U ∈ nhds x, C ∩ U = D ∩ U := by
  obtain ⟨U, hU, hCD⟩ := h.exists_mem
  refine ⟨U, hU, ?_⟩
  ext y
  constructor
  · rintro ⟨hyC, hyU⟩
    exact ⟨Eq.mp (hCD hyU) hyC, hyU⟩
  · rintro ⟨hyD, hyU⟩
    exact ⟨Eq.mp (hCD hyU).symm hyD, hyU⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Tangent cones agree when the sets have the same germ at the base point. -/
theorem tangentCone_congr_nhds {C D : Set E} {x : E} (h : C =ᶠ[nhds x] D) :
    tangentCone C x = tangentCone D x := by
  obtain ⟨U, hU, hCD⟩ := exists_inter_nhds_eq_of_eventuallyEq h
  calc
    tangentCone C x = tangentCone (C ∩ U) x := (tangentCone_inter_nhds hU).symm
    _ = tangentCone (D ∩ U) x := congrArg (fun S : Set E ↦ tangentCone S x) hCD
    _ = tangentCone D x := tangentCone_inter_nhds hU

/-- Derivable cones agree when the sets have the same germ at the base point. -/
theorem derivableCone_congr_nhds {C D : Set E} {x : E} (h : C =ᶠ[nhds x] D) :
    derivableCone C x = derivableCone D x := by
  obtain ⟨U, hU, hCD⟩ := exists_inter_nhds_eq_of_eventuallyEq h
  calc
    derivableCone C x = derivableCone (C ∩ U) x := (derivableCone_inter_nhds hU).symm
    _ = derivableCone (D ∩ U) x := congrArg (fun S : Set E ↦ derivableCone S x) hCD
    _ = derivableCone D x := derivableCone_inter_nhds hU

end GermCongruence

section InnerProductGermCongruence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Regular normal cones agree when the sets have the same germ at the base point. -/
theorem regularNormalCone_congr_nhds {C D : Set E} {x : E} (h : C =ᶠ[nhds x] D) :
    regularNormalCone C x = regularNormalCone D x := by
  obtain ⟨U, hU, hCD⟩ := exists_inter_nhds_eq_of_eventuallyEq h
  calc
    regularNormalCone C x = regularNormalCone (C ∩ U) x :=
      (regularNormalCone_inter_nhds hU).symm
    _ = regularNormalCone (D ∩ U) x :=
      congrArg (fun S : Set E ↦ regularNormalCone S x) hCD
    _ = regularNormalCone D x := regularNormalCone_inter_nhds hU

/-- Limiting normal cones agree when the sets have the same germ at the base point. -/
theorem normalCone_congr_nhds {C D : Set E} {x : E} (h : C =ᶠ[nhds x] D) :
    normalCone C x = normalCone D x := by
  obtain ⟨U, hU, hCD⟩ := exists_inter_nhds_eq_of_eventuallyEq h
  calc
    normalCone C x = normalCone (C ∩ U) x := (normalCone_inter_nhds hU).symm
    _ = normalCone (D ∩ U) x := congrArg (fun S : Set E ↦ normalCone S x) hCD
    _ = normalCone D x := normalCone_inter_nhds hU

end InnerProductGermCongruence

section ElementaryTangents

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every vector is derivable tangent to the whole space. -/
@[simp]
theorem derivableCone_univ (x : E) : derivableCone (Set.univ : Set E) x = Set.univ := by
  apply eq_univ_iff_forall.2
  intro w
  refine ⟨1, one_pos, fun t ↦ x + t • w, by simp, fun _ _ ↦ mem_univ _, ?_⟩
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]

/-- Every vector is tangent to the whole space. -/
@[simp]
theorem tangentCone_univ (x : E) : tangentCone (Set.univ : Set E) x = Set.univ := by
  apply eq_univ_iff_forall.2
  intro w
  apply derivableCone_subset_tangentCone (mem_univ x)
  rw [derivableCone_univ]
  exact mem_univ w

/-- The only tangent vector to a singleton at its point is zero. -/
@[simp]
theorem tangentCone_singleton (x : E) : tangentCone ({x} : Set E) x = {0} := by
  refine Subset.antisymm ?_ ?_
  · rintro w ⟨xs, τs, hxs, -, -, -, hq⟩
    have hq0 : Tendsto (fun n ↦ (τs n)⁻¹ • (xs n - x)) atTop (nhds (0 : E)) := by
      convert tendsto_const_nhds using 1
      funext n
      have hxn : xs n = x := by simpa using hxs n
      simp [hxn]
    have hw : w = 0 := tendsto_nhds_unique hq hq0
    simp [hw]
  · intro w hw
    have hw0 : w = 0 := by simpa using hw
    subst w
    exact (isCone_tangentCone (C := ({x} : Set E)) (by simp)).1

/-- The only derivable tangent vector to a singleton at its point is zero. -/
@[simp]
theorem derivableCone_singleton (x : E) : derivableCone ({x} : Set E) x = {0} := by
  refine Subset.antisymm ?_ ?_
  · intro w hw
    have hwt : w ∈ tangentCone ({x} : Set E) x :=
      derivableCone_subset_tangentCone (by simp) hw
    simpa using hwt
  · intro w hw
    have hw0 : w = 0 := by simpa using hw
    subst w
    exact ⟨1, one_pos, fun _ ↦ x, rfl, fun _ _ ↦ by simp, by simp⟩

/-- The whole space is geometrically derivable everywhere. -/
@[simp]
theorem isGeometricallyDerivable_univ (x : E) :
    IsGeometricallyDerivable (Set.univ : Set E) x := by
  simp [IsGeometricallyDerivable]

/-- A singleton is geometrically derivable at its point. -/
@[simp]
theorem isGeometricallyDerivable_singleton (x : E) :
    IsGeometricallyDerivable ({x} : Set E) x := by
  simp [IsGeometricallyDerivable]

end ElementaryTangents

section ElementaryNormals

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The regular normal cone to the empty set is empty.  The general off-set
formula is `regularNormalCone_eq_empty`. -/
@[simp]
theorem regularNormalCone_empty (x : E) :
    regularNormalCone (∅ : Set E) x = ∅ :=
  regularNormalCone_eq_empty (by simp)

/-- The limiting normal cone to the empty set is empty.  The general off-set
formula is `normalCone_eq_empty`. -/
@[simp]
theorem normalCone_empty (x : E) : normalCone (∅ : Set E) x = ∅ :=
  normalCone_eq_empty (by simp)

/-- The only regular normal to the whole space is zero. -/
@[simp]
theorem regularNormalCone_univ (x : E) :
    regularNormalCone (Set.univ : Set E) x = {0} := by
  rw [regularNormalCone_eq_of_convex convex_univ (mem_univ x)]
  ext v
  constructor
  · intro hv
    rw [mem_singleton_iff]
    apply real_inner_self_nonpos.mp
    simpa using hv (x + v) (mem_univ _)
  · intro hv
    rw [mem_singleton_iff] at hv
    subst v
    simp

/-- The limiting normal cone to the whole space is also just zero. -/
@[simp]
theorem normalCone_univ (x : E) : normalCone (Set.univ : Set E) x = {0} := by
  rw [normalCone_eq_regularNormalCone_of_convex convex_univ (mem_univ x),
    regularNormalCone_univ]

/-- Every vector is a regular normal to a singleton at its point. -/
@[simp]
theorem regularNormalCone_singleton (x : E) :
    regularNormalCone ({x} : Set E) x = Set.univ := by
  rw [regularNormalCone_eq_of_convex (convex_singleton x) (by simp)]
  ext v
  simp

/-- Every vector is a limiting normal to a singleton at its point. -/
@[simp]
theorem normalCone_singleton (x : E) : normalCone ({x} : Set E) x = Set.univ := by
  rw [normalCone_eq_regularNormalCone_of_convex (convex_singleton x) (by simp),
    regularNormalCone_singleton]

/-- The whole space is Clarke regular everywhere. -/
@[simp]
theorem isClarkeRegularAt_univ (x : E) :
    IsClarkeRegularAt (Set.univ : Set E) x :=
  isClarkeRegularAt_of_convex convex_univ (mem_univ x)
    ⟨Set.univ, univ_mem, isClosed_univ, by simp⟩

/-- A singleton is Clarke regular at its point. -/
@[simp]
theorem isClarkeRegularAt_singleton (x : E) :
    IsClarkeRegularAt ({x} : Set E) x :=
  isClarkeRegularAt_of_convex (convex_singleton x) (by simp)
    ⟨Set.univ, univ_mem, isClosed_univ, by simp⟩

end ElementaryNormals

section InteriorPoints

/-- Every interior point is a point of local closedness.  Regularity of the
ambient topology supplies a closed neighborhood contained in the set. -/
theorem isLocallyClosedAt_of_mem_interior {E : Type*} [TopologicalSpace E]
    [RegularSpace E] {C : Set E} {x : E} (hx : x ∈ interior C) :
    IsLocallyClosedAt C x := by
  obtain ⟨V, hV, hVclosed, hVC⟩ :=
    exists_mem_nhds_isClosed_subset (mem_interior_iff_mem_nhds.1 hx)
  exact ⟨V, hV, hVclosed, by simpa [inter_eq_right.2 hVC] using hVclosed⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- At an interior point every vector is tangent. -/
theorem tangentCone_eq_univ_of_mem_interior {C : Set E} {x : E}
    (hx : x ∈ interior C) : tangentCone C x = Set.univ := by
  have hC : C ∈ nhds x := mem_interior_iff_mem_nhds.1 hx
  simpa using (tangentCone_inter_nhds (C := Set.univ) hC)

/-- At an interior point every vector is derivable tangent. -/
theorem derivableCone_eq_univ_of_mem_interior {C : Set E} {x : E}
    (hx : x ∈ interior C) : derivableCone C x = Set.univ := by
  have hC : C ∈ nhds x := mem_interior_iff_mem_nhds.1 hx
  simpa using (derivableCone_inter_nhds (C := Set.univ) hC)

/-- Every interior point is a point of geometric derivability. -/
theorem isGeometricallyDerivable_of_mem_interior {C : Set E} {x : E}
    (hx : x ∈ interior C) : IsGeometricallyDerivable C x := by
  rw [IsGeometricallyDerivable, tangentCone_eq_univ_of_mem_interior hx,
    derivableCone_eq_univ_of_mem_interior hx]

end InteriorPoints

section InnerProductInteriorPoints

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The regular normal cone at an interior point is just zero. -/
theorem regularNormalCone_eq_singleton_of_mem_interior {C : Set E} {x : E}
    (hx : x ∈ interior C) : regularNormalCone C x = {0} := by
  have hC : C ∈ nhds x := mem_interior_iff_mem_nhds.1 hx
  simpa using (regularNormalCone_inter_nhds (C := Set.univ) hC)

/-- The limiting normal cone at an interior point is just zero. -/
theorem normalCone_eq_singleton_of_mem_interior {C : Set E} {x : E}
    (hx : x ∈ interior C) : normalCone C x = {0} := by
  have hC : C ∈ nhds x := mem_interior_iff_mem_nhds.1 hx
  simpa using (normalCone_inter_nhds (C := Set.univ) hC)

/-- Every interior point is Clarke regular. -/
theorem isClarkeRegularAt_of_mem_interior {C : Set E} {x : E}
    (hx : x ∈ interior C) : IsClarkeRegularAt C x := by
  exact ⟨isLocallyClosedAt_of_mem_interior hx, by
    rw [normalCone_eq_singleton_of_mem_interior hx,
      regularNormalCone_eq_singleton_of_mem_interior hx]⟩

end InnerProductInteriorPoints

end RW
