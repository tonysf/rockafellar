/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: projections on subspaces and on polar pairs of cones

This file formalizes Example 12.21 and Exercise 12.22.

For a linear subspace `M`, the normal cone mapping `N_M` has graph `M × M⊥`, so
it is the maximal monotone mapping of 12.18 for `C = M`, and its inverse is
`N_{M⊥}` (since `M⊥⊥ = M`).  The resolvents `(I + N_M)⁻¹` and
`(I + N_M⁻¹)⁻¹` are the orthogonal projections `M.starProjection` and
`Mᗮ.starProjection` of Mathlib, and they agree with the nearest-point mappings
`P_M` and `P_{M⊥}` of 12.20.

For a closed convex cone `K` with polar `K*`, a vector `v` is normal to `K` at
`x` exactly when `x ∈ K`, `v ∈ K*` and `x ⊥ v`, and `N_K`, `N_{K*}` are inverse
to each other (formula 11(5) of Chapter 11, the guide's route through 11.3 and
11.4).  The Minty parameterization 12.15 of `gph N_K` is then the decomposition
`z = P_K(z) + P_{K*}(z)`.
-/

import RockafellarWets.Chapter12.ProjectionMonotonicity
import RockafellarWets.Chapter12.MintyParameterization
import RockafellarWets.Chapter6.Polarity
import RockafellarWets.Chapter11.SupportConjugates

open Set
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Subspaces

omit [FiniteDimensional ℝ E] in
/-- For `x ∈ M`, the normal cone to a subspace `M` is `M⊥`. -/
theorem normalCone_submodule_of_mem (M : Submodule ℝ E) {x : E} (hx : x ∈ M) :
    normalCone (M : Set E) x = (Mᗮ : Set E) := by
  rw [normalCone_eq_of_convex M.convex hx]
  ext v
  simp only [mem_setOf_eq, SetLike.mem_coe, Submodule.mem_orthogonal']
  constructor
  · intro h u hu
    have h1 := h (x + u) (M.add_mem hx hu)
    have h2 := h (x - u) (M.sub_mem hx hu)
    rw [add_sub_cancel_left] at h1
    rw [sub_sub_cancel_left, inner_neg_right] at h2
    linarith
  · intro h y hy
    rw [h (y - x) (M.sub_mem hy hx)]

omit [FiniteDimensional ℝ E] in
/-- Normal vectors to a subspace: `v ∈ N_M(x) ↔ x ∈ M ∧ v ∈ M⊥`. -/
theorem mem_normalCone_submodule_iff (M : Submodule ℝ E) {x v : E} :
    v ∈ normalCone (M : Set E) x ↔ x ∈ M ∧ v ∈ Mᗮ := by
  constructor
  · intro hv
    have hx : x ∈ M := hv.1
    rw [normalCone_submodule_of_mem M hx] at hv
    exact ⟨hx, hv⟩
  · rintro ⟨hx, hv⟩
    rw [normalCone_submodule_of_mem M hx]
    exact hv

omit [FiniteDimensional ℝ E] in
open Classical in
/-- **Example 12.21**: `N_M(x) = M⊥` for `x ∈ M` and `N_M(x) = ∅` otherwise. -/
theorem normalCone_submodule (M : Submodule ℝ E) (x : E) :
    normalCone (M : Set E) x = if x ∈ M then (Mᗮ : Set E) else ∅ := by
  split_ifs with hx
  · exact normalCone_submodule_of_mem M hx
  · exact normalCone_eq_empty hx

omit [FiniteDimensional ℝ E] in
/-- **Example 12.21**: `gph N_M = M × M⊥`. -/
theorem svGraph_normalCone_submodule (M : Submodule ℝ E) :
    svGraph (normalCone (M : Set E)) = (M : Set E) ×ˢ (Mᗮ : Set E) := by
  ext p
  exact mem_normalCone_submodule_iff M

/-- **Example 12.21**: the inverse of `N_M` is `N_{M⊥}`. -/
theorem svInv_normalCone_submodule (M : Submodule ℝ E) :
    svInv (normalCone (M : Set E)) = normalCone (Mᗮ : Set E) := by
  funext v
  ext x
  rw [mem_svInv, mem_normalCone_submodule_iff, mem_normalCone_submodule_iff,
    Submodule.orthogonal_orthogonal (K := M), and_comm]

open Classical in
/-- **Example 12.21**: `N_M⁻¹(v) = M` for `v ∈ M⊥` and `N_M⁻¹(v) = ∅` otherwise. -/
theorem svInv_normalCone_submodule_apply (M : Submodule ℝ E) (v : E) :
    svInv (normalCone (M : Set E)) v = if v ∈ Mᗮ then (M : Set E) else ∅ := by
  rw [svInv_normalCone_submodule, normalCone_submodule, Submodule.orthogonal_orthogonal (K := M)]

/-- **Example 12.21**: `N_M` is maximal monotone. -/
theorem svMaximalMonotone_normalCone_submodule (M : Submodule ℝ E) :
    SvMaximalMonotone (normalCone (M : Set E)) :=
  svMaximalMonotone_normalCone M.closed_of_finiteDimensional M.convex ⟨0, M.zero_mem⟩

/-- **Example 12.21**: `(I + N_M)⁻¹` is the orthogonal projection onto `M`. -/
theorem svResolvent_normalCone_submodule (M : Submodule ℝ E) :
    svResolvent (normalCone (M : Set E)) 1 = fun z ↦ {M.starProjection z} := by
  funext z
  ext x
  rw [mem_svResolvent, mem_singleton_iff]
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨hx, hv⟩ := (mem_normalCone_submodule_iff M).1 hv
    rw [one_smul]
    exact (Submodule.eq_starProjection_of_mem_orthogonal' (K := M) hx hv rfl).symm
  · rintro rfl
    refine ⟨z - M.starProjection z, (mem_normalCone_submodule_iff M).2
      ⟨M.starProjection_apply_mem z, Submodule.sub_starProjection_mem_orthogonal (K := M) z⟩, ?_⟩
    rw [one_smul]
    abel

/-- **Example 12.21**: `(I + N_M⁻¹)⁻¹` is the orthogonal projection onto `M⊥`. -/
theorem svResolvent_svInv_normalCone_submodule (M : Submodule ℝ E) :
    svResolvent (svInv (normalCone (M : Set E))) 1 = fun z ↦ {Mᗮ.starProjection z} := by
  rw [svInv_normalCone_submodule]
  exact svResolvent_normalCone_submodule Mᗮ

/-- The nearest-point mapping onto a subspace is the orthogonal projection. -/
theorem projMapping_submodule (M : Submodule ℝ E) :
    projMapping (M : Set E) = fun z ↦ {M.starProjection z} := by
  rw [projMapping_eq_svResolvent_normalCone M.convex ⟨0, M.zero_mem⟩]
  exact svResolvent_normalCone_submodule M

open Classical in
/-- **Example 12.21 (projections on subspaces).**  For a linear subspace `M`,
`N_M` is maximal monotone with `gph N_M = M × M⊥`, `N_M(x)` is `M⊥` or `∅`
according to `x ∈ M`, and `N_M⁻¹(v)` is `M` or `∅` according to `v ∈ M⊥`.  The
linear projections onto `M` and `M⊥` are `P_M = (I + N_M)⁻¹` and
`P_{M⊥} = (I + N_M⁻¹)⁻¹`, and they are maximal monotone and nonexpansive. -/
theorem projections_on_subspaces (M : Submodule ℝ E) :
    SvMaximalMonotone (normalCone (M : Set E)) ∧
      svGraph (normalCone (M : Set E)) = (M : Set E) ×ˢ (Mᗮ : Set E) ∧
      (∀ x, normalCone (M : Set E) x = if x ∈ M then (Mᗮ : Set E) else ∅) ∧
      (∀ v, svInv (normalCone (M : Set E)) v = if v ∈ Mᗮ then (M : Set E) else ∅) ∧
      projMapping (M : Set E) = svResolvent (normalCone (M : Set E)) 1 ∧
      projMapping (Mᗮ : Set E) = svResolvent (svInv (normalCone (M : Set E))) 1 ∧
      (∀ z, projMapping (M : Set E) z = {M.starProjection z}) ∧
      (∀ z, projMapping (Mᗮ : Set E) z = {Mᗮ.starProjection z}) ∧
      SvMaximalMonotone (projMapping (M : Set E)) ∧ SvNonexpansive (projMapping (M : Set E)) ∧
      SvMaximalMonotone (projMapping (Mᗮ : Set E)) ∧
      SvNonexpansive (projMapping (Mᗮ : Set E)) := by
  have hT := svMaximalMonotone_normalCone_submodule M
  have hP : projMapping (M : Set E) = svResolvent (normalCone (M : Set E)) 1 := by
    rw [projMapping_submodule, svResolvent_normalCone_submodule]
  have hP' : projMapping (Mᗮ : Set E) = svResolvent (svInv (normalCone (M : Set E))) 1 := by
    rw [projMapping_submodule, svResolvent_svInv_normalCone_submodule]
  refine ⟨hT, svGraph_normalCone_submodule M, normalCone_submodule M,
    svInv_normalCone_submodule_apply M, hP, hP', fun z ↦ by rw [projMapping_submodule],
    fun z ↦ by rw [projMapping_submodule], ?_, ?_, ?_, ?_⟩
  · rw [hP]
    exact hT.svMaximalMonotone_svResolvent one_pos
  · rw [hP]
    exact hT.1.svNonexpansive_svResolvent zero_le_one
  · rw [hP']
    exact hT.inv.svMaximalMonotone_svResolvent one_pos
  · rw [hP']
    exact hT.inv.1.svNonexpansive_svResolvent zero_le_one

end Subspaces

section PolarCones

variable {K : Set E}

/-- Normal vectors to a convex cone in the form of 12.22:
`v ∈ N_K(x) ↔ x ∈ K, v ∈ K*, x ⊥ v` (formula 11(5)). -/
theorem mem_normalCone_cone_iff' (hconv : Convex ℝ K) (hcone : IsCone K) {x v : E} :
    v ∈ normalCone K x ↔ x ∈ K ∧ v ∈ polarCone K ∧ ⟪x, v⟫_ℝ = 0 := by
  rw [mem_normalCone_cone_iff hconv hcone, real_inner_comm x v]

/-- For a closed convex cone, `N_K` and `N_{K*}` are inverse to each other. -/
theorem svInv_normalCone_cone (hK : IsClosed K) (hconv : Convex ℝ K) (hcone : IsCone K) :
    svInv (normalCone K) = normalCone (polarCone K) := by
  funext v
  ext x
  rw [mem_svInv]
  exact mem_normalCone_iff_mem_normalCone_polar hconv hK hcone

/-- **Exercise 12.22 (projections on a polar pair of cones).**  For a closed
convex cone `K` with polar `K*`, every `z` is uniquely `z = x + v` with
`x ∈ K`, `v ∈ K*` and `x ⊥ v`, namely `x = P_K(z)` and `v = P_{K*}(z)`, and
these projection mappings are maximal monotone and nonexpansive. -/
theorem projections_on_polar_cones (hK : IsClosed K) (hconv : Convex ℝ K) (hcone : IsCone K) :
    (∀ z x v, (x ∈ K ∧ v ∈ polarCone K ∧ ⟪x, v⟫_ℝ = 0 ∧ z = x + v) ↔
        (projMapping K z = {x} ∧ projMapping (polarCone K) z = {v})) ∧
      (∀ z, ∃! p : E × E, p.1 ∈ K ∧ p.2 ∈ polarCone K ∧ ⟪p.1, p.2⟫_ℝ = 0 ∧ z = p.1 + p.2) ∧
      SvMaximalMonotone (projMapping K) ∧ SvNonexpansive (projMapping K) ∧
      SvMaximalMonotone (projMapping (polarCone K)) ∧
      SvNonexpansive (projMapping (polarCone K)) := by
  have hne : K.Nonempty := ⟨0, hcone.1⟩
  have hT := svMaximalMonotone_normalCone hK hconv hne
  have hP : projMapping K = svResolvent (normalCone K) 1 :=
    projMapping_eq_svResolvent_normalCone hconv hne
  have hP' : projMapping (polarCone K) = svResolvent (svInv (normalCone K)) 1 := by
    rw [svInv_normalCone_cone hK hconv hcone]
    exact projMapping_eq_svResolvent_normalCone (convex_polarCone K) ⟨0, zero_mem_polarCone K⟩
  have key : ∀ z x v, (projMapping K z = {x} ∧ projMapping (polarCone K) z = {v}) ↔
      z = x + v ∧ v ∈ normalCone K x := by
    intro z x v
    rw [hP, hP', hT.svResolvent_eq_singleton_resolventMap one_pos,
      hT.inv.svResolvent_eq_singleton_resolventMap one_pos, singleton_eq_singleton_iff,
      singleton_eq_singleton_iff, ← Prod.mk.injEq]
    exact hT.mintyMap_eq_iff
  refine ⟨fun z x v ↦ ?_, fun z ↦ ?_, ?_, ?_, ?_, ?_⟩
  · rw [key, mem_normalCone_cone_iff' hconv hcone]
    constructor
    · rintro ⟨hx, hv, hxv, hz⟩
      exact ⟨hz, hx, hv, hxv⟩
    · rintro ⟨hz, hx, hv, hxv⟩
      exact ⟨hx, hv, hxv, hz⟩
  · obtain ⟨hz, hmem⟩ := (hT.mintyMap_eq_iff (z := z)).1 rfl
    obtain ⟨hx, hv, hxv⟩ := (mem_normalCone_cone_iff' hconv hcone).1 hmem
    refine ⟨mintyMap (normalCone K) z, ⟨hx, hv, hxv, hz⟩, ?_⟩
    rintro ⟨x, v⟩ ⟨hx', hv', hxv', hz'⟩
    exact ((hT.mintyMap_eq_iff).2
      ⟨hz', (mem_normalCone_cone_iff' hconv hcone).2 ⟨hx', hv', hxv'⟩⟩).symm
  · rw [hP]
    exact hT.svMaximalMonotone_svResolvent one_pos
  · rw [hP]
    exact hT.1.svNonexpansive_svResolvent zero_le_one
  · rw [hP']
    exact hT.inv.svMaximalMonotone_svResolvent one_pos
  · rw [hP']
    exact hT.inv.1.svNonexpansive_svResolvent zero_le_one

end PolarCones

end RW
