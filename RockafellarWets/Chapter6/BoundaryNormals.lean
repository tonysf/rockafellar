/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Normals at Boundary Points

Exercise 6.19: a point of a closed set is on its boundary exactly when it
has a nonzero limiting normal, and is interior exactly when its normal
cone is the zero cone.  The boundary construction gives a unit normal by
projecting nearby exterior points and passing to a convergent subsequence.

For arbitrary sets, regular normals extend to the closure at points of the
original set, and limiting normals are included in those of the closure.
-/

import RockafellarWets.Chapter6.ElementaryCones
import RockafellarWets.Chapter6.ProximalNormals

open Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A regular normal to a set is also a regular normal to its closure.
The local defining inequality extends by continuity. -/
theorem regularNormalCone_subset_closure (C : Set E) (x : E) :
    regularNormalCone C x ⊆ regularNormalCone (closure C) x := by
  intro v hv
  obtain ⟨hx, hv⟩ := mem_regularNormalCone_iff.1 hv
  refine mem_regularNormalCone_iff.2 ⟨subset_closure hx, fun ε hε ↦ ?_⟩
  obtain ⟨δ, hδ, hbound⟩ := hv ε hε
  refine ⟨δ, hδ, fun y hy hyd ↦ ?_⟩
  let H : Set E := {z | ⟪v, z - x⟫_ℝ ≤ ε * ‖z - x‖}
  have hH : IsClosed H := isClosed_le (by fun_prop) (by fun_prop)
  have hsub : ball x δ ∩ C ⊆ H := by
    intro z hz
    exact hbound z hz.2 (by simpa [dist_eq_norm] using hz.1)
  apply closure_minimal hsub hH
  apply isOpen_ball.inter_closure
  exact ⟨by simpa [dist_eq_norm] using hyd, hy⟩

/-- Taking the closure preserves regular normals at points of the set. -/
theorem regularNormalCone_closure {C : Set E} {x : E} (hx : x ∈ C) :
    regularNormalCone (closure C) x = regularNormalCone C x := by
  refine Subset.antisymm ?_ (regularNormalCone_subset_closure C x)
  intro v hv
  refine mem_regularNormalCone_iff.2 ⟨hx, fun ε hε ↦ ?_⟩
  obtain ⟨δ, hδ, hbound⟩ := (mem_regularNormalCone_iff.1 hv).2 ε hε
  exact ⟨δ, hδ, fun y hy ↦ hbound y (subset_closure hy)⟩

/-- **Exercise 6.19**, the nonclosed-set clause: limiting normals to a set
are limiting normals to its closure. -/
theorem normalCone_subset_closure (C : Set E) (x : E) :
    normalCone C x ⊆ normalCone (closure C) x := by
  rintro v ⟨hx, xs, vs, -, hxto, hvs, hvto⟩
  exact mem_normalCone_of_forall (subset_closure hx) hxto
    (fun n ↦ regularNormalCone_subset_closure C (xs n) (hvs n)) hvto

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- **Exercise 6.19**: every boundary point of a closed set has a limiting
normal of unit length. -/
theorem exists_unit_normal_of_mem_frontier {C : Set E} (hC : IsClosed C)
    {x : E} (hx : x ∈ frontier C) :
    ∃ v ∈ normalCone C x, ‖v‖ = 1 := by
  classical
  have hxC : x ∈ C := hC.frontier_subset hx
  have hxext : x ∈ closure Cᶜ := by
    rw [frontier_eq_closure_inter_closure] at hx
    exact hx.2
  obtain ⟨zs, hzsC, hzsto⟩ := mem_closure_iff_seq_limit.1 hxext
  choose ps hps using fun n ↦ projMapping_nonempty hC ⟨x, hxC⟩ (zs n)
  have hdist : ∀ n, ‖ps n - x‖ ≤ 2 * ‖zs n - x‖ := by
    intro n
    have hmin := (hps n).2 x hxC
    have htri : ‖ps n - x‖ ≤ ‖ps n - zs n‖ + ‖zs n - x‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    rw [norm_sub_rev x (zs n)] at hmin
    linarith
  have hpsto : Tendsto ps atTop (nhds x) := by
    apply tendsto_iff_norm_sub_tendsto_zero.2
    apply squeeze_zero (fun n ↦ norm_nonneg _) hdist
    simpa using (hzsto.sub_const x).norm.const_mul 2
  have hne : ∀ n, zs n - ps n ≠ 0 := by
    intro n h
    apply hzsC n
    rw [sub_eq_zero.1 h]
    exact (hps n).1
  let vs : ℕ → E := fun n ↦ ‖zs n - ps n‖⁻¹ • (zs n - ps n)
  have hvsnorm : ∀ n, ‖vs n‖ = 1 := by
    intro n
    exact norm_smul_inv_norm (hne n)
  have hvsreg : ∀ n, vs n ∈ regularNormalCone C (ps n) := fun n ↦
    nonneg_smul_sub_mem_regularNormalCone_of_mem_projMapping (hps n)
      (inv_nonneg.2 (norm_nonneg _))
  have hvssphere : ∀ n, vs n ∈ sphere (0 : E) 1 := by
    intro n
    simpa only [mem_sphere, dist_zero_right] using hvsnorm n
  obtain ⟨v, hvsphere, φ, hφ, hvto⟩ :=
    (isCompact_sphere (0 : E) 1).tendsto_subseq hvssphere
  refine ⟨v, mem_normalCone_of_forall hxC (hpsto.comp hφ.tendsto_atTop)
    (fun n ↦ hvsreg (φ n)) hvto, ?_⟩
  simpa only [mem_sphere, dist_zero_right] using hvsphere

/-- **Exercise 6.19**: the boundary of a closed set consists exactly of the
points with a nonzero limiting normal.  Feasibility follows from membership
in the normal cone, so no separate hypothesis `x ∈ C` is needed. -/
theorem mem_frontier_iff_exists_nonzero_normal {C : Set E} (hC : IsClosed C)
    {x : E} : x ∈ frontier C ↔ ∃ v ∈ normalCone C x, v ≠ 0 := by
  constructor
  · intro hx
    obtain ⟨v, hv, hnorm⟩ := exists_unit_normal_of_mem_frontier hC hx
    refine ⟨v, hv, ?_⟩
    intro hzero
    simp [hzero] at hnorm
  · rintro ⟨v, hv, hne⟩
    rw [hC.frontier_eq]
    refine ⟨hv.1, fun hx ↦ hne ?_⟩
    rw [normalCone_eq_singleton_of_mem_interior hx] at hv
    exact mem_singleton_iff.1 hv

/-- The boundary criterion can equivalently require a unit normal. -/
theorem mem_frontier_iff_exists_unit_normal {C : Set E} (hC : IsClosed C)
    {x : E} : x ∈ frontier C ↔ ∃ v ∈ normalCone C x, ‖v‖ = 1 := by
  refine ⟨exists_unit_normal_of_mem_frontier hC, ?_⟩
  rintro ⟨v, hv, hnorm⟩
  apply (mem_frontier_iff_exists_nonzero_normal hC).2
  refine ⟨v, hv, ?_⟩
  intro hzero
  simp [hzero] at hnorm

/-- **Exercise 6.19**: a point is interior to a closed set exactly when its
limiting normal cone is the zero cone. -/
theorem mem_interior_iff_normalCone_eq_singleton {C : Set E} (hC : IsClosed C)
    {x : E} : x ∈ interior C ↔ normalCone C x = {0} := by
  refine ⟨normalCone_eq_singleton_of_mem_interior, fun hzero ↦ ?_⟩
  have hmem : (0 : E) ∈ normalCone C x := by rw [hzero]; simp
  by_contra hx
  have hxfront : x ∈ frontier C := by
    rw [hC.frontier_eq]
    exact ⟨hmem.1, hx⟩
  obtain ⟨v, hv, hne⟩ := (mem_frontier_iff_exists_nonzero_normal hC).1 hxfront
  rw [hzero] at hv
  exact hne (mem_singleton_iff.1 hv)

end FiniteDimensional

end RW
