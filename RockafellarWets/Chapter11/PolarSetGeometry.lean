/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Boundedness, polyhedrality, and horizon cones under general polarity
-/

import RockafellarWets.Chapter11.PolarSets
import RockafellarWets.Chapter3.MinkowskiWeyl

open Set Metric Topology Bornology
open scoped InnerProductSpace Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Bounded sets have a polar containing a neighborhood of the origin. -/
theorem mem_interior_polarSet_zero_of_isBounded {C : Set E} (hb : IsBounded C) :
    (0 : E) ∈ interior (polarSet C) := by
  obtain ⟨R,hR⟩ := hb.exists_norm_le
  have hpos : 0 < |R|+1 := by positivity
  apply mem_interior_iff_mem_nhds.mpr
  apply Metric.mem_nhds_iff.mpr
  refine ⟨(|R|+1)⁻¹, inv_pos.mpr hpos, ?_⟩
  intro v hv x hx
  have hv' : ‖v‖ < (|R|+1)⁻¹ := by simpa using hv
  have hx' : ‖x‖ ≤ |R|+1 := (hR x hx).trans (by linarith [le_abs_self R])
  calc
    ⟪v,x⟫_ℝ ≤ ‖v‖ * ‖x‖ := (le_abs_self _).trans (abs_real_inner_le_norm v x)
    _ ≤ (|R|+1)⁻¹ * (|R|+1) := mul_le_mul hv'.le hx' (norm_nonneg _) (inv_nonneg.mpr hpos.le)
    _ = 1 := inv_mul_cancel₀ hpos.ne'

/-- A neighborhood of zero in the polar gives a uniform bound on the original set. -/
theorem isBounded_of_mem_interior_polarSet_zero {C : Set E}
    (h0 : (0 : E) ∈ interior (polarSet C)) : IsBounded C := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h0)
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨2/ε, fun x hx ↦ ?_⟩
  by_cases hx0 : x = 0
  · simp only [hx0,norm_zero]
    positivity
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  let t : ℝ := ε/(2*‖x‖)
  have ht : 0 < t := div_pos hε (by positivity)
  have htn : t*‖x‖ = ε/2 := by dsimp [t]; field_simp
  have hmem : t • x ∈ ball (0:E) ε := by
    simp only [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht, htn]
    linarith
  have hbound := hball hmem x hx
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq] at hbound
  have hlin : (ε/2)*‖x‖ ≤ 1 := by nlinarith [htn]
  apply (le_div_iff₀ hε).mpr
  nlinarith

theorem isBounded_iff_zero_mem_interior_polarSet (C : Set E) :
    IsBounded C ↔ (0 : E) ∈ interior (polarSet C) :=
  ⟨mem_interior_polarSet_zero_of_isBounded, isBounded_of_mem_interior_polarSet_zero⟩

@[simp] theorem polarCone_positiveHull (C : Set E) :
    polarCone (positiveHull C) = polarCone C := by
  refine Subset.antisymm (polarCone_antitone subset_positiveHull) ?_
  intro v hv x hx
  rcases hx with rfl | ⟨t,ht,z,hz,rfl⟩
  · simp
  · rw [real_inner_smul_right]
    exact mul_nonpos_of_nonneg_of_nonpos ht.le (hv z hz)

variable [FiniteDimensional ℝ E]

/-- The symmetric boundedness/interiority equivalence in Exercise 11.20(a). -/
theorem isBounded_polarSet_iff_zero_mem_interior {C : Set E} (hc : Convex ℝ C)
    (hclosed : IsClosed C) (h0 : (0 : E) ∈ C) :
    IsBounded (polarSet C) ↔ (0 : E) ∈ interior C := by
  rw [isBounded_iff_zero_mem_interior_polarSet, polarSet_bipolar_eq_self hc hclosed h0]

/-- Exercise 11.20(c), in the direction involving the horizon of the polar. -/
theorem horizonCone_polarSet {C : Set E} (hc : Convex ℝ C)
    (hclosed : IsClosed C) (h0 : (0 : E) ∈ C) :
    horizonCone (polarSet C) = polarCone (positiveHull C) := by
  rw [(horizonCone_polar_effectiveDomain_supportFunction (isClosed_polarSet C)
    (convex_polarSet C) ⟨0,zero_mem_polarSet C⟩).1,
    supportFunction_polarSet_eq_gaugeFunction hc hclosed h0, effectiveDomain_gaugeFunction]

/-- The other horizon identity in Exercise 11.20(c). -/
theorem horizonCone_eq_polarCone_positiveHull_polarSet {C : Set E} (hc : Convex ℝ C)
    (hclosed : IsClosed C) (h0 : (0 : E) ∈ C) :
    horizonCone C = polarCone (positiveHull (polarSet C)) := by
  have h := horizonCone_polarSet (convex_polarSet C) (isClosed_polarSet C) (zero_mem_polarSet C)
  rwa [polarSet_bipolar_eq_self hc hclosed h0] at h

/-- A finite convex-plus-conic description dualizes to finitely many inequalities. -/
theorem polarSet_convexHull_add_closure_conicHull {s t : Finset E} (hs : s.Nonempty) :
    polarSet (convexHull ℝ (s:Set E) + closure (conicHull (t:Set E))) =
      {v | (∀x∈s, ⟪v,x⟫_ℝ ≤ 1) ∧ (∀x∈t, ⟪v,x⟫_ℝ ≤ 0)} := by
  have hz : (0:E) ∈ closure (conicHull (t:Set E)) := subset_closure (zero_mem_conicHull _)
  obtain ⟨z,hzmem⟩ := hs
  have hzconv := subset_convexHull ℝ (s:Set E) hzmem
  ext v
  constructor
  · intro hv
    refine ⟨fun x hx ↦ by simpa using hv (x+0) ⟨x,subset_convexHull ℝ _ hx,0,hz,rfl⟩, ?_⟩
    intro x hx
    by_contra! hp
    let r : ℝ := (|⟪v,z⟫_ℝ|+2)/⟪v,x⟫_ℝ
    have hr : 0 < r := div_pos (by positivity) hp
    have hm : r • x ∈ closure (conicHull (t:Set E)) :=
      subset_closure ((isCone_conicHull _).2 (subset_conicHull hx) hr)
    have hb := hv (z+r • x) ⟨z,hzconv,r • x,hm,rfl⟩
    rw [inner_add_right, real_inner_smul_right] at hb
    have he : r*⟪v,x⟫_ℝ = |⟪v,z⟫_ℝ|+2 := div_mul_cancel₀ _ hp.ne'
    nlinarith [neg_abs_le ⟪v,z⟫_ℝ]
  · rintro ⟨hs,ht⟩ x ⟨a,ha,b,hb,rfl⟩
    have hsa : v ∈ polarSet (convexHull ℝ (s:Set E)) := by
      rw [polarSet_convexHull]; exact hs
    have htb : v ∈ polarCone (closure (conicHull (t:Set E))) := by
      rw [polarCone_closure_conicHull]; exact ht
    rw [inner_add_right]
    linarith [hsa a ha, htb b hb]

theorem IsClosedPolyhedral.polarSet {C : Set E} (hc : IsClosedPolyhedral C)
    (hne : C.Nonempty) : IsClosedPolyhedral (polarSet C) := by
  obtain ⟨s,t,hs,rfl⟩ := hc.exists_nonempty_generators_of_nonempty hne
  rw [polarSet_convexHull_add_closure_conicHull hs]
  have hset : {v : E | (∀x∈s, ⟪v,x⟫_ℝ ≤ 1) ∧ (∀x∈t, ⟪v,x⟫_ℝ ≤ 0)} =
      (⋂x∈s, {v : E | ⟪v,x⟫_ℝ ≤ 1}) ∩ (⋂x∈t, {v : E | ⟪v,x⟫_ℝ ≤ 0}) := by ext; simp
  rw [hset]
  apply IsPolyhedral.isClosedPolyhedral
  apply IsHPolyhedral.isPolyhedral
  apply IsHPolyhedral.inter
  · exact IsHPolyhedral.iInter_finset s _ fun x _ ↦ by
      simpa [real_inner_comm] using IsHPolyhedral.halfspace (innerSL ℝ x) 1
  · exact IsHPolyhedral.iInter_finset t _ fun x _ ↦ by
      simpa [real_inner_comm] using IsHPolyhedral.halfspace (innerSL ℝ x) 0

/-- Exercise 11.20(b): polyhedrality is invariant under polarity. -/
theorem isClosedPolyhedral_polarSet_iff {C : Set E} (hc : Convex ℝ C)
    (hclosed : IsClosed C) (h0 : (0 : E) ∈ C) :
    IsClosedPolyhedral (polarSet C) ↔ IsClosedPolyhedral C := by
  refine ⟨fun hp ↦ ?_, fun hp ↦ hp.polarSet ⟨0,h0⟩⟩
  have h := hp.polarSet ⟨0,zero_mem_polarSet C⟩
  rwa [polarSet_bipolar_eq_self hc hclosed h0] at h

end RW
