/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Smooth level-set geometry
-/

import RockafellarWets.Chapter10.LevelSetNormals
import RockafellarWets.Chapter8.SmoothSubderivativeRegularity
import RockafellarWets.Chapter8.SubgradientsAndGradients

open Filter Set Topology
open scoped InnerProductSpace Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The positive hull of one vector is its nonnegative ray. -/
theorem positiveHull_singleton (v : E) :
    positiveHull ({v}:Set E) = {z | ∃ a : ℝ, 0 ≤ a ∧ z = a • v} := by
  ext z
  constructor
  · rintro (rfl | ⟨a,ha,y,hy,rfl⟩)
    · exact ⟨0,le_rfl,by simp⟩
    · exact ⟨a,ha.le,by rw [mem_singleton_iff.mp hy]⟩
  · rintro ⟨a,ha,rfl⟩
    rcases eq_or_lt_of_le ha with rfl | ha
    · exact Or.inl (zero_smul ℝ v)
    · exact Or.inr ⟨a,ha,v,rfl,rfl⟩

/-- The smooth specialization following Proposition 10.3. -/
theorem levelSet_geometry_of_smooth {f : E → ℝ} {x : E}
    (hf : ContDiff ℝ 1 f) (hz : gradient f x ≠ 0) :
    let C := {y | f y ≤ f x}
    IsClarkeRegularAt C x ∧
      tangentCone C x = {w | ⟪gradient f x,w⟫_ℝ ≤ 0} ∧
      normalCone C x = {z | ∃ a : ℝ, 0 ≤ a ∧ z = a • gradient f x} := by
  have he : levelSet (fun y ↦ (f y:EReal)) (f x) = {y | f y ≤ f x} := by
    ext y
    exact EReal.coe_le_coe_iff
  obtain ⟨hs,hh,-⟩ := subdifferentials_of_smooth (hf.contDiffAt (x := x))
  have hr := (regularSubderivatives_of_smooth (x := x) (U := univ) univ_mem hf.contDiffOn).1
  have hz' : (0:E) ∉ subdifferential (fun y ↦ (f y:EReal)) x := by
    rw [hs,mem_singleton_iff]
    exact Ne.symm hz
  obtain ⟨hreg,hTC,hNC⟩ := levelSet_geometry_of_regular
    (f := fun y ↦ (f y:EReal))
    (continuous_coe_real_ereal.comp hf.continuous).lowerSemicontinuous rfl hz' hr
  rw [he] at hreg hTC hNC
  refine ⟨hreg,?_,?_⟩
  · rw [hTC]
    ext w
    simp only [mem_setOf_eq]
    rw [(smooth_subderivatives_eq_inner_gradient (x := x) (U := univ) univ_mem hf.contDiffOn w).1]
    exact EReal.coe_nonpos
  · rw [hNC,hs,hh,union_eq_left.mpr (singleton_subset_iff.mpr (zero_mem_positiveHull _)),
      positiveHull_singleton]

end RW
