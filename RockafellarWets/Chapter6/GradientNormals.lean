/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Regular Normals as Gradients

The differentiable part of Theorem 6.11: regular normals are precisely the
gradients at relative local maxima.  The forward direction is witnessed by a
function with a unique global maximum relative to the set.
-/

import RockafellarWets.Chapter6.NormalCones
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Asymptotics.Lemmas

open Asymptotics Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {C : Set E} {x v : E} {h : E → ℝ}

/-- The easy direction of Theorem 6.11: the gradient at a relative local
maximum is a regular normal.  No convexity assumption is needed. -/
theorem mem_regularNormalCone_of_isLocalMaxOn_hasGradientAt
    (hx : x ∈ C) (hmax : IsLocalMaxOn h C x)
    (hh : HasGradientAt h v x) :
    v ∈ regularNormalCone C x := by
  rw [mem_regularNormalCone]
  refine ⟨hx, fun ε hε ↦ ?_⟩
  have hrem := hasGradientAt_iff_isLittleO.mp hh
  filter_upwards [hmax, (hrem.def hε).filter_mono nhdsWithin_le_nhds] with y hymax hyrem
  calc
    ⟪v, y - x⟫_ℝ ≤ -(h y - h x - ⟪v, y - x⟫_ℝ) := by linarith
    _ ≤ ‖h y - h x - ⟪v, y - x⟫_ℝ‖ := neg_le_abs _
    _ ≤ ε * ‖y - x‖ := hyrem

/-- A regular normal is the gradient of a function having a unique global
maximum relative to the set.  The witness is not asserted to be smooth away
from the base point. -/
theorem exists_hasGradientAt_unique_isMaxOn_of_mem_regularNormalCone
    (hv : v ∈ regularNormalCone C x) :
    ∃ h : E → ℝ,
      HasGradientAt h v x ∧ IsMaxOn h C x ∧
        ∀ y ∈ C, h y = h x → y = x := by
  classical
  let q : E → ℝ := fun y ↦ if y ∈ C then max ⟪v, y - x⟫_ℝ 0 else 0
  let h : E → ℝ := fun y ↦ ⟪v, y - x⟫_ℝ - q y - ‖y - x‖ ^ 2
  have hxC : x ∈ C := hv.1
  have hqx : q x = 0 := by simp [q, hxC]
  have hhx : h x = 0 := by simp [h, hqx]
  have hq : q =o[nhds x] (fun y ↦ y - x) := by
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    have hv' := hv.2 c hc
    rw [eventually_nhdsWithin_iff] at hv'
    filter_upwards [hv'] with y hy
    by_cases hyC : y ∈ C
    · have hupper : max ⟪v, y - x⟫_ℝ 0 ≤ c * ‖y - x‖ := by
        exact max_le (hy hyC) (mul_nonneg hc.le (norm_nonneg _))
      have hnonneg : 0 ≤ max ⟪v, y - x⟫_ℝ 0 := le_max_right _ _
      simpa only [q, if_pos hyC, Real.norm_eq_abs, abs_of_nonneg hnonneg] using hupper
    · simp [q, hyC, mul_nonneg hc.le (norm_nonneg _)]
  have hquad : (fun y : E ↦ ‖y - x‖ ^ 2) =o[nhds x] (fun y ↦ y - x) :=
    isLittleO_pow_sub_sub x one_lt_two
  have hrem : (fun y ↦ -q y + -(‖y - x‖ ^ 2)) =o[nhds x] (fun y ↦ y - x) :=
    hq.neg_left.add hquad.neg_left
  have hgrad : HasGradientAt h v x := by
    rw [hasGradientAt_iff_isLittleO]
    refine hrem.congr_left ?_
    intro y
    simp only [h, hhx]
    ring
  refine ⟨h, hgrad, ?_, ?_⟩
  · rw [isMaxOn_iff]
    intro y hyC
    rw [hhx]
    have hqge : ⟪v, y - x⟫_ℝ ≤ q y := by
      simp only [q, if_pos hyC]
      exact le_max_left _ _
    simp only [h]
    nlinarith [sq_nonneg ‖y - x‖]
  · intro y hyC hy
    have hqge : ⟪v, y - x⟫_ℝ ≤ q y := by
      simp only [q, if_pos hyC]
      exact le_max_left _ _
    have hnormsq : ‖y - x‖ ^ 2 = 0 := by
      rw [hhx] at hy
      simp only [h] at hy
      nlinarith [sq_nonneg ‖y - x‖]
    have : y - x = 0 := by
      rw [sq_eq_zero_iff, norm_eq_zero] at hnormsq
      exact hnormsq
    exact sub_eq_zero.mp this

/-- Pointwise differentiable characterization in Theorem 6.11, with
feasibility stated explicitly because `IsLocalMaxOn` itself does not require
the base point to belong to the set. -/
theorem mem_regularNormalCone_iff_exists_isLocalMaxOn_hasGradientAt
    (hx : x ∈ C) :
    v ∈ regularNormalCone C x ↔
      ∃ h : E → ℝ, IsLocalMaxOn h C x ∧ HasGradientAt h v x := by
  constructor
  · intro hv
    obtain ⟨h, hgrad, hmax, _⟩ :=
      exists_hasGradientAt_unique_isMaxOn_of_mem_regularNormalCone hv
    exact ⟨h, hmax.localize, hgrad⟩
  · rintro ⟨h, hmax, hgrad⟩
    exact mem_regularNormalCone_of_isLocalMaxOn_hasGradientAt hx hmax hgrad

end RW
