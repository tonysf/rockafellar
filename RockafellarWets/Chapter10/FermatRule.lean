/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The generalized Fermat rule
-/

import RockafellarWets.Chapter8.RegularSubgradientBridge
import RockafellarWets.Chapter8.ConvexSubgradients
import RockafellarWets.Chapter8.SubdifferentialRegularityCriterion
import RockafellarWets.Chapter8.SubgradientsAndGradients

open Filter Set Topology
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {f g : E → EReal} {x : E} {c : ℝ}

/-- **Theorem 10.1**: a finite local minimum has zero as a regular subgradient.
Neither lower semicontinuity nor global properness is required for this step. -/
theorem IsLocalMin.zero_mem_regularSubdifferential (hm : IsLocalMin f x) (hx : f x = c) :
    (0:E) ∈ regularSubdifferential f x := by
  refine ⟨c,hx,fun ε hε ↦ ?_⟩
  filter_upwards [hm] with y hy
  have hlow : ((c + ⟪(0:E),y-x⟫_ℝ - ε * ‖y-x‖ : ℝ) : EReal) ≤ (c: EReal) := by
    apply EReal.coe_le_coe_iff.mpr
    simp only [inner_zero_left,add_zero,sub_le_self_iff]
    exact mul_nonneg hε.le (norm_nonneg _)
  exact hlow.trans (hx ▸ hy)

/-- **Theorem 10.1**: limiting stationarity at a finite local minimum. -/
theorem IsLocalMin.zero_mem_subdifferential (hm : IsLocalMin f x) (hx : f x = c) :
    (0:E) ∈ subdifferential f x :=
  regularSubdifferential_subset_subdifferential f x (RW.IsLocalMin.zero_mem_regularSubdifferential hm hx)

variable [FiniteDimensional ℝ E]

/-- The first-order directional condition is exactly regular stationarity. -/
theorem subderivative_nonneg_iff_zero_mem_regularSubdifferential (hx : f x = c) :
    (∀ w, 0 ≤ subderivative f x w) ↔ (0:E) ∈ regularSubdifferential f x := by
  rw [mem_regularSubdifferential_iff_inner_le_subderivative hx]
  simp only [inner_zero_left,EReal.coe_zero]

/-- **Theorem 10.1**, both necessary conditions together. -/
theorem IsLocalMin.fermat (hm : IsLocalMin f x) (hx : f x = c) :
    (∀ w, 0 ≤ subderivative f x w) ∧ (0:E) ∈ subdifferential f x :=
  ⟨(subderivative_nonneg_iff_zero_mem_regularSubdifferential hx).mpr
    (RW.IsLocalMin.zero_mem_regularSubdifferential hm hx),RW.IsLocalMin.zero_mem_subdifferential hm hx⟩

/-- Under subdifferential regularity the two stationarity conditions coincide. -/
theorem subderivative_nonneg_iff_zero_mem_subdifferential_of_regular
    (hx : f x = c) (hr : IsSubdifferentiallyRegularAt f x) :
    (∀ w, 0 ≤ subderivative f x w) ↔ (0:E) ∈ subdifferential f x := by
  rw [hr.subdifferential_eq_regularSubdifferential]
  exact subderivative_nonneg_iff_zero_mem_regularSubdifferential hx

/-- **Theorem 10.1**, convex stationarity is necessary and sufficient for a
global minimum, without requiring a closed epigraph. -/
theorem mem_argmin_iff_zero_mem_subdifferential_of_convex
    (hc : Convex ℝ (epigraph f)) (hp : IsProper f) (hx : f x = c) :
    x ∈ argmin f ↔ (0:E) ∈ subdifferential f x := by
  rw [mem_subdifferential_iff_of_convex hc hp hx]
  simp only [inner_zero_left,add_zero]
  constructor
  · intro hm y
    rw [← hx,hm.1]
    exact iInf_le _ y
  · intro h
    have he : f x = ⨅ y, f y := le_antisymm (le_iInf (fun y ↦ hx ▸ h y)) (iInf_le _ x)
    exact ⟨he,he ▸ hx.trans_lt (EReal.coe_lt_top c)⟩

/-- **Theorem 10.1**, the limiting condition after adding a smooth function. -/
theorem zero_mem_subdifferential_add_smooth_iff {k : E → ℝ}
    (hx : g x = c) (hk : ContDiffAt ℝ 1 k x) :
    (0:E) ∈ subdifferential (fun y ↦ g y + (k y:EReal)) x ↔
      -gradient k x ∈ subdifferential g x := by
  rw [(subdifferentials_add_smooth hx hk).2.1]
  constructor
  · rintro ⟨v,hv,hv0⟩
    have he : v = -gradient k x := eq_neg_of_add_eq_zero_left hv0
    exact he ▸ hv
  · intro h
    exact ⟨-gradient k x,h,neg_add_cancel _⟩

/-- **Theorem 10.1**, the directional condition after adding a smooth function. -/
theorem subderivative_nonneg_add_smooth_iff {k : E → ℝ}
    (hx : g x = c) (hk : ContDiffAt ℝ 1 k x) :
    (∀ w, 0 ≤ subderivative (fun y ↦ g y + (k y:EReal)) x w) ↔
      ∀ w, ((-⟪gradient k x,w⟫_ℝ : ℝ) : EReal) ≤ subderivative g x w := by
  have hfx : g x + (k x:EReal) = ((c+k x:ℝ):EReal) := by rw [hx,EReal.coe_add]
  rw [subderivative_nonneg_iff_zero_mem_regularSubdifferential
    (f := fun y : E ↦ g y + (k y:EReal)) (x := x) hfx,
    (subdifferentials_add_smooth hx hk).1]
  have he : (0:E) ∈ (fun v ↦ v+gradient k x) '' regularSubdifferential g x ↔
      -gradient k x ∈ regularSubdifferential g x := by
    constructor
    · rintro ⟨v,hv,hv0⟩
      exact (eq_neg_of_add_eq_zero_left hv0) ▸ hv
    · exact fun h ↦ ⟨-gradient k x,h,neg_add_cancel _⟩
  rw [he,mem_regularSubdifferential_iff_inner_le_subderivative hx]
  simp only [inner_neg_left]

end RW
