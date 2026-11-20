/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lipschitz continuity and quantitative bounds for convex functions
-/

import RockafellarWets.Chapter9.LipschitzModulus
import RockafellarWets.Chapter8.ConvexSubgradients
import RockafellarWets.Chapter8.ConvexEnvelopes
import Mathlib.Analysis.Convex.Continuous

open Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Example 9.14.** A finite convex function on an open convex set is
strictly continuous at each point of that set. -/
theorem strictlyContinuousAt_of_convexOn {f : E → ℝ} {O : Set E} (hO : IsOpen O)
    (hf : ConvexOn ℝ O f) {x : E} (hx : x ∈ O) : StrictlyContinuousAt f x := by
  obtain ⟨k,U,hU,hL⟩ := hf.locallyLipschitzOn hO hx
  rw [nhdsWithin_eq_nhds.mpr (hO.mem_nhds hx)] at hU
  exact strictlyContinuousAt_iff.mpr ⟨k,U,hU,hL⟩

/-- Proper convex functions have subgradients at every point in the interior
of their effective domain. -/
theorem subdifferential_nonempty_of_convex_interior {f : E → EReal} (hc : Convex ℝ (epigraph f))
    (hp : IsProper f) {x : E} (hx : x ∈ interior (effectiveDomain f)) :
    (subdifferential f x).Nonempty := by
  obtain ⟨l,b,hs,hxval⟩ := exists_affineSupport_at_of_mem_interior hc hp hx
  refine ⟨(InnerProductSpace.toDual ℝ E).symm l,(mem_subdifferential_iff_of_convex hc hp hxval).mpr ?_⟩
  intro y
  have he : (l x+b) + ⟪(InnerProductSpace.toDual ℝ E).symm l,y-x⟫_ℝ = l y+b := by
    rw [InnerProductSpace.toDual_symm_apply,map_sub]
    ring
  rw [he]
  exact hs.1 y

/-- **Example 9.14**, the sharp subgradient bound obtained from a lower
bound at the base point and an upper bound on the surrounding closed ball. -/
theorem norm_subgradient_le_of_convex_bounds {f : E → EReal} (hc : Convex ℝ (epigraph f))
    (hp : IsProper f) {x v : E} {α β ε : ℝ} (hε : 0 < ε) (hlo : (α:EReal) ≤ f x)
    (hhi : ∀ z ∈ closedBall x ε, f z ≤ (β:EReal)) (hv : v ∈ subdifferential f x) :
    ‖v‖ ≤ (β-α)/ε := by
  obtain ⟨c,hcx⟩ := hv.1
  have hα : α ≤ c := EReal.coe_le_coe_iff.mp (hcx ▸ hlo)
  have hβ : c ≤ β := EReal.coe_le_coe_iff.mp (hcx ▸ hhi x (mem_closedBall_self hε.le))
  rcases eq_or_ne v 0 with rfl | hv0
  · simp only [norm_zero]
    exact div_nonneg (by linarith) hε.le
  let z := x + (ε / ‖v‖) • v
  have hz : z ∈ closedBall x ε := by
    rw [mem_closedBall,dist_eq_norm,show z-x = (ε/‖v‖) • v by simp [z],norm_smul,Real.norm_eq_abs,
      abs_of_pos (div_pos hε (norm_pos_iff.mpr hv0)),div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hv0)]
  have hsup := ((mem_subdifferential_iff_of_convex hc hp hcx).mp hv z).trans (hhi z hz)
  rw [EReal.coe_le_coe_iff,show z-x = (ε/‖v‖) • v by simp [z],inner_smul_right,
    real_inner_self_eq_norm_sq] at hsup
  rw [le_div_iff₀ hε]
  have heq : ε / ‖v‖ * ‖v‖ ^ 2 = ε * ‖v‖ := by
    field_simp [norm_ne_zero_iff.mpr hv0]
  rw [heq] at hsup
  linarith

/-- **Example 9.14**, Lipschitz continuity on any set with the stated
uniform bounds on its enlargement. The set itself may be nonconvex. -/
theorem lipschitzOnWith_of_convex_bounds {f : E → EReal} (hc : Convex ℝ (epigraph f))
    (hp : IsProper f) {X : Set E} {α β ε : ℝ} (hε : 0 < ε)
    (hlo : ∀ x ∈ X, (α:EReal) ≤ f x)
    (hhi : ∀ x ∈ X, ∀ z ∈ closedBall x ε, f z ≤ (β:EReal)) :
    LipschitzOnWith ((β-α)/ε).toNNReal (fun x ↦ (f x).toReal) X ∧
      ∀ x ∈ X, ∀ v ∈ subdifferential f x, ‖v‖ ≤ (β-α)/ε := by
  have hnorm (x : E) (hx : x ∈ X) (v : E) (hv : v ∈ subdifferential f x) :
      ‖v‖ ≤ (β-α)/ε := norm_subgradient_le_of_convex_bounds hc hp hε (hlo x hx) (hhi x hx) hv
  have hfinite (x : E) (hx : x ∈ X) : f x = ((f x).toReal : EReal) :=
    (EReal.coe_toReal ((hhi x hx x (mem_closedBall_self hε.le)).trans_lt (EReal.coe_lt_top β)).ne (hp.2 x).ne').symm
  refine ⟨LipschitzOnWith.of_le_add_mul _ (fun x hx y hy ↦ ?_),hnorm⟩
  have hinterior : x ∈ interior (effectiveDomain f) := mem_interior_iff_mem_nhds.mpr
    (mem_of_superset (ball_mem_nhds x hε) fun z hz ↦ (hhi x hx z (ball_subset_closedBall hz)).trans_lt (EReal.coe_lt_top β))
  obtain ⟨v,hv⟩ := subdifferential_nonempty_of_convex_interior hc hp hinterior
  have hsup := (mem_subdifferential_iff_of_convex hc hp (hfinite x hx)).mp hv y
  rw [hfinite y hy,EReal.coe_le_coe_iff] at hsup
  have hinner := real_inner_le_norm (-v) (y-x)
  rw [inner_neg_left,norm_neg] at hinner
  have hbound := mul_le_mul_of_nonneg_right ((hnorm x hx v hv).trans (Real.le_coe_toNNReal _)) (norm_nonneg (y-x))
  rw [dist_eq_norm,norm_sub_rev]
  linarith

end RW
