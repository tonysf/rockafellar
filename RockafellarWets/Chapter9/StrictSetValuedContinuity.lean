/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: Neighborhood descriptions of strict set-valued continuity
-/

import RockafellarWets.Chapter9.SetValuedModuli

open Filter Metric Set Topology
open scoped NNReal ENNReal

namespace RW

variable {E F : Type*} [MetricSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {S : E → Set F} {X : Set E} {x : E}

/-- The truncated geometric inclusion with a fixed input set and output radius. -/
def RhoTransport (k ρ : ℝ≥0) (S : E → Set F) (X : Set E) : Prop :=
  ∀ a ∈ X, ∀ b ∈ X, ∀ v ∈ S a ∩ closedBall (0:F) (ρ:ℝ), ∃ z ∈ S b, dist v z ≤ k*dist a b

omit [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
theorem RhoTransport.mono {k ρ : ℝ≥0} {Y : Set E} (h : RhoTransport k ρ S X) (hYX : Y ⊆ X) :
    RhoTransport k ρ S Y := fun a ha b hb ↦ h a (hYX ha) b (hYX hb)

theorem rhoTransport_iff_rhoHatDistance (hS : NonemptyClosedValuedOn S X) {k ρ : ℝ≥0} :
    RhoTransport k ρ S X ↔ ∀ a ∈ X, ∀ b ∈ X, rhoHatDistance ρ (S a) (S b) ≤ k*dist a b := by
  constructor
  · intro h a ha b hb
    apply (rhoHatDistance_le_iff ρ (hS a ha).1 (hS b hb).1 (mul_nonneg k.2 dist_nonneg)).2
    constructor
    · exact fun v hv ↦ (exists_mem_dist_le_iff_infEDist_le (hS b hb).1 (hS b hb).2 v (mul_nonneg k.2 dist_nonneg)).1 (h a ha b hb v hv)
    · rw [dist_comm a b]
      exact fun v hv ↦ (exists_mem_dist_le_iff_infEDist_le (hS a ha).1 (hS a ha).2 v (mul_nonneg k.2 dist_nonneg)).1 (h b hb a ha v hv)
  · intro h a ha b hb v hv
    apply (exists_mem_dist_le_iff_infEDist_le (hS b hb).1 (hS b hb).2 _ (by positivity)).2
    exact ((rhoHatDistance_le_iff ρ (hS a ha).1 (hS b hb).1 (by positivity)).1 (h a ha b hb)).1 hv

/-- **Proposition 9.29(a).** Finite local moduli are equivalent to profile
Lipschitz estimates on relative neighborhoods, which can depend on the radius. -/
theorem svStrictlyContinuousWithinAt_iff_local_profile (hx : x ∈ X) (hS : NonemptyClosedValuedOn S X) :
    SvStrictlyContinuousWithinAt S X x ↔
      ∀ ρ : ℝ≥0, ∃ k : ℝ≥0, ∃ U ∈ 𝓝[X] x, SvRhoLipschitzOnWith k ρ S U := by
  refine ⟨fun h r ↦ (strictlyContinuousWithinAt_iff.1 ⟨hx,h.2.2 r⟩).2,fun h ↦ ⟨hx,?_,fun r ↦ ?_⟩⟩
  · filter_upwards [self_mem_nhdsWithin] with y hy using hS y hy
  · exact (strictlyContinuousWithinAt_iff.2 ⟨hx,h r⟩).2

/-- **Proposition 9.29(c).** The point-to-fiber distances have one Lipschitz
constant on a common input neighborhood for all centers in the output ball. -/
theorem svStrictlyContinuousWithinAt_iff_local_distance_functions (hx : x ∈ X) (hS : NonemptyClosedValuedOn S X) :
    SvStrictlyContinuousWithinAt S X x ↔ ∀ ρ : ℝ≥0, ∃ k : ℝ≥0, ∃ U ∈ 𝓝[X] x,
      ∀ v ∈ closedBall (0:F) (ρ:ℝ), LipschitzOnWith k (fun a ↦ infDist v (S a)) U := by
  simp only [svStrictlyContinuousWithinAt_iff_local_profile hx hS,svRhoLipschitzOnWith_iff_distance_functions]

/-- **Proposition 9.29(b).** Near the base point a bounded member of the base
fiber gives a uniform bound on the distances of the nearby fibers from zero.
Chapter 4's comparison can then be applied at a larger radius. -/
theorem svStrictlyContinuousWithinAt_iff_local_transport (hx : x ∈ X) (hS : NonemptyClosedValuedOn S X) :
    SvStrictlyContinuousWithinAt S X x ↔
      ∀ ρ : ℝ≥0, ∃ k : ℝ≥0, ∃ U ∈ 𝓝[X] x, RhoTransport k ρ S U := by
  rw [svStrictlyContinuousWithinAt_iff_local_profile hx hS]
  constructor
  · intro h r
    obtain ⟨k,U,hU,hk⟩ := h r
    refine ⟨k,U ∩ X,inter_mem hU self_mem_nhdsWithin,fun a ha b hb v hv ↦ ?_⟩
    exact SvRhoLipschitzOnWith.transport (X := U ∩ X) (k := k) (ρ := r) (hk.mono inter_subset_left)
      (fun z hz ↦ hS z hz.2) ha hb hv
  · intro h r
    obtain ⟨u,hu⟩ := (hS x hx).1
    let R : ℝ≥0 := 2*r + ‖u‖₊ + 1
    have hR : (R:ℝ) = 2*(r:ℝ)+‖u‖+1 := by simp [R]
    obtain ⟨k,U,hU,hraw⟩ := h R
    let δ : ℝ := ((k:ℝ)+1)⁻¹
    have hd : 0 < δ := by dsimp [δ]; positivity
    let V := U ∩ X ∩ ball x δ
    have hV : V ∈ 𝓝[X] x := inter_mem (inter_mem hU self_mem_nhdsWithin)
      (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ hd))
    have hXV : V ⊆ X := fun _ hv ↦ hv.1.2
    have hVU : V ⊆ U := fun _ hv ↦ hv.1.1
    have hxU := mem_of_mem_nhdsWithin hx hU
    have h0 (a : E) (ha : a ∈ V) : infDist 0 (S a) ≤ ‖u‖+1 := by
      obtain ⟨z,hz,hzdist⟩ := hraw x hxU a (hVU ha) u ⟨hu, mem_closedBall_zero_iff.2 (by rw [hR]; linarith [show (0:ℝ) ≤ (r:ℝ) by positivity])⟩
      have hsmall : dist x a < δ := by simpa only [dist_comm x a] using ha.2
      have hkd : (k:ℝ)*dist x a ≤ 1 := by
        calc
          _ ≤ ((k:ℝ)+1)*dist x a := by nlinarith [dist_nonneg (x := x) (y := a)]
          _ ≤ ((k:ℝ)+1)*δ := mul_le_mul_of_nonneg_left hsmall.le (by positivity)
          _ = 1 := mul_inv_cancel₀ (by positivity)
      calc
        infDist 0 (S a) ≤ dist 0 z := infDist_le_dist_of_mem hz
        _ ≤ dist 0 u + dist u z := dist_triangle _ _ _
        _ ≤ ‖u‖+1 := by rw [dist_zero_left]; linarith
    refine ⟨k,V,hV,svRhoLipschitzOnWith_iff_rhoDistance.2 (fun a ha b hb ↦ ?_)⟩
    have hr := rhoDistance_le_rhoHatDistance_of_two_mul (r := r) (s := R) (hS a (hXV ha)).2
      (hS b (hXV hb)).2 (hS a (hXV ha)).1 (hS b (hXV hb)).1 (by
        rw [hR]; linarith [max_le (h0 a ha) (h0 b hb)])
    exact hr.trans ((rhoTransport_iff_rhoHatDistance (fun z hz ↦ hS z (hXV hz))).1 (hraw.mono hVU) a ha b hb)

/-- The truncated-inclusion distance form of 9.29(b). -/
theorem svStrictlyContinuousWithinAt_iff_local_rhoHatDistance (hx : x ∈ X) (hS : NonemptyClosedValuedOn S X) :
    SvStrictlyContinuousWithinAt S X x ↔ ∀ ρ : ℝ≥0, ∃ k : ℝ≥0, ∃ U ∈ 𝓝[X] x,
      ∀ a ∈ U, ∀ b ∈ U, rhoHatDistance ρ (S a) (S b) ≤ k*dist a b := by
  rw [svStrictlyContinuousWithinAt_iff_local_transport hx hS]
  constructor
  · intro h r
    obtain ⟨k,U,hU,hk⟩ := h r
    exact ⟨k,U ∩ X,inter_mem hU self_mem_nhdsWithin,
      (rhoTransport_iff_rhoHatDistance (fun z hz ↦ hS z hz.2)).1 (hk.mono inter_subset_left)⟩
  · intro h r
    obtain ⟨k,U,hU,hk⟩ := h r
    exact ⟨k,U ∩ X,inter_mem hU self_mem_nhdsWithin,
      (rhoTransport_iff_rhoHatDistance (fun z hz ↦ hS z hz.2)).2 fun a ha b hb ↦ hk a ha.1 b hb.1⟩

end RW
