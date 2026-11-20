/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: Recovering strict continuity from directional bounds
-/

import RockafellarWets.Chapter9.StrictContinuityEReal
import RockafellarWets.Chapter8.SubgradientLimits

open Filter Function Metric Set Topology
open scoped ENNReal NNReal

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → EReal} {x : E} {c : ℝ}

/-- A uniform upper bound on difference quotients for directions near zero
gives a straight-line increment estimate for every sufficiently small displacement. -/
private theorem eventually_increment_bound_of_upperDirectionalSlope {f : E → EReal} {x : E} {c : ℝ}
    (hx : f x = c) (h : upperDirectionalSlope f x 0 < ⊤) :
    ∃ k : ℝ≥0, ∃ d > 0, ∀ᶠ y in attentiveNhds f x, f y = ((f y).toReal : EReal) ∧
      ∀ z, dist z y < d → f z ≤ (((f y).toReal + k * dist z y : ℝ) : EReal) := by
  obtain ⟨a, hlt, -⟩ := EReal.exists_between_coe_real h
  obtain ⟨P, hP, W, hW, hPW⟩ := mem_prod_iff.mp (eventually_lt_of_limsup_lt hlt)
  obtain ⟨Y, hY, T, hT, hYT⟩ := mem_prod_iff.mp hP
  obtain ⟨s, hs, hsW⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hW
  obtain ⟨δ, hδ, hδT⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hT
  let k : ℝ≥0 := ⟨max a 0 / s, div_nonneg (le_max_right ..) hs.le⟩
  refine ⟨k, δ*s, mul_pos hδ hs, ?_⟩
  filter_upwards [hY, eventually_finite_attentiveNhds hx] with y hy hfy
  refine ⟨hfy, ?_⟩
  intro z hz
  rcases eq_or_ne z y with rfl | hne
  · simpa only [dist_self, mul_zero, add_zero] using hfy.le
  let t := dist z y / s
  have ht : 0 < t := div_pos (dist_pos.mpr hne) hs
  have htδ : t < δ := (div_lt_iff₀ hs).mpr hz
  let w := t⁻¹ • (z-y)
  have hw : ‖w‖ = s := by
    rw [show ‖w‖ = |t⁻¹| * ‖z-y‖ from norm_smul .., abs_of_pos (inv_pos.mpr ht), ← dist_eq_norm]
    dsimp [t]
    field_simp [dist_ne_zero.mpr hne]
  have hz' : y + t • w = z := by simp [w, smul_smul, ht.ne']
  have hq := hPW (a := ((y,t),w)) ⟨hYT ⟨hy, hδT ⟨ht, htδ⟩⟩, hsW (mem_closedBall_zero_iff.mpr hw.le)⟩
  have hdq := (differenceQuotient_le_coe_iff hfy ht).mp hq.le
  rw [hz'] at hdq
  apply hdq.trans (EReal.coe_le_coe_iff.mpr (add_le_add_right ?_ _))
  calc
    t*a ≤ t * max a 0 := mul_le_mul_of_nonneg_left (le_max_left ..) ht.le
    _ = k * dist z y := by dsimp [k, t]; ring

/-- A finite upper slope at the zero direction yields actual Lipschitz
continuity on a neighborhood. Local lower semicontinuity first turns
attentive neighborhoods into ordinary neighborhoods at the base point. -/
theorem eRealStrictlyContinuousAt_of_upperDirectionalSlope_zero (hx : f x = c)
    (hl : LowerSemicontinuousAt f x) (h : upperDirectionalSlope f x 0 < ⊤) :
    ERealStrictlyContinuousAt f x := by
  obtain ⟨k, d, hd, hinc⟩ := eventually_increment_bound_of_upperDirectionalSlope hx h
  have hbase := (pure_le_attentiveNhds f x hinc : ∀ᶠ y in pure x, _)
  have hb : ∀ z, dist z x < d → f z ≤ (((f x).toReal + k * dist z x : ℝ) : EReal) := hbase.2
  have hcont : ContinuousAt f x := by
    apply tendsto_order.mpr
    refine ⟨fun a ha ↦ hl a ha, ?_⟩
    intro b hfb
    have hh : Tendsto (fun z ↦ (((f x).toReal + k * dist z x : ℝ) : EReal)) (𝓝 x) (𝓝 (f x)) := by
      have hc : Continuous (fun z ↦ (f x).toReal + k * dist z x) := by fun_prop
      simpa only [Function.comp_apply, dist_self, mul_zero, add_zero, hx, EReal.toReal_coe] using
        (continuous_coe_real_ereal.comp hc).tendsto x
    filter_upwards [ball_mem_nhds x hd, hh.eventually_lt_const hfb] with z hz hzb
    exact (hb z hz).trans_lt hzb
  have he : attentiveNhds f x = 𝓝 x := inf_eq_left.mpr hcont.le_comap
  rw [he] at hinc
  refine ⟨hinc.mono fun _ h ↦ h.1, strictlyContinuousAt_iff.mpr ?_⟩
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hinc
  let δ := min r (d/2)
  have hδ : 0 < δ := lt_min hr (half_pos hd)
  have hyz {y z : E} (hy : y ∈ ball x δ) (hz : z ∈ ball x δ) : dist z y < d := by
    have hy' := (mem_ball.mp hy).trans_le (min_le_right r (d/2))
    have hz' := (mem_ball.mp hz).trans_le (min_le_right r (d/2))
    linarith [dist_triangle z x y, dist_comm x y]
  have hnear {y : E} (hy : y ∈ ball x δ) := hrsub ((mem_ball.mp hy).trans_le (min_le_left r (d/2)))
  refine ⟨k, ball x δ, ball_mem_nhds x hδ, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro y hy z hz
  have hy' := hnear hy
  have hz' := hnear hz
  have h1 := (hy'.2 z (hyz hy hz))
  have h2 := (hz'.2 y (hyz hz hy))
  rw [hz'.1, EReal.coe_le_coe_iff, dist_comm z y] at h1
  rw [hy'.1, EReal.coe_le_coe_iff] at h2
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith

section Euclidean

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {g : F → EReal} {y : F} {b : ℝ}

/-- **Theorem 9.13(e) implies (a)**, in the stronger interior-domain form. -/
theorem eRealStrictlyContinuousAt_of_interior_regularSubderivative (hy : g y = b) (hl : IsLocallyLscAt g y)
    (h : 0 ∈ interior (effectiveDomain (regularSubderivative g y))) : ERealStrictlyContinuousAt g y := by
  apply eRealStrictlyContinuousAt_of_upperDirectionalSlope_zero hy hl.lowerSemicontinuousAt
  rw [interior_effectiveDomain_regularSubderivative hy hl] at h
  exact h

end Euclidean

end RW
