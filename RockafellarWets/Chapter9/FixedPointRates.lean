/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: Nonexpansiveness and rates of fixed-point iteration
-/

import RockafellarWets.Chapter9.LipschitzModulus
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Function Metric Set Topology
open scoped ENNReal NNReal

namespace RW

variable {E F : Type*} [MetricSpace E] [MetricSpace F]

/-- **Example 9.4.** Nonexpansiveness is precisely the Lipschitz inequality
with constant one. -/
theorem nonexpansiveOn_iff (f : E → F) (X : Set E) :
    LipschitzOnWith 1 f X ↔ ∀ x ∈ X, ∀ y ∈ X, dist (f x) (f y) ≤ dist x y := by
  simp only [lipschitzOnWith_iff_dist_le_mul, NNReal.coe_one, one_mul]

theorem contractiveOn_of_lipschitzOnWith_lt_one {f : E → F} {X : Set E} {k : ℝ≥0}
    (h : LipschitzOnWith k f X) (hk : k < 1) {x y : E} (hx : x ∈ X) (hy : y ∈ X) (hne : x ≠ y) :
    dist (f x) (f y) < dist x y :=
  (h.dist_le_mul _ hx _ hy).trans_lt (mul_lt_of_lt_one_left (dist_pos.mpr hne) hk)

/-- Along every orbit converging to a fixed point, the upper limit of the
successive error ratios is bounded by the exact local modulus. -/
theorem limsup_fixedPoint_error_ratio_le {f : E → E} {x y : E} (hx : f x = x)
    (hy : Tendsto (fun n ↦ f^[n] y) atTop (𝓝 x)) :
    limsup (fun n ↦ edist (f^[n+1] y) x / edist (f^[n] y) x) atTop ≤ lipschitzModulus f x := by
  rw [limsup_le_iff]
  intro a ha
  obtain ⟨k, hk, hka⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp ha
  obtain ⟨U, hU, h⟩ := exists_lipschitzOnWith_of_modulus_lt hk
  filter_upwards [hy.eventually hU] with n hn
  have he := h hn (mem_of_mem_nhds hU)
  rw [hx] at he
  rw [Function.iterate_succ_apply']
  exact (ENNReal.div_le_of_le_mul he).trans_lt hka

/-- **Exercise 9.5.** Every sufficiently small closed ball around a fixed
point of modulus below one is invariant and contractive. Every orbit in
the ball converges, with the printed upper bound on its error ratios. -/
theorem exists_contractive_closedBalls_of_modulus_lt_one {f : E → E} {x : E} (hx : f x = x)
    (hmod : lipschitzModulus f x < 1) :
    ∃ k : ℝ≥0, k < 1 ∧ ∃ r > 0, ∀ δ ∈ Ioc 0 r,
      LipschitzOnWith k f (closedBall x δ) ∧ MapsTo f (closedBall x δ) (closedBall x δ) ∧
        ∀ y ∈ closedBall x δ, Tendsto (fun n ↦ f^[n] y) atTop (𝓝 x) ∧
          limsup (fun n ↦ edist (f^[n+1] y) x / edist (f^[n] y) x) atTop ≤ lipschitzModulus f x := by
  obtain ⟨k, hk, hk1⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hmod
  have hk' : k < 1 := ENNReal.coe_lt_coe.mp hk1
  obtain ⟨U, hU, hl⟩ := exists_lipschitzOnWith_of_modulus_lt hk
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hU
  refine ⟨k, hk', r, hr, ?_⟩
  intro δ hδ
  have h := hl.mono ((closedBall_subset_closedBall hδ.2).trans hsub)
  have hstep (z : E) (hz : z ∈ closedBall x δ) : dist (f z) x ≤ k * dist z x := by
    simpa only [hx] using h.dist_le_mul _ hz _ (mem_closedBall_self hδ.1.le)
  have hm : MapsTo f (closedBall x δ) (closedBall x δ) := fun z hz ↦
    (hstep z hz).trans ((mul_le_of_le_one_left dist_nonneg hk'.le).trans hz)
  refine ⟨h, hm, ?_⟩
  intro y hy
  have hbound (n : ℕ) : dist (f^[n] y) x ≤ (k : ℝ)^n * dist y x := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [iterate_succ_apply', pow_succ', mul_assoc]
      exact (hstep _ (hm.iterate n hy)).trans (mul_le_mul_of_nonneg_left ih k.coe_nonneg)
  have hz : Tendsto (fun n ↦ f^[n] y) atTop (𝓝 x) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one k.coe_nonneg (show (k : ℝ) < 1 from hk')).mul_const (dist y x)
    exact squeeze_zero (fun _ ↦ dist_nonneg) hbound (by simpa only [zero_mul] using ht)
  exact ⟨hz, limsup_fixedPoint_error_ratio_le hx hz⟩

end RW
