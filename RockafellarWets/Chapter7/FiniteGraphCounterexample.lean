/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The neighborhood qualification in Theorem 7.11

A finite function can be continuous at the tested point while having a
nonclosed graph on every neighborhood of that point. The local graphical
criterion in `FiniteGraphConvergence` therefore tests the graph at the point.
-/

import RockafellarWets.Chapter7.FiniteGraphConvergence
import Mathlib.NumberTheory.Real.Irrational

open Filter Metric Set Topology

namespace RW

/-- **Obstruction to the neighborhood version of 7.11.** The constant
sequence of a function which is zero on the rationals and equals the
identity on the irrationals converges continuously at zero. Its finite-height
graphs fail to converge graphically on every neighborhood of zero. -/
theorem continuousAt_zero_without_neighborhood_graphical_convergence :
    ∃ u : ℝ → ℝ, ConvergesContinuouslyWithinAt (fun _ x ↦ (u x : EReal))
        (fun x ↦ (u x : EReal)) univ 0 ∧
      ∀ V ∈ 𝓝 (0 : ℝ), ¬ GraphicalConvergesOn
        (fun _ ↦ finiteGraphFiber (fun x ↦ (u x : EReal)))
        (finiteGraphFiber (fun x ↦ (u x : EReal))) V := by
  classical
  let u (x : ℝ) := if Irrational x then x else 0
  have hzero : u 0 = 0 := by simp [u]
  refine ⟨u, ?_, ?_⟩
  · intro z _ hz
    change Tendsto (fun n ↦ (u (z n) : EReal)) atTop (𝓝 (u 0 : EReal))
    rw [hzero]
    apply continuous_coe_real_ereal.continuousAt.tendsto.comp
    apply tendsto_iff_dist_tendsto_zero.mpr
    refine squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ ?_) (tendsto_iff_dist_tendsto_zero.mp hz)
    dsimp [u]
    split <;> simp
  · intro V hV hg
    obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp hV
    obtain ⟨x, hxi, hx, hxδ⟩ := exists_irrational_btwn hδ
    have hxV := hsub (show x ∈ ball 0 δ by simpa [Real.dist_eq, abs_of_pos hx] using hxδ)
    have hh (n : ℕ) : x < min δ (x + 1 / ((n : ℝ) + 1)) :=
      lt_min hxδ (lt_add_of_pos_right _ (by positivity))
    choose q hq using fun n ↦ exists_rat_btwn (hh n)
    have hqV (n : ℕ) : (q n : ℝ) ∈ V := by
      apply hsub
      change dist (q n : ℝ) 0 < δ
      rw [Real.dist_eq, sub_zero, abs_of_pos (hx.trans (hq n).1)]
      exact
        (hq n).2.trans_le (min_le_left _ _)
    have hqx : Tendsto (fun n ↦ (q n : ℝ)) atTop (𝓝 x) := by
      apply tendsto_iff_dist_tendsto_zero.mpr
      refine squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ ?_) tendsto_one_div_add_atTop_nhds_zero_nat
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr (hq n).1)]
      linarith [(hq n).2.trans_le (min_le_right _ _)]
    have hmem : (0 : ℝ) ∈ graphicalOuterLimitWithin
        (fun _ ↦ finiteGraphFiber (fun x ↦ (u x : EReal))) V x := by
      apply mem_graphicalOuterLimitWithin_iff.mpr
      refine ⟨fun n ↦ (q n : ℝ), ⟨hqV, hqx⟩, ?_⟩
      intro W hW
      exact (Eventually.of_forall fun n ↦ ⟨0, by simp [finiteGraphFiber, u, (q n).not_irrational],
        mem_of_mem_nhds hW⟩).frequently
    have heq : ((0 : ℝ) : EReal) = (u x : EReal) := (hg x hxV).1 hmem
    have hz : (0 : ℝ) = x := EReal.coe_injective (by simpa [u, hxi] using heq)
    exact hx.ne' hz.symm

end RW
