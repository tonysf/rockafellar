/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Projection characterization of set convergence

This file proves the general, set-valued part of Theorem 4.9.
-/

import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Sequences
import RockafellarWets.Chapter4.DistanceConvergence

open Filter Function Metric Set Topology

namespace RW

section ProjectionConvergence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The (possibly set-valued) metric projection of `x` on `C`. -/
def nearestPoints (C : Set E) (x : E) : Set E :=
  {y | y ∈ C ∧ dist x y = Metric.infDist x C}

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem mem_nearestPoints {C : Set E} {x y : E} :
    y ∈ nearestPoints C x ↔
      y ∈ C ∧ dist x y = Metric.infDist x C :=
  Iff.rfl

/-- A nonempty closed set in a finite-dimensional space has a nearest point. -/
theorem nearestPoints_nonempty {C : Set E} (hC : IsClosed C)
    (hCne : C.Nonempty) (x : E) :
    (nearestPoints C x).Nonempty := by
  rcases hC.exists_infDist_eq_dist hCne x with ⟨y, hyC, hy⟩
  exact ⟨y, hyC, hy.symm⟩

omit [FiniteDimensional ℝ E] in
/-- Convex sets have at most one nearest point in a strictly convex normed
space (in particular, in a real inner-product space). -/
theorem nearestPoints_subsingleton [StrictConvexSpace ℝ E]
    {C : Set E} (hCconv : Convex ℝ C) (x : E) :
    (nearestPoints C x).Subsingleton := by
  intro y hy z hz
  by_contra hyz
  let r : ℝ := Metric.infDist x C
  have hyBall : y ∈ closedBall x r := by
    rw [mem_closedBall, dist_comm, hy.2]
  have hzBall : z ∈ closedBall x r := by
    rw [mem_closedBall, dist_comm, hz.2]
  let m : E := (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • z
  have hmC : m ∈ C :=
    hCconv hy.1 hz.1 one_half_pos.le one_half_pos.le (add_halves 1)
  have hmBall : m ∈ ball x r :=
    combo_mem_ball_of_ne hyBall hzBall hyz one_half_pos one_half_pos
      (add_halves 1)
  have hinf : r ≤ dist x m := Metric.infDist_le_dist_of_mem hmC
  have hlt : dist x m < r := by
    simpa only [mem_ball, dist_comm] using hmBall
  exact (not_le_of_gt hlt) hinf

/-- The metric projection selected from a nonempty closed set.  It is
canonical when the set is convex and the ambient norm is strictly convex. -/
noncomputable def nearestPoint (C : Set E) (hC : IsClosed C)
    (hCne : C.Nonempty) (x : E) : E :=
  (nearestPoints_nonempty hC hCne x).choose

theorem nearestPoint_mem (C : Set E) (hC : IsClosed C)
    (hCne : C.Nonempty) (x : E) :
    nearestPoint C hC hCne x ∈ nearestPoints C x :=
  (nearestPoints_nonempty hC hCne x).choose_spec

theorem nearestPoints_eq_singleton [StrictConvexSpace ℝ E]
    {C : Set E} (hC : IsClosed C) (hCne : C.Nonempty)
    (hCconv : Convex ℝ C) (x : E) :
    nearestPoints C x = {nearestPoint C hC hCne x} := by
  apply Set.Subset.antisymm
  · intro y hy
    rw [mem_singleton_iff]
    exact nearestPoints_subsingleton hCconv x hy
      (nearestPoint_mem C hC hCne x)
  · exact singleton_subset_iff.2 (nearestPoint_mem C hC hCne x)

/-- The boundedness condition `limsup d(x,Cₙ) < +∞`, expressed without an
extended-real coercion.  For real nonnegative distances this is precisely
eventual boundedness from above. -/
def EventuallyBoundedInfDistAt (x : E) (Cseq : ℕ → Set E) : Prop :=
  ∃ R : ℝ, ∀ᶠ n in atTop, Metric.infDist x (Cseq n) ≤ R

/-- **Theorem 4.9 (projection characterization).** For nonempty closed sets,
set convergence is equivalent to bounded distance from one base point and
the outer-limit condition on all metric projection sets. -/
theorem pkConverges_iff_eventuallyBoundedInfDistAt_zero_and_outer_nearestPoints
    {C : Set E} {Cseq : ℕ → Set E}
    (hC : IsClosed C) (hCne : C.Nonempty)
    (hCseqClosed : ∀ n, IsClosed (Cseq n))
    (hCseqNe : ∀ n, (Cseq n).Nonempty) :
    PKConverges Cseq C ↔
      EventuallyBoundedInfDistAt (0 : E) Cseq ∧
        ∀ x : E,
          outerSetLimit (fun n ↦ nearestPoints (Cseq n) x) ⊆
            nearestPoints C x := by
  constructor
  · intro hconv
    have hinner : C ⊆ innerSetLimit Cseq := hconv.inner_eq.symm.subset
    let c : E := hCne.some
    have hcC : c ∈ C := hCne.some_mem
    have hhit :
        ∀ᶠ n in atTop, (Cseq n ∩ ball c 1).Nonempty :=
      (mem_innerSetLimit_iff_eventually_ball.1 (hinner hcC)) 1 zero_lt_one
    refine ⟨⟨‖c‖ + 1, hhit.mono fun n hn ↦ ?_⟩, ?_⟩
    · rcases hn with ⟨z, hzCn, hzBall⟩
      calc
        Metric.infDist 0 (Cseq n) ≤ dist 0 z :=
          Metric.infDist_le_dist_of_mem hzCn
        _ = ‖z‖ := dist_zero_left z
        _ ≤ ‖z - c‖ + ‖c‖ := norm_le_norm_sub_add z c
        _ ≤ 1 + ‖c‖ := by
          have : ‖z - c‖ < 1 := by
            simpa only [mem_ball, dist_eq_norm] using hzBall
          linarith
        _ = ‖c‖ + 1 := add_comm _ _
    · intro x y hyOuter
      rcases mem_outerSetLimit_iff_exists_subsequence.1 hyOuter with
        ⟨φ, z, hφ, hzProj, hzy⟩
      have hyC : y ∈ C := by
        apply hconv.outer_eq.subset
        exact mem_outerSetLimit_iff_exists_subsequence.2
          ⟨φ, z, hφ, fun n ↦ (hzProj n).1, hzy⟩
      have hdE :=
        (pkConverges_iff_tendsto_infEDist hC).1 hconv x
      have hdR :
          Tendsto (fun n ↦ Metric.infDist x (Cseq n)) atTop
            (nhds (Metric.infDist x C)) := by
        exact (ENNReal.tendsto_toReal
          (Metric.infEDist_ne_top hCne)).comp hdE
      have hdRsub :
          Tendsto (fun n ↦ Metric.infDist x (Cseq (φ n))) atTop
            (nhds (Metric.infDist x C)) :=
        hdR.comp hφ.tendsto_atTop
      have hdist :
          Tendsto (fun n ↦ dist x (z n)) atTop (nhds (dist x y)) :=
        tendsto_const_nhds.dist hzy
      have hdist' :
          Tendsto (fun n ↦ Metric.infDist x (Cseq (φ n))) atTop
            (nhds (dist x y)) := by
        simpa only [funext_iff, (hzProj _).2] using hdist
      exact ⟨hyC, tendsto_nhds_unique hdist' hdRsub⟩
  · rintro ⟨hbound, hproj⟩
    have houter : outerSetLimit Cseq ⊆ C := by
      intro y hyOuter
      rcases mem_outerSetLimit_iff_exists_subsequence.1 hyOuter with
        ⟨φ, z, hφ, hzC, hzy⟩
      choose p hpProj using fun n ↦
        nearestPoints_nonempty (hCseqClosed (φ n)) (hCseqNe (φ n)) y
      have hpDist : Tendsto (fun n ↦ dist y (p n)) atTop (nhds 0) := by
        exact squeeze_zero (fun n ↦ dist_nonneg)
          (fun n ↦ (hpProj n).2.le.trans
            (Metric.infDist_le_dist_of_mem (hzC n))) <| by
          simpa only [dist_comm] using
            (tendsto_iff_dist_tendsto_zero.1 hzy)
      have hpy : Tendsto p atTop (nhds y) :=
        tendsto_iff_dist_tendsto_zero.2 <| by
          simpa only [dist_comm] using hpDist
      have hyProj : y ∈ nearestPoints C y := hproj y <|
        mem_outerSetLimit_iff_exists_subsequence.2
          ⟨φ, p, hφ, hpProj, hpy⟩
      exact hyProj.1
    have hinner : C ⊆ innerSetLimit Cseq := by
      intro x hxC
      apply mem_innerSetLimit_iff_eventually_ball.2
      intro ε hε
      by_contra hnot
      rw [not_eventually] at hnot
      rcases hbound with ⟨R, hR⟩
      have hfrequentBound :
          ∃ᶠ n in atTop,
            ¬(Cseq n ∩ ball x ε).Nonempty ∧
              Metric.infDist 0 (Cseq n) ≤ R :=
        hnot.and_eventually hR
      rcases extraction_of_frequently_atTop hfrequentBound with
        ⟨φ, hφ, hbad⟩
      have hmiss : ∀ n, ¬(Cseq (φ n) ∩ ball x ε).Nonempty :=
        fun n ↦ (hbad n).1
      have hRsub : ∀ n, Metric.infDist 0 (Cseq (φ n)) ≤ R :=
        fun n ↦ (hbad n).2
      choose p hpProj using fun n ↦
        nearestPoints_nonempty (hCseqClosed (φ n)) (hCseqNe (φ n)) x
      have hpBall : ∀ n, p n ∈ closedBall (0 : E) (R + 2 * ‖x‖) := by
        intro n
        rw [mem_closedBall, dist_zero_right]
        calc
          ‖p n‖ ≤ ‖p n - x‖ + ‖x‖ := norm_le_norm_sub_add _ _
          _ = dist x (p n) + ‖x‖ := by rw [dist_eq_norm, norm_sub_rev]
          _ = Metric.infDist x (Cseq (φ n)) + ‖x‖ := by rw [(hpProj n).2]
          _ ≤ Metric.infDist 0 (Cseq (φ n)) + dist x 0 + ‖x‖ := by
            gcongr
            exact Metric.infDist_le_infDist_add_dist
          _ ≤ R + 2 * ‖x‖ := by
            rw [dist_zero_right]
            linarith [hRsub n]
      rcases (isCompact_closedBall (0 : E) (R + 2 * ‖x‖)).tendsto_subseq hpBall with
        ⟨pbar, _hpbarBall, ψ, hψ, hppbar⟩
      have hpbarProj : pbar ∈ nearestPoints C x := hproj x <|
        mem_outerSetLimit_iff_exists_subsequence.2
          ⟨φ ∘ ψ, p ∘ ψ, hφ.comp hψ,
            fun n ↦ hpProj (ψ n), hppbar⟩
      have hxInf : Metric.infDist x C = 0 := Metric.infDist_zero_of_mem hxC
      have hpbarEq : pbar = x := by
        apply dist_eq_zero.1
        rw [dist_comm, hpbarProj.2, hxInf]
      have hpNear : ∀ᶠ n in atTop, p (ψ n) ∈ ball x ε := by
        rw [hpbarEq] at hppbar
        exact hppbar.eventually (ball_mem_nhds x hε)
      rcases hpNear.exists with ⟨n, hn⟩
      exact hmiss (ψ n) ⟨p (ψ n), (hpProj (ψ n)).1, hn⟩
    exact ⟨Set.Subset.antisymm
      ((innerSetLimit_subset_outerSetLimit Cseq).trans houter) hinner,
      Set.Subset.antisymm houter
        (hinner.trans (innerSetLimit_subset_outerSetLimit Cseq))⟩

/-- **Theorem 4.9 (convex clause).** For nonempty closed convex sets in a
strictly convex finite-dimensional space, set convergence is equivalent to
pointwise convergence of the single-valued metric projections. -/
theorem pkConverges_iff_tendsto_nearestPoint [StrictConvexSpace ℝ E]
    {C : Set E} {Cseq : ℕ → Set E}
    (hC : IsClosed C) (hCne : C.Nonempty) (hCconv : Convex ℝ C)
    (hCseqClosed : ∀ n, IsClosed (Cseq n))
    (hCseqNe : ∀ n, (Cseq n).Nonempty)
    (hCseqConv : ∀ n, Convex ℝ (Cseq n)) :
    PKConverges Cseq C ↔
      ∀ x : E,
        Tendsto
          (fun n ↦ nearestPoint (Cseq n) (hCseqClosed n) (hCseqNe n) x)
          atTop (nhds (nearestPoint C hC hCne x)) := by
  let p : E → ℕ → E := fun x n ↦
    nearestPoint (Cseq n) (hCseqClosed n) (hCseqNe n) x
  let pC : E → E := fun x ↦ nearestPoint C hC hCne x
  have hpMem : ∀ x n, p x n ∈ nearestPoints (Cseq n) x :=
    fun x n ↦ nearestPoint_mem (Cseq n) (hCseqClosed n) (hCseqNe n) x
  have hpCMem : ∀ x, pC x ∈ nearestPoints C x :=
    fun x ↦ nearestPoint_mem C hC hCne x
  constructor
  · intro hconv
    rcases
        (pkConverges_iff_eventuallyBoundedInfDistAt_zero_and_outer_nearestPoints
          hC hCne hCseqClosed hCseqNe).1 hconv with
      ⟨hbound, hproj⟩
    intro x
    rw [Metric.tendsto_atTop]
    intro ε hε
    by_contra hnot
    push_neg at hnot
    have hfar : ∃ᶠ n in atTop, ε ≤ dist (p x n) (pC x) := by
      rw [frequently_atTop]
      exact fun N ↦ hnot N
    rcases hbound with ⟨R, hR⟩
    have hboth : ∃ᶠ n in atTop,
        ε ≤ dist (p x n) (pC x) ∧
          Metric.infDist 0 (Cseq n) ≤ R :=
      hfar.and_eventually hR
    rcases extraction_of_frequently_atTop hboth with ⟨φ, hφ, hbad⟩
    have hpBall : ∀ n,
        p x (φ n) ∈ closedBall (0 : E) (R + 2 * ‖x‖) := by
      intro n
      rw [mem_closedBall, dist_zero_right]
      calc
        ‖p x (φ n)‖ ≤ ‖p x (φ n) - x‖ + ‖x‖ :=
          norm_le_norm_sub_add _ _
        _ = dist x (p x (φ n)) + ‖x‖ := by
          rw [dist_eq_norm, norm_sub_rev]
        _ = Metric.infDist x (Cseq (φ n)) + ‖x‖ := by
          rw [(hpMem x (φ n)).2]
        _ ≤ Metric.infDist 0 (Cseq (φ n)) + dist x 0 + ‖x‖ := by
          gcongr
          exact Metric.infDist_le_infDist_add_dist
        _ ≤ R + 2 * ‖x‖ := by
          rw [dist_zero_right]
          linarith [(hbad n).2]
    rcases
        (isCompact_closedBall (0 : E) (R + 2 * ‖x‖)).tendsto_subseq hpBall with
      ⟨q, _hqBall, ψ, hψ, hpq⟩
    have hqProj : q ∈ nearestPoints C x := hproj x <|
      mem_outerSetLimit_iff_exists_subsequence.2
        ⟨φ ∘ ψ, (p x ∘ φ) ∘ ψ, hφ.comp hψ,
          fun n ↦ hpMem x (φ (ψ n)), hpq⟩
    have hqeq : q = pC x :=
      nearestPoints_subsingleton hCconv x hqProj (hpCMem x)
    have hpNear : ∀ᶠ n in atTop,
        p x (φ (ψ n)) ∈ ball (pC x) ε := by
      rw [hqeq] at hpq
      exact hpq.eventually (ball_mem_nhds (pC x) hε)
    rcases hpNear.exists with ⟨n, hn⟩
    exact (not_lt_of_ge (hbad (ψ n)).1) (by
      simpa only [mem_ball] using hn)
  · intro hpTendsto
    apply
      (pkConverges_iff_eventuallyBoundedInfDistAt_zero_and_outer_nearestPoints
        hC hCne hCseqClosed hCseqNe).2
    constructor
    · refine ⟨‖pC 0‖ + 1, ?_⟩
      have hpNear : ∀ᶠ n in atTop, p 0 n ∈ ball (pC 0) 1 :=
        (hpTendsto 0).eventually (ball_mem_nhds (pC 0) zero_lt_one)
      exact hpNear.mono fun n hn ↦ by
        rw [← (hpMem 0 n).2]
        calc
          dist 0 (p 0 n) = ‖p 0 n‖ := dist_zero_left _
          _ ≤ ‖p 0 n - pC 0‖ + ‖pC 0‖ := norm_le_norm_sub_add _ _
          _ ≤ 1 + ‖pC 0‖ := by
            have : ‖p 0 n - pC 0‖ < 1 := by
              simpa only [mem_ball, dist_eq_norm] using hn
            linarith
          _ = ‖pC 0‖ + 1 := add_comm _ _
    · intro x y hyOuter
      rcases mem_outerSetLimit_iff_exists_subsequence.1 hyOuter with
        ⟨φ, z, hφ, hzProj, hzy⟩
      have hzEq : ∀ n, z n = p x (φ n) := fun n ↦
        nearestPoints_subsingleton (hCseqConv (φ n)) x (hzProj n)
          (hpMem x (φ n))
      have hpSub : Tendsto (fun n ↦ p x (φ n)) atTop (nhds (pC x)) :=
        (hpTendsto x).comp hφ.tendsto_atTop
      have hyeq : y = pC x := by
        apply tendsto_nhds_unique hzy
        rw [show z = fun n ↦ p x (φ n) from funext hzEq]
        exact hpSub
      rw [hyeq]
      exact hpCMem x

end ProjectionConvergence

end RW
