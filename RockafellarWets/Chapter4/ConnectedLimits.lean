/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Limits of connected sets

This file proves Corollary 4.12.
-/

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.IntermediateValue
import RockafellarWets.Chapter4.SetConvergenceCompactness
import RockafellarWets.Chapter4.UniformApproximation

open Bornology Filter Function Metric Set Topology

namespace RW

section ConnectedLimits

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- No subsequence escapes to the horizon: every subsequence has a nonempty
outer set limit.  By Corollary 4.11 this is equivalent to saying that no
subsequence converges to the empty set. -/
def NoSubsequenceEscapesToHorizon (Cseq : ℕ → Set E) : Prop :=
  ∀ φ : ℕ → ℕ, StrictMono φ →
    (outerSetLimit (Cseq ∘ φ)).Nonempty

/-- **Corollary 4.12 (limits of connected sets).** If the terms are connected,
their outer limit is bounded, and no subsequence escapes to the horizon, then
all sufficiently late terms lie in one bounded set. -/
theorem eventually_bounded_of_connected_of_bounded_outerSetLimit
    {Cseq : ℕ → Set E} (hconn : ∀ n, IsConnected (Cseq n))
    (houterBounded : IsBounded (outerSetLimit Cseq))
    (hnoescape : NoSubsequenceEscapesToHorizon Cseq) :
    ∃ B : Set E, IsBounded B ∧ ∀ᶠ n in atTop, Cseq n ⊆ B := by
  let D : Set E := outerSetLimit Cseq
  let B : Set E := thickening 1 D
  have hBbounded : IsBounded B := houterBounded.thickening
  rcases hBbounded.subset_ball_lt 0 (0 : E) with ⟨ρ, hρ, hBball⟩
  have houterApprox : EventuallyOuterApproximates Cseq D :=
    (outerSetLimit_subset_iff_eventuallyOuterApproximates
      (isClosed_outerSetLimit Cseq)).1 Set.Subset.rfl
  have hlocal : ∀ᶠ n in atTop,
      Cseq n ∩ closedBall (0 : E) ρ ⊆ B := by
    simpa only [D, B] using houterApprox ρ hρ 1 zero_lt_one
  have hhit : ∀ᶠ n in atTop, (Cseq n ∩ B).Nonempty := by
    by_contra hnot
    rw [not_eventually] at hnot
    rcases extraction_of_frequently_atTop hnot with ⟨φ, hφ, hmiss⟩
    rcases hnoescape φ hφ with ⟨x, hxOuterSub⟩
    have hxD : x ∈ D :=
      outerSetLimit_subsequence_subset hφ hxOuterSub
    have hxB : x ∈ B := by
      exact self_subset_thickening zero_lt_one D hxD
    have hfrequentHit :
        ∃ᶠ n in atTop, ((Cseq ∘ φ) n ∩ B).Nonempty :=
      hxOuterSub B (isOpen_thickening.mem_nhds hxB)
    rcases hfrequentHit.exists with ⟨n, hn⟩
    exact hmiss n hn
  refine ⟨closedBall (0 : E) ρ, isBounded_closedBall, ?_⟩
  filter_upwards [hlocal, hhit] with n hnLocal hnHit
  intro y hyC
  by_contra hyBall
  have hyNorm : ρ < ‖y‖ := by
    simpa only [mem_closedBall, dist_zero_right, not_le] using hyBall
  rcases hnHit with ⟨q, hqC, hqB⟩
  have hqNorm : ‖q‖ < ρ := by
    simpa only [mem_ball, dist_zero_right] using hBball hqB
  have hρImage : ρ ∈ (fun z : E ↦ ‖z‖) '' Cseq n := by
    apply (hconn n).isPreconnected.intermediate_value hqC hyC
      continuous_norm.continuousOn
    exact ⟨hqNorm.le, hyNorm.le⟩
  rcases hρImage with ⟨z, hzC, hzNorm⟩
  change ‖z‖ = ρ at hzNorm
  have hzBall : z ∈ closedBall (0 : E) ρ := by
    rw [mem_closedBall, dist_zero_right]
    exact hzNorm.le
  have hzB : z ∈ B := hnLocal ⟨hzC, hzBall⟩
  have hzNormLt : ‖z‖ < ρ := by
    simpa only [mem_ball, dist_zero_right] using hBball hzB
  exact (not_lt_of_ge hzNorm.symm.le) hzNormLt

/-- Closed-ball form of Corollary 4.12. -/
theorem eventually_subset_closedBall_of_connected_of_bounded_outerSetLimit
    {Cseq : ℕ → Set E} (hconn : ∀ n, IsConnected (Cseq n))
    (houterBounded : IsBounded (outerSetLimit Cseq))
    (hnoescape : NoSubsequenceEscapesToHorizon Cseq) :
    ∃ ρ : ℝ, ∀ᶠ n in atTop, Cseq n ⊆ closedBall (0 : E) ρ := by
  rcases eventually_bounded_of_connected_of_bounded_outerSetLimit
      hconn houterBounded hnoescape with ⟨B, hB, hsub⟩
  rcases hB.subset_closedBall (0 : E) with ⟨ρ, hBρ⟩
  exact ⟨ρ, hsub.mono fun n hn ↦ hn.trans hBρ⟩

end ConnectedLimits

end RW
