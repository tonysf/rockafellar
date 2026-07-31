/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Limits of Star-Shaped Sets

This file proves Theorem 4.17 of Rockafellar--Wets: a bounded convergent
sequence of star-shaped sets has a star-shaped limit.
-/

import Mathlib.Analysis.Convex.Star
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Sequences
import RockafellarWets.Chapter4.SetLimitCharacterizations

open Bornology Filter Function Metric Set Topology

namespace RW

section Definitions

variable {E : Type*} [AddCommMonoid E] [SMul ℝ E]

/-- The book's nonvacuous notion of a star-shaped set: there is a center in
the set from which every segment to another set point stays in the set. -/
def IsStarShaped (C : Set E) : Prop :=
  ∃ q ∈ C, StarConvex ℝ q C

theorem IsStarShaped.nonempty {C : Set E} (hC : IsStarShaped C) : C.Nonempty := by
  rcases hC with ⟨q, hq, _⟩
  exact ⟨q, hq⟩

theorem Convex.isStarShaped {C : Set E} (hC : Convex ℝ C) (hne : C.Nonempty) :
    IsStarShaped C := by
  rcases hne with ⟨q, hq⟩
  exact ⟨q, hq, hC.starConvex hq⟩

end Definitions

section StarShapedLimits

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **Theorem 4.17.** If the union of a sequence of star-shaped sets is
bounded and the sequence converges in the Painleve--Kuratowski sense, then
the limit is star-shaped. -/
theorem isStarShaped_of_pkConverges {C : ℕ → Set E} {D : Set E}
    (hstar : ∀ n, IsStarShaped (C n))
    (hbounded : IsBounded (⋃ n, C n))
    (hlim : PKConverges C D) : IsStarShaped D := by
  choose q hqC hqstar using hstar
  have hqUnion : ∀ n, q n ∈ ⋃ k, C k := fun n ↦ mem_iUnion_of_mem n (hqC n)
  rcases tendsto_subseq_of_bounded hbounded hqUnion with
    ⟨qbar, _hqbarClosure, φ, hφ, hqbar⟩
  have hqbarOuter : qbar ∈ outerSetLimit C :=
    mem_outerSetLimit_iff_exists_subsequence.2
      ⟨φ, q ∘ φ, hφ, fun n ↦ hqC (φ n), hqbar⟩
  have hqbarD : qbar ∈ D := by
    rw [← hlim.outer_eq]
    exact hqbarOuter
  refine ⟨qbar, hqbarD, ?_⟩
  intro x hxD a b ha hb hab
  have hxInner : x ∈ innerSetLimit C := by
    rw [hlim.inner_eq]
    exact hxD
  have hhits : ∀ k : ℕ,
      ∀ᶠ n in atTop, (C (φ n) ∩ ball x (1 / ((k : ℝ) + 1))).Nonempty := by
    intro k
    have hpositive : 0 < 1 / ((k : ℝ) + 1) := by positivity
    exact hφ.tendsto_atTop.eventually
      (mem_innerSetLimit_iff_eventually_ball.1 hxInner _ hpositive)
  rcases extraction_forall_of_eventually hhits with ⟨ψ, hψ, hhit⟩
  choose y hyC hyBall using hhit
  have hyx : Tendsto y atTop (nhds x) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n ↦ dist_nonneg)
      (fun n ↦ (mem_ball.1 (hyBall n)).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  let z : ℕ → E := fun n ↦ a • q (φ (ψ n)) + b • y n
  have hzC : ∀ n, z n ∈ C ((φ ∘ ψ) n) := by
    intro n
    exact hqstar (φ (ψ n)) (hyC n) ha hb hab
  have hqSub : Tendsto (fun n ↦ q (φ (ψ n))) atTop (nhds qbar) := by
    simpa only [Function.comp_apply] using hqbar.comp hψ.tendsto_atTop
  have hzTendsto : Tendsto z atTop (nhds (a • qbar + b • x)) := by
    exact (hqSub.const_smul a).add (hyx.const_smul b)
  have hzOuter : a • qbar + b • x ∈ outerSetLimit C :=
    mem_outerSetLimit_iff_exists_subsequence.2
      ⟨φ ∘ ψ, z, hφ.comp hψ, hzC, hzTendsto⟩
  rw [hlim.outer_eq] at hzOuter
  exact hzOuter

end StarShapedLimits

section StarShapedLimitRegressions

/-- Regression: the theorem recovers star-shapedness of a constant bounded
closed interval. -/
example : IsStarShaped (Set.Icc (-1 : ℝ) 1) := by
  apply isStarShaped_of_pkConverges
      (C := fun _ : ℕ ↦ Set.Icc (-1 : ℝ) 1)
  · intro n
    exact RW.Convex.isStarShaped (convex_Icc (-1 : ℝ) 1) ⟨0, by norm_num⟩
  · simpa only [iUnion_const] using Metric.isBounded_Icc (-1 : ℝ) 1
  · exact pkConverges_const_of_isClosed isClosed_Icc

end StarShapedLimitRegressions

end RW
