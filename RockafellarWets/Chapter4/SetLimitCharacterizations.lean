/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Characterizations and Elementary Set Limits

Neighborhood, metric, and subsequence characterizations of the limits from
Definition 4.1, followed by the monotone and sandwich rules in 4.3.
-/

import Mathlib.Analysis.SpecificLimits.Basic
import RockafellarWets.Chapter4.SetLimits

open Filter Function Metric Set Topology

namespace RW

section NeighborhoodCharacterizations

variable {E : Type*} [TopologicalSpace E]

/-- Tail-union formula for the outer limit. -/
theorem outerSetLimit_eq_iInter_closure_iUnion_tail (C : ℕ → Set E) :
    outerSetLimit C =
      ⋂ N : ℕ, closure (⋃ n : ℕ, ⋃ _ : N ≤ n, C n) := by
  ext x
  constructor
  · intro hx
    simp only [mem_iInter]
    intro N
    refine mem_closure_iff_nhds.2 fun V hV ↦ ?_
    have hfrequent := hx V hV
    have hlarge : ∀ᶠ n in atTop, N ≤ n := eventually_ge_atTop N
    rcases (hfrequent.and_eventually hlarge).exists with ⟨n, ⟨y, hyC, hyV⟩, hn⟩
    exact ⟨y, hyV, mem_iUnion_of_mem n (mem_iUnion_of_mem hn hyC)⟩
  · intro hx V hV
    rw [frequently_atTop]
    intro N
    have hxN : x ∈ closure (⋃ n : ℕ, ⋃ _ : N ≤ n, C n) := by
      exact mem_iInter.1 hx N
    rcases mem_closure_iff_nhds.1 hxN V hV with ⟨y, hyV, hyTail⟩
    simp only [mem_iUnion] at hyTail
    rcases hyTail with ⟨n, hn, hyC⟩
    exact ⟨n, hn, y, hyC, hyV⟩

/-- Subsequence-intersection formula for the inner limit.  Quantifying over
strictly increasing maps is the sequence form of quantifying over all infinite
index sets in Exercise 4.2(b). -/
theorem innerSetLimit_eq_iInter_subsequence_closure (C : ℕ → Set E) :
    innerSetLimit C =
      ⋂ φ : ℕ → ℕ, ⋂ (_ : StrictMono φ), closure (⋃ n : ℕ, C (φ n)) := by
  ext x
  constructor
  · intro hx
    apply mem_iInter.2
    intro φ
    apply mem_iInter.2
    intro hφ
    refine mem_closure_iff_nhds.2 fun V hV ↦ ?_
    have hhit : ∀ᶠ n in atTop, (C (φ n) ∩ V).Nonempty :=
      hφ.tendsto_atTop.eventually (hx V hV)
    rcases hhit.exists with ⟨n, y, hyC, hyV⟩
    exact ⟨y, hyV, mem_iUnion_of_mem n hyC⟩
  · intro hx V hV
    by_contra hnot
    rw [not_eventually] at hnot
    rcases extraction_of_frequently_atTop hnot with ⟨φ, hφ, hmiss⟩
    have hxφ : x ∈ closure (⋃ n : ℕ, C (φ n)) :=
      mem_iInter.1 (mem_iInter.1 hx φ) hφ
    rcases mem_closure_iff_nhds.1 hxφ V hV with ⟨y, hyV, hyUnion⟩
    simp only [mem_iUnion] at hyUnion
    rcases hyUnion with ⟨n, hyC⟩
    exact hmiss n ⟨y, hyC, hyV⟩

end NeighborhoodCharacterizations

section MetricCharacterizations

variable {E : Type*} [PseudoMetricSpace E]

/-- Metric-ball form of membership in the outer limit. -/
theorem mem_outerSetLimit_iff_frequently_ball {C : ℕ → Set E} {x : E} :
    x ∈ outerSetLimit C ↔
      ∀ ε : ℝ, 0 < ε → ∃ᶠ n in atTop, (C n ∩ ball x ε).Nonempty := by
  constructor
  · intro hx ε hε
    exact hx (ball x ε) (ball_mem_nhds x hε)
  · intro hx V hV
    rcases Metric.mem_nhds_iff.1 hV with ⟨ε, hε, hball⟩
    exact (hx ε hε).mono fun n ⟨y, hyC, hyBall⟩ ↦
      ⟨y, hyC, hball hyBall⟩

/-- Metric-ball form of membership in the inner limit. -/
theorem mem_innerSetLimit_iff_eventually_ball {C : ℕ → Set E} {x : E} :
    x ∈ innerSetLimit C ↔
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, (C n ∩ ball x ε).Nonempty := by
  constructor
  · intro hx ε hε
    exact hx (ball x ε) (ball_mem_nhds x hε)
  · intro hx V hV
    rcases Metric.mem_nhds_iff.1 hV with ⟨ε, hε, hball⟩
    exact (hx ε hε).mono fun n ⟨y, hyC, hyBall⟩ ↦
      ⟨y, hyC, hball hyBall⟩

/-- Thickening formula from Exercise 4.2(c), first in its open-thickening
form.  The outer intersection over every positive radius makes this
equivalent to the printed closed-ball formula. -/
theorem innerSetLimit_eq_iInter_iUnion_iInter_thickening (C : ℕ → Set E) :
    innerSetLimit C =
      ⋂ ε : ℝ, ⋂ (_ : 0 < ε),
        ⋃ N : ℕ, ⋂ n : ℕ, ⋂ (_ : N ≤ n), Metric.thickening ε (C n) := by
  ext x
  rw [mem_innerSetLimit_iff_eventually_ball]
  simp only [mem_iInter, mem_iUnion, eventually_atTop]
  constructor
  · intro hx ε hε
    rcases hx ε hε with ⟨N, hN⟩
    exact ⟨N, fun n hn ↦ Metric.mem_thickening_iff.2 <| by
      rcases hN n hn with ⟨y, hyC, hyBall⟩
      exact ⟨y, hyC, by simpa only [mem_ball, dist_comm] using hyBall⟩⟩
  · intro hx ε hε
    rcases hx ε hε with ⟨N, hN⟩
    exact ⟨N, fun n hn ↦ by
      rcases Metric.mem_thickening_iff.1 (hN n hn) with ⟨y, hyC, hyDist⟩
      exact ⟨y, hyC, by simpa only [mem_ball, dist_comm] using hyDist⟩⟩

/-- The closed-thickening form of Exercise 4.2(c), matching the book's use of
closed balls. -/
theorem innerSetLimit_eq_iInter_iUnion_iInter_cthickening (C : ℕ → Set E) :
    innerSetLimit C =
      ⋂ ε : ℝ, ⋂ (_ : 0 < ε),
        ⋃ N : ℕ, ⋂ n : ℕ, ⋂ (_ : N ≤ n), Metric.cthickening ε (C n) := by
  rw [innerSetLimit_eq_iInter_iUnion_iInter_thickening]
  ext x
  simp only [mem_iInter, mem_iUnion]
  constructor
  · intro hx ε hε
    rcases hx ε hε with ⟨N, hN⟩
    exact ⟨N, fun n hn ↦
      Metric.thickening_subset_cthickening ε (C n) (hN n hn)⟩
  · intro hx ε hε
    rcases hx (ε / 2) (half_pos hε) with ⟨N, hN⟩
    exact ⟨N, fun n hn ↦
      Metric.cthickening_subset_thickening' hε (half_lt_self hε) (C n) (hN n hn)⟩

/-- Sequential characterization of the outer set limit: an outer-limit point
is reached along a strictly increasing extraction of indices. -/
theorem mem_outerSetLimit_iff_exists_subsequence {C : ℕ → Set E} {x : E} :
    x ∈ outerSetLimit C ↔
      ∃ φ : ℕ → ℕ, ∃ y : ℕ → E,
        StrictMono φ ∧ (∀ n, y n ∈ C (φ n)) ∧ Tendsto y atTop (nhds x) := by
  constructor
  · intro hx
    have hfrequent : ∀ k : ℕ,
        ∃ᶠ n in atTop, (C n ∩ ball x (1 / ((k : ℝ) + 1))).Nonempty := by
      intro k
      apply (mem_outerSetLimit_iff_frequently_ball.1 hx)
      positivity
    rcases extraction_forall_of_frequently hfrequent with ⟨φ, hφ, hhit⟩
    choose y hyC hyBall using hhit
    refine ⟨φ, y, hφ, hyC, tendsto_iff_dist_tendsto_zero.2 ?_⟩
    exact squeeze_zero (fun n ↦ dist_nonneg)
      (fun n ↦ (Metric.mem_ball.mp (hyBall n)).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  · rintro ⟨φ, y, hφ, hyC, hyx⟩ V hV
    rw [frequently_atTop]
    intro N
    have hlarge : ∀ᶠ n in atTop, N ≤ φ n :=
      hφ.tendsto_atTop (eventually_ge_atTop N)
    have hyV : ∀ᶠ n in atTop, y n ∈ V := hyx.eventually hV
    rcases (hlarge.and hyV).exists with ⟨n, hn, hyn⟩
    exact ⟨φ n, hn, y n, hyC n, hyn⟩

end MetricCharacterizations

section MonotoneLimits

variable {E : Type*} [TopologicalSpace E]

/-- **Theorem 4.3 (increasing sets).** An increasing sequence converges to the
closure of its union. -/
theorem pkConverges_of_monotone {C : ℕ → Set E} (hC : Monotone C) :
    PKConverges C (closure (⋃ n, C n)) := by
  have hclosure_inner : closure (⋃ n, C n) ⊆ innerSetLimit C := by
    intro x hx V hV
    rcases mem_closure_iff_nhds.1 hx V hV with ⟨y, hyV, hyUnion⟩
    simp only [mem_iUnion] at hyUnion
    rcases hyUnion with ⟨k, hyC⟩
    filter_upwards [eventually_ge_atTop k] with n hn
    exact ⟨y, hC hn hyC, hyV⟩
  have houter_closure : outerSetLimit C ⊆ closure (⋃ n, C n) := by
    intro x hx
    refine mem_closure_iff_nhds.2 fun V hV ↦ ?_
    rcases (hx V hV).exists with ⟨n, y, hyC, hyV⟩
    exact ⟨y, hyV, mem_iUnion_of_mem n hyC⟩
  apply And.intro
  · exact Set.Subset.antisymm
      ((innerSetLimit_subset_outerSetLimit C).trans houter_closure)
      hclosure_inner
  · exact Set.Subset.antisymm houter_closure
      (hclosure_inner.trans (innerSetLimit_subset_outerSetLimit C))

/-- **Theorem 4.3 (decreasing sets).** An antitone sequence converges to the
intersection of the closures of its terms. -/
theorem pkConverges_of_antitone {C : ℕ → Set E} (hC : Antitone C) :
    PKConverges C (⋂ n, closure (C n)) := by
  have hinter_inner : (⋂ n, closure (C n)) ⊆ innerSetLimit C := by
    intro x hx V hV
    apply Eventually.of_forall
    intro n
    have hxn : x ∈ closure (C n) := mem_iInter.1 hx n
    rcases mem_closure_iff_nhds.1 hxn V hV with ⟨y, hyV, hyC⟩
    exact ⟨y, hyC, hyV⟩
  have houter_inter : outerSetLimit C ⊆ ⋂ n, closure (C n) := by
    intro x hx
    apply mem_iInter.2
    intro k
    refine mem_closure_iff_nhds.2 fun V hV ↦ ?_
    have hfrequent := hx V hV
    have hlarge : ∀ᶠ n in atTop, k ≤ n := eventually_ge_atTop k
    rcases (hfrequent.and_eventually hlarge).exists with ⟨n, ⟨y, hyC, hyV⟩, hn⟩
    exact ⟨y, hyV, hC hn hyC⟩
  apply And.intro
  · exact Set.Subset.antisymm
      ((innerSetLimit_subset_outerSetLimit C).trans houter_inter)
      hinter_inner
  · exact Set.Subset.antisymm houter_inter
      (hinter_inner.trans (innerSetLimit_subset_outerSetLimit C))

theorem pkConverges_of_antitone_isClosed {C : ℕ → Set E}
    (hC : Antitone C) (hclosed : ∀ n, IsClosed (C n)) :
    PKConverges C (⋂ n, C n) := by
  simpa only [(hclosed _).closure_eq] using pkConverges_of_antitone hC

/-- **Theorem 4.3 (sandwich rule).** -/
theorem PKConverges.sandwich {A B C : ℕ → Set E} {D : Set E}
    (hA : PKConverges A D) (hC : PKConverges C D)
    (hAB : ∀ n, A n ⊆ B n) (hBC : ∀ n, B n ⊆ C n) :
    PKConverges B D := by
  constructor
  · apply Set.Subset.antisymm
    · rw [← hC.outer_eq]
      exact (innerSetLimit_subset_outerSetLimit B).trans (outerSetLimit_mono hBC)
    · rw [← hA.inner_eq]
      exact innerSetLimit_mono hAB
  · apply Set.Subset.antisymm
    · rw [← hC.outer_eq]
      exact outerSetLimit_mono hBC
    · rw [← hA.inner_eq]
      exact (innerSetLimit_mono hAB).trans (innerSetLimit_subset_outerSetLimit B)

end MonotoneLimits

end RW
