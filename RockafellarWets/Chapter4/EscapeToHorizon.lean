/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Escape to the horizon

This file completes Corollary 4.11, including its two excess-set
characterizations.
-/

import RockafellarWets.Chapter4.UniformApproximation

open Filter Metric Set Topology

namespace RW

section EscapeToHorizon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Convergence to the empty set is equivalent to having empty outer limit. -/
theorem pkConverges_empty_iff_outerSetLimit_eq_empty
    {Cseq : ℕ → Set E} :
    PKConverges Cseq ∅ ↔ outerSetLimit Cseq = ∅ := by
  constructor
  · exact PKConverges.outer_eq
  · intro houter
    refine ⟨Set.Subset.antisymm ?_ (Set.empty_subset _), houter⟩
    intro x hx
    have hxOuter : x ∈ outerSetLimit Cseq :=
      innerSetLimit_subset_outerSetLimit Cseq hx
    rw [houter] at hxOuter
    exact hxOuter

/-- **Corollary 4.11 (bounded-ball criterion).** A sequence escapes to the
horizon exactly when it eventually misses every ball about the origin. -/
theorem outerSetLimit_eq_empty_iff_eventually_disjoint_closedBall_zero
    (Cseq : ℕ → Set E) :
    outerSetLimit Cseq = ∅ ↔
      ∀ ρ > 0, ∀ᶠ n in atTop,
        Disjoint (Cseq n) (closedBall (0 : E) ρ) := by
  constructor
  · intro houter ρ _hρ
    have hsubset : outerSetLimit Cseq ⊆ (∅ : Set E) := by
      rw [houter]
    exact (outerSetLimit_subset_iff_eventually_misses_closedBall
      isClosed_empty).1 hsubset 0 ρ (by simp)
  · intro hmiss
    apply Set.Subset.antisymm
    · intro x hxOuter
      let ρ : ℝ := dist (0 : E) x + 1
      have hρ : 0 < ρ := by
        dsimp [ρ]
        positivity
      have heventual := hmiss ρ hρ
      have hfrequent := hxOuter (ball x 1) (ball_mem_nhds x zero_lt_one)
      rcases (hfrequent.and_eventually heventual).exists with
        ⟨n, ⟨y, hyC, hyBall⟩, hn⟩
      have hyClosedBall : y ∈ closedBall (0 : E) ρ := by
        rw [mem_closedBall]
        have htriangle : dist y 0 ≤ dist y x + dist x 0 :=
          dist_triangle _ _ _
        have hyClose : dist y x < 1 := by
          simpa only [mem_ball] using hyBall
        dsimp [ρ]
        rw [dist_comm (0 : E) x]
        linarith
      exact (hn.le_bot ⟨hyC, hyClosedBall⟩).elim
    · exact Set.empty_subset _

/-- The bounded-ball form of the first assertion of Corollary 4.11, stated
directly using Painleve--Kuratowski convergence. -/
theorem pkConverges_empty_iff_eventually_disjoint_closedBall_zero
    (Cseq : ℕ → Set E) :
    PKConverges Cseq ∅ ↔
      ∀ ρ > 0, ∀ᶠ n in atTop,
        Disjoint (Cseq n) (closedBall (0 : E) ρ) := by
  rw [pkConverges_empty_iff_outerSetLimit_eq_empty,
    outerSetLimit_eq_empty_iff_eventually_disjoint_closedBall_zero]

/-- **Corollary 4.11(a).** Inner-limit inclusion is equivalent to every
inner excess escaping to the horizon. -/
theorem subset_innerSetLimit_iff_inner_excesses_escape
    {C : Set E} {Cseq : ℕ → Set E} (hC : IsClosed C) :
    C ⊆ innerSetLimit Cseq ↔
      ∀ ε > 0,
        outerSetLimit (fun n ↦ C \ thickening ε (Cseq n)) = ∅ := by
  rw [subset_innerSetLimit_iff_eventuallyInnerApproximates hC]
  constructor
  · intro hunif ε hε
    rw [outerSetLimit_eq_empty_iff_eventually_disjoint_closedBall_zero]
    intro ρ hρ
    exact (hunif ρ hρ ε hε).mono fun n hn ↦ by
      rw [Set.disjoint_left]
      intro x hxExcess hxBall
      exact hxExcess.2 (hn ⟨hxExcess.1, hxBall⟩)
  · intro hescape ρ hρ ε hε
    have hmiss :=
      (outerSetLimit_eq_empty_iff_eventually_disjoint_closedBall_zero
        (fun n ↦ C \ thickening ε (Cseq n))).1
        (hescape ε hε) ρ hρ
    exact hmiss.mono fun n hn x hx ↦ by
      by_contra hxThick
      exact hn.le_bot ⟨⟨hx.1, hxThick⟩, hx.2⟩

/-- **Corollary 4.11(b).** Outer-limit inclusion is equivalent to every
outer excess escaping to the horizon. -/
theorem outerSetLimit_subset_iff_outer_excesses_escape
    {C : Set E} {Cseq : ℕ → Set E} (hC : IsClosed C) :
    outerSetLimit Cseq ⊆ C ↔
      ∀ ε > 0,
        outerSetLimit (fun n ↦ Cseq n \ thickening ε C) = ∅ := by
  rw [outerSetLimit_subset_iff_eventuallyOuterApproximates hC]
  constructor
  · intro hunif ε hε
    rw [outerSetLimit_eq_empty_iff_eventually_disjoint_closedBall_zero]
    intro ρ hρ
    exact (hunif ρ hρ ε hε).mono fun n hn ↦ by
      rw [Set.disjoint_left]
      intro x hxExcess hxBall
      exact hxExcess.2 (hn ⟨hxExcess.1, hxBall⟩)
  · intro hescape ρ hρ ε hε
    have hmiss :=
      (outerSetLimit_eq_empty_iff_eventually_disjoint_closedBall_zero
        (fun n ↦ Cseq n \ thickening ε C)).1
        (hescape ε hε) ρ hρ
    exact hmiss.mono fun n hn x hx ↦ by
      by_contra hxThick
      exact hn.le_bot ⟨⟨hx.1, hxThick⟩, hx.2⟩

end EscapeToHorizon

end RW
