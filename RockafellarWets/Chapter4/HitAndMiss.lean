/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Hit-and-Miss Criteria

The two halves of Painleve--Kuratowski convergence are characterized by
eventual hits of open sets and eventual misses of compact sets.
-/

import RockafellarWets.Chapter4.SetLimitCharacterizations

open Filter Function Metric Set Topology

namespace RW

section Hits

variable {E : Type*} [TopologicalSpace E]

/-- **Theorem 4.5(a) (hit criterion).** -/
theorem subset_innerSetLimit_iff_eventually_hits_open
    {C : Set E} {Cseq : ℕ → Set E} :
    C ⊆ innerSetLimit Cseq ↔
      ∀ O : Set E, IsOpen O → (C ∩ O).Nonempty →
        ∀ᶠ n in atTop, (Cseq n ∩ O).Nonempty := by
  constructor
  · intro h O hO
    rintro ⟨x, hxC, hxO⟩
    exact h hxC O (hO.mem_nhds hxO)
  · intro h x hxC V hV
    rcases mem_nhds_iff.1 hV with ⟨O, hOV, hO, hxO⟩
    exact (h O hO ⟨x, hxC, hxO⟩).mono fun n ⟨y, hyC, hyO⟩ ↦
      ⟨y, hyC, hOV hyO⟩

/-- **Exercise 4.6 (index criterion).** If every open set that is hit
frequently is in fact hit eventually, the set sequence converges. -/
theorem pkConverges_outerSetLimit_of_frequently_hits_imp_eventually_hits
    {Cseq : ℕ → Set E}
    (h : ∀ O : Set E, IsOpen O →
      (∃ᶠ n in atTop, (Cseq n ∩ O).Nonempty) →
        ∀ᶠ n in atTop, (Cseq n ∩ O).Nonempty) :
    PKConverges Cseq (outerSetLimit Cseq) := by
  have houter_inner : outerSetLimit Cseq ⊆ innerSetLimit Cseq := by
    intro x hx V hV
    rcases mem_nhds_iff.1 hV with ⟨O, hOV, hO, hxO⟩
    have hfrequent : ∃ᶠ n in atTop, (Cseq n ∩ O).Nonempty :=
      hx O (hO.mem_nhds hxO)
    exact (h O hO hfrequent).mono fun n ⟨y, hyC, hyO⟩ ↦
      ⟨y, hyC, hOV hyO⟩
  exact ⟨Set.Subset.antisymm (innerSetLimit_subset_outerSetLimit Cseq) houter_inner,
    rfl⟩

end Hits

section MetricHitsAndMisses

variable {E : Type*} [PseudoMetricSpace E]

/-- **Theorem 4.5(a').** It is enough to test hits on open metric balls. -/
theorem subset_innerSetLimit_iff_eventually_hits_ball
    {C : Set E} {Cseq : ℕ → Set E} :
    C ⊆ innerSetLimit Cseq ↔
      ∀ x : E, ∀ ρ : ℝ, 0 < ρ → (C ∩ ball x ρ).Nonempty →
        ∀ᶠ n in atTop, (Cseq n ∩ ball x ρ).Nonempty := by
  constructor
  · intro h x ρ hρ
    rintro ⟨y, hyC, hyBall⟩
    exact h hyC (ball x ρ) (isOpen_ball.mem_nhds hyBall)
  · intro h x hxC V hV
    rcases Metric.mem_nhds_iff.1 hV with ⟨ρ, hρ, hball⟩
    have hhit := h x ρ hρ ⟨x, hxC, mem_ball_self hρ⟩
    exact hhit.mono fun n ⟨y, hyC, hyBall⟩ ↦
      ⟨y, hyC, hball hyBall⟩

variable [ProperSpace E]

/-- **Theorem 4.5(b) (miss criterion).** Compact sets disjoint from the
candidate limit are eventually missed exactly when the outer limit is
contained in that candidate. -/
theorem outerSetLimit_subset_iff_eventually_misses_compact
    {C : Set E} {Cseq : ℕ → Set E} (hC : IsClosed C) :
    outerSetLimit Cseq ⊆ C ↔
      ∀ K : Set E, IsCompact K → Disjoint C K →
        ∀ᶠ n in atTop, Disjoint (Cseq n) K := by
  constructor
  · intro h K hK hCK
    by_contra hnot
    rw [not_eventually] at hnot
    have hfrequent : ∃ᶠ n in atTop, (Cseq n ∩ K).Nonempty :=
      hnot.mono fun n hn ↦ not_disjoint_iff_nonempty_inter.1 hn
    rcases extraction_of_frequently_atTop hfrequent with ⟨φ, hφ, hhit⟩
    choose y hyCseq hyK using hhit
    rcases hK.tendsto_subseq hyK with ⟨x, hxK, ψ, hψ, hyx⟩
    have hxOuter : x ∈ outerSetLimit Cseq :=
      mem_outerSetLimit_iff_exists_subsequence.2
        ⟨φ ∘ ψ, y ∘ ψ, hφ.comp hψ, fun n ↦ hyCseq (ψ n), hyx⟩
    exact hCK.le_bot ⟨h hxOuter, hxK⟩
  · intro h x hxOuter
    by_contra hxC
    have hxCompl : Cᶜ ∈ nhds x := hC.isOpen_compl.mem_nhds hxC
    rcases Metric.mem_nhds_iff.1 hxCompl with ⟨ρ, hρ, hball⟩
    let K : Set E := closedBall x (ρ / 2)
    have hCK : Disjoint C K := by
      rw [Set.disjoint_left]
      intro y hyC hyK
      have hyBall : y ∈ ball x ρ :=
        closedBall_subset_ball (half_lt_self hρ) hyK
      exact hball hyBall hyC
    have hmiss : ∀ᶠ n in atTop, Disjoint (Cseq n) K :=
      h K (isCompact_closedBall x (ρ / 2)) hCK
    have hhit : ∃ᶠ n in atTop, (Cseq n ∩ ball x (ρ / 2)).Nonempty :=
      hxOuter (ball x (ρ / 2)) (ball_mem_nhds x (half_pos hρ))
    rcases (hhit.and_eventually hmiss).exists with ⟨n, ⟨y, hyCseq, hyBall⟩, hn⟩
    exact hn.le_bot ⟨hyCseq, ball_subset_closedBall hyBall⟩

/-- **Theorem 4.5(b').** It is enough to test misses on closed metric balls. -/
theorem outerSetLimit_subset_iff_eventually_misses_closedBall
    {C : Set E} {Cseq : ℕ → Set E} (hC : IsClosed C) :
    outerSetLimit Cseq ⊆ C ↔
      ∀ x : E, ∀ ρ : ℝ, Disjoint C (closedBall x ρ) →
        ∀ᶠ n in atTop, Disjoint (Cseq n) (closedBall x ρ) := by
  constructor
  · intro h x ρ hdisj
    exact (outerSetLimit_subset_iff_eventually_misses_compact hC).1 h
      (closedBall x ρ) (isCompact_closedBall x ρ) hdisj
  · intro h x hxOuter
    by_contra hxC
    have hxCompl : Cᶜ ∈ nhds x := hC.isOpen_compl.mem_nhds hxC
    rcases Metric.mem_nhds_iff.1 hxCompl with ⟨ρ, hρ, hball⟩
    have hdisj : Disjoint C (closedBall x (ρ / 2)) := by
      rw [Set.disjoint_left]
      intro y hyC hyBall
      exact hball (closedBall_subset_ball (half_lt_self hρ) hyBall) hyC
    have hmiss := h x (ρ / 2) hdisj
    have hhit := hxOuter (ball x (ρ / 2)) (ball_mem_nhds x (half_pos hρ))
    rcases (hhit.and_eventually hmiss).exists with ⟨n, ⟨y, hyCseq, hyBall⟩, hn⟩
    exact hn.le_bot ⟨hyCseq, ball_subset_closedBall hyBall⟩

end MetricHitsAndMisses

end RW
