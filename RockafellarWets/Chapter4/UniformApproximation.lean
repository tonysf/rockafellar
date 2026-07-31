/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Uniform approximation on bounded balls

This file proves Theorem 4.10 in its closed-ball/open-thickening form.
-/

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Sequences
import RockafellarWets.Chapter4.DistanceConvergence

open Bornology Filter Function Metric Set Topology

namespace RW

section UniformApproximation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Uniform inner approximation on every bounded ball. -/
def EventuallyInnerApproximates
    (C : Set E) (Cseq : ℕ → Set E) : Prop :=
  ∀ ρ > 0, ∀ ε > 0,
    ∀ᶠ n in atTop,
      C ∩ closedBall 0 ρ ⊆ thickening ε (Cseq n)

/-- Uniform outer approximation on every bounded ball. -/
def EventuallyOuterApproximates
    (Cseq : ℕ → Set E) (C : Set E) : Prop :=
  ∀ ρ > 0, ∀ ε > 0,
    ∀ᶠ n in atTop,
      Cseq n ∩ closedBall 0 ρ ⊆ thickening ε C

/-- **Theorem 4.10(a).** Inner-limit inclusion is equivalent to uniform
approximation of the limit set on every bounded ball. -/
theorem subset_innerSetLimit_iff_eventuallyInnerApproximates
    {C : Set E} {Cseq : ℕ → Set E} (hC : IsClosed C) :
    C ⊆ innerSetLimit Cseq ↔ EventuallyInnerApproximates C Cseq := by
  constructor
  · intro hinner ρ hρ ε hε
    by_contra hnot
    rw [not_eventually] at hnot
    have hfrequent :
        ∃ᶠ n in atTop,
          ∃ x ∈ C ∩ closedBall 0 ρ,
            x ∉ thickening ε (Cseq n) := by
      exact hnot.mono fun _ hn ↦ Set.not_subset.mp hn
    rcases extraction_of_frequently_atTop hfrequent with
      ⟨φ, hφ, hbad⟩
    choose x hxK hxnot using hbad
    have hKcompact : IsCompact (C ∩ closedBall (0 : E) ρ) :=
      (isCompact_closedBall (0 : E) ρ).inter_left hC
    rcases hKcompact.tendsto_subseq hxK with
      ⟨xbar, hxbarK, ψ, hψ, hxto⟩
    have hxbarInner : xbar ∈ innerSetLimit Cseq := hinner hxbarK.1
    have hhit :
        ∀ᶠ n in atTop,
          (Cseq ((φ ∘ ψ) n) ∩ ball xbar (ε / 3)).Nonempty :=
      (hφ.comp hψ).tendsto_atTop.eventually
        ((mem_innerSetLimit_iff_eventually_ball.1 hxbarInner)
          (ε / 3) (by positivity))
    have hclose :
        ∀ᶠ n in atTop, x (ψ n) ∈ ball xbar (ε / 3) :=
      hxto.eventually (ball_mem_nhds xbar (by positivity))
    rcases (hhit.and hclose).exists with
      ⟨n, ⟨z, hzC, hzclose⟩, hxclose⟩
    apply hxnot (ψ n)
    rw [mem_thickening_iff]
    refine ⟨z, hzC, ?_⟩
    have htri : dist (x (ψ n)) z ≤
        dist (x (ψ n)) xbar + dist xbar z := dist_triangle _ _ _
    have hxlt : dist (x (ψ n)) xbar < ε / 3 := by
      simpa only [mem_ball, dist_comm] using hxclose
    have hzlt : dist xbar z < ε / 3 := by
      simpa only [mem_ball, dist_comm] using hzclose
    linarith
  · intro hunif x hxC
    apply mem_innerSetLimit_iff_eventually_ball.2
    intro ε hε
    let ρ : ℝ := ‖x‖ + 1
    have hρ : 0 < ρ := by dsimp [ρ]; positivity
    have hxBall : x ∈ closedBall (0 : E) ρ := by
      simp only [mem_closedBall, dist_zero_right, ρ]
      linarith
    exact (hunif ρ hρ ε hε).mono fun n hn ↦ by
      have hxThick : x ∈ thickening ε (Cseq n) := hn ⟨hxC, hxBall⟩
      rcases mem_thickening_iff.1 hxThick with ⟨y, hyC, hyDist⟩
      exact ⟨y, hyC, by simpa only [mem_ball, dist_comm] using hyDist⟩

/-- **Theorem 4.10(b).** Outer-limit inclusion in a closed set is equivalent
to eventual uniform containment near that set on every bounded ball. -/
theorem outerSetLimit_subset_iff_eventuallyOuterApproximates
    {C : Set E} {Cseq : ℕ → Set E} (hC : IsClosed C) :
    outerSetLimit Cseq ⊆ C ↔ EventuallyOuterApproximates Cseq C := by
  constructor
  · intro houter ρ hρ ε hε
    by_contra hnot
    rw [not_eventually] at hnot
    have hfrequent :
        ∃ᶠ n in atTop,
          ∃ x ∈ Cseq n ∩ closedBall 0 ρ,
            x ∉ thickening ε C := by
      exact hnot.mono fun _ hn ↦ Set.not_subset.mp hn
    rcases extraction_of_frequently_atTop hfrequent with
      ⟨φ, hφ, hbad⟩
    choose x hxK hxnot using hbad
    rcases (isCompact_closedBall (0 : E) ρ).tendsto_subseq
        (fun n ↦ (hxK n).2) with
      ⟨xbar, _hxbarBall, ψ, hψ, hxto⟩
    have hxbarOuter : xbar ∈ outerSetLimit Cseq :=
      mem_outerSetLimit_iff_exists_subsequence.2
        ⟨φ ∘ ψ, x ∘ ψ, hφ.comp hψ,
          fun n ↦ (hxK (ψ n)).1, hxto⟩
    have hxbarC : xbar ∈ C := houter hxbarOuter
    have hclose :
        ∀ᶠ n in atTop, x (ψ n) ∈ ball xbar ε :=
      hxto.eventually (ball_mem_nhds xbar hε)
    rcases hclose.exists with ⟨n, hn⟩
    apply hxnot (ψ n)
    rw [mem_thickening_iff]
    exact ⟨xbar, hxbarC, by simpa only [mem_ball] using hn⟩
  · intro hunif x hxOuter
    rcases mem_outerSetLimit_iff_exists_subsequence.1 hxOuter with
      ⟨φ, y, hφ, hyC, hyx⟩
    rw [← hC.closure_eq]
    apply mem_closure_iff_nhds.2
    intro V hV
    rcases Metric.mem_nhds_iff.1 hV with ⟨ε, hε, hball⟩
    let ρ : ℝ := ‖x‖ + 1
    have hρ : 0 < ρ := by dsimp [ρ]; positivity
    have hyBall :
        ∀ᶠ n in atTop, y n ∈ closedBall (0 : E) ρ := by
      have hball : ball x 1 ⊆ closedBall (0 : E) ρ := by
        intro z hz
        rw [mem_ball] at hz
        rw [mem_closedBall, dist_zero_right]
        have htri := norm_le_norm_sub_add z x
        have hz' : ‖z - x‖ < 1 := by
          simpa only [dist_eq_norm] using hz
        dsimp [ρ]
        linarith
      exact (hyx.eventually (ball_mem_nhds x zero_lt_one)).mono
        fun n hn ↦ hball hn
    have hunifSub :
        ∀ᶠ n in atTop,
          Cseq (φ n) ∩ closedBall 0 ρ ⊆ thickening (ε / 2) C :=
      hφ.tendsto_atTop.eventually
        (hunif ρ hρ (ε / 2) (half_pos hε))
    have hyClose : ∀ᶠ n in atTop, y n ∈ ball x (ε / 2) :=
      hyx.eventually (ball_mem_nhds x (half_pos hε))
    rcases (hunifSub.and (hyBall.and hyClose)).exists with
      ⟨n, hn, hynBall, hynClose⟩
    have hyThick : y n ∈ thickening (ε / 2) C :=
      hn ⟨hyC n, hynBall⟩
    rcases mem_thickening_iff.1 hyThick with ⟨z, hzC, hyz⟩
    refine ⟨z, hball ?_, hzC⟩
    have htri : dist z x ≤ dist z (y n) + dist (y n) x :=
      dist_triangle _ _ _
    have hzy : dist z (y n) < ε / 2 := by simpa [dist_comm] using hyz
    have hyxn : dist (y n) x < ε / 2 := by
      simpa only [mem_ball, dist_comm] using hynClose
    exact htri.trans_lt (by linarith)

/-- The convergent form of Theorem 4.10. -/
theorem pkConverges_iff_eventuallyInnerApproximates_and_eventuallyOuterApproximates
    {C : Set E} {Cseq : ℕ → Set E} (hC : IsClosed C) :
    PKConverges Cseq C ↔
      EventuallyInnerApproximates C Cseq ∧
        EventuallyOuterApproximates Cseq C := by
  constructor
  · intro h
    exact ⟨
      (subset_innerSetLimit_iff_eventuallyInnerApproximates hC).1
        h.inner_eq.symm.subset,
      (outerSetLimit_subset_iff_eventuallyOuterApproximates hC).1
        h.outer_eq.subset⟩
  · rintro ⟨hin, hout⟩
    have hCinner :=
      (subset_innerSetLimit_iff_eventuallyInnerApproximates hC).2 hin
    have houterC :=
      (outerSetLimit_subset_iff_eventuallyOuterApproximates hC).2 hout
    exact ⟨Set.Subset.antisymm
      ((innerSetLimit_subset_outerSetLimit Cseq).trans houterC) hCinner,
      Set.Subset.antisymm houterC
        (hCinner.trans (innerSetLimit_subset_outerSetLimit Cseq))⟩

/-- The arbitrary-center variant in Theorem 4.10(a'). -/
def EventuallyInnerApproximatesAround
    (x₀ : E) (C : Set E) (Cseq : ℕ → Set E) : Prop :=
  ∀ ρ > 0, ∀ ε > 0,
    ∀ᶠ n in atTop,
      C ∩ closedBall x₀ ρ ⊆ thickening ε (Cseq n)

/-- The arbitrary-center variant in Theorem 4.10(b'). -/
def EventuallyOuterApproximatesAround
    (x₀ : E) (Cseq : ℕ → Set E) (C : Set E) : Prop :=
  ∀ ρ > 0, ∀ ε > 0,
    ∀ᶠ n in atTop,
      Cseq n ∩ closedBall x₀ ρ ⊆ thickening ε C

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem closedBall_center_subset_closedBall_zero
    (x₀ : E) {ρ : ℝ} :
    closedBall x₀ ρ ⊆ closedBall (0 : E) (ρ + ‖x₀‖) := by
  intro x hx
  rw [mem_closedBall] at hx ⊢
  rw [dist_zero_right]
  calc
    ‖x‖ ≤ ‖x - x₀‖ + ‖x₀‖ := norm_le_norm_sub_add _ _
    _ = dist x x₀ + ‖x₀‖ := by rw [dist_eq_norm]
    _ ≤ ρ + ‖x₀‖ := add_le_add hx le_rfl

/-- **Theorem 4.10(a').** The inner approximation criterion may be tested
on balls with arbitrary centers. -/
theorem subset_innerSetLimit_iff_forall_eventuallyInnerApproximatesAround
    {C : Set E} {Cseq : ℕ → Set E} (hC : IsClosed C) :
    C ⊆ innerSetLimit Cseq ↔
      ∀ x₀ : E, EventuallyInnerApproximatesAround x₀ C Cseq := by
  rw [subset_innerSetLimit_iff_eventuallyInnerApproximates hC]
  constructor
  · intro h x₀ ρ hρ ε hε
    have hR : 0 < ρ + ‖x₀‖ :=
      hρ.trans_le (le_add_of_nonneg_right (norm_nonneg x₀))
    exact (h (ρ + ‖x₀‖) hR ε hε).mono fun _ hn ↦
      (inter_subset_inter_right C
        (closedBall_center_subset_closedBall_zero x₀)).trans hn
  · intro h
    simpa only [EventuallyInnerApproximatesAround, norm_zero, add_zero] using h 0

/-- **Theorem 4.10(b').** The outer approximation criterion may be tested
on balls with arbitrary centers. -/
theorem outerSetLimit_subset_iff_forall_eventuallyOuterApproximatesAround
    {C : Set E} {Cseq : ℕ → Set E} (hC : IsClosed C) :
    outerSetLimit Cseq ⊆ C ↔
      ∀ x₀ : E, EventuallyOuterApproximatesAround x₀ Cseq C := by
  rw [outerSetLimit_subset_iff_eventuallyOuterApproximates hC]
  constructor
  · intro h x₀ ρ hρ ε hε
    have hR : 0 < ρ + ‖x₀‖ :=
      hρ.trans_le (le_add_of_nonneg_right (norm_nonneg x₀))
    exact (h (ρ + ‖x₀‖) hR ε hε).mono fun _ hn x hx ↦
      hn ⟨hx.1, closedBall_center_subset_closedBall_zero x₀ hx.2⟩
  · intro h
    simpa only [EventuallyOuterApproximatesAround, norm_zero, add_zero] using h 0

/-- It is enough in Theorem 4.10(a) to impose the inclusions only above one
fixed nonnegative radius. -/
theorem subset_innerSetLimit_iff_exists_large_ball_approximation
    {C : Set E} {Cseq : ℕ → Set E} (hC : IsClosed C) :
    C ⊆ innerSetLimit Cseq ↔
      ∃ ρ₀ : ℝ, 0 ≤ ρ₀ ∧
        ∀ ρ : ℝ, ρ₀ ≤ ρ → 0 < ρ → ∀ ε > 0,
          ∀ᶠ n in atTop,
            C ∩ closedBall (0 : E) ρ ⊆ thickening ε (Cseq n) := by
  rw [subset_innerSetLimit_iff_eventuallyInnerApproximates hC]
  constructor
  · intro h
    exact ⟨0, le_rfl, fun ρ _ hρ ε hε ↦ h ρ hρ ε hε⟩
  · rintro ⟨ρ₀, _hρ₀, h⟩ ρ hρ ε hε
    let R : ℝ := max ρ₀ ρ
    have hρR : ρ ≤ R := le_max_right _ _
    have hRpos : 0 < R := hρ.trans_le hρR
    exact (h R (le_max_left _ _) hRpos ε hε).mono fun _ hn ↦
      (inter_subset_inter_right C (closedBall_subset_closedBall hρR)).trans hn

/-- It is enough in Theorem 4.10(b) to impose the inclusions only above one
fixed nonnegative radius. -/
theorem outerSetLimit_subset_iff_exists_large_ball_approximation
    {C : Set E} {Cseq : ℕ → Set E} (hC : IsClosed C) :
    outerSetLimit Cseq ⊆ C ↔
      ∃ ρ₀ : ℝ, 0 ≤ ρ₀ ∧
        ∀ ρ : ℝ, ρ₀ ≤ ρ → 0 < ρ → ∀ ε > 0,
          ∀ᶠ n in atTop,
            Cseq n ∩ closedBall (0 : E) ρ ⊆ thickening ε C := by
  rw [outerSetLimit_subset_iff_eventuallyOuterApproximates hC]
  constructor
  · intro h
    exact ⟨0, le_rfl, fun ρ _ hρ ε hε ↦ h ρ hρ ε hε⟩
  · rintro ⟨ρ₀, _hρ₀, h⟩ ρ hρ ε hε
    let R : ℝ := max ρ₀ ρ
    have hρR : ρ ≤ R := le_max_right _ _
    have hRpos : 0 < R := hρ.trans_le hρR
    exact (h R (le_max_left _ _) hRpos ε hε).mono fun _ hn x hx ↦
      hn ⟨hx.1, closedBall_subset_closedBall hρR hx.2⟩

/-- Rational-radius and rational-error form of Theorem 4.10(a). -/
theorem subset_innerSetLimit_iff_rational_ball_approximation
    {C : Set E} {Cseq : ℕ → Set E} (hC : IsClosed C) :
    C ⊆ innerSetLimit Cseq ↔
      ∀ ρ : ℚ, 0 < ρ → ∀ ε : ℚ, 0 < ε →
        ∀ᶠ n in atTop,
          C ∩ closedBall (0 : E) (ρ : ℝ) ⊆
            thickening (ε : ℝ) (Cseq n) := by
  rw [subset_innerSetLimit_iff_eventuallyInnerApproximates hC]
  constructor
  · intro h ρ hρ ε hε
    exact h (ρ : ℝ) (by exact_mod_cast hρ) (ε : ℝ) (by exact_mod_cast hε)
  · intro h ρ hρ ε hε
    obtain ⟨qρ, hρqρ⟩ := exists_rat_gt ρ
    obtain ⟨qε, hqε, hqεε⟩ := exists_pos_rat_lt hε
    have hqρpos : 0 < qρ := by
      exact_mod_cast hρ.trans hρqρ
    exact (h qρ hqρpos qε hqε).mono fun _ hn ↦
      (inter_subset_inter_right C <|
        closedBall_subset_closedBall hρqρ.le).trans <|
        hn.trans (thickening_mono hqεε.le (Cseq _))

/-- Rational-radius and rational-error form of Theorem 4.10(b). -/
theorem outerSetLimit_subset_iff_rational_ball_approximation
    {C : Set E} {Cseq : ℕ → Set E} (hC : IsClosed C) :
    outerSetLimit Cseq ⊆ C ↔
      ∀ ρ : ℚ, 0 < ρ → ∀ ε : ℚ, 0 < ε →
        ∀ᶠ n in atTop,
          Cseq n ∩ closedBall (0 : E) (ρ : ℝ) ⊆
            thickening (ε : ℝ) C := by
  rw [outerSetLimit_subset_iff_eventuallyOuterApproximates hC]
  constructor
  · intro h ρ hρ ε hε
    exact h (ρ : ℝ) (by exact_mod_cast hρ) (ε : ℝ) (by exact_mod_cast hε)
  · intro h ρ hρ ε hε
    obtain ⟨qρ, hρqρ⟩ := exists_rat_gt ρ
    obtain ⟨qε, hqε, hqεε⟩ := exists_pos_rat_lt hε
    have hqρpos : 0 < qρ := by
      exact_mod_cast hρ.trans hρqρ
    exact (h qρ hqρpos qε hqε).mono fun _ hn x hx ↦
      thickening_mono hqεε.le C <|
        hn ⟨hx.1, closedBall_subset_closedBall hρqρ.le hx.2⟩

end UniformApproximation

end RW
