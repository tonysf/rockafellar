/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 7: The auxiliary epi-distance
-/

import RockafellarWets.Chapter7.MinimizationCriteria

open Metric Set

open scoped NNReal

namespace RW

variable {E : Type*} [NormedAddCommGroup E]

/-- One of the directed conditions in formula 7(29). The lower cutoff
applies to the source value. -/
def auxEpiComparison (ρ : ℝ≥0) (f g : E → EReal) (η : ℝ) : Prop :=
  ∀ x ∈ closedBall (0 : E) (ρ : ℝ), ∃ y : E, dist x y ≤ η ∧
    g y ≤ max (f x) ((-(ρ : ℝ) : ℝ) : EReal) + (η : EReal)

/-- On proper metric spaces the existential comparison is exactly the
minimum-over-a-closed-ball condition printed in formula 7(29). -/
theorem auxEpiComparison_iff_infimumOn [ProperSpace E] {ρ : ℝ≥0} {f g : E → EReal}
    (hg : LowerSemicontinuous g) {η : ℝ} (hη : 0 ≤ η) :
    auxEpiComparison ρ f g η ↔ ∀ x ∈ closedBall (0 : E) (ρ : ℝ),
      infimumOn g (closedBall x η) ≤ max (f x) ((-(ρ : ℝ) : ℝ) : EReal) + (η : EReal) := by
  constructor
  · intro h x hx
    obtain ⟨y, hxy, hy⟩ := h x hx
    exact (infimumOn_le (show y ∈ closedBall x η from (dist_comm y x).trans_le hxy)).trans hy
  · intro h x hx
    obtain ⟨y, hy, hm⟩ := (hg.lowerSemicontinuousOn _).exists_isMinOn
      ⟨x, mem_closedBall_self hη⟩ (isCompact_closedBall x η)
    exact ⟨y, (dist_comm x y).trans_le hy, (le_infimumOn (isMinOn_iff.mp hm)).trans (h x hx)⟩

/-- An admissible enlargement in formula 7(29), in both directions. For
lower semicontinuous functions on finite-dimensional spaces, the infimum
over a closed ball in the book is attained. -/
def auxEpiAdmissible (ρ : ℝ≥0) (f g : E → EReal) (η : ℝ) : Prop :=
  0 ≤ η ∧ auxEpiComparison ρ f g η ∧ auxEpiComparison ρ g f η

/-- The auxiliary epi-distance in 7.61. Admissible radii exist as soon as
both effective domains are nonempty. -/
noncomputable def auxEpiDistance (ρ : ℝ≥0) (f g : E → EReal) : ℝ :=
  sInf {η | auxEpiAdmissible ρ f g η}

theorem auxEpiAdmissible_bddBelow (ρ : ℝ≥0) (f g : E → EReal) :
    BddBelow {η | auxEpiAdmissible ρ f g η} := ⟨0, fun _ h ↦ h.1⟩

theorem exists_auxEpiAdmissible (ρ : ℝ≥0) {f g : E → EReal}
    (hf : (effectiveDomain f).Nonempty) (hg : (effectiveDomain g).Nonempty) :
    ∃ η, auxEpiAdmissible ρ f g η := by
  have hdir {v u : E → EReal} (h : (effectiveDomain u).Nonempty) :
      ∃ M : ℝ, ∀ η ≥ M, auxEpiComparison ρ v u η := by
    obtain ⟨y, hy⟩ := h
    obtain ⟨r, hr, _⟩ := EReal.exists_between_coe_real (show u y < ⊤ from hy)
    refine ⟨max ((ρ : ℝ) + ‖y‖) (r + ρ), ?_⟩
    intro η hη x hx
    refine ⟨y, ?_, ?_⟩
    · have hx' : ‖x‖ ≤ ρ := by simpa using hx
      calc
        dist x y ≤ ‖x‖ + ‖y‖ := by rw [dist_eq_norm]; exact norm_sub_le _ _
        _ ≤ η := (add_le_add_left hx' _).trans ((le_max_left _ _).trans hη)
    · have h' := (le_max_right _ _).trans hη
      calc
        u y ≤ (r : EReal) := hr.le
        _ ≤ (((-(ρ : ℝ) + η : ℝ)) : EReal) := EReal.coe_le_coe_iff.mpr (by linarith)
        _ ≤ _ := by rw [EReal.coe_add]; exact add_le_add_left (le_max_right _ _) _
  obtain ⟨M, hM⟩ := hdir (v := f) hg
  obtain ⟨N, hN⟩ := hdir (v := g) hf
  exact ⟨max 0 (max M N), le_max_left _ _, hM _ ((le_max_left _ _).trans (le_max_right _ _)),
    hN _ ((le_max_right _ _).trans (le_max_right _ _))⟩

theorem auxEpiAdmissible_mono {ρ : ℝ≥0} {f g : E → EReal} {η η' : ℝ}
    (h : auxEpiAdmissible ρ f g η) (hle : η ≤ η') : auxEpiAdmissible ρ f g η' := by
  have dir {u v : E → EReal} (hc : auxEpiComparison ρ u v η) : auxEpiComparison ρ u v η' := by
    intro x hx
    obtain ⟨y, hdist, hy⟩ := hc x hx
    exact ⟨y, hdist.trans hle, hy.trans (add_le_add_right (EReal.coe_le_coe_iff.mpr hle) _)⟩
  exact ⟨h.1.trans hle, dir h.2.1, dir h.2.2⟩

theorem auxEpiAdmissible_of_lt {ρ : ℝ≥0} {f g : E → EReal}
    (hf : (effectiveDomain f).Nonempty) (hg : (effectiveDomain g).Nonempty)
    {η : ℝ} (hη : auxEpiDistance ρ f g < η) : auxEpiAdmissible ρ f g η := by
  obtain ⟨e, he, heη⟩ := exists_lt_of_csInf_lt (exists_auxEpiAdmissible ρ hf hg) hη
  exact auxEpiAdmissible_mono he heη.le

theorem auxEpiDistance_nonneg {ρ : ℝ≥0} {f g : E → EReal}
    (hf : (effectiveDomain f).Nonempty) (hg : (effectiveDomain g).Nonempty) :
    0 ≤ auxEpiDistance ρ f g := le_csInf (exists_auxEpiAdmissible ρ hf hg) fun _ h ↦ h.1

end RW
