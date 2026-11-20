/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 7: Escape and subsequential compactness of epigraphs
-/

import RockafellarWets.Chapter7.EpiLimits
import RockafellarWets.Chapter4.EscapeToHorizon
import RockafellarWets.Chapter4.SetConvergenceCompactness

open Filter Metric Set Topology

namespace RW

variable {E : Type*}

theorem epigraph_const_top : epigraph (fun _ : E ↦ (⊤ : EReal)) = ∅ := by
  ext ⟨x, a⟩
  simp [mem_epigraph_iff]

/-- **Exercise 7.5(a,b).** Escaping epigraphs have identically infinite
lower epi-limit, which already forces epi-convergence. -/
theorem epiConverges_top_iff_epiLowerLimit_eq_top [TopologicalSpace E] (f : ℕ → E → EReal) :
    EpiConverges f (fun _ ↦ ⊤) ↔ epiLowerLimit f = fun _ ↦ ⊤ := by
  refine ⟨fun h ↦ (epiConverges_iff_epiLimits_eq.mp h).1, fun h ↦ ?_⟩
  apply epiConverges_iff_epiLimits_eq.mpr
  exact ⟨h, funext fun x ↦ top_unique (by
    simpa only [h] using epiLowerLimit_le_epiUpperLimit f x)⟩

theorem epiLowerLimit_eq_top_iff [TopologicalSpace E] (f : ℕ → E → EReal) :
    (epiLowerLimit f = fun _ ↦ ⊤) ↔ outerSetLimit (fun n ↦ epigraph (f n)) = ∅ := by
  rw [← epigraph_epiLowerLimit, ← epigraph_const_top (E := E)]
  exact ⟨congrArg epigraph, eq_of_epigraph_eq⟩

/-- **Exercise 7.5(c).** Escape is uniform on each ball, with the same
radius used for the lower bound on function values. -/
theorem epiConverges_top_iff_eventually_on_closedBall [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : ℕ → E → EReal) :
    EpiConverges f (fun _ ↦ ⊤) ↔
      ∀ r : ℝ, 0 < r → ∀ᶠ n in atTop, ∀ x ∈ closedBall (0 : E) r, (r : EReal) ≤ f n x := by
  rw [epiConverges_top_iff_epiLowerLimit_eq_top, epiLowerLimit_eq_top_iff,
    outerSetLimit_eq_empty_iff_eventually_disjoint_closedBall_zero]
  constructor
  · intro h r hr
    filter_upwards [h r hr] with n hn x hx
    apply le_of_not_gt
    intro hlt
    exact (Set.disjoint_left.mp hn (show (x, r) ∈ epigraph (f n) from hlt.le)) (by
      change dist (x, r) (0, 0) ≤ r
      rw [Prod.dist_eq]
      exact max_le hx (by simp [abs_of_pos hr]))
  · intro h r hr
    filter_upwards [h (r + 1) (by linarith)] with n hn
    apply Set.disjoint_left.mpr
    rintro ⟨x, a⟩ hep hb
    change max (dist x 0) (dist a 0) ≤ r at hb
    have hx := hn x (show dist x 0 ≤ r + 1 from (le_max_left _ _).trans hb |>.trans (by linarith))
    have ha : a ≤ r := (le_abs_self a).trans (by simpa [Real.dist_eq] using (le_max_right _ _).trans hb)
    exact (not_le_of_gt (show (a : EReal) < ((r + 1 : ℝ) : EReal) from
      EReal.coe_lt_coe_iff.mpr (by linarith))) (hx.trans hep)

/-- **Theorem 7.6.** A sequence that does not escape epigraphically has a
subsequence with an epi-limit which is finite or minus infinity somewhere. -/
theorem exists_epiConvergent_subsequence_of_not_escape [PseudoMetricSpace E]
    [SecondCountableTopology E] {f : ℕ → E → EReal} (h : ¬ EpiConverges f (fun _ ↦ ⊤)) :
    ∃ (φ : ℕ → ℕ) (g : E → EReal), StrictMono φ ∧ g ≠ (fun _ ↦ ⊤) ∧ EpiConverges (f ∘ φ) g := by
  rw [epiConverges_top_iff_epiLowerLimit_eq_top, epiLowerLimit_eq_top_iff] at h
  obtain ⟨φ, D, hφ, hD, hlim⟩ := exists_pkConvergent_subsequence_with_nonempty_limit
    (Set.nonempty_iff_ne_empty.mpr h)
  have heq : epigraph (epiLowerLimit (f ∘ φ)) = D :=
    (epigraph_epiLowerLimit _).trans hlim.outer_eq
  refine ⟨φ, epiLowerLimit (f ∘ φ), hφ, ?_, ?_⟩
  · intro htop
    rw [htop, epigraph_const_top] at heq
    exact hD.ne_empty heq.symm
  · unfold EpiConverges
    rw [heq]
    exact hlim

end RW
