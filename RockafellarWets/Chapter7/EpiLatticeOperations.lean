/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Minima and maxima in epigraphical limits

These are the formulas on page 277 immediately before Proposition 7.48.
Taking the lower epi-limit commutes with taking the pointwise minimum.
For the upper epi-limit there is an inequality, which can be strict.
-/

import RockafellarWets.Chapter7.EpiLimitProperties
import RockafellarWets.Chapter3.Pointwise
import RockafellarWets.Chapter4.SetLimitExamples
import RockafellarWets.Chapter5.HorizonSetLimitsAlong

open Filter Set Topology

namespace RW

variable {E : Type*}

section Topological
variable [TopologicalSpace E]

theorem epiLowerLimit_mono {f g : ℕ → E → EReal} (h : f ≤ g) :
    epiLowerLimit f ≤ epiLowerLimit g := by
  apply epigraph_subset_epigraph_iff.mp
  rw [epigraph_epiLowerLimit, epigraph_epiLowerLimit]
  exact outerSetLimit_mono fun n ↦ epigraph_subset_epigraph_iff.mpr (h n)

theorem epiUpperLimit_mono {f g : ℕ → E → EReal} (h : f ≤ g) :
    epiUpperLimit f ≤ epiUpperLimit g := by
  apply epigraph_subset_epigraph_iff.mp
  rw [epigraph_epiUpperLimit, epigraph_epiUpperLimit]
  exact innerSetLimit_mono fun n ↦ epigraph_subset_epigraph_iff.mpr (h n)

theorem epiUpperLimit_inf_le (f g : ℕ → E → EReal) :
    epiUpperLimit (fun n x ↦ f n x ⊓ g n x) ≤ fun x ↦ epiUpperLimit f x ⊓ epiUpperLimit g x :=
  le_inf (epiUpperLimit_mono fun _ _ ↦ inf_le_left) (epiUpperLimit_mono fun _ _ ↦ inf_le_right)

theorem sup_epiLowerLimit_le (f g : ℕ → E → EReal) :
    (fun x ↦ epiLowerLimit f x ⊔ epiLowerLimit g x) ≤ epiLowerLimit (fun n x ↦ f n x ⊔ g n x) :=
  sup_le (epiLowerLimit_mono fun _ _ ↦ le_sup_left) (epiLowerLimit_mono fun _ _ ↦ le_sup_right)

end Topological

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem epiLowerLimit_inf (f g : ℕ → E → EReal) :
    epiLowerLimit (fun n x ↦ f n x ⊓ g n x) = fun x ↦ epiLowerLimit f x ⊓ epiLowerLimit g x := by
  apply eq_of_epigraph_eq
  rw [epigraph_epiLowerLimit, epigraph_inf]
  simp only [epigraph_inf, epigraph_epiLowerLimit]
  exact outerSetLimitAlong_union atTop (fun n ↦ epigraph (f n)) (fun n ↦ epigraph (g n))

theorem EpiConverges.inf {f g : ℕ → E → EReal} {u v : E → EReal} (hf : EpiConverges f u)
    (hg : EpiConverges g v) : EpiConverges (fun n x ↦ f n x ⊓ g n x) (fun x ↦ u x ⊓ v x) := by
  obtain ⟨hfL, hfU⟩ := epiConverges_iff_epiLimits_eq.mp hf
  obtain ⟨hgL, hgU⟩ := epiConverges_iff_epiLimits_eq.mp hg
  apply epiConverges_iff_epiLimits_eq.mpr
  have hL := epiLowerLimit_inf f g
  rw [hfL, hgL] at hL
  have hU := epiUpperLimit_inf_le f g
  rw [hfU, hgU] at hU
  exact ⟨hL, hU.antisymm (hL ▸ epiLowerLimit_le_epiUpperLimit _)⟩

/-- The upper epi-limit of a sequence alternating between two functions
is the maximum of their lower semicontinuous closures. -/
theorem epiUpperLimit_alternating (f g : E → EReal) :
    epiUpperLimit (fun n ↦ if Even n then f else g) =
      fun x ↦ epiClosure f x ⊔ epiClosure g x := by
  apply eq_of_epigraph_eq
  rw [epigraph_epiUpperLimit, epigraph_sup, epigraph_epiClosure, epigraph_epiClosure,
    ← innerSetLimit_alternatingSets]
  congr 1
  funext n
  by_cases he : Even n <;> simp [alternatingSets, he]

/-- Finite constant functions alternating in opposite phases have pointwise
minimum zero. Each sequence has upper epi-limit one. -/
theorem epiUpperLimit_inf_strict :
    ∃ f g : ℕ → ℝ → EReal, epiUpperLimit (fun n x ↦ f n x ⊓ g n x) 0 <
      epiUpperLimit f 0 ⊓ epiUpperLimit g 0 := by
  let z := fun _ : ℝ ↦ (0 : EReal)
  let o := fun _ : ℝ ↦ (1 : EReal)
  let f := fun n : ℕ ↦ if Even n then z else o
  let g := fun n : ℕ ↦ if Even n then o else z
  have hz : epiClosure z = z := epiClosure_eq_of_lowerSemicontinuous continuous_const.lowerSemicontinuous
  have ho : epiClosure o = o := epiClosure_eq_of_lowerSemicontinuous continuous_const.lowerSemicontinuous
  have hmin : (fun n x ↦ f n x ⊓ g n x) = (fun _ ↦ z) := by
    funext n x
    by_cases hn : Even n <;> simp [f, g, z, o, hn]
  refine ⟨f, g, ?_⟩
  rw [hmin]
  change epiUpperLimit (fun _ ↦ z) 0 < epiUpperLimit (fun n ↦ if Even n then z else o) 0 ⊓
    epiUpperLimit (fun n ↦ if Even n then o else z) 0
  rw [epiUpperLimit_alternating, epiUpperLimit_alternating, hz, ho]
  have ht : epiUpperLimit (fun _ ↦ z) = z := by
    apply eq_of_epigraph_eq
    rw [epigraph_epiUpperLimit, innerSetLimit_const,
      (isClosed_epigraph_of_lsc_ereal z continuous_const.lowerSemicontinuous).closure_eq]
  simp [ht, z, o]

end RW
