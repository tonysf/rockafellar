/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 7: Total epi-convergence
-/

import RockafellarWets.Chapter4.TotalConvergenceAutomaticCompletion
import RockafellarWets.Chapter7.EpiLimits

open Set

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Definition 7.51.** Total convergence of real epigraphs. -/
def TotalEpiConverges (f : ℕ → E → EReal) (g : E → EReal) : Prop :=
  TotalConverges (fun n ↦ epigraph (f n)) (epigraph g)

variable [FiniteDimensional ℝ E] {f : ℕ → E → EReal} {g : E → EReal}

theorem TotalEpiConverges.epiConverges (h : TotalEpiConverges f g) : EpiConverges f g :=
  TotalConverges.pkConverges h

/-- **Theorem 7.53(a).** Epi-convergence of convex functions to a function
with nonempty epigraph is total. -/
theorem EpiConverges.total_of_convex (h : EpiConverges f g) (hg : (epigraph g).Nonempty)
    (hf : ∀ n, Convex ℝ (epigraph (f n))) : TotalEpiConverges f g :=
  totalConverges_of_convex h hg hf

/-- **Theorem 7.53(b).** Epi-convergence of positively homogeneous functions
to a function with nonempty epigraph is total. -/
theorem EpiConverges.total_of_positivelyHomogeneous (h : EpiConverges f g)
    (hg : (epigraph g).Nonempty) (hf : ∀ n, PositivelyHomogeneous (f n)) :
    TotalEpiConverges f g :=
  totalConverges_of_isCone h hg fun n ↦ isCone_epigraph_of_positivelyHomogeneous (hf n)

/-- **Theorem 7.53(c).** Epi-convergence of a decreasing sequence of functions
to a function with nonempty epigraph is total. -/
theorem EpiConverges.total_of_antitone (h : EpiConverges f g) (hg : (epigraph g).Nonempty)
    (hf : Antitone f) : TotalEpiConverges f g :=
  totalConverges_of_monotone h hg fun _ _ hij ↦ epigraph_subset_epigraph_iff.mpr (hf hij)

end RW
