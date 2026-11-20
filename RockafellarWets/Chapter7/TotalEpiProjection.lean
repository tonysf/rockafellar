/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 7: Inf-projection under total epi-convergence
-/

import RockafellarWets.Chapter3.Parametric
import RockafellarWets.Chapter4.TotalLinearImages
import RockafellarWets.Chapter7.EpiLimitProperties
import RockafellarWets.Chapter7.TotalEpiConvergence

open Filter Function Set Topology

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The projection of an epigraph and the epigraph of the inf-projection
have the same closure, including when a fiber infimum is unattained. -/
theorem closure_epigraph_valueFunction (f : E × F → EReal) :
    closure (epigraph (valueFunction f)) = closure (valueProjection '' epigraph f) := by
  apply le_antisymm _ (closure_mono valueProjection_image_epigraph_subset_epigraph_valueFunction)
  apply closure_minimal _ isClosed_closure
  rintro ⟨u, a⟩ hu
  have hsub : Ioi a ⊆ (Prod.mk u) ⁻¹' closure (valueProjection '' epigraph f) := by
    intro b hab
    obtain ⟨x, hx⟩ := iInf_lt_iff.mp (show (⨅ x, f (x, u)) < (b : EReal) from
      hu.trans_lt (EReal.coe_lt_coe_iff.mpr hab))
    exact subset_closure ⟨((x, u), b), hx.le, rfl⟩
  exact closure_minimal hsub (isClosed_closure.preimage (continuous_const.prodMk continuous_id))
    (by simp [closure_Ioi])

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
/-- Termwise replacements having the same closures preserve total set convergence. -/
theorem TotalConverges.of_termwise_closure_eq {A B : ℕ → Set E} {C : Set E}
    (hc : TotalConverges A C) (hcl : ∀ n, closure (B n) = closure (A n)) : TotalConverges B C := by
  apply totalConverges_iff_pkConverges_and_horizonOuter_subset.mpr
  constructor
  · rw [← pkConverges_closure_iff, funext hcl, pkConverges_closure_iff]
    exact hc.pkConverges
  · rw [← horizonOuterSetLimit_closure, funext hcl, horizonOuterSetLimit_closure]
    exact hc.horizonOuter_subset

/-- **Exercise 7.57.** Inf-projection preserves total epi-convergence when
the limit has strictly positive horizon on nonzero decision directions.
The conclusion permits unattained infima of the approximating functions. -/
theorem TotalEpiConverges.valueFunction {f : ℕ → E × F → EReal} {g : E × F → EReal}
    (hc : TotalEpiConverges f g)
    (hpos : ∀ ⦃x : E⦄, x ≠ 0 → 0 < horizonFunction g (x, (0 : F))) :
    TotalEpiConverges (fun n ↦ valueFunction (f n)) (valueFunction g) := by
  have hker : ∀ ⦃v : (E × F) × ℝ⦄, v ∈ horizonCone (epigraph g) → valueProjection v = 0 → v = 0 := by
    rintro ⟨⟨x, u⟩, a⟩ hv he
    have hu : u = 0 := congrArg Prod.fst he
    have ha : a = 0 := congrArg Prod.snd he
    subst u
    subst a
    have hx : x = 0 := by
      by_contra hn
      exact (hpos hn).not_ge (by simpa using horizonFunction_le_of_mem_horizonCone_epigraph hv)
    simp [hx]
  have h := TotalConverges.linear_image hc valueProjection hker
  rw [← epigraph_valueFunction_eq_valueProjection_image_epigraph_of_lsc_localUniform
    hc.epiConverges.lowerSemicontinuous (isLevelBoundedInXLocallyUniformly_of_horizonFunction_pos hpos)] at h
  exact h.of_termwise_closure_eq fun n ↦ closure_epigraph_valueFunction (f n)

/-- Ordinary epi-convergence suffices in the automatic cases 7.53(a)--(c).
For monotone functions the required direction is nonincreasing. -/
theorem EpiConverges.valueFunction_of_convex_or_homogeneous_or_antitone
    {f : ℕ → E × F → EReal} {g : E × F → EReal}
    (hc : EpiConverges f g) (hg : (epigraph g).Nonempty)
    (hpos : ∀ ⦃x : E⦄, x ≠ 0 → 0 < horizonFunction g (x, (0 : F)))
    (hf : (∀ n, Convex ℝ (epigraph (f n))) ∨ (∀ n, PositivelyHomogeneous (f n)) ∨ Antitone f) :
    EpiConverges (fun n ↦ valueFunction (f n)) (valueFunction g) := by
  have ht : TotalEpiConverges f g := by
    rcases hf with h | h | h
    · exact hc.total_of_convex hg h
    · exact hc.total_of_positivelyHomogeneous hg h
    · exact hc.total_of_antitone hg h
  exact (ht.valueFunction hpos).epiConverges

end RW
