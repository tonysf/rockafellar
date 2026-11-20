/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 7: Properties of horizon epi-limits
-/

import RockafellarWets.Chapter3.PositiveHulls
import RockafellarWets.Chapter4.HorizonConeLimits
import RockafellarWets.Chapter7.EpigraphAddition
import RockafellarWets.Chapter7.EpiLimitProperties
import RockafellarWets.Chapter7.HorizonEpiLimits
import RockafellarWets.Chapter7.TotalEpiConvergence

open Filter Function Set Topology

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Proposition 7.52.** Both horizon epi-limits are lower semicontinuous,
including for sequences with empty epigraphs. -/
theorem lowerSemicontinuous_horizonEpiLimits (f : ℕ → E → EReal) :
    LowerSemicontinuous (lowerHorizonEpiLimit f) ∧ LowerSemicontinuous (upperHorizonEpiLimit f) :=
  ⟨(lowerSemicontinuous_epiLowerLimit _).comp (continuous_const.prodMk continuous_id),
    (lowerSemicontinuous_epiUpperLimit _).comp (continuous_const.prodMk continuous_id)⟩

theorem positivelyHomogeneous_lowerHorizonEpiLimit {f : ℕ → E → EReal}
    (hf : ∃ᶠ n in atTop, (epigraph (f n)).Nonempty) :
    PositivelyHomogeneous (lowerHorizonEpiLimit f) := by
  rw [positivelyHomogeneous_iff_isCone_epigraph, epigraph_lowerHorizonEpiLimit hf]
  exact isCone_horizonOuterSetLimit _

theorem positivelyHomogeneous_upperHorizonEpiLimit {f : ℕ → E → EReal}
    (hf : ∀ᶠ n in atTop, (epigraph (f n)).Nonempty) :
    PositivelyHomogeneous (upperHorizonEpiLimit f) := by
  rw [positivelyHomogeneous_iff_isCone_epigraph, epigraph_upperHorizonEpiLimit hf]
  exact isCone_horizonInnerSetLimit _

theorem lowerHorizonEpiLimit_le_upperHorizonEpiLimit (f : ℕ → E → EReal) :
    lowerHorizonEpiLimit f ≤ upperHorizonEpiLimit f := fun x ↦ epiLowerLimit_le_epiUpperLimit _ (0, x)

private theorem epigraph_positiveScalePerspective_eq (f : E → EReal) :
    epigraph (positiveScalePerspective f) =
      positiveHull (epigraph (unitSliceFunction f)) ∩ {p | 0 < p.1.1} := by
  ext ⟨⟨s, x⟩, a⟩
  rw [mem_epigraph_positiveScalePerspective]
  constructor
  · rintro ⟨hs, h⟩
    refine ⟨Or.inr ⟨s, hs, ((1, s⁻¹ • x), s⁻¹ * a), ?_, ?_⟩, hs⟩
    · exact mem_epigraph_unitSliceFunction_iff.mpr ⟨rfl, h⟩
    · simp [Prod.smul_mk, smul_eq_mul, smul_smul, hs.ne']
  · rintro ⟨h, hs⟩
    change 0 < s at hs
    rcases h with he | ⟨t, ht, ⟨⟨r, y⟩, b⟩, hy, he⟩
    · have hz : s = 0 := congrArg (fun p : (ℝ × E) × ℝ ↦ p.1.1) he
      exact (hs.ne' hz).elim
    · obtain ⟨rfl, hfb⟩ := mem_epigraph_unitSliceFunction_iff.mp hy
      have hst' : s = t := by simpa [Prod.smul_mk, smul_eq_mul] using congrArg (fun p : (ℝ × E) × ℝ ↦ p.1.1) he
      have hxy : x = t • y := congrArg (fun p : (ℝ × E) × ℝ ↦ p.1.2) he
      have hab : a = t * b := congrArg Prod.snd he
      subst s
      subst x
      subst a
      simpa [Prod.smul_mk, smul_smul, ht.ne', mul_assoc, smul_eq_mul, ← mul_assoc] using
        And.intro ht hfb

theorem convex_epigraph_positiveScalePerspective {f : E → EReal} (hf : Convex ℝ (epigraph f)) :
    Convex ℝ (epigraph (positiveScalePerspective f)) := by
  rw [epigraph_positiveScalePerspective_eq]
  apply (convex_positiveHull (convex_epigraph_unitSliceFunction hf)).inter
  exact (convex_Ioi (0 : ℝ)).linear_preimage
    ((LinearMap.fst ℝ ℝ E).comp (LinearMap.fst ℝ (ℝ × E) ℝ))

theorem convex_epigraph_upperHorizonEpiLimit {f : ℕ → E → EReal}
    (hf : ∀ n, Convex ℝ (epigraph (f n))) : Convex ℝ (epigraph (upperHorizonEpiLimit f)) := by
  let L : E × ℝ →ₗ[ℝ] (ℝ × E) × ℝ :=
    ((0 : E × ℝ →ₗ[ℝ] ℝ).prod (LinearMap.fst ℝ E ℝ)).prod (LinearMap.snd ℝ E ℝ)
  change Convex ℝ (L ⁻¹' epigraph (epiUpperLimit (fun n ↦ positiveScalePerspective (f n))))
  rw [epigraph_epiUpperLimit]
  exact (convex_innerSetLimit _ (fun n ↦ convex_epigraph_positiveScalePerspective (hf n))).linear_preimage L

/-- **Proposition 7.52**, subadditivity with the book's inf-addition, which
also applies when opposite infinite function values occur. -/
theorem upperHorizonEpiLimit_subadditive {f : ℕ → E → EReal}
    (hf : ∀ n, Convex ℝ (epigraph (f n))) (hne : ∀ᶠ n in atTop, (epigraph (f n)).Nonempty)
    (x y : E) : upperHorizonEpiLimit f (x + y) ≤
      infAddition (upperHorizonEpiLimit f x) (upperHorizonEpiLimit f y) := by
  by_contra! h
  obtain ⟨b, hb, hfb⟩ := EReal.exists_between_coe_real h
  obtain ⟨r, s, hr, hs, rfl⟩ := (infAddition_le_coe_iff ..).mp hb.le
  have hcone := isCone_epigraph_of_positivelyHomogeneous (positivelyHomogeneous_upperHorizonEpiLimit hne)
  exact hfb.not_ge ((hcone.convex_iff_add_mem.mp (convex_epigraph_upperHorizonEpiLimit hf))
    (x := (x, r)) (y := (y, s)) hr hs)

variable [FiniteDimensional ℝ E]

/-- The ordinary epi-limits of the individual horizon functions dominate
the corresponding horizon epi-limits. -/
theorem horizonEpiLimits_le_epiLimits_horizonFunction {f : ℕ → E → EReal}
    (hne : ∀ n, (epigraph (f n)).Nonempty) :
    lowerHorizonEpiLimit f ≤ epiLowerLimit (fun n ↦ horizonFunction (f n)) ∧
      upperHorizonEpiLimit f ≤ epiUpperLimit (fun n ↦ horizonFunction (f n)) := by
  have hev := Eventually.of_forall hne (f := atTop)
  simp only [← epigraph_subset_epigraph_iff, epigraph_epiLowerLimit, epigraph_epiUpperLimit,
    epigraph_lowerHorizonEpiLimit hev.frequently, epigraph_upperHorizonEpiLimit hev,
    epigraph_horizonFunction_eq_horizonCone_epigraph (hne _)]
  exact ⟨outerSetLimit_horizonCone_subset_horizonOuterSetLimit _,
    innerSetLimit_horizonCone_subset_horizonInnerSetLimit _⟩

omit [FiniteDimensional ℝ E] [NormedSpace ℝ E] in
theorem EpiConverges.eventually_nonempty_epigraph {f : ℕ → E → EReal} {g : E → EReal}
    (h : EpiConverges f g) (hg : (epigraph g).Nonempty) : ∀ᶠ n in atTop, (epigraph (f n)).Nonempty := by
  obtain ⟨p, hp⟩ := hg
  have hi : p ∈ innerSetLimit (fun n ↦ epigraph (f n)) := h.inner_eq.symm ▸ hp
  simpa only [inter_univ] using hi univ univ_mem

/-- **Proposition 7.52**, criterion in terms of the lower horizon epi-limit. -/
theorem totalEpiConverges_iff_epiConverges_and_le_lowerHorizon {f : ℕ → E → EReal} {g : E → EReal}
    (hg : (epigraph g).Nonempty) :
    TotalEpiConverges f g ↔ EpiConverges f g ∧ horizonFunction g ≤ lowerHorizonEpiLimit f := by
  rw [TotalEpiConverges, totalConverges_iff_pkConverges_and_horizonOuter_subset]
  apply and_congr_right
  intro h
  have hne := EpiConverges.eventually_nonempty_epigraph h hg
  rw [← epigraph_lowerHorizonEpiLimit hne.frequently, ← epigraph_horizonFunction_eq_horizonCone_epigraph hg,
    epigraph_subset_epigraph_iff]

/-- **Proposition 7.52**, criterion using convergence of both horizon epi-limits. -/
theorem totalEpiConverges_iff_epiConverges_and_horizonEpiConverges {f : ℕ → E → EReal} {g : E → EReal}
    (hg : (epigraph g).Nonempty) :
    TotalEpiConverges f g ↔ EpiConverges f g ∧ HorizonEpiConverges f (horizonFunction g) := by
  constructor
  · intro h
    have hc := h.epiConverges
    have hne := hc.eventually_nonempty_epigraph hg
    have hhor := TotalConverges.horizonConverges h
    exact ⟨hc, eq_of_epigraph_eq ((epigraph_lowerHorizonEpiLimit hne.frequently).trans
      (hhor.2.trans (epigraph_horizonFunction_eq_horizonCone_epigraph hg).symm)),
      eq_of_epigraph_eq ((epigraph_upperHorizonEpiLimit hne).trans
      (hhor.1.trans (epigraph_horizonFunction_eq_horizonCone_epigraph hg).symm))⟩
  · rintro ⟨h, hl, _⟩
    exact (totalEpiConverges_iff_epiConverges_and_le_lowerHorizon hg).mpr ⟨h, hl.ge⟩

end RW
