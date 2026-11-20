/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 7: Properties of epi-limits
-/

import RockafellarWets.Chapter7.EpiLimits
import RockafellarWets.Chapter4.ConeLimits

open Filter Set Topology

namespace RW

section Topological

variable {E : Type*} [TopologicalSpace E]

/-- **Proposition 7.4(a).** -/
theorem lowerSemicontinuous_epiLowerLimit (f : ℕ → E → EReal) :
    LowerSemicontinuous (epiLowerLimit f) := by
  apply lowerSemicontinuous_of_isClosed_epigraph_ereal
  rw [epigraph_epiLowerLimit]
  exact isClosed_outerSetLimit _

theorem lowerSemicontinuous_epiUpperLimit (f : ℕ → E → EReal) :
    LowerSemicontinuous (epiUpperLimit f) := by
  apply lowerSemicontinuous_of_isClosed_epigraph_ereal
  rw [epigraph_epiUpperLimit]
  exact isClosed_innerSetLimit _

theorem EpiConverges.lowerSemicontinuous {f : ℕ → E → EReal} {g : E → EReal}
    (h : EpiConverges f g) : LowerSemicontinuous g := by
  rw [← (epiConverges_iff_epiLimits_eq.mp h).1]
  exact lowerSemicontinuous_epiLowerLimit _

/-- The lower semicontinuous closure of an arbitrary extended-real function. -/
noncomputable def epiClosure (f : E → EReal) : E → EReal := epiLowerLimit (fun _ ↦ f)

theorem epigraph_epiClosure (f : E → EReal) :
    epigraph (epiClosure f) = closure (epigraph f) := by
  rw [epiClosure, epigraph_epiLowerLimit, outerSetLimit_const]

theorem epiClosure_eq_of_lowerSemicontinuous {f : E → EReal} (hf : LowerSemicontinuous f) :
    epiClosure f = f := by
  apply eq_of_epigraph_eq
  rw [epigraph_epiClosure, (isClosed_epigraph_of_lsc_ereal f hf).closure_eq]

/-- **Proposition 7.4(b).** Termwise lower closure preserves both epi-limits. -/
theorem epiLimits_congr_epiClosure {f g : ℕ → E → EReal}
    (h : ∀ n, epiClosure (f n) = epiClosure (g n)) :
    epiLowerLimit f = epiLowerLimit g ∧ epiUpperLimit f = epiUpperLimit g := by
  have hc : (fun n ↦ closure (epigraph (f n))) = fun n ↦ closure (epigraph (g n)) :=
    funext fun n ↦ by rw [← epigraph_epiClosure, h n, epigraph_epiClosure]
  constructor
  · apply eq_of_epigraph_eq
    rw [epigraph_epiLowerLimit, epigraph_epiLowerLimit,
      ← outerSetLimit_closure (fun n ↦ epigraph (f n)), hc, outerSetLimit_closure]
  · apply eq_of_epigraph_eq
    rw [epigraph_epiUpperLimit, epigraph_epiUpperLimit,
      ← innerSetLimit_closure (fun n ↦ epigraph (f n)), hc, innerSetLimit_closure]

/-- At a height strictly above the pointwise infimum some epigraph already
contains the point. Taking closures also captures the endpoint. -/
theorem closure_epigraph_iInf {ι : Type*} (f : ι → E → EReal) :
    closure (epigraph (fun x ↦ ⨅ i, f i x)) = closure (⋃ i, epigraph (f i)) := by
  apply Subset.antisymm
  · apply closure_minimal _ isClosed_closure
    rintro ⟨x, a⟩ ha
    change (⨅ i, f i x) ≤ (a : EReal) at ha
    have hsub : Ioi a ⊆ (Prod.mk x) ⁻¹' closure (⋃ i, epigraph (f i)) := by
      intro b hab
      obtain ⟨i, hi⟩ := iInf_lt_iff.mp (ha.trans_lt (EReal.coe_lt_coe_iff.mpr hab))
      exact subset_closure (mem_iUnion_of_mem i (show (x, b) ∈ epigraph (f i) from hi.le))
    exact closure_minimal hsub (isClosed_closure.preimage
      (continuous_const.prodMk continuous_id)) (by simp [closure_Ioi])
  · exact closure_mono (iUnion_subset fun i ↦ epigraph_subset_epigraph_iff.mpr
      fun x ↦ iInf_le (fun j ↦ f j x) i)

/-- **Proposition 7.4(c).** A decreasing sequence epi-converges to the lower
closure of its pointwise infimum. -/
theorem epiConverges_of_antitone {f : ℕ → E → EReal} (h : Antitone f) :
    EpiConverges f (epiClosure (fun x ↦ ⨅ n, f n x)) := by
  unfold EpiConverges
  rw [epigraph_epiClosure, closure_epigraph_iInf]
  exact pkConverges_of_monotone fun _ _ hij ↦ epigraph_subset_epigraph_iff.mpr (h hij)

/-- **Proposition 7.4(d).** An increasing sequence epi-converges to the
pointwise supremum of its termwise lower closures. -/
theorem epiConverges_of_monotone {f : ℕ → E → EReal} (h : Monotone f) :
    EpiConverges f (fun x ↦ ⨆ n, epiClosure (f n) x) := by
  have hsup : epigraph (fun x ↦ ⨆ n, epiClosure (f n) x) =
      ⋂ n, closure (epigraph (f n)) := by
    ext ⟨x, a⟩
    simp only [mem_epigraph_iff, iSup_le_iff, mem_iInter, ← epigraph_epiClosure]
  unfold EpiConverges
  rw [hsup]
  exact pkConverges_of_antitone fun _ _ hij ↦ epigraph_subset_epigraph_iff.mpr (h hij)

/-- **Proposition 7.4(g).** The sandwich rule for epi-convergence. -/
theorem EpiConverges.sandwich {f g h : ℕ → E → EReal} {u : E → EReal}
    (hf : EpiConverges f u) (hh : EpiConverges h u) (hfg : f ≤ g) (hgh : g ≤ h) :
    EpiConverges g u :=
  PKConverges.sandwich hh hf (fun n ↦ epigraph_subset_epigraph_iff.mpr (hgh n))
    (fun n ↦ epigraph_subset_epigraph_iff.mpr (hfg n))

/-- **Proposition 7.4(h).** Projecting the outer limit of the epigraphs
bounds the effective domain of the lower epi-limit. -/
theorem effectiveDomain_epiLowerLimit_subset (f : ℕ → E → EReal) :
    effectiveDomain (epiLowerLimit f) ⊆ outerSetLimit (fun n ↦ effectiveDomain (f n)) := by
  rw [← epigraph_proj_eq_effectiveDomain, epigraph_epiLowerLimit]
  simpa only [epigraph_proj_eq_effectiveDomain] using
    (image_outerSetLimit_subset_outerSetLimit_image continuous_fst (C := fun n ↦ epigraph (f n)))

theorem innerSetLimit_prod_const {F : Type*} [TopologicalSpace F]
    (C : ℕ → Set E) {D : Set F} (hD : IsClosed D) :
    innerSetLimit (fun n ↦ C n ×ˢ D) = innerSetLimit C ×ˢ D := by
  ext ⟨x, y⟩
  constructor
  · intro h
    refine ⟨fun U hU ↦ ?_, ?_⟩
    · exact (h _ (continuous_fst.continuousAt hU)).mono fun _ ⟨p, hp, hU'⟩ ↦
        ⟨p.1, hp.1, hU'⟩
    · rw [← hD.closure_eq]
      exact mem_closure_iff_nhds.mpr fun V hV ↦ by
        obtain ⟨_, p, hp, hpV⟩ := (h _ (continuous_snd.continuousAt hV)).exists
        exact ⟨p.2, hpV, hp.2⟩
  · rintro ⟨hx, hy⟩ W hW
    obtain ⟨U, hU, V, hV, hsub⟩ := mem_nhds_prod_iff.mp hW
    exact (hx U hU).mono fun _ ⟨z, hz, hzU⟩ ↦
      ⟨(z, y), ⟨hz, hy⟩, hsub ⟨hzU, mem_of_mem_nhds hV⟩⟩

private theorem outerSetLimit_prod_const {F : Type*} [TopologicalSpace F]
    (C : ℕ → Set E) {D : Set F} (hD : IsClosed D) :
    outerSetLimit (fun n ↦ C n ×ˢ D) = outerSetLimit C ×ˢ D := by
  ext ⟨x, y⟩
  constructor
  · intro h
    refine ⟨fun U hU ↦ ?_, ?_⟩
    · exact (h _ (continuous_fst.continuousAt hU)).mono fun _ ⟨p, hp, hU'⟩ ↦
        ⟨p.1, hp.1, hU'⟩
    · rw [← hD.closure_eq]
      exact mem_closure_iff_nhds.mpr fun V hV ↦ by
        obtain ⟨_, p, hp, hpV⟩ := (h _ (continuous_snd.continuousAt hV)).exists
        exact ⟨p.2, hpV, hp.2⟩
  · rintro ⟨hx, hy⟩ W hW
    obtain ⟨U, hU, V, hV, hsub⟩ := mem_nhds_prod_iff.mp hW
    exact (hx U hU).mono fun _ ⟨z, hz, hzU⟩ ↦
      ⟨(z, y), ⟨hz, hy⟩, hsub ⟨hzU, mem_of_mem_nhds hV⟩⟩

/-- **Proposition 7.4(f).** Lower and upper epi-limits of indicators are the
indicators of the respective outer and inner set limits. -/
theorem epiLimits_indicatorVA (C : ℕ → Set E) :
    epiLowerLimit (fun n ↦ indicatorVA (C n)) = indicatorVA (outerSetLimit C) ∧
      epiUpperLimit (fun n ↦ indicatorVA (C n)) = indicatorVA (innerSetLimit C) := by
  constructor <;> apply eq_of_epigraph_eq
  · simp only [epigraph_epiLowerLimit, epigraph_indicatorVA, outerSetLimit_prod_const C isClosed_Ici]
  · simp only [epigraph_epiUpperLimit, epigraph_indicatorVA, innerSetLimit_prod_const C isClosed_Ici]

theorem indicatorVA_epiLimit_iff (C : ℕ → Set E) (D : Set E) :
    (indicatorVA D = epiLowerLimit (fun n ↦ indicatorVA (C n)) ↔ D = outerSetLimit C) ∧
    (indicatorVA D = epiUpperLimit (fun n ↦ indicatorVA (C n)) ↔ D = innerSetLimit C) := by
  have inj : Function.Injective (indicatorVA (E := E)) := fun A B h ↦ by
    simpa only [effectiveDomain_indicatorVA] using congrArg effectiveDomain h
  rw [(epiLimits_indicatorVA C).1, (epiLimits_indicatorVA C).2]
  exact ⟨inj.eq_iff, inj.eq_iff⟩

end Topological

/-- **Proposition 7.4(e).** Positive homogeneity passes to both epi-limits. -/
theorem positivelyHomogeneous_epiLimits {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℕ → E → EReal} (h : ∀ n, PositivelyHomogeneous (f n)) :
    PositivelyHomogeneous (epiLowerLimit f) ∧ PositivelyHomogeneous (epiUpperLimit f) := by
  simp only [positivelyHomogeneous_iff_isCone_epigraph, epigraph_epiLowerLimit, epigraph_epiUpperLimit]
  exact ⟨isCone_outerSetLimit _ (fun n ↦ isCone_epigraph_of_positivelyHomogeneous (h n)),
    isCone_innerSetLimit _ (fun n ↦ isCone_epigraph_of_positivelyHomogeneous (h n))⟩

end RW
