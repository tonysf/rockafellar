/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 7: Lower and upper epi-limits
-/

import RockafellarWets.Chapter3.HorizonFunctions
import RockafellarWets.Chapter4.ImageLimits
import RockafellarWets.Chapter5.GraphicalLimits
import RockafellarWets.Chapter5.ProfileMappings

open Set Topology

namespace RW

variable {E : Type*}

/-- The lower endpoint of each real vertical fiber. An empty fiber gives
`⊤`, while a fiber unbounded below gives `⊥`. -/
noncomputable def epiBoundary (S : Set (E × ℝ)) (x : E) : EReal :=
  ⨅ a : {a : ℝ // (x, a) ∈ S}, ((a : ℝ) : EReal)

theorem epigraph_subset_epigraph_iff {f g : E → EReal} :
    epigraph f ⊆ epigraph g ↔ g ≤ f := by
  constructor
  · intro h x
    by_contra! hlt
    obtain ⟨a, hfa, hag⟩ := EReal.exists_between_coe_real hlt
    exact hag.not_ge (h (a := (x, a)) hfa.le)
  · intro h p hp
    exact (h p.1).trans hp

variable [TopologicalSpace E]

/-- A closed set whose vertical fibers are upward closed is the epigraph of
its fiber endpoints. -/
theorem epigraph_epiBoundary {S : Set (E × ℝ)} (hc : IsClosed S)
    (hup : ∀ x a b, (x, a) ∈ S → a ≤ b → (x, b) ∈ S) :
    epigraph (epiBoundary S) = S := by
  ext ⟨x, a⟩
  change epiBoundary S x ≤ (a : EReal) ↔ (x, a) ∈ S
  constructor
  · intro ha
    have hsub : Ioi a ⊆ (Prod.mk x) ⁻¹' S := by
      intro b hab
      have hlt : epiBoundary S x < (b : EReal) :=
        ha.trans_lt (EReal.coe_lt_coe_iff.mpr hab)
      obtain ⟨t, ht⟩ := iInf_lt_iff.mp hlt
      exact hup x t b t.property (EReal.coe_lt_coe_iff.mp ht).le
    have hclosed : IsClosed ((Prod.mk x) ⁻¹' S) :=
      hc.preimage (continuous_const.prodMk continuous_id)
    exact closure_minimal hsub hclosed (by simp [closure_Ioi])
  · intro ha
    exact iInf_le _ (⟨a, ha⟩ : {t : ℝ // (x, t) ∈ S})

/-- **Definition 7.1.** The function with the outer limit of the epigraphs
as its epigraph. -/
noncomputable def epiLowerLimit (f : ℕ → E → EReal) : E → EReal :=
  epiBoundary (outerSetLimit fun n ↦ epigraph (f n))

/-- **Definition 7.1.** The function with the inner limit of the epigraphs
as its epigraph. -/
noncomputable def epiUpperLimit (f : ℕ → E → EReal) : E → EReal :=
  epiBoundary (innerSetLimit fun n ↦ epigraph (f n))

/-- **Definition 7.1.** Epi-convergence is set convergence of real epigraphs. -/
def EpiConverges (f : ℕ → E → EReal) (g : E → EReal) : Prop :=
  PKConverges (fun n ↦ epigraph (f n)) (epigraph g)

omit [TopologicalSpace E] in
private theorem shift_epigraph_subset (f : E → EReal) {d : ℝ} (hd : 0 ≤ d) :
    (fun p : E × ℝ ↦ (p.1, p.2 + d)) '' epigraph f ⊆ epigraph f := by
  rintro _ ⟨p, hp, rfl⟩
  exact hp.trans (EReal.coe_le_coe_iff.mpr (le_add_of_nonneg_right hd))

theorem epigraph_epiLowerLimit (f : ℕ → E → EReal) :
    epigraph (epiLowerLimit f) = outerSetLimit (fun n ↦ epigraph (f n)) := by
  apply epigraph_epiBoundary (isClosed_outerSetLimit _)
  intro x a b ha hab
  let T := fun p : E × ℝ ↦ (p.1, p.2 + (b - a))
  have hc : Continuous T := continuous_fst.prodMk (continuous_snd.add continuous_const)
  have ht := image_outerSetLimit_subset_outerSetLimit_image hc
    (C := fun n ↦ epigraph (f n)) ⟨(x, a), ha, rfl⟩
  have h := outerSetLimit_mono (fun n ↦ shift_epigraph_subset (f n) (sub_nonneg.mpr hab)) ht
  simpa [T] using h

theorem epigraph_epiUpperLimit (f : ℕ → E → EReal) :
    epigraph (epiUpperLimit f) = innerSetLimit (fun n ↦ epigraph (f n)) := by
  apply epigraph_epiBoundary (isClosed_innerSetLimit _)
  intro x a b ha hab
  let T := fun p : E × ℝ ↦ (p.1, p.2 + (b - a))
  have hc : Continuous T := continuous_fst.prodMk (continuous_snd.add continuous_const)
  have ht := image_innerSetLimit_subset_innerSetLimit_image hc
    (C := fun n ↦ epigraph (f n)) ⟨(x, a), ha, rfl⟩
  have h := innerSetLimit_mono (fun n ↦ shift_epigraph_subset (f n) (sub_nonneg.mpr hab)) ht
  simpa [T] using h

theorem epiLowerLimit_le_epiUpperLimit (f : ℕ → E → EReal) :
    epiLowerLimit f ≤ epiUpperLimit f := by
  apply epigraph_subset_epigraph_iff.mp
  rw [epigraph_epiLowerLimit, epigraph_epiUpperLimit]
  exact innerSetLimit_subset_outerSetLimit _

theorem epiConverges_iff_epiLimits_eq {f : ℕ → E → EReal} {g : E → EReal} :
    EpiConverges f g ↔ epiLowerLimit f = g ∧ epiUpperLimit f = g := by
  unfold EpiConverges PKConverges
  rw [← epigraph_epiLowerLimit, ← epigraph_epiUpperLimit]
  exact ⟨fun ⟨hu, hl⟩ ↦ ⟨eq_of_epigraph_eq hl, eq_of_epigraph_eq hu⟩,
    fun ⟨hl, hu⟩ ↦ ⟨congrArg epigraph hu, congrArg epigraph hl⟩⟩

theorem exists_epiConverges_iff (f : ℕ → E → EReal) :
    (∃ g, EpiConverges f g) ↔ epiLowerLimit f = epiUpperLimit f := by
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨hl, hu⟩ := epiConverges_iff_epiLimits_eq.mp hg
    exact hl.trans hu.symm
  · exact fun h ↦ ⟨_, epiConverges_iff_epiLimits_eq.mpr ⟨h, rfl⟩⟩

/-- Equation 7(1). -/
theorem epiConverges_iff_graphicalConverges {f : ℕ → E → EReal} {g : E → EReal} :
    EpiConverges f g ↔ GraphicalConverges (fun n ↦ epiProfile (f n)) (epiProfile g) :=
  Iff.rfl

/-- Equation 7(2), outer limit. -/
theorem epigraph_epiLowerLimit_eq_svGraph (f : ℕ → E → EReal) :
    epigraph (epiLowerLimit f) = svGraph (graphicalOuterLimit (fun n ↦ epiProfile (f n))) :=
  epigraph_epiLowerLimit f

/-- Equation 7(2), inner limit. -/
theorem epigraph_epiUpperLimit_eq_svGraph (f : ℕ → E → EReal) :
    epigraph (epiUpperLimit f) = svGraph (graphicalInnerLimit (fun n ↦ epiProfile (f n))) :=
  epigraph_epiUpperLimit f

end RW
