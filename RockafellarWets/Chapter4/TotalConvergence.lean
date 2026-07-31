/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Total Set Convergence

Definition 4.23 and the horizon criterion in Proposition 4.24.
-/

import RockafellarWets.Chapter4.HorizonLimits

open Filter Function Set Topology

namespace RW

section TotalConvergence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **Definition 4.23.** Total convergence is cosmic convergence of the
ordinary sets to the cosmic closure of a closed limit set. -/
def TotalConverges (Cseq : ℕ → Set E) (C : Set E) : Prop :=
  IsClosed C ∧
    PKConverges (ordinaryCosmicSequence Cseq)
      (closure (cosmicSet C ({0} : Set E)))

omit [FiniteDimensional ℝ E] in
/-- The equivalent `csm Cν → csm C` formulation in Definition 4.23. -/
theorem totalConverges_iff_cosmicClosures {Cseq : ℕ → Set E} {C : Set E} :
    TotalConverges Cseq C ↔
      IsClosed C ∧
        PKConverges (fun n ↦ closure (cosmicSet (Cseq n) ({0} : Set E)))
          (closure (cosmicSet C ({0} : Set E))) := by
  rw [TotalConverges, and_congr_right_iff]
  intro _
  symm
  exact pkConverges_closure_iff _ _

private theorem cosmicEmbed_mem_cosmicClosure_iff {C : Set E} {x : E} :
    cosmicEmbed x ∈ closure (cosmicSet C ({0} : Set E)) ↔ x ∈ closure C := by
  have hzero : IsCone ({0} : Set E) := ⟨by simp, by simp⟩
  rw [closure_cosmicSet hzero, cosmicEmbed_mem_cosmicSet_iff]

private theorem cosmicDirection_mem_cosmicClosure_iff
    {C : Set E} {u : CosmicBoundary E} :
    cosmicDirection u ∈ closure (cosmicSet C ({0} : Set E)) ↔
      (u : E) ∈ horizonCone C := by
  have hzero : IsCone ({0} : Set E) := ⟨by simp, by simp⟩
  rw [closure_cosmicSet hzero, mem_cosmicSet]
  constructor
  · rintro (⟨x, _, hxu⟩ | ⟨v, hv, hvu⟩)
    · exact (cosmicEmbed_ne_cosmicDirection x u hxu).elim
    · have huv : v = u := injective_cosmicDirection hvu
      rcases hv with hv | hv
      · simpa [huv] using hv
      · have hv0 : (v : E) = 0 := by simpa using hv
        have hvnorm : ‖(v : E)‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
        simp [hv0] at hvnorm
  · intro hu
    right
    exact ⟨u, Or.inl hu, rfl⟩

/-- Total convergence entails ordinary Painleve--Kuratowski convergence. -/
theorem TotalConverges.pkConverges {Cseq : ℕ → Set E} {C : Set E}
    (h : TotalConverges Cseq C) : PKConverges Cseq C := by
  rcases h with ⟨hC, hcosmic⟩
  constructor
  · ext x
    rw [← cosmicEmbed_mem_inner_ordinaryCosmicSequence_iff,
      hcosmic.inner_eq, cosmicEmbed_mem_cosmicClosure_iff, hC.closure_eq]
  · ext x
    rw [← cosmicEmbed_mem_outer_ordinaryCosmicSequence_iff,
      hcosmic.outer_eq, cosmicEmbed_mem_cosmicClosure_iff, hC.closure_eq]

/-- Total convergence forces the horizon outer limit into the horizon cone
of the limit. -/
theorem TotalConverges.horizonOuter_subset {Cseq : ℕ → Set E} {C : Set E}
    (h : TotalConverges Cseq C) :
    horizonOuterSetLimit Cseq ⊆ horizonCone C := by
  intro w hw
  rcases hw with rfl | ⟨u, huOuter, r, hr, rfl⟩
  · exact zero_mem_horizonCone C
  · have huClosure : cosmicDirection u ∈
        closure (cosmicSet C ({0} : Set E)) := by
      rw [← h.2.outer_eq]
      exact huOuter
    have huHorizon : (u : E) ∈ horizonCone C :=
      cosmicDirection_mem_cosmicClosure_iff.1 huClosure
    exact (isCone_horizonCone C).2 huHorizon hr

omit [FiniteDimensional ℝ E] in
private theorem cosmicClosure_subset_inner_of_pkConverges
    {Cseq : ℕ → Set E} {C : Set E} (hlim : PKConverges Cseq C) :
    closure (cosmicSet C ({0} : Set E)) ⊆
      innerSetLimit (ordinaryCosmicSequence Cseq) := by
  apply closure_minimal
  · intro p hp
    rw [mem_cosmicSet] at hp
    rcases hp with ⟨x, hxC, rfl⟩ | ⟨u, hu0, rfl⟩
    · exact cosmicEmbed_mem_inner_ordinaryCosmicSequence_iff.2 <| by
        rw [hlim.inner_eq]
        exact hxC
    · have huZero : (u : E) = 0 := by simpa using hu0
      have huNorm : ‖(u : E)‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
      simp [huZero] at huNorm
  · exact isClosed_innerSetLimit _

/-- **Proposition 4.24 (horizon criterion for total convergence).** -/
theorem totalConverges_iff_pkConverges_and_horizonOuter_subset
    {Cseq : ℕ → Set E} {C : Set E} :
    TotalConverges Cseq C ↔
      PKConverges Cseq C ∧ horizonOuterSetLimit Cseq ⊆ horizonCone C := by
  constructor
  · intro h
    exact ⟨h.pkConverges, h.horizonOuter_subset⟩
  · rintro ⟨hlim, hhor⟩
    have hC : IsClosed C := hlim.isClosed
    let T : Set (CosmicSpace E) := closure (cosmicSet C ({0} : Set E))
    have hTInner : T ⊆ innerSetLimit (ordinaryCosmicSequence Cseq) :=
      cosmicClosure_subset_inner_of_pkConverges hlim
    have hOuterT : outerSetLimit (ordinaryCosmicSequence Cseq) ⊆ T := by
      intro p hp
      rcases cosmicEmbed_or_cosmicDirection p with ⟨x, rfl⟩ | ⟨u, rfl⟩
      · apply cosmicEmbed_mem_cosmicClosure_iff.2
        rw [hC.closure_eq, ← hlim.outer_eq]
        exact cosmicEmbed_mem_outer_ordinaryCosmicSequence_iff.1 hp
      · apply cosmicDirection_mem_cosmicClosure_iff.2
        exact hhor (cosmicDirection_mem_outer_ordinaryCosmicSequence_iff.1 hp)
    refine ⟨hC, ?_⟩
    constructor
    · exact Set.Subset.antisymm
        ((innerSetLimit_subset_outerSetLimit _).trans hOuterT) hTInner
    · exact Set.Subset.antisymm hOuterT
        (hTInner.trans (innerSetLimit_subset_outerSetLimit _))

/-- In the situation of Proposition 4.24 the horizon limit exists and equals
the horizon cone of the limit set. -/
theorem TotalConverges.horizonConverges {Cseq : ℕ → Set E} {C : Set E}
    (h : TotalConverges Cseq C) : HorizonConverges Cseq (horizonCone C) := by
  have houter : horizonOuterSetLimit Cseq = horizonCone C := by
    apply Set.Subset.antisymm h.horizonOuter_subset
    intro w hw
    by_cases hw0 : w = 0
    · simpa [hw0] using (isCone_horizonOuterSetLimit Cseq).1
    · let u : CosmicBoundary E := cosmicDirectionOf w hw0
      have huHor : (u : E) ∈ horizonCone C := by
        change NormedSpace.normalize w ∈ horizonCone C
        exact (isCone_horizonCone C).smul_mem hw
          (inv_nonneg.mpr (norm_nonneg w))
      have huOuter : (u : E) ∈ horizonOuterSetLimit Cseq :=
        cosmicDirection_mem_outer_ordinaryCosmicSequence_iff.1 <| by
          rw [h.2.outer_eq]
          exact cosmicDirection_mem_cosmicClosure_iff.2 huHor
      have hscaled := (isCone_horizonOuterSetLimit Cseq).smul_mem huOuter
        (norm_nonneg w)
      simpa only [u, coe_cosmicDirectionOf,
        NormedSpace.norm_smul_normalize w] using hscaled
  have hinner : horizonInnerSetLimit Cseq = horizonCone C := by
    apply Set.Subset.antisymm
    · exact (horizonInnerSetLimit_subset_horizonOuterSetLimit Cseq).trans
        h.horizonOuter_subset
    · intro w hw
      by_cases hw0 : w = 0
      · simpa [hw0] using (isCone_horizonInnerSetLimit Cseq).1
      · let u : CosmicBoundary E := cosmicDirectionOf w hw0
        have huHor : (u : E) ∈ horizonCone C := by
          change NormedSpace.normalize w ∈ horizonCone C
          exact (isCone_horizonCone C).smul_mem hw
            (inv_nonneg.mpr (norm_nonneg w))
        have huInner : (u : E) ∈ horizonInnerSetLimit Cseq :=
          cosmicDirection_mem_inner_ordinaryCosmicSequence_iff.1 <| by
            rw [h.2.inner_eq]
            exact cosmicDirection_mem_cosmicClosure_iff.2 huHor
        have hscaled := (isCone_horizonInnerSetLimit Cseq).smul_mem huInner
          (norm_nonneg w)
        simpa only [u, coe_cosmicDirectionOf,
          NormedSpace.norm_smul_normalize w] using hscaled
  exact ⟨hinner, houter⟩

end TotalConvergence

end RW
