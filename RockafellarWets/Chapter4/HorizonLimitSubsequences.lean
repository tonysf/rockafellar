/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Subsequence Formulas for Horizon Limits

Exercise 4.21(e), with infinite index sets represented by strictly increasing
maps from the natural numbers.
-/

import RockafellarWets.Chapter4.HorizonLimits

open Filter Function Set Topology

namespace RW

section HorizonSubsequenceFormulas

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- **Exercise 4.21(e), inner formula.** -/
theorem horizonInnerSetLimit_eq_iInter_subsequence_outer (C : ℕ → Set E) :
    horizonInnerSetLimit C =
      ⋂ φ : ℕ → ℕ, ⋂ (_ : StrictMono φ), horizonOuterSetLimit (C ∘ φ) := by
  apply Set.Subset.antisymm
  · intro w hw
    apply mem_iInter.2
    intro φ
    apply mem_iInter.2
    intro hφ
    exact (horizonInnerSetLimit_subset_subsequence hφ hw)
      |> horizonInnerSetLimit_subset_horizonOuterSetLimit (C ∘ φ)
  · intro w hw
    by_cases hw0 : w = 0
    · simpa [hw0] using (isCone_horizonInnerSetLimit C).1
    · let u : CosmicBoundary E := cosmicDirectionOf w hw0
      have huAll : ∀ (φ : ℕ → ℕ), StrictMono φ →
          cosmicDirection u ∈ outerSetLimit (ordinaryCosmicSequence C ∘ φ) := by
        intro φ hφ
        apply cosmicDirection_mem_outer_ordinaryCosmicSequence_iff.2
        change NormedSpace.normalize w ∈ horizonOuterSetLimit (C ∘ φ)
        exact (isCone_horizonOuterSetLimit (C ∘ φ)).smul_mem
          (mem_iInter.1 (mem_iInter.1 hw φ) hφ)
          (inv_nonneg.mpr (norm_nonneg w))
      have huInnerCosmic : cosmicDirection u ∈
          innerSetLimit (ordinaryCosmicSequence C) := by
        rw [mem_innerSetLimit_iff_forall_subsequence_outerSetLimit]
        intro φ hφ
        simpa only [ordinaryCosmicSequence, Function.comp_def] using huAll φ hφ
      have huInner : (u : E) ∈ horizonInnerSetLimit C :=
        cosmicDirection_mem_inner_ordinaryCosmicSequence_iff.1 huInnerCosmic
      have hscaled := (isCone_horizonInnerSetLimit C).smul_mem huInner (norm_nonneg w)
      simpa only [u, coe_cosmicDirectionOf,
        NormedSpace.norm_smul_normalize w] using hscaled

/-- **Exercise 4.21(e), outer formula.** -/
theorem horizonOuterSetLimit_eq_iUnion_subsequence_inner (C : ℕ → Set E) :
    horizonOuterSetLimit C =
      ⋃ φ : ℕ → ℕ, ⋃ (_ : StrictMono φ), horizonInnerSetLimit (C ∘ φ) := by
  apply Set.Subset.antisymm
  · intro w hw
    by_cases hw0 : w = 0
    · apply mem_iUnion_of_mem id
      apply mem_iUnion_of_mem strictMono_id
      simpa [hw0] using (isCone_horizonInnerSetLimit C).1
    · let u : CosmicBoundary E := cosmicDirectionOf w hw0
      have huOuter : cosmicDirection u ∈ outerSetLimit (ordinaryCosmicSequence C) :=
        cosmicDirection_mem_outer_ordinaryCosmicSequence_iff.2 <| by
          change NormedSpace.normalize w ∈ horizonOuterSetLimit C
          exact (isCone_horizonOuterSetLimit C).smul_mem hw
            (inv_nonneg.mpr (norm_nonneg w))
      rcases mem_outerSetLimit_iff_exists_subsequence.1 huOuter with
        ⟨φ, z, hφ, hz, hzu⟩
      rcases exists_pkConvergent_subsequence (ordinaryCosmicSequence C ∘ φ) with
        ⟨ψ, D, hψ, hconv⟩
      have huFinalOuter : cosmicDirection u ∈
          outerSetLimit ((ordinaryCosmicSequence C ∘ φ) ∘ ψ) :=
        mem_outerSetLimit_iff_exists_subsequence.2
          ⟨id, z ∘ ψ, strictMono_id, fun n ↦ by simpa using hz (ψ n),
            hzu.comp hψ.tendsto_atTop⟩
      have huFinalInner : cosmicDirection u ∈
          innerSetLimit ((ordinaryCosmicSequence C ∘ φ) ∘ ψ) := by
        rw [hconv.inner_eq, ← hconv.outer_eq]
        exact huFinalOuter
      let θ : ℕ → ℕ := φ ∘ ψ
      have hθ : StrictMono θ := hφ.comp hψ
      apply mem_iUnion_of_mem θ
      apply mem_iUnion_of_mem hθ
      have huHorizon : (u : E) ∈ horizonInnerSetLimit (C ∘ θ) :=
        cosmicDirection_mem_inner_ordinaryCosmicSequence_iff.1 <| by
          simpa only [θ, ordinaryCosmicSequence, Function.comp_def] using huFinalInner
      have hscaled := (isCone_horizonInnerSetLimit (C ∘ θ)).smul_mem
        huHorizon (norm_nonneg w)
      simpa only [u, coe_cosmicDirectionOf,
        NormedSpace.norm_smul_normalize w] using hscaled
  · intro w hw
    simp only [mem_iUnion] at hw
    rcases hw with ⟨φ, hφ, hw⟩
    exact horizonOuterSetLimit_subsequence_subset hφ
      (horizonInnerSetLimit_subset_horizonOuterSetLimit (C ∘ φ) hw)

end HorizonSubsequenceFormulas

end RW
