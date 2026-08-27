/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Limits of Termwise Horizon Cones

The two inclusions in Exercise 4.21(b).
-/

import RockafellarWets.Chapter4.HorizonLimits

open Filter Function Set Topology

namespace RW

section HorizonConeLimits

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- A nonzero outer limit of a sequence of cones gives an outer limit of
the corresponding direction points in cosmic space. -/
theorem cosmicDirection_mem_outer_cosmicDirections_of_mem_outer_cones
    {K : ℕ → Set E} (hK : ∀ n, IsCone (K n)) {u : CosmicBoundary E}
    (hu : (u : E) ∈ outerSetLimit K) :
    cosmicDirection u ∈ outerSetLimit (fun n ↦ cosmicDirections (K n)) := by
  rcases mem_outerSetLimit_iff_exists_subsequence.1 hu with
    ⟨φ, y, hφ, hyK, hyu⟩
  have hne : ∀ᶠ n in atTop, y n ≠ 0 := by
    exact hyu.eventually (isOpen_compl_singleton.mem_nhds <| by
      intro hu0
      have huEq : (u : E) = 0 := by simpa using hu0
      have hunorm : ‖(u : E)‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
      simp [huEq] at hunorm)
  rcases extraction_of_eventually_atTop hne with ⟨ψ, hψ, hψne⟩
  let v : ℕ → CosmicBoundary E := fun n ↦
    cosmicDirectionOf (y (ψ n)) (hψne n)
  have hySub : Tendsto (fun n ↦ y (ψ n)) atTop (nhds (u : E)) :=
    hyu.comp hψ.tendsto_atTop
  have hnorm : Tendsto (fun n ↦ ‖y (ψ n)‖) atTop (nhds (1 : ℝ)) := by
    simpa [mem_sphere_zero_iff_norm.mp u.property] using hySub.norm
  have hinv : Tendsto (fun n ↦ ‖y (ψ n)‖⁻¹) atTop (nhds (1 : ℝ)) := by
    simpa using hnorm.inv₀ one_ne_zero
  have hnormalize : Tendsto
      (fun n ↦ NormedSpace.normalize (y (ψ n))) atTop (nhds (u : E)) := by
    simpa only [NormedSpace.normalize, one_smul] using hinv.smul hySub
  apply mem_outerSetLimit_iff_exists_subsequence.2
  refine ⟨φ ∘ ψ, fun n ↦ cosmicDirection (v n), hφ.comp hψ, ?_, ?_⟩
  · intro n
    apply mem_cosmicDirections.2
    refine ⟨v n, ?_, rfl⟩
    change NormedSpace.normalize (y (ψ n)) ∈ K (φ (ψ n))
    exact (hK (φ (ψ n))).smul_mem (hyK (ψ n))
      (inv_nonneg.mpr (norm_nonneg _))
  · apply tendsto_subtype_rng.mpr
    simpa only [v, coe_cosmicDirection, coe_cosmicDirectionOf] using hnormalize

/-- **Exercise 4.21(b), outer-limit inclusion.** -/
theorem outerSetLimit_horizonCone_subset_horizonOuterSetLimit
    (C : ℕ → Set E) :
    outerSetLimit (fun n ↦ horizonCone (C n)) ⊆ horizonOuterSetLimit C := by
  intro w hw
  by_cases hw0 : w = 0
  · simpa [hw0] using (isCone_horizonOuterSetLimit C).1
  · let u : CosmicBoundary E := cosmicDirectionOf w hw0
    have huOuter : (u : E) ∈ outerSetLimit (fun n ↦ horizonCone (C n)) := by
      change NormedSpace.normalize w ∈ outerSetLimit (fun n ↦ horizonCone (C n))
      exact (isCone_outerSetLimit _ (fun n ↦ isCone_horizonCone (C n))).smul_mem hw
        (inv_nonneg.mpr (norm_nonneg w))
    have huDirections : cosmicDirection u ∈
        outerSetLimit (fun n ↦ cosmicDirections (horizonCone (C n))) :=
      cosmicDirection_mem_outer_cosmicDirections_of_mem_outer_cones
        (fun n ↦ isCone_horizonCone (C n)) huOuter
    have hterm : ∀ n, cosmicDirections (horizonCone (C n)) ⊆
        closure (ordinaryCosmicSequence C n) := by
      intro n p hp
      rcases mem_cosmicDirections.1 hp with ⟨v, hv, rfl⟩
      exact cosmicDirection_mem_closure_cosmicSet_of_mem_horizonCone hv
    have huClosure : cosmicDirection u ∈
        outerSetLimit (fun n ↦ closure (ordinaryCosmicSequence C n)) :=
      outerSetLimit_mono hterm huDirections
    rw [outerSetLimit_closure] at huClosure
    have huHorizon : (u : E) ∈ horizonOuterSetLimit C :=
      cosmicDirection_mem_outer_ordinaryCosmicSequence_iff.1 huClosure
    have hscaled :=
      (isCone_horizonOuterSetLimit C).smul_mem huHorizon (norm_nonneg w)
    simpa only [u, coe_cosmicDirectionOf,
      NormedSpace.norm_smul_normalize w] using hscaled

/-- **Exercise 4.21(b), inner-limit inclusion.** -/
theorem innerSetLimit_horizonCone_subset_horizonInnerSetLimit
    (C : ℕ → Set E) :
    innerSetLimit (fun n ↦ horizonCone (C n)) ⊆ horizonInnerSetLimit C := by
  intro w hw
  by_cases hw0 : w = 0
  · simpa [hw0] using (isCone_horizonInnerSetLimit C).1
  · let u : CosmicBoundary E := cosmicDirectionOf w hw0
    have huAll : ∀ (φ : ℕ → ℕ), StrictMono φ →
        cosmicDirection u ∈ outerSetLimit (ordinaryCosmicSequence C ∘ φ) := by
      intro φ hφ
      have hwOuter : w ∈
          outerSetLimit ((fun n ↦ horizonCone (C n)) ∘ φ) :=
        innerSetLimit_subset_outerSetLimit _
          (innerSetLimit_subset_subsequence hφ hw)
      have huOuter : (u : E) ∈
          outerSetLimit (fun n ↦ horizonCone (C (φ n))) := by
        change NormedSpace.normalize w ∈
          outerSetLimit (fun n ↦ horizonCone (C (φ n)))
        apply (isCone_outerSetLimit _
          (fun n ↦ isCone_horizonCone (C (φ n)))).smul_mem
        · simpa only [Function.comp_def] using hwOuter
        · exact inv_nonneg.mpr (norm_nonneg w)
      have huDirections : cosmicDirection u ∈
          outerSetLimit (fun n ↦ cosmicDirections (horizonCone (C (φ n)))) :=
        cosmicDirection_mem_outer_cosmicDirections_of_mem_outer_cones
          (fun n ↦ isCone_horizonCone (C (φ n))) huOuter
      have hterm : ∀ n, cosmicDirections (horizonCone (C (φ n))) ⊆
          closure (ordinaryCosmicSequence C (φ n)) := by
        intro n p hp
        rcases mem_cosmicDirections.1 hp with ⟨v, hv, rfl⟩
        exact cosmicDirection_mem_closure_cosmicSet_of_mem_horizonCone hv
      have huClosure : cosmicDirection u ∈
          outerSetLimit (fun n ↦ closure (ordinaryCosmicSequence C (φ n))) :=
        outerSetLimit_mono hterm huDirections
      rw [outerSetLimit_closure] at huClosure
      simpa only [Function.comp_def] using huClosure
    have huInner : cosmicDirection u ∈
        innerSetLimit (ordinaryCosmicSequence C) :=
      mem_innerSetLimit_iff_forall_subsequence_outerSetLimit.2 huAll
    have huHorizon : (u : E) ∈ horizonInnerSetLimit C :=
      cosmicDirection_mem_inner_ordinaryCosmicSequence_iff.1 huInner
    have hscaled :=
      (isCone_horizonInnerSetLimit C).smul_mem huHorizon (norm_nonneg w)
    simpa only [u, coe_cosmicDirectionOf,
      NormedSpace.norm_smul_normalize w] using hscaled

end HorizonConeLimits

end RW
