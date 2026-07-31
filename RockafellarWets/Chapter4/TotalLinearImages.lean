/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Total convergence of linear images

This file proves Theorem 4.27 and exposes the subsequential form of horizon
outer-limit membership used by later operation theorems.
-/

import RockafellarWets.Chapter3.LinearImages
import RockafellarWets.Chapter4.ImageLimits
import RockafellarWets.Chapter4.TotalConvergence

open Bornology Filter Function Metric Set Topology

namespace RW

section HorizonSelections

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A unit horizon-outer direction is witnessed by a genuine subsequence of
points in the varying sets converging cosmically to that direction. -/
theorem mem_horizonOuterSetLimit_iff_exists_cosmicDirection_subsequence
    {C : ℕ → Set E} {u : CosmicBoundary E} :
    (u : E) ∈ horizonOuterSetLimit C ↔
      ∃ (φ : ℕ → ℕ) (x : ℕ → E), StrictMono φ ∧
        (∀ n, x n ∈ C (φ n)) ∧
        Tendsto (fun n ↦ cosmicEmbed (x n)) atTop
          (nhds (cosmicDirection u)) := by
  constructor
  · intro hu
    have huCosmic : cosmicDirection u ∈
        outerSetLimit (ordinaryCosmicSequence C) :=
      cosmicDirection_mem_outer_ordinaryCosmicSequence_iff.2 hu
    rcases mem_outerSetLimit_iff_exists_subsequence.1 huCosmic with
      ⟨φ, z, hφ, hz, hzu⟩
    have hzImage : ∀ n, z n ∈ cosmicEmbed '' C (φ n) := by
      intro n
      simpa only [ordinaryCosmicSequence, cosmicSet, cosmicDirections_zero,
        union_empty] using hz n
    choose x hxC hxz using hzImage
    refine ⟨φ, x, hφ, hxC, ?_⟩
    apply hzu.congr'
    exact Eventually.of_forall fun n ↦ (hxz n).symm
  · rintro ⟨φ, x, hφ, hxC, hxu⟩
    apply cosmicDirection_mem_outer_ordinaryCosmicSequence_iff.1
    exact mem_outerSetLimit_iff_exists_subsequence.2
      ⟨φ, fun n ↦ cosmicEmbed (x n), hφ,
        fun n ↦ (cosmicEmbed_mem_cosmicSet_iff).2 (hxC n), hxu⟩

end HorizonSelections

section TotalLinearImages

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
/-- A linear image cannot acquire a finite cluster point from an unbounded
source selection when its kernel is trivial on the source horizon outer
limit.  This is the sequence-level engine behind 4.27 and 4.29(c). -/
theorem noConvergentImageEscapeAlong_linear_of_horizonOuter
    {Cseq : ℕ → Set E} (L : E →ₗ[ℝ] F)
    (hker : ∀ ⦃v : E⦄,
      v ∈ horizonOuterSetLimit Cseq → L v = 0 → v = 0) :
    NoConvergentImageEscapeAlong L Cseq := by
  intro φ x y hφ hxC hLxy
  by_contra hxBounded
  rcases exists_cosmicDirection_subsequence_of_not_isBounded hxBounded with
    ⟨u, ψ, hψ, hxu⟩
  have huOuter : (u : E) ∈ horizonOuterSetLimit Cseq :=
    mem_horizonOuterSetLimit_iff_exists_cosmicDirection_subsequence.2
      ⟨φ ∘ ψ, x ∘ ψ, hφ.comp hψ, fun n ↦ hxC (ψ n), hxu⟩
  rcases exists_scaling_of_tendsto_cosmicDirection hxu with
    ⟨a, haPos, haZero, haxu⟩
  have hLscaled : Tendsto (fun n ↦ a n • L (x (ψ n))) atTop
      (nhds (L (u : E))) := by
    convert (L.continuous_of_finiteDimensional.tendsto (u : E)).comp haxu using 1
    ext n
    simp
  have hLsub : Tendsto (fun n ↦ L (x (ψ n))) atTop (nhds y) := by
    simpa only [Function.comp_apply] using hLxy.comp hψ.tendsto_atTop
  have hzero : Tendsto (fun n ↦ a n • L (x (ψ n))) atTop (nhds 0) := by
    simpa only [zero_smul] using haZero.smul hLsub
  have hLu : L (u : E) = 0 := tendsto_nhds_unique hLscaled hzero
  have huZero : (u : E) = 0 := hker huOuter hLu
  have huNorm : ‖(u : E)‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
  simp [huZero] at huNorm

omit [FiniteDimensional ℝ F] in
/-- Under the kernel/horizon hypothesis of Theorem 4.27, a convergent image
selection cannot escape to infinity in the source. -/
theorem noConvergentImageEscapeAlong_linear_of_total
    {Cseq : ℕ → Set E} {C : Set E} (hC : TotalConverges Cseq C)
    (L : E →ₗ[ℝ] F)
    (hker : ∀ ⦃v : E⦄, v ∈ horizonCone C → L v = 0 → v = 0) :
    NoConvergentImageEscapeAlong L Cseq := by
  apply noConvergentImageEscapeAlong_linear_of_horizonOuter L
  intro v hv hLv
  exact hker (hC.horizonOuter_subset hv) hLv

omit [FiniteDimensional ℝ F] in
/-- Positive rescalings of a selection from a totally convergent sequence
are bounded whenever their linear images are bounded. -/
private theorem isBounded_scaled_selection_of_total
    {Cseq : ℕ → Set E} {C : Set E} (hC : TotalConverges Cseq C)
    (L : E →ₗ[ℝ] F)
    (hker : ∀ ⦃v : E⦄, v ∈ horizonCone C → L v = 0 → v = 0)
    {φ : ℕ → ℕ} {x : ℕ → E} {a : ℕ → ℝ}
    (hφ : StrictMono φ) (hxC : ∀ n, x n ∈ Cseq (φ n))
    (haPos : ∀ n, 0 < a n) (haZero : Tendsto a atTop (nhds 0))
    (hLscaled : IsBounded (Set.range fun n ↦ a n • L (x n))) :
    IsBounded (Set.range fun n ↦ a n • x n) := by
  by_contra hscaled
  rcases exists_cosmicDirection_subsequence_of_not_isBounded hscaled with
    ⟨u, ψ, hψ, hqDirection⟩
  rcases exists_scaling_of_tendsto_cosmicDirection hqDirection with
    ⟨b, hbPos, hbZero, hbq⟩
  have habPos : ∀ n, 0 < b n * a (ψ n) := fun n ↦
    mul_pos (hbPos n) (haPos (ψ n))
  have haSub : Tendsto (fun n ↦ a (ψ n)) atTop (nhds 0) :=
    haZero.comp hψ.tendsto_atTop
  have habZero : Tendsto (fun n ↦ b n * a (ψ n)) atTop (nhds 0) := by
    simpa only [zero_mul] using hbZero.mul haSub
  have hxDirection : Tendsto (fun n ↦ cosmicEmbed (x (ψ n))) atTop
      (nhds (cosmicDirection u)) := by
    apply tendsto_cosmicDirection_of_scaling habPos habZero
    simpa only [mul_smul, Function.comp_apply] using hbq
  have huOuter : (u : E) ∈ horizonOuterSetLimit Cseq :=
    mem_horizonOuterSetLimit_iff_exists_cosmicDirection_subsequence.2
      ⟨φ ∘ ψ, x ∘ ψ, hφ.comp hψ, fun n ↦ hxC (ψ n), hxDirection⟩
  have huC : (u : E) ∈ horizonCone C := hC.horizonOuter_subset huOuter
  have hLqBounded : IsBounded
      (Set.range fun n ↦ L (a (ψ n) • x (ψ n))) := by
    apply hLscaled.subset
    rintro _ ⟨n, rfl⟩
    exact ⟨ψ n, by simp⟩
  have hbLqZero : Tendsto
      (fun n ↦ b n • L (a (ψ n) • x (ψ n))) atTop (nhds 0) := by
    obtain ⟨R, hR⟩ := hLqBounded.exists_norm_le
    rw [tendsto_iff_dist_tendsto_zero]
    have hupper : Tendsto (fun n ↦ ‖b n‖ * max R 0) atTop (nhds 0) := by
      simpa only [norm_zero, zero_mul] using
        hbZero.norm.mul_const (max R 0)
    apply squeeze_zero (fun n ↦ dist_nonneg)
      (fun n ↦ ?_) hupper
    calc
      dist (b n • L (a (ψ n) • x (ψ n))) 0 =
          ‖b n • L (a (ψ n) • x (ψ n))‖ := dist_zero_right _
      _ =
          ‖b n‖ * ‖L (a (ψ n) • x (ψ n))‖ := norm_smul _ _
      _ ≤ ‖b n‖ * max R 0 := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact (hR _ ⟨n, rfl⟩).trans (le_max_left _ _)
  have hLhbq : Tendsto
      (fun n ↦ b n • L (a (ψ n) • x (ψ n))) atTop
      (nhds (L (u : E))) := by
    convert (L.continuous_of_finiteDimensional.tendsto (u : E)).comp hbq using 1
    ext n
    simp [smul_smul]
  have hLu : L (u : E) = 0 := tendsto_nhds_unique hLhbq hbLqZero
  have huZero : (u : E) = 0 := hker huC hLu
  have huNorm : ‖(u : E)‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
  simp [huZero] at huNorm

omit [FiniteDimensional ℝ F] in
/-- Unit horizon directions of the image sequence come from horizon
directions of the limit set. -/
private theorem horizonOuter_linear_image_subset
    {Cseq : ℕ → Set E} {C : Set E} (hC : TotalConverges Cseq C)
    (L : E →ₗ[ℝ] F)
    (hker : ∀ ⦃v : E⦄, v ∈ horizonCone C → L v = 0 → v = 0) :
    horizonOuterSetLimit (fun n ↦ L '' Cseq n) ⊆
      horizonCone (L '' C) := by
  intro w hw
  rcases hw with rfl | ⟨u, huOuter, r, hr, rfl⟩
  · exact zero_mem_horizonCone (L '' C)
  · rcases
        mem_horizonOuterSetLimit_iff_exists_cosmicDirection_subsequence.1
          (cosmicDirection_mem_outer_ordinaryCosmicSequence_iff.1 huOuter) with
      ⟨φ, y, hφ, hyImage, hyDirection⟩
    choose x hxC hLx using hyImage
    rcases exists_scaling_of_tendsto_cosmicDirection hyDirection with
      ⟨a, haPos, haZero, hayu⟩
    have hscaledBounded : IsBounded (Set.range fun n ↦ a n • x n) := by
      apply isBounded_scaled_selection_of_total hC L hker hφ hxC haPos haZero
      have hayBounded : IsBounded (Set.range fun n ↦ a n • y n) :=
        Metric.isBounded_range_of_tendsto _ hayu
      simpa only [hLx, ← map_smul] using hayBounded
    rcases tendsto_subseq_of_bounded hscaledBounded
        (fun n ↦ Set.mem_range_self n) with
      ⟨q, -, ψ, hψ, hq⟩
    have hLq : L q = (u : F) := by
      have htoLq : Tendsto (fun n ↦ a (ψ n) • y (ψ n)) atTop
          (nhds (L q)) := by
        convert (L.continuous_of_finiteDimensional.tendsto q).comp hq using 1
        ext n
        simp [Function.comp_def, hLx]
      have htou : Tendsto (fun n ↦ a (ψ n) • y (ψ n)) atTop
          (nhds (u : F)) := hayu.comp hψ.tendsto_atTop
      exact tendsto_nhds_unique htoLq htou
    have hqNe : q ≠ 0 := by
      intro hq0
      subst q
      have huZero : (u : F) = 0 := by simpa using hLq.symm
      have huNorm : ‖(u : F)‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
      simp [huZero] at huNorm
    let v : CosmicBoundary E := cosmicDirectionOf q hqNe
    have haSub : Tendsto (fun n ↦ a (ψ n)) atTop (nhds 0) :=
      haZero.comp hψ.tendsto_atTop
    have hscalePos : ∀ n, 0 < ‖q‖⁻¹ * a (ψ n) := fun n ↦
      mul_pos (inv_pos.mpr (norm_pos_iff.mpr hqNe)) (haPos (ψ n))
    have hscaleZero : Tendsto (fun n ↦ ‖q‖⁻¹ * a (ψ n)) atTop (nhds 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul haSub
    have hscaledToV : Tendsto
        (fun n ↦ (‖q‖⁻¹ * a (ψ n)) • x (ψ n)) atTop
        (nhds (v : E)) := by
      have hconst : Tendsto (fun n ↦ ‖q‖⁻¹ • (a (ψ n) • x (ψ n))) atTop
          (nhds (‖q‖⁻¹ • q)) := tendsto_const_nhds.smul hq
      simpa only [mul_smul, v, coe_cosmicDirectionOf,
        NormedSpace.normalize] using hconst
    have hxDirection : Tendsto (fun n ↦ cosmicEmbed (x (ψ n))) atTop
        (nhds (cosmicDirection v)) :=
      tendsto_cosmicDirection_of_scaling hscalePos hscaleZero hscaledToV
    have hvOuter : (v : E) ∈ horizonOuterSetLimit Cseq :=
      mem_horizonOuterSetLimit_iff_exists_cosmicDirection_subsequence.2
        ⟨φ ∘ ψ, x ∘ ψ, hφ.comp hψ, fun n ↦ hxC (ψ n), hxDirection⟩
    have hvC : (v : E) ∈ horizonCone C := hC.horizonOuter_subset hvOuter
    have hqC : q ∈ horizonCone C := by
      have hscaled := (isCone_horizonCone C).smul_mem hvC (norm_nonneg q)
      simpa only [v, coe_cosmicDirectionOf,
        NormedSpace.norm_smul_normalize q] using hscaled
    have huImage : (u : F) ∈ horizonCone (L '' C) :=
      linearMap_image_horizonCone_subset L ⟨q, hqC, hLq⟩
    exact (isCone_horizonCone (L '' C)).smul_mem huImage hr.le

/-- **Theorem 4.27.** Total convergence is preserved by a linear image when
the kernel meets the horizon cone of the limit only at the origin. -/
theorem TotalConverges.linear_image
    {Cseq : ℕ → Set E} {C : Set E} (hC : TotalConverges Cseq C)
    (L : E →ₗ[ℝ] F)
    (hker : ∀ ⦃v : E⦄, v ∈ horizonCone C → L v = 0 → v = 0) :
    TotalConverges (fun n ↦ L '' Cseq n) (L '' C) := by
  apply totalConverges_iff_pkConverges_and_horizonOuter_subset.2
  constructor
  · exact hC.pkConverges.image_of_noConvergentImageEscapeAlong
      L.continuous_of_finiteDimensional
      (noConvergentImageEscapeAlong_linear_of_total hC L hker)
  · exact horizonOuter_linear_image_subset hC L hker

end TotalLinearImages

end RW
