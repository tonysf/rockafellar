/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Mixed Cosmic Set Limits

The full ordinary-plus-direction formulas in Exercise 4.20.
-/

import RockafellarWets.Chapter4.HorizonLimits

open Filter Function Metric Set Topology

namespace RW

section MixedOuterLimit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
private theorem cosmicDirection_outer_of_mem_outer_cones
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

omit [FiniteDimensional ℝ E] in
/-- **Exercise 4.20 (cosmic outer limit).** -/
theorem outerSetLimit_cosmicSet
    (C K : ℕ → Set E) (hK : ∀ n, IsCone (K n)) :
    outerSetLimit (fun n ↦ cosmicSet (C n) (K n)) =
      cosmicSet (outerSetLimit C)
        (horizonOuterSetLimit C ∪ outerSetLimit K) := by
  ext p
  constructor
  · intro hp
    rcases mem_outerSetLimit_iff_exists_subsequence.1 hp with
      ⟨φ, z, hφ, hz, hzp⟩
    have hzUnion : ∀ n, z n ∈ cosmicEmbed '' C (φ n) ∪
        cosmicDirections (K (φ n)) := by
      intro n
      simpa only [cosmicSet] using hz n
    by_cases hord : ∃ᶠ n in atTop, z n ∈ cosmicEmbed '' C (φ n)
    · rcases extraction_of_frequently_atTop hord with ⟨g, hg, hgOrd⟩
      choose x hxC hxz using hgOrd
      have hxCosmic : Tendsto (fun n ↦ cosmicEmbed (x n)) atTop (nhds p) := by
        apply (hzp.comp hg.tendsto_atTop).congr'
        exact Eventually.of_forall fun n ↦ (hxz n).symm
      rcases cosmicEmbed_or_cosmicDirection p with ⟨xbar, rfl⟩ | ⟨u, rfl⟩
      · apply cosmicEmbed_mem_cosmicSet_iff.2
        exact mem_outerSetLimit_iff_exists_subsequence.2
          ⟨φ ∘ g, x, hφ.comp hg, hxC,
            tendsto_cosmicEmbed_iff.1 hxCosmic⟩
      · apply mem_cosmicSet.2
        right
        exact ⟨u, Or.inl <|
          cosmicDirection_mem_outer_ordinaryCosmicSequence_iff.1 <|
            mem_outerSetLimit_iff_exists_subsequence.2
              ⟨φ ∘ g, fun n ↦ cosmicEmbed (x n),
                hφ.comp hg,
                fun n ↦ (cosmicEmbed_mem_cosmicSet_iff).2 (hxC n), hxCosmic⟩, rfl⟩
    · rw [not_frequently] at hord
      have heventDir : ∀ᶠ n in atTop, z n ∈ cosmicDirections (K (φ n)) :=
        hord.mono fun n hn ↦ (hzUnion n).resolve_left hn
      rcases extraction_of_eventually_atTop heventDir with ⟨g, hg, hgDir⟩
      choose u huK huz using hgDir
      have huCosmic : Tendsto (fun n ↦ cosmicDirection (u n)) atTop (nhds p) := by
        apply (hzp.comp hg.tendsto_atTop).congr'
        exact Eventually.of_forall fun n ↦ (huz n).symm
      rcases cosmicEmbed_or_cosmicDirection p with ⟨xbar, rfl⟩ | ⟨v, rfl⟩
      · have huNorm := (tendsto_subtype_rng.mp huCosmic).norm
        have hconst : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop
            (nhds ‖((cosmicEmbed xbar : CosmicSpace E) : E)‖) := by
          simpa only [coe_cosmicDirection,
            mem_sphere_zero_iff_norm.mp (u _).property] using huNorm
        have heq := tendsto_nhds_unique hconst tendsto_const_nhds
        exfalso
        exact (norm_cosmicEmbed_lt_one xbar).ne heq
      · apply mem_cosmicSet.2
        right
        refine ⟨v, Or.inr ?_, rfl⟩
        exact mem_outerSetLimit_iff_exists_subsequence.2
          ⟨φ ∘ g, fun n ↦ (u n : E),
            hφ.comp hg, huK, by
              simpa only [coe_cosmicDirection] using tendsto_subtype_rng.mp huCosmic⟩
  · intro hp
    rw [mem_cosmicSet] at hp
    rcases hp with ⟨x, hx, rfl⟩ | ⟨u, hu, rfl⟩
    · rcases mem_outerSetLimit_iff_exists_subsequence.1 hx with
        ⟨φ, y, hφ, hyC, hyx⟩
      exact mem_outerSetLimit_iff_exists_subsequence.2
        ⟨φ, fun n ↦ cosmicEmbed (y n), hφ,
          fun n ↦ (cosmicEmbed_mem_cosmicSet_iff).2 (hyC n),
          tendsto_cosmicEmbed_iff.2 hyx⟩
    · rcases hu with hu | hu
      · exact outerSetLimit_mono
          (C := ordinaryCosmicSequence C)
          (D := fun n ↦ cosmicSet (C n) (K n))
          (fun n ↦ cosmicSet_mono Subset.rfl (singleton_subset_iff.mpr (hK n).1))
          (cosmicDirection_mem_outer_ordinaryCosmicSequence_iff.2 hu)
      · exact outerSetLimit_mono
          (C := fun n ↦ cosmicDirections (K n))
          (D := fun n ↦ cosmicSet (C n) (K n))
          (fun n ↦ subset_union_right)
          (cosmicDirection_outer_of_mem_outer_cones hK hu)

/-- Directional outer limits turn union with a cone sequence into the union
of the two corresponding outer limits. -/
theorem horizonOuterSetLimit_union_cones
    (C K : ℕ → Set E) (hK : ∀ n, IsCone (K n)) :
    horizonOuterSetLimit (fun n ↦ C n ∪ K n) =
      horizonOuterSetLimit C ∪ outerSetLimit K := by
  apply Set.Subset.antisymm
  · intro w hw
    rcases hw with rfl | ⟨u, huOuter, r, hr, rfl⟩
    · exact Or.inl (isCone_horizonOuterSetLimit C).1
    · rcases mem_outerSetLimit_iff_exists_subsequence.1 huOuter with
        ⟨φ, z, hφ, hz, hzu⟩
      have hz' : ∀ n, ∃ x ∈ C (φ n) ∪ K (φ n), cosmicEmbed x = z n := by
        intro n
        simpa only [ordinaryCosmicSequence, cosmicSet, cosmicDirections_zero,
          union_empty, mem_image] using hz n
      choose x hxU hxz using hz'
      have hxCosmic : Tendsto (fun n ↦ cosmicEmbed (x n)) atTop
          (nhds (cosmicDirection u)) := by
        apply hzu.congr'
        exact Eventually.of_forall fun n ↦ (hxz n).symm
      by_cases hCfreq : ∃ᶠ n in atTop, x n ∈ C (φ n)
      · rcases extraction_of_frequently_atTop hCfreq with ⟨ψ, hψ, hψC⟩
        apply Or.inl
        apply (isCone_horizonOuterSetLimit C).smul_mem _ hr.le
        apply cosmicDirection_mem_outer_ordinaryCosmicSequence_iff.1
        exact mem_outerSetLimit_iff_exists_subsequence.2
          ⟨φ ∘ ψ, fun n ↦ cosmicEmbed (x (ψ n)), hφ.comp hψ,
            fun n ↦ (cosmicEmbed_mem_cosmicSet_iff).2 (hψC n),
            hxCosmic.comp hψ.tendsto_atTop⟩
      · rw [not_frequently] at hCfreq
        have hKevent : ∀ᶠ n in atTop, x n ∈ K (φ n) :=
          hCfreq.mono fun n hn ↦ (hxU n).resolve_left hn
        rcases extraction_of_eventually_atTop hKevent with ⟨ψ, hψ, hψK⟩
        rcases exists_scaling_of_tendsto_cosmicDirection
            (hxCosmic.comp hψ.tendsto_atTop) with
          ⟨scale, hscalePos, _, hscaled⟩
        apply Or.inr
        apply (isCone_outerSetLimit K hK).smul_mem _ hr.le
        exact mem_outerSetLimit_iff_exists_subsequence.2
          ⟨φ ∘ ψ, fun n ↦ scale n • x (ψ n), hφ.comp hψ,
            fun n ↦ (hK (φ (ψ n))).2 (hψK n) (hscalePos n), hscaled⟩
  · intro w hw
    rcases hw with hw | hw
    · exact cosmicDirectionCone_mono
        (outerSetLimit_mono fun n ↦ cosmicSet_mono
          (subset_union_left : C n ⊆ C n ∪ K n) Subset.rfl) hw
    · by_cases hw0 : w = 0
      · simpa [hw0] using (isCone_horizonOuterSetLimit (fun n ↦ C n ∪ K n)).1
      · let u : CosmicBoundary E := cosmicDirectionOf w hw0
        have huOuter : (u : E) ∈ outerSetLimit K := by
          change NormedSpace.normalize w ∈ outerSetLimit K
          exact (isCone_outerSetLimit K hK).smul_mem hw
            (inv_nonneg.mpr (norm_nonneg w))
        have huUnion : (u : E) ∈
            horizonOuterSetLimit (fun n ↦ C n ∪ K n) := by
          have huDir := cosmicDirection_outer_of_mem_outer_cones hK huOuter
          have hterm : ∀ n, cosmicDirections (K n) ⊆
              closure (ordinaryCosmicSequence (fun n ↦ C n ∪ K n) n) := by
            intro n p hp
            rcases mem_cosmicDirections.1 hp with ⟨v, hvK, rfl⟩
            apply cosmicDirection_mem_closure_cosmicSet_of_mem_horizonCone
            apply mem_horizonCone_of_forall_smul_add_mem (x := 0)
            intro τ hτ
            simpa using Or.inr ((hK n).smul_mem hvK hτ)
          have huClosureOuter := outerSetLimit_mono hterm huDir
          rw [outerSetLimit_closure] at huClosureOuter
          exact cosmicDirection_mem_outer_ordinaryCosmicSequence_iff.1 huClosureOuter
        have hscaled :=
          (isCone_horizonOuterSetLimit (fun n ↦ C n ∪ K n)).smul_mem
            huUnion (norm_nonneg w)
        simpa only [u, coe_cosmicDirectionOf,
          NormedSpace.norm_smul_normalize w] using hscaled

/-- **Exercise 4.20 (cosmic inner limit).** -/
theorem innerSetLimit_cosmicSet
    (C K : ℕ → Set E) (hK : ∀ n, IsCone (K n)) :
    innerSetLimit (fun n ↦ cosmicSet (C n) (K n)) =
      cosmicSet (innerSetLimit C)
        (horizonInnerSetLimit (fun n ↦ C n ∪ K n)) := by
  ext p
  rcases cosmicEmbed_or_cosmicDirection p with ⟨x, rfl⟩ | ⟨u, rfl⟩
  · rw [cosmicEmbed_mem_cosmicSet_iff,
      mem_innerSetLimit_iff_forall_subsequence_outerSetLimit,
      mem_innerSetLimit_iff_forall_subsequence_outerSetLimit]
    constructor <;> intro h φ hφ
    · have hp := h φ hφ
      have hp' : cosmicEmbed x ∈
          outerSetLimit (fun n ↦ cosmicSet ((C ∘ φ) n) ((K ∘ φ) n)) := by
        simpa only [Function.comp_def] using hp
      rw [outerSetLimit_cosmicSet (C ∘ φ) (K ∘ φ) (fun n ↦ hK (φ n)),
        cosmicEmbed_mem_cosmicSet_iff] at hp'
      exact hp'
    · have hp : cosmicEmbed x ∈
          outerSetLimit (fun n ↦ cosmicSet ((C ∘ φ) n) ((K ∘ φ) n)) := by
        rw [outerSetLimit_cosmicSet (C ∘ φ) (K ∘ φ) (fun n ↦ hK (φ n)),
          cosmicEmbed_mem_cosmicSet_iff]
        exact h φ hφ
      simpa only [Function.comp_def] using hp
  · constructor
    · intro hleft
      apply mem_cosmicSet.2
      right
      refine ⟨u, ?_, rfl⟩
      apply cosmicDirection_mem_inner_ordinaryCosmicSequence_iff.1
      rw [mem_innerSetLimit_iff_forall_subsequence_outerSetLimit]
      intro φ hφ
      have hpMixed : cosmicDirection u ∈
          outerSetLimit ((fun n ↦ cosmicSet (C n) (K n)) ∘ φ) :=
        (mem_innerSetLimit_iff_forall_subsequence_outerSetLimit.1
          hleft) φ hφ
      have hpMixed' : cosmicDirection u ∈
          outerSetLimit (fun n ↦ cosmicSet ((C ∘ φ) n) ((K ∘ φ) n)) := by
        simpa only [Function.comp_def] using hpMixed
      rw [outerSetLimit_cosmicSet (C ∘ φ) (K ∘ φ) (fun n ↦ hK (φ n)),
        mem_cosmicSet] at hpMixed'
      have hu : (u : E) ∈ horizonOuterSetLimit (C ∘ φ) ∪ outerSetLimit (K ∘ φ) := by
        rcases hpMixed' with ⟨x, _, hxu⟩ | ⟨v, hv, hvu⟩
        · exact (cosmicEmbed_ne_cosmicDirection x u hxu).elim
        · have hvu' : v = u := injective_cosmicDirection hvu
          simpa [hvu'] using hv
      rw [← horizonOuterSetLimit_union_cones (C ∘ φ) (K ∘ φ)
        (fun n ↦ hK (φ n))] at hu
      simpa only [Function.comp_def] using
        cosmicDirection_mem_outer_ordinaryCosmicSequence_iff.2 hu
    · intro hright
      rw [mem_innerSetLimit_iff_forall_subsequence_outerSetLimit]
      intro φ hφ
      rw [mem_cosmicSet] at hright
      rcases hright with ⟨x, _, hxu⟩ | ⟨v, hv, hvu⟩
      · exact (cosmicEmbed_ne_cosmicDirection x u hxu).elim
      · have hvu' : v = u := injective_cosmicDirection hvu
        have huInner : (u : E) ∈ horizonInnerSetLimit (fun n ↦ C n ∪ K n) := by
          simpa [hvu'] using hv
        have huSubOuter : (u : E) ∈
            horizonOuterSetLimit ((fun n ↦ C n ∪ K n) ∘ φ) :=
          (mem_innerSetLimit_iff_forall_subsequence_outerSetLimit.1
            (cosmicDirection_mem_inner_ordinaryCosmicSequence_iff.2 huInner)) φ hφ
          |> cosmicDirection_mem_outer_ordinaryCosmicSequence_iff.1
        have huSubOuter' : (u : E) ∈
            horizonOuterSetLimit (fun n ↦ (C ∘ φ) n ∪ (K ∘ φ) n) := by
          simpa only [Function.comp_def] using huSubOuter
        rw [horizonOuterSetLimit_union_cones (C ∘ φ) (K ∘ φ)
          (fun n ↦ hK (φ n))] at huSubOuter'
        have hp : cosmicDirection u ∈
            outerSetLimit (fun n ↦ cosmicSet ((C ∘ φ) n) ((K ∘ φ) n)) := by
          rw [outerSetLimit_cosmicSet (C ∘ φ) (K ∘ φ) (fun n ↦ hK (φ n))]
          apply mem_cosmicSet.2
          exact Or.inr ⟨u, huSubOuter', rfl⟩
        simpa only [Function.comp_def] using hp

/-- **Exercise 4.20 (cosmic convergence criterion).** -/
theorem pkConverges_cosmicSet_iff
    {Cseq Kseq : ℕ → Set E} {C K : Set E}
    (hKseq : ∀ n, IsCone (Kseq n)) (hK : IsCone K) :
    PKConverges (fun n ↦ cosmicSet (Cseq n) (Kseq n)) (cosmicSet C K) ↔
      PKConverges Cseq C ∧
        horizonOuterSetLimit Cseq ∪ outerSetLimit Kseq ⊆ K ∧
        K ⊆ horizonInnerSetLimit (fun n ↦ Cseq n ∪ Kseq n) := by
  have hOuterCone : IsCone
      (horizonOuterSetLimit Cseq ∪ outerSetLimit Kseq) := by
    rw [← horizonOuterSetLimit_union_cones Cseq Kseq hKseq]
    exact isCone_horizonOuterSetLimit _
  have hInnerCone : IsCone
      (horizonInnerSetLimit (fun n ↦ Cseq n ∪ Kseq n)) :=
    isCone_horizonInnerSetLimit _
  constructor
  · intro h
    have hinner := h.inner_eq
    rw [innerSetLimit_cosmicSet Cseq Kseq hKseq] at hinner
    have hinnerParts := (cosmicSet_injective hInnerCone hK).1 hinner
    have houter := h.outer_eq
    rw [outerSetLimit_cosmicSet Cseq Kseq hKseq] at houter
    have houterParts := (cosmicSet_injective hOuterCone hK).1 houter
    exact ⟨⟨hinnerParts.1, houterParts.1⟩,
      houterParts.2.le, hinnerParts.2.ge⟩
  · rintro ⟨hordinary, hOuterK, hKInner⟩
    have hInnerOuter :
        horizonInnerSetLimit (fun n ↦ Cseq n ∪ Kseq n) ⊆
          horizonOuterSetLimit Cseq ∪ outerSetLimit Kseq := by
      rw [← horizonOuterSetLimit_union_cones Cseq Kseq hKseq]
      exact horizonInnerSetLimit_subset_horizonOuterSetLimit _
    have houterEq : horizonOuterSetLimit Cseq ∪ outerSetLimit Kseq = K :=
      Set.Subset.antisymm hOuterK (hKInner.trans hInnerOuter)
    have hinnerEq : horizonInnerSetLimit (fun n ↦ Cseq n ∪ Kseq n) = K :=
      Set.Subset.antisymm (hInnerOuter.trans hOuterK) hKInner
    constructor
    · rw [innerSetLimit_cosmicSet Cseq Kseq hKseq,
        hordinary.inner_eq, hinnerEq]
    · rw [outerSetLimit_cosmicSet Cseq Kseq hKseq,
        hordinary.outer_eq, houterEq]

end MixedOuterLimit

end RW
