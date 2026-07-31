/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3: Closure of Closed-Ball Cosmic Sets

This file transports Exercise 3.4 from the ray-space backend to the actual
closed-ball compactification `CosmicSpace`.
-/

import RockafellarWets.Chapter3.CosmicSets

open Set Bornology Filter Topology

namespace RW

section CosmicSetClosure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem cosmicEmbed_mem_closure_cosmicSet_of_mem_closure
    {C K : Set E} {x : E} (hx : x ∈ closure C) :
    cosmicEmbed x ∈ closure (cosmicSet C K) := by
  rcases mem_closure_iff_seq_limit.mp hx with ⟨v, hvC, hv⟩
  refine mem_closure_iff_seq_limit.mpr ⟨fun n ↦ cosmicEmbed (v n), ?_, ?_⟩
  · intro n
    exact (cosmicEmbed_mem_cosmicSet_iff).2 (hvC n)
  · exact (tendsto_cosmicEmbed_iff).2 hv

theorem cosmicDirection_mem_closure_cosmicSet_of_mem_horizonCone
    {C K : Set E} {u : CosmicBoundary E}
    (hu : (u : E) ∈ horizonCone C) :
    cosmicDirection u ∈ closure (cosmicSet C K) := by
  have hu0 : (u : E) ≠ 0 := by
    intro h
    have hunorm : ‖(u : E)‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
    simp [h] at hunorm
  have huasy : (u : E) ∈ asymptoticCone ℝ C := by
    simpa [horizonCone, hu0] using hu
  rcases exists_seq_pos_smul_of_mem_asymptoticCone (C := C) huasy with
    ⟨c, v, hc, hv, hcpos, hmem⟩
  refine mem_closure_iff_seq_limit.mpr ⟨fun n ↦ cosmicEmbed (c n • v n), ?_, ?_⟩
  · intro n
    exact (cosmicEmbed_mem_cosmicSet_iff).2 (hmem n)
  · apply tendsto_cosmicDirection_of_scaling (scale := fun n ↦ (c n)⁻¹)
    · intro n
      exact inv_pos.mpr (hcpos n)
    · simpa using hc.inv_tendsto_atTop
    · convert hv using 1
      funext n
      rw [smul_smul, inv_mul_cancel₀ (hcpos n).ne', one_smul]

omit [FiniteDimensional ℝ E] in
theorem cosmicDirection_mem_closure_cosmicSet_of_mem_closure_cone
    {C K : Set E} (hK : IsCone K) {u : CosmicBoundary E}
    (hu : (u : E) ∈ closure K) :
    cosmicDirection u ∈ closure (cosmicSet C K) := by
  rcases mem_closure_iff_seq_limit.mp hu with ⟨v, hvK, hv⟩
  have hu0 : (u : E) ≠ 0 := by
    intro h
    have hunorm : ‖(u : E)‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
    simp [h] at hunorm
  have hev : ∀ᶠ n in atTop, v n ≠ 0 := by
    have hmem : {0}ᶜ ∈ nhds (u : E) := isOpen_compl_singleton.mem_nhds hu0
    exact hv.eventually hmem
  obtain ⟨φ, hφ, hne⟩ := extraction_of_eventually_atTop hev
  let d : ℕ → CosmicBoundary E := fun n ↦ cosmicDirectionOf (v (φ n)) (hne n)
  have hvsub : Tendsto (fun n ↦ v (φ n)) atTop (nhds (u : E)) :=
    hv.comp hφ.tendsto_atTop
  have hnorm : Tendsto (fun n ↦ ‖v (φ n)‖) atTop (nhds (1 : ℝ)) := by
    simpa [mem_sphere_zero_iff_norm.mp u.property] using hvsub.norm
  have hinv : Tendsto (fun n ↦ ‖v (φ n)‖⁻¹) atTop (nhds (1 : ℝ)) := by
    simpa using hnorm.inv₀ one_ne_zero
  have hnormalized :
      Tendsto (fun n ↦ NormedSpace.normalize (v (φ n))) atTop (nhds (u : E)) := by
    simpa only [NormedSpace.normalize, one_smul] using hinv.smul hvsub
  refine mem_closure_iff_seq_limit.mpr ⟨fun n ↦ cosmicDirection (d n), ?_, ?_⟩
  · intro n
    apply (mem_cosmicSet).2
    right
    refine ⟨d n, ?_, rfl⟩
    change NormedSpace.normalize (v (φ n)) ∈ K
    exact hK.smul_mem (hvK (φ n)) (inv_nonneg.mpr (norm_nonneg _))
  · apply tendsto_subtype_rng.mpr
    simpa only [d, coe_cosmicDirection, coe_cosmicDirectionOf] using hnormalized

omit [FiniteDimensional ℝ E] in
private theorem mem_closure_cosmicSet_imp_mem_closed_form
    {C K : Set E} {p : CosmicSpace E}
    (hp : p ∈ closure (cosmicSet C K)) :
    p ∈ cosmicSet (closure C) (horizonCone C ∪ closure K) := by
  rcases mem_closure_iff_seq_limit.mp hp with ⟨z, hz, hzp⟩
  have hzUnion : ∀ n, z n ∈ cosmicEmbed '' C ∪ cosmicDirections K := by
    simpa only [cosmicSet] using hz
  rcases Nat.exists_subseq_of_forall_mem_union z hzUnion with
    ⟨g, hgOrd | hgDir⟩
  · choose x hxC hxz using hgOrd
    have hzsub : Tendsto (fun n ↦ z (g n)) atTop (nhds p) :=
      hzp.comp (OrderEmbedding.strictMono g).tendsto_atTop
    have hxcosmic : Tendsto (fun n ↦ cosmicEmbed (x n)) atTop (nhds p) := by
      apply hzsub.congr'
      exact Eventually.of_forall fun n ↦ (hxz n).symm
    rcases cosmicEmbed_or_cosmicDirection p with ⟨y, rfl⟩ | ⟨u, rfl⟩
    · have hxy : Tendsto x atTop (nhds y) := (tendsto_cosmicEmbed_iff).1 hxcosmic
      have hy : y ∈ closure C := mem_closure_iff_seq_limit.mpr ⟨x, hxC, hxy⟩
      exact (cosmicEmbed_mem_cosmicSet_iff).2 hy
    · rcases exists_scaling_of_tendsto_cosmicDirection hxcosmic with
        ⟨scale, hscalePos, hscale, hscaled⟩
      have hscaleWithin : Tendsto scale atTop (nhdsWithin (0 : ℝ) (Set.Ioi 0)) :=
        tendsto_nhdsWithin_iff.mpr ⟨hscale, Eventually.of_forall hscalePos⟩
      have hinv : Tendsto (fun n ↦ (scale n)⁻¹) atTop atTop :=
        hscaleWithin.inv_tendsto_nhdsGT_zero
      have hmem : ∀ n, (scale n)⁻¹ • (scale n • x n) ∈ C := by
        intro n
        simpa [smul_smul, inv_mul_cancel₀ (hscalePos n).ne'] using hxC n
      have huasy : (u : E) ∈ asymptoticCone ℝ C :=
        mem_asymptoticCone_of_seq_smul hinv hscaled hmem
      apply (mem_cosmicSet).2
      right
      exact ⟨u, Or.inl (Set.mem_insert_of_mem 0 huasy), rfl⟩
  · choose u huK huz using hgDir
    have hzsub : Tendsto (fun n ↦ z (g n)) atTop (nhds p) :=
      hzp.comp (OrderEmbedding.strictMono g).tendsto_atTop
    have hucosmic : Tendsto (fun n ↦ cosmicDirection (u n)) atTop (nhds p) := by
      apply hzsub.congr'
      exact Eventually.of_forall fun n ↦ (huz n).symm
    rcases cosmicEmbed_or_cosmicDirection p with ⟨y, rfl⟩ | ⟨v, rfl⟩
    · have huUnderlying :
          Tendsto (fun n ↦ (u n : E)) atTop
            (nhds (((cosmicEmbed y : CosmicSpace E) : E))) := by
        simpa only [coe_cosmicDirection] using tendsto_subtype_rng.mp hucosmic
      have hnormT := huUnderlying.norm
      have hlimOne :
          Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop
            (nhds ‖((cosmicEmbed y : CosmicSpace E) : E)‖) := by
        simpa only [mem_sphere_zero_iff_norm.mp (u _).property] using hnormT
      have hEq : ‖((cosmicEmbed y : CosmicSpace E) : E)‖ = 1 :=
        tendsto_nhds_unique hlimOne tendsto_const_nhds
      exfalso
      exact (norm_cosmicEmbed_lt_one y).ne hEq
    · have huUnderlying :
          Tendsto (fun n ↦ (u n : E)) atTop (nhds (v : E)) := by
        simpa only [coe_cosmicDirection] using tendsto_subtype_rng.mp hucosmic
      have hvK : (v : E) ∈ closure K :=
        mem_closure_iff_seq_limit.mpr ⟨fun n ↦ (u n : E), huK, huUnderlying⟩
      apply (mem_cosmicSet).2
      right
      exact ⟨v, Or.inr hvK, rfl⟩

/-- **Exercise 3.4 (cosmic closure), exact closed-ball form.** -/
theorem closure_cosmicSet {C K : Set E} (hK : IsCone K) :
    closure (cosmicSet C K) =
      cosmicSet (closure C) (horizonCone C ∪ closure K) := by
  apply Set.Subset.antisymm
  · exact fun _ hp ↦ mem_closure_cosmicSet_imp_mem_closed_form hp
  · intro p hp
    rw [mem_cosmicSet] at hp
    rcases hp with ⟨x, hx, rfl⟩ | ⟨u, hu, rfl⟩
    · exact cosmicEmbed_mem_closure_cosmicSet_of_mem_closure hx
    · rcases hu with hHor | hKcl
      · exact cosmicDirection_mem_closure_cosmicSet_of_mem_horizonCone hHor
      · exact cosmicDirection_mem_closure_cosmicSet_of_mem_closure_cone hK hKcl

/-- **Exercise 3.4 (cosmic closedness), exact closed-ball form.** -/
theorem isClosed_cosmicSet_iff {C K : Set E} (hK : IsCone K) :
    IsClosed (cosmicSet C K) ↔
      IsClosed C ∧ IsClosed K ∧ horizonCone C ⊆ K := by
  have hClosureCone : IsCone (closure K) := by
    refine ⟨subset_closure hK.1, ?_⟩
    intro x hx c hc
    exact map_mem_closure (continuous_const.smul continuous_id) hx fun y hy ↦
      hK.2 hy hc
  have hUnionCone : IsCone (horizonCone C ∪ closure K) := by
    refine ⟨Or.inl (zero_mem_horizonCone C), ?_⟩
    intro x hx c hc
    rcases hx with hx | hx
    · exact Or.inl ((isCone_horizonCone C).2 hx hc)
    · exact Or.inr (hClosureCone.2 hx hc)
  rw [← closure_eq_iff_isClosed, closure_cosmicSet hK]
  rw [cosmicSet_injective hUnionCone hK]
  constructor
  · rintro ⟨hC, hKall⟩
    have hCclosed : IsClosed C := by
      rwa [← closure_eq_iff_isClosed]
    have hclK : closure K = K := by
      apply Set.Subset.antisymm
      · intro x hx
        rw [← hKall]
        exact Or.inr hx
      · exact subset_closure
    refine ⟨hCclosed, ?_, ?_⟩
    · rwa [← closure_eq_iff_isClosed]
    · intro x hx
      rw [← hKall]
      exact Or.inl hx
  · rintro ⟨hC, hKclosed, hHor⟩
    refine ⟨hC.closure_eq, ?_⟩
    rw [hKclosed.closure_eq]
    exact Set.union_eq_right.mpr hHor

omit [FiniteDimensional ℝ E] in
@[simp]
theorem closure_cosmicSet_empty_zero :
    closure (cosmicSet (∅ : Set E) ({0} : Set E)) = ∅ := by
  simp

/-- Regression: a bounded ordinary set acquires no direction points when
closed cosmically. -/
theorem closure_cosmicSet_zero_of_isBounded {C : Set E} (hC : IsBounded C) :
    closure (cosmicSet C ({0} : Set E)) =
      cosmicSet (closure C) ({0} : Set E) := by
  have hzero : IsCone ({0} : Set E) := ⟨Set.mem_singleton 0, by simp⟩
  rw [closure_cosmicSet hzero,
    (isBounded_iff_horizonCone_eq_singleton_zero.mp hC)]
  simp

/-- Regression: the whole ordinary space with no directions closes up to the
whole cosmic compactification. -/
theorem closure_cosmicSet_univ_zero :
    closure (cosmicSet (Set.univ : Set E) ({0} : Set E)) = Set.univ := by
  have hzero : IsCone ({0} : Set E) := ⟨Set.mem_singleton 0, by simp⟩
  rw [closure_cosmicSet hzero]
  simp [horizonCone, asymptoticCone_univ]

/-- Regression: when every direction is already present, closure only closes
the ordinary part. -/
theorem closure_cosmicSet_fullCone (C : Set E) :
    closure (cosmicSet C (Set.univ : Set E)) =
      cosmicSet (closure C) (Set.univ : Set E) := by
  have hfull : IsCone (Set.univ : Set E) := ⟨Set.mem_univ 0, by simp⟩
  rw [closure_cosmicSet hfull]
  simp

end CosmicSetClosure

end RW
