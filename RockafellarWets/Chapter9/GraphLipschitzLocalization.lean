/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lipschitz localization from moving-base tangent cones
-/

import RockafellarWets.Chapter9.StrictGraphicalDerivatives

open Filter Metric Set Topology
open scoped NNReal

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- A uniform Lipschitz estimate between graph points near a base point. -/
def LocalGraphLipschitzBound (G : Set (E × F)) (p₀ : E × F) (k : ℝ≥0) : Prop :=
  ∃ δ > 0, ∀ p ∈ G ∩ ball p₀ δ, ∀ q ∈ G ∩ ball p₀ δ,
    dist p.2 q.2 ≤ k * dist p.1 q.1

/-- A local graph estimate passes to every moving-base tangent. -/
theorem LocalGraphLipschitzBound.norm_le {G : Set (E × F)} {p₀ : E × F} {k : ℝ≥0}
    (h : LocalGraphLipschitzBound G p₀ k) {w : E} {z : F}
    (hz : (w,z) ∈ strictTangentCone G p₀) : ‖z‖ ≤ k * ‖w‖ := by
  obtain ⟨δ,hδ,hbound⟩ := h
  obtain ⟨a,b,τ,ha,hb,hat,hτ,hτt,hq⟩ := mem_strictTangentCone_iff_exists_sequences.mp hz
  have hbt := tendsto_endpoint_of_scaled_secants hat hτ hτt hq
  have he : ∀ᶠ n in atTop,
      ‖(τ n)⁻¹ • ((b n).2-(a n).2)‖ ≤ k * ‖(τ n)⁻¹ • ((b n).1-(a n).1)‖ := by
    filter_upwards [hat (ball_mem_nhds p₀ hδ),hbt (ball_mem_nhds p₀ hδ)] with n han hbn
    have hdist := hbound (b n) ⟨hb n,hbn⟩ (a n) ⟨ha n,han⟩
    simp only [dist_eq_norm] at hdist
    rw [norm_smul_of_nonneg (inv_pos.mpr (hτ n)).le,norm_smul_of_nonneg (inv_pos.mpr (hτ n)).le]
    calc
      _ ≤ (τ n)⁻¹ * (k * ‖(b n).1-(a n).1‖) := mul_le_mul_of_nonneg_left hdist (inv_pos.mpr (hτ n)).le
      _ = _ := by ring
  exact le_of_tendsto_of_tendsto hq.snd_nhds.norm (hq.fst_nhds.norm.const_mul (k:ℝ)) he

/-- The compactness argument behind **Theorem 9.54**. A graph with no
nonzero vertical moving-base tangent satisfies a local Lipschitz estimate. -/
theorem exists_localGraphLipschitzBound_of_vertical_zero {G : Set (E × F)} {p₀ : E × F}
    (hz : ∀ z : F, ((0:E),z) ∈ strictTangentCone G p₀ → z = 0) :
    ∃ k : ℝ≥0, LocalGraphLipschitzBound G p₀ k := by
  classical
  by_contra hno
  have hpick (n : ℕ) : ∃ p ∈ G ∩ ball p₀ (1/((n:ℝ)+1)),
      ∃ q ∈ G ∩ ball p₀ (1/((n:ℝ)+1)),
        ((n:ℝ)+1) * dist p.1 q.1 < dist p.2 q.2 := by
    have hn : (0:ℝ) < 1/((n:ℝ)+1) := by positivity
    have h : ¬ ∀ p ∈ G ∩ ball p₀ (1/((n:ℝ)+1)),
        ∀ q ∈ G ∩ ball p₀ (1/((n:ℝ)+1)), dist p.2 q.2 ≤ ((n:ℝ≥0)+1) * dist p.1 q.1 :=
      fun hbound ↦ hno ⟨(n:ℝ≥0)+1,1/((n:ℝ)+1),hn,hbound⟩
    push_neg at h
    simpa only [NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one] using h
  choose p hp q hq hbad using hpick
  have hpt : Tendsto p atTop (𝓝 p₀) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ (mem_ball.mp (hp n).2).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hqt : Tendsto q atTop (𝓝 p₀) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ (mem_ball.mp (hq n).2).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  let τ (n : ℕ) := ‖(q n).2-(p n).2‖
  have hτ (n : ℕ) : 0 < τ n := by
    have hd : 0 < dist (p n).2 (q n).2 := lt_of_le_of_lt
      (mul_nonneg (show 0 ≤ (n:ℝ)+1 by positivity) dist_nonneg) (hbad n)
    simpa only [τ,dist_eq_norm,norm_sub_rev] using hd
  have hτt : Tendsto τ atTop (𝓝 0) := by
    simpa only [sub_self,norm_zero] using (hqt.snd_nhds.sub hpt.snd_nhds).norm
  let v (n : ℕ) := (τ n)⁻¹ • ((q n).1-(p n).1)
  let z (n : ℕ) := (τ n)⁻¹ • ((q n).2-(p n).2)
  have hvbound (n : ℕ) : ‖v n‖ ≤ 1/((n:ℝ)+1) := by
    have hb := hbad n
    rw [dist_comm (p n).1,dist_comm (p n).2,dist_eq_norm,dist_eq_norm] at hb
    change ((n:ℝ)+1) * ‖(q n).1-(p n).1‖ < τ n at hb
    dsimp only [v]
    rw [norm_smul_of_nonneg (inv_pos.mpr (hτ n)).le,← div_eq_inv_mul]
    exact ((div_lt_div_iff₀ (hτ n) (by positivity)).mpr (by nlinarith only [hb])).le
  have hvt : Tendsto v atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun _ ↦ norm_nonneg _) hvbound tendsto_one_div_add_atTop_nhds_zero_nat
  have hznorm (n : ℕ) : ‖z n‖ = 1 := by
    dsimp only [z]
    rw [norm_smul_of_nonneg (inv_pos.mpr (hτ n)).le]
    exact inv_mul_cancel₀ (hτ n).ne'
  obtain ⟨z₀,hz₀,φ,hφ,hzt⟩ := (isCompact_sphere (0:F) 1).tendsto_subseq
    (fun n ↦ mem_sphere_zero_iff_norm.mpr (hznorm n))
  have hmem : ((0:E),z₀) ∈ strictTangentCone G p₀ := by
    apply mem_strictTangentCone_iff_exists_sequences.mpr
    refine ⟨p ∘ φ,q ∘ φ,τ ∘ φ,fun n ↦ (hp _).1,fun n ↦ (hq _).1,
      hpt.comp hφ.tendsto_atTop,fun n ↦ hτ _,hτt.comp hφ.tendsto_atTop,?_⟩
    exact (hvt.comp hφ.tendsto_atTop).prodMk_nhds hzt
  have hzero := hz z₀ hmem
  norm_num [hzero,mem_sphere_zero_iff_norm] at hz₀

/-- The vertical-kernel form of the strict derivative criterion. -/
theorem strictGraphicalDerivative_zero_iff_localGraphLipschitz {S : E → Set F} {x : E} {u : F}
    (hu : u ∈ S x) : strictGraphicalDerivative S x u 0 = {0} ↔
      ∃ k : ℝ≥0, LocalGraphLipschitzBound (svGraph S) (x,u) k := by
  constructor
  · intro h
    apply exists_localGraphLipschitzBound_of_vertical_zero
    intro z hz
    exact mem_singleton_iff.mp (h ▸ hz)
  · rintro ⟨k,hk⟩
    apply Subset.antisymm
    · intro z hz
      apply mem_singleton_iff.mpr
      have h := hk.norm_le hz
      simpa only [norm_zero,mul_zero,norm_le_zero_iff] using h
    · apply singleton_subset_iff.mpr
      exact (svPositivelyHomogeneous_strictGraphicalDerivative hu).1

/-- A bound on all strict tangents gives every strictly larger local graph
Lipschitz constant. This yields the sharp infimum form of9.54. -/
theorem localGraphLipschitzBound_of_strictTangent_bound [FiniteDimensional ℝ E]
    {G : Set (E × F)} {p₀ : E × F} {k l : ℝ≥0} (hkl : k < l)
    (hcone : ∀ w z, (w,z) ∈ strictTangentCone G p₀ → ‖z‖ ≤ k * ‖w‖) :
    LocalGraphLipschitzBound G p₀ l := by
  classical
  obtain ⟨K,δ,hδ,hKbound⟩ := exists_localGraphLipschitzBound_of_vertical_zero
    (fun z hz ↦ norm_le_zero_iff.mp (by simpa only [norm_zero,mul_zero] using hcone 0 z hz))
  by_contra hno
  have hpick (n : ℕ) : ∃ p ∈ G ∩ ball p₀ (min δ (1/((n:ℝ)+1))),
      ∃ q ∈ G ∩ ball p₀ (min δ (1/((n:ℝ)+1))),
        l * dist p.1 q.1 < dist p.2 q.2 := by
    have hr : 0 < min δ (1/((n:ℝ)+1)) := lt_min hδ (by positivity)
    have h : ¬ ∀ p ∈ G ∩ ball p₀ (min δ (1/((n:ℝ)+1))),
        ∀ q ∈ G ∩ ball p₀ (min δ (1/((n:ℝ)+1))), dist p.2 q.2 ≤ l * dist p.1 q.1 :=
      fun hbound ↦ hno ⟨_,hr,hbound⟩
    push_neg at h
    exact h
  choose p hp q hq hbad using hpick
  have hK (n : ℕ) : ‖(q n).2-(p n).2‖ ≤ K * ‖(q n).1-(p n).1‖ := by
    simpa only [dist_eq_norm] using hKbound (q n) ⟨(hq n).1,ball_subset_ball (min_le_left _ _) (hq n).2⟩
      (p n) ⟨(hp n).1,ball_subset_ball (min_le_left _ _) (hp n).2⟩
  have hbad' (n : ℕ) : l * ‖(q n).1-(p n).1‖ < ‖(q n).2-(p n).2‖ := by
    simpa only [dist_eq_norm,norm_sub_rev] using hbad n
  have hpt : Tendsto p atTop (𝓝 p₀) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun _ ↦ dist_nonneg)
      (fun n ↦ (mem_ball.mp (hp n).2).le.trans (min_le_right _ _)) tendsto_one_div_add_atTop_nhds_zero_nat
  have hqt : Tendsto q atTop (𝓝 p₀) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun _ ↦ dist_nonneg)
      (fun n ↦ (mem_ball.mp (hq n).2).le.trans (min_le_right _ _)) tendsto_one_div_add_atTop_nhds_zero_nat
  let τ (n : ℕ) := ‖(q n).1-(p n).1‖
  have hτ (n : ℕ) : 0 < τ n := by
    have hb := hbad' n
    have hbK := hK n
    change 0 < ‖(q n).1-(p n).1‖
    by_contra! hz
    have he := le_antisymm hz (norm_nonneg _)
    simp only [he,mul_zero] at hb hbK
    exact (not_lt_of_ge hbK) hb
  have hτt : Tendsto τ atTop (𝓝 0) := by
    simpa only [sub_self,norm_zero] using (hqt.fst_nhds.sub hpt.fst_nhds).norm
  let v (n : ℕ) := (τ n)⁻¹ • ((q n).1-(p n).1)
  let z (n : ℕ) := (τ n)⁻¹ • ((q n).2-(p n).2)
  have hvnorm (n : ℕ) : ‖v n‖ = 1 := by
    dsimp only [v]
    rw [norm_smul_of_nonneg (inv_pos.mpr (hτ n)).le]
    exact inv_mul_cancel₀ (hτ n).ne'
  have hzbound (n : ℕ) : ‖z n‖ ≤ K := by
    dsimp only [z]
    rw [norm_smul_of_nonneg (inv_pos.mpr (hτ n)).le,← div_eq_inv_mul,div_le_iff₀ (hτ n)]
    exact hK n
  have hzlower (n : ℕ) : (l:ℝ) < ‖z n‖ := by
    dsimp only [z]
    rw [norm_smul_of_nonneg (inv_pos.mpr (hτ n)).le,← div_eq_inv_mul,lt_div_iff₀ (hτ n)]
    exact hbad' n
  have hcompactMem (n : ℕ) : (v n,z n) ∈ sphere (0:E) 1 ×ˢ closedBall (0:F) (K:ℝ) :=
    ⟨mem_sphere_zero_iff_norm.mpr (hvnorm n),mem_closedBall_zero_iff.mpr (hzbound n)⟩
  obtain ⟨⟨w₀,z₀⟩,hmem,φ,hφ,hlim⟩ :=
    ((isCompact_sphere (0:E) 1).prod (isCompact_closedBall (0:F) (K:ℝ))).tendsto_subseq
      hcompactMem
  have hstrict : (w₀,z₀) ∈ strictTangentCone G p₀ := by
    apply mem_strictTangentCone_iff_exists_sequences.mpr
    exact ⟨p ∘ φ,q ∘ φ,τ ∘ φ,fun n ↦ (hp _).1,fun n ↦ (hq _).1,
      hpt.comp hφ.tendsto_atTop,fun n ↦ hτ _,hτt.comp hφ.tendsto_atTop,hlim⟩
  have hlo : (l:ℝ) ≤ ‖z₀‖ := le_of_tendsto_of_tendsto tendsto_const_nhds hlim.snd_nhds.norm
    (.of_forall fun n ↦ (hzlower (φ n)).le)
  have hhi := hcone w₀ z₀ hstrict
  rw [mem_sphere_zero_iff_norm.mp hmem.1,mul_one] at hhi
  exact (not_le_of_gt (show (k:ℝ) < l from hkl)) (hlo.trans hhi)

end RW
