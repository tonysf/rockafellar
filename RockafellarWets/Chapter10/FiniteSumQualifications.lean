/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Sufficient qualifications for finite mapping sums
-/

import RockafellarWets.Chapter10.FiniteMappingSumLipschitz
import RockafellarWets.Chapter5.TotalContinuity
import RockafellarWets.Chapter5.ConvergingImages

open Bornology Filter Metric Set Topology

namespace RW

variable {X Y : Type*} [MetricSpace X] [NormedAddCommGroup Y]

/-- Failure of local boundedness produces escaping values above points
converging to the base point. -/
theorem exists_escaping_sequence_of_not_svLocallyBoundedAt {S : X → Set Y} {x : X}
    (h : ¬ SvLocallyBoundedAt S x) :
    ∃ (a : ℕ → X) (q : ℕ → Y), Tendsto a atTop (𝓝 x) ∧
      (∀ n, q n ∈ S (a n)) ∧ Tendsto (fun n ↦ ‖q n‖) atTop atTop := by
  have he (n : ℕ) : ∃ a ∈ ball x ((n:ℝ)+1)⁻¹, ∃ q ∈ S a, (n:ℝ) < ‖q‖ := by
    by_contra! hn
    apply h
    refine ⟨ball x ((n:ℝ)+1)⁻¹,ball_mem_nhds x (by positivity),?_⟩
    apply isBounded_closedBall.subset (t := closedBall (0:Y) n)
    intro q hq
    obtain ⟨a,ha,hq⟩ := mem_svImage.mp hq
    simpa only [mem_closedBall,dist_zero_right] using hn a ha q hq
  choose a ha q hq hnorm using he
  refine ⟨a,q,?_,hq,?_⟩
  · apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun n ↦ dist_nonneg) (fun n ↦ (ha n).le)
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  · exact tendsto_atTop_mono (fun n ↦ (hnorm n).le) tendsto_natCast_atTop_atTop

variable {ι E F : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {S : ι → E → Set F} {x : E} {b : F}

/-- The horizon sufficient condition in 10.41(a). -/
theorem finiteSumMappingAux_locallyBounded_of_horizon
    (hQ : ∀ z : ι → F, (∀ i, z i ∈ svHorizonOuterLimit (S i) x) →
      (∑ i, z i) = 0 → ∀ i, z i = 0) :
    SvLocallyBoundedAt (finiteSumMappingAux S) (x,b) := by
  by_contra hn
  obtain ⟨a,q,ha,hq,hnorm⟩ := exists_escaping_sequence_of_not_svLocallyBoundedAt hn
  obtain ⟨c,z,φ,hφ,hc,hsum,hct,hzt⟩ :=
    exists_normalized_multiplier_subsequence (fun _ ↦ 1) q (fun _ ↦ by norm_num)
  have hzero : Tendsto (fun n ↦ (1+‖q (φ n)‖)⁻¹) atTop (𝓝 (0:ℝ)) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left atTop (1:ℝ) (hnorm.comp hφ.tendsto_atTop))
  have hc0 : c = 0 := tendsto_nhds_unique (by simpa only [one_div] using hct) hzero
  have hzH (i : ι) : z i ∈ svHorizonOuterLimit (S i) x := by
    apply horizonOuterSetLimit_comp_subset ha.fst_nhds
    apply mem_horizonOuterSetLimit_of_seq_smul hφ (fun n ↦ (hq (φ n)).1 i)
      (fun n ↦ inv_pos.mpr (by positivity)) hzero
    exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι ↦ F) i).continuous.tendsto z).comp hzt
  have hsum0 : (∑ i, z i) = 0 := by
    have ht := ((l2PiSum (ι := ι) (E := F)).continuous.tendsto z).comp hzt
    have ht0 : Tendsto (fun n ↦ (1+‖q (φ n)‖)⁻¹ • (a (φ n)).2) atTop (𝓝 (0:F)) := by
      simpa only [zero_smul] using hzero.smul ((ha.comp hφ.tendsto_atTop).snd_nhds)
    have he : (fun n ↦ l2PiSum ((1+‖q (φ n)‖)⁻¹ • q (φ n))) =
        (fun n ↦ (1+‖q (φ n)‖)⁻¹ • (a (φ n)).2) := by
      funext n
      rw [map_smul,l2PiSum_apply,(hq (φ n)).2]
    simp only [Function.comp_def] at ht
    rw [he] at ht
    simpa only [l2PiSum_apply] using tendsto_nhds_unique ht ht0
  have hz0 : z = 0 := by
    apply WithLp.ofLp_injective
    exact funext (hQ (fun i ↦ z i) hzH hsum0)
  simp only [hc0,hz0,norm_zero,add_zero] at hsum
  norm_num at hsum

/-- All but at most one locally bounded summand suffices in 10.41(a). -/
theorem finiteSumMappingAux_locallyBounded_of_all_but_one (j : ι)
    (hb : ∀ i, i ≠ j → SvLocallyBoundedAt (S i) x) :
    SvLocallyBoundedAt (finiteSumMappingAux S) (x,b) := by
  classical
  apply finiteSumMappingAux_locallyBounded_of_horizon
  intro z hz hsum i
  have hoff (k : ι) (hk : k ≠ j) : z k = 0 := by
    simpa only [svHorizonOuterLimit_eq_zero_of_svLocallyBoundedAt (hb k hk),mem_singleton_iff] using hz k
  by_cases hij : i = j
  · subst i
    have he : (∑ k, z k) = z j := Finset.sum_eq_single j (fun k _ hk ↦ hoff k hk) (by simp)
    exact he.symm.trans hsum
  · exact hoff i hij

/-- All but at most one Aubin summand suffices for 10.41(b). -/
theorem finiteSumCoderivativeQualification_of_all_but_one_aubin {u : PiLp 2 (fun _ : ι ↦ F)}
    (j : ι) (ha : ∀ i, i ≠ j → HasAubinPropertyAt (S i) x (u i)) :
    FiniteSumCoderivativeQualification S x u := by
  classical
  intro v hv hsum i
  have hoff (k : ι) (hk : k ≠ j) : v k = 0 := by
    simpa only [(hasAubinPropertyAt_iff_coderivative_zero (ha k hk).2.1 (ha k hk).2.2.1).mp
      (ha k hk),mem_singleton_iff] using hv k
  by_cases hij : i = j
  · subst i
    have he : (∑ k, v k) = v j := Finset.sum_eq_single j (fun k _ hk ↦ hoff k hk) (by simp)
    exact he.symm.trans hsum
  · exact hoff i hij

theorem finiteSumCoderivativeQualification_of_all_but_one_strict {u : PiLp 2 (fun _ : ι ↦ F)}
    (hu : ∀ i, u i ∈ S i x) (j : ι)
    (hs : ∀ i, i ≠ j → SvStrictlyContinuousAt (S i) x) :
    FiniteSumCoderivativeQualification S x u :=
  finiteSumCoderivativeQualification_of_all_but_one_aubin j
    (fun i hi ↦ (hs i hi).hasAubinPropertyAt (hu i))

end RW
