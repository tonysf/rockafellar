/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Remaining Automatic Total-Convergence Cases

The convex and Pompeiu--Hausdorff clauses of Theorem 4.25.
-/

import RockafellarWets.Chapter4.ConvexLimits
import RockafellarWets.Chapter4.HausdorffConvergence
import RockafellarWets.Chapter4.TotalConvergenceAutomatic

open Bornology Filter Function Metric Set Topology

namespace RW

section ConvexCase

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **Theorem 4.25(a).** Ordinary convergence of convex sets to a nonempty
set is automatically total convergence. -/
theorem totalConverges_of_convex
    {Cseq : ℕ → Set E} {C : Set E} (hlim : PKConverges Cseq C)
    (hCne : C.Nonempty) (hconv : ∀ n, Convex ℝ (Cseq n)) :
    TotalConverges Cseq C := by
  apply totalConverges_iff_pkConverges_and_horizonOuter_subset.2
  refine ⟨hlim, ?_⟩
  have hCconv : Convex ℝ C := hlim.convex hconv
  intro w hw
  rcases hw with rfl | ⟨u, huOuter, r, hr, rfl⟩
  · exact zero_mem_horizonCone C
  · have huHorizon : (u : E) ∈ horizonCone C := by
      rcases mem_outerSetLimit_iff_exists_subsequence.1 huOuter with
        ⟨φ, z, hφ, hz, hzu⟩
      have hz' : ∀ n, z n ∈ cosmicEmbed '' Cseq (φ n) := by
        intro n
        simpa only [ordinaryCosmicSequence, cosmicSet, cosmicDirections_zero,
          union_empty] using hz n
      choose y hyC hyz using hz'
      have hyu : Tendsto (fun n ↦ cosmicEmbed (y n)) atTop
          (nhds (cosmicDirection u)) := by
        apply hzu.congr'
        exact Eventually.of_forall fun n ↦ (hyz n).symm
      rcases exists_scaling_of_tendsto_cosmicDirection hyu with
        ⟨scale, hscalePos, hscaleZero, hscaled⟩
      rcases hCne with ⟨xbar, hxbar⟩
      apply mem_horizonCone_of_forall_smul_add_mem (x := xbar)
      intro τ hτ
      have hhit : ∀ k : ℕ, ∀ᶠ n in atTop,
          (Cseq (φ n) ∩ ball xbar (1 / ((k : ℝ) + 1))).Nonempty := by
        intro k
        exact hφ.tendsto_atTop.eventually <|
          (show xbar ∈ innerSetLimit Cseq by simpa [hlim.inner_eq] using hxbar)
            _ (ball_mem_nhds _ (by positivity))
      rcases extraction_forall_of_frequently
          (fun k ↦ (hhit k).frequently) with ⟨ψ, hψ, hψhit⟩
      choose xb hxbC hxbBall using hψhit
      have hxb : Tendsto xb atTop (nhds xbar) := by
        rw [tendsto_iff_dist_tendsto_zero]
        exact squeeze_zero (fun n ↦ dist_nonneg)
          (fun n ↦ (mem_ball.mp (hxbBall n)).le)
          tendsto_one_div_add_atTop_nhds_zero_nat
      let a : ℕ → ℝ := fun n ↦ τ * scale (ψ n)
      have haZero : Tendsto a atTop (nhds 0) := by
        simpa only [a, mul_zero] using
          tendsto_const_nhds.mul (hscaleZero.comp hψ.tendsto_atTop)
      have haNonneg : ∀ n, 0 ≤ a n := fun n ↦
        mul_nonneg hτ (hscalePos (ψ n)).le
      have haLe : ∀ᶠ n in atTop, a n ≤ 1 :=
        haZero.eventually (Iic_mem_nhds (show (0 : ℝ) < 1 by norm_num))
      let q : ℕ → E := fun n ↦
        (1 - a n) • xb n + a n • y (ψ n)
      have hqLim : Tendsto q atTop (nhds (τ • (u : E) + xbar)) := by
        have hfirst : Tendsto (fun n ↦ (1 - a n) • xb n) atTop
            (nhds xbar) := by
          simpa only [one_smul, sub_zero] using
            ((tendsto_const_nhds (x := (1 : ℝ))).sub haZero).smul hxb
        have hsecond : Tendsto (fun n ↦ a n • y (ψ n)) atTop
            (nhds (τ • (u : E))) := by
          have hs := (hscaled.comp hψ.tendsto_atTop).const_smul τ
          simpa only [a, mul_smul] using hs
        simpa only [q, add_comm] using hfirst.add hsecond
      have hqMem : ∀ᶠ n in atTop, q n ∈ Cseq (φ (ψ n)) := by
        filter_upwards [haLe] with n han
        exact hconv (φ (ψ n)) (hxbC n) (hyC (ψ n))
          (sub_nonneg.mpr han) (haNonneg n) (by ring)
      rcases extraction_of_eventually_atTop hqMem with ⟨χ, hχ, hχmem⟩
      have hlimitOuter : τ • (u : E) + xbar ∈ outerSetLimit Cseq :=
        mem_outerSetLimit_iff_exists_subsequence.2
          ⟨φ ∘ ψ ∘ χ, q ∘ χ, (hφ.comp hψ).comp hχ,
            hχmem, hqLim.comp hχ.tendsto_atTop⟩
      rw [hlim.outer_eq] at hlimitOuter
      exact hlimitOuter
    exact (isCone_horizonCone C).2 huHorizon hr

end ConvexCase

section HausdorffCase

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **Theorem 4.25(e).** Pompeiu--Hausdorff convergence to a nonempty closed
set is total convergence. -/
theorem totalConverges_of_tendsto_pompeiuHausdorffEDist_zero
    {Cseq : ℕ → Set E} {C : Set E} (hC : IsClosed C) (_hCne : C.Nonempty)
    (hH : Tendsto (fun n ↦ pompeiuHausdorffEDist (Cseq n) C)
      atTop (nhds 0)) :
    TotalConverges Cseq C := by
  have hlim : PKConverges Cseq C :=
    pkConverges_of_tendsto_pompeiuHausdorffEDist_zero hC hH
  apply totalConverges_iff_pkConverges_and_horizonOuter_subset.2
  refine ⟨hlim, ?_⟩
  intro w hw
  rcases hw with rfl | ⟨u, huOuter, r, hr, rfl⟩
  · exact zero_mem_horizonCone C
  · have huHorizon : (u : E) ∈ horizonCone C := by
      rcases mem_outerSetLimit_iff_exists_subsequence.1 huOuter with
        ⟨φ, zcosmic, hφ, hzcosmic, hzu⟩
      have hzcosmic' : ∀ n, zcosmic n ∈ cosmicEmbed '' Cseq (φ n) := by
        intro n
        simpa only [ordinaryCosmicSequence, cosmicSet, cosmicDirections_zero,
          union_empty] using hzcosmic n
      choose y hyC hyz using hzcosmic'
      have hyu : Tendsto (fun n ↦ cosmicEmbed (y n)) atTop
          (nhds (cosmicDirection u)) := by
        apply hzu.congr'
        exact Eventually.of_forall fun n ↦ (hyz n).symm
      rcases exists_scaling_of_tendsto_cosmicDirection hyu with
        ⟨scale, hscalePos, hscaleZero, hscaled⟩
      have hHsub : Tendsto
          (fun n ↦ pompeiuHausdorffEDist (Cseq (φ n)) C)
          atTop (nhds 0) := hH.comp hφ.tendsto_atTop
      have hsmall : ∀ k : ℕ, ∀ᶠ n in atTop,
          pompeiuHausdorffEDist (Cseq (φ n)) C <
            ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
        intro k
        have hpos : 0 < (1 / ((k : ℝ) + 1) / 2) := by positivity
        have hev := (ENNReal.tendsto_nhds_zero.1 hHsub)
          (ENNReal.ofReal (1 / ((k : ℝ) + 1) / 2))
          (ENNReal.ofReal_pos.2 hpos)
        exact hev.mono fun n hn ↦ hn.trans_lt <| by
          rw [ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < 1 / ((k : ℝ) + 1))]
          exact half_lt_self (by positivity)
      rcases extraction_forall_of_frequently
          (fun k ↦ (hsmall k).frequently) with ⟨ψ, hψ, hψsmall⟩
      have hnear : ∀ n, ∃ c ∈ C,
          edist (y (ψ n)) c < ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
        intro n
        exact exists_edist_lt_of_hausdorffEDist_lt
          (hyC (ψ n)) (hψsmall n)
      choose c hcC hyc using hnear
      have hycDist : ∀ n, dist (y (ψ n)) (c n) < 1 / ((n : ℝ) + 1) := by
        intro n
        have hn := hyc n
        rw [edist_dist] at hn
        exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 hn
      have hdiff : Tendsto (fun n ↦ c n - y (ψ n)) atTop (nhds 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        exact squeeze_zero (fun n ↦ norm_nonneg _)
          (fun n ↦ by simpa only [norm_sub_rev, dist_eq_norm] using (hycDist n).le)
          tendsto_one_div_add_atTop_nhds_zero_nat
      have hscaledC : Tendsto (fun n ↦ scale (ψ n) • c n) atTop
          (nhds (u : E)) := by
        have herror : Tendsto
            (fun n ↦ scale (ψ n) • (c n - y (ψ n))) atTop
            (nhds 0) := by
          simpa only [zero_smul] using
            (hscaleZero.comp hψ.tendsto_atTop).smul hdiff
        have hsum := (hscaled.comp hψ.tendsto_atTop).add herror
        convert hsum using 1
        · funext n
          simp only [Function.comp_apply, smul_sub]
          abel
        · simp
      have hcosmicC : Tendsto (fun n ↦ cosmicEmbed (c n)) atTop
          (nhds (cosmicDirection u)) :=
        tendsto_cosmicDirection_of_scaling
          (fun n ↦ hscalePos (ψ n))
          (hscaleZero.comp hψ.tendsto_atTop) hscaledC
      have huClosure : cosmicDirection u ∈
          closure (cosmicSet C ({0} : Set E)) :=
        mem_closure_iff_seq_limit.mpr
          ⟨fun n ↦ cosmicEmbed (c n),
            fun n ↦ (cosmicEmbed_mem_cosmicSet_iff).2 (hcC n), hcosmicC⟩
      have hzeroCone : IsCone ({0} : Set E) := ⟨by simp, by simp⟩
      rw [closure_cosmicSet hzeroCone, mem_cosmicSet] at huClosure
      rcases huClosure with ⟨x, _, hxu⟩ | ⟨v, hv, hvu⟩
      · exact (cosmicEmbed_ne_cosmicDirection x u hxu).elim
      · have hvu' : v = u := injective_cosmicDirection hvu
        rcases hv with hv | hv
        · simpa [hvu'] using hv
        · have hv0 : (v : E) = 0 := by simpa using hv
          have hvnorm : ‖(v : E)‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
          simp [hv0] at hvnorm
    exact (isCone_horizonCone C).2 huHorizon hr

end HausdorffCase

end RW
