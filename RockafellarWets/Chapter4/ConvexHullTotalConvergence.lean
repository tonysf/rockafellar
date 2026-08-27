/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Total convergence of convex hulls

This file proves Proposition 4.30(c).  Its no-escape argument is the direct
finite-dimensional counterpart of the book's ray-space proof.
-/

import RockafellarWets.Chapter3.CosmicClosure
import RockafellarWets.Chapter4.ConvexHullConvergence
import RockafellarWets.Chapter4.TotalConvergenceAutomaticCompletion
import RockafellarWets.Chapter4.TotalLinearImages

open Bornology Filter Function Metric Set Topology
open scoped BigOperators Pointwise

namespace RW

section ConvexHullTotalConvergence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A vanishing nonnegative rescaling of points selected from a totally
convergent sequence can only have a limiting vector in the horizon cone. -/
private theorem limit_scaled_selection_mem_horizon
    {Cseq : ℕ → Set E} {C : Set E} (hC : TotalConverges Cseq C)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {z : ℕ → E}
    (hz : ∀ n, z n ∈ Cseq (φ n)) {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (ha0 : Tendsto a atTop (nhds 0))
    {q : E} (hq : Tendsto (fun n ↦ a n • z n) atTop (nhds q)) :
    q ∈ horizonCone C := by
  by_cases hq0 : q = 0
  · subst q
    exact zero_mem_horizonCone C
  · have hane : ∀ᶠ n in atTop, a n ≠ 0 := by
      have hscaledNe : ∀ᶠ n in atTop, a n • z n ≠ 0 :=
        hq.eventually (compl_singleton_mem_nhds_iff.mpr hq0)
      exact hscaledNe.mono fun n hn hzero ↦ hn (by simp [hzero])
    have hapos : ∀ᶠ n in atTop, 0 < a n :=
      hane.mono fun n hn ↦ (lt_of_le_of_ne (ha n) (Ne.symm hn))
    rcases extraction_of_eventually_atTop hapos with ⟨ψ, hψ, hapos'⟩
    let u : CosmicBoundary E := cosmicDirectionOf q hq0
    have hscalePos : ∀ n, 0 < ‖q‖⁻¹ * a (ψ n) := fun n ↦
      mul_pos (inv_pos.mpr (norm_pos_iff.mpr hq0)) (hapos' n)
    have hscaleZero : Tendsto (fun n ↦ ‖q‖⁻¹ * a (ψ n)) atTop
        (nhds 0) := by
      simpa only [mul_zero] using
        tendsto_const_nhds.mul (ha0.comp hψ.tendsto_atTop)
    have hscaled : Tendsto
        (fun n ↦ (‖q‖⁻¹ * a (ψ n)) • z (ψ n)) atTop
        (nhds (u : E)) := by
      have hconst : Tendsto
          (fun n ↦ ‖q‖⁻¹ • (a (ψ n) • z (ψ n))) atTop
          (nhds (‖q‖⁻¹ • q)) :=
        tendsto_const_nhds.smul (hq.comp hψ.tendsto_atTop)
      simpa only [mul_smul, u, coe_cosmicDirectionOf,
        NormedSpace.normalize] using hconst
    have hdir : Tendsto (fun n ↦ cosmicEmbed (z (ψ n))) atTop
        (nhds (cosmicDirection u)) :=
      tendsto_cosmicDirection_of_scaling hscalePos hscaleZero hscaled
    have huOuter : (u : E) ∈ horizonOuterSetLimit Cseq :=
      mem_horizonOuterSetLimit_iff_exists_cosmicDirection_subsequence.2
        ⟨φ ∘ ψ, z ∘ ψ, hφ.comp hψ, fun n ↦ hz (ψ n), hdir⟩
    have huC : (u : E) ∈ horizonCone C := hC.horizonOuter_subset huOuter
    have hscaledBack :=
      (isCone_horizonCone C).smul_mem huC (norm_nonneg q)
    simpa only [u, coe_cosmicDirectionOf,
      NormedSpace.norm_smul_normalize q] using hscaledBack

/-- **Proposition 4.30(c), ordinary consequence.** -/
theorem TotalConverges.pkConverges_convexHull
    {Cseq : ℕ → Set E} {C : Set E} (hC : TotalConverges Cseq C)
    (hCne : C.Nonempty) (hpointed : IsPointed (horizonCone C)) :
    PKConverges (fun n ↦ convexHull ℝ (Cseq n))
      (closure (convexHull ℝ C)) := by
  have hinner0 : convexHull ℝ C ⊆
      innerSetLimit (fun n ↦ convexHull ℝ (Cseq n)) := by
    rw [← hC.pkConverges.inner_eq]
    exact convexHull_innerSetLimit_subset Cseq
  have hinner : closure (convexHull ℝ C) ⊆
      innerSetLimit (fun n ↦ convexHull ℝ (Cseq n)) :=
    closure_minimal hinner0 (isClosed_innerSetLimit _)
  have houter : outerSetLimit (fun n ↦ convexHull ℝ (Cseq n)) ⊆
      closure (convexHull ℝ C) := by
    intro x hx
    rcases mem_outerSetLimit_iff_exists_subsequence.1 hx with
      ⟨φ, y, hφ, hyHull, hyx⟩
    have hCneSeq : ∀ n, (Cseq (φ n)).Nonempty := by
      intro n
      by_contra hn
      have hempty := not_nonempty_iff_eq_empty.mp hn
      simpa [hempty] using hyHull n
    choose z w hzC hsum using fun n ↦
      exists_finrank_succ_convexCombination (hCneSeq n) (hyHull n)
    let k := Module.finrank ℝ E + 1
    let v : ℕ → Fin k → E := fun n i ↦
      (((w n : stdSimplex ℝ (Fin k)) : Fin k → ℝ) i) • z n i
    have hvBounded : IsBounded (range v) := by
      by_contra hvNot
      rcases exists_cosmicDirection_subsequence_of_not_isBounded hvNot with
        ⟨u, ψ, hψ, hvDirection⟩
      rcases exists_scaling_of_tendsto_cosmicDirection hvDirection with
        ⟨scale, hscalePos, hscale0, hscaled⟩
      rcases CompactSpace.tendsto_subseq (w ∘ ψ) with
        ⟨wbar, χ, hχ, hwwbar⟩
      have huHorizon : ∀ i, (u : Fin k → E) i ∈ horizonCone C := by
        intro i
        let a : ℕ → ℝ := fun n ↦ scale (χ n) *
          (((w (ψ (χ n)) : stdSimplex ℝ (Fin k)) : Fin k → ℝ) i)
        have haNonneg : ∀ n, 0 ≤ a n := fun n ↦
          mul_nonneg (hscalePos (χ n)).le ((w (ψ (χ n))).property.1 i)
        have ha0 : Tendsto a atTop (nhds 0) := by
          have hwcoord := tendsto_pi_nhds.1
            (continuous_subtype_val.continuousAt.tendsto.comp hwwbar) i
          simpa only [a, zero_mul] using
            (hscale0.comp hχ.tendsto_atTop).mul hwcoord
        apply limit_scaled_selection_mem_horizon hC
          ((hφ.comp hψ).comp hχ)
          (fun n ↦ hzC (ψ (χ n)) i) haNonneg ha0
        have hi := tendsto_pi_nhds.1 (hscaled.comp hχ.tendsto_atTop) i
        simpa only [a, v, mul_smul] using hi
      have hsumScaled : Tendsto
          (fun n ↦ ∑ i, scale (χ n) • v (ψ (χ n)) i) atTop
          (nhds 0) := by
        have hySub := hyx.comp (hψ.comp hχ).tendsto_atTop
        have hs := (hscale0.comp hχ.tendsto_atTop).smul hySub
        have heq : (fun n ↦ ∑ i, scale (χ n) • v (ψ (χ n)) i) =
            (fun n ↦ scale (χ n) • y (ψ (χ n))) := by
          funext n
          rw [← Finset.smul_sum]
          simpa only [v] using congrArg (fun q ↦ scale (χ n) • q)
            (hsum (ψ (χ n)))
        rw [heq]
        convert hs using 1
        simp only [zero_smul]
      have hsumU : ∑ i, (u : Fin k → E) i = 0 := by
        have hlimSum : Tendsto
            (fun n ↦ ∑ i, scale (χ n) • v (ψ (χ n)) i) atTop
            (nhds (∑ i, (u : Fin k → E) i)) := by
          apply tendsto_finset_sum
          intro i _hi
          exact tendsto_pi_nhds.1 (hscaled.comp hχ.tendsto_atTop) i
        exact tendsto_nhds_unique hlimSum hsumScaled
      have huZero : (u : Fin k → E) = 0 := by
        apply funext
        exact hpointed.fintype (u : Fin k → E) huHorizon hsumU
      have huNorm : ‖(u : Fin k → E)‖ = 1 :=
        mem_sphere_zero_iff_norm.mp u.property
      simp [huZero] at huNorm
    rcases tendsto_subseq_of_bounded hvBounded (fun n ↦ mem_range_self n) with
      ⟨vbar, _hvbarRange, ψ, hψ, hvvbar⟩
    rcases CompactSpace.tendsto_subseq (w ∘ ψ) with
      ⟨wbar, χ, hχ, hwwbar⟩
    let θ : ℕ → ℕ := ψ ∘ χ
    have hθ : StrictMono θ := hψ.comp hχ
    have hvlim : Tendsto (v ∘ θ) atTop (nhds vbar) :=
      hvvbar.comp hχ.tendsto_atTop
    have hwlim : Tendsto (w ∘ θ) atTop (nhds wbar) := hwwbar
    have hex : ∀ i : Fin k, ∃ c ∈ C, ∃ d ∈ horizonCone C,
        vbar i =
          (((wbar : stdSimplex ℝ (Fin k)) : Fin k → ℝ) i) • c + d := by
      intro i
      by_cases hwi : ((wbar : stdSimplex ℝ (Fin k)) : Fin k → ℝ) i = 0
      · exact ⟨hCne.choose, hCne.choose_spec, vbar i,
          limit_scaled_selection_mem_horizon hC (hφ.comp hθ)
            (fun n ↦ hzC (θ n) i)
            (fun n ↦ (w (θ n)).property.1 i)
            (by
              have hi := tendsto_pi_nhds.1
                (continuous_subtype_val.continuousAt.tendsto.comp hwlim) i
              change ((wbar : Fin k → ℝ) i = 0) at hwi
              have hi' : Tendsto (fun n ↦ ((w (θ n) : Fin k → ℝ) i)) atTop
                  (nhds ((wbar : Fin k → ℝ) i)) := by
                simpa only [Function.comp_apply] using hi
              rw [hwi] at hi'
              exact hi')
            (by
              have hi := tendsto_pi_nhds.1 hvlim i
              simpa only [Function.comp_apply, v] using hi),
          by simp [hwi]⟩
      · have hwiPos : 0 < ((wbar : stdSimplex ℝ (Fin k)) : Fin k → ℝ) i :=
          lt_of_le_of_ne (wbar.property.1 i) (Ne.symm hwi)
        have hwPosEv : ∀ᶠ n in atTop,
            0 < (((w (θ n) : stdSimplex ℝ (Fin k)) : Fin k → ℝ) i) := by
          have hi := tendsto_pi_nhds.1
            (continuous_subtype_val.continuousAt.tendsto.comp hwlim) i
          exact hi.eventually (Ioi_mem_nhds hwiPos)
        rcases extraction_of_eventually_atTop hwPosEv with ⟨η, hη, hwPos⟩
        let ci : E :=
          (((wbar : stdSimplex ℝ (Fin k)) : Fin k → ℝ) i)⁻¹ • vbar i
        have hzci : Tendsto (fun n ↦ z (θ (η n)) i) atTop (nhds ci) := by
          have hwcoord := tendsto_pi_nhds.1
            (continuous_subtype_val.continuousAt.tendsto.comp hwlim) i
          have hinv := (hwcoord.comp hη.tendsto_atTop).inv₀ hwi
          have hvcoord := tendsto_pi_nhds.1
            (hvlim.comp hη.tendsto_atTop) i
          have hprod := hinv.smul hvcoord
          have hprod' : Tendsto (fun n ↦ z (θ (η n)) i) atTop
              (nhds (((((wbar : stdSimplex ℝ (Fin k)) : Fin k → ℝ) i)⁻¹) •
                vbar i)) := by
            apply hprod.congr'
            exact Eventually.of_forall fun n ↦ by
              simp only [Function.comp_apply, v]
              exact inv_smul_smul₀ (ne_of_gt (hwPos n)) (z (θ (η n)) i)
          simpa only [ci] using hprod'
        have hciC : ci ∈ C := by
          rw [← hC.pkConverges.outer_eq]
          exact mem_outerSetLimit_iff_exists_subsequence.2
            ⟨φ ∘ θ ∘ η, fun n ↦ z (θ (η n)) i,
              (hφ.comp hθ).comp hη, fun n ↦ hzC (θ (η n)) i, hzci⟩
        refine ⟨ci, hciC, 0, zero_mem_horizonCone C, ?_⟩
        simp only [add_zero, ci, smul_smul]
        rw [mul_inv_cancel₀ hwi, one_smul]
    choose c hcC d hdH hvdecomp using hex
    have hsumVbar : ∑ i, vbar i = x := by
      have hsumLim : Tendsto (fun n ↦ ∑ i, v (θ n) i) atTop
          (nhds (∑ i, vbar i)) := by
        apply tendsto_finset_sum
        intro i _hi
        exact tendsto_pi_nhds.1 hvlim i
      have hySub := hyx.comp hθ.tendsto_atTop
      have hsumY : (fun n ↦ ∑ i, v (θ n) i) = y ∘ θ := by
        funext n
        simpa only [v] using hsum (θ n)
      rw [hsumY] at hsumLim
      exact tendsto_nhds_unique hsumLim hySub
    rw [closure_convexHull_eq_add_convexHull_horizonCone hC.1 hpointed]
    refine ⟨∑ i, ((wbar : stdSimplex ℝ (Fin k)) : Fin k → ℝ) i • c i,
      ?_, ∑ i, d i, ?_, ?_⟩
    · apply mem_convexHull_of_exists_fintype
        (w := fun i ↦ ((wbar : stdSimplex ℝ (Fin k)) : Fin k → ℝ) i)
        (z := c) wbar.property.1 wbar.property.2 hcC
      rfl
    · exact (mem_convexHull_iff_exists_finrank_succ_sum_mem
        (isCone_horizonCone C)).2 ⟨d, hdH, rfl⟩
    · rw [← hsumVbar]
      simp_rw [hvdecomp]
      exact (Finset.sum_add_distrib).symm
  exact ⟨Set.Subset.antisymm
      ((innerSetLimit_subset_outerSetLimit _).trans houter) hinner,
    Set.Subset.antisymm houter
      (hinner.trans (innerSetLimit_subset_outerSetLimit _))⟩

/-- **Proposition 4.30(c).** Total convergence is preserved by convex hulls
when the limit is nonempty and its horizon cone is pointed. -/
theorem TotalConverges.convexHull
    {Cseq : ℕ → Set E} {C : Set E} (hC : TotalConverges Cseq C)
    (hCne : C.Nonempty) (hpointed : IsPointed (horizonCone C)) :
    TotalConverges (fun n ↦ convexHull ℝ (Cseq n))
      (closure (convexHull ℝ C)) := by
  apply totalConverges_of_convex (hC.pkConverges_convexHull hCne hpointed)
  · exact hCne.mono fun x hx ↦ subset_closure (subset_convexHull ℝ C hx)
  · exact fun n ↦ convex_convexHull ℝ (Cseq n)

/-- Proposition 4.30(c) with the book's displayed description of the limit,
`con C + con C∞`. -/
theorem TotalConverges.convexHull_add_horizonCone
    {Cseq : ℕ → Set E} {C : Set E} (hC : TotalConverges Cseq C)
    (hCne : C.Nonempty) (hpointed : IsPointed (horizonCone C)) :
    TotalConverges (fun n ↦ _root_.convexHull ℝ (Cseq n))
      (_root_.convexHull ℝ C + _root_.convexHull ℝ (horizonCone C)) := by
  rw [← closure_convexHull_eq_add_convexHull_horizonCone hC.1 hpointed]
  exact hC.convexHull hCne hpointed

end ConvexHullTotalConvergence

end RW
