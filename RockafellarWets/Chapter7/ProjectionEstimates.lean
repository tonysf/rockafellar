/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 7: Quantitative stability of metric projections
-/

import RockafellarWets.Chapter5.ProjectionMappings
import RockafellarWets.Chapter7.LipschitzEpiDistance
import RockafellarWets.Chapter7.ProximalEstimates

open Metric Set
open scoped NNReal

namespace RW

variable {E : Type*} [NormedAddCommGroup E]

/-- On the ball of radius `r`, the squared distance from `a` is Lipschitz
with constant `2 * (‖a‖ + r)`, as used in the guide to Exercise 7.67. -/
theorem lipschitzOnWith_norm_sub_sq (a : E) (r : ℝ≥0) :
    LipschitzOnWith (2 * (‖a‖₊ + r)) (fun x : E ↦ ‖x - a‖ ^ 2) (closedBall 0 (r : ℝ)) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hdiff := abs_norm_sub_norm_le (x-a) (y-a)
  rw [sub_sub_sub_cancel_right] at hdiff
  have hx' : ‖x-a‖ ≤ r + ‖a‖ := (norm_sub_le x a).trans (add_le_add_left (mem_closedBall_zero_iff.1 hx) _)
  have hy' : ‖y-a‖ ≤ r + ‖a‖ := (norm_sub_le y a).trans (add_le_add_left (mem_closedBall_zero_iff.1 hy) _)
  rw [Real.dist_eq, sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)), dist_eq_norm]
  push_cast
  exact mul_le_mul (by linarith) hdiff (abs_nonneg _) (by positivity)

private theorem projection_mem_indicator_prox {C : Set E} {a x : E} (hx : x ∈ projMapping C a) :
    x ∈ proximalMappingEReal (indicatorVA C) (1/2) a ∧
      moreauEnvelopeEReal (indicatorVA C) (1/2) a = ((‖x-a‖^2 : ℝ) : EReal) := by
  have hv {z : E} (hz : z ∈ C) :
      proximalObjectiveEReal (indicatorVA C) (1/2) a z = ((‖z-a‖^2 : ℝ) : EReal) := by
    norm_num [proximalObjectiveEReal, indicatorVA_apply_mem hz]
  have hmin (z : E) : proximalObjectiveEReal (indicatorVA C) (1/2) a x ≤
      proximalObjectiveEReal (indicatorVA C) (1/2) a z := by
    by_cases hz : z ∈ C
    · rw [hv hx.1, hv hz, EReal.coe_le_coe_iff]
      exact pow_le_pow_left₀ (norm_nonneg _) (hx.2 z hz) _
    · change _ ≤ indicatorVA C z + (((1/(2*(1/2)))*‖z-a‖^2 : ℝ) : EReal)
      rw [indicatorVA_apply_not_mem hz, EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
      exact le_top
  have heq := (le_iInf hmin).antisymm (iInf_le _ x)
  have he : moreauEnvelopeEReal (indicatorVA C) (1/2) a = ((‖x-a‖^2 : ℝ) : EReal) :=
    heq.symm.trans (hv hx.1)
  exact ⟨mem_proximalMappingEReal_iff.2 ⟨heq, he.trans_lt (EReal.coe_lt_top _)⟩,he⟩

section

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The auxiliary epi-distance bound in the guide to 7.67 for two
indicator functions regularized by the same squared distance. -/
theorem auxEpiDistance_indicator_proximalObjective_le {C D : Set E} (hC : IsClosed C)
    (hnC : C.Nonempty) (hD : IsClosed D) (hnD : D.Nonempty) (a : E) (r : ℝ≥0)
    (hd : rhoHatDistance r C D ≤ 1/2) :
    auxEpiDistance r (proximalObjectiveEReal (indicatorVA C) (1/2) a)
      (proximalObjectiveEReal (indicatorVA D) (1/2) a) ≤
        2*(1+‖a‖+(r : ℝ))*rhoHatDistance r C D := by
  let s : ℝ≥0 := r + 1/2
  let q := fun x : E ↦ ‖x-a‖^2
  have hrs : rhoHatDistance r C D ≤ (s : ℝ) - r := by dsimp [s]; linarith
  have h := auxEpiDistance_add_indicatorVA_le hC hnC hD hnD (lipschitzOnWith_norm_sub_sq a s)
    (lipschitzOnWith_norm_sub_sq a s) hrs
  have hsup : sSup ((fun x : E ↦ |q x - q x|) '' closedBall 0 (r : ℝ)) = 0 := by
    simp only [sub_self, abs_zero]
    rw [(nonempty_closedBall.2 r.2 : (closedBall (0:E) (r:ℝ)).Nonempty).image_const (0:ℝ), csSup_singleton]
  have heq (A : Set E) : proximalObjectiveEReal (indicatorVA A) (1/2) a =
      fun x ↦ (q x : EReal) + indicatorVA A x := by
    funext x; norm_num [proximalObjectiveEReal, q, add_comm]
  rw [heq C, heq D]
  change auxEpiDistance r _ _ ≤ sSup ((fun x ↦ |q x-q x|) '' closedBall 0 (r : ℝ)) + _ at h
  rw [hsup, zero_add, max_self] at h
  refine h.trans_eq ?_
  dsimp [s]; ring

end

/-- **Exercise 7.67 (projection estimates).** If the two closed convex sets
are close in truncated set distance, their projections at `a` differ by
at most `3 * √(θ * d)`, with `θ = 1 + ‖a‖ + r`. -/
theorem projection_estimate [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {C D : Set E} (hC : IsClosed C) (hc : Convex ℝ C) (hD : IsClosed D) (hd : Convex ℝ D)
    {a x y : E} (hx : x ∈ projMapping C a) (hy : y ∈ projMapping D a) {r : ℝ≥0} (hr : ‖x‖+4 < r)
    (hnear : rhoHatDistance r C D < 1 / (4*(1+‖a‖+(r : ℝ)))) :
    ‖y-x‖ ≤ 3 * √((1+‖a‖+(r : ℝ)) * rhoHatDistance r C D) := by
  let θ := 1+‖a‖+(r : ℝ)
  let d := rhoHatDistance r C D
  let e := auxEpiDistance r (proximalObjectiveEReal (indicatorVA C) (1/2) a)
    (proximalObjectiveEReal (indicatorVA D) (1/2) a)
  have hθ : 1 ≤ θ := by dsimp [θ]; linarith [norm_nonneg a, r.coe_nonneg]
  have hθpos : 0 < θ := by linarith
  have hdn : 0 ≤ d := rhoHatDistance_nonneg _ _ _
  change d < 1 / (4*θ) at hnear
  have hsmall : θ*d < 1/4 := by
    have h := (lt_div_iff₀ (show 0 < 4*θ by positivity)).1 hnear
    linarith
  have hdhalf : d ≤ 1/2 := by nlinarith [mul_le_mul_of_nonneg_right hθ hdn]
  have hes : e ≤ 2*θ*d := auxEpiDistance_indicator_proximalObjective_le hC ⟨x,hx.1⟩ hD ⟨y,hy.1⟩ a r hdhalf
  have hc' : Convex ℝ (epigraph (indicatorVA C)) := by rw [epigraph_indicatorVA]; exact hc.prod (convex_Ici _)
  have hd' : Convex ℝ (epigraph (indicatorVA D)) := by rw [epigraph_indicatorVA]; exact hd.prod (convex_Ici _)
  obtain ⟨hxp,hxe⟩ := projection_mem_indicator_prox hx
  obtain ⟨hyp,_⟩ := projection_mem_indicator_prox hy
  have hfloor : ((-‖x‖ : ℝ) : EReal) ≤ moreauEnvelopeEReal (indicatorVA C) (1/2) a := by
    rw [hxe, EReal.coe_le_coe_iff]; exact (neg_nonpos.2 (norm_nonneg _)).trans (sq_nonneg _)
  have hprox := (proximal_estimates hc' (lowerSemicontinuous_indicatorVA hC)
    ((indicatorVA_isProper_iff C).2 ⟨x,hx.1⟩) hd' (lowerSemicontinuous_indicatorVA hD)
    ((indicatorVA_isProper_iff D).2 ⟨y,hy.1⟩) (by norm_num : (0:ℝ) < 1/2) hxp hyp hfloor le_rfl
    (by linarith : ‖x‖ + 8*(1/2 : ℝ) < r) (show e ≤ 4*(1/2 : ℝ) by linarith)).2
  change ‖y-x‖ ≤ e + 2*√((1/2)*e) at hprox
  change ‖y-x‖ ≤ 3*√(θ*d)
  have hsqrt : √((1/2)*e) ≤ √(θ*d) := Real.sqrt_le_sqrt (by linarith)
  have hsq := Real.sq_sqrt (mul_nonneg hθpos.le hdn)
  have hs : √(θ*d) ≤ 1/2 := (Real.sqrt_le_iff.2 ⟨by norm_num, by linarith⟩)
  nlinarith only [hprox, hes, hsqrt, hsq, mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg (θ*d))]

end RW
