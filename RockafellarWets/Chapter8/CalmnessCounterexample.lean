/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: The zero direction in Proposition 8.32

For the symmetric downward square-root cusp, nearby slopes tend to plus or minus
infinity. At its vertex the limiting subdifferential is empty while the regular
subderivative takes plus infinity in every nonzero direction. The “nonzero”
restriction printed in the second equivalence of 8.32 therefore loses information.
-/

import RockafellarWets.Chapter8.CalmnessCriterion
import RockafellarWets.Chapter8.SubgradientsAndGradients
import Mathlib.Analysis.Calculus.Deriv.Abs

open Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

/-- The continuous downward cusp with steep branches on both sides of the origin. -/
noncomputable def symmetricDownwardCusp (x : ℝ) : EReal := ((-√|x| : ℝ) : EReal)

private theorem cusp_continuous : Continuous symmetricDownwardCusp :=
  continuous_coe_real_ereal.comp (Real.continuous_sqrt.comp continuous_abs).neg

private theorem cusp_zero : symmetricDownwardCusp 0 = ((0:ℝ):EReal) := by simp [symmetricDownwardCusp]

private theorem cusp_not_calm : ¬IsCalmFromBelowAt symmetricDownwardCusp 0 := by
  rintro ⟨k,hk,c,hc,hlocal⟩
  have hc0 : c = 0 := EReal.coe_injective (hc.symm.trans cusp_zero)
  subst c
  have ht : Tendsto (fun t : ℝ ↦ t^2) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((continuous_id.pow 2).tendsto (0:ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, k*t < 1 := by
    have hl : Tendsto (fun t : ℝ ↦ k*t) (𝓝[>] 0) (𝓝 0) := by
      simpa using (tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id.const_mul k) : Tendsto _ (𝓝[>] (0:ℝ)) _)
    exact hl.eventually (gt_mem_nhds zero_lt_one)
  obtain ⟨t,hh,hlt,htp⟩ := ((ht.eventually hlocal).and (hsmall.and self_mem_nhdsWithin)).exists
  have htp' : 0 < t := htp
  change ((0 - k * ‖t^2-0‖ : ℝ) : EReal) ≤ ((-√|t^2| : ℝ) : EReal) at hh
  rw [EReal.coe_le_coe_iff,sub_zero,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg t),
    Real.sqrt_sq htp'.le] at hh
  nlinarith [mul_pos htp' (sub_pos.2 hlt)]

private theorem cusp_regular_zero : regularSubdifferential symmetricDownwardCusp 0 = ∅ := by
  apply eq_empty_of_forall_notMem
  intro v hv
  obtain ⟨c,hc,hlocal⟩ := hv
  apply cusp_not_calm
  refine ⟨|v|+1,by positivity,c,hc,?_⟩
  filter_upwards [hlocal 1 one_pos] with y hy
  apply (EReal.coe_le_coe_iff.2 ?_).trans hy
  have hinner := (neg_le_abs ⟪v,y-0⟫_ℝ).trans (abs_real_inner_le_norm v (y-0))
  rw [Real.norm_eq_abs v] at hinner
  linarith

private noncomputable def cuspSlope (y : ℝ) : ℝ :=
  if 0 < y then -(2*√|y|)⁻¹ else (2*√|y|)⁻¹

private theorem cusp_regular_ne_zero {y : ℝ} (hy : y ≠ 0) :
    regularSubdifferential symmetricDownwardCusp y = {cuspSlope y} := by
  have hs := Real.hasDerivAt_sqrt (abs_ne_zero.2 hy)
  have hder : HasDerivAt (fun z : ℝ ↦ -√|z|) (cuspSlope y) y := by
    rcases hy.lt_or_gt with hn | hp
    · simpa [cuspSlope, hn.not_gt, Function.comp_def,one_div] using (hs.comp y (hasDerivAt_abs_neg hn)).neg
    · simpa [cuspSlope,hp,Function.comp_def,one_div] using (hs.comp y (hasDerivAt_abs_pos hp)).neg
  exact (regularSubdifferential_of_hasGradientAt hder.hasGradientAt').1

private theorem cusp_limiting_empty : subdifferential symmetricDownwardCusp 0 = ∅ := by
  apply eq_empty_of_forall_notMem
  intro v hv
  obtain ⟨_,y,z,hy,_,hz,hzlim⟩ := mem_subdifferential_iff_exists_seq.mp hv
  have hprod (n : ℕ) : |z n| * (2*√|y n|) = 1 := by
    have hy0 : y n ≠ 0 := by
      intro he
      have hm := hz n
      rw [he,cusp_regular_zero] at hm
      exact hm
    have hne : 2*√|y n| ≠ 0 := by positivity
    have hm := hz n
    rw [cusp_regular_ne_zero hy0,mem_singleton_iff] at hm
    rw [hm,cuspSlope]
    have hpos : 0 ≤ (2*√|y n|)⁻¹ := by positivity
    split <;> simp only [abs_neg,abs_of_nonneg hpos,inv_mul_cancel₀ hne]
  have ht : Tendsto (fun n ↦ 2*√|y n|) atTop (𝓝 0) := by
    simpa using (((Real.continuous_sqrt.tendsto |(0:ℝ)|).comp hy.abs).const_mul 2)
  have hlim : Tendsto (fun n ↦ |z n| * (2*√|y n|)) atTop (𝓝 0) := by simpa using hzlim.abs.mul ht
  simp_rw [hprod] at hlim
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hlim)

private theorem cusp_horizon_sign {a : ℝ} (ha : a = 1 ∨ a = -1) : a ∈ horizonSubdifferential symmetricDownwardCusp 0 := by
  let s := fun n : ℕ ↦ 1/((n:ℝ)+1)
  have hs (n : ℕ) : 0 < s n := by dsimp [s]; positivity
  have hs0 : Tendsto s atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let y := fun n ↦ -a*(s n)^2
  have hy : Tendsto y atTop (𝓝 0) := by simpa [y] using (hs0.pow 2).const_mul (-a)
  have heq (n : ℕ) : 2*s n * cuspSlope (y n) = a := by
    have ne := (hs n).ne'
    rcases ha with rfl | rfl
    · have hyval : y n = -(s n)^2 := by simp [y]
      rw [hyval,cuspSlope,if_neg (by linarith [sq_nonneg (s n)]),abs_neg,
        abs_of_nonneg (sq_nonneg (s n)),Real.sqrt_sq (hs n).le,mul_inv_cancel₀ (mul_ne_zero (by norm_num) ne)]
    · have hyval : y n = (s n)^2 := by simp [y]
      rw [hyval,cuspSlope,if_pos (sq_pos_of_pos (hs n)),abs_of_nonneg (sq_nonneg (s n)),
        Real.sqrt_sq (hs n).le,mul_neg,mul_inv_cancel₀ (mul_ne_zero (by norm_num) ne)]
  refine (mem_horizonSubdifferential_iff_zero_or_scaledSeq cusp_zero).2 (.inr
    ⟨y,fun n ↦ cuspSlope (y n),fun n ↦ 2*s n,tendsto_attentiveNhds_iff.2 ⟨hy,(cusp_continuous.tendsto 0).comp hy⟩,
      fun n ↦ ?_,fun n ↦ mul_pos (by norm_num) (hs n),by simpa only [mul_zero] using hs0.const_mul 2,?_⟩)
  · have hane : a ≠ 0 := by rcases ha with rfl | rfl <;> norm_num
    rw [cusp_regular_ne_zero (mul_ne_zero (neg_ne_zero.2 hane) (pow_ne_zero 2 (hs n).ne'))]
    rfl
  · simpa only [smul_eq_mul,heq] using (tendsto_const_nhds (x := a) (f := atTop))

/-- **Counterexample to 8.32.** The lower bound for the regular subderivative
on every nonzero direction does not imply existence of a limiting subgradient. -/
theorem regularSubderivative_nonzero_directions_counterexample :
    IsLocallyLscAt symmetricDownwardCusp 0 ∧
      subdifferential symmetricDownwardCusp 0 = ∅ ∧ regularSubderivative symmetricDownwardCusp 0 0 = ⊥ ∧
      ∀ w : ℝ, w ≠ 0 → regularSubderivative symmetricDownwardCusp 0 w = ⊤ := by
  have hl : IsLocallyLscAt symmetricDownwardCusp 0 :=
    isLocallyLscAt_of_isLocallyClosedAt_epigraph cusp_zero
      (RW.IsClosed.isLocallyClosedAt (isClosed_epigraph_of_lsc_ereal _ cusp_continuous.lowerSemicontinuous) _)
  refine ⟨hl,cusp_limiting_empty,(positivelyHomogeneous_regularSubderivative cusp_zero).zero_eq_zero_or_bot.resolve_left ?_,?_⟩
  · intro h
    simpa [cusp_limiting_empty] using (regularSubderivative_zero_eq_zero_iff cusp_zero hl).1 h
  · intro w hw
    apply regularSubderivative_eq_top_of_not_mem_polar cusp_zero hl
    intro hp
    rcases hw.lt_or_gt with hn | hpos
    · have hh := hp (-1) (cusp_horizon_sign (Or.inr rfl))
      change -1*w ≤ 0 at hh
      linarith
    · have hh := hp 1 (cusp_horizon_sign (Or.inl rfl))
      change 1*w ≤ 0 at hh
      linarith

end RW
