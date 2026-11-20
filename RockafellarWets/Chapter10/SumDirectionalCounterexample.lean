/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Mixed infinite slopes in the unconditional sum inequality
-/

import RockafellarWets.Chapter10.SumRegularityCounterexample
import RockafellarWets.Chapter7.EpigraphAddition

open Filter Set Topology

namespace RW

/-- The upward square-root cusp has infinite semiderivative in direction one. -/
theorem positiveRoot_hasSemiderivative_one : HasSemiderivative positiveRoot 0 1 ⊤ := by
  refine ⟨by simp,by simp,EReal.tendsto_nhds_top_iff_real.mpr ?_⟩
  intro a
  let K : ℝ := |a|+1
  have hK : 0 < K := by dsimp [K]; positivity
  let δ : ℝ := 1/(2*K^2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t ∧ t < δ :=
    inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iio_mem_nhds hδ))
  filter_upwards [prod_mem_prod hsmall (Ioi_mem_nhds (show (1/2:ℝ)<1 by norm_num))] with p hp
  have ht : 0 < p.1 := hp.1.1
  have hw : 0 < p.2 := lt_trans (by norm_num : (0:ℝ)<1/2) hp.2
  have hsq : (K*p.1)^2 < p.1*p.2 := by
    have hbound : p.1*(2*K^2) < 1 := (lt_div_iff₀ (by positivity : (0:ℝ)<2*K^2)).mp hp.1.2
    have hmul := mul_lt_mul_of_pos_right hbound ht
    have hw' := mul_lt_mul_of_pos_left hp.2 ht
    nlinarith
  have hs : K*p.1 < √(p.1*p.2) := Real.lt_sqrt_of_sq_lt hsq
  have haK : a < K := by dsimp [K]; linarith [le_abs_self a]
  have hfinal : a < √(p.1*p.2)/p.1 := (lt_div_iff₀ ht).mpr
    ((mul_lt_mul_of_pos_right haK ht).trans hs)
  rw [differenceQuotient_eq_coe positiveRoot_zero (rfl : positiveRoot (0+p.1 • p.2) = ((√|0+p.1 • p.2|:ℝ):EReal)),EReal.coe_lt_coe_iff]
  simpa only [zero_add,smul_eq_mul,sub_zero,abs_of_pos (mul_pos ht hw),div_eq_mul_inv,mul_comm] using hfinal

/-- **Counterexample to the unconditional derivative bound in 10.9** under
the book's inf-addition convention. The two finite continuous cusps cancel,
but their directional slopes are opposite infinities. -/
theorem infAddition_subderivative_sum_counterexample :
    ∃ f g : ℝ → EReal, IsProper f ∧ IsProper g ∧ Continuous f ∧ Continuous g ∧
      f 0 = 0 ∧ g 0 = 0 ∧ subderivative f 0 1 = ⊥ ∧ subderivative g 0 1 = ⊤ ∧
      subderivative (f+g) 0 1 = 0 ∧
      ¬ infAddition (subderivative f 0 1) (subderivative g 0 1) ≤ subderivative (f+g) 0 1 := by
  let f : ℝ → EReal := fun z ↦ ((-√|z|:ℝ):EReal)
  have hf0 : f 0 = ((0:ℝ):EReal) := by simp [f]
  have hcont : Continuous f := continuous_coe_real_ereal.comp (Real.continuous_sqrt.comp continuous_abs).neg
  have hneg : HasSemiderivative f 0 1 ⊥ := by
    refine ⟨by rw [hf0]; simp,by rw [hf0]; simp,?_⟩
    have hn := positiveRoot_hasSemiderivative_one.2.2.neg
    have he (p : ℝ × ℝ) : differenceQuotient f 0 p.1 p.2 =
        -differenceQuotient positiveRoot 0 p.1 p.2 := by
      rw [differenceQuotient_eq_coe hf0 rfl,differenceQuotient_eq_coe positiveRoot_zero rfl]
      simp only [f,sub_zero,mul_neg,EReal.coe_neg,positiveRoot]
    simpa only [he,EReal.neg_top] using hn
  have hsum : f+positiveRoot = fun _ ↦ (0:EReal) := by
    funext z
    change ((-√|z|:ℝ):EReal)+((√|z|:ℝ):EReal) = 0
    rw [← EReal.coe_add,neg_add_cancel,EReal.coe_zero]
  have hzero : subderivative (f+positiveRoot) 0 1 = 0 := by
    rw [hsum]
    apply HasSemiderivative.subderivative_eq
    refine ⟨by simp,by simp,?_⟩
    simpa [differenceQuotient] using (tendsto_const_nhds (x := (0:EReal)) (f := 𝓝[>] (0:ℝ) ×ˢ 𝓝 (1:ℝ)))
  refine ⟨f,positiveRoot,⟨⟨0,by rw [hf0]; exact EReal.coe_lt_top _⟩,fun z ↦ EReal.bot_lt_coe _⟩,
    positiveRoot_isProper,hcont,positiveRoot_continuous,hf0,positiveRoot_zero,
    hneg.subderivative_eq,positiveRoot_hasSemiderivative_one.subderivative_eq,hzero,?_⟩
  rw [hneg.subderivative_eq,positiveRoot_hasSemiderivative_one.subderivative_eq,hzero]
  simp [infAddition]

end RW
