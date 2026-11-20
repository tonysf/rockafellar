/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The quantitative correction after constraint relaxation

For `f(x)=x²`, `C={0}`, `κ=0`, and penalty weight `λ=1`, every neighborhood
of the feasible set contains points where the penalized objective has
modulus strictly greater than `κ+λ=1`. Thus the unrelaxed neighborhood
bound printed after Proposition 9.68 is false.
-/

import RockafellarWets.Chapter9.ConstraintRelaxation
import RockafellarWets.Chapter9.ModulusCompositionCounterexample
import Mathlib.Analysis.Calculus.Deriv.Abs

open Filter Metric Set Topology
open scoped ENNReal NNReal

namespace RW

theorem lipschitzModulus_square_distancePenalty_gt_one {x : ℝ} (hx : 0 < x) :
    1 < lipschitzModulus (distancePenalty (fun y : ℝ ↦ y^2) {0} 1) x := by
  have hd : HasStrictDerivAt (fun y : ℝ ↦ y^2 + |y|) (2*x+1) x := by
    simpa using (hasStrictDerivAt_pow 2 x).add (hasStrictDerivAt_abs_pos hx)
  have he : distancePenalty (fun y : ℝ ↦ y^2) {0} 1 = fun y ↦ y^2 + |y| := by
    funext y
    simp [distancePenalty,infDist_singleton,Real.dist_eq]
  rw [he,lipschitzModulus_eq_of_hasStrictFDerivAt hd.hasStrictFDerivAt,
    ContinuousLinearMap.nnnorm_toSpanSingleton]
  apply ENNReal.coe_lt_coe.mpr
  change (1 : ℝ≥0) < ‖2*x+1‖₊
  rw [← NNReal.coe_lt_coe,coe_nnnorm,Real.norm_eq_abs,abs_of_pos (by linarith : 0 < 2*x+1)]
  norm_num
  linarith

/-- No open neighborhood of the feasible set supports the printed
`κ+λ` penalty modulus bound, even though the hypotheses of 9.68 hold. -/
theorem constraintRelaxation_unrelaxed_modulus_counterexample :
    (∀ x ∈ ({0} : Set ℝ), lipschitzModulus (fun y : ℝ ↦ y^2) x ≤ 0) ∧
      ∀ O : Set ℝ, IsOpen O → (0 : ℝ) ∈ O → ∃ x ∈ O,
        1 < lipschitzModulus (distancePenalty (fun y : ℝ ↦ y^2) {0} 1) x := by
  constructor
  · intro x hx
    have hx0 : x = 0 := hx
    rw [hx0,lipschitzModulus_sq_zero]
  · intro O hO h0
    obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds h0)
    refine ⟨r/2,hball ?_,lipschitzModulus_square_distancePenalty_gt_one (half_pos hr)⟩
    simpa only [mem_ball,Real.dist_eq,sub_zero,abs_of_pos (half_pos hr)] using half_lt_self hr

end RW
