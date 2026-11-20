/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The zero-times-infinity qualification in modulus composition
-/

import RockafellarWets.Chapter9.SmoothLipschitzModulus
import RockafellarWets.Chapter9.DistanceModulus
import RockafellarWets.Chapter9.LipschitzModulusCalculus
import Mathlib.Analysis.Calculus.Deriv.Pow

open Metric Set
open scoped ENNReal NNReal

namespace RW

/-- The inner square map has zero modulus at the origin. -/
theorem lipschitzModulus_sq_zero : lipschitzModulus (fun x : ℝ ↦ x^2) 0 = 0 := by
  have hd : HasStrictDerivAt (fun x : ℝ ↦ x^2) 0 0 := by
    simpa using hasStrictDerivAt_pow 2 (0:ℝ)
  simpa using lipschitzModulus_eq_of_hasStrictFDerivAt hd.hasStrictFDerivAt

theorem lipschitzModulus_abs_zero : lipschitzModulus (fun x : ℝ ↦ |x|) 0 = 1 := by
  have h := (lipschitzModulus_infDist (E := ℝ) (C := {0}) isClosed_singleton
    (singleton_nonempty 0) 0).2.2 (by simp)
  simpa only [infDist_singleton,Real.dist_eq,sub_zero] using h

/-- In **Exercise 9.8(c)** the unqualified composition inequality fails
with the convention `0 * ∞ = 0`. The maps `x ↦ x²` and `s ↦ √|s|` compose
to absolute value: its modulus is one while the displayed product is zero. -/
theorem modulus_composition_zero_infinity_counterexample :
    lipschitzModulus ((fun s : ℝ ↦ Real.sqrt |s|) ∘ (fun x : ℝ ↦ x^2)) 0 = 1 ∧
      lipschitzModulus (fun s : ℝ ↦ Real.sqrt |s|) 0 *
        lipschitzModulus (fun x : ℝ ↦ x^2) 0 = 0 := by
  constructor
  · have he : ((fun s : ℝ ↦ Real.sqrt |s|) ∘ (fun x : ℝ ↦ x^2)) = fun x ↦ |x| := by
      funext x
      simp only [Function.comp_def,abs_of_nonneg (sq_nonneg x),Real.sqrt_sq_eq_abs]
    rw [he,lipschitzModulus_abs_zero]
  · rw [lipschitzModulus_sq_zero,mul_zero]

theorem lipschitzModulus_sqrt_abs_zero :
    lipschitzModulus (fun s : ℝ ↦ Real.sqrt |s|) 0 = ⊤ := by
  by_contra hn
  have hf : StrictlyContinuousAt (fun x : ℝ ↦ x^2) 0 := by
    change lipschitzModulus (fun x : ℝ ↦ x^2) 0 < ⊤
    rw [lipschitzModulus_sq_zero]
    exact ENNReal.zero_lt_top
  have hg : StrictlyContinuousAt (fun s : ℝ ↦ Real.sqrt |s|) ((0:ℝ)^2) := by
    simpa only [zero_pow (by norm_num : 2 ≠ 0)] using (lt_top_iff_ne_top.mpr hn)
  have h := lipschitzModulus_comp_le hf hg
  simp only [zero_pow (by norm_num : 2 ≠ 0),modulus_composition_zero_infinity_counterexample.1,
    modulus_composition_zero_infinity_counterexample.2] at h
  exact (by norm_num at h)

end RW
