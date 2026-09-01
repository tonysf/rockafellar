/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Smooth strict majorants on the positive half-line

This file isolates the scalar smoothing construction used in the proof of Theorem 6.11.  For a
nondecreasing modulus `f` on `[0, ∞)`, `positiveAverage f` is the average of `f` on `[r, 2r]`.
It is written after the change of variables `s = r * t`; this form makes preservation of
monotonicity transparent.  Two averages turn a possibly discontinuous monotone modulus into a
`C¹` function on `(0, ∞)`, and adding `r²` makes the majorization strict.

The fixed-interval definition is constant at zero on negative radii.  After the second averaging
and addition of `r²`, this gives a particularly simple global extension: it equals `r²` to the
left of zero.  The right derivative and its limiting value glue with this polynomial piece, so the
final strict majorant is everywhere `C¹`.
-/

open Filter MeasureTheory Set
open scoped Interval Topology

noncomputable section

namespace RW

/-- Extend a scalar function from the nonnegative half-line by keeping its value at zero. -/
def nonnegativeExtension (f : ℝ → ℝ) (x : ℝ) : ℝ := f (max x 0)

/-- The average of `f` on `[r, 2r]`, written on the fixed interval `[1, 2]`.

For `r > 0`, `positiveAverage f r = r⁻¹ ∫ s in r..2*r, f s`.  The fixed-interval form also
gives the intended value at the origin without a separate conditional. -/
def positiveAverage (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  ∫ t in (1 : ℝ)..2, nonnegativeExtension f (r * t)

/-- A monotone function on `[0, ∞)` is interval integrable between nonnegative endpoints. -/
theorem MonotoneOn.intervalIntegrable_nonnegative {f : ℝ → ℝ}
    (hf : MonotoneOn f (Ici 0)) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable f volume a b := by
  apply (hf.mono ?_).intervalIntegrable
  intro x hx
  exact le_trans (le_min ha hb) hx.1

/-- The constant-at-zero extension of a monotone function is globally monotone. -/
theorem monotone_nonnegativeExtension {f : ℝ → ℝ} (hf : MonotoneOn f (Ici 0)) :
    Monotone (nonnegativeExtension f) := by
  intro a b hab
  apply hf (by simp) (by simp)
  exact max_le_max hab le_rfl

/-- The fixed-interval definition agrees with the moving-average formula for positive radii. -/
theorem positiveAverage_eq_div_integral {f : ℝ → ℝ} {r : ℝ} (hr : 0 < r) :
    positiveAverage f r = (∫ s in r..2 * r, nonnegativeExtension f s) / r := by
  apply (eq_div_iff hr.ne').2
  simp [positiveAverage, mul_comm]

/-- On a positive moving interval the constant-at-zero extension does not change the integral. -/
theorem integral_nonnegativeExtension_eq {f : ℝ → ℝ} {r : ℝ} (hr : 0 < r) :
    (∫ s in r..2 * r, nonnegativeExtension f s) = ∫ s in r..2 * r, f s := by
  apply intervalIntegral.integral_congr
  intro s hs
  simp only [uIcc_of_le (by linarith : r ≤ 2 * r)] at hs
  simp [nonnegativeExtension, max_eq_left (hr.le.trans hs.1)]

/-- The averaging operator preserves the value zero at the origin. -/
@[simp]
theorem positiveAverage_zero {f : ℝ → ℝ} (hf : f 0 = 0) : positiveAverage f 0 = 0 := by
  simp [positiveAverage, nonnegativeExtension, hf]

private theorem intervalIntegrable_average_integrand {f : ℝ → ℝ}
    (hf : MonotoneOn f (Ici 0)) {r : ℝ} (hr : 0 ≤ r) :
    IntervalIntegrable (fun t : ℝ ↦ nonnegativeExtension f (r * t)) volume 1 2 := by
  apply Monotone.intervalIntegrable
  intro a b hab
  apply monotone_nonnegativeExtension hf
  exact mul_le_mul_of_nonneg_left hab hr

/-- Averaging preserves monotonicity on the nonnegative half-line. -/
theorem monotoneOn_positiveAverage {f : ℝ → ℝ} (hf : MonotoneOn f (Ici 0)) :
    MonotoneOn (positiveAverage f) (Ici 0) := by
  intro a ha b hb hab
  apply intervalIntegral.integral_mono_on (by norm_num)
      (intervalIntegrable_average_integrand hf ha)
      (intervalIntegrable_average_integrand hf hb)
  intro t ht
  apply monotone_nonnegativeExtension hf
  have ht' : t ∈ Icc (1 : ℝ) 2 := ht
  exact mul_le_mul_of_nonneg_right hab (zero_le_one.trans ht'.1)

/-- A monotone input is bounded above by its positive average. -/
theorem le_positiveAverage {f : ℝ → ℝ} (hf : MonotoneOn f (Ici 0))
    {r : ℝ} (hr : 0 < r) : f r ≤ positiveAverage f r := by
  calc
    f r = ∫ _t : ℝ in (1 : ℝ)..2, f r := by norm_num
    _ ≤ ∫ t : ℝ in (1 : ℝ)..2, nonnegativeExtension f (r * t) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
          (intervalIntegrable_const) (intervalIntegrable_average_integrand hf hr.le)
      intro t ht
      have ht' : t ∈ Icc (1 : ℝ) 2 := ht
      have hrt : 0 ≤ r * t := mul_nonneg hr.le (zero_le_one.trans ht'.1)
      apply hf (mem_Ici.mpr hr.le) (mem_Ici.mpr (le_max_right _ _))
      rw [max_eq_left hrt]
      simpa using mul_le_mul_of_nonneg_left ht'.1 hr.le
    _ = positiveAverage f r := rfl

/-- A positive average is bounded above by the input at twice the radius. -/
theorem positiveAverage_le_two {f : ℝ → ℝ} (hf : MonotoneOn f (Ici 0))
    {r : ℝ} (hr : 0 < r) : positiveAverage f r ≤ f (2 * r) := by
  calc
    positiveAverage f r =
        ∫ t : ℝ in (1 : ℝ)..2, nonnegativeExtension f (r * t) := rfl
    _ ≤ ∫ _t : ℝ in (1 : ℝ)..2, f (2 * r) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
          (intervalIntegrable_average_integrand hf hr.le) intervalIntegrable_const
      intro t ht
      have ht' : t ∈ Icc (1 : ℝ) 2 := ht
      have hrt : 0 ≤ r * t := mul_nonneg hr.le (zero_le_one.trans ht'.1)
      apply hf (mem_Ici.mpr (le_max_right _ _)) (mem_Ici.mpr (by positivity))
      rw [max_eq_left hrt]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left ht'.2 hr.le
    _ = f (2 * r) := by norm_num

private theorem tendsto_two_mul_right :
    Tendsto (fun r : ℝ ↦ 2 * r) (nhdsWithin 0 (Ioi 0)) (nhdsWithin 0 (Ioi 0)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · simpa using
      (tendsto_const_nhds.mul
        (tendsto_id.mono_right inf_le_left) :
          Tendsto (fun r : ℝ ↦ 2 * r) (nhdsWithin 0 (Ioi 0)) (nhds (2 * 0)))
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact mem_Ioi.mpr (mul_pos (by norm_num) hr)

/-- The little-o ratio at zero is preserved by positive averaging. -/
theorem tendsto_positiveAverage_div {f : ℝ → ℝ}
    (hf : MonotoneOn f (Ici 0)) (hf0 : f 0 = 0)
    (hsmall : Tendsto (fun r : ℝ ↦ f r / r)
      (nhdsWithin 0 (Ioi 0)) (nhds 0)) :
    Tendsto (fun r : ℝ ↦ positiveAverage f r / r)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hscaled : Tendsto (fun r : ℝ ↦ f (2 * r) / (2 * r))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := hsmall.comp tendsto_two_mul_right
  have hupper : Tendsto (fun r : ℝ ↦ 2 * (f (2 * r) / (2 * r)))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using tendsto_const_nhds.mul hscaled
  apply squeeze_zero'
  · filter_upwards [self_mem_nhdsWithin] with r hr
    apply div_nonneg _ hr.le
    rw [← hf0]
    exact (hf (mem_Ici.mpr le_rfl) (mem_Ici.mpr hr.le) hr.le).trans
      (le_positiveAverage hf hr)
  · filter_upwards [self_mem_nhdsWithin] with r hr
    calc
      positiveAverage f r / r ≤ f (2 * r) / r :=
        div_le_div_of_nonneg_right (positiveAverage_le_two hf hr) hr.le
      _ = 2 * (f (2 * r) / (2 * r)) := by field_simp
  · exact hupper

/-- The positive average itself converges to zero at the origin. -/
theorem tendsto_positiveAverage_zero {f : ℝ → ℝ}
    (hf : MonotoneOn f (Ici 0)) (hf0 : f 0 = 0)
    (hsmall : Tendsto (fun r : ℝ ↦ f r / r)
      (nhdsWithin 0 (Ioi 0)) (nhds 0)) :
    Tendsto (positiveAverage f) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hr : Tendsto (fun r : ℝ ↦ r) (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    tendsto_id.mono_right inf_le_left
  have hprod : Tendsto (fun r : ℝ ↦ positiveAverage f r / r * r)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using (tendsto_positiveAverage_div hf hf0 hsmall).mul hr
  refine Tendsto.congr' ?_ hprod
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact div_mul_cancel₀ _ hr.ne'

/-- The first averaging step is continuous on the open positive half-line. -/
theorem continuousOn_positiveAverage_Ioi {f : ℝ → ℝ}
    (hf : MonotoneOn f (Ici 0)) : ContinuousOn (positiveAverage f) (Ioi 0) := by
  let F : ℝ → ℝ := fun x ↦ ∫ s in (0 : ℝ)..x, nonnegativeExtension f s
  have hext : Monotone (nonnegativeExtension f) := monotone_nonnegativeExtension hf
  have hF : Continuous F := by
    exact intervalIntegral.continuous_primitive
      (fun a b ↦ hext.intervalIntegrable) 0
  have havg : EqOn (positiveAverage f) (fun r ↦ (F (2 * r) - F r) / r) (Ioi 0) := by
    intro r hr
    rw [positiveAverage_eq_div_integral hr]
    congr 1
    exact (intervalIntegral.integral_interval_sub_left
      (hext.intervalIntegrable : IntervalIntegrable (nonnegativeExtension f) volume 0 (2 * r))
      (hext.intervalIntegrable : IntervalIntegrable (nonnegativeExtension f) volume 0 r)).symm
  rw [continuousOn_congr havg]
  exact ((hF.comp (continuous_const.mul continuous_id)).sub hF).continuousOn.div
    continuous_id.continuousOn (fun r hr ↦ hr.ne')

/-- The first average is continuous on the closed nonnegative half-line. -/
theorem continuousOn_positiveAverage {f : ℝ → ℝ}
    (hf : MonotoneOn f (Ici 0)) (hf0 : f 0 = 0)
    (hsmall : Tendsto (fun r : ℝ ↦ f r / r)
      (nhdsWithin 0 (Ioi 0)) (nhds 0)) :
    ContinuousOn (positiveAverage f) (Ici 0) := by
  have hpos := continuousOn_positiveAverage_Ioi hf
  intro r hr
  have hrle : 0 ≤ r := hr
  rcases eq_or_lt_of_le hrle with rfl | hr
  · have hright : ContinuousWithinAt (positiveAverage f) (Ioi 0) 0 := by
      rw [ContinuousWithinAt, positiveAverage_zero hf0]
      exact tendsto_positiveAverage_zero hf hf0 hsmall
    have hsingle : ContinuousWithinAt (positiveAverage f) ({0} : Set ℝ) 0 :=
      continuousWithinAt_singleton
    simpa [union_singleton, Ioi_insert] using hright.union hsingle
  · exact hpos r hr
    |>.continuousAt (Ioi_mem_nhds hr)
    |>.continuousWithinAt

/-- The derivative furnished by the second averaging step. -/
def positiveAverageDeriv (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  (2 * f (2 * r) - f r - positiveAverage f r) / r

private theorem continuousAt_nonnegativeExtension {f : ℝ → ℝ}
    (hf : ContinuousOn f (Ioi 0)) {r : ℝ} (hr : 0 < r) :
    ContinuousAt (nonnegativeExtension f) r := by
  have hfr : ContinuousAt f r := (hf r hr).continuousAt (Ioi_mem_nhds hr)
  apply hfr.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hr] with x hx
  have hx' : 0 < x := hx
  simp [nonnegativeExtension, max_eq_left hx'.le]

/-- At positive radii, the derivative of an average has the usual moving-endpoint formula. -/
theorem hasDerivAt_positiveAverage {f : ℝ → ℝ}
    (hf : MonotoneOn f (Ici 0)) (hcont : ContinuousOn f (Ioi 0))
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (positiveAverage f) (positiveAverageDeriv f r) r := by
  let F : ℝ → ℝ := fun x ↦ ∫ s in (0 : ℝ)..x, nonnegativeExtension f s
  have hext : Monotone (nonnegativeExtension f) := monotone_nonnegativeExtension hf
  have hextcont : ContinuousOn (nonnegativeExtension f) (Ioi 0) :=
    hcont.congr fun x hx ↦ by
      have hx' : 0 < x := hx
      simp [nonnegativeExtension, max_eq_left hx'.le]
  have hF (x : ℝ) (hx : 0 < x) :
      HasDerivAt F (nonnegativeExtension f x) x := by
    exact intervalIntegral.integral_hasDerivAt_right
      (hext.intervalIntegrable : IntervalIntegrable (nonnegativeExtension f) volume 0 x)
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hextcont x hx)
      (continuousAt_nonnegativeExtension hcont hx)
  have hnum : HasDerivAt (fun x ↦ F (2 * x) - F x)
      (2 * nonnegativeExtension f (2 * r) - nonnegativeExtension f r) r := by
    convert ((hF (2 * r) (by positivity)).comp r
      ((hasDerivAt_id r).const_mul 2)).sub (hF r hr) using 1
    all_goals ring
  have hquot : HasDerivAt (fun x ↦ (F (2 * x) - F x) / x)
      (((2 * nonnegativeExtension f (2 * r) - nonnegativeExtension f r) * r -
        (F (2 * r) - F r)) / r ^ 2) r :=
    by
      convert hnum.div (hasDerivAt_id r) hr.ne' using 1
      all_goals simp [id]
  have havg : EqOn (positiveAverage f) (fun x ↦ (F (2 * x) - F x) / x) (Ioi 0) := by
    intro x hx
    rw [positiveAverage_eq_div_integral hx]
    congr 1
    exact (intervalIntegral.integral_interval_sub_left
      (hext.intervalIntegrable : IntervalIntegrable (nonnegativeExtension f) volume 0 (2 * x))
      (hext.intervalIntegrable : IntervalIntegrable (nonnegativeExtension f) volume 0 x)).symm
  have hlocal : positiveAverage f =ᶠ[𝓝 r] fun x ↦ (F (2 * x) - F x) / x :=
    havg.eventuallyEq_of_mem (Ioi_mem_nhds hr)
  apply (hquot.congr_of_eventuallyEq hlocal).congr_deriv
  have hdiff : F (2 * r) - F r = r * positiveAverage f r := by
    have hmov : F (2 * r) - F r =
        ∫ s in r..2 * r, nonnegativeExtension f s :=
      intervalIntegral.integral_interval_sub_left
        (hext.intervalIntegrable : IntervalIntegrable (nonnegativeExtension f) volume 0 (2 * r))
        (hext.intervalIntegrable : IntervalIntegrable (nonnegativeExtension f) volume 0 r)
    rw [hmov, positiveAverage_eq_div_integral hr]
    field_simp
  simp only [positiveAverageDeriv]
  rw [hdiff]
  simp [nonnegativeExtension, max_eq_left hr.le, max_eq_left (by positivity : 0 ≤ 2 * r)]
  field_simp

private theorem continuousOn_positiveAverageDeriv {f : ℝ → ℝ}
    (hf : MonotoneOn f (Ici 0)) (hcont : ContinuousOn f (Ioi 0)) :
    ContinuousOn (positiveAverageDeriv f) (Ioi 0) := by
  have htwice : ContinuousOn (fun r : ℝ ↦ f (2 * r)) (Ioi 0) :=
    hcont.comp (continuous_const.mul continuous_id).continuousOn (by
      intro r hr
      exact mul_pos (by norm_num) (show 0 < r from hr))
  have hnum : ContinuousOn
      (fun r : ℝ ↦ 2 * f (2 * r) - f r - positiveAverage f r) (Ioi 0) :=
    ((continuous_const.continuousOn.mul htwice).sub hcont).sub
      (continuousOn_positiveAverage_Ioi hf)
  exact hnum.div continuous_id.continuousOn (fun r hr ↦ hr.ne')

/-- The second averaging step is continuously differentiable on `(0, ∞)`. -/
theorem contDiffOn_positiveAverage {f : ℝ → ℝ}
    (hf : MonotoneOn f (Ici 0)) (hcont : ContinuousOn f (Ioi 0)) :
    ContDiffOn ℝ 1 (positiveAverage f) (Ioi 0) := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by rfl,
    contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    exact (hasDerivAt_positiveAverage hf hcont hr).differentiableAt.differentiableWithinAt
  · simp
  · apply contDiffOn_zero.mpr
    exact (continuousOn_positiveAverageDeriv hf hcont).congr fun r hr ↦
      (hasDerivAt_positiveAverage hf hcont hr).deriv

/-- The derivative created by an averaging step tends to zero at the origin. -/
theorem tendsto_deriv_positiveAverage_zero {f : ℝ → ℝ}
    (hf : MonotoneOn f (Ici 0)) (hf0 : f 0 = 0)
    (hsmall : Tendsto (fun r : ℝ ↦ f r / r)
      (nhdsWithin 0 (Ioi 0)) (nhds 0))
    (hcont : ContinuousOn f (Ioi 0)) :
    Tendsto (fun r : ℝ ↦ deriv (positiveAverage f) r)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hscaled : Tendsto (fun r : ℝ ↦ f (2 * r) / (2 * r))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := hsmall.comp tendsto_two_mul_right
  have htwice : Tendsto (fun r : ℝ ↦ f (2 * r) / r)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hmul : Tendsto (fun r : ℝ ↦ 2 * (f (2 * r) / (2 * r)))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      simpa using tendsto_const_nhds.mul hscaled
    refine Tendsto.congr' ?_ hmul
    filter_upwards [self_mem_nhdsWithin] with r hr
    field_simp
  have hformula : Tendsto
      (fun r : ℝ ↦ 2 * (f (2 * r) / r) - f r / r - positiveAverage f r / r)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using ((tendsto_const_nhds.mul htwice).sub hsmall).sub
      (tendsto_positiveAverage_div hf hf0 hsmall)
  have hD : Tendsto (positiveAverageDeriv f)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    refine Tendsto.congr' ?_ hformula
    filter_upwards [self_mem_nhdsWithin] with r hr
    simp only [positiveAverageDeriv]
    field_simp
  apply hD.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (hasDerivAt_positiveAverage hf hcont hr).deriv.symm

/-- With zero input value, the positive average vanishes at every nonpositive radius. -/
theorem positiveAverage_eq_zero_of_nonpos {f : ℝ → ℝ} (hf0 : f 0 = 0)
    {r : ℝ} (hr : r ≤ 0) : positiveAverage f r = 0 := by
  rw [positiveAverage]
  calc
    (∫ t in (1 : ℝ)..2, nonnegativeExtension f (r * t)) =
        ∫ _t in (1 : ℝ)..2, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Icc (1 : ℝ) 2 := by
        simpa only [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] using ht
      have ht0 : 0 ≤ t := by
        exact zero_le_one.trans ht'.1
      simp [nonnegativeExtension, max_eq_right (mul_nonpos_of_nonpos_of_nonneg hr ht0), hf0]
    _ = 0 := by simp

/-- The double average with the strictifying square added. -/
def smoothStrictMajorant (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  positiveAverage (positiveAverage f) r + r ^ 2

private theorem contDiff_one_of_right_data {f : ℝ → ℝ}
    (hpos : ContDiffOn ℝ 1 f (Ioi 0))
    (hright : HasDerivWithinAt f 0 (Ici 0) 0)
    (hderiv : Tendsto (fun r : ℝ ↦ deriv f r)
      (nhdsWithin 0 (Ioi 0)) (nhds 0))
    (hneg : ∀ r ≤ 0, f r = r ^ 2) :
    ContDiff ℝ 1 f ∧ HasDerivAt f 0 0 := by
  have hsquare (r : ℝ) : HasDerivAt (fun x : ℝ ↦ x ^ 2) (2 * r) r := by
    convert (hasDerivAt_id r).pow 2 using 1
    all_goals simp [id]
  have hnegDerivAt {r : ℝ} (hr : r < 0) : HasDerivAt f (2 * r) r := by
    apply (hsquare r).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hr] with x hx
    exact hneg x hx.le
  have hleft : HasDerivWithinAt f 0 (Iic 0) 0 := by
    have hsquare0 : HasDerivAt (fun x : ℝ ↦ x ^ 2) 0 0 := by
      simpa using hsquare 0
    exact hsquare0.hasDerivWithinAt.congr (fun x hx ↦ hneg x hx) (hneg 0 le_rfl)
  have hzero : HasDerivAt f 0 0 := by
    rw [← hasDerivWithinAt_univ]
    simpa only [Iic_union_Ici] using hleft.union hright
  have hdiff : Differentiable ℝ f := by
    intro r
    rcases lt_trichotomy r 0 with hr | rfl | hr
    · exact (hnegDerivAt hr).differentiableAt
    · exact hzero.differentiableAt
    · exact (hpos.differentiableOn_one r hr).differentiableAt (Ioi_mem_nhds hr)
  have hnegDeriv (r : ℝ) (hr : r ≤ 0) : deriv f r = 2 * r := by
    rcases hr.eq_or_lt with rfl | hr
    · simpa using hzero.deriv
    · exact (hnegDerivAt hr).deriv
  have hposDeriv : ContinuousOn (deriv f) (Ioi 0) :=
    hpos.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hderivCont : Continuous (deriv f) := by
    rw [continuous_iff_continuousAt]
    intro r
    rcases lt_trichotomy r 0 with hr | rfl | hr
    · have heq : (fun x : ℝ ↦ deriv f x) =ᶠ[𝓝 r] fun x ↦ 2 * x := by
        filter_upwards [Iio_mem_nhds hr] with x hx
        exact hnegDeriv x hx.le
      exact (continuousAt_const.mul continuousAt_id).congr_of_eventuallyEq heq
    · have hleftCont : ContinuousWithinAt (deriv f) (Iic 0) 0 := by
        exact (continuousAt_const.mul continuousAt_id).continuousWithinAt.congr
          (fun x hx ↦ hnegDeriv x hx) (hnegDeriv 0 le_rfl)
      have hrightOpen : ContinuousWithinAt (deriv f) (Ioi 0) 0 := by
        rw [ContinuousWithinAt, hzero.deriv]
        exact hderiv
      have hrightCont : ContinuousWithinAt (deriv f) (Ici 0) 0 := by
        have hsingle : ContinuousWithinAt (deriv f) ({0} : Set ℝ) 0 :=
          continuousWithinAt_singleton
        simpa [union_singleton, Ioi_insert] using hrightOpen.union hsingle
      have huniv : ContinuousWithinAt (deriv f) univ 0 := by
        simpa only [Iic_union_Ici] using hleftCont.union hrightCont
      simpa only [continuousWithinAt_univ] using huniv
    · exact (hposDeriv r hr).continuousAt (Ioi_mem_nhds hr)
  exact ⟨contDiff_one_iff_deriv.mpr ⟨hdiff, hderivCont⟩, hzero⟩

/-- A double positive average, followed by addition of `r²`, is an everywhere `C¹` strict
majorant with first-order contact at the origin. -/
theorem exists_contDiff_one_strict_majorant
    {θ₀ : ℝ → ℝ}
    (hmono : MonotoneOn θ₀ (Ici 0))
    (hzero : θ₀ 0 = 0)
    (hsmall : Tendsto (fun r : ℝ ↦ θ₀ r / r)
      (nhdsWithin 0 (Ioi 0)) (nhds 0)) :
    ∃ θ : ℝ → ℝ,
      ContDiff ℝ 1 θ ∧
      θ 0 = 0 ∧
      HasDerivAt θ 0 0 ∧
      (∀ r > 0, θ₀ r < θ r) ∧
      Tendsto (fun r : ℝ ↦ θ r / r)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) ∧
      Tendsto (fun r : ℝ ↦ deriv θ r)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  let θ₁ : ℝ → ℝ := positiveAverage θ₀
  let θ₂ : ℝ → ℝ := positiveAverage θ₁
  let θ : ℝ → ℝ := fun r ↦ θ₂ r + r ^ 2
  have hmono₁ : MonotoneOn θ₁ (Ici 0) := monotoneOn_positiveAverage hmono
  have hzero₁ : θ₁ 0 = 0 := positiveAverage_zero hzero
  have hsmall₁ : Tendsto (fun r : ℝ ↦ θ₁ r / r)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    tendsto_positiveAverage_div hmono hzero hsmall
  have hcont₁ : ContinuousOn θ₁ (Ici 0) :=
    continuousOn_positiveAverage hmono hzero hsmall
  have hcont₁' : ContinuousOn θ₁ (Ioi 0) := hcont₁.mono Ioi_subset_Ici_self
  have hzero₂ : θ₂ 0 = 0 := positiveAverage_zero hzero₁
  have hsmall₂ : Tendsto (fun r : ℝ ↦ θ₂ r / r)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    tendsto_positiveAverage_div hmono₁ hzero₁ hsmall₁
  have hc1₂ : ContDiffOn ℝ 1 θ₂ (Ioi 0) :=
    contDiffOn_positiveAverage hmono₁ hcont₁'
  have hderiv₂ : Tendsto (fun r : ℝ ↦ deriv θ₂ r)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    tendsto_deriv_positiveAverage_zero hmono₁ hzero₁ hsmall₁ hcont₁'
  have hr0 : Tendsto (fun r : ℝ ↦ r) (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    tendsto_id.mono_right inf_le_left
  have hθzero : θ 0 = 0 := by simp [θ, hzero₂]
  have hθsmall : Tendsto (fun r : ℝ ↦ θ r / r)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hsum : Tendsto (fun r : ℝ ↦ θ₂ r / r + r)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      simpa using hsmall₂.add hr0
    refine Tendsto.congr' ?_ hsum
    filter_upwards [self_mem_nhdsWithin] with r hr
    simp only [θ]
    field_simp
  have hright : HasDerivWithinAt θ 0 (Ici 0) 0 := by
    rw [hasDerivWithinAt_iff_tendsto_slope]
    have hset : Ici (0 : ℝ) \ {0} = Ioi 0 := by
      ext r
      simp only [mem_diff, mem_Ici, mem_singleton_iff, mem_Ioi]
      constructor
      · rintro ⟨hr, hr0⟩
        exact lt_of_le_of_ne hr (Ne.symm hr0)
      · intro hr
        exact ⟨hr.le, hr.ne'⟩
    rw [hset]
    refine Tendsto.congr' ?_ hθsmall
    filter_upwards [self_mem_nhdsWithin] with r hr
    simp [slope_def_field, hθzero]
  have hθderiv : Tendsto (fun r : ℝ ↦ deriv θ r)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hlin : Tendsto (fun r : ℝ ↦ 2 * r)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      simpa using tendsto_const_nhds.mul hr0
    have hsum : Tendsto (fun r : ℝ ↦ deriv θ₂ r + 2 * r)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      simpa using hderiv₂.add hlin
    refine Tendsto.congr' ?_ hsum
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hsquare : HasDerivAt (fun x : ℝ ↦ x ^ 2) (2 * r) r := by
      convert (hasDerivAt_id r).pow 2 using 1
      all_goals simp [id]
    have havgD := hasDerivAt_positiveAverage hmono₁ hcont₁' hr
    have havg : HasDerivAt θ₂ (deriv θ₂ r) r := by
      apply (show HasDerivAt θ₂ (positiveAverageDeriv θ₁ r) r by
        simpa only [θ₂] using havgD).congr_deriv
      simpa only [θ₂] using havgD.deriv.symm
    simpa only [θ] using (havg.add hsquare).deriv.symm
  have hc1θ : ContDiffOn ℝ 1 θ (Ioi 0) := by
    simpa only [θ] using hc1₂.add (contDiff_id.pow 2).contDiffOn
  have hθneg (r : ℝ) (hr : r ≤ 0) : θ r = r ^ 2 := by
    have hθ₂neg : θ₂ r = 0 := by
      simpa only [θ₂] using positiveAverage_eq_zero_of_nonpos hzero₁ hr
    simp [θ, hθ₂neg]
  have hglobal := contDiff_one_of_right_data hc1θ hright hθderiv hθneg
  refine ⟨θ, hglobal.1, hθzero, hglobal.2, ?_, hθsmall, hθderiv⟩
  · intro r hr
    calc
      θ₀ r ≤ θ₁ r := le_positiveAverage hmono hr
      _ ≤ θ₂ r := le_positiveAverage hmono₁ hr
      _ < θ₂ r + r ^ 2 := lt_add_of_pos_right _ (sq_pos_of_pos hr)
      _ = θ r := rfl

end RW
