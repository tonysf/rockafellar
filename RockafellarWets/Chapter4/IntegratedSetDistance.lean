/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: The Integrated Set Distance

This file introduces the integrated set distance 4(12),

  `dl(C, D) = ∫_0^∞ dl_ρ(C, D) e^{-ρ} dρ`,

and proves the estimates of Lemma 4.41 together with the comparison 4(13)
against the Pompeiu--Hausdorff distance.
-/

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import RockafellarWets.Chapter4.EscapeToHorizon
import RockafellarWets.Chapter4.SetConvergenceCompactness
import RockafellarWets.Chapter4.LocalSetDistances

open Filter MeasureTheory Metric Set Topology
open scoped ENNReal NNReal

namespace RW

section ExponentialIntegrals

/-- `x e^{-x/2} ≤ 2` for `x ≥ 0`, the elementary damping bound behind every
integrability claim in this file. -/
theorem mul_exp_neg_half_le_two (x : ℝ) :
    x * Real.exp (-(x / 2)) ≤ 2 := by
  have hexp : x / 2 + 1 ≤ Real.exp (x / 2) := Real.add_one_le_exp _
  have hpos : (0 : ℝ) < Real.exp (x / 2) := Real.exp_pos _
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hpos]
  linarith

/-- A continuous function of at most affine growth stays integrable after
damping by `e^{-τ}`.  Both integrands of this file are of this shape. -/
theorem integrableOn_mul_exp_neg_of_abs_le_affine {f : ℝ → ℝ} {M : ℝ}
    (a : ℝ) (hM : 0 ≤ M) (hf : Continuous f)
    (hbound : ∀ x : ℝ, 0 ≤ x → |f x| ≤ M + x) :
    IntegrableOn (fun τ : ℝ ↦ f τ * Real.exp (-τ)) (Ioi a) := by
  refine integrable_of_isBigO_exp_neg (b := 1 / 2) (by norm_num)
    (hf.mul (Real.continuous_exp.comp continuous_neg)).continuousOn ?_
  rw [Asymptotics.isBigO_iff]
  refine ⟨M + 2, ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  have hhalf : Real.exp (-(x / 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  have hhalfpos : (0 : ℝ) < Real.exp (-(x / 2)) := Real.exp_pos _
  have hxe : x * Real.exp (-(x / 2)) ≤ 2 := mul_exp_neg_half_le_two x
  have hsplit : Real.exp (-x) = Real.exp (-(x / 2)) * Real.exp (-(x / 2)) := by
    rw [← Real.exp_add]; ring_nf
  have hnorm : ‖Real.exp (-(1 / 2) * x)‖ = Real.exp (-(x / 2)) := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    ring_nf
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), hnorm, hsplit]
  have hfb : |f x| ≤ M + x := hbound x hx
  calc |f x| * (Real.exp (-(x / 2)) * Real.exp (-(x / 2)))
      ≤ (M + x) * (Real.exp (-(x / 2)) * Real.exp (-(x / 2))) := by
        exact mul_le_mul_of_nonneg_right hfb (by positivity)
    _ = (M * Real.exp (-(x / 2)) + x * Real.exp (-(x / 2))) *
          Real.exp (-(x / 2)) := by ring
    _ ≤ (M + 2) * Real.exp (-(x / 2)) := by
        have : M * Real.exp (-(x / 2)) + x * Real.exp (-(x / 2)) ≤ M + 2 := by
          nlinarith
        exact mul_le_mul_of_nonneg_right this hhalfpos.le

/-- The affine-times-exponential decay used both for the closed form below
and for choosing a truncation radius in Theorem 4.42. -/
theorem tendsto_affine_mul_exp_neg_atTop (M : ℝ) :
    Tendsto (fun ρ : ℝ ↦ (M + ρ + 1) * Real.exp (-ρ)) atTop (𝓝 0) := by
  have hx : Tendsto (fun t : ℝ ↦ t * Real.exp (-t)) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have hc : Tendsto (fun t : ℝ ↦ Real.exp (-t)) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero
  have hsum : Tendsto (fun t : ℝ ↦ (M + 1) * Real.exp (-t) + t * Real.exp (-t))
      atTop (𝓝 ((M + 1) * 0 + 0)) := (hc.const_mul (M + 1)).add hx
  simp only [mul_zero, add_zero] at hsum
  refine hsum.congr fun t ↦ ?_
  ring

/-- `∫_ρ^∞ (M + τ) e^{-τ} dτ = (M + ρ + 1) e^{-ρ}`, the closed form driving
the tail estimates of Lemma 4.41. -/
theorem integral_Ioi_affine_mul_exp_neg (M ρ : ℝ) :
    ∫ τ in Ioi ρ, (M + τ) * Real.exp (-τ) = (M + ρ + 1) * Real.exp (-ρ) := by
  have hint : IntegrableOn (fun τ : ℝ ↦ (M + τ) * Real.exp (-τ)) (Ioi ρ) := by
    refine integrableOn_mul_exp_neg_of_abs_le_affine (M := |M|) ρ (abs_nonneg M)
      (continuous_const.add continuous_id) ?_
    intro x hx
    calc |M + x| ≤ |M| + |x| := abs_add_le _ _
      _ = |M| + x := by rw [abs_of_nonneg hx]
  have hderiv : ∀ τ ∈ Ici ρ,
      HasDerivAt (fun t : ℝ ↦ -(M + t + 1) * Real.exp (-t))
        ((M + τ) * Real.exp (-τ)) τ := by
    intro τ _
    have h0 : HasDerivAt (fun t : ℝ ↦ M + t + 1) 1 τ := by
      simpa using ((hasDerivAt_id τ).const_add M).add_const 1
    have h1 : HasDerivAt (fun t : ℝ ↦ -(M + t + 1)) (-1) τ := h0.neg
    have h2 : HasDerivAt (fun t : ℝ ↦ Real.exp (-t)) (-Real.exp (-τ)) τ := by
      simpa using (Real.hasDerivAt_exp (-τ)).comp τ (hasDerivAt_neg τ)
    have := h1.mul h2
    convert this using 1
    ring
  have hlim : Tendsto (fun t : ℝ ↦ -(M + t + 1) * Real.exp (-t)) atTop (𝓝 0) := by
    have h := (tendsto_affine_mul_exp_neg_atTop M).neg
    rw [neg_zero] at h
    exact h.congr fun t ↦ by ring
  have := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  rw [this]
  ring

/-- Splitting of the defining integral 4(12) at a radius `ρ ≥ 0`. -/
theorem integral_Ioi_zero_split {f : ℝ → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h₁ : IntegrableOn f (Ioc 0 ρ)) (h₂ : IntegrableOn f (Ioi ρ)) :
    ∫ τ in Ioi (0 : ℝ), f τ
      = (∫ τ in Ioc (0 : ℝ) ρ, f τ) + ∫ τ in Ioi ρ, f τ := by
  rw [← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi h₁ h₂,
    Ioc_union_Ioi_eq_Ioi hρ]

theorem integral_Ioc_exp_neg {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∫ τ in Ioc (0 : ℝ) ρ, Real.exp (-τ) = 1 - Real.exp (-ρ) := by
  have hsplit := integral_Ioi_zero_split (f := fun τ : ℝ ↦ Real.exp (-τ)) hρ
    ((integrableOn_exp_neg_Ioi 0).mono_set Ioc_subset_Ioi_self)
    (integrableOn_exp_neg_Ioi ρ)
  rw [integral_exp_neg_Ioi_zero, integral_exp_neg_Ioi] at hsplit
  linarith

end ExponentialIntegrals

section Definition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The `ρ`-distance reindexed by a real radius, so that it can be integrated
against `e^{-ρ} dρ` on `(0, ∞)`.  Negative radii are clipped to `0`. -/
noncomputable def rhoDistanceReal (ρ : ℝ) (C D : Set E) : ℝ :=
  rhoDistance ρ.toNNReal C D

theorem rhoDistanceReal_nonneg (ρ : ℝ) (C D : Set E) :
    0 ≤ rhoDistanceReal ρ C D :=
  rhoDistance_nonneg _ _ _

theorem rhoDistanceReal_comm (ρ : ℝ) (C D : Set E) :
    rhoDistanceReal ρ C D = rhoDistanceReal ρ D C :=
  rhoDistance_comm _ _ _

theorem rhoDistanceReal_self (ρ : ℝ) (C : Set E) :
    rhoDistanceReal ρ C C = 0 :=
  rhoDistance_self _ _

theorem rhoDistanceReal_triangle (ρ : ℝ) (C₁ C₂ C₃ : Set E) :
    rhoDistanceReal ρ C₁ C₃ ≤
      rhoDistanceReal ρ C₁ C₂ + rhoDistanceReal ρ C₂ C₃ :=
  rhoDistance_triangle _ _ _ _

theorem rhoDistanceReal_coe (ρ : ℝ≥0) (C D : Set E) :
    rhoDistanceReal (ρ : ℝ) C D = rhoDistance ρ C D := by
  rw [rhoDistanceReal, Real.toNNReal_coe]

theorem continuous_rhoDistanceReal (C D : Set E) :
    Continuous (fun ρ : ℝ ↦ rhoDistanceReal ρ C D) :=
  (continuous_rhoDistance C D).comp continuous_real_toNNReal

theorem rhoDistanceReal_mono {r s : ℝ} (hrs : r ≤ s) (C D : Set E) :
    rhoDistanceReal r C D ≤ rhoDistanceReal s C D :=
  rhoDistance_mono (Real.toNNReal_mono hrs) C D

/-- Proposition 4.37(c) in the real-radius indexing. -/
theorem rhoDistanceReal_le_max_infDist_zero_add {ρ : ℝ} (hρ : 0 ≤ ρ)
    (C D : Set E) :
    rhoDistanceReal ρ C D ≤ max (infDist 0 C) (infDist 0 D) + ρ := by
  have h := rhoDistance_le_max_infDist_zero_add ρ.toNNReal C D
  rw [Real.coe_toNNReal ρ hρ] at h
  exact h

/-- Formula 4(12): the integrated set distance. -/
noncomputable def integratedSetDistance (C D : Set E) : ℝ :=
  ∫ ρ in Ioi (0 : ℝ), rhoDistanceReal ρ C D * Real.exp (-ρ)

/-- The integrand of 4(12) is integrable on every right ray. -/
theorem integrableOn_rhoDistanceReal_mul_exp_neg (a : ℝ) (C D : Set E) :
    IntegrableOn
      (fun ρ : ℝ ↦ rhoDistanceReal ρ C D * Real.exp (-ρ)) (Ioi a) := by
  refine integrableOn_mul_exp_neg_of_abs_le_affine
    (M := max (infDist 0 C) (infDist 0 D)) a ?_
    (continuous_rhoDistanceReal C D) ?_
  · exact le_max_of_le_left infDist_nonneg
  · intro x hx
    rw [abs_of_nonneg (rhoDistanceReal_nonneg x C D)]
    exact rhoDistanceReal_le_max_infDist_zero_add hx C D

end Definition

section Lemma441

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem integrableOn_rhoDistanceReal_mul_exp_neg_Ioc
    (ρ : ℝ) (C D : Set E) :
    IntegrableOn
      (fun τ : ℝ ↦ rhoDistanceReal τ C D * Real.exp (-τ)) (Ioc 0 ρ) :=
  (integrableOn_rhoDistanceReal_mul_exp_neg 0 C D).mono_set Ioc_subset_Ioi_self

/-- The `ρ`-distance at radius zero already dominates the gap between the
two distance-to-the-origin values. -/
theorem abs_infDist_zero_sub_le_rhoDistanceReal (τ : ℝ) (C D : Set E) :
    |infDist 0 C - infDist 0 D| ≤ rhoDistanceReal τ C D :=
  abs_infDist_sub_infDist_le_rhoDistance τ.toNNReal C D
    (mem_closedBall_self (by positivity))

/-- **Lemma 4.41(a).**  Stated for arbitrary sets: the proof uses only the
estimates of 4.37, which carry no nonemptiness hypothesis. -/
theorem integratedSetDistance_ge {ρ : ℝ} (hρ : 0 ≤ ρ) (C₁ C₂ : Set E) :
    (1 - Real.exp (-ρ)) * |infDist 0 C₁ - infDist 0 C₂|
        + Real.exp (-ρ) * rhoDistanceReal ρ C₁ C₂
      ≤ integratedSetDistance C₁ C₂ := by
  set Δ := |infDist 0 C₁ - infDist 0 C₂| with hΔ
  have hsplit := integral_Ioi_zero_split
    (f := fun τ : ℝ ↦ rhoDistanceReal τ C₁ C₂ * Real.exp (-τ)) hρ
    (integrableOn_rhoDistanceReal_mul_exp_neg_Ioc ρ C₁ C₂)
    (integrableOn_rhoDistanceReal_mul_exp_neg ρ C₁ C₂)
  have hnear : Δ * (1 - Real.exp (-ρ))
      ≤ ∫ τ in Ioc (0 : ℝ) ρ, rhoDistanceReal τ C₁ C₂ * Real.exp (-τ) := by
    have hmono : ∫ τ in Ioc (0 : ℝ) ρ, Δ * Real.exp (-τ)
        ≤ ∫ τ in Ioc (0 : ℝ) ρ, rhoDistanceReal τ C₁ C₂ * Real.exp (-τ) := by
      refine setIntegral_mono_on
        (((integrableOn_exp_neg_Ioi 0).mono_set Ioc_subset_Ioi_self).const_mul Δ)
        (integrableOn_rhoDistanceReal_mul_exp_neg_Ioc ρ C₁ C₂)
        measurableSet_Ioc fun τ hτ ↦ ?_
      exact mul_le_mul_of_nonneg_right
        (abs_infDist_zero_sub_le_rhoDistanceReal τ C₁ C₂)
        (Real.exp_pos _).le
    rwa [integral_const_mul, integral_Ioc_exp_neg hρ] at hmono
  have hfar : rhoDistanceReal ρ C₁ C₂ * Real.exp (-ρ)
      ≤ ∫ τ in Ioi ρ, rhoDistanceReal τ C₁ C₂ * Real.exp (-τ) := by
    have hmono : ∫ τ in Ioi ρ, rhoDistanceReal ρ C₁ C₂ * Real.exp (-τ)
        ≤ ∫ τ in Ioi ρ, rhoDistanceReal τ C₁ C₂ * Real.exp (-τ) := by
      refine setIntegral_mono_on
        ((integrableOn_exp_neg_Ioi ρ).const_mul _)
        (integrableOn_rhoDistanceReal_mul_exp_neg ρ C₁ C₂)
        measurableSet_Ioi fun τ hτ ↦ ?_
      exact mul_le_mul_of_nonneg_right
        (rhoDistanceReal_mono hτ.le C₁ C₂) (Real.exp_pos _).le
    rwa [integral_const_mul, integral_exp_neg_Ioi] at hmono
  rw [integratedSetDistance, hsplit]
  nlinarith [hnear, hfar]

/-- **Lemma 4.41(b).** -/
theorem integratedSetDistance_le {ρ : ℝ} (hρ : 0 ≤ ρ) (C₁ C₂ : Set E) :
    integratedSetDistance C₁ C₂
      ≤ (1 - Real.exp (-ρ)) * rhoDistanceReal ρ C₁ C₂
        + Real.exp (-ρ) * (max (infDist 0 C₁) (infDist 0 C₂) + ρ + 1) := by
  set M := max (infDist 0 C₁) (infDist 0 C₂) with hM
  have hsplit := integral_Ioi_zero_split
    (f := fun τ : ℝ ↦ rhoDistanceReal τ C₁ C₂ * Real.exp (-τ)) hρ
    (integrableOn_rhoDistanceReal_mul_exp_neg_Ioc ρ C₁ C₂)
    (integrableOn_rhoDistanceReal_mul_exp_neg ρ C₁ C₂)
  have haffine : IntegrableOn (fun τ : ℝ ↦ (M + τ) * Real.exp (-τ)) (Ioi ρ) := by
    refine integrableOn_mul_exp_neg_of_abs_le_affine (M := |M|) ρ (abs_nonneg M)
      (continuous_const.add continuous_id) fun x hx ↦ ?_
    calc |M + x| ≤ |M| + |x| := abs_add_le _ _
      _ = |M| + x := by rw [abs_of_nonneg hx]
  have hnear : (∫ τ in Ioc (0 : ℝ) ρ, rhoDistanceReal τ C₁ C₂ * Real.exp (-τ))
      ≤ rhoDistanceReal ρ C₁ C₂ * (1 - Real.exp (-ρ)) := by
    have hmono : ∫ τ in Ioc (0 : ℝ) ρ, rhoDistanceReal τ C₁ C₂ * Real.exp (-τ)
        ≤ ∫ τ in Ioc (0 : ℝ) ρ, rhoDistanceReal ρ C₁ C₂ * Real.exp (-τ) := by
      refine setIntegral_mono_on
        (integrableOn_rhoDistanceReal_mul_exp_neg_Ioc ρ C₁ C₂)
        (((integrableOn_exp_neg_Ioi 0).mono_set Ioc_subset_Ioi_self).const_mul _)
        measurableSet_Ioc fun τ hτ ↦ ?_
      exact mul_le_mul_of_nonneg_right
        (rhoDistanceReal_mono hτ.2 C₁ C₂) (Real.exp_pos _).le
    rwa [integral_const_mul, integral_Ioc_exp_neg hρ] at hmono
  have hfar : (∫ τ in Ioi ρ, rhoDistanceReal τ C₁ C₂ * Real.exp (-τ))
      ≤ (M + ρ + 1) * Real.exp (-ρ) := by
    have hmono : ∫ τ in Ioi ρ, rhoDistanceReal τ C₁ C₂ * Real.exp (-τ)
        ≤ ∫ τ in Ioi ρ, (M + τ) * Real.exp (-τ) := by
      refine setIntegral_mono_on
        (integrableOn_rhoDistanceReal_mul_exp_neg ρ C₁ C₂) haffine
        measurableSet_Ioi fun τ hτ ↦ ?_
      exact mul_le_mul_of_nonneg_right
        (rhoDistanceReal_le_max_infDist_zero_add (hρ.trans hτ.le) C₁ C₂)
        (Real.exp_pos _).le
    rwa [integral_Ioi_affine_mul_exp_neg] at hmono
  rw [integratedSetDistance, hsplit]
  nlinarith [hnear, hfar]

/-- **Lemma 4.41(c)**, lower half. -/
theorem abs_infDist_zero_sub_le_integratedSetDistance (C₁ C₂ : Set E) :
    |infDist 0 C₁ - infDist 0 C₂| ≤ integratedSetDistance C₁ C₂ := by
  set Δ := |infDist 0 C₁ - infDist 0 C₂| with hΔ
  have hmono : ∫ τ in Ioi (0 : ℝ), Δ * Real.exp (-τ)
      ≤ ∫ τ in Ioi (0 : ℝ), rhoDistanceReal τ C₁ C₂ * Real.exp (-τ) := by
    refine setIntegral_mono_on
      ((integrableOn_exp_neg_Ioi 0).const_mul Δ)
      (integrableOn_rhoDistanceReal_mul_exp_neg 0 C₁ C₂)
      measurableSet_Ioi fun τ hτ ↦ ?_
    exact mul_le_mul_of_nonneg_right
      (abs_infDist_zero_sub_le_rhoDistanceReal τ C₁ C₂) (Real.exp_pos _).le
  rwa [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one,
    ← integratedSetDistance] at hmono

/-- **Lemma 4.41(c)**, upper half. -/
theorem integratedSetDistance_le_max_infDist_zero_add_one (C₁ C₂ : Set E) :
    integratedSetDistance C₁ C₂
      ≤ max (infDist 0 C₁) (infDist 0 C₂) + 1 := by
  have h := integratedSetDistance_le (ρ := 0) le_rfl C₁ C₂
  simpa using h

/-- Formula 4(13): the integrated set distance never exceeds the
Pompeiu--Hausdorff distance, because `∫₀^∞ e^{-ρ} dρ = 1`. -/
theorem integratedSetDistance_le_hausdorffDist {C D : Set E}
    (hfin : hausdorffEDist C D ≠ ⊤) :
    integratedSetDistance C D ≤ hausdorffDist C D := by
  have hH : 0 ≤ hausdorffDist C D := hausdorffDist_nonneg
  have hrho : ∀ ρ : ℝ, rhoDistanceReal ρ C D ≤ hausdorffDist C D := by
    intro ρ
    rw [rhoDistanceReal, rhoDistance_le_iff hH]
    intro x _
    have h1 : infDist x D ≤ infDist x C + hausdorffDist C D :=
      infDist_le_infDist_add_hausdorffDist hfin
    have h2 : infDist x C ≤ infDist x D + hausdorffDist D C :=
      infDist_le_infDist_add_hausdorffDist
        (by rwa [hausdorffEDist_comm] at hfin)
    rw [hausdorffDist_comm] at h2
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  rw [integratedSetDistance]
  have hmono : (∫ ρ in Ioi (0 : ℝ), rhoDistanceReal ρ C D * Real.exp (-ρ))
      ≤ ∫ ρ in Ioi (0 : ℝ), hausdorffDist C D * Real.exp (-ρ) := by
    refine setIntegral_mono_on (integrableOn_rhoDistanceReal_mul_exp_neg 0 C D)
      ((integrableOn_exp_neg_Ioi 0).const_mul _) measurableSet_Ioi fun τ _ ↦ ?_
    exact mul_le_mul_of_nonneg_right (hrho τ) (Real.exp_pos _).le
  rwa [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one] at hmono

theorem integratedSetDistance_nonneg (C₁ C₂ : Set E) :
    0 ≤ integratedSetDistance C₁ C₂ :=
  le_trans (abs_nonneg _) (abs_infDist_zero_sub_le_integratedSetDistance C₁ C₂)

end Lemma441

section Theorem442

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem integratedSetDistance_self (C : Set E) :
    integratedSetDistance C C = 0 := by
  simp [integratedSetDistance, rhoDistanceReal_self]

theorem integratedSetDistance_comm (C D : Set E) :
    integratedSetDistance C D = integratedSetDistance D C := by
  simp_rw [integratedSetDistance, rhoDistanceReal_comm]

theorem integratedSetDistance_triangle (C₁ C₂ C₃ : Set E) :
    integratedSetDistance C₁ C₃
      ≤ integratedSetDistance C₁ C₂ + integratedSetDistance C₂ C₃ := by
  have h₁ := integrableOn_rhoDistanceReal_mul_exp_neg 0 C₁ C₂
  have h₂ := integrableOn_rhoDistanceReal_mul_exp_neg 0 C₂ C₃
  have h₃ := integrableOn_rhoDistanceReal_mul_exp_neg 0 C₁ C₃
  rw [integratedSetDistance, integratedSetDistance, integratedSetDistance,
    ← integral_add h₁ h₂]
  refine setIntegral_mono_on h₃ (h₁.add h₂) measurableSet_Ioi fun τ _ ↦ ?_
  have htri := rhoDistanceReal_triangle τ C₁ C₂ C₃
  have hexp : (0 : ℝ) < Real.exp (-τ) := Real.exp_pos _
  nlinarith

/-- Lemma 4.41(a) with its nonnegative first term discarded: each
`ρ`-distance is dominated by the integrated distance. -/
theorem exp_neg_mul_rhoDistanceReal_le {ρ : ℝ} (hρ : 0 ≤ ρ) (C₁ C₂ : Set E) :
    Real.exp (-ρ) * rhoDistanceReal ρ C₁ C₂ ≤ integratedSetDistance C₁ C₂ := by
  have h := integratedSetDistance_ge hρ C₁ C₂
  have hexp : Real.exp (-ρ) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  have hne : 0 ≤ (1 - Real.exp (-ρ)) * |infDist 0 C₁ - infDist 0 C₂| :=
    mul_nonneg (by linarith) (abs_nonneg _)
  linarith

theorem rhoDistanceReal_eq_zero_of_integratedSetDistance_eq_zero
    {C₁ C₂ : Set E} (h : integratedSetDistance C₁ C₂ = 0)
    {ρ : ℝ} (hρ : 0 ≤ ρ) :
    rhoDistanceReal ρ C₁ C₂ = 0 := by
  have hle := exp_neg_mul_rhoDistanceReal_le hρ C₁ C₂
  rw [h] at hle
  have hpos : (0 : ℝ) < Real.exp (-ρ) := Real.exp_pos _
  have hnn := rhoDistanceReal_nonneg ρ C₁ C₂
  nlinarith

/-- Separation clause of Theorem 4.42: on closed nonempty sets the
integrated distance vanishes only on the diagonal. -/
theorem eq_of_integratedSetDistance_eq_zero {C D : Set E}
    (hC : IsClosed C) (hD : IsClosed D) (hCne : C.Nonempty) (hDne : D.Nonempty)
    (h : integratedSetDistance C D = 0) : C = D := by
  have hdist : ∀ x : E, infDist x C = infDist x D := by
    intro x
    have hx : x ∈ closedBall (0 : E) ((‖x‖₊ : ℝ≥0) : ℝ) := by
      simp [mem_closedBall, dist_zero_right]
    have hb := abs_infDist_sub_infDist_le_rhoDistance (‖x‖₊) C D hx
    have hz : rhoDistance (‖x‖₊) C D = 0 := by
      have hzz := rhoDistanceReal_eq_zero_of_integratedSetDistance_eq_zero h
        (ρ := ((‖x‖₊ : ℝ≥0) : ℝ)) (by positivity)
      rwa [rhoDistanceReal_coe] at hzz
    rw [hz] at hb
    exact sub_eq_zero.1 (abs_nonpos_iff.1 hb)
  ext x
  rw [hC.mem_iff_infDist_zero hCne, hD.mem_iff_infDist_zero hDne, hdist x]

/-- **Theorem 4.42**, convergence clause: the integrated set distance
metrizes Painleve--Kuratowski convergence. -/
theorem pkConverges_iff_tendsto_integratedSetDistance
    {Cseq : ℕ → Set E} {C : Set E} (hCclosed : IsClosed C)
    (hCne : C.Nonempty) (hCseqne : ∀ n, (Cseq n).Nonempty) :
    PKConverges Cseq C ↔
      Tendsto (fun n ↦ integratedSetDistance (Cseq n) C) atTop (nhds 0) := by
  rw [pkConverges_iff_tendsto_rhoDistance hCclosed hCne hCseqne]
  constructor
  · intro hrho
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨ρ, hρsmall, hρ0⟩ :
        ∃ ρ : ℝ, (infDist (0 : E) C + 1 + ρ + 1) * Real.exp (-ρ) < ε / 2
          ∧ 0 ≤ ρ := by
      have hlim := tendsto_affine_mul_exp_neg_atTop (infDist (0 : E) C + 1)
      have hev := hlim.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 2))
      exact (hev.and (eventually_ge_atTop (0 : ℝ))).exists
    have h0 : ∀ᶠ n in atTop, rhoDistance 0 (Cseq n) C < 1 :=
      (hrho 0).eventually (gt_mem_nhds one_pos)
    have hρev : ∀ᶠ n in atTop,
        rhoDistance ρ.toNNReal (Cseq n) C < ε / 2 :=
      (hrho ρ.toNNReal).eventually
        (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 2))
    obtain ⟨N, hN⟩ := eventually_atTop.1 (h0.and hρev)
    refine ⟨N, fun n hn ↦ ?_⟩
    obtain ⟨hn0, hnρ⟩ := hN n hn
    have habs : |infDist 0 (Cseq n) - infDist 0 C|
        ≤ rhoDistanceReal 0 (Cseq n) C :=
      abs_infDist_zero_sub_le_rhoDistanceReal 0 (Cseq n) C
    have hn0' : rhoDistanceReal 0 (Cseq n) C < 1 := by
      rw [show (0 : ℝ) = ((0 : ℝ≥0) : ℝ) by norm_num, rhoDistanceReal_coe]
      exact hn0
    have hmax : max (infDist 0 (Cseq n)) (infDist 0 C)
        ≤ infDist (0 : E) C + 1 := by
      refine max_le ?_ (by linarith)
      have := abs_lt.1 (lt_of_le_of_lt habs hn0')
      linarith [this.2]
    have hb := integratedSetDistance_le hρ0 (Cseq n) C
    have hnρ' : rhoDistanceReal ρ (Cseq n) C < ε / 2 := hnρ
    have hexp : Real.exp (-ρ) ≤ 1 := by
      rw [Real.exp_le_one_iff]; linarith
    have hexppos : (0 : ℝ) < Real.exp (-ρ) := Real.exp_pos _
    have hrnn := rhoDistanceReal_nonneg ρ (Cseq n) C
    have hdlnn := integratedSetDistance_nonneg (Cseq n) C
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hdlnn]
    nlinarith
  · intro hdl ρ
    have hbound : ∀ n, rhoDistance ρ (Cseq n) C
        ≤ Real.exp ((ρ : ℝ)) * integratedSetDistance (Cseq n) C := by
      intro n
      have h := exp_neg_mul_rhoDistanceReal_le
        (ρ := (ρ : ℝ)) (by positivity) (Cseq n) C
      rw [rhoDistanceReal_coe] at h
      have hmul : Real.exp ((ρ : ℝ)) * Real.exp (-(ρ : ℝ)) = 1 := by
        rw [← Real.exp_add]; simp
      calc rhoDistance ρ (Cseq n) C
          = Real.exp ((ρ : ℝ)) *
              (Real.exp (-(ρ : ℝ)) * rhoDistance ρ (Cseq n) C) := by
            rw [← mul_assoc, hmul, one_mul]
        _ ≤ Real.exp ((ρ : ℝ)) * integratedSetDistance (Cseq n) C :=
            mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    have hlim : Tendsto
        (fun n ↦ Real.exp ((ρ : ℝ)) * integratedSetDistance (Cseq n) C)
        atTop (nhds 0) := by
      simpa using hdl.const_mul (Real.exp ((ρ : ℝ)))
    exact squeeze_zero (fun n ↦ rhoDistance_nonneg _ _ _) hbound hlim

/-- Escape to the horizon is exactly divergence of the distance to the
origin.  This is the hinge of the escape clause in Theorem 4.42. -/
theorem outerSetLimit_eq_empty_iff_tendsto_infDist_atTop
    {Cseq : ℕ → Set E} (hne : ∀ n, (Cseq n).Nonempty) :
    outerSetLimit Cseq = ∅ ↔
      Tendsto (fun n ↦ infDist (0 : E) (Cseq n)) atTop atTop := by
  rw [outerSetLimit_eq_empty_iff_eventually_disjoint_closedBall_zero]
  constructor
  · intro hmiss
    rw [Filter.tendsto_atTop]
    intro R
    filter_upwards [hmiss (max R 0 + 1) (by positivity)] with n hn
    have hle : max R 0 + 1 ≤ infDist (0 : E) (Cseq n) := by
      rw [le_infDist (hne n)]
      intro y hy
      by_contra hcon
      push_neg at hcon
      refine Set.disjoint_left.1 hn hy (mem_closedBall.2 ?_)
      rw [dist_comm]
      exact hcon.le
    have hRle : R ≤ max R 0 := le_max_left R 0
    linarith
  · intro htend ρ hρ
    filter_upwards [htend.eventually_ge_atTop (ρ + 1)] with n hn
    rw [Set.disjoint_left]
    intro y hy hyball
    have : infDist (0 : E) (Cseq n) ≤ ρ :=
      le_trans (infDist_le_dist_of_mem hy) (by simpa using hyball)
    linarith

/-- **Theorem 4.42**, escape clause: relative to any fixed reference set the
integrated distance diverges exactly when the sequence escapes. -/
theorem outerSetLimit_eq_empty_iff_tendsto_integratedSetDistance_atTop
    {Cseq : ℕ → Set E} {C : Set E} (hne : ∀ n, (Cseq n).Nonempty) :
    outerSetLimit Cseq = ∅ ↔
      Tendsto (fun n ↦ integratedSetDistance (Cseq n) C) atTop atTop := by
  rw [outerSetLimit_eq_empty_iff_tendsto_infDist_atTop hne]
  constructor
  · intro htend
    rw [Filter.tendsto_atTop]
    intro R
    filter_upwards [htend.eventually_ge_atTop (R + infDist (0 : E) C)] with n hn
    have h := abs_infDist_zero_sub_le_integratedSetDistance (Cseq n) C
    have h2 := le_abs_self (infDist (0 : E) (Cseq n) - infDist (0 : E) C)
    linarith
  · intro htend
    rw [Filter.tendsto_atTop]
    intro R
    filter_upwards [htend.eventually_ge_atTop
      (max R 0 + infDist (0 : E) C + 2)] with n hn
    have hub := integratedSetDistance_le_max_infDist_zero_add_one (Cseq n) C
    have hmax : max R 0 + infDist (0 : E) C + 2
        ≤ max (infDist (0 : E) (Cseq n)) (infDist (0 : E) C) + 1 :=
      le_trans hn hub
    have hR0 : (0 : ℝ) ≤ max R 0 := le_max_right R 0
    have hRle : R ≤ max R 0 := le_max_left R 0
    have hCnn : (0 : ℝ) ≤ infDist (0 : E) C := infDist_nonneg
    rcases le_total (infDist (0 : E) (Cseq n)) (infDist (0 : E) C) with hc | hc
    · rw [max_eq_right hc] at hmax; linarith
    · rw [max_eq_left hc] at hmax; linarith

end Theorem442

section HyperspaceMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The hyperspace `cl-sets≠∅(E)` carrying the integrated set metric `dl` of
Theorem 4.42.  A dedicated wrapper keeps this metric from colliding with the
`ρ`-pseudometrics of 4.36 on the same underlying type. -/
@[ext]
structure SetMetricModel (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] where
  toClosedNonemptySet : ClosedNonemptySet E

namespace SetMetricModel

/-- The underlying set of a point of the hyperspace. -/
def carrier (C : SetMetricModel E) : Set E := (C.toClosedNonemptySet : Set E)

theorem isClosed_carrier (C : SetMetricModel E) : IsClosed C.carrier :=
  C.toClosedNonemptySet.isClosed

theorem nonempty_carrier (C : SetMetricModel E) : C.carrier.Nonempty :=
  C.toClosedNonemptySet.nonempty

theorem carrier_injective : Function.Injective (carrier : SetMetricModel E → Set E) :=
  fun _ _ h ↦ SetMetricModel.ext (SetLike.coe_injective h)

/-- **Theorem 4.42**, metric clause. -/
noncomputable instance : MetricSpace (SetMetricModel E) where
  dist C D := integratedSetDistance C.carrier D.carrier
  dist_self C := integratedSetDistance_self _
  dist_comm C D := integratedSetDistance_comm _ _
  dist_triangle C D F := integratedSetDistance_triangle _ _ _
  eq_of_dist_eq_zero {C D} h :=
    carrier_injective (eq_of_integratedSetDistance_eq_zero C.isClosed_carrier
      D.isClosed_carrier C.nonempty_carrier D.nonempty_carrier h)

@[simp]
theorem dist_eq (C D : SetMetricModel E) :
    dist C D = integratedSetDistance C.carrier D.carrier := rfl

/-- **Theorem 4.42**, convergence clause in the metric space. -/
theorem tendsto_iff_pkConverges {u : ℕ → SetMetricModel E}
    {C : SetMetricModel E} :
    Tendsto u atTop (nhds C) ↔ PKConverges (fun n ↦ (u n).carrier) C.carrier := by
  rw [pkConverges_iff_tendsto_integratedSetDistance C.isClosed_carrier
    C.nonempty_carrier (fun n ↦ (u n).nonempty_carrier)]
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [dist_eq]

/-- Sequential compactness of the closed balls, proved from the escape
criterion of Theorem 4.42 together with the compactness Theorem 4.18. -/
theorem isSeqCompact_closedBall (C₀ : SetMetricModel E) (r : ℝ) :
    IsSeqCompact (Metric.closedBall C₀ r) := by
  intro u hu
  set Cseq : ℕ → Set E := fun n ↦ (u n).carrier with hCseqdef
  have hne : ∀ n, (Cseq n).Nonempty := fun n ↦ (u n).nonempty_carrier
  have hball : ∀ n, integratedSetDistance (Cseq n) C₀.carrier ≤ r := fun n ↦
    Metric.mem_closedBall.1 (hu n)
  have hbdd : ∀ n,
      infDist (0 : E) (Cseq n) ≤ infDist (0 : E) C₀.carrier + r := by
    intro n
    have h1 := abs_infDist_zero_sub_le_integratedSetDistance (Cseq n) C₀.carrier
    have h3 := le_abs_self (infDist (0 : E) (Cseq n) - infDist (0 : E) C₀.carrier)
    linarith [hball n]
  have houter : (outerSetLimit Cseq).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hempty
    have htend := (outerSetLimit_eq_empty_iff_tendsto_infDist_atTop hne).1 hempty
    obtain ⟨n, hn⟩ :=
      (htend.eventually_ge_atTop (infDist (0 : E) C₀.carrier + r + 1)).exists
    linarith [hbdd n]
  obtain ⟨φ, D, hφ, hDne, hconv⟩ :=
    exists_pkConvergent_subsequence_with_nonempty_limit houter
  set Dm : SetMetricModel E := ⟨⟨D, ⟨hconv.isClosed, hDne⟩⟩⟩ with hDm
  have htendsto : Tendsto (u ∘ φ) atTop (nhds Dm) :=
    SetMetricModel.tendsto_iff_pkConverges.2 hconv
  refine ⟨Dm, ?_, φ, hφ, htendsto⟩
  have hd : Tendsto (fun k ↦ dist ((u ∘ φ) k) C₀) atTop (nhds (dist Dm C₀)) :=
    htendsto.dist tendsto_const_nhds
  exact Metric.mem_closedBall.2
    (le_of_tendsto hd (Eventually.of_forall fun k ↦ hball (φ k)))

/-- **Corollary 4.43 (local compactness).**  Every closed ball of the
hyperspace `(cl-sets≠∅(E), dl)` is compact. -/
instance : ProperSpace (SetMetricModel E) :=
  ⟨fun C₀ r ↦ (isSeqCompact_closedBall C₀ r).isCompact⟩

/-- **Theorem 4.42**, completeness clause. -/
example : CompleteSpace (SetMetricModel E) := inferInstance

theorem completeSpace : CompleteSpace (SetMetricModel E) := inferInstance

end SetMetricModel

end HyperspaceMetric

end RW
