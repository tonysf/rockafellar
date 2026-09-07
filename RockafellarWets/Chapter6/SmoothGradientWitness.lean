/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: The Smooth Witness in the Gradient Characterization

`GradientNormals.lean` proves the differentiable half of Theorem 6.11 and
produces a witness that is differentiable only at the base point.  This file
supplies the strengthening printed after the statement: the witness may be
taken continuously differentiable on all of the ambient space, with its
*global* maximum relative to `C` attained at `x̄` alone.

The analytic content is the radial composite `y ↦ θ‖y - x̄‖`.  The norm is
smooth away from the origin but not at it, so a first-order argument is needed
exactly where the gradient is wanted; the composite survives because `θ` is
built with `θ'(0) = 0`.
-/

import RockafellarWets.Chapter6.GradientNormals
import RockafellarWets.Chapter6.SmoothMajorant
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Norm

open Asymptotics Filter Set Topology
open scoped InnerProductSpace

noncomputable section

namespace RW

section RadialComposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {theta : ℝ → ℝ}

omit [InnerProductSpace ℝ E] in
/-- A scalar function with vanishing derivative at the origin composes with the
norm to something of first order at the center.  This is the estimate that
makes the radial penalty of Theorem 6.11 invisible to the gradient. -/
theorem isLittleO_comp_norm_sub (hderiv : HasDerivAt theta 0 0) (x : E) :
    (fun y : E ↦ theta ‖y - x‖ - theta 0) =o[nhds x] fun y : E ↦ y - x := by
  have hscalar : (fun t : ℝ ↦ theta t - theta 0) =o[nhds (0 : ℝ)] fun t : ℝ ↦ t := by
    have hlo := hasDerivAt_iff_isLittleO.mp hderiv
    simpa using hlo
  have hto : Tendsto (fun y : E ↦ ‖y - x‖) (nhds x) (nhds 0) := by
    have hcont : Continuous fun y : E ↦ ‖y - x‖ :=
      (continuous_id.sub continuous_const).norm
    have := hcont.tendsto x
    simpa using this
  have hcomp := hscalar.comp_tendsto hto
  have hdom : (fun y : E ↦ ‖y - x‖) =O[nhds x] fun y : E ↦ y - x :=
    isBigO_of_le _ fun y ↦ by simp
  exact hcomp.trans_isBigO hdom

/-- The radial penalty has zero derivative at its center. -/
theorem hasFDerivAt_comp_norm_sub (hderiv : HasDerivAt theta 0 0) (x : E) :
    HasFDerivAt (fun y : E ↦ theta ‖y - x‖) (0 : E →L[ℝ] ℝ) x := by
  apply HasFDerivAtFilter.of_isLittleO
  simpa using isLittleO_comp_norm_sub hderiv x

/-- Away from the center the composite differentiates by the chain rule. -/
theorem hasFDerivAt_comp_norm_of_ne (htheta : ContDiff ℝ 1 theta) {z : E} (hz : z ≠ 0) :
    HasFDerivAt (fun w : E ↦ theta ‖w‖)
      (deriv theta ‖z‖ • fderiv ℝ (‖·‖ : E → ℝ) z) z := by
  have hnormdiff : DifferentiableAt ℝ (‖·‖ : E → ℝ) z :=
    (contDiffAt_norm (n := 1) ℝ hz).differentiableAt one_ne_zero
  have hth : HasDerivAt theta (deriv theta ‖z‖) ‖z‖ :=
    (htheta.differentiable one_ne_zero ‖z‖).hasDerivAt
  exact hth.comp_hasFDerivAt z hnormdiff.hasFDerivAt

/-- The derivative of a radial composite is controlled by the scalar
derivative alone, because the norm is `1`-Lipschitz with derivatives of
operator norm exactly one. -/
theorem norm_fderiv_comp_norm_le (htheta : ContDiff ℝ 1 theta)
    (hderiv : HasDerivAt theta 0 0) (z : E) :
    ‖fderiv ℝ (fun w : E ↦ theta ‖w‖) z‖ ≤ |deriv theta ‖z‖| := by
  rcases subsingleton_or_nontrivial E with _ | _
  · have hzz : z = 0 := Subsingleton.elim z 0
    have hconst : (fun w : E ↦ theta ‖w‖) = fun _ : E ↦ theta 0 := by
      funext w
      rw [Subsingleton.elim w (0 : E), norm_zero]
    rw [hconst]
    simp [hzz, hderiv.deriv]
  rcases eq_or_ne z 0 with rfl | hz
  · have hfd : HasFDerivAt (fun w : E ↦ theta ‖w‖) (0 : E →L[ℝ] ℝ) (0 : E) := by
      have h0 := hasFDerivAt_comp_norm_sub hderiv (0 : E)
      simpa using h0
    rw [hfd.fderiv]
    simp [hderiv.deriv]
  · have hnormdiff : DifferentiableAt ℝ (‖·‖ : E → ℝ) z :=
      (contDiffAt_norm (n := 1) ℝ hz).differentiableAt one_ne_zero
    rw [(hasFDerivAt_comp_norm_of_ne htheta hz).fderiv, norm_smul,
      norm_fderiv_norm hnormdiff]
    simp

/-- **The radial composition lemma.**  A `C¹` scalar function whose derivative
vanishes at the origin composes with the norm to a function that is `C¹` on the
whole space, singularity of the norm at the origin notwithstanding. -/
theorem contDiff_one_comp_norm (htheta : ContDiff ℝ 1 theta)
    (hderiv : HasDerivAt theta 0 0) : ContDiff ℝ 1 fun z : E ↦ theta ‖z‖ := by
  rcases subsingleton_or_nontrivial E with _ | _
  · have hconst : (fun z : E ↦ theta ‖z‖) = fun _ : E ↦ theta 0 := by
      funext z
      rw [Subsingleton.elim z (0 : E), norm_zero]
    rw [hconst]
    exact contDiff_const
  have hderivCont : Continuous (deriv theta) := (contDiff_one_iff_deriv.mp htheta).2
  have hcenter : HasFDerivAt (fun z : E ↦ theta ‖z‖) (0 : E →L[ℝ] ℝ) (0 : E) := by
    have h0 := hasFDerivAt_comp_norm_sub hderiv (0 : E)
    simpa using h0
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun z ↦ ?_, continuous_iff_continuousAt.mpr fun z ↦ ?_⟩
  · rcases eq_or_ne z 0 with rfl | hz
    · exact hcenter.differentiableAt
    · exact (hasFDerivAt_comp_norm_of_ne htheta hz).differentiableAt
  · rcases eq_or_ne z 0 with rfl | hz
    · have hg : Tendsto (fun w : E ↦ |deriv theta ‖w‖|) (nhds 0) (nhds 0) := by
        have hc : Continuous fun w : E ↦ |deriv theta ‖w‖| :=
          (hderivCont.comp continuous_norm).abs
        have hct := hc.tendsto (0 : E)
        simpa [hderiv.deriv] using hct
      have hsq : Tendsto (fun w : E ↦ ‖fderiv ℝ (fun u : E ↦ theta ‖u‖) w‖)
          (nhds 0) (nhds 0) :=
        squeeze_zero (fun w ↦ norm_nonneg _)
          (fun w ↦ norm_fderiv_comp_norm_le htheta hderiv w) hg
      have hlim : Tendsto (fun w : E ↦ fderiv ℝ (fun u : E ↦ theta ‖u‖) w)
          (nhds 0) (nhds 0) := tendsto_zero_iff_norm_tendsto_zero.mpr hsq
      have hval : fderiv ℝ (fun u : E ↦ theta ‖u‖) (0 : E) = 0 := hcenter.fderiv
      rw [ContinuousAt, hval]
      exact hlim
    · have hcd : ContDiffAt ℝ 1 (fun w : E ↦ theta ‖w‖) z :=
        htheta.contDiffAt.comp z (contDiffAt_norm ℝ hz)
      exact hcd.continuousAt_fderiv one_ne_zero

/-- The radial composition lemma centered at an arbitrary point. -/
theorem contDiff_one_comp_norm_sub (htheta : ContDiff ℝ 1 theta)
    (hderiv : HasDerivAt theta 0 0) (x : E) :
    ContDiff ℝ 1 fun y : E ↦ theta ‖y - x‖ :=
  (contDiff_one_comp_norm htheta hderiv).comp (contDiff_id.sub contDiff_const)

end RadialComposition

section Modulus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {C : Set E} {x v y : E}

/-- The modulus `θ₀` of the proof of Theorem 6.11: the largest value of
`⟪v, y - x̄⟫` over the points of `C` within distance `r` of `x̄`.  At a negative
radius the indexing set is empty and the supremum is `0`, which is also the
value at `r = 0`, so no separate branch is needed. -/
def normalModulus (C : Set E) (x v : E) (r : ℝ) : ℝ :=
  sSup ((fun y ↦ ⟪v, y - x⟫_ℝ) '' (C ∩ Metric.closedBall x r))

/-- Cauchy--Schwarz bounds the modulus set by `r‖v‖`. -/
theorem bddAbove_image_inner_closedBall (C : Set E) (x v : E) (r : ℝ) :
    BddAbove ((fun y ↦ ⟪v, y - x⟫_ℝ) '' (C ∩ Metric.closedBall x r)) := by
  refine ⟨‖v‖ * r, ?_⟩
  rintro t ⟨y, ⟨-, hy⟩, rfl⟩
  have hyr : ‖y - x‖ ≤ r := by
    rw [← dist_eq_norm]
    exact Metric.mem_closedBall.mp hy
  calc
    ⟪v, y - x⟫_ℝ ≤ ‖v‖ * ‖y - x‖ := real_inner_le_norm v (y - x)
    _ ≤ ‖v‖ * r := mul_le_mul_of_nonneg_left hyr (norm_nonneg v)

/-- The base point itself contributes the value `0` at every nonnegative
radius. -/
theorem normalModulus_nonneg (hx : x ∈ C) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ normalModulus C x v r :=
  le_csSup (bddAbove_image_inner_closedBall C x v r)
    ⟨x, ⟨hx, Metric.mem_closedBall_self hr⟩, by simp⟩

theorem normalModulus_zero (hx : x ∈ C) : normalModulus C x v 0 = 0 := by
  rw [normalModulus, Metric.closedBall_zero,
    Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr hx), Set.image_singleton]
  simp

theorem monotoneOn_normalModulus (hx : x ∈ C) :
    MonotoneOn (normalModulus C x v) (Ici 0) := by
  intro a ha b _ hab
  refine csSup_le_csSup (bddAbove_image_inner_closedBall C x v b)
    ⟨0, x, ⟨hx, Metric.mem_closedBall_self ha⟩, by simp⟩ ?_
  exact Set.image_mono
    (Set.inter_subset_inter_right _ (Metric.closedBall_subset_closedBall hab))

/-- The defining domination property: the modulus at radius `‖y - x̄‖`
dominates the pairing at `y`. -/
theorem inner_le_normalModulus (hy : y ∈ C) :
    ⟪v, y - x⟫_ℝ ≤ normalModulus C x v ‖y - x‖ :=
  le_csSup (bddAbove_image_inner_closedBall C x v _)
    ⟨y, ⟨hy, Metric.mem_closedBall.mpr (le_of_eq (dist_eq_norm y x))⟩, rfl⟩

/-- Being a regular normal says exactly that the modulus is of first order at
the origin. -/
theorem tendsto_normalModulus_div (hv : v ∈ regularNormalCone C x) :
    Tendsto (fun r : ℝ ↦ normalModulus C x v r / r) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  obtain ⟨hxC, hprop⟩ := mem_regularNormalCone_iff.mp hv
  rw [NormedAddCommGroup.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨δ, hδ, hδprop⟩ := hprop (ε / 2) (by positivity)
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  have hrpos : 0 < r := hr.1
  have hupper : normalModulus C x v r ≤ ε / 2 * r := by
    refine csSup_le ⟨0, x, ⟨hxC, Metric.mem_closedBall_self hrpos.le⟩, by simp⟩ ?_
    rintro t ⟨z, ⟨hzC, hzb⟩, rfl⟩
    have hzr : ‖z - x‖ ≤ r := by
      rw [← dist_eq_norm]
      exact Metric.mem_closedBall.mp hzb
    calc
      ⟪v, z - x⟫_ℝ ≤ ε / 2 * ‖z - x‖ := hδprop z hzC (lt_of_le_of_lt hzr hr.2)
      _ ≤ ε / 2 * r := mul_le_mul_of_nonneg_left hzr (by positivity)
  have hlower : 0 ≤ normalModulus C x v r := normalModulus_nonneg hxC hrpos.le
  have hdiv : normalModulus C x v r / r ≤ ε / 2 :=
    (div_le_iff₀ hrpos).mpr hupper
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hlower hrpos.le)]
  linarith

end Modulus

section SmoothWitness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {C : Set E} {x v : E}

/-- **Theorem 6.11**, the strengthened witness clause: a regular normal is the
gradient of a function that is continuously differentiable on the whole space
and attains its global maximum relative to `C` at the base point alone. -/
theorem exists_contDiff_one_hasGradientAt_unique_isMaxOn_of_mem_regularNormalCone
    (hv : v ∈ regularNormalCone C x) :
    ∃ h : E → ℝ,
      ContDiff ℝ 1 h ∧
      HasGradientAt h v x ∧
      IsMaxOn h C x ∧
      ∀ y ∈ C, h y = h x → y = x := by
  have hxC : x ∈ C := hv.1
  obtain ⟨θ, hθC1, hθzero, hθderiv, hθstrict, -, -⟩ :=
    exists_contDiff_one_strict_majorant (monotoneOn_normalModulus (v := v) hxC)
      (normalModulus_zero hxC) (tendsto_normalModulus_div hv)
  let h : E → ℝ := fun y ↦ ⟪v, y - x⟫_ℝ - θ ‖y - x‖
  have hhx : h x = 0 := by simp [h, hθzero]
  have hlt : ∀ y ∈ C, y ≠ x → h y < h x := by
    intro y hyC hyne
    have hpos : 0 < ‖y - x‖ := by
      rw [norm_pos_iff, sub_ne_zero]
      exact hyne
    have h1 : ⟪v, y - x⟫_ℝ ≤ normalModulus C x v ‖y - x‖ := inner_le_normalModulus hyC
    have h2 : normalModulus C x v ‖y - x‖ < θ ‖y - x‖ := hθstrict _ hpos
    rw [hhx]
    simp only [h]
    linarith
  refine ⟨h, ?_, ?_, ?_, ?_⟩
  · have hlin : ContDiff ℝ 1 fun y : E ↦ ⟪v, y - x⟫_ℝ := by
      have hcomp : ContDiff ℝ 1 fun y : E ↦ (innerSL ℝ v) (y - x) :=
        (innerSL ℝ v).contDiff.comp (contDiff_id.sub contDiff_const)
      exact hcomp
    exact hlin.sub (contDiff_one_comp_norm_sub hθC1 hθderiv x)
  · rw [hasGradientAt_iff_isLittleO]
    refine (isLittleO_comp_norm_sub hθderiv x).neg_left.congr_left ?_
    intro y
    simp only [h, hhx]
    simp [hθzero]
  · rw [isMaxOn_iff]
    intro y hyC
    rcases eq_or_ne y x with rfl | hyne
    · exact le_rfl
    · exact (hlt y hyC hyne).le
  · intro y hyC heq
    by_contra hyne
    exact absurd heq (ne_of_lt (hlt y hyC hyne))

/-- **Theorem 6.11** in full: the smooth-witness characterization of regular
normals.  Feasibility of the base point is stated explicitly because
`IsMaxOn` does not require it. -/
theorem mem_regularNormalCone_iff_exists_contDiff_one_unique_isMaxOn_hasGradientAt
    (hx : x ∈ C) :
    v ∈ regularNormalCone C x ↔
      ∃ h : E → ℝ,
        ContDiff ℝ 1 h ∧
        IsMaxOn h C x ∧
        (∀ y ∈ C, h y = h x → y = x) ∧
        HasGradientAt h v x := by
  constructor
  · intro hv
    obtain ⟨h, hC1, hgrad, hmax, huniq⟩ :=
      exists_contDiff_one_hasGradientAt_unique_isMaxOn_of_mem_regularNormalCone hv
    exact ⟨h, hC1, hmax, huniq, hgrad⟩
  · rintro ⟨h, -, hmax, -, hgrad⟩
    exact mem_regularNormalCone_of_isLocalMaxOn_hasGradientAt hx hmax.localize hgrad

end SmoothWitness

end RW
