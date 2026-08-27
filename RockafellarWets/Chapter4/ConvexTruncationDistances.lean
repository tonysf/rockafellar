/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Distances Between Convex Truncations

This file proves Proposition 4.39, comparing the localized inclusion
distance with the Pompeiu--Hausdorff distance between ball truncations.
-/

import RockafellarWets.Chapter4.LocalSetDistances

open Bornology Metric Set
open scoped ENNReal NNReal

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem infDist_inter_closedBall_le_four_mul
    {C : Set E} (hCclosed : IsClosed C) (hCne : C.Nonempty)
    (hCconv : Convex ℝ C) {r r₀ e : ℝ} (hr₀ : 0 ≤ r₀) (he : 0 ≤ e)
    (hr : 2 * r₀ < r) (hzero : infDist 0 C ≤ r₀)
    {x : E} (hx : x ∈ closedBall (0 : E) r) (hxC : infDist x C ≤ e) :
    infDist x (C ∩ closedBall (0 : E) r) ≤ 4 * e := by
  rcases hCclosed.exists_infDist_eq_dist hCne 0 with ⟨x₀, hx₀C, hx₀dist⟩
  rcases hCclosed.exists_infDist_eq_dist hCne x with ⟨x₁, hx₁C, hx₁dist⟩
  have hx₀norm : ‖x₀‖ ≤ r₀ := by
    rw [← dist_zero_left]
    linarith
  have hxx₁ : dist x x₁ ≤ e := by linarith
  have hx₁norm : ‖x₁‖ ≤ r + e := by
    rw [← dist_zero_left]
    calc
      dist 0 x₁ ≤ dist 0 x + dist x x₁ := dist_triangle _ _ _
      _ ≤ r + e := by
        rw [mem_closedBall, dist_comm x 0] at hx
        linarith
  let δ : ℝ := r - r₀
  let den : ℝ := δ + e
  have hδpos : 0 < δ := by
    dsimp only [δ]
    linarith
  have hdenpos : 0 < den := by
    dsimp only [den]
    linarith
  let q : ℝ := e / den
  have hqnonneg : 0 ≤ q := div_nonneg he hdenpos.le
  have hqle : q ≤ 1 := by
    apply (div_le_one hdenpos).2
    dsimp only [den, δ]
    linarith
  let xbar : E := q • x₀ + (1 - q) • x₁
  have hxbarC : xbar ∈ C :=
    hCconv hx₀C hx₁C hqnonneg (sub_nonneg.mpr hqle) (by ring)
  have hxbarNorm : ‖xbar‖ ≤ r := by
    calc
      ‖xbar‖ ≤ ‖q • x₀‖ + ‖(1 - q) • x₁‖ := by
        dsimp only [xbar]
        exact norm_add_le _ _
      _ = q * ‖x₀‖ + (1 - q) * ‖x₁‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg hqnonneg, abs_of_nonneg (sub_nonneg.mpr hqle)]
      _ ≤ q * r₀ + (1 - q) * (r + e) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hx₀norm hqnonneg)
          (mul_le_mul_of_nonneg_left hx₁norm (sub_nonneg.mpr hqle))
      _ = r := by
        have hqden : q * den = e := by
          dsimp only [q]
          exact div_mul_cancel₀ e hdenpos.ne'
        dsimp only [den, δ] at hqden
        nlinarith
  have hxbarBall : xbar ∈ closedBall (0 : E) r := by
    simpa only [mem_closedBall, dist_zero_right] using hxbarNorm
  have hdist₁ : dist x₁ xbar ≤ 3 * e := by
    have hsub : x₁ - xbar = q • (x₁ - x₀) := by
      dsimp only [xbar]
      module
    have hraw : dist x₁ xbar ≤ q * (r + e + r₀) := by
      rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hqnonneg]
      calc
        q * ‖x₁ - x₀‖ ≤ q * (‖x₁‖ + ‖x₀‖) := by
          gcongr
          exact norm_sub_le _ _
        _ ≤ q * (r + e + r₀) := by gcongr
    calc
      dist x₁ xbar ≤ q * (r + e + r₀) := hraw
      _ ≤ q * (3 * den) := by
        gcongr
        dsimp only [den, δ]
        linarith
      _ = 3 * e := by
        have hqden : q * den = e := by
          dsimp only [q]
          exact div_mul_cancel₀ e hdenpos.ne'
        nlinarith
  calc
    infDist x (C ∩ closedBall (0 : E) r) ≤ dist x xbar :=
      infDist_le_dist_of_mem ⟨hxbarC, hxbarBall⟩
    _ ≤ dist x x₁ + dist x₁ xbar := dist_triangle _ _ _
    _ ≤ 4 * e := by linarith

private theorem inter_closedBall_nonempty_of_infDist_zero_lt
    {C : Set E} (hCclosed : IsClosed C) (hCne : C.Nonempty)
    {r r₀ : ℝ} (hzero : infDist 0 C ≤ r₀) (hr : r₀ < r) :
    (C ∩ closedBall (0 : E) r).Nonempty := by
  rcases hCclosed.exists_infDist_eq_dist hCne 0 with ⟨x, hxC, hx⟩
  refine ⟨x, hxC, ?_⟩
  rw [mem_closedBall, dist_zero_right, ← dist_zero_left]
  linarith

/-- Proposition 4.39.  For closed nonempty convex sets, the Hausdorff
distance between equal-radius truncations lies between the localized
inclusion distance and four times that distance. -/
theorem rhoHatDistance_le_hausdorffDist_truncations_le_four_mul
    (r : ℝ≥0) {C D : Set E} (hCclosed : IsClosed C) (hDclosed : IsClosed D)
    (hCne : C.Nonempty) (hDne : D.Nonempty)
    (hCconv : Convex ℝ C) (hDconv : Convex ℝ D)
    (hr : 2 * max (infDist 0 C) (infDist 0 D) < (r : ℝ)) :
    rhoHatDistance r C D ≤
        hausdorffDist (C ∩ closedBall (0 : E) (r : ℝ))
          (D ∩ closedBall (0 : E) (r : ℝ)) ∧
      hausdorffDist (C ∩ closedBall (0 : E) (r : ℝ))
          (D ∩ closedBall (0 : E) (r : ℝ)) ≤
        4 * rhoHatDistance r C D := by
  let r₀ : ℝ := max (infDist 0 C) (infDist 0 D)
  have hr₀nonneg : 0 ≤ r₀ := by
    exact (show 0 ≤ infDist (0 : E) C from infDist_nonneg).trans (le_max_left _ _)
  have hCr₀ : infDist 0 C ≤ r₀ := le_max_left _ _
  have hDr₀ : infDist 0 D ≤ r₀ := le_max_right _ _
  have hr' : 2 * r₀ < (r : ℝ) := hr
  have hr₀r : r₀ < (r : ℝ) := by linarith
  let A : Set E := C ∩ closedBall (0 : E) (r : ℝ)
  let B : Set E := D ∩ closedBall (0 : E) (r : ℝ)
  have hAne : A.Nonempty :=
    inter_closedBall_nonempty_of_infDist_zero_lt hCclosed hCne hCr₀ hr₀r
  have hBne : B.Nonempty :=
    inter_closedBall_nonempty_of_infDist_zero_lt hDclosed hDne hDr₀ hr₀r
  have hAbounded : IsBounded A :=
    (isBounded_closedBall : IsBounded (closedBall (0 : E) (r : ℝ))).subset inter_subset_right
  have hBbounded : IsBounded B :=
    (isBounded_closedBall : IsBounded (closedBall (0 : E) (r : ℝ))).subset inter_subset_right
  have hfinite : hausdorffEDist A B ≠ ⊤ :=
    hausdorffEDist_ne_top_of_nonempty_of_bounded hAne hBne hAbounded hBbounded
  let H : ℝ := hausdorffDist A B
  have hHnonneg : 0 ≤ H := hausdorffDist_nonneg
  have hlower : rhoHatDistance r C D ≤ H := by
    apply (rhoHatDistance_le_iff r hCne hDne hHnonneg).2
    constructor
    · intro x hx
      rw [mem_cthickening_iff]
      apply (ENNReal.le_ofReal_iff_toReal_le (infEDist_ne_top hDne) hHnonneg).2
      calc
        infDist x D ≤ infDist x B :=
          infDist_le_infDist_of_subset inter_subset_left hBne
        _ ≤ H := infDist_le_hausdorffDist_of_mem hx hfinite
    · intro x hx
      rw [mem_cthickening_iff]
      apply (ENNReal.le_ofReal_iff_toReal_le (infEDist_ne_top hCne) hHnonneg).2
      calc
        infDist x C ≤ infDist x A :=
          infDist_le_infDist_of_subset inter_subset_left hAne
        _ ≤ H := by
          change infDist x A ≤ hausdorffDist A B
          rw [hausdorffDist_comm]
          exact infDist_le_hausdorffDist_of_mem hx (by
            rwa [hausdorffEDist_comm])
  have he : 0 ≤ rhoHatDistance r C D := rhoHatDistance_nonneg r C D
  have hincl := (rhoHatDistance_le_iff r hCne hDne he).1 le_rfl
  have hupper : H ≤ 4 * rhoHatDistance r C D := by
    apply hausdorffDist_le_of_infDist (mul_nonneg (by norm_num) he)
    · intro x hxA
      have hxD : infDist x D ≤ rhoHatDistance r C D := by
        apply (ENNReal.le_ofReal_iff_toReal_le (infEDist_ne_top hDne) he).1
        rw [← mem_cthickening_iff]
        exact hincl.1 hxA
      exact infDist_inter_closedBall_le_four_mul hDclosed hDne hDconv
        hr₀nonneg he hr' hDr₀ hxA.2 hxD
    · intro x hxB
      have hxC : infDist x C ≤ rhoHatDistance r C D := by
        apply (ENNReal.le_ofReal_iff_toReal_le (infEDist_ne_top hCne) he).1
        rw [← mem_cthickening_iff]
        exact hincl.2 hxB
      exact infDist_inter_closedBall_le_four_mul hCclosed hCne hCconv
        hr₀nonneg he hr' hCr₀ hxB.2 hxC
  exact ⟨hlower, hupper⟩

end RW
