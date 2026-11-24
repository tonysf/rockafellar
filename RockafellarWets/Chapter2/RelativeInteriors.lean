/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 2H: Relative interiors of convex sets

This file formalizes Section H of Chapter 2 of Rockafellar–Wets in
finite-dimensional real normed spaces, with `rint C = intrinsicInterior ℝ C`
(Mathlib's interior of `C` relative to its affine hull).  The basic tools, the
ball description of `rint` and the relative line segment principle, are the
normed-space versions of the Chapter 12 lemmas `mem_intrinsicInterior_iff_ball`
and `Convex.add_smul_sub_mem_intrinsicInterior`; the normed setting covers the
product spaces `ℝⁿ × ℝᵐ` of 2.43–2.45.

* Proposition 2.40: `rint C` is nonempty and convex, `cl(rint C) = cl C`,
  `rint(cl C) = rint C`, and `rint[x₀, x₁] ⊆ rint C`.
* Exercise 2.41: the segment criterion for relative interior points.
* Proposition 2.42: relative interiors and closures of intersections.
-/

import RockafellarWets.Chapter2.SeparationTheorem
import Mathlib.Analysis.Convex.Intrinsic

open Set Filter Topology Metric
open scoped Pointwise

noncomputable section

namespace RW

section Basic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The relative interior through balls in the affine hull. -/
theorem mem_intrinsicInterior_iff_ball_normed {s : Set E} {z : E} :
    z ∈ intrinsicInterior ℝ s ↔
      z ∈ s ∧ ∃ r > 0, ∀ y ∈ affineSpan ℝ s, dist y z < r → y ∈ s := by
  constructor
  · intro hz
    obtain ⟨p, hp, rfl⟩ := mem_intrinsicInterior.1 hz
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hp)
    refine ⟨(interior_subset hp : p ∈ ((↑) ⁻¹' s : Set (affineSpan ℝ s))), r, hr,
      fun y hy hyz ↦ ?_⟩
    have hmem : (⟨y, hy⟩ : affineSpan ℝ s) ∈ ball p r := by
      rw [mem_ball, Subtype.dist_eq]
      exact hyz
    exact hball hmem
  · rintro ⟨hz, r, hr, hball⟩
    refine mem_intrinsicInterior.2 ⟨⟨z, subset_affineSpan ℝ s hz⟩, ?_, rfl⟩
    refine mem_interior_iff_mem_nhds.2 (Metric.mem_nhds_iff.2 ⟨r, hr, fun q hq ↦ ?_⟩)
    rw [mem_ball, Subtype.dist_eq] at hq
    exact hball q q.2 hq

theorem lineMap_eq_add_smul (x₀ x₁ : E) (c : ℝ) :
    AffineMap.lineMap x₀ x₁ c = x₀ + c • (x₁ - x₀) := by
  rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm]

/-- From a relative interior point one can move a little beyond it, away from
any other point of the set. -/
theorem exists_add_smul_sub_mem_of_mem_intrinsicInterior {C : Set E} {z z₀ : E}
    (hz : z ∈ intrinsicInterior ℝ C) (hz₀ : z₀ ∈ C) :
    ∃ ε : ℝ, 0 < ε ∧ z + ε • (z - z₀) ∈ C := by
  obtain ⟨hzC, r, hr, hball⟩ := mem_intrinsicInterior_iff_ball_normed.1 hz
  by_cases hzz : z = z₀
  · exact ⟨1, one_pos, by rw [hzz, sub_self, smul_zero, add_zero]; exact hz₀⟩
  have hn : 0 < ‖z - z₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzz)
  set ε := r / (2 * ‖z - z₀‖) with hε
  have hεpos : 0 < ε := by positivity
  refine ⟨ε, hεpos, hball _ ?_ ?_⟩
  · have h := AffineMap.lineMap_mem (1 + ε) (subset_affineSpan ℝ C hz₀)
      (subset_affineSpan ℝ C hzC)
    rw [lineMap_eq_add_smul] at h
    convert h using 1
    module
  · rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hεpos.le, hε]
    calc r / (2 * ‖z - z₀‖) * ‖z - z₀‖ = r / 2 := by field_simp
      _ < r := by linarith

variable [FiniteDimensional ℝ E]

/-- The line segment principle relative to the affine hull: the half-open
segment from a closure point to a relative interior point lies in `rint C`. -/
theorem Convex.add_smul_sub_mem_intrinsicInterior_normed {s : Set E} (hs : Convex ℝ s)
    {x z : E} (hx : x ∈ closure s) (hz : z ∈ intrinsicInterior ℝ s) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t ≤ 1) : x + t • (z - x) ∈ intrinsicInterior ℝ s := by
  obtain ⟨hzs, r, hr, hball⟩ := mem_intrinsicInterior_iff_ball_normed.1 hz
  obtain ⟨x', hx's, hxx'⟩ := Metric.mem_closure_iff.1 hx (t * r / 2) (by positivity)
  have key : ∀ y ∈ affineSpan ℝ s, dist y (x + t • (z - x)) < t * r / 2 → y ∈ s := by
    intro y hy hyw
    set z' : E := x' + t⁻¹ • (y - x') with hz'
    have hz'A : z' ∈ affineSpan ℝ s := by
      have h := AffineMap.lineMap_mem t⁻¹ (subset_affineSpan ℝ s hx's) hy
      rwa [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm] at h
    have e : t • (z' - z) = (y - (x + t • (z - x))) + (1 - t) • (x - x') := by
      rw [hz', smul_sub, smul_add, smul_smul, mul_inv_cancel₀ ht0.ne', one_smul]
      module
    have hz'z : dist z' z < r := by
      have hn : t * ‖z' - z‖ ≤ ‖y - (x + t • (z - x))‖ + (1 - t) * ‖x - x'‖ := by
        calc t * ‖z' - z‖ = ‖t • (z' - z)‖ := by
              rw [norm_smul, Real.norm_of_nonneg ht0.le]
          _ ≤ ‖y - (x + t • (z - x))‖ + ‖(1 - t) • (x - x')‖ := by
              rw [e]
              exact norm_add_le _ _
          _ = ‖y - (x + t • (z - x))‖ + (1 - t) * ‖x - x'‖ := by
              rw [norm_smul, Real.norm_of_nonneg (by linarith)]
      have h1 : ‖y - (x + t • (z - x))‖ < t * r / 2 := by rwa [← dist_eq_norm]
      have h2 : (1 - t) * ‖x - x'‖ ≤ t * r / 2 := by
        have : ‖x - x'‖ < t * r / 2 := by rwa [← dist_eq_norm]
        have h1t : 0 ≤ 1 - t := by linarith
        nlinarith [norm_nonneg (x - x')]
      rw [dist_eq_norm]
      by_contra hcon
      push_neg at hcon
      nlinarith
    have hz's : z' ∈ s := hball z' hz'A hz'z
    have hy_eq : y = x' + t • (z' - x') := by
      rw [hz', add_sub_cancel_left, smul_smul, mul_inv_cancel₀ ht0.ne', one_smul,
        add_sub_cancel]
    rw [hy_eq]
    exact hs.add_smul_sub_mem hx's hz's ⟨ht0.le, ht1⟩
  have hxA : x ∈ affineSpan ℝ s :=
    closure_minimal (subset_affineSpan ℝ s) (AffineSubspace.closed_of_finiteDimensional _) hx
  have hwA : x + t • (z - x) ∈ affineSpan ℝ s := by
    have h := AffineMap.lineMap_mem t hxA (subset_affineSpan ℝ s hzs)
    rwa [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm] at h
  refine mem_intrinsicInterior_iff_ball_normed.2
    ⟨key _ hwA (by rw [dist_self]; positivity), t * r / 2, by positivity, key⟩

/-- Convex combinations with positive weight on a relative interior point stay
in the relative interior. -/
theorem Convex.combo_mem_intrinsicInterior_normed {s : Set E} (hs : Convex ℝ s) {x z : E}
    (hx : x ∈ closure s) (hz : z ∈ intrinsicInterior ℝ s) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hab : a + b = 1) : a • x + b • z ∈ intrinsicInterior ℝ s := by
  have h := Convex.add_smul_sub_mem_intrinsicInterior_normed hs hx hz hb (by linarith)
  convert h using 1
  rw [show a = 1 - b by linarith]
  module

theorem affineSpan_closure_eq {s : Set E} : affineSpan ℝ (closure s) = affineSpan ℝ s :=
  le_antisymm (affineSpan_le.2 (closure_minimal (subset_affineSpan ℝ s)
    (AffineSubspace.closed_of_finiteDimensional _))) (affineSpan_mono ℝ subset_closure)

end Basic

/-! ## Relative interiors of segments -/

section Segments

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem affineSpan_segment (x₀ x₁ : E) :
    affineSpan ℝ (segment ℝ x₀ x₁) = affineSpan ℝ {x₀, x₁} := by
  rw [← convexHull_pair, affineSpan_convexHull]

theorem mem_affineSpan_segment {x₀ x₁ y : E} (hy : y ∈ affineSpan ℝ (segment ℝ x₀ x₁)) :
    ∃ c : ℝ, y = x₀ + c • (x₁ - x₀) := by
  rw [affineSpan_segment] at hy
  obtain ⟨c, hc⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hy
  exact ⟨c, by rw [← hc, lineMap_eq_add_smul]⟩

theorem add_smul_sub_mem_affineSpan_segment (x₀ x₁ : E) (c : ℝ) :
    x₀ + c • (x₁ - x₀) ∈ affineSpan ℝ (segment ℝ x₀ x₁) := by
  rw [← lineMap_eq_add_smul]
  exact AffineMap.lineMap_mem c (subset_affineSpan ℝ _ (left_mem_segment ℝ x₀ x₁))
    (subset_affineSpan ℝ _ (right_mem_segment ℝ x₀ x₁))

theorem eq_of_add_smul_eq {x₀ x₁ : E} (hne : x₀ ≠ x₁) {c d : ℝ}
    (h : x₀ + c • (x₁ - x₀) = x₀ + d • (x₁ - x₀)) : c = d := by
  have : (c - d) • (x₁ - x₀) = 0 := by
    rw [sub_smul, sub_eq_zero]
    exact add_left_cancel h
  rcases smul_eq_zero.mp this with h0 | h0
  · linarith [sub_eq_zero.mp h0]
  · exact absurd (sub_eq_zero.mp h0).symm hne

theorem mem_segment_iff_param {x₀ x₁ y : E} :
    y ∈ segment ℝ x₀ x₁ ↔ ∃ c ∈ Icc (0 : ℝ) 1, y = x₀ + c • (x₁ - x₀) := by
  rw [segment_eq_image]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, hc, by module⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, hc, by module⟩

theorem mem_openSegment_iff_param {x₀ x₁ y : E} :
    y ∈ openSegment ℝ x₀ x₁ ↔ ∃ c ∈ Ioo (0 : ℝ) 1, y = x₀ + c • (x₁ - x₀) := by
  rw [openSegment_eq_image]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, hc, by module⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, hc, by module⟩

/-- The relative interior of a nondegenerate segment is the open segment. -/
theorem intrinsicInterior_segment {x₀ x₁ : E} (hne : x₀ ≠ x₁) :
    intrinsicInterior ℝ (segment ℝ x₀ x₁) = openSegment ℝ x₀ x₁ := by
  have hn : 0 < ‖x₁ - x₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
  ext z
  rw [mem_intrinsicInterior_iff_ball_normed]
  constructor
  · rintro ⟨hz, r, hr, hball⟩
    obtain ⟨c, hc, rfl⟩ := mem_segment_iff_param.mp hz
    set δ := r / (2 * ‖x₁ - x₀‖) with hδ
    have hδpos : 0 < δ := by positivity
    have hdist : ∀ c' : ℝ, |c' - c| = δ →
        dist (x₀ + c' • (x₁ - x₀)) (x₀ + c • (x₁ - x₀)) < r := by
      intro c' hc'
      rw [dist_eq_norm, show x₀ + c' • (x₁ - x₀) - (x₀ + c • (x₁ - x₀)) =
        (c' - c) • (x₁ - x₀) by module, norm_smul, Real.norm_eq_abs, hc', hδ]
      calc r / (2 * ‖x₁ - x₀‖) * ‖x₁ - x₀‖ = r / 2 := by field_simp
        _ < r := by linarith
    have hnot : ∀ c' : ℝ, c' ∉ Icc (0 : ℝ) 1 → |c' - c| = δ → False := by
      intro c' hc'out hc'
      have hmem := hball _ (add_smul_sub_mem_affineSpan_segment x₀ x₁ c') (hdist c' hc')
      obtain ⟨d, hd, hdeq⟩ := mem_segment_iff_param.mp hmem
      have := eq_of_add_smul_eq hne hdeq
      exact hc'out (this ▸ hd)
    refine mem_openSegment_iff_param.mpr ⟨c, ⟨?_, ?_⟩, rfl⟩
    · by_contra h0
      have hc0 : c = 0 := le_antisymm (not_lt.mp h0) hc.1
      exact hnot (c - δ) (fun h ↦ by linarith [h.1]) (by rw [hc0]; simp [abs_of_pos hδpos])
    · by_contra h1
      have hc1 : c = 1 := le_antisymm hc.2 (not_lt.mp h1)
      exact hnot (c + δ) (fun h ↦ by linarith [h.2]) (by simp [abs_of_pos hδpos])
  · intro hz
    obtain ⟨c, hc, rfl⟩ := mem_openSegment_iff_param.mp hz
    refine ⟨openSegment_subset_segment ℝ x₀ x₁ hz, min c (1 - c) * ‖x₁ - x₀‖,
      mul_pos (lt_min hc.1 (by linarith [hc.2])) hn, fun y hy hyd ↦ ?_⟩
    obtain ⟨d, rfl⟩ := mem_affineSpan_segment hy
    rw [dist_eq_norm, show x₀ + d • (x₁ - x₀) - (x₀ + c • (x₁ - x₀)) = (d - c) • (x₁ - x₀) by
      module, norm_smul, Real.norm_eq_abs] at hyd
    have habs : |d - c| < min c (1 - c) := lt_of_mul_lt_mul_right hyd hn.le
    have h1 := (abs_lt.mp (habs.trans_le (min_le_left _ _)))
    have h2 := (abs_lt.mp (habs.trans_le (min_le_right _ _)))
    exact mem_segment_iff_param.mpr ⟨d, ⟨by linarith [h1.1], by linarith [h2.2]⟩, rfl⟩

end Segments

/-! ## Proposition 2.40 and Exercise 2.41 -/

section Properties

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem Convex.convex_intrinsicInterior_normed {C : Set E} (hC : Convex ℝ C) :
    Convex ℝ (intrinsicInterior ℝ C) := by
  intro x hx z hz a b ha hb hab
  rcases hb.eq_or_lt with rfl | hb'
  · simp only [add_zero] at hab
    subst hab
    simpa using hx
  exact Convex.combo_mem_intrinsicInterior_normed hC
    (subset_closure (intrinsicInterior_subset hx)) hz ha hb' hab

theorem Convex.subset_closure_intrinsicInterior_normed {C : Set E} (hC : Convex ℝ C) :
    C ⊆ closure (intrinsicInterior ℝ C) := by
  intro x hx
  obtain ⟨z, hz⟩ := Set.Nonempty.intrinsicInterior hC ⟨x, hx⟩
  have ht : Tendsto (fun t : ℝ ↦ x + t • (z - x)) (𝓝[>] 0) (𝓝 x) := by
    have h : Tendsto (fun t : ℝ ↦ x + t • (z - x)) (𝓝 0) (𝓝 (x + (0 : ℝ) • (z - x))) :=
      (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
    rw [zero_smul, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with t ht
  exact Convex.add_smul_sub_mem_intrinsicInterior_normed hC (subset_closure hx) hz ht.1 ht.2.le

/-- **Proposition 2.40**: for nonempty convex `C`, `rint C` is nonempty and
convex, `cl(rint C) = cl C`, `rint(cl C) = rint C`, and
`rint[x₀, x₁] ⊆ rint C` for `x₀ ∈ rint C`, `x₁ ∈ cl C`. -/
theorem intrinsicInterior_properties {C : Set E} (hC : Convex ℝ C) (hne : C.Nonempty) :
    (intrinsicInterior ℝ C).Nonempty ∧ Convex ℝ (intrinsicInterior ℝ C) ∧
      closure (intrinsicInterior ℝ C) = closure C ∧
      intrinsicInterior ℝ (closure C) = intrinsicInterior ℝ C ∧
      ∀ x₀ ∈ intrinsicInterior ℝ C, ∀ x₁ ∈ closure C,
        intrinsicInterior ℝ (segment ℝ x₀ x₁) ⊆ intrinsicInterior ℝ C := by
  refine ⟨hne.intrinsicInterior hC, Convex.convex_intrinsicInterior_normed hC,
    le_antisymm (closure_mono intrinsicInterior_subset)
      (closure_minimal (Convex.subset_closure_intrinsicInterior_normed hC) isClosed_closure),
    ?_, ?_⟩
  · apply Subset.antisymm
    · intro z hz
      obtain ⟨x₀, hx₀⟩ := hne.intrinsicInterior hC
      by_cases hzx : z = x₀
      · rw [hzx]; exact hx₀
      obtain ⟨ε, hε, hmem⟩ := exists_add_smul_sub_mem_of_mem_intrinsicInterior hz
        (subset_closure (intrinsicInterior_subset hx₀))
      have h := Convex.add_smul_sub_mem_intrinsicInterior_normed hC hmem hx₀
        (t := ε / (1 + ε)) (by positivity) (by rw [div_le_one (by linarith)]; linarith)
      convert h using 1
      have h1 : (1 + ε) ≠ 0 := by linarith
      match_scalars <;> field_simp <;> ring
    · intro z hz
      obtain ⟨hzC, r, hr, hball⟩ := mem_intrinsicInterior_iff_ball_normed.1 hz
      refine mem_intrinsicInterior_iff_ball_normed.2 ⟨subset_closure hzC, r, hr, fun y hy hyz ↦ ?_⟩
      rw [affineSpan_closure_eq] at hy
      exact subset_closure (hball y hy hyz)
  · intro x₀ hx₀ x₁ hx₁ z hz
    by_cases h01 : x₀ = x₁
    · subst h01
      rw [segment_same, intrinsicInterior_singleton] at hz
      rw [mem_singleton_iff.mp hz]
      exact hx₀
    rw [intrinsicInterior_segment h01] at hz
    obtain ⟨c, hc, rfl⟩ := mem_openSegment_iff_param.mp hz
    have h := Convex.add_smul_sub_mem_intrinsicInterior_normed hC hx₁ hx₀ (t := 1 - c)
      (by linarith [hc.2]) (by linarith [hc.1])
    convert h using 1
    module

/-- **Exercise 2.41 (relative interior criterion)**: `x ∈ rint C` if and only if
`x ∈ C` and every `x₀ ≠ x` in `C` has some `x₁ ∈ C` with `x ∈ rint[x₀, x₁]`. -/
theorem mem_intrinsicInterior_iff_segment {C : Set E} (hC : Convex ℝ C) {x : E} :
    x ∈ intrinsicInterior ℝ C ↔
      x ∈ C ∧ ∀ x₀ ∈ C, x₀ ≠ x → ∃ x₁ ∈ C, x ∈ intrinsicInterior ℝ (segment ℝ x₀ x₁) := by
  constructor
  · intro hx
    refine ⟨intrinsicInterior_subset hx, fun x₀ hx₀ hne ↦ ?_⟩
    obtain ⟨ε, hε, hmem⟩ := exists_add_smul_sub_mem_of_mem_intrinsicInterior hx hx₀
    refine ⟨x + ε • (x - x₀), hmem, ?_⟩
    have hne' : x₀ ≠ x + ε • (x - x₀) := by
      intro h
      have : (1 + ε) • (x - x₀) = 0 := by
        calc (1 + ε) • (x - x₀) = (x + ε • (x - x₀)) - x₀ := by module
          _ = 0 := by rw [← h, sub_self]
      rcases smul_eq_zero.mp this with h0 | h0
      · linarith
      · exact hne (sub_eq_zero.mp h0).symm
    rw [intrinsicInterior_segment hne']
    refine mem_openSegment_iff_param.mpr ⟨1 / (1 + ε), ⟨by positivity, ?_⟩, ?_⟩
    · rw [div_lt_one (by linarith)]
      linarith
    · have h1 : (1 + ε) ≠ 0 := by linarith
      match_scalars <;> (field_simp; try ring)
  · rintro ⟨hxC, hcrit⟩
    obtain ⟨z, hz⟩ := Set.Nonempty.intrinsicInterior hC ⟨x, hxC⟩
    by_cases hzx : z = x
    · rw [← hzx]; exact hz
    obtain ⟨x₁, hx₁, hxs⟩ := hcrit z (intrinsicInterior_subset hz) hzx
    by_cases hz1 : z = x₁
    · subst hz1
      rw [segment_same, intrinsicInterior_singleton] at hxs
      exact absurd (mem_singleton_iff.mp hxs).symm hzx
    rw [intrinsicInterior_segment hz1] at hxs
    obtain ⟨c, hc, rfl⟩ := mem_openSegment_iff_param.mp hxs
    have h := Convex.add_smul_sub_mem_intrinsicInterior_normed hC (subset_closure hx₁) hz
      (t := 1 - c) (by linarith [hc.2]) (by linarith [hc.1])
    convert h using 1
    module

end Properties

/-! ## Proposition 2.42 -/

section Intersections

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The by-product in the proof of 2.42: points of `⋂ cl Cᵢ` are limits of
points of `⋂ rint Cᵢ`. -/
theorem iInter_closure_subset_closure_iInter_intrinsicInterior {ι : Sort*} {C : ι → Set E}
    (hC : ∀ i, Convex ℝ (C i)) (hne : (⋂ i, intrinsicInterior ℝ (C i)).Nonempty) :
    ⋂ i, closure (C i) ⊆ closure (⋂ i, intrinsicInterior ℝ (C i)) := by
  obtain ⟨x₀, hx₀⟩ := hne
  rw [mem_iInter] at hx₀
  intro x₁ hx₁
  rw [mem_iInter] at hx₁
  have ht : Tendsto (fun t : ℝ ↦ x₁ + t • (x₀ - x₁)) (𝓝[>] 0) (𝓝 x₁) := by
    have h : Tendsto (fun t : ℝ ↦ x₁ + t • (x₀ - x₁)) (𝓝 0) (𝓝 (x₁ + (0 : ℝ) • (x₀ - x₁))) :=
      (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
    rw [zero_smul, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with t ht
  exact mem_iInter.mpr fun i ↦
    Convex.add_smul_sub_mem_intrinsicInterior_normed (hC i) (hx₁ i) (hx₀ i) ht.1 ht.2.le

/-- **Proposition 2.42**: if `⋂ rint Cᵢ ≠ ∅`, then `cl ⋂ Cᵢ = ⋂ cl Cᵢ`. -/
theorem closure_iInter_eq_of_intrinsicInterior {ι : Sort*} {C : ι → Set E}
    (hC : ∀ i, Convex ℝ (C i)) (hne : (⋂ i, intrinsicInterior ℝ (C i)).Nonempty) :
    closure (⋂ i, C i) = ⋂ i, closure (C i) := by
  apply Subset.antisymm (subset_iInter fun i ↦ closure_mono (iInter_subset C i))
  refine (iInter_closure_subset_closure_iInter_intrinsicInterior hC hne).trans
    (closure_mono (iInter_mono fun i ↦ intrinsicInterior_subset))

/-- **Proposition 2.42**: for finitely many convex sets with
`⋂ rint Cᵢ ≠ ∅`, `rint ⋂ Cᵢ = ⋂ rint Cᵢ`. -/
theorem intrinsicInterior_iInter_eq {ι : Type*} [Finite ι] {C : ι → Set E}
    (hC : ∀ i, Convex ℝ (C i)) (hne : (⋂ i, intrinsicInterior ℝ (C i)).Nonempty) :
    intrinsicInterior ℝ (⋂ i, C i) = ⋂ i, intrinsicInterior ℝ (C i) := by
  have hA : Convex ℝ (⋂ i, C i) := convex_iInter hC
  have hB : Convex ℝ (⋂ i, intrinsicInterior ℝ (C i)) :=
    convex_iInter fun i ↦ Convex.convex_intrinsicInterior_normed (hC i)
  have hAne : (⋂ i, C i).Nonempty :=
    hne.mono (iInter_mono fun i ↦ intrinsicInterior_subset)
  apply Subset.antisymm
  · have hcl : closure (⋂ i, C i) = closure (⋂ i, intrinsicInterior ℝ (C i)) := by
      apply Subset.antisymm
      · exact (closure_mono (iInter_mono fun i ↦ subset_closure)).trans
          (closure_minimal (iInter_closure_subset_closure_iInter_intrinsicInterior hC hne)
            isClosed_closure)
      · exact closure_mono (iInter_mono fun i ↦ intrinsicInterior_subset)
    calc intrinsicInterior ℝ (⋂ i, C i) = intrinsicInterior ℝ (closure (⋂ i, C i)) :=
          ((intrinsicInterior_properties hA hAne).2.2.2.1).symm
      _ = intrinsicInterior ℝ (closure (⋂ i, intrinsicInterior ℝ (C i))) := by rw [hcl]
      _ = intrinsicInterior ℝ (⋂ i, intrinsicInterior ℝ (C i)) :=
          (intrinsicInterior_properties hB hne).2.2.2.1
      _ ⊆ ⋂ i, intrinsicInterior ℝ (C i) := intrinsicInterior_subset
  · intro z hz
    rw [mem_iInter] at hz
    have hball := fun i ↦ (mem_intrinsicInterior_iff_ball_normed.1 (hz i))
    choose hzC r hr hrball using hball
    rcases isEmpty_or_nonempty ι with hι | hι
    · refine mem_intrinsicInterior_iff_ball_normed.2 ⟨by simp, 1, one_pos, fun y _ _ ↦ by simp⟩
    · have := Fintype.ofFinite ι
      obtain ⟨i₀, hi₀⟩ := Finite.exists_min r
      refine mem_intrinsicInterior_iff_ball_normed.2 ⟨mem_iInter.mpr hzC, r i₀, hr i₀,
        fun y hy hyz ↦ mem_iInter.mpr fun i ↦ hrball i y ?_ (hyz.trans_le (hi₀ i))⟩
      exact affineSpan_mono ℝ (iInter_subset C i) hy

end Intersections

end RW
