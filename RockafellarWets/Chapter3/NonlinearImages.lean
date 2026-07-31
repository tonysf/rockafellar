/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3: Closed Nonlinear Images

This file formalizes Exercise 3.16 of Rockafellar--Wets.

The book excludes an unbounded sequence in a closed set whose image is
bounded and which converges cosmically to a nonzero horizon direction.  In
the closed-ball model from `CosmicSpace`, nonzero directions are precisely
the boundary points.  The predicate `NoBoundedHorizonEscape` states this
sequential condition directly.

We first prove that a cosmic boundary limit of points of `C` really belongs
to `horizonCone C`.  The closed-image theorem then follows by extracting a
cosmically convergent subsequence from any unbounded sequence of preimages.
-/

import RockafellarWets.Chapter3.CosmicSpace
import RockafellarWets.Chapter3.HorizonCones
import Mathlib.Topology.LocalAtTarget

open Bornology Filter Function Metric Set Topology

namespace RW

section NonlinearImages

variable {E G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The sequential escape excluded in Exercise 3.16.

The unit vector `u` is automatically nonzero because it belongs to
`CosmicBoundary E`.  We nevertheless retain both the unboundedness of the
sequence and membership of `u` in `horizonCone C`, so that the Lean
predicate mirrors the hypotheses in the book. -/
def NoBoundedHorizonEscape (F : E → G) (C : Set E) : Prop :=
  ∀ (x : ℕ → E) (u : CosmicBoundary E),
    (∀ n, x n ∈ C) →
    ¬ IsBounded (Set.range x) →
    IsBounded (Set.range (F ∘ x)) →
    Tendsto (fun n ↦ cosmicEmbed (x n)) atTop
      (𝓝 (cosmicDirection u)) →
    (u : E) ∈ horizonCone C →
    False

/-- A convenient sequential coercivity condition on the restriction of a
map to a set. -/
def IsSequentiallyCoerciveOn (F : E → G) (C : Set E) : Prop :=
  ∀ x : ℕ → E, (∀ n, x n ∈ C) →
    IsBounded (Set.range (F ∘ x)) →
    IsBounded (Set.range x)

/-- Cosmic convergence to a boundary direction, along points of `C`, puts
that direction in the horizon cone of `C`.

This is the bridge between the closed-ball compactification and Mathlib's
filter definition of the asymptotic cone. -/
theorem mem_horizonCone_of_tendsto_cosmicDirection
    {C : Set E} {x : ℕ → E} {u : CosmicBoundary E}
    (hxC : ∀ n, x n ∈ C)
    (hx : Tendsto (fun n ↦ cosmicEmbed (x n)) atTop
      (𝓝 (cosmicDirection u))) :
    (u : E) ∈ horizonCone C := by
  rcases exists_scaling_of_tendsto_cosmicDirection hx with
    ⟨scale, hscale_pos, hscale_zero, hscaled⟩
  have hscale_within :
      Tendsto scale atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hscale_zero, Eventually.of_forall hscale_pos⟩
  have hinv :
      Tendsto (fun n ↦ (scale n)⁻¹) atTop atTop :=
    hscale_within.inv_tendsto_nhdsGT_zero
  have hasymptotic :
      Tendsto x atTop (AffineSpace.asymptoticNhds ℝ E (u : E)) := by
    have hrescaled :=
      hinv.atTop_smul_nhds_tendsto_asymptoticNhds hscaled
    exact hrescaled.congr' (Eventually.of_forall fun n ↦ by
      simp [hscale_pos n |>.ne'])
  refine Set.mem_insert_of_mem 0 ?_
  rw [mem_asymptoticCone_iff]
  exact hasymptotic.frequently (Eventually.of_forall hxC).frequently

omit [NormedSpace ℝ E] in
/-- A sequence whose `n`th norm is larger than `n` has unbounded range. -/
private theorem not_isBounded_range_of_nat_lt_norm
    {x : ℕ → E} (hx : ∀ n : ℕ, (n : ℝ) < ‖x n‖) :
    ¬ IsBounded (Set.range x) := by
  intro hbounded
  obtain ⟨R, hR⟩ := hbounded.exists_norm_le
  obtain ⟨n, hn⟩ := exists_nat_gt R
  have hupper : ‖x n‖ ≤ R := hR (x n) (Set.mem_range_self n)
  exact (not_lt_of_ge (hupper.trans hn.le)) (hx n)

omit [NormedSpace ℝ E] in
/-- An unbounded sequence has a reindexing whose `n`th norm is larger than
`n`.  Monotonicity of the reindexing is unnecessary here: boundedness of the
image is inherited by every reindexing. -/
private theorem exists_norm_escaping_reindex
    {x : ℕ → E} (hx : ¬ IsBounded (Set.range x)) :
    ∃ k : ℕ → ℕ, ∀ n : ℕ, (n : ℝ) < ‖x (k n)‖ := by
  have hlarge : ∀ n : ℕ, ∃ k : ℕ, (n : ℝ) < ‖x k‖ := by
    intro n
    by_contra h
    push_neg at h
    apply hx
    exact isBounded_iff_forall_norm_le.mpr
      ⟨(n : ℝ), by
        rintro y ⟨k, rfl⟩
        exact h k⟩
  choose k hk using hlarge
  exact ⟨k, hk⟩

omit [NormedSpace ℝ G] in
/-- **Exercise 3.16 (closed nonlinear image).** Let `F` be continuous and
`C` closed in a finite-dimensional space.  If no unbounded sequence in `C`
has bounded image while converging cosmically to a nonzero direction in
`horizonCone C`, then `F '' C` is closed. -/
theorem isClosed_image_of_noBoundedHorizonEscape
    [FiniteDimensional ℝ E]
    {F : E → G} {C : Set E}
    (hF : Continuous F) (hC : IsClosed C)
    (hescape : NoBoundedHorizonEscape F C) :
    IsClosed (F '' C) := by
  rw [isClosed_iff_frequently]
  intro y hy
  have hyclosure : y ∈ closure (F '' C) :=
    mem_closure_iff_frequently.mpr hy
  rcases mem_closure_iff_seq_limit.mp hyclosure with
    ⟨yseq, hyseq, hyseq_tendsto⟩
  choose x hxC hFx using fun n ↦ hyseq n
  have hFx_tendsto :
      Tendsto (fun n ↦ F (x n)) atTop (𝓝 y) := by
    simpa only [hFx] using hyseq_tendsto
  have hFx_bounded : IsBounded (Set.range (F ∘ x)) := by
    simpa only [Function.comp_apply] using
      Metric.isBounded_range_of_tendsto _ hFx_tendsto
  by_cases hx_bounded : IsBounded (Set.range x)
  · rcases tendsto_subseq_of_bounded hx_bounded
      (fun n ↦ Set.mem_range_self n) with
      ⟨xbar, -, φ, hφ, hxbar⟩
    have hxbarC : xbar ∈ C :=
      hC.mem_of_tendsto hxbar
        (Eventually.of_forall fun n ↦ hxC (φ n))
    have hF_at_xbar :
        Tendsto (fun n ↦ F (x (φ n))) atTop (𝓝 (F xbar)) :=
      (hF.tendsto xbar).comp hxbar
    have hF_at_y :
        Tendsto (fun n ↦ F (x (φ n))) atTop (𝓝 y) :=
      hFx_tendsto.comp hφ.tendsto_atTop
    exact ⟨xbar, hxbarC, tendsto_nhds_unique hF_at_xbar hF_at_y⟩
  · rcases exists_norm_escaping_reindex hx_bounded with ⟨k, hk⟩
    let z : ℕ → E := fun n ↦ x (k n)
    rcases exists_cosmic_subsequence_with_classified_limit z with
      ⟨p, φ, hφ, hp, hpclass⟩
    rcases hpclass with ⟨xbar, hxbar⟩ | ⟨u, hu⟩
    · have hz_tendsto :
          Tendsto (z ∘ φ) atTop (𝓝 xbar) := by
        apply (tendsto_cosmicEmbed_iff (x₀ := xbar)).mp
        simpa only [Function.comp_apply, hxbar] using hp
      have hz_bounded : IsBounded (Set.range (z ∘ φ)) :=
        Metric.isBounded_range_of_tendsto _ hz_tendsto
      have hz_large : ∀ n : ℕ, (n : ℝ) < ‖(z ∘ φ) n‖ := by
        intro n
        have hnφ : (n : ℝ) ≤ (φ n : ℝ) := by
          exact_mod_cast hφ.id_le n
        exact hnφ.trans_lt (hk (φ n))
      exact ((not_isBounded_range_of_nat_lt_norm hz_large) hz_bounded).elim
    · have hz_cosmic :
          Tendsto (fun n ↦ cosmicEmbed ((z ∘ φ) n)) atTop
            (𝓝 (cosmicDirection u)) := by
        simpa only [Function.comp_apply, hu] using hp
      have hzC : ∀ n, (z ∘ φ) n ∈ C := fun n ↦
        hxC (k (φ n))
      have hz_image_bounded :
          IsBounded (Set.range (F ∘ (z ∘ φ))) :=
        hFx_bounded.subset <| by
          rintro _ ⟨n, rfl⟩
          exact ⟨k (φ n), rfl⟩
      have hz_large : ∀ n : ℕ, (n : ℝ) < ‖(z ∘ φ) n‖ := by
        intro n
        have hnφ : (n : ℝ) ≤ (φ n : ℝ) := by
          exact_mod_cast hφ.id_le n
        exact hnφ.trans_lt (hk (φ n))
      exact (hescape (z ∘ φ) u hzC
        (not_isBounded_range_of_nat_lt_norm hz_large)
        hz_image_bounded hz_cosmic
        (mem_horizonCone_of_tendsto_cosmicDirection hzC hz_cosmic)).elim

omit [NormedSpace ℝ G] in
/-- Sequential coercivity on `C` rules out the escape from Exercise 3.16. -/
theorem IsSequentiallyCoerciveOn.noBoundedHorizonEscape
    {F : E → G} {C : Set E}
    (hF : IsSequentiallyCoerciveOn F C) :
    NoBoundedHorizonEscape F C := by
  intro x _ hxC hx_unbounded hx_image_bounded _ _
  exact hx_unbounded (hF x hxC hx_image_bounded)

omit [NormedSpace ℝ G] in
/-- A continuous sequentially coercive map has closed image on every closed
set on which the coercivity condition holds. -/
theorem IsSequentiallyCoerciveOn.isClosed_image
    [FiniteDimensional ℝ E]
    {F : E → G} {C : Set E}
    (hcoercive : IsSequentiallyCoerciveOn F C)
    (hF : Continuous F) (hC : IsClosed C) :
    IsClosed (F '' C) :=
  isClosed_image_of_noBoundedHorizonEscape hF hC
    hcoercive.noBoundedHorizonEscape

omit [NormedSpace ℝ G] in
/-- The continuous image of a closed bounded finite-dimensional set is
closed.  This is the bounded-set boundary case of Exercise 3.16. -/
theorem isClosed_image_of_isClosed_isBounded
    [FiniteDimensional ℝ E]
    {F : E → G} {C : Set E}
    (hF : Continuous F) (hC : IsClosed C) (hC_bounded : IsBounded C) :
    IsClosed (F '' C) :=
  ((isCompact_iff_isClosed_bounded.mpr ⟨hC, hC_bounded⟩).image hF).isClosed

omit [NormedSpace ℝ E] [NormedSpace ℝ G] in
/-- A proper map is closed, hence sends every closed set to a closed set.
This gives the standard proper-map corollary of Exercise 3.16. -/
theorem IsProperMap.isClosed_image
    {F : E → G} (hF : IsProperMap F) {C : Set E} (hC : IsClosed C) :
    IsClosed (F '' C) :=
  hF.isClosedMap C hC

end NonlinearImages

end RW
