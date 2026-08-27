/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Relations Between Distance Functions and Truncated Inclusions

This file proves Lemma 4.34 of Rockafellar--Wets.  The book works in
Euclidean space; the basic estimate is valid in any finite-dimensional real
normed space, while the sharper convex and conic radii use an inner product.
-/

import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Thickening
import RockafellarWets.Chapter3.Cones

open Bornology Metric Set

namespace RW

section BasicRelations

variable {E : Type*} [NormedAddCommGroup E]

private theorem infDist_le_add_of_mem_cthickening
    {C : Set E} (hCne : C.Nonempty) {x p : E} {e : ℝ} (he : 0 ≤ e)
    (hp : p ∈ cthickening e C) :
    infDist x C ≤ dist x p + e := by
  have hp' : infDist p C ≤ e := by
    rw [mem_cthickening_iff] at hp
    exact (ENNReal.le_ofReal_iff_toReal_le (infEDist_ne_top hCne) he).1 hp
  exact infDist_le_infDist_add_dist.trans <| by
    rw [dist_comm x p]
    linarith

/-- Lemma 4.34(c), in closed-thickening form.  A global inclusion in an
`e`-enlargement gives the corresponding global inequality of distance
functions. -/
theorem infDist_le_infDist_add_of_subset_cthickening
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {C₁ C₂ : Set E} (hC₁closed : IsClosed C₁) (hC₁ne : C₁.Nonempty)
    (hC₂ne : C₂.Nonempty) {e : ℝ} (he : 0 ≤ e)
    (hsub : C₁ ⊆ cthickening e C₂) (x : E) :
    infDist x C₂ ≤ infDist x C₁ + e := by
  rcases hC₁closed.exists_infDist_eq_dist hC₁ne x with ⟨p, hpC₁, hp⟩
  calc
    infDist x C₂ ≤ dist x p + e :=
      infDist_le_add_of_mem_cthickening hC₂ne he (hsub hpC₁)
    _ = infDist x C₁ + e := by rw [← hp]

/-- Lemma 4.34(a).  A distance-function upper estimate on a ball implies
the corresponding truncated set inclusion. -/
theorem inter_closedBall_subset_cthickening_of_infDist_le
    {C₁ C₂ : Set E} (hC₂ne : C₂.Nonempty) {ρ e : ℝ} (he : 0 ≤ e)
    (h : ∀ x ∈ closedBall (0 : E) ρ,
      infDist x C₂ ≤ infDist x C₁ + e) :
    C₁ ∩ closedBall (0 : E) ρ ⊆ cthickening e C₂ := by
  intro x hx
  rw [mem_cthickening_iff]
  apply (ENNReal.le_ofReal_iff_toReal_le (infEDist_ne_top hC₂ne) he).2
  simpa only [infDist_zero_of_mem hx.1, zero_add] using h x hx.2

private theorem exists_projection_mem_closedBall_of_two_mul
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {C : Set E} (hCclosed : IsClosed C) (hCne : C.Nonempty)
    {x : E} {ρ ρ' : ℝ} (hxρ : x ∈ closedBall (0 : E) ρ)
    (hρ' : 2 * ρ + infDist 0 C ≤ ρ') :
    ∃ p ∈ C ∩ closedBall (0 : E) ρ', infDist x C = dist x p := by
  rcases hCclosed.exists_infDist_eq_dist hCne x with ⟨p, hpC, hp⟩
  refine ⟨p, ⟨hpC, ?_⟩, hp⟩
  rw [mem_closedBall, dist_zero_right] at hxρ ⊢
  have hdist : infDist x C ≤ infDist 0 C + ‖x‖ := by
    simpa only [dist_zero_right] using
      (infDist_le_infDist_add_dist (x := x) (y := (0 : E)) (s := C))
  have hnorm : ‖p‖ ≤ ‖x‖ + infDist x C := by
    calc
      ‖p‖ ≤ ‖p - x‖ + ‖x‖ := norm_le_norm_sub_add p x
      _ = infDist x C + ‖x‖ := by
        rw [norm_sub_rev, ← dist_eq_norm, ← hp]
      _ = ‖x‖ + infDist x C := add_comm _ _
  linarith

/-- Lemma 4.34(b), with the general radius `2 * ρ + d(0,C₁)` valid
without convexity. -/
theorem infDist_le_on_closedBall_of_truncated_subset
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {C₁ C₂ : Set E} (hC₁closed : IsClosed C₁) (hC₁ne : C₁.Nonempty)
    (hC₂ne : C₂.Nonempty) {ρ ρ' e : ℝ} (he : 0 ≤ e)
    (hρ' : 2 * ρ + infDist 0 C₁ ≤ ρ')
    (hsub : C₁ ∩ closedBall (0 : E) ρ' ⊆ cthickening e C₂) :
    ∀ x ∈ closedBall (0 : E) ρ,
      infDist x C₂ ≤ infDist x C₁ + e := by
  intro x hx
  rcases exists_projection_mem_closedBall_of_two_mul
      hC₁closed hC₁ne hx hρ' with ⟨p, ⟨hpC, hpBall⟩, hp⟩
  calc
    infDist x C₂ ≤ dist x p + e :=
      infDist_le_add_of_mem_cthickening hC₂ne he (hsub ⟨hpC, hpBall⟩)
    _ = infDist x C₁ + e := congrArg (fun t : ℝ ↦ t + e) hp.symm

/-- Lemma 4.34(d).  Sufficient separation of the two distances at the
origin orders the distance functions on the smaller ball. -/
theorem infDist_le_infDist_on_closedBall_of_origin_gap
    (C₁ C₂ : Set E) {ρ : ℝ}
    (hgap : 2 * ρ + infDist 0 C₁ ≤ infDist 0 C₂) :
    ∀ x ∈ closedBall (0 : E) ρ, infDist x C₁ ≤ infDist x C₂ := by
  intro x hx
  rw [mem_closedBall, dist_zero_right] at hx
  have h₁ : infDist x C₁ ≤ infDist 0 C₁ + ‖x‖ := by
    simpa only [dist_zero_right] using
      (infDist_le_infDist_add_dist (x := x) (y := (0 : E)) (s := C₁))
  have h₂ : infDist 0 C₂ ≤ infDist x C₂ + ‖x‖ := by
    simpa only [dist_zero_left] using
      (infDist_le_infDist_add_dist (x := (0 : E)) (y := x) (s := C₂))
  linarith

end BasicRelations

section SharpEuclideanRadii

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem dist_projection_le_of_convex
    {C : Set E} (hC : Convex ℝ C) {x y px py : E}
    (hpxC : px ∈ C) (hpyC : py ∈ C)
    (hpx : infDist x C = dist x px) (hpy : infDist y C = dist y py) :
    dist px py ≤ dist x y := by
  have hpxMin : ‖x - px‖ = ⨅ w : C, ‖x - w‖ := by
    simpa only [dist_eq_norm] using
      hpx.symm.trans (infDist_eq_iInf (x := x) (s := C))
  have hpyMin : ‖y - py‖ = ⨅ w : C, ‖y - w‖ := by
    simpa only [dist_eq_norm] using
      hpy.symm.trans (infDist_eq_iInf (x := y) (s := C))
  have hxvar :=
    (norm_eq_iInf_iff_real_inner_le_zero hC hpxC).1 hpxMin py hpyC
  have hyvar :=
    (norm_eq_iInf_iff_real_inner_le_zero hC hpyC).1 hpyMin px hpxC
  let d : E := px - py
  have hxnonneg : 0 ≤ inner ℝ (x - px) d := by
    have hneg : py - px = -d := by simp only [d, neg_sub]
    rw [hneg, inner_neg_right] at hxvar
    linarith
  have hynonpos : inner ℝ (y - py) d ≤ 0 := by
    simpa only [d] using hyvar
  have hdecomp : x - y = (x - px) - (y - py) + d := by
    dsimp only [d]
    abel
  have hsq : ‖d‖ ^ 2 ≤ inner ℝ (x - y) d := by
    rw [hdecomp, inner_add_left, inner_sub_left,
      real_inner_self_eq_norm_sq]
    linarith
  have hcs : inner ℝ (x - y) d ≤ ‖x - y‖ * ‖d‖ :=
    real_inner_le_norm _ _
  by_cases hd : d = 0
  · have hpxpy : px = py := sub_eq_zero.mp (by simpa only [d] using hd)
    rw [hpxpy, dist_self]
    exact dist_nonneg
  · have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hd
    rw [dist_eq_norm, dist_eq_norm]
    change ‖d‖ ≤ ‖x - y‖
    nlinarith

private theorem exists_projection_mem_closedBall_of_convex
    [FiniteDimensional ℝ E]
    {C : Set E} (hCclosed : IsClosed C) (hCne : C.Nonempty) (hCconv : Convex ℝ C)
    {x : E} {ρ ρ' : ℝ} (hxρ : x ∈ closedBall (0 : E) ρ)
    (hρ' : ρ + infDist 0 C ≤ ρ') :
    ∃ p ∈ C ∩ closedBall (0 : E) ρ', infDist x C = dist x p := by
  rcases hCclosed.exists_infDist_eq_dist hCne x with ⟨p, hpC, hp⟩
  rcases hCclosed.exists_infDist_eq_dist hCne 0 with ⟨p₀, hp₀C, hp₀⟩
  have hproj : dist p p₀ ≤ dist x (0 : E) :=
    dist_projection_le_of_convex hCconv hpC hp₀C hp hp₀
  refine ⟨p, ⟨hpC, ?_⟩, hp⟩
  rw [mem_closedBall, dist_zero_right] at hxρ ⊢
  have hp₀norm : ‖p₀‖ = infDist 0 C := by
    simpa only [dist_zero_left] using hp₀.symm
  calc
    ‖p‖ ≤ dist p p₀ + ‖p₀‖ := by
      simpa only [dist_eq_norm] using norm_le_norm_sub_add p p₀
    _ ≤ ‖x‖ + infDist 0 C := by
      rw [hp₀norm]
      have hproj' : dist p p₀ ≤ ‖x‖ := by
        simpa only [dist_zero_right] using hproj
      linarith
    _ ≤ ρ' := by linarith

/-- Sharpened part of Lemma 4.34(b): for a convex first set, the radius
`2 * ρ` improves to `ρ`. -/
theorem infDist_le_on_closedBall_of_convex_truncated_subset
    [FiniteDimensional ℝ E]
    {C₁ C₂ : Set E} (hC₁closed : IsClosed C₁) (hC₁ne : C₁.Nonempty)
    (hC₁conv : Convex ℝ C₁) (hC₂ne : C₂.Nonempty)
    {ρ ρ' e : ℝ} (he : 0 ≤ e)
    (hρ' : ρ + infDist 0 C₁ ≤ ρ')
    (hsub : C₁ ∩ closedBall (0 : E) ρ' ⊆ cthickening e C₂) :
    ∀ x ∈ closedBall (0 : E) ρ,
      infDist x C₂ ≤ infDist x C₁ + e := by
  intro x hx
  rcases exists_projection_mem_closedBall_of_convex
      hC₁closed hC₁ne hC₁conv hx hρ' with ⟨p, ⟨hpC, hpBall⟩, hp⟩
  calc
    infDist x C₂ ≤ dist x p + e :=
      infDist_le_add_of_mem_cthickening hC₂ne he (hsub ⟨hpC, hpBall⟩)
    _ = infDist x C₁ + e := congrArg (fun t : ℝ ↦ t + e) hp.symm

private theorem ray_convex (p : E) :
    Convex ℝ {z : E | ∃ t : ℝ, 0 ≤ t ∧ t • p = z} := by
  rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩ a b ha hb hab
  refine ⟨a * s + b * t, add_nonneg (mul_nonneg ha hs) (mul_nonneg hb ht), ?_⟩
  simp only [add_smul, mul_smul]

private theorem exists_projection_mem_closedBall_of_isCone
    [FiniteDimensional ℝ E]
    {C : Set E} (hCclosed : IsClosed C) (hCne : C.Nonempty) (hCcone : IsCone C)
    {x : E} {ρ : ℝ} (hxρ : x ∈ closedBall (0 : E) ρ) :
    ∃ p ∈ C ∩ closedBall (0 : E) ρ, infDist x C = dist x p := by
  rcases hCclosed.exists_infDist_eq_dist hCne x with ⟨p, hpC, hp⟩
  let K : Set E := {z : E | ∃ t : ℝ, 0 ≤ t ∧ t • p = z}
  have hpK : p ∈ K := ⟨1, zero_le_one, one_smul ℝ p⟩
  have hzeroK : (0 : E) ∈ K := ⟨0, le_rfl, zero_smul ℝ p⟩
  have hKC : K ⊆ C := by
    rintro z ⟨t, ht, rfl⟩
    exact hCcone.smul_mem hpC ht
  have hpKproj : infDist x K = dist x p := by
    apply le_antisymm (infDist_le_dist_of_mem hpK)
    rw [← hp]
    exact infDist_le_infDist_of_subset hKC ⟨p, hpK⟩
  have hzeroKproj : infDist (0 : E) K = dist (0 : E) (0 : E) := by
    simp only [infDist_zero_of_mem hzeroK, dist_self]
  have hKconv : Convex ℝ K := by
    simpa only [K] using ray_convex p
  have hproj : dist p 0 ≤ dist x 0 :=
    dist_projection_le_of_convex hKconv hpK hzeroK hpKproj hzeroKproj
  refine ⟨p, ⟨hpC, ?_⟩, hp⟩
  rw [mem_closedBall] at hxρ ⊢
  exact hproj.trans hxρ

/-- Final clause of Lemma 4.34: for a closed cone the same radius is enough,
without convexity. -/
theorem infDist_le_on_closedBall_of_isCone_truncated_subset
    [FiniteDimensional ℝ E]
    {C₁ C₂ : Set E} (hC₁closed : IsClosed C₁) (hC₁ne : C₁.Nonempty)
    (hC₁cone : IsCone C₁) (hC₂ne : C₂.Nonempty)
    {ρ e : ℝ} (he : 0 ≤ e)
    (hsub : C₁ ∩ closedBall (0 : E) ρ ⊆ cthickening e C₂) :
    ∀ x ∈ closedBall (0 : E) ρ,
      infDist x C₂ ≤ infDist x C₁ + e := by
  intro x hx
  rcases exists_projection_mem_closedBall_of_isCone
      hC₁closed hC₁ne hC₁cone hx with ⟨p, ⟨hpC, hpBall⟩, hp⟩
  calc
    infDist x C₂ ≤ dist x p + e :=
      infDist_le_add_of_mem_cthickening hC₂ne he (hsub ⟨hpC, hpBall⟩)
    _ = infDist x C₁ + e := congrArg (fun t : ℝ ↦ t + e) hp.symm

/-- For a closed cone, the two directions of Lemma 4.34 give an exact
equivalence on a fixed ball. -/
theorem inter_closedBall_subset_cthickening_iff_infDist_le_of_isCone
    [FiniteDimensional ℝ E]
    {C₁ C₂ : Set E} (hC₁closed : IsClosed C₁) (hC₁ne : C₁.Nonempty)
    (hC₁cone : IsCone C₁) (hC₂ne : C₂.Nonempty)
    {ρ e : ℝ} (he : 0 ≤ e) :
    C₁ ∩ closedBall (0 : E) ρ ⊆ cthickening e C₂ ↔
      ∀ x ∈ closedBall (0 : E) ρ,
        infDist x C₂ ≤ infDist x C₁ + e := by
  constructor
  · exact infDist_le_on_closedBall_of_isCone_truncated_subset
      hC₁closed hC₁ne hC₁cone hC₂ne he
  · exact inter_closedBall_subset_cthickening_of_infDist_le hC₂ne he

end SharpEuclideanRadii

end RW
