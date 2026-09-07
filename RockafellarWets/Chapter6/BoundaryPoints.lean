/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Characterization of Boundary Points

Exercise 6.19.  For a closed set the points carrying a nonzero normal vector
are exactly the boundary points, the interior points being those where the
normal cone collapses to the origin; and for an arbitrary set the normal cone
is no larger than the normal cone to its closure.

The interior half is already available from the locality of the cones, so the
work is the boundary half.  It is the book's guide: a non-interior point is
approached from outside the set, each outside point is projected onto the
set, and the displacement from the projection to the outside point is a
proximal normal there, of unit length once rescaled.  A cluster point of those
unit vectors is normal at the limit by Definition 6.3 itself, so 6.6 is not
needed.
-/

import RockafellarWets.Chapter6.ElementaryCones
import RockafellarWets.Chapter6.ProximalNormals

open Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

section Closure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Regular normals cannot tell a set from its closure.  The `ε` inequality of
6(5) cuts out a closed set of test points, so once it holds on `C` inside a
ball it holds on `cl C` inside that ball. -/
theorem regularNormalCone_closure {C : Set E} {x : E} (hx : x ∈ C) :
    regularNormalCone (closure C) x = regularNormalCone C x := by
  refine Subset.antisymm ?_ ?_
  · rintro v ⟨-, hv⟩
    exact ⟨hx, fun ε hε ↦ (hv ε hε).filter_mono (nhdsWithin_mono x subset_closure)⟩
  · intro v hv
    rw [mem_regularNormalCone_iff] at hv ⊢
    refine ⟨subset_closure hx, fun ε hε ↦ ?_⟩
    obtain ⟨δ, hδ, hbound⟩ := hv.2 ε hε
    refine ⟨δ, hδ, fun y hy hyδ ↦ ?_⟩
    have hS : IsClosed {z : E | ⟪v, z - x⟫_ℝ ≤ ε * ‖z - x‖} :=
      isClosed_le (continuous_const.inner (continuous_id.sub continuous_const))
        (continuous_const.mul ((continuous_id.sub continuous_const).norm))
    have hsub : ball x δ ∩ C ⊆ {z : E | ⟪v, z - x⟫_ℝ ≤ ε * ‖z - x‖} := by
      rintro z ⟨hzB, hzC⟩
      exact hbound z hzC (by rwa [← dist_eq_norm])
    have hyc : y ∈ closure (ball x δ ∩ C) :=
      isOpen_ball.inter_closure ⟨mem_ball.2 (by rwa [dist_eq_norm]), hy⟩
    exact hS.closure_subset_iff.2 hsub hyc

/-- **Exercise 6.19**, the clause for nonclosed sets: the normal cone to `C` is
contained in the normal cone to `cl C`.  Monotonicity alone runs the wrong
way -- a larger set has *smaller* regular normal cones -- so the inclusion is
read off the sequential definition, the regular normals along the approaching
sequence being the same for `C` and for `cl C`. -/
theorem normalCone_subset_normalCone_closure (C : Set E) (x : E) :
    normalCone C x ⊆ normalCone (closure C) x := by
  rintro v ⟨hx, xs, vs, hxC, hxto, hvs, hvto⟩
  refine mem_normalCone_of_forall (subset_closure hx) hxto (fun n ↦ ?_) hvto
  rw [regularNormalCone_closure (hxC n)]
  exact hvs n

end Closure

section Boundary

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/-- **Exercise 6.19**, the substantive half: at a point of a closed set that is
not interior there is a normal vector of unit length. -/
theorem exists_norm_eq_one_mem_normalCone_of_notMem_interior {C : Set E}
    (hC : IsClosed C) {x : E} (hx : x ∈ C) (hxi : x ∉ interior C) :
    ∃ v ∈ normalCone C x, ‖v‖ = 1 := by
  have hCnhds : C ∉ nhds x := fun h ↦ hxi (mem_interior_iff_mem_nhds.2 h)
  have hpick : ∀ n : ℕ, ∃ z : E, z ∉ C ∧ ‖z - x‖ < 1 / ((n : ℝ) + 1) := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    by_contra hcon
    push_neg at hcon
    refine hCnhds (mem_nhds_iff.2
      ⟨ball x (1 / ((n : ℝ) + 1)), fun z hz ↦ ?_, isOpen_ball, mem_ball_self hpos⟩)
    by_contra hzC
    have hle := hcon z hzC
    rw [mem_ball, dist_eq_norm] at hz
    linarith
  choose zs hzsC hzsd using hpick
  have hprojne : ∀ n, (projMapping C (zs n)).Nonempty := fun n ↦
    projMapping_nonempty hC ⟨x, hx⟩ (zs n)
  choose ys hys using hprojne
  have hysC : ∀ n, ys n ∈ C := fun n ↦ (hys n).1
  have hysle : ∀ n, ‖ys n - zs n‖ ≤ ‖x - zs n‖ := fun n ↦ (hys n).2 x hx
  have hrpos : ∀ n, 0 < ‖zs n - ys n‖ := by
    intro n
    rw [norm_pos_iff, sub_ne_zero]
    intro h
    exact hzsC n (by rw [h]; exact hysC n)
  have hydist : ∀ n, ‖ys n - x‖ < 2 * (1 / ((n : ℝ) + 1)) := by
    intro n
    have h1 : ‖ys n - zs n‖ ≤ ‖zs n - x‖ := by
      rw [← norm_sub_rev x (zs n)]
      exact hysle n
    have h3 : ‖ys n - x‖ ≤ ‖ys n - zs n‖ + ‖zs n - x‖ := by
      have h := norm_add_le (ys n - zs n) (zs n - x)
      simpa using h
    have h4 := hzsd n
    linarith
  have hyto : Tendsto ys atTop (nhds x) := by
    have hb : Tendsto (fun n : ℕ ↦ 2 * (1 / ((n : ℝ) + 1))) atTop (nhds 0) := by
      have h := Filter.Tendsto.const_mul (2 : ℝ) tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using h
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (f := fun n ↦ dist (ys n) x) (fun n ↦ dist_nonneg)
      (fun n ↦ ?_) hb
    dsimp only
    rw [dist_eq_norm]
    exact (hydist n).le
  have hvsnorm : ∀ n, ‖‖zs n - ys n‖⁻¹ • (zs n - ys n)‖ = 1 := by
    intro n
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hrpos n)),
      inv_mul_cancel₀ (hrpos n).ne']
  have hvsmem : ∀ n, ‖zs n - ys n‖⁻¹ • (zs n - ys n) ∈ regularNormalCone C (ys n) := by
    intro n
    refine proximalNormalCone_subset_regularNormalCone ⟨‖zs n - ys n‖, hrpos n, ?_⟩
    have heq : ys n + ‖zs n - ys n‖ • (‖zs n - ys n‖⁻¹ • (zs n - ys n)) = zs n := by
      rw [smul_smul, mul_inv_cancel₀ (hrpos n).ne', one_smul]
      abel
    rw [heq]
    exact hys n
  have hball : ∀ n, ‖zs n - ys n‖⁻¹ • (zs n - ys n) ∈ closedBall (0 : E) 1 := by
    intro n
    rw [mem_closedBall, dist_zero_right, hvsnorm n]
  obtain ⟨v, -, φ, hφ, hvto⟩ := (isCompact_closedBall (0 : E) 1).tendsto_subseq hball
  refine ⟨v, mem_normalCone_of_forall hx (xs := fun n ↦ ys (φ n))
    (hyto.comp hφ.tendsto_atTop) (fun n ↦ hvsmem (φ n)) hvto, ?_⟩
  have hnorms : Tendsto
      (fun n ↦ ‖‖zs (φ n) - ys (φ n)‖⁻¹ • (zs (φ n) - ys (φ n))‖) atTop (nhds ‖v‖) :=
    hvto.norm
  have hone : ∀ n, ‖‖zs (φ n) - ys (φ n)‖⁻¹ • (zs (φ n) - ys (φ n))‖ = 1 :=
    fun n ↦ hvsnorm (φ n)
  simp only [hone] at hnorms
  exact tendsto_nhds_unique hnorms tendsto_const_nhds

/-- **Exercise 6.19**: the interior points of a closed set are exactly the
points where the normal cone is the zero cone. -/
theorem normalCone_eq_zero_iff_mem_interior {C : Set E} (hC : IsClosed C) {x : E}
    (hx : x ∈ C) : normalCone C x = {0} ↔ x ∈ interior C := by
  refine ⟨fun h ↦ ?_, normalCone_eq_singleton_of_mem_interior⟩
  by_contra hxi
  obtain ⟨v, hv, hvnorm⟩ :=
    exists_norm_eq_one_mem_normalCone_of_notMem_interior hC hx hxi
  rw [h, mem_singleton_iff] at hv
  rw [hv, norm_zero] at hvnorm
  exact zero_ne_one hvnorm

/-- **Exercise 6.19**: a point of a closed set is a boundary point exactly when
some nonzero vector is normal there. -/
theorem mem_frontier_iff_exists_ne_zero_mem_normalCone {C : Set E} (hC : IsClosed C)
    {x : E} (hx : x ∈ C) :
    x ∈ frontier C ↔ ∃ v ∈ normalCone C x, v ≠ 0 := by
  rw [hC.frontier_eq]
  constructor
  · rintro ⟨-, hxi⟩
    obtain ⟨v, hv, hvnorm⟩ :=
      exists_norm_eq_one_mem_normalCone_of_notMem_interior hC hx hxi
    refine ⟨v, hv, fun h ↦ ?_⟩
    rw [h, norm_zero] at hvnorm
    exact zero_ne_one hvnorm
  · rintro ⟨v, hv, hv0⟩
    refine ⟨hx, fun hxi ↦ hv0 ?_⟩
    rw [normalCone_eq_singleton_of_mem_interior hxi, mem_singleton_iff] at hv
    exact hv

/-- **Exercise 6.19**, restated: the boundary points of a closed set are the
points whose normal cone is not the zero cone. -/
theorem mem_frontier_iff_normalCone_ne_zero {C : Set E} (hC : IsClosed C) {x : E}
    (hx : x ∈ C) : x ∈ frontier C ↔ normalCone C x ≠ {0} := by
  rw [hC.frontier_eq, mem_diff]
  constructor
  · intro h
    rw [Ne, normalCone_eq_zero_iff_mem_interior hC hx]
    exact h.2
  · intro h
    refine ⟨hx, fun hxi ↦ h ?_⟩
    exact normalCone_eq_singleton_of_mem_interior hxi

end Boundary

end RW
