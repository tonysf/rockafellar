/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Proximal Normals and Convex Projections

Example 6.16 identifies displacements from a point to one of its nearest
points as regular normals.  Proposition 6.17 says that, for a convex set,
these proximal normals are exactly the usual normal cone and expresses the
projection mapping as the inverse of `I + N_C`.
-/

import RockafellarWets.Chapter5.ProjectionGraphicalConvergence
import RockafellarWets.Chapter6.ConvexSets
import Mathlib.Analysis.InnerProductSpace.Convex

open Set
open scoped InnerProductSpace

namespace RW

section ProximalNormals

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Example 6.16**: a vector is proximal normal to `C` at `x` when a
positive step from `x` in that direction has `x` as a nearest point in `C`.
-/
def proximalNormalCone (C : Set E) (x : E) : Set E :=
  {v | ∃ τ : ℝ, 0 < τ ∧ x ∈ projMapping C (x + τ • v)}

@[simp]
theorem mem_proximalNormalCone {C : Set E} {x v : E} :
    v ∈ proximalNormalCone C x ↔
      ∃ τ : ℝ, 0 < τ ∧ x ∈ projMapping C (x + τ • v) :=
  Iff.rfl

/-- Proximal normals, like the other normal cones, are empty away from the
set. -/
theorem proximalNormalCone_eq_empty {C : Set E} {x : E} (hx : x ∉ C) :
    proximalNormalCone C x = ∅ := by
  refine eq_empty_of_forall_notMem fun v hv ↦ hx ?_
  obtain ⟨τ, hτ, hproj⟩ := hv
  exact hproj.1

/-- At a feasible point the proximal normal cone is a cone. -/
theorem isCone_proximalNormalCone {C : Set E} {x : E} (hx : x ∈ C) :
    IsCone (proximalNormalCone C x) := by
  constructor
  · refine ⟨1, one_pos, ?_⟩
    simpa using (mem_projMapping_self hx)
  · rintro v ⟨τ, hτ, hproj⟩ c hc
    refine ⟨τ / c, by positivity, ?_⟩
    have hscalar : τ / c * c = τ := div_mul_cancel₀ τ (ne_of_gt hc)
    simpa only [smul_smul, hscalar] using hproj

/-- Squaring the nearest-point inequality gives the basic quadratic
inequality used throughout this file. -/
private theorem mem_projMapping_add_smul_iff_two_mul_inner_le
    {C : Set E} {x v : E} {τ : ℝ} (hτ : 0 < τ) :
    x ∈ projMapping C (x + τ • v) ↔
      x ∈ C ∧ ∀ y ∈ C, 2 * τ * ⟪v, y - x⟫_ℝ ≤ ‖y - x‖ ^ 2 := by
  constructor
  · rintro ⟨hx, hmin⟩
    refine ⟨hx, ?_⟩
    intro y hy
    have hnorm := hmin y hy
    have hsq : ‖x - (x + τ • v)‖ ^ 2 ≤ ‖y - (x + τ • v)‖ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hnorm
    have hxsub : x - (x + τ • v) = -(τ • v) := by module
    have hysub : y - (x + τ • v) = (y - x) - τ • v := by module
    rw [hxsub, norm_neg, hysub, norm_sub_sq_real] at hsq
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hτ,
      real_inner_smul_right] at hsq
    rw [real_inner_comm v (y - x)] at hsq
    linarith
  · rintro ⟨hx, hquad⟩
    refine ⟨hx, ?_⟩
    intro y hy
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
    have hq := hquad y hy
    have hxsub : x - (x + τ • v) = -(τ • v) := by module
    have hysub : y - (x + τ • v) = (y - x) - τ • v := by module
    rw [hxsub, norm_neg, hysub, norm_sub_sq_real]
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hτ,
      real_inner_smul_right]
    rw [real_inner_comm v (y - x)]
    linarith

/-- The quadratic-support characterization of a proximal normal.  The
constant is the reciprocal of twice the positive projection step. -/
theorem mem_proximalNormalCone_iff_quadratic_support {C : Set E} {x v : E} :
    v ∈ proximalNormalCone C x ↔
      x ∈ C ∧ ∃ ε > 0, ∀ y ∈ C,
        ⟪v, y - x⟫_ℝ ≤ ε * ‖y - x‖ ^ 2 := by
  constructor
  · rintro ⟨τ, hτ, hproj⟩
    have hquad :=
      (mem_projMapping_add_smul_iff_two_mul_inner_le hτ).1 hproj
    refine ⟨hquad.1, 1 / (2 * τ), by positivity, ?_⟩
    intro y hy
    rw [one_div_mul_eq_div]
    apply (le_div_iff₀ (by positivity : 0 < 2 * τ)).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hquad.2 y hy
  · rintro ⟨hx, ε, hε, hbound⟩
    let τ : ℝ := 1 / (2 * ε)
    have hτ : 0 < τ := by
      dsimp [τ]
      positivity
    refine ⟨τ, hτ,
      (mem_projMapping_add_smul_iff_two_mul_inner_le hτ).2 ⟨hx, ?_⟩⟩
    intro y hy
    have hb := hbound y hy
    have hmul := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2 * τ)
    calc
      2 * τ * ⟪v, y - x⟫_ℝ
          ≤ 2 * τ * (ε * ‖y - x‖ ^ 2) := hmul
      _ = (2 * τ * ε) * ‖y - x‖ ^ 2 := by ring
      _ = ‖y - x‖ ^ 2 := by
        have hεne : ε ≠ 0 := ne_of_gt hε
        dsimp [τ]
        field_simp

/-- Every proximal normal is a regular normal. -/
theorem proximalNormalCone_subset_regularNormalCone {C : Set E} {x : E} :
    proximalNormalCone C x ⊆ regularNormalCone C x := by
  intro v hv
  obtain ⟨hx, κ, hκ, hbound⟩ :=
    mem_proximalNormalCone_iff_quadratic_support.1 hv
  rw [mem_regularNormalCone_iff]
  refine ⟨hx, ?_⟩
  intro ε hε
  refine ⟨ε / κ, by positivity, ?_⟩
  intro y hy hdist
  have hb := hbound y hy
  have hsmall : κ * ‖y - x‖ < ε := by
    have hmul := mul_lt_mul_of_pos_left hdist hκ
    have hκne : κ ≠ 0 := ne_of_gt hκ
    calc
      κ * ‖y - x‖ < κ * (ε / κ) := hmul
      _ = ε := by field_simp
  calc
    ⟪v, y - x⟫_ℝ ≤ κ * ‖y - x‖ ^ 2 := hb
    _ = (κ * ‖y - x‖) * ‖y - x‖ := by ring
    _ ≤ ε * ‖y - x‖ :=
      mul_le_mul_of_nonneg_right hsmall.le (norm_nonneg _)

/-- **Example 6.16**: the displacement from a nearest point to the point
being projected is a regular normal. -/
theorem sub_mem_regularNormalCone_of_mem_projMapping {C : Set E} {x xbar : E}
    (hx : xbar ∈ projMapping C x) :
    x - xbar ∈ regularNormalCone C xbar := by
  apply proximalNormalCone_subset_regularNormalCone
  refine ⟨1, one_pos, ?_⟩
  have hcenter : xbar + (1 : ℝ) • (x - xbar) = x := by module
  rw [hcenter]
  exact hx

/-- Nonnegative multiples of a projection displacement are regular normals.
-/
theorem nonneg_smul_sub_mem_regularNormalCone_of_mem_projMapping
    {C : Set E} {x xbar : E} (hx : xbar ∈ projMapping C x)
    {c : ℝ} (hc : 0 ≤ c) :
    c • (x - xbar) ∈ regularNormalCone C xbar := by
  rcases hc.eq_or_lt with rfl | hc
  · simpa using (isCone_regularNormalCone hx.1).1
  · exact (isCone_regularNormalCone hx.1).2
      (sub_mem_regularNormalCone_of_mem_projMapping hx) hc

/-- Moving a strictly smaller positive distance in a proximal-normal
direction makes the original point the unique projection. -/
theorem projMapping_add_smul_eq_singleton_of_lt
    {C : Set E} {x v : E} {τ τ' : ℝ}
    (hproj : x ∈ projMapping C (x + τ • v))
    (hτ' : 0 < τ') (hlt : τ' < τ) :
    projMapping C (x + τ' • v) = {x} := by
  have hτ : 0 < τ := lt_trans hτ' hlt
  let ε : ℝ := 1 - τ' / τ
  have hε : 0 < ε := by
    dsimp [ε]
    exact sub_pos.2 ((div_lt_one hτ).2 hlt)
  have hε1 : ε < 1 := by
    dsimp [ε]
    exact sub_lt_self 1 (div_pos hτ' hτ)
  have hcenter :
      (x + τ • v) + ε • (x - (x + τ • v)) = x + τ' • v := by
    have hcoeff : τ - ε * τ = τ' := by
      dsimp [ε]
      field_simp [ne_of_gt hτ]
      ring
    calc
      (x + τ • v) + ε • (x - (x + τ • v))
          = x + (τ - ε * τ) • v := by module
      _ = x + τ' • v := by rw [hcoeff]
  rw [← hcenter]
  exact projMapping_segment hproj hε hε1

/-- For a convex set, normality is equivalent to being the projection after
one unit step in the normal direction. -/
theorem mem_normalCone_iff_mem_projMapping_add_of_convex
    {C : Set E} {x v : E} (hC : Convex ℝ C) (hx : x ∈ C) :
    v ∈ normalCone C x ↔ x ∈ projMapping C (x + v) := by
  constructor
  · intro hv
    have hsupp : ∀ y ∈ C, ⟪v, y - x⟫_ℝ ≤ 0 := by
      rw [normalCone_eq_of_convex hC hx] at hv
      exact hv
    rw [mem_projMapping]
    refine ⟨hx, ?_⟩
    intro y hy
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
    have hxy : x - (x + v) = -v := by module
    have hyy : y - (x + v) = (y - x) - v := by module
    rw [hxy, norm_neg, hyy, norm_sub_sq_real]
    rw [real_inner_comm v (y - x)]
    have hs := hsupp y hy
    have hsqnonneg : 0 ≤ ‖y - x‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]
      exact real_inner_self_nonneg
    linarith
  · intro hproj
    have hreg := sub_mem_regularNormalCone_of_mem_projMapping hproj
    have hvreg : v ∈ regularNormalCone C x := by
      convert hreg using 1
      module
    exact regularNormalCone_subset_normalCone C x hvreg

/-- **Proposition 6.17**: proximal and limiting normals agree for a convex
set. -/
theorem proximalNormalCone_eq_normalCone_of_convex
    {C : Set E} {x : E} (hC : Convex ℝ C) (hx : x ∈ C) :
    proximalNormalCone C x = normalCone C x := by
  apply Subset.antisymm
  · intro v hv
    exact regularNormalCone_subset_normalCone C x
      (proximalNormalCone_subset_regularNormalCone hv)
  · intro v hv
    refine ⟨1, one_pos, ?_⟩
    simpa using
      (mem_normalCone_iff_mem_projMapping_add_of_convex hC hx).1 hv

/-- The mapping form of `P_C = (I + N_C)⁻¹` for a convex set. -/
theorem projMapping_eq_svInv_add_normalCone_of_convex {C : Set E}
    (hC : Convex ℝ C) :
    projMapping C =
      svInv (fun x ↦ (fun v ↦ x + v) '' normalCone C x) := by
  funext z
  ext x
  rw [mem_svInv]
  constructor
  · intro hproj
    refine ⟨z - x, ?_, by module⟩
    exact regularNormalCone_subset_normalCone C x
      (sub_mem_regularNormalCone_of_mem_projMapping hproj)
  · rintro ⟨v, hv, rfl⟩
    exact (mem_normalCone_iff_mem_projMapping_add_of_convex hC hv.1).1 hv

/-- Pointwise, the normal cone is the inverse projection mapping minus the
identity. -/
theorem normalCone_eq_image_sub_svInv_projMapping_of_convex {C : Set E}
    (hC : Convex ℝ C) (x : E) :
    normalCone C x =
      (fun z ↦ z - x) '' svInv (projMapping C) x := by
  ext v
  constructor
  · intro hv
    refine ⟨x + v, ?_, by module⟩
    rw [mem_svInv]
    exact (mem_normalCone_iff_mem_projMapping_add_of_convex hC hv.1).1 hv
  · rintro ⟨z, hz, rfl⟩
    rw [mem_svInv] at hz
    exact regularNormalCone_subset_normalCone C x
      (sub_mem_regularNormalCone_of_mem_projMapping hz)

end ProximalNormals

end RW
