/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Interior tangents and recession

Theorem 6.36 and Corollary 6.37. Strict normal inequalities persist near the
base point by outer semicontinuity and compactness of the unit sphere. The
corollary covers a compact set of interior directions by finitely many of the
uniform step neighborhoods of 6.36(c).
-/

import RockafellarWets.Chapter6.RecessionCharacterization
import Mathlib.Analysis.Normed.Affine.Convex

open Filter Metric Set Topology
open scoped InnerProductSpace Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- For a cone, strict inequalities on unit vectors and on all nonzero
vectors are equivalent. -/
theorem forall_unit_inner_lt_iff {K : Set E} (hK : IsCone K) (w : E) :
    (∀ v ∈ K, ‖v‖ = 1 → ⟪v, w⟫_ℝ < 0) ↔
      ∀ v ∈ K, v ≠ 0 → ⟪v, w⟫_ℝ < 0 := by
  constructor
  · intro h v hv hv0
    have hnorm : ‖‖v‖⁻¹ • v‖ = 1 := norm_smul_inv_norm hv0
    have hscaled := h (‖v‖⁻¹ • v) (hK.2 hv (inv_pos.2 (norm_pos_iff.2 hv0))) hnorm
    rw [real_inner_smul_left] at hscaled
    have hpos : 0 < ‖v‖⁻¹ := inv_pos.2 (norm_pos_iff.2 hv0)
    nlinarith
  · intro h v hv hvnorm
    apply h v hv
    intro hv0
    simp [hv0] at hvnorm

/-- **Theorem 6.36(a),(e)**: the interior regular tangent directions are
exactly those strictly opposed to all unit normals at the base point. -/
theorem mem_interior_regularTangentCone_iff_unit_normal_inner_lt
    {C : Set E} {x w : E} (hx : x ∈ C) (hC : IsLocallyClosedAt C x) :
    w ∈ interior (regularTangentCone C x) ↔
      ∀ v ∈ normalCone C x, ‖v‖ = 1 → ⟪v, w⟫_ℝ < 0 := by
  rw [regularTangentCone_eq_polarCone_normalCone hx hC,
    mem_interior_polarCone_iff_inner_lt_zero (isClosed_normalCone C x) (isCone_normalCone hx)]
  exact (forall_unit_inner_lt_iff (isCone_normalCone hx) w).symm

/-- Strict inequalities on all unit normals persist near a feasible base
point. Compactness of the unit sphere makes the outer-limit argument uniform. -/
theorem exists_nhds_unit_normal_inner_lt {C : Set E} {xbar w : E}
    (hxbar : xbar ∈ C)
    (hstrict : ∀ v ∈ normalCone C xbar, ‖v‖ = 1 → ⟪v, w⟫_ℝ < 0) :
    ∃ V ∈ nhds xbar, ∀ x ∈ C ∩ V,
      ∀ v ∈ normalCone C x, ‖v‖ = 1 → ⟪v, w⟫_ℝ < 0 := by
  by_contra hnot
  have hpick : ∀ n : ℕ, ∃ x ∈ C ∩ ball xbar (1 / ((n : ℝ) + 1)),
      ∃ v ∈ normalCone C x, ‖v‖ = 1 ∧ 0 ≤ ⟪v, w⟫_ℝ := by
    intro n
    have hbad : ¬ ∀ x ∈ C ∩ ball xbar (1 / ((n : ℝ) + 1)),
        ∀ v ∈ normalCone C x, ‖v‖ = 1 → ⟪v, w⟫_ℝ < 0 := by
      intro h
      exact hnot ⟨_, ball_mem_nhds _ (by positivity), h⟩
    push_neg at hbad
    exact hbad
  choose xs hxs vs hvs hvsnorm hvsinner using hpick
  have hxsto : Tendsto xs atTop (nhds xbar) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n ↦ dist_nonneg)
      (fun n ↦ (Metric.mem_ball.1 (hxs n).2).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hvsSphere : ∀ n, vs n ∈ sphere (0 : E) 1 := by
    intro n
    simpa only [mem_sphere, dist_zero_right] using hvsnorm n
  obtain ⟨v, hvSphere, φ, hφ, hvsto⟩ :=
    (isCompact_sphere (0 : E) 1).tendsto_subseq hvsSphere
  have hvnorm : ‖v‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using hvSphere
  have hvC : v ∈ normalCone C xbar :=
    mem_normalCone_of_tendsto hxbar (fun n ↦ (hxs (φ n)).1)
      (hxsto.comp hφ.tendsto_atTop) (fun n ↦ hvs (φ n)) hvsto
  have hnonneg : 0 ≤ ⟪v, w⟫_ℝ :=
    ge_of_tendsto (hvsto.inner tendsto_const_nhds)
      (Eventually.of_forall fun n ↦ hvsinner (φ n))
  exact (not_lt_of_ge hnonneg) (hstrict v hvC hvnorm)

/-- **Theorem 6.36(d),(e)**, the neighborhood and pointwise strict tests. -/
theorem unit_normal_inner_lt_iff_exists_nhds {C : Set E} {xbar w : E}
    (hxbar : xbar ∈ C) :
    (∀ v ∈ normalCone C xbar, ‖v‖ = 1 → ⟪v, w⟫_ℝ < 0) ↔
      ∃ V ∈ nhds xbar, ∀ x ∈ C ∩ V,
        ∀ v ∈ normalCone C x, ‖v‖ = 1 → ⟪v, w⟫_ℝ < 0 := by
  refine ⟨exists_nhds_unit_normal_inner_lt hxbar, ?_⟩
  rintro ⟨V, hV, h⟩
  exact h xbar ⟨hxbar, mem_of_mem_nhds hV⟩

/-- Every interior regular tangent direction is a local recession direction. -/
theorem interior_regularTangentCone_subset_localRecessionCone
    {C : Set E} {xbar : E} (hxbar : xbar ∈ C) (hC : IsLocallyClosedAt C xbar) :
    interior (regularTangentCone C xbar) ⊆ localRecessionCone C xbar := by
  intro w hw
  obtain ⟨V, hV, hstrict⟩ := exists_nhds_unit_normal_inner_lt hxbar
    ((mem_interior_regularTangentCone_iff_unit_normal_inner_lt hxbar hC).1 hw)
  apply mem_localRecessionCone_of_regularNormal_nonpos hxbar hC hV
  intro x hx v hv
  by_cases hv0 : v = 0
  · simp [hv0]
  · exact ((forall_unit_inner_lt_iff (isCone_normalCone hx.1) w).1 (hstrict x hx)
      v (regularNormalCone_subset_normalCone C x hv) hv0).le

/-- **Theorem 6.36(a),(b)**: the local recession cone and the regular tangent
cone have the same interior. -/
theorem interior_localRecessionCone_eq_interior_regularTangentCone
    {C : Set E} {xbar : E} (hxbar : xbar ∈ C) (hC : IsLocallyClosedAt C xbar) :
    interior (localRecessionCone C xbar) = interior (regularTangentCone C xbar) := by
  apply Subset.antisymm (interior_mono localRecessionCone_subset_regularTangentCone)
  exact interior_maximal (interior_regularTangentCone_subset_localRecessionCone hxbar hC)
    isOpen_interior

/-- **Theorem 6.36(b),(c)**: an interior recession direction has one
neighborhood of directions and one uniform local step bound. -/
theorem mem_interior_localRecessionCone_iff_uniform_recession
    {C : Set E} {xbar w : E} (hxbar : xbar ∈ C) :
    w ∈ interior (localRecessionCone C xbar) ↔
      ∃ W ∈ nhds w, ∃ V ∈ nhds xbar, ∃ ε > 0,
        ∀ x ∈ C ∩ V, ∀ τ ∈ Icc (0 : ℝ) ε, ∀ z ∈ W, x + τ • z ∈ C := by
  constructor
  · intro hw
    obtain ⟨b, hwb, hbR⟩ := exists_mem_interior_convexHull_affineBasis
      (mem_interior_iff_mem_nhds.1 hw)
    have hb : ∀ i, b i ∈ localRecessionCone C xbar :=
      fun i ↦ hbR (subset_convexHull ℝ _ (mem_range_self i))
    obtain ⟨V, hV, ε, hε, hstep⟩ :=
      exists_nhds_forall_smul_mem_of_mem_convexHull_range hb
    exact ⟨convexHull ℝ (range b), mem_interior_iff_mem_nhds.1 hwb,
      V, hV, ε, hε, hstep⟩
  · rintro ⟨W, hW, V, hV, ε, hε, hstep⟩
    apply mem_interior_iff_mem_nhds.2
    apply mem_of_superset hW
    intro z hz
    exact ⟨hxbar, V, hV, ε, hε, fun x hx τ hτ ↦ hstep x hx τ hτ z hz⟩

/-- **Theorem 6.36(a),(c)**, the uniform forward-step formulation. -/
theorem mem_interior_regularTangentCone_iff_uniform_recession
    {C : Set E} {xbar w : E} (hxbar : xbar ∈ C) (hC : IsLocallyClosedAt C xbar) :
    w ∈ interior (regularTangentCone C xbar) ↔
      ∃ W ∈ nhds w, ∃ V ∈ nhds xbar, ∃ ε > 0,
        ∀ x ∈ C ∩ V, ∀ τ ∈ Icc (0 : ℝ) ε, ∀ z ∈ W, x + τ • z ∈ C := by
  rw [← interior_localRecessionCone_eq_interior_regularTangentCone hxbar hC]
  exact mem_interior_localRecessionCone_iff_uniform_recession hxbar

/-- The common strict/recession/interior directions of Theorem 6.36 exist
exactly when the normal cone is pointed. -/
theorem interior_localRecessionCone_nonempty_iff_isPointed_normalCone
    {C : Set E} {xbar : E} (hxbar : xbar ∈ C) (hC : IsLocallyClosedAt C xbar) :
    (interior (localRecessionCone C xbar)).Nonempty ↔ IsPointed (normalCone C xbar) := by
  rw [interior_localRecessionCone_eq_interior_regularTangentCone hxbar hC,
    regularTangentCone_eq_polarCone_normalCone hxbar hC]
  exact interior_polarCone_nonempty_iff_isPointed
    (isClosed_normalCone C xbar) (isCone_normalCone hxbar)

/-- **Theorem 6.36**, the concluding closure formula under pointedness. -/
theorem closure_localRecessionCone_eq_regularTangentCone_of_isPointed
    {C : Set E} {xbar : E} (hxbar : xbar ∈ C) (hC : IsLocallyClosedAt C xbar)
    (hpointed : IsPointed (normalCone C xbar)) :
    closure (localRecessionCone C xbar) = regularTangentCone C xbar := by
  have hR : (interior (localRecessionCone C xbar)).Nonempty :=
    (interior_localRecessionCone_nonempty_iff_isPointed_normalCone hxbar hC).2 hpointed
  have hT : (interior (regularTangentCone C xbar)).Nonempty := by
    rwa [interior_localRecessionCone_eq_interior_regularTangentCone hxbar hC] at hR
  calc
    closure (localRecessionCone C xbar) =
        closure (interior (localRecessionCone C xbar)) :=
      (convex_localRecessionCone.closure_interior_eq_closure_of_nonempty_interior hR).symm
    _ = closure (interior (regularTangentCone C xbar)) := by
      rw [interior_localRecessionCone_eq_interior_regularTangentCone hxbar hC]
    _ = closure (regularTangentCone C xbar) :=
      (convex_regularTangentCone hxbar).closure_interior_eq_closure_of_nonempty_interior hT
    _ = regularTangentCone C xbar := (isClosed_regularTangentCone C xbar).closure_eq

/-- **Corollary 6.37**: a compact set of interior regular tangent directions
is contained in every magnified difference set `τ⁻¹(C - x)` for all
sufficiently small `τ > 0` and all feasible `x` near the base point. -/
theorem exists_nhds_forall_subset_blowUp_of_isCompact
    {C : Set E} {xbar : E} (hxbar : xbar ∈ C) (hC : IsLocallyClosedAt C xbar)
    {B : Set E} (hB : IsCompact B)
    (hBint : B ⊆ interior (regularTangentCone C xbar)) :
    ∃ ε > 0, ∃ V ∈ nhds xbar, ∀ x ∈ C ∩ V, ∀ τ ∈ Ioo (0 : ℝ) ε, B ⊆ blowUp C x τ := by
  have hpt : ∀ w ∈ B, ∃ W ∈ nhds w, ∃ V ∈ nhds xbar, ∃ ε > 0,
      ∀ x ∈ C ∩ V, ∀ τ ∈ Icc (0 : ℝ) ε, ∀ z ∈ W, x + τ • z ∈ C := fun w hw ↦
    (mem_interior_regularTangentCone_iff_uniform_recession hxbar hC).1 (hBint hw)
  choose! W hW V hV ε hε hstep using hpt
  obtain ⟨t, htB, hcover⟩ := hB.elim_nhds_subcover W (fun w hw ↦ hW w hw)
  rcases t.eq_empty_or_nonempty with ht | ht
  · refine ⟨1, one_pos, univ, univ_mem, fun x _ τ _ w hw ↦ ?_⟩
    have := hcover hw
    simp [ht] at this
  refine ⟨t.inf' ht ε, (Finset.lt_inf'_iff ht).2 fun w hw ↦ hε w (htB w hw),
    ⋂ w ∈ t, V w, (Filter.biInter_finset_mem t).2 fun w hw ↦ hV w (htB w hw), ?_⟩
  intro x hx τ hτ w hw
  obtain ⟨w', hw't, hwW⟩ := mem_iUnion₂.1 (hcover hw)
  have hxV : x ∈ V w' := mem_iInter₂.1 hx.2 w' hw't
  have hmem : x + τ • w ∈ C :=
    hstep w' (htB w' hw't) x ⟨hx.1, hxV⟩ τ
      ⟨hτ.1.le, hτ.2.le.trans (Finset.inf'_le ε hw't)⟩ w hwW
  refine ⟨x + τ • w, hmem, ?_⟩
  change τ⁻¹ • (x + τ • w - x) = w
  rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hτ.1.ne', one_smul]

/-- **Corollary 6.37**, the tangent consequence: the compact set lies in the
tangent cone at every feasible point of a neighborhood. -/
theorem exists_nhds_forall_subset_tangentCone_of_isCompact
    {C : Set E} {xbar : E} (hxbar : xbar ∈ C) (hC : IsLocallyClosedAt C xbar)
    {B : Set E} (hB : IsCompact B)
    (hBint : B ⊆ interior (regularTangentCone C xbar)) :
    ∃ V ∈ nhds xbar, ∀ x ∈ C ∩ V, B ⊆ tangentCone C x := by
  obtain ⟨ε, hε, V, hV, hblow⟩ :=
    exists_nhds_forall_subset_blowUp_of_isCompact hxbar hC hB hBint
  refine ⟨V, hV, fun x hx w hw ↦ ?_⟩
  let τs : ℕ → ℝ := fun n ↦ ε / 2 * (1 / ((n : ℝ) + 1))
  have hτpos : ∀ n, 0 < τs n := fun n ↦ by dsimp only [τs]; positivity
  have hτlt : ∀ n, τs n < ε := by
    intro n
    dsimp only [τs]
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    nlinarith
  have hτ0 : Tendsto τs atTop (nhds 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (ε / 2)
    simpa only [mul_zero] using this
  refine mem_tangentCone_of_forall (xs := fun n ↦ x + τs n • w) (τs := τs)
    (fun n ↦ ?_) hτpos hτ0 ?_
  · obtain ⟨y, hy, hyw⟩ := hblow x hx (τs n) ⟨hτpos n, hτlt n⟩ hw
    have : y = x + τs n • w := by
      rw [← hyw, smul_smul, mul_inv_cancel₀ (hτpos n).ne', one_smul, add_sub_cancel]
    change x + τs n • w ∈ C
    rwa [← this]
  · refine tendsto_const_nhds.congr fun n ↦ ?_
    change w = (τs n)⁻¹ • (x + τs n • w - x)
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ (hτpos n).ne', one_smul]

/-- **Corollary 6.37** at a Clarke regular point: the interior of the
ordinary tangent cone may be used instead. -/
theorem exists_nhds_forall_subset_blowUp_of_isCompact_of_isClarkeRegularAt
    {C : Set E} {xbar : E} (hxbar : xbar ∈ C) (hreg : IsClarkeRegularAt C xbar)
    {B : Set E} (hB : IsCompact B) (hBint : B ⊆ interior (tangentCone C xbar)) :
    ∃ ε > 0, ∃ V ∈ nhds xbar, ∀ x ∈ C ∩ V, ∀ τ ∈ Ioo (0 : ℝ) ε, B ⊆ blowUp C x τ := by
  apply exists_nhds_forall_subset_blowUp_of_isCompact hxbar hreg.1 hB
  rwa [← tangentCone_eq_regularTangentCone_of_isClarkeRegularAt hxbar hreg]

end RW
