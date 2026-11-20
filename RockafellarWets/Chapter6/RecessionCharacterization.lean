/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Recession vectors from tangents and normals

Proposition 6.35. The converse uses a one-sided mean-value inequality for
squared distance along a ray. A nearest point gives a differentiable upper
bound whose derivative is the inner product with a projection normal.
-/

import RockafellarWets.Chapter6.RecessionCones
import RockafellarWets.Chapter6.TangentNormalPolarity
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus

open Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A ray cannot leave a closed set if every projection displacement along
it has nonpositive inner product with its direction. -/
theorem add_smul_mem_of_projection_inner_nonpos {C : Set E} (hC : IsClosed C)
    {x w : E} (hx : x ∈ C) {T : ℝ} (hT : 0 ≤ T)
    (hproj : ∀ t ∈ Ico (0 : ℝ) T, ∀ p ∈ projMapping C (x + t • w),
      ⟪x + t • w - p, w⟫_ℝ ≤ 0) :
    x + T • w ∈ C := by
  let f : ℝ → ℝ := fun t ↦ infDist (x + t • w) C ^ 2
  have hfcont : Continuous f :=
    ((continuous_infDist_pt C).comp (continuous_const.add
      (continuous_id.smul continuous_const))).pow 2
  have hf0 : f 0 = 0 := by simp [f, infDist_zero_of_mem hx]
  have hfnonpos : ∀ t ∈ Icc (0 : ℝ) T, f t ≤ 0 := by
    apply image_le_of_liminf_slope_right_le_deriv_boundary hfcont.continuousOn
      (B := fun _ ↦ (0 : ℝ)) (B' := fun _ ↦ (0 : ℝ))
      (by rw [hf0]) continuousOn_const
      (fun t _ ↦ hasDerivWithinAt_const t _ (0 : ℝ))
    intro t ht r hr
    obtain ⟨p, hp⟩ := projMapping_nonempty hC ⟨x, hx⟩ (x + t • w)
    let q : ℝ → ℝ := fun s ↦ ‖x + s • w - p‖ ^ 2
    have hpdist : ‖x + t • w - p‖ = infDist (x + t • w) C := by
      simpa only [dist_eq_norm] using (mem_projMapping_iff_dist.1 hp).2
    have hqderiv : HasDerivAt q (2 * ⟪x + t • w - p, w⟫_ℝ) t := by
      simpa only [q, one_smul] using
        ((((hasDerivAt_id t).smul_const w).const_add x).sub_const p).norm_sq
    have hqfreq : ∃ᶠ s in nhdsWithin t (Ioi t), slope q t s < r :=
      hqderiv.hasDerivWithinAt.liminf_right_slope_le (by
        have := hproj t ht p hp
        linarith)
    apply (hqfreq.and_eventually self_mem_nhdsWithin).mono
    rintro s ⟨hs, hts⟩
    have hfs : f s ≤ q s := by
      apply (sq_le_sq₀ (infDist_nonneg : 0 ≤ infDist (x + s • w) C) (norm_nonneg _)).2
      simpa only [dist_eq_norm] using (infDist_le_dist_of_mem hp.1 (x := x + s • w))
    have hft : f t = q t := by simp only [f, q, hpdist]
    apply lt_of_le_of_lt _ hs
    rw [slope_def_field, slope_def_field, hft]
    exact div_le_div_of_nonneg_right (sub_le_sub_right hfs _) (sub_pos.2 hts).le
  apply (hC.mem_iff_infDist_zero ⟨x, hx⟩).2
  have hsq := hfnonpos T ⟨hT, le_rfl⟩
  have hnonneg : 0 ≤ infDist (x + T • w) C := infDist_nonneg
  dsimp [f] at hsq
  nlinarith [sq_nonneg (infDist (x + T • w) C)]

/-- Nearby regular-normal inequalities imply a uniform short-ray property
for a closed set. The same neighborhood and time bound work for all nearby
feasible starting points. -/
theorem mem_localRecessionCone_of_regularNormal_nonpos_of_isClosed
    {C V : Set E} (hC : IsClosed C) {xbar w : E} (hxbar : xbar ∈ C)
    (hV : V ∈ nhds xbar)
    (hnormal : ∀ x ∈ C ∩ V, ∀ v ∈ regularNormalCone C x, ⟪v, w⟫_ℝ ≤ 0) :
    w ∈ localRecessionCone C xbar := by
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.1 hV
  let ε : ℝ := R / (4 * (‖w‖ + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεbound : ε * (‖w‖ + 1) = R / 4 := by
    dsimp [ε]
    field_simp
  apply mem_localRecessionCone_iff_exists_ball.2
  refine ⟨hxbar, R / 4, by positivity, ε, hε, ?_⟩
  intro x hxC hxxbar τ hτ
  apply add_smul_mem_of_projection_inner_nonpos hC hxC hτ.1
  intro t ht p hp
  have htx : dist (x + t • w) x = t * ‖w‖ := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht.1]
  have hpdist : dist p (x + t • w) ≤ t * ‖w‖ := by
    rw [dist_comm, (mem_projMapping_iff_dist.1 hp).2, ← htx]
    exact infDist_le_dist_of_mem hxC
  have hpd : dist p xbar ≤ 2 * (t * ‖w‖) + dist x xbar := by
    have h₁ := dist_triangle p (x + t • w) xbar
    have h₂ := dist_triangle (x + t • w) x xbar
    rw [htx] at h₂
    linarith
  have htε : t ≤ ε := ht.2.le.trans hτ.2
  have htw : t * ‖w‖ ≤ R / 4 := by
    have h₁ := mul_le_mul_of_nonneg_right htε (norm_nonneg w)
    nlinarith
  have hpV : p ∈ V := hball (Metric.mem_ball.2 (by linarith))
  exact hnormal p ⟨hp.1, hpV⟩ (x + t • w - p)
    (sub_mem_regularNormalCone_of_mem_projMapping hp)

/-- The implication from regular-normal inequalities to recession is local,
so local closedness at the base point suffices. -/
theorem mem_localRecessionCone_of_regularNormal_nonpos
    {C V : Set E} {xbar w : E} (hxbar : xbar ∈ C)
    (hC : IsLocallyClosedAt C xbar) (hV : V ∈ nhds xbar)
    (hnormal : ∀ x ∈ C ∩ V, ∀ v ∈ regularNormalCone C x, ⟪v, w⟫_ℝ ≤ 0) :
    w ∈ localRecessionCone C xbar := by
  obtain ⟨U, hU, -, hCU⟩ := hC
  obtain ⟨O, hOUV, hO, hxO⟩ := _root_.mem_nhds_iff.1 (inter_mem hU hV)
  have hxCU : xbar ∈ C ∩ U := ⟨hxbar, mem_of_mem_nhds hU⟩
  have hnormalCU : ∀ x ∈ (C ∩ U) ∩ O,
      ∀ v ∈ regularNormalCone (C ∩ U) x, ⟪v, w⟫_ℝ ≤ 0 := by
    intro x hx v hv
    have hUx : U ∈ nhds x := mem_of_superset (hO.mem_nhds hx.2)
      (fun y hy ↦ (hOUV hy).1)
    rw [regularNormalCone_inter_nhds hUx] at hv
    exact hnormal x ⟨hx.1.1, (hOUV hx.2).2⟩ v hv
  obtain ⟨-, W, hW, ε, hε, hstep⟩ :=
    mem_localRecessionCone_of_regularNormal_nonpos_of_isClosed hCU hxCU
      (hO.mem_nhds hxO) hnormalCU
  refine ⟨hxbar, W ∩ O, inter_mem hW (hO.mem_nhds hxO), ε, hε, ?_⟩
  intro x hx τ hτ
  exact (hstep x ⟨⟨hx.1, (hOUV hx.2.2).1⟩, hx.2.1⟩ τ hτ).1

omit [FiniteDimensional ℝ E] in
/-- A recession direction remains a recession direction at every feasible
point in a sufficiently small open neighborhood. -/
theorem exists_open_forall_mem_localRecessionCone
    {C : Set E} {xbar w : E} (hw : w ∈ localRecessionCone C xbar) :
    ∃ V : Set E, IsOpen V ∧ xbar ∈ V ∧
      ∀ x ∈ C ∩ V, w ∈ localRecessionCone C x := by
  obtain ⟨-, U, hU, ε, hε, hstep⟩ := hw
  obtain ⟨V, hVU, hV, hxV⟩ := _root_.mem_nhds_iff.1 hU
  refine ⟨V, hV, hxV, ?_⟩
  intro x hx
  exact ⟨hx.1, U, mem_of_superset (hV.mem_nhds hx.2) hVU, ε, hε, hstep⟩

omit [FiniteDimensional ℝ E] in
/-- On an open set, the inequalities for regular normals imply the same
inequalities for limiting normals, by their sequential definition. -/
theorem forall_normal_nonpos_of_forall_regularNormal_nonpos
    {C V : Set E} {w : E} (hV : IsOpen V)
    (h : ∀ x ∈ C ∩ V, ∀ v ∈ regularNormalCone C x, ⟪v, w⟫_ℝ ≤ 0) :
    ∀ x ∈ C ∩ V, ∀ v ∈ normalCone C x, ⟪v, w⟫_ℝ ≤ 0 := by
  intro x hx v hv
  obtain ⟨-, xs, vs, hxsC, hxsto, hvs, hvsto⟩ := hv
  apply le_of_tendsto (hvsto.inner tendsto_const_nhds)
  filter_upwards [hxsto.eventually (hV.mem_nhds hx.2)] with n hn
  exact h (xs n) ⟨hxsC n, hn⟩ (vs n) (hvs n)

/-- **Proposition 6.35(d)**: local recession is equivalent to nonpositive
pairing with every regular normal at nearby feasible points. -/
theorem mem_localRecessionCone_iff_exists_open_regularNormal_nonpos
    {C : Set E} {xbar w : E} (hxbar : xbar ∈ C)
    (hC : IsLocallyClosedAt C xbar) :
    w ∈ localRecessionCone C xbar ↔
      ∃ V : Set E, IsOpen V ∧ xbar ∈ V ∧
        ∀ x ∈ C ∩ V, ∀ v ∈ regularNormalCone C x, ⟪v, w⟫_ℝ ≤ 0 := by
  constructor
  · intro hw
    obtain ⟨V, hV, hxV, hlocal⟩ := exists_open_forall_mem_localRecessionCone hw
    exact ⟨V, hV, hxV, fun x hx v hv ↦ inner_nonpos_of_mem_regularNormalCone hv
      (localRecessionCone_subset_tangentCone (hlocal x hx))⟩
  · rintro ⟨V, hV, hxV, hnormal⟩
    exact mem_localRecessionCone_of_regularNormal_nonpos hxbar hC (hV.mem_nhds hxV) hnormal

/-- **Proposition 6.35(c)**: the equivalent local inequality for limiting normals. -/
theorem mem_localRecessionCone_iff_exists_open_normal_nonpos
    {C : Set E} {xbar w : E} (hxbar : xbar ∈ C)
    (hC : IsLocallyClosedAt C xbar) :
    w ∈ localRecessionCone C xbar ↔
      ∃ V : Set E, IsOpen V ∧ xbar ∈ V ∧
        ∀ x ∈ C ∩ V, ∀ v ∈ normalCone C x, ⟪v, w⟫_ℝ ≤ 0 := by
  constructor
  · intro hw
    obtain ⟨V, hV, hxV, hnormal⟩ :=
      (mem_localRecessionCone_iff_exists_open_regularNormal_nonpos hxbar hC).1 hw
    exact ⟨V, hV, hxV, forall_normal_nonpos_of_forall_regularNormal_nonpos hV hnormal⟩
  · rintro ⟨V, hV, hxV, hnormal⟩
    apply (mem_localRecessionCone_iff_exists_open_regularNormal_nonpos hxbar hC).2
    exact ⟨V, hV, hxV, fun x hx v hv ↦
      hnormal x hx v (regularNormalCone_subset_normalCone C x hv)⟩

/-- **Proposition 6.35(a)**: the direction lies in every nearby tangent cone. -/
theorem mem_localRecessionCone_iff_exists_open_tangent
    {C : Set E} {xbar w : E} (hxbar : xbar ∈ C)
    (hC : IsLocallyClosedAt C xbar) :
    w ∈ localRecessionCone C xbar ↔
      ∃ V : Set E, IsOpen V ∧ xbar ∈ V ∧
        ∀ x ∈ C ∩ V, w ∈ tangentCone C x := by
  constructor
  · intro hw
    obtain ⟨V, hV, hxV, hlocal⟩ := exists_open_forall_mem_localRecessionCone hw
    exact ⟨V, hV, hxV, fun x hx ↦ localRecessionCone_subset_tangentCone (hlocal x hx)⟩
  · rintro ⟨V, hV, hxV, htangent⟩
    apply (mem_localRecessionCone_iff_exists_open_regularNormal_nonpos hxbar hC).2
    exact ⟨V, hV, hxV, fun x hx v hv ↦
      inner_nonpos_of_mem_regularNormalCone hv (htangent x hx)⟩

/-- **Proposition 6.35(b)**: the equivalent condition using regular tangents. -/
theorem mem_localRecessionCone_iff_exists_open_regularTangent
    {C : Set E} {xbar w : E} (hxbar : xbar ∈ C)
    (hC : IsLocallyClosedAt C xbar) :
    w ∈ localRecessionCone C xbar ↔
      ∃ V : Set E, IsOpen V ∧ xbar ∈ V ∧
        ∀ x ∈ C ∩ V, w ∈ regularTangentCone C x := by
  constructor
  · intro hw
    obtain ⟨V, hV, hxV, hlocal⟩ := exists_open_forall_mem_localRecessionCone hw
    exact ⟨V, hV, hxV, fun x hx ↦ localRecessionCone_subset_regularTangentCone (hlocal x hx)⟩
  · rintro ⟨V, hV, hxV, htangent⟩
    apply (mem_localRecessionCone_iff_exists_open_tangent hxbar hC).2
    exact ⟨V, hV, hxV, fun x hx ↦
      regularTangentCone_subset_tangentCone hx.1 (htangent x hx)⟩

end RW
