/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Corollary 13.43 fails at the printed base point `ū = x̄ + v̄`

Corollary 13.43 states (b), (c) and `DP_C(ū) = [I + DN_C(x̄ ∣ v̄)]⁻¹` at `ū = x̄ + v̄` for `C`
prox-regular at `x̄` for `v̄`.  No curvature is needed to see that this fails: the closed set
`C = {0, 1} ⊂ ℝ` is prox-regular at `x̄ = 0` for `v̄ = 1` (near `0` it is the point `{0}`, whose
normal cone is all of `ℝ`), yet `P_C(x̄ + v̄) = P_C(1) = {1}`, so `x̄ ∉ P_C(ū)`, and the graphical
derivative of `P_C` at `(ū, x̄)` is empty while `[I + DN_C(x̄ ∣ v̄)]⁻¹(1)` contains `0`
(`normal_cone_projection_counterexample`).  In this repository `IsProtoDifferentiableAt S ū x̄`
does not require `x̄ ∈ S(ū)`, so the failure shows in `P_C(ū)` and in the derivative formula rather
than in (b).  `normal_cone_mappings_and_projections` therefore works at `ū = x̄ + λv̄` with `λ > 0`
small; the printed base point is covered by `normal_cone_mappings_and_projections_convex` (closed
convex `C`) and `normal_cone_mappings_and_projections_of_constants` (constants `ε, ρ` of
prox-regularity at `x̄` for `v̄` with `2‖v̄‖ < ε` and `ρ‖v̄‖ < ‖v̄‖ + ε`, `C` locally closed at
`x̄`).  The circle of radius `r < 1` with its inward unit normal fails in the same way, and there
the formula read at the actual nearest point has the wrong sign
(`NormalConeProjectionsCircle.normal_cone_projection_circle_counterexample`).

Neither strict inequality of that sufficient condition can be relaxed.  For the radius condition:
`C = {0} ∪ (2, 3) ⊂ ℝ` is locally closed at `x̄ = 0`, and with `v̄ = 1`, `ε = 2`, `ρ = 0` every
hypothesis holds except that `2‖v̄‖ = ε`; no point of `C` is nearest to any `u ∈ (1, 2)`, so
`P_C` is not single-valued around `ū = 1` and has no Aubin property there
(`normal_cone_projection_radius_counterexample`).  For the curvature condition: the closed set
`C = {-1, 1}`, the sphere of radius `1` in `ℝ`, with `x̄ = 1`, the inward normal `v̄ = -1`,
`ε = 3` and `ρ = 4` satisfies every hypothesis except that `ρ‖v̄‖ = ‖v̄‖ + ε`, and
`P_C(ū) = P_C(0) = {-1, 1}` (`normal_cone_projection_curvature_counterexample`).
-/

import RockafellarWets.Chapter13.NormalConeProjections

open Filter Set Topology Metric
open scoped InnerProductSpace

namespace RW
namespace NormalConeProjectionsCounterexample

/-- The two-point set `{0, 1} ⊂ ℝ`. -/
def twoPts : Set ℝ := {0, 1}

theorem isClosed_twoPts : IsClosed twoPts := by
  unfold twoPts
  exact (Set.toFinite _).isClosed

theorem twoPts_inter_ball : twoPts ∩ ball (0 : ℝ) (1 / 2) = {0} ∩ ball (0 : ℝ) (1 / 2) := by
  ext y
  simp only [twoPts, mem_inter_iff, mem_insert_iff, mem_singleton_iff, mem_ball, Real.dist_eq,
    sub_zero]
  constructor
  · rintro ⟨h | h, hy⟩
    · exact ⟨h, hy⟩
    · rw [h] at hy; norm_num at hy
  · rintro ⟨h, hy⟩
    exact ⟨Or.inl h, hy⟩

theorem normalCone_twoPts_zero : normalCone twoPts 0 = univ := by
  have hb : ball (0 : ℝ) (1 / 2) ∈ 𝓝 (0 : ℝ) := ball_mem_nhds _ (by norm_num)
  rw [← normalCone_inter_nhds (C := twoPts) hb, twoPts_inter_ball, normalCone_inter_nhds hb,
    normalCone_singleton]

theorem isProxRegularSetAt_twoPts : IsProxRegularSetAt twoPts 0 1 := by
  refine ⟨IsClosed.isLocallyClosedAt isClosed_twoPts 0,
    by rw [normalCone_twoPts_zero]; exact mem_univ _,
    1 / 2, by norm_num, 0, le_rfl, fun y v' hv' _ hy x' hx' ↦ ?_⟩
  have hyC : y ∈ twoPts := hv'.1
  have hy0 : y = 0 := by
    rcases hyC with h | h
    · exact h
    · rw [mem_singleton_iff] at h
      rw [h, sub_zero] at hy
      norm_num at hy
  have hx0 : x' = 0 := by
    obtain ⟨hxC, hxb⟩ := hx'
    rcases hxC with h | h
    · exact h
    · rw [mem_singleton_iff] at h
      rw [h, mem_closedBall, Real.dist_eq, sub_zero] at hxb
      norm_num at hxb
  rw [hy0, hx0]
  simp

theorem zero_notMem_projMapping_twoPts : (0 : ℝ) ∉ projMapping twoPts (0 + 1) := by
  rintro ⟨-, h⟩
  have := h 1 (by simp [twoPts])
  norm_num at this

theorem projMapping_twoPts_one : projMapping twoPts (0 + 1) = {(1 : ℝ)} := by
  ext y
  simp only [mem_projMapping, mem_singleton_iff]
  constructor
  · rintro ⟨hy, h⟩
    rcases hy with h0 | h1
    · exfalso
      rw [h0] at h
      have := h 1 (by simp [twoPts])
      norm_num at this
    · exact h1
  · rintro rfl
    refine ⟨by simp [twoPts], fun w' _ ↦ ?_⟩
    simp

theorem graphicalDerivative_ne_twoPts :
    graphicalDerivative (projMapping twoPts) (0 + 1) 0 ≠
      svResolvent (graphicalDerivative (normalCone twoPts) 0 1) 1 := by
  intro heq
  have h1 : (0 : ℝ) ∈ svResolvent (graphicalDerivative (normalCone twoPts) 0 1) 1 0 := by
    rw [mem_svResolvent]
    refine ⟨0, ?_, by simp⟩
    have hmem : ((0 : ℝ), (1 : ℝ)) ∈ svGraph (normalCone twoPts) := by
      change (1 : ℝ) ∈ normalCone twoPts 0
      rw [normalCone_twoPts_zero]; exact mem_univ _
    have h0 := (isCone_tangentCone hmem).1
    rw [← svGraph_graphicalDerivative] at h0
    exact h0
  rw [← heq] at h1
  have h2 : ((0 : ℝ), (0 : ℝ)) ∈ tangentCone (svGraph (projMapping twoPts)) (0 + 1, 0) := by
    rw [← svGraph_graphicalDerivative]; exact h1
  obtain ⟨xs, τs, hxs, hlim, -⟩ := h2
  have hcl : ((0 : ℝ) + 1, (0 : ℝ)) ∈ svGraph (projMapping twoPts) :=
    (isClosed_svGraph_projMapping isClosed_twoPts).mem_of_tendsto hlim (Eventually.of_forall hxs)
  exact zero_notMem_projMapping_twoPts hcl

/-- **Corollary 13.43**, the printed base point.  The closed set `C = {0, 1} ⊂ ℝ` is prox-regular at
`x̄ = 0` for the normal `v̄ = 1`, but `x̄` is not the projection of `ū = x̄ + v̄` (`P_C(ū) = {1}`),
and `DP_C(ū ∣ x̄) ≠ [I + DN_C(x̄ ∣ v̄)]⁻¹`: the latter contains `(1, 0)`, the former is empty
because `(ū, x̄)` is off the closed graph of `P_C`. -/
theorem normal_cone_projection_counterexample :
    IsClosed twoPts ∧ (1 : ℝ) ∈ normalCone twoPts 0 ∧ IsProxRegularSetAt twoPts 0 1 ∧
      projMapping twoPts (0 + 1) = {1} ∧ (0 : ℝ) ∉ projMapping twoPts (0 + 1) ∧
      graphicalDerivative (projMapping twoPts) (0 + 1) 0 ≠
        svResolvent (graphicalDerivative (normalCone twoPts) 0 1) 1 :=
  ⟨isClosed_twoPts, isProxRegularSetAt_twoPts.2.1, isProxRegularSetAt_twoPts,
    projMapping_twoPts_one, zero_notMem_projMapping_twoPts, graphicalDerivative_ne_twoPts⟩

/-! ### The radius condition `2‖v̄‖ < ε` -/

/-- The set `{0} ∪ (2, 3) ⊂ ℝ`, locally closed at `0` but not closed. -/
def pointInterval : Set ℝ := insert 0 (Ioo 2 3)

theorem pointInterval_inter_ball :
    pointInterval ∩ ball (0 : ℝ) 1 = {0} ∩ ball (0 : ℝ) 1 := by
  ext y
  simp only [pointInterval, mem_inter_iff, mem_insert_iff, mem_Ioo, mem_singleton_iff, mem_ball,
    Real.dist_eq, sub_zero]
  constructor
  · rintro ⟨h | h, hy⟩
    · exact ⟨h, hy⟩
    · exfalso
      rw [abs_lt] at hy
      linarith [h.1]
  · rintro ⟨h, hy⟩
    exact ⟨Or.inl h, hy⟩

theorem isLocallyClosedAt_pointInterval : IsLocallyClosedAt pointInterval 0 := by
  refine ⟨closedBall 0 (1 / 2), closedBall_mem_nhds _ (by norm_num), isClosed_closedBall, ?_⟩
  have heq : pointInterval ∩ closedBall (0 : ℝ) (1 / 2) = {0} := by
    ext y
    simp only [pointInterval, mem_inter_iff, mem_insert_iff, mem_Ioo, mem_closedBall,
      Real.dist_eq, sub_zero, mem_singleton_iff]
    constructor
    · rintro ⟨h | h, hy⟩
      · exact h
      · exfalso
        rw [abs_le] at hy
        linarith [h.1]
    · rintro rfl
      exact ⟨Or.inl rfl, by norm_num⟩
  rw [heq]
  exact isClosed_singleton

theorem normalCone_pointInterval_zero : normalCone pointInterval 0 = univ := by
  have hb : ball (0 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := ball_mem_nhds _ one_pos
  rw [← normalCone_inter_nhds (C := pointInterval) hb, pointInterval_inter_ball,
    normalCone_inter_nhds hb, normalCone_singleton]

/-- The inequality of prox-regularity at `x̄ = 0` for `v̄ = 1` with `ε = 2` and `ρ = 0`: within
distance `2` of `0`, the set is `{0}`. -/
theorem proxRegular_inequality_pointInterval :
    ∀ y v', v' ∈ normalCone pointInterval y → ‖v' - 1‖ < 2 → ‖y - 0‖ < 2 →
      ∀ x' ∈ pointInterval ∩ closedBall 0 2, ⟪v', x' - y⟫_ℝ ≤ 0 / 2 * ‖x' - y‖ ^ 2 := by
  intro y v' hv' _ hy x' hx'
  have hy0 : y = 0 := by
    rcases hv'.1 with h | h
    · exact h
    · exfalso
      rw [sub_zero, Real.norm_eq_abs, abs_lt] at hy
      linarith [h.1]
  have hx0 : x' = 0 := by
    obtain ⟨h | h, hb⟩ := hx'
    · exact h
    · exfalso
      rw [mem_closedBall, Real.dist_eq, sub_zero, abs_le] at hb
      linarith [h.1]
  rw [hy0, hx0]
  simp

/-- For `1 < u < 2` no point of `{0} ∪ (2, 3)` is nearest to `u`: the infimum `2 - u < u` of the
distances is approached in `(2, 3)` but not attained. -/
theorem projMapping_pointInterval_eq_empty {u : ℝ} (hu1 : 1 < u) (hu2 : u < 2) :
    projMapping pointInterval u = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  rintro y ⟨hy, hmin⟩
  rcases hy with h | h
  · -- `y = 0` is beaten by `2 + (u - 1)/2 ∈ (2, 3)`
    rw [h] at hmin
    have hw : 2 + (u - 1) / 2 ∈ pointInterval := Or.inr ⟨by linarith, by linarith⟩
    have := hmin _ hw
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_neg (by linarith),
      abs_of_pos (by linarith)] at this
    linarith
  · -- `y ∈ (2, 3)` is beaten by the midpoint of `2` and `y`
    have hw : (2 + y) / 2 ∈ pointInterval := Or.inr ⟨by linarith [h.1], by linarith [h.2]⟩
    have := hmin _ hw
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by linarith [h.1]),
      abs_of_pos (by linarith [h.1])] at this
    linarith [h.1]

theorem projMapping_pointInterval_one : projMapping pointInterval (0 + 1) = {0} := by
  ext y
  simp only [mem_projMapping, mem_singleton_iff, zero_add]
  constructor
  · rintro ⟨hy, h⟩
    rcases hy with h0 | h1
    · exact h0
    · exfalso
      have := h 0 (Or.inl rfl)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by linarith [h1.1])] at this
      norm_num at this
      linarith [h1.1]
  · rintro rfl
    refine ⟨Or.inl rfl, fun w hw ↦ ?_⟩
    rcases hw with h | h
    · rw [h]
    · have h1 : ‖(0 : ℝ) - 1‖ = 1 := by norm_num
      rw [h1, Real.norm_eq_abs, abs_of_pos (by linarith [h.1])]
      linarith [h.1]

theorem not_eventually_projMapping_pointInterval :
    ¬ ∀ᶠ u in 𝓝 ((0 : ℝ) + 1), ∃ p, projMapping pointInterval u = {p} := by
  intro h
  rw [zero_add, Metric.eventually_nhds_iff] at h
  obtain ⟨δ, hδ, hball⟩ := h
  set u : ℝ := 1 + min (δ / 2) (1 / 2) with hu
  have hm : 0 < min (δ / 2) (1 / 2) := lt_min (by linarith) (by norm_num)
  have hu1 : 1 < u := by linarith
  have hu2 : u < 2 := by linarith [min_le_right (δ / 2) (1 / 2)]
  have hdist : dist u 1 < δ := by
    rw [Real.dist_eq, hu, add_sub_cancel_left, abs_of_pos hm]
    linarith [min_le_left (δ / 2) (1 / 2)]
  obtain ⟨p, hp⟩ := hball hdist
  rw [projMapping_pointInterval_eq_empty hu1 hu2] at hp
  exact (Set.singleton_ne_empty p) hp.symm

theorem not_hasAubinPropertyAt_pointInterval :
    ¬ HasAubinPropertyAt (projMapping pointInterval) (0 + 1) 0 := by
  rintro ⟨-, -, -, k, V, hV, W, hW, hest⟩
  rw [zero_add] at hV
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hV
  set u : ℝ := 1 + min (δ / 2) (1 / 2) with hu
  have hm : 0 < min (δ / 2) (1 / 2) := lt_min (by linarith) (by norm_num)
  have hu1 : 1 < u := by linarith
  have hu2 : u < 2 := by linarith [min_le_right (δ / 2) (1 / 2)]
  have huV : u ∈ V := by
    apply hball
    rw [mem_ball, Real.dist_eq, hu, add_sub_cancel_left, abs_of_pos hm]
    linarith [min_le_left (δ / 2) (1 / 2)]
  have h0 : (0 : ℝ) ∈ projMapping pointInterval 1 := by
    rw [← zero_add (1 : ℝ), projMapping_pointInterval_one]; rfl
  obtain ⟨z, hz, -⟩ := hest 1 ⟨mem_univ _, mem_of_mem_nhds hV⟩ u ⟨mem_univ _, huV⟩ 0
    ⟨h0, mem_of_mem_nhds hW⟩
  rw [projMapping_pointInterval_eq_empty hu1 hu2] at hz
  exact hz

/-- **Corollary 13.43 at `ū = x̄ + v̄`: the radius condition `2‖v̄‖ < ε` is needed.**  The set
`C = {0} ∪ (2, 3) ⊂ ℝ` is locally closed at `x̄ = 0` (not closed), `v̄ = 1 ∈ N_C(x̄)`, and the
inequality of prox-regularity holds with `ε = 2` and `ρ = 0`, so `C` is prox-regular at `x̄` for
`v̄` and every hypothesis of `normal_cone_mappings_and_projections_of_constants` holds except
`2‖v̄‖ < ε`, which holds with equality.  Then `P_C(ū) = {x̄}` for `ū = x̄ + v̄`, but `P_C` has no
value at any `u ∈ (1, 2)`, so it is not single-valued around `ū` and has no Aubin property at `ū`
for `x̄`. -/
theorem normal_cone_projection_radius_counterexample :
    IsLocallyClosedAt pointInterval 0 ∧ (1 : ℝ) ∈ normalCone pointInterval 0 ∧
      IsProxRegularSetAt pointInterval 0 1 ∧ 2 * ‖(1 : ℝ)‖ = 2 ∧ 0 * ‖(1 : ℝ)‖ < ‖(1 : ℝ)‖ + 2 ∧
      (∀ y v', v' ∈ normalCone pointInterval y → ‖v' - 1‖ < 2 → ‖y - 0‖ < 2 →
        ∀ x' ∈ pointInterval ∩ closedBall 0 2, ⟪v', x' - y⟫_ℝ ≤ 0 / 2 * ‖x' - y‖ ^ 2) ∧
      projMapping pointInterval (0 + 1) = {0} ∧
      ¬ (∀ᶠ u in 𝓝 ((0 : ℝ) + 1), ∃ p, projMapping pointInterval u = {p}) ∧
      ¬ HasAubinPropertyAt (projMapping pointInterval) (0 + 1) 0 := by
  have hv : (1 : ℝ) ∈ normalCone pointInterval 0 := by
    rw [normalCone_pointInterval_zero]; exact mem_univ _
  exact ⟨isLocallyClosedAt_pointInterval, hv,
    ⟨isLocallyClosedAt_pointInterval, hv, 2, two_pos, 0, le_rfl,
      proxRegular_inequality_pointInterval⟩,
    by norm_num, by norm_num, proxRegular_inequality_pointInterval, projMapping_pointInterval_one,
    not_eventually_projMapping_pointInterval, not_hasAubinPropertyAt_pointInterval⟩

/-! ### The curvature condition `ρ‖v̄‖ < ‖v̄‖ + ε` -/

/-- The set `{-1, 1} ⊂ ℝ`, the sphere of radius `1`. -/
def signPts : Set ℝ := {-1, 1}

theorem isClosed_signPts : IsClosed signPts := by
  unfold signPts
  exact (Set.toFinite _).isClosed

theorem normalCone_signPts {y : ℝ} (hy : y ∈ signPts) : normalCone signPts y = univ := by
  have hb : ball y 1 ∈ 𝓝 y := ball_mem_nhds _ one_pos
  have heq : signPts ∩ ball y 1 = {y} ∩ ball y 1 := by
    ext z
    simp only [mem_inter_iff, mem_singleton_iff, mem_ball, Real.dist_eq]
    constructor
    · rintro ⟨hz, hzy⟩
      refine ⟨?_, hzy⟩
      rcases hy with h | h <;> rcases hz with h' | h'
      · rw [h, h']
      · exfalso; rw [mem_singleton_iff] at h'; rw [h, h', abs_lt] at hzy; linarith [hzy.2]
      · exfalso; rw [mem_singleton_iff] at h; rw [h, h', abs_lt] at hzy; linarith [hzy.1]
      · rw [mem_singleton_iff] at h h'; rw [h, h']
    · rintro ⟨rfl, hzy⟩
      exact ⟨hy, hzy⟩
  rw [← normalCone_inter_nhds (C := signPts) hb, heq, normalCone_inter_nhds hb,
    normalCone_singleton]

/-- The inequality of prox-regularity at `x̄ = 1` for `v̄ = -1` with `ε = 3` and `ρ = 4`: the
normals within `3` of `-1` lie in `(-4, 2)`. -/
theorem proxRegular_inequality_signPts :
    ∀ y v', v' ∈ normalCone signPts y → ‖v' - -1‖ < 3 → ‖y - 1‖ < 3 →
      ∀ x' ∈ signPts ∩ closedBall 1 3, ⟪v', x' - y⟫_ℝ ≤ 4 / 2 * ‖x' - y‖ ^ 2 := by
  intro y v' hv' hvv _ x' hx'
  have hyC : y ∈ signPts := hv'.1
  rw [Real.norm_eq_abs, sub_neg_eq_add, abs_lt] at hvv
  rw [RCLike.inner_apply, conj_trivial, Real.norm_eq_abs, sq_abs]
  rcases hyC with h | h <;> rcases hx'.1 with h' | h'
  · rw [h, h']; norm_num
  · rw [mem_singleton_iff] at h'; rw [h, h']; nlinarith
  · rw [mem_singleton_iff] at h; rw [h, h']; nlinarith
  · rw [mem_singleton_iff] at h h'; rw [h, h']; norm_num

theorem projMapping_signPts_zero : projMapping signPts (1 + -1) = {-1, 1} := by
  ext y
  simp only [mem_projMapping, add_neg_cancel, sub_zero]
  constructor
  · rintro ⟨hy, -⟩
    exact hy
  · intro hy
    refine ⟨hy, fun w hw ↦ ?_⟩
    rcases hy with h | h <;> rcases hw with h' | h'
    all_goals simp_all

/-- **Corollary 13.43 at `ū = x̄ + v̄`: the curvature condition `ρ‖v̄‖ < ‖v̄‖ + ε` is needed.**  The
closed set `C = {-1, 1} ⊂ ℝ`, the sphere of radius `1`, with `x̄ = 1` and the inward normal
`v̄ = -1`, satisfies the inequality of prox-regularity with `ε = 3` and `ρ = 4`, so every hypothesis
of `normal_cone_mappings_and_projections_of_constants` holds except `ρ‖v̄‖ < ‖v̄‖ + ε`, which holds
with equality.  Then `ū = x̄ + v̄ = 0` has the two nearest points `±1`, so `P_C(ū) ≠ {x̄}`. -/
theorem normal_cone_projection_curvature_counterexample :
    IsClosed signPts ∧ (-1 : ℝ) ∈ normalCone signPts 1 ∧ IsProxRegularSetAt signPts 1 (-1) ∧
      2 * ‖(-1 : ℝ)‖ < 3 ∧ 4 * ‖(-1 : ℝ)‖ = ‖(-1 : ℝ)‖ + 3 ∧
      (∀ y v', v' ∈ normalCone signPts y → ‖v' - -1‖ < 3 → ‖y - 1‖ < 3 →
        ∀ x' ∈ signPts ∩ closedBall 1 3, ⟪v', x' - y⟫_ℝ ≤ 4 / 2 * ‖x' - y‖ ^ 2) ∧
      projMapping signPts (1 + -1) = {-1, 1} ∧ projMapping signPts (1 + -1) ≠ {1} := by
  have hv : (-1 : ℝ) ∈ normalCone signPts 1 := by
    rw [normalCone_signPts (by simp [signPts])]; exact mem_univ _
  refine ⟨isClosed_signPts, hv,
    ⟨IsClosed.isLocallyClosedAt isClosed_signPts 1, hv, 3, by norm_num, 4, by norm_num,
      proxRegular_inequality_signPts⟩,
    by norm_num, by norm_num, proxRegular_inequality_signPts, projMapping_signPts_zero, ?_⟩
  rw [projMapping_signPts_zero]
  intro h
  have : (-1 : ℝ) ∈ ({1} : Set ℝ) := h ▸ (by simp)
  norm_num at this

end NormalConeProjectionsCounterexample
end RW
