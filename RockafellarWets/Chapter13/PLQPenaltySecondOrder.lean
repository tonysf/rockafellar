/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Second subderivatives of piecewise linear-quadratic penalties

Example 13.23.  `θ_{Y,B} = φ*` with `φ = δ_Y + j_B` convex and piecewise linear-quadratic
(Example 11.18).  For `ȳ ∈ ∂θ(ū)` one has `ū ∈ ∂φ(ȳ)`, `φ` is fully amenable at `ȳ`, and along
rays `φ(ȳ + τw) = φ(ȳ) + τ⟪Bȳ, w⟫ + ½τ²⟪w, Bw⟫` for `w ∈ T_Y(ȳ)`, so by Proposition 13.9
`d²φ(ȳ | ū) = ⟪·, B·⟫ + δ_{Y'}` with `Y' = {w ∈ T_Y(ȳ) | w ⊥ ū - Bȳ}`.  Corollary 13.22 then gives
`d²θ(ū | ȳ)(z) = sup_{w ∈ Y'} {2⟪w, z⟫ - ⟪w, Bw⟫} = 2θ_{Y',B}(z)`.
-/

import RockafellarWets.Chapter13.ConjugateSecondOrder
import RockafellarWets.Chapter11.PiecewiseLinearQuadraticPenalties
import RockafellarWets.Chapter10.PolyhedralPieceDerivatives

open Filter Set Topology Metric
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Y : Set E} {B : E →L[ℝ] E}

/-- The polyhedral cone `Y'(ū, ȳ) = {w ∈ T_Y(ȳ) | w ⊥ ū - Bȳ}` of Example 13.23. -/
def penaltyCriticalCone (Y : Set E) (B : E →L[ℝ] E) (u y : E) : Set E :=
  {w | w ∈ tangentCone Y y ∧ ⟪w, u - B y⟫_ℝ = 0}

omit [FiniteDimensional ℝ E] in
/-- The expansion of `j_B` along a ray. -/
theorem half_inner_map_add_smul (hB : ∀ x y, ⟪B x, y⟫_ℝ = ⟪x, B y⟫_ℝ) (y w : E) (τ : ℝ) :
    1 / 2 * ⟪y + τ • w, B (y + τ • w)⟫_ℝ =
      1 / 2 * ⟪y, B y⟫_ℝ + τ * ⟪B y, w⟫_ℝ + τ ^ 2 / 2 * ⟪w, B w⟫_ℝ := by
  simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right]
  have e1 : ⟪y, B w⟫_ℝ = ⟪B y, w⟫_ℝ := (hB y w).symm
  have e2 : ⟪w, B y⟫_ℝ = ⟪B y, w⟫_ℝ := real_inner_comm _ _
  rw [e1, e2]
  ring

open Classical in
theorem subderivative_plqPenaltyPrimal (hY : IsPolyhedral Y)
    (hB : ∀ x y, ⟪B x, y⟫_ℝ = ⟪x, B y⟫_ℝ) {y : E} (hy : y ∈ Y) (w : E) :
    subderivative (plqPenaltyPrimal Y B) y w =
      if w ∈ tangentCone Y y then ((⟪B y, w⟫_ℝ : ℝ) : EReal) else ⊤ := by
  have hplq := isPiecewiseLinearQuadratic_plqPenaltyPrimal hY hB
  have hyd : y ∈ effectiveDomain (plqPenaltyPrimal Y B) := by
    rw [mem_effectiveDomain_iff, plqPenaltyPrimal_eq_ite, if_pos hy]; exact EReal.coe_lt_top _
  have hc : plqPenaltyPrimal Y B y = ((1 / 2 * ⟪y, B y⟫_ℝ : ℝ) : EReal) := by
    rw [plqPenaltyPrimal_eq_ite, if_pos hy]
  refine tendsto_nhds_unique (hplq.hasOneSidedDirDeriv hyd w).2.2 ?_
  split_ifs with hw
  · have hr : Tendsto (fun τ : ℝ ↦ ⟪B y, w⟫_ℝ + τ / 2 * ⟪w, B w⟫_ℝ) (𝓝[>] (0 : ℝ))
        (𝓝 ⟪B y, w⟫_ℝ) := by
      have : Tendsto (fun τ : ℝ ↦ ⟪B y, w⟫_ℝ + τ / 2 * ⟪w, B w⟫_ℝ) (𝓝 (0 : ℝ))
          (𝓝 (⟪B y, w⟫_ℝ + 0 / 2 * ⟪w, B w⟫_ℝ)) :=
        (continuous_const.add ((continuous_id.div_const 2).mul continuous_const)).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    refine ((continuous_coe_real_ereal.tendsto _).comp hr).congr' ?_
    filter_upwards [hY.eventually_ray_mem_iff hy w, self_mem_nhdsWithin] with τ hτ hτpos
    have hτ' : (0 : ℝ) < τ := hτpos
    rw [Function.comp_apply, differenceQuotient_eq_coe hc (by
      rw [plqPenaltyPrimal_eq_ite, if_pos (hτ.2 hw), half_inner_map_add_smul hB])]
    congr 1
    field_simp
    ring
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [hY.eventually_ray_mem_iff hy w, self_mem_nhdsWithin] with τ hτ hτpos
    have hτ' : (0 : ℝ) < τ := hτpos
    rw [differenceQuotient_eq_top hτ' hc (by
      rw [plqPenaltyPrimal_eq_ite, if_neg (fun h ↦ hw (hτ.1 h))])]

open Classical in
theorem secondSubderivativeAt_plqPenaltyPrimal (hY : IsPolyhedral Y)
    (hB : ∀ x y, ⟪B x, y⟫_ℝ = ⟪x, B y⟫_ℝ) (hBpos : ∀ y, 0 ≤ ⟪y, B y⟫_ℝ) {y : E} (hy : y ∈ Y)
    (w : E) : secondSubderivativeAt (plqPenaltyPrimal Y B) y w =
      if w ∈ tangentCone Y y then ((⟪w, B w⟫_ℝ : ℝ) : EReal) else ⊤ := by
  have hplq := isPiecewiseLinearQuadratic_plqPenaltyPrimal hY hB
  have hconv := convex_epigraph_plqPenaltyPrimal hY.convex hB hBpos
  have hyd : y ∈ effectiveDomain (plqPenaltyPrimal Y B) := by
    rw [mem_effectiveDomain_iff, plqPenaltyPrimal_eq_ite, if_pos hy]; exact EReal.coe_lt_top _
  have hc : plqPenaltyPrimal Y B y = ((1 / 2 * ⟪y, B y⟫_ℝ : ℝ) : EReal) := by
    rw [plqPenaltyPrimal_eq_ite, if_pos hy]
  have hlim := ((piecewise_linear_quadratic_second_order hplq hconv hyd).1.2.2 w).2
  refine tendsto_nhds_unique hlim ?_
  have hd := subderivative_plqPenaltyPrimal hY hB hy w
  split_ifs with hw
  · rw [if_pos hw] at hd
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hY.eventually_ray_mem_iff hy w, self_mem_nhdsWithin] with τ hτ hτpos
    have hτ' : (0 : ℝ) < τ := hτpos
    rw [secondDifferenceQuotientAt_eq_of_subderivative_eq hd, secondDifferenceQuotient_of_coe hc
      (by rw [plqPenaltyPrimal_eq_ite, if_pos (hτ.2 hw), half_inner_map_add_smul hB])]
    congr 1
    field_simp
    ring
  · rw [if_neg hw] at hd
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hY.eventually_ray_mem_iff hy w, self_mem_nhdsWithin] with τ hτ hτpos
    have hτ' : (0 : ℝ) < τ := hτpos
    rw [secondDifferenceQuotientAt, hd, plqPenaltyPrimal_eq_ite, if_neg (fun h ↦ hw (hτ.1 h)), hc,
      EReal.top_sub_coe, infAddition, if_pos (Or.inl rfl)]
    exact (EReal.coe_mul_top_of_pos (by positivity)).symm

open Classical in
/-- `d²φ(ȳ | ū) = ⟪·, B·⟫ + δ_{Y'(ū,ȳ)}` for `ū ∈ ∂φ(ȳ)`, `φ = δ_Y + j_B`. -/
theorem secondSubderivative_plqPenaltyPrimal (hY : IsPolyhedral Y)
    (hB : ∀ x y, ⟪B x, y⟫_ℝ = ⟪x, B y⟫_ℝ) (hBpos : ∀ y, 0 ≤ ⟪y, B y⟫_ℝ) {u y : E}
    (huy : u ∈ subdifferential (plqPenaltyPrimal Y B) y) (w : E) :
    secondSubderivative (plqPenaltyPrimal Y B) y u w =
      if w ∈ penaltyCriticalCone Y B u y then ((⟪w, B w⟫_ℝ : ℝ) : EReal) else ⊤ := by
  have hplq := isPiecewiseLinearQuadratic_plqPenaltyPrimal hY hB
  have hconv := convex_epigraph_plqPenaltyPrimal hY.convex hB hBpos
  have hy : y ∈ Y := by
    by_contra h
    obtain ⟨⟨c, hc⟩, -⟩ := huy
    rw [plqPenaltyPrimal_eq_ite, if_neg h] at hc
    exact EReal.coe_ne_top c hc.symm
  have hyd : y ∈ effectiveDomain (plqPenaltyPrimal Y B) := by
    rw [mem_effectiveDomain_iff, plqPenaltyPrimal_eq_ite, if_pos hy]; exact EReal.coe_lt_top _
  have h := (((piecewise_linear_quadratic_second_order hplq hconv hyd).2.1 u huy).2.2.2.2.2.1 w).1
  rw [h, secondSubderivativeAt_plqPenaltyPrimal hY hB hBpos hy]
  have hK : w ∈ {w | subderivative (plqPenaltyPrimal Y B) y w = ((⟪u, w⟫_ℝ : ℝ) : EReal)} ↔
      w ∈ penaltyCriticalCone Y B u y := by
    simp only [mem_setOf_eq, penaltyCriticalCone, subderivative_plqPenaltyPrimal hY hB hy]
    split_ifs with hw
    · rw [EReal.coe_eq_coe_iff, inner_sub_right, real_inner_comm w u, real_inner_comm w (B y)]
      constructor
      · intro h; exact ⟨hw, by linarith⟩
      · rintro ⟨-, h⟩; linarith
    · simp [hw]
  by_cases hw : w ∈ penaltyCriticalCone Y B u y
  · rw [if_pos hw, if_pos hw.1, indicatorVA_apply_mem (hK.2 hw), add_zero]
  · rw [if_neg hw, indicatorVA_apply_not_mem (fun h ↦ hw (hK.1 h))]
    split_ifs
    · exact EReal.coe_add_top _
    · exact EReal.top_add_top

/-- **Example 13.23** (piecewise linear-quadratic penalties).  For nonempty polyhedral `Y` and
symmetric positive-semidefinite `B`, `θ_{Y,B}` is properly twice epi-differentiable at every
`ū ∈ dom θ_{Y,B}` for every `ȳ ∈ ∂θ_{Y,B}(ū)`, with
`d²θ_{Y,B}(ū | ȳ)(z) = sup_{w ∈ Y'(ū,ȳ)} {2⟪w, z⟫ - ⟪w, Bw⟫}` for the polyhedral cone
`Y'(ū, ȳ) = {w ∈ T_Y(ȳ) | w ⊥ ū - Bȳ}`; consequently `d²θ_{Y,B}(ū | ȳ) = 2θ_{Y'(ū,ȳ),B}` and
`dom d²θ_{Y,B}(ū | ȳ) = {w ∈ T_Y(ȳ) | Bw = 0, w ⊥ ū}*`, and for `B = 0` it is the indicator of
`Y'(ū, ȳ)*`. -/
theorem piecewise_linear_quadratic_penalties (hY : IsPolyhedral Y) (hne : Y.Nonempty)
    (hB : ∀ x y, ⟪B x, y⟫_ℝ = ⟪x, B y⟫_ℝ) (hBpos : ∀ y, 0 ≤ ⟪y, B y⟫_ℝ) {u y : E}
    (hyu : y ∈ subdifferential (plqPenalty Y B) u) :
    IsPolyhedral (penaltyCriticalCone Y B u y) ∧ IsCone (penaltyCriticalCone Y B u y) ∧
    ProperlyTwiceEpiDifferentiableAt (plqPenalty Y B) u y ∧
    (∀ z, secondSubderivative (plqPenalty Y B) u y z =
      ⨆ w ∈ penaltyCriticalCone Y B u y, ((2 * ⟪w, z⟫_ℝ - ⟪w, B w⟫_ℝ : ℝ) : EReal)) ∧
    (∀ z, secondSubderivative (plqPenalty Y B) u y z =
      ((2 : ℝ) : EReal) * plqPenalty (penaltyCriticalCone Y B u y) B z) ∧
    effectiveDomain (secondSubderivative (plqPenalty Y B) u y) =
      polarCone {w | w ∈ tangentCone Y y ∧ B w = 0 ∧ ⟪w, u⟫_ℝ = 0} ∧
    (B = 0 → secondSubderivative (plqPenalty Y B) u y =
      indicatorVA (polarCone (penaltyCriticalCone Y B u y))) := by
  have hplq := isPiecewiseLinearQuadratic_plqPenaltyPrimal hY hB
  have hp := isProper_plqPenaltyPrimal (B := B) hne
  have hconv := convex_epigraph_plqPenaltyPrimal hY.convex hB hBpos
  have hl := hplq.lowerSemicontinuous
  rw [plqPenalty_eq_fenchelConjugate] at hyu ⊢
  have huy : u ∈ subdifferential (plqPenaltyPrimal Y B) y :=
    (mem_subdifferential_fenchelConjugate_iff hp hl hconv y u).1 hyu
  have hy : y ∈ Y := by
    by_contra h
    obtain ⟨⟨c, hc⟩, -⟩ := huy
    rw [plqPenaltyPrimal_eq_ite, if_neg h] at hc
    exact EReal.coe_ne_top c hc.symm
  have hyd : y ∈ effectiveDomain (plqPenaltyPrimal Y B) := by
    rw [mem_effectiveDomain_iff, plqPenaltyPrimal_eq_ite, if_pos hy]; exact EReal.coe_lt_top _
  have hfa := fullyAmenableAt_of_convex_plq hplq hconv hyd
  obtain ⟨-, h22⟩ := conjugates_of_fully_amenable_functions hp hl hconv
  obtain ⟨hpte, hform⟩ := h22 u y hyu hfa
  -- the critical cone
  have hTpoly : IsPolyhedral (tangentCone Y y) := hY.isPolyhedral_tangentCone hy
  have hKpoly : IsPolyhedral (penaltyCriticalCone Y B u y) := by
    have h1 : IsPolyhedral {w : E | ⟪w, u - B y⟫_ℝ = 0} := by
      have ha := isPolyhedral_linearHalfspace (innerSL ℝ (u - B y)) 0
      have hb := isPolyhedral_linearHalfspace (innerSL ℝ (-(u - B y))) 0
      have : {w : E | ⟪w, u - B y⟫_ℝ = 0} = {x | innerSL ℝ (u - B y) x ≤ 0} ∩
          {x | innerSL ℝ (-(u - B y)) x ≤ 0} := by
        ext w
        simp only [mem_setOf_eq, mem_inter_iff, innerSL_apply_apply, inner_neg_left,
          real_inner_comm w]
        constructor
        · intro h; rw [h]; simp
        · rintro ⟨h1, h2⟩; linarith
      rw [this]; exact ha.inter hb
    exact hTpoly.inter h1
  have hKcone : IsCone (penaltyCriticalCone Y B u y) := by
    refine ⟨⟨(isCone_tangentCone hy).1, by simp⟩, fun w hw c hc ↦
      ⟨(isCone_tangentCone hy).2 hw.1 hc, by rw [real_inner_smul_left, hw.2, mul_zero]⟩⟩
  -- the formula
  have hsup : ∀ z, secondSubderivative (fenchelConjugate (plqPenaltyPrimal Y B)) u y z =
      ⨆ w ∈ penaltyCriticalCone Y B u y, ((2 * ⟪w, z⟫_ℝ - ⟪w, B w⟫_ℝ : ℝ) : EReal) := by
    intro z
    rw [hform z]
    apply le_antisymm
    · refine iSup_le fun w ↦ ?_
      rw [secondSubderivative_plqPenaltyPrimal hY hB hBpos huy]
      split_ifs with hw
      · refine le_trans (le_of_eq ?_) (le_iSup₂ (f := fun w _ ↦
          ((2 * ⟪w, z⟫_ℝ - ⟪w, B w⟫_ℝ : ℝ) : EReal)) w hw)
        rw [← EReal.coe_sub, real_inner_comm w z]
      · rw [EReal.sub_top]; exact bot_le
    · refine iSup₂_le fun w hw ↦ le_trans (le_of_eq ?_) (le_iSup _ w)
      rw [secondSubderivative_plqPenaltyPrimal hY hB hBpos huy, if_pos hw, ← EReal.coe_sub,
        real_inner_comm w z]
  have htwice : ∀ z, secondSubderivative (fenchelConjugate (plqPenaltyPrimal Y B)) u y z =
      ((2 : ℝ) : EReal) * plqPenalty (penaltyCriticalCone Y B u y) B z := by
    intro z
    rw [hsup z, plqPenalty]
    simp only [ereal_coe_mul_iSup _ (show (0 : ℝ) < 2 by norm_num)]
    congr 1
    funext w
    congr 1
    funext _
    rw [← EReal.coe_mul]
    congr 1
    ring
  have hKne : (penaltyCriticalCone Y B u y).Nonempty := ⟨0, hKcone.1⟩
  have hdomK := effectiveDomain_plqPenalty hKpoly hKne hB hBpos
  refine ⟨hKpoly, hKcone, hpte, hsup, htwice, ?_, fun hB0 ↦ ?_⟩
  · have hdom : effectiveDomain (secondSubderivative (fenchelConjugate (plqPenaltyPrimal Y B)) u y)
        = effectiveDomain (plqPenalty (penaltyCriticalCone Y B u y) B) := by
      ext z
      rw [mem_effectiveDomain_iff, mem_effectiveDomain_iff, htwice z]
      rcases ereal_trichotomy (plqPenalty (penaltyCriticalCone Y B u y) B z) with h | h | ⟨r, h⟩
      · rw [h, EReal.coe_mul_bot_of_pos (by norm_num)]
      · rw [h, EReal.coe_mul_top_of_pos (by norm_num)]
      · rw [h, ← EReal.coe_mul]
        exact ⟨fun _ ↦ EReal.coe_lt_top _, fun _ ↦ EReal.coe_lt_top _⟩
    rw [hdom, hdomK, horizonCone_eq_self_of_isClosed_isCone hKpoly.isClosed hKcone]
    congr 1
    ext w
    simp only [penaltyCriticalCone, mem_inter_iff, mem_setOf_eq]
    constructor
    · rintro ⟨⟨hw, h⟩, hBw⟩
      refine ⟨hw, hBw, ?_⟩
      rw [inner_sub_right, ← hB w y, hBw, inner_zero_left, sub_zero] at h
      exact h
    · rintro ⟨hw, hBw, h⟩
      refine ⟨⟨hw, ?_⟩, hBw⟩
      rw [inner_sub_right, ← hB w y, hBw, inner_zero_left, sub_zero]
      exact h
  · subst hB0
    funext z
    rw [htwice z, plqPenalty_zero, supportFunction_cone hKcone]
    by_cases hz : z ∈ polarCone (penaltyCriticalCone Y 0 u y)
    · rw [indicatorVA_apply_mem hz]; simp
    · rw [indicatorVA_apply_not_mem hz]
      exact EReal.coe_mul_top_of_pos (by norm_num)

end RW
