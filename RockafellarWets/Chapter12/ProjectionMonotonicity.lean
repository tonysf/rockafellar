/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: monotonicity of projection mappings

This file formalizes Corollary 12.20.  The projection mapping `P_C` is the
Chapter 5 mapping `projMapping C`, and it is the proximal mapping `Pλδ_C` for
every `λ > 0` (`proximalMappingEReal_indicatorVA`).  Since `∂δ_C = N_C` (8.14),
Proposition 12.19 for `f = δ_C` gives the monotonicity of `P_C` and the
equivalence of (a), (d) and (e).  Nonexpansivity (c) follows from (a) by the
convex case of 12.19, (c) gives single-valuedness (b) since `P_C` is nonempty
(1.20), and (b) gives continuity of `P_C` from outer semicontinuity and local
boundedness (5.20, 5.23(a)), hence maximal monotonicity (d) by 12.7.

For (e) the book allows any `ρ ∈ ℝ`: monotonicity of `N_C + ρI` passes to
`N_C + ρ'I` for `ρ' = |ρ| + 1 > 0`, and `I + N_C = ρ'⁻¹(N_C + ρ'I)` since the
nonempty values of `N_C` are cones.
-/

import RockafellarWets.Chapter12.ProximalMappingMonotonicity
import RockafellarWets.Chapter12.ContinuousMaximality
import RockafellarWets.Chapter5.ProjectionMappings
import RockafellarWets.Chapter5.LocallyBoundedContinuity
import RockafellarWets.Chapter6.ProximalNormals
import RockafellarWets.Chapter10.DistanceSubsmoothness

open Set Filter Topology
open scoped InnerProductSpace Pointwise

namespace RW

section Projection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
/-- The proximal mappings of an indicator are the projection mapping:
`Pλδ_C = P_C` for every `λ > 0`. -/
theorem proximalMappingEReal_indicatorVA (C : Set E) {lam : ℝ} (hlam : 0 < lam) :
    proximalMappingEReal (indicatorVA C) lam = projMapping C := by
  funext a
  ext x
  rw [mem_proximalMappingEReal_iff, mem_projMapping]
  have hc : 0 < 1 / (2 * lam) := by positivity
  have hv : ∀ z ∈ C, proximalObjectiveEReal (indicatorVA C) lam a z =
      (((1 / (2 * lam)) * ‖z - a‖ ^ 2 : ℝ) : EReal) := by
    intro z hz
    rw [proximalObjectiveEReal, indicatorVA_apply_mem hz, zero_add]
  have hnv : ∀ z ∉ C, proximalObjectiveEReal (indicatorVA C) lam a z = ⊤ := by
    intro z hz
    rw [proximalObjectiveEReal, indicatorVA_apply_not_mem hz, EReal.top_add_coe]
  constructor
  · rintro ⟨heq, hlt⟩
    have hxC : x ∈ C := by
      by_contra hx
      rw [← heq, hnv x hx] at hlt
      exact lt_irrefl _ hlt
    refine ⟨hxC, fun w hw ↦ ?_⟩
    have h : proximalObjectiveEReal (indicatorVA C) lam a x ≤
        proximalObjectiveEReal (indicatorVA C) lam a w := by
      rw [heq]
      exact iInf_le _ w
    rw [hv x hxC, hv w hw, EReal.coe_le_coe_iff] at h
    have h' := le_of_mul_le_mul_left h hc
    nlinarith [norm_nonneg (x - a), norm_nonneg (w - a)]
  · rintro ⟨hxC, hmin⟩
    have hle : ∀ z, proximalObjectiveEReal (indicatorVA C) lam a x ≤
        proximalObjectiveEReal (indicatorVA C) lam a z := by
      intro z
      by_cases hz : z ∈ C
      · rw [hv x hxC, hv z hz, EReal.coe_le_coe_iff]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hmin z hz) 2) hc.le
      · rw [hnv z hz]
        exact le_top
    have heq : proximalObjectiveEReal (indicatorVA C) lam a x =
        moreauEnvelopeEReal (indicatorVA C) lam a :=
      le_antisymm (le_iInf hle) (iInf_le _ x)
    exact ⟨heq, by rw [← heq, hv x hxC]; exact EReal.coe_lt_top _⟩

/-- **Corollary 12.20**, first assertion: the projection mapping is monotone.
Neither closedness nor nonemptiness of `C` is needed. -/
theorem svMonotone_projMapping (C : Set E) : SvMonotone (projMapping C) := by
  rcases C.eq_empty_or_nonempty with rfl | hne
  · intro x₀ v₀ h₀
    exact absurd h₀.1 (notMem_empty _)
  · rw [← proximalMappingEReal_indicatorVA C one_pos]
    exact svMonotone_proximalMappingEReal (isProper_indicatorVA hne) one_pos

/-- If `δ_C + k` has a convex epigraph for a real-valued `k`, then `C` is convex:
`C` is the effective domain. -/
theorem convex_of_convex_epigraph_indicatorVA_add {C : Set E} {k : E → ℝ}
    (h : Convex ℝ (epigraph fun y ↦ indicatorVA C y + (k y : EReal))) : Convex ℝ C := by
  intro x hx y hy a b ha hb hab
  have hxe : (x, k x) ∈ epigraph fun y ↦ indicatorVA C y + (k y : EReal) := by
    rw [mem_epigraph_iff, indicatorVA_apply_mem hx, zero_add]
  have hye : (y, k y) ∈ epigraph fun y ↦ indicatorVA C y + (k y : EReal) := by
    rw [mem_epigraph_iff, indicatorVA_apply_mem hy, zero_add]
  have hz := h hxe hye ha hb hab
  have he : a • ((x, k x) : E × ℝ) + b • (y, k y) = (a • x + b • y, a * k x + b * k y) := by
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  rw [he, mem_epigraph_iff] at hz
  by_contra hn
  rw [indicatorVA_apply_not_mem hn, EReal.top_add_coe] at hz
  exact absurd hz (not_le.2 (EReal.coe_lt_top _))

variable [FiniteDimensional ℝ E]

/-- Monotonicity of `N_C + ρI` for some real `ρ` gives monotonicity of
`I + N_C`, written as `I + 1·∂δ_C`. -/
theorem svMonotone_id_add_normalCone_of_svMonotone_add_smul {C : Set E} {ρ : ℝ}
    (h : SvMonotone (svAdd (normalCone C) (fun x ↦ ({ρ • x} : Set E)))) :
    SvMonotone (svAdd (fun y ↦ ({y} : Set E))
      (fun y ↦ (1 : ℝ) • subdifferential (indicatorVA C) y)) := by
  rw [subdifferential_indicatorVA_eq_normalCone]
  set r : ℝ := |ρ| + 1 with hr
  have hrpos : 0 < r := by positivity
  have hrρ : ρ < r := by
    have := le_abs_self ρ
    linarith
  intro x₀ z₀ h₀ x₁ z₁ h₁
  obtain ⟨v₀, hv₀, rfl⟩ := mem_svAdd_id_smul_iff.1 h₀
  obtain ⟨v₁, hv₁, rfl⟩ := mem_svAdd_id_smul_iff.1 h₁
  have hm : ∀ {x v}, v ∈ normalCone C x →
      r • v + ρ • x ∈ svAdd (normalCone C) (fun x ↦ ({ρ • x} : Set E)) x := by
    intro x v hv
    exact mem_svAdd.2 ⟨r • v, (isCone_normalCone hv.1).2 hv hrpos, ρ • x, rfl, rfl⟩
  have hmono := h (hm hv₀) (hm hv₁)
  have e1 : r • v₁ + ρ • x₁ - (r • v₀ + ρ • x₀) = r • (v₁ - v₀) + ρ • (x₁ - x₀) := by
    simp only [smul_sub]
    abel
  have e2 : x₁ + (1 : ℝ) • v₁ - (x₀ + (1 : ℝ) • v₀) = (x₁ - x₀) + (v₁ - v₀) := by
    simp only [one_smul]
    abel
  rw [e1, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq] at hmono
  rw [e2, inner_add_left, real_inner_self_eq_norm_sq]
  have hsq := sq_nonneg ‖x₁ - x₀‖
  by_contra hneg
  push_neg at hneg
  nlinarith

/-- **Corollary 12.20 (projection mappings).** For a nonempty closed set `C`,
the projection mapping `P_C` is monotone, and the following are equivalent:
(a) `C` is convex; (b) `P_C` is single-valued; (c) `P_C` is nonexpansive;
(d) `P_C` is maximal monotone; (e) `N_C + ρI` is monotone for some `ρ ∈ ℝ`. -/
theorem projection_mappings {C : Set E} (hC : IsClosed C) (hne : C.Nonempty) :
    SvMonotone (projMapping C) ∧
      List.TFAE [Convex ℝ C, ∀ x, ∃ w, projMapping C x = {w},
        SvNonexpansive (projMapping C), SvMaximalMonotone (projMapping C),
        ∃ ρ : ℝ, SvMonotone (svAdd (normalCone C) (fun x ↦ ({ρ • x} : Set E)))] := by
  have hp := isProper_indicatorVA hne
  have hl := lowerSemicontinuous_indicatorVA hC
  have hP := proximalMappingEReal_indicatorVA C (one_pos : (0 : ℝ) < 1)
  refine ⟨svMonotone_projMapping C, ?_⟩
  tfae_have 1 → 3 := by
    intro hconv
    rw [← hP]
    exact svNonexpansive_proximalMappingEReal_of_convex hp
      (indicatorVA_proper_lsc_convex hC hconv hne).2.2 one_pos
  tfae_have 3 → 2 := by
    intro hn x
    obtain ⟨w, hw⟩ := projMapping_nonempty hC hne x
    exact ⟨w, hn.eq_singleton hw⟩
  tfae_have 2 → 4 := by
    intro hs
    choose p hpx using hs
    have hPp : projMapping C = svSingleton p := funext hpx
    have hcont : Continuous p := continuous_iff_continuousAt.2 fun x ↦ by
      have hosc := svOsc_projMapping hC x
      have hlb := svLocallyBounded_projMapping hne x
      rw [hPp] at hosc hlb
      exact continuousAt_of_svOscAt_svSingleton hosc hlb
    have hmono := svMonotone_projMapping C
    rw [hPp] at hmono ⊢
    exact svMaximalMonotone_singleton_of_continuous hcont hmono
  tfae_have 4 → 1 := by
    intro hmax
    rw [← hP] at hmax
    exact convex_of_convex_epigraph_indicatorVA_add
      ((svMaximalMonotone_proximalMappingEReal_iff_convex hp hl one_pos).1 hmax)
  tfae_have 1 → 5 := by
    intro hconv
    refine ⟨0, fun x₀ z₀ h₀ x₁ z₁ h₁ ↦ ?_⟩
    obtain ⟨v₀, hv₀, b₀, hb₀, rfl⟩ := mem_svAdd.1 h₀
    obtain ⟨v₁, hv₁, b₁, hb₁, rfl⟩ := mem_svAdd.1 h₁
    rw [mem_singleton_iff, zero_smul] at hb₀ hb₁
    subst hb₀ hb₁
    simp only [add_zero]
    have hmono := svMonotone_subdifferential_of_convex hp
      (indicatorVA_proper_lsc_convex hC hconv hne).2.2
    rw [subdifferential_indicatorVA_eq_normalCone] at hmono
    exact hmono hv₀ hv₁
  tfae_have 5 → 1 := by
    rintro ⟨ρ, hρ⟩
    exact convex_of_convex_epigraph_indicatorVA_add
      ((convex_add_half_norm_sq_iff_svMonotone hp hl one_pos).2
        (svMonotone_id_add_normalCone_of_svMonotone_add_smul hρ))
  tfae_finish

/-- For a convex set, `P_C = (I + N_C)⁻¹`, the resolvent of `N_C`. -/
theorem projMapping_eq_svResolvent_normalCone {C : Set E} (hconv : Convex ℝ C)
    (hne : C.Nonempty) : projMapping C = svResolvent (normalCone C) 1 := by
  rw [← proximalMappingEReal_indicatorVA C one_pos, ← subdifferential_indicatorVA_eq_normalCone]
  exact proximalMappingEReal_eq_svResolvent_of_convex (isProper_indicatorVA hne)
    (by rw [epigraph_indicatorVA]; exact hconv.prod (convex_Ici 0)) one_pos

/-- The parameterization of `gph N_C` following 12.20: for a nonempty closed
convex `C`, `Q_C = I - P_C` is the proximal mapping `P₁σ_C` of the support
function `σ_C = δ_C*`, and `(P_C(z), Q_C(z)) = (x, v)` exactly when `z = x + v`
and `v ∈ N_C(x)`. -/
theorem projMapping_normalCone_parameterization {C : Set E} (hC : IsClosed C)
    (hconv : Convex ℝ C) (hne : C.Nonempty) :
    (fun z ↦ ({z} : Set E) - projMapping C z) =
        proximalMappingEReal (fenchelConjugate (indicatorVA C)) 1 ∧
      ∀ z x v, (projMapping C z = {x} ∧
          proximalMappingEReal (fenchelConjugate (indicatorVA C)) 1 z = {v}) ↔
        z = x + v ∧ v ∈ normalCone C x := by
  obtain ⟨hp, hl, hc⟩ := indicatorVA_proper_lsc_convex hC hconv hne
  rw [← proximalMappingEReal_indicatorVA C one_pos, ← subdifferential_indicatorVA_eq_normalCone]
  exact ⟨sub_proximalMappingEReal_one_eq_fenchelConjugate hp hl hc,
    fun z x v ↦ proximalMappingEReal_one_eq_pair_iff hp hl hc⟩

end Projection

end RW
