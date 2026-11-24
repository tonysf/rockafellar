/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: monotonicity of proximal mappings

This file formalizes Proposition 12.19.  The proximal mapping `Pλf` is the
Chapter 1 mapping `proximalMappingEReal f λ`, and `(I + λ∂f)⁻¹` is the
resolvent `svResolvent (subdifferential f) λ` of the foundations module.

For a proper `f` and `λ > 0` write `g = f + (2λ)⁻¹‖·‖²` (the book's
`λ⁻¹(j + λf)` with `j = ½‖·‖²`; scaling by `λ⁻¹ > 0` changes neither
convexity nor subgradient monotonicity).  The basic observation of the proof
is that `x ∈ Pλf(w)` exactly when `λ⁻¹w` is the slope of an affine minorant of
`g` touching `g` at `x`; see `mem_proximalMappingEReal_iff_mem_globalSupportSlopes`.

* (b) ⇒ (a): for convex `g` these slopes are the subgradients of `g`, a maximal
  monotone mapping by 12.17.
* (a) ⇒ (b): the touching slopes of `g` lie in `∂g**`.  Maximality forces
  equality, so `g = g**` on `dom ∂g**`.  Since `dom ∂g**` is attentively dense
  in `dom g**` (8.10) and `g` is lsc with `g ≥ g**`, we get `g = g**`.  The book
  reaches the same conclusion through `cl(con g)` and relative interiors.
* (b) ⇔ (c): `∂g = λ⁻¹(I + λ∂f)` by 8.8(c), and 12.17 applies to `g`.

The Lipschitz constant `λ/(λ - μ)` for `Pμf` follows directly from the
monotonicity of `I + λ∂f` and 10.2.  Nonemptiness of `Pμf` comes from an affine
minorant of the convex function `g`, which makes `f` prox-bounded with
threshold at least `λ`.
-/

import RockafellarWets.Chapter12.ConvexSubgradientMappings
import RockafellarWets.Chapter12.Resolvents
import RockafellarWets.Chapter12.MintyParameterization
import RockafellarWets.Chapter11.SubgradientConjugacy
import RockafellarWets.Chapter10.SubsmoothMoreauEnvelopes
import RockafellarWets.Chapter10.PLQCalculus
import RockafellarWets.Chapter3.CoercivityCompletion
import RockafellarWets.Chapter8.SubgradientExistence
import RockafellarWets.Chapter9.SmoothnessCriteria
import Mathlib.Analysis.Convex.Mul

open Set Filter Topology
open scoped InnerProductSpace Pointwise

namespace RW

section Identities

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The four-point identity behind the monotonicity of proximal mappings. -/
theorem norm_sub_sq_cross_identity (x₀ x₁ w₀ w₁ : E) :
    ‖x₀ - w₀‖ ^ 2 + ‖x₁ - w₁‖ ^ 2 - ‖x₁ - w₀‖ ^ 2 - ‖x₀ - w₁‖ ^ 2 =
      -2 * ⟪x₁ - x₀, w₁ - w₀⟫_ℝ := by
  simp only [norm_sub_sq_real, inner_sub_left, inner_sub_right]
  ring

/-- **Proposition 12.19**, first assertion: for a proper function and `λ > 0`
the proximal mapping `Pλf` is monotone.  Lower semicontinuity is not needed:
adding the two proximal inequalities gives the four-point identity. -/
theorem svMonotone_proximalMappingEReal {f : E → EReal} (hp : IsProper f) {lam : ℝ}
    (hlam : 0 < lam) : SvMonotone (proximalMappingEReal f lam) := by
  intro w₀ x₀ h₀ w₁ x₁ h₁
  obtain ⟨hf₀, he₀⟩ := moreauEnvelope_eq_of_mem_proximalMapping hp h₀
  obtain ⟨hf₁, he₁⟩ := moreauEnvelope_eq_of_mem_proximalMapping hp h₁
  have i₀ := moreauEnvelope_le (f := f) (lam := lam) w₀ x₁
  have i₁ := moreauEnvelope_le (f := f) (lam := lam) w₁ x₀
  rw [he₀, hf₁, ← EReal.coe_add, EReal.coe_le_coe_iff] at i₀
  rw [he₁, hf₀, ← EReal.coe_add, EReal.coe_le_coe_iff] at i₁
  have hid := norm_sub_sq_cross_identity x₀ x₁ w₀ w₁
  have hc : 0 < 1 / (2 * lam) := by positivity
  have key : 1 / (2 * lam) *
      (‖x₀ - w₀‖ ^ 2 + ‖x₁ - w₁‖ ^ 2 - ‖x₁ - w₀‖ ^ 2 - ‖x₀ - w₁‖ ^ 2) ≤ 0 := by
    linarith
  rw [hid] at key
  by_contra hneg
  push_neg at hneg
  nlinarith

/-- Membership in `I + λT`, written as in the resolvent of the foundations module. -/
theorem mem_svAdd_id_smul_iff {T : E → Set E} {lam : ℝ} {x z : E} :
    z ∈ svAdd (fun y ↦ ({y} : Set E)) (fun y ↦ lam • T y) x ↔ ∃ v ∈ T x, z = x + lam • v := by
  rw [mem_svAdd]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [mem_singleton_iff] at ha
    obtain ⟨v, hv, rfl⟩ := mem_smul_set.1 hb
    exact ⟨v, hv, by rw [ha]⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨x, rfl, lam • v, smul_mem_smul_set hv, rfl⟩

/-- The inverse of the shifted subgradient relation of 10.2 is the resolvent. -/
theorem svInv_subgradientShift_eq_svResolvent (f : E → EReal) (lam : ℝ) :
    svInv (subgradientShift f lam) = svResolvent (subdifferential f) lam := by
  funext z
  ext x
  rw [mem_svResolvent, mem_svInv, subgradientShift]
  constructor
  · rintro ⟨v, hv, hvz⟩
    exact ⟨v, hv, hvz⟩
  · rintro ⟨v, hv, hvz⟩
    exact ⟨v, hv, hvz⟩

/-- Positive rescaling of the inverse relation preserves monotonicity. -/
theorem svMonotone_iff_of_mem_iff_inv_smul {P T : E → Set E} {lam : ℝ} (hlam : 0 < lam)
    (h : ∀ w x, x ∈ P w ↔ lam⁻¹ • w ∈ T x) : SvMonotone P ↔ SvMonotone T := by
  have hP : ∀ {x u}, u ∈ T x → x ∈ P (lam • u) := fun hu ↦ (h _ _).2 (by
    rwa [smul_smul, inv_mul_cancel₀ hlam.ne', one_smul])
  constructor
  · intro hPm x₀ u₀ h₀ x₁ u₁ h₁
    have := hPm (hP h₀) (hP h₁)
    rw [← smul_sub, real_inner_smul_right, real_inner_comm] at this
    exact nonneg_of_mul_nonneg_right this hlam
  · intro hTm w₀ x₀ h₀ w₁ x₁ h₁
    have := hTm ((h _ _).1 h₀) ((h _ _).1 h₁)
    rw [← smul_sub, real_inner_smul_left, real_inner_comm] at this
    exact nonneg_of_mul_nonneg_right this (inv_pos.2 hlam)

/-- Positive rescaling of the inverse relation preserves maximal monotonicity. -/
theorem svMaximalMonotone_iff_of_mem_iff_inv_smul {P T : E → Set E} {lam : ℝ} (hlam : 0 < lam)
    (h : ∀ w x, x ∈ P w ↔ lam⁻¹ • w ∈ T x) : SvMaximalMonotone P ↔ SvMaximalMonotone T := by
  have hP : ∀ {x u}, u ∈ T x → x ∈ P (lam • u) := fun hu ↦ (h _ _).2 (by
    rwa [smul_smul, inv_mul_cancel₀ hlam.ne', one_smul])
  rw [svMaximalMonotone_iff_forall_inner_nonneg, svMaximalMonotone_iff_forall_inner_nonneg,
    svMonotone_iff_of_mem_iff_inv_smul hlam h]
  refine and_congr_right fun _ ↦ ⟨fun hmax x u hu ↦ ?_, fun hmax w x hx ↦ ?_⟩
  · have hx : x ∈ P (lam • u) := by
      refine hmax (lam • u) x fun w' x' hx' ↦ ?_
      have h1 := hu x' (lam⁻¹ • w') ((h _ _).1 hx')
      have he : lam • u - w' = lam • (u - lam⁻¹ • w') := by
        rw [smul_sub, smul_smul, mul_inv_cancel₀ hlam.ne', one_smul]
      rw [he, real_inner_smul_right, real_inner_comm]
      exact mul_nonneg hlam.le h1
    have := (h _ _).1 hx
    rwa [smul_smul, inv_mul_cancel₀ hlam.ne', one_smul] at this
  · refine (h _ _).2 (hmax x (lam⁻¹ • w) fun x' u' hu' ↦ ?_)
    have h1 := hx (lam • u') x' (hP hu')
    have he : w - lam • u' = lam • (lam⁻¹ • w - u') := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hlam.ne', one_smul]
    rw [he, real_inner_smul_right, real_inner_comm] at h1
    exact nonneg_of_mul_nonneg_right h1 hlam

end Identities

section Quadratic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Slopes of affine minorants of `g` that touch `g` at `x`.  For a proper
convex function these are its subgradients (8.12). -/
def globalSupportSlopes (g : E → EReal) (x : E) : Set E :=
  {u | ∃ a : ℝ, g x = a ∧ ∀ y, ((a + ⟪u, y - x⟫_ℝ : ℝ) : EReal) ≤ g y}

theorem hasGradientAt_half_norm_sq [CompleteSpace E] (lam : ℝ) (x : E) :
    HasGradientAt (fun y ↦ 1 / (2 * lam) * ‖y‖ ^ 2) (lam⁻¹ • x) x := by
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt).const_mul (1 / (2 * lam))
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h using 1
  ext w
  simp only [InnerProductSpace.toDual_apply_apply, real_inner_smul_left,
    ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul,
    Nat.cast_ofNat]
  ring

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem isProper_add_coe {f : E → EReal} (hp : IsProper f) (k : E → ℝ) :
    IsProper fun y ↦ f y + (k y : EReal) := by
  obtain ⟨⟨x, hx⟩, hb⟩ := hp
  exact ⟨⟨x, EReal.add_lt_top hx.ne (EReal.coe_ne_top _)⟩,
    fun y ↦ EReal.bot_lt_add_iff.2 ⟨hb y, EReal.bot_lt_coe _⟩⟩

theorem convex_epigraph_coe_half_norm_sq {lam : ℝ} (hlam : 0 ≤ lam) :
    Convex ℝ (epigraph fun y : E ↦ (((1 / (2 * lam)) * ‖y‖ ^ 2 : ℝ) : EReal)) := by
  have hc : ConvexOn ℝ univ fun y : E ↦ (1 / (2 * lam)) * ‖y‖ ^ 2 := by
    have h2 : ConvexOn ℝ univ fun y : E ↦ ‖y‖ ^ 2 :=
      (convexOn_norm convex_univ).pow (fun _ _ ↦ norm_nonneg _) 2
    exact h2.smul (by positivity)
  have he : epigraph (fun y : E ↦ (((1 / (2 * lam)) * ‖y‖ ^ 2 : ℝ) : EReal)) =
      {p : E × ℝ | p.1 ∈ univ ∧ (1 / (2 * lam)) * ‖p.1‖ ^ 2 ≤ p.2} := by
    ext p
    simp only [epigraph, mem_setOf_eq, mem_univ, true_and, ge_iff_le, EReal.coe_le_coe_iff]
  rw [he]
  exact hc.convex_epigraph

/-- A proximal point of `w` is a point where `λ⁻¹w` supports
`g = f + (2λ)⁻¹‖·‖²` globally, and conversely. -/
theorem mem_proximalMappingEReal_iff_mem_globalSupportSlopes {f : E → EReal}
    (hf : ∀ y, f y ≠ ⊥) {lam : ℝ} (hlam : 0 < lam) {w x : E} :
    x ∈ proximalMappingEReal f lam w ↔
      lam⁻¹ • w ∈
        globalSupportSlopes (fun y ↦ f y + (((1 / (2 * lam)) * ‖y‖ ^ 2 : ℝ) : EReal)) x := by
  have hy2 : ∀ y : E, ‖y‖ ^ 2 = ‖y - x‖ ^ 2 + 2 * ⟪y - x, x⟫_ℝ + ‖x‖ ^ 2 := by
    intro y
    rw [show y = (y - x) + x by abel, norm_add_sq_real]
    simp
  have hw2 : ∀ y : E, ‖y - w‖ ^ 2 = ‖y‖ ^ 2 - 2 * ⟪y, w⟫_ℝ + ‖w‖ ^ 2 :=
    fun y ↦ norm_sub_sq_real y w
  simp only [globalSupportSlopes, mem_setOf_eq]
  constructor
  · intro hx
    obtain ⟨c, hc, hglob, -⟩ := global_inequality_of_mem_proximalMappingEReal hlam hx (hf x)
    refine ⟨c + 1 / (2 * lam) * ‖x‖ ^ 2, by rw [hc, ← EReal.coe_add], fun y ↦ ?_⟩
    by_cases htop : f y = ⊤
    · rw [htop, EReal.top_add_coe]
      exact le_top
    have hfy : f y = ((f y).toReal : EReal) := (EReal.coe_toReal htop (hf y)).symm
    have hg := hglob y
    rw [hfy, EReal.coe_le_coe_iff] at hg
    rw [hfy, ← EReal.coe_add, EReal.coe_le_coe_iff]
    have hin : ⟪lam⁻¹ • (w - x), y - x⟫_ℝ = ⟪lam⁻¹ • w, y - x⟫_ℝ - lam⁻¹ * ⟪y - x, x⟫_ℝ := by
      rw [smul_sub, inner_sub_left, real_inner_smul_left, real_inner_smul_left,
        real_inner_comm x (y - x)]
    rw [hin] at hg
    have hq : 1 / (2 * lam) * ‖y‖ ^ 2 = 1 / (2 * lam) * ‖y - x‖ ^ 2 +
        lam⁻¹ * ⟪y - x, x⟫_ℝ + 1 / (2 * lam) * ‖x‖ ^ 2 := by
      rw [hy2 y]
      field_simp
    linarith
  · rintro ⟨a, ha, hsupp⟩
    have hxtop : f x ≠ ⊤ := by
      intro htop
      rw [htop, EReal.top_add_coe] at ha
      exact EReal.coe_ne_top a ha.symm
    have hfx : f x = ((f x).toReal : EReal) := (EReal.coe_toReal hxtop (hf x)).symm
    have ha' : a = (f x).toReal + 1 / (2 * lam) * ‖x‖ ^ 2 := by
      rw [hfx, ← EReal.coe_add] at ha
      exact (EReal.coe_injective ha).symm
    have hmin : ∀ y, proximalObjectiveEReal f lam w x ≤ proximalObjectiveEReal f lam w y := by
      intro y
      rw [proximalObjectiveEReal, proximalObjectiveEReal]
      by_cases htop : f y = ⊤
      · rw [htop, EReal.top_add_coe]
        exact le_top
      have hfy : f y = ((f y).toReal : EReal) := (EReal.coe_toReal htop (hf y)).symm
      have hs := hsupp y
      rw [hfy, ← EReal.coe_add, EReal.coe_le_coe_iff] at hs
      rw [hfx, hfy, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
      rw [ha', real_inner_smul_left, inner_sub_right] at hs
      have hlam' : lam⁻¹ = 2 * (1 / (2 * lam)) := by field_simp
      rw [hw2 y, hw2 x, real_inner_comm w y, real_inner_comm w x]
      rw [hlam'] at hs
      linarith
    have hlt : proximalObjectiveEReal f lam w x < ⊤ := by
      rw [proximalObjectiveEReal, hfx, ← EReal.coe_add]
      exact EReal.coe_lt_top _
    have heq : proximalObjectiveEReal f lam w x = moreauEnvelopeEReal f lam w :=
      le_antisymm (le_iInf hmin) (iInf_le _ x)
    exact (mem_proximalMappingEReal_iff).2 ⟨heq, by rw [← heq]; exact hlt⟩

variable [FiniteDimensional ℝ E]

theorem globalSupportSlopes_eq_subdifferential {g : E → EReal} (hp : IsProper g)
    (hc : Convex ℝ (epigraph g)) : globalSupportSlopes g = subdifferential g := by
  funext x
  ext u
  constructor
  · rintro ⟨a, ha, h⟩
    exact (mem_subdifferential_iff_of_convex hc hp ha).2 h
  · intro hu
    obtain ⟨a, ha⟩ := hu.1
    exact ⟨a, ha, (mem_subdifferential_iff_of_convex hc hp ha).1 hu⟩

/-- Subgradients of `f + (2λ)⁻¹‖·‖²` are those of `f` translated by `λ⁻¹x`
(8.8(c)); both sides are empty where `f = ⊤`. -/
theorem mem_subdifferential_add_half_norm_sq_iff {f : E → EReal} (hf : ∀ y, f y ≠ ⊥)
    {lam : ℝ} {x u : E} :
    u ∈ subdifferential (fun y ↦ f y + (((1 / (2 * lam)) * ‖y‖ ^ 2 : ℝ) : EReal)) x ↔
      ∃ v ∈ subdifferential f x, u = v + lam⁻¹ • x := by
  by_cases htop : f x = ⊤
  · rw [subdifferential_eq_empty_of_eq_top (by rw [htop, EReal.top_add_coe]),
      subdifferential_eq_empty_of_eq_top htop]
    simp
  have hfx : f x = ((f x).toReal : EReal) := (EReal.coe_toReal htop (hf x)).symm
  have hk : ContDiffAt ℝ 1 (fun y : E ↦ 1 / (2 * lam) * ‖y‖ ^ 2) x :=
    (contDiff_const.mul (contDiff_norm_sq ℝ)).contDiffAt
  rw [(subdifferentials_add_smooth hfx hk).2.1, (hasGradientAt_half_norm_sq lam x).gradient]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, rfl⟩

/-- An lsc function whose touching affine minorants form a maximal monotone
slope mapping is convex (properness follows from maximality).  The touching
slopes are subgradients of the biconjugate, so maximality identifies the two
mappings; then `g = g**` on `dom ∂g**`, which is attentively dense in
`dom g**` (8.10), and lower semicontinuity of `g` gives `g = g**` everywhere. -/
theorem convex_epigraph_of_svMaximalMonotone_globalSupportSlopes {g : E → EReal}
    (hl : LowerSemicontinuous g)
    (hmax : SvMaximalMonotone (globalSupportSlopes g)) : Convex ℝ (epigraph g) := by
  have hne : ∃ x₀ u₀, u₀ ∈ globalSupportSlopes g x₀ := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨x', v', hv', -⟩ := hmax.2 0 0 (hcon 0 0)
    exact hcon x' v' hv'
  obtain ⟨x₀, u₀, a₀, ha₀, hsupp₀⟩ := hne
  set φ := fenchelConjugate (fenchelConjugate g) with hφdef
  have hφle : ∀ x, φ x ≤ g x := fenchelConjugate_fenchelConjugate_le g
  have hgs_top : fenchelConjugate g u₀ < ⊤ := by
    refine lt_of_le_of_lt ((fenchelConjugate_le_coe_iff g u₀ (⟪u₀, x₀⟫_ℝ - a₀)).2 fun y ↦ ?_)
      (EReal.coe_lt_top _)
    have he : ⟪u₀, y⟫_ℝ - (⟪u₀, x₀⟫_ℝ - a₀) = a₀ + ⟪u₀, y - x₀⟫_ℝ := by
      rw [inner_sub_right]
      ring
    rw [he]
    exact hsupp₀ y
  have hgs_p : IsProper (fenchelConjugate g) :=
    ⟨⟨u₀, hgs_top⟩, fun v ↦ bot_lt_fenchelConjugate_of_finite ha₀ v⟩
  have hφp : IsProper φ := isProper_fenchelConjugate hgs_p
    (lowerSemicontinuous_fenchelConjugate g) (convex_epigraph_fenchelConjugate g)
  have hφl : LowerSemicontinuous φ := lowerSemicontinuous_fenchelConjugate _
  have hφc : Convex ℝ (epigraph φ) := convex_epigraph_fenchelConjugate _
  have hA : ∀ x u, u ∈ globalSupportSlopes g x → g x = φ x ∧ u ∈ subdifferential φ x := by
    rintro x u ⟨a, ha, hs⟩
    have haff : ∀ z, (((innerSL ℝ u) z + (a - ⟪u, x⟫_ℝ) : ℝ) : EReal) =
        ((a + ⟪u, z - x⟫_ℝ : ℝ) : EReal) := by
      intro z
      rw [innerSL_apply_apply, inner_sub_right]
      congr 1
      ring
    have hmin : ∀ y, ((a + ⟪u, y - x⟫_ℝ : ℝ) : EReal) ≤ φ y := by
      intro y
      have h := affineMinorant_le_biconjugate (f := g) (l := innerSL ℝ u) (b := a - ⟪u, x⟫_ℝ)
        (fun z ↦ by rw [haff]; exact hs z) y
      rwa [haff] at h
    have hφx : φ x = a := le_antisymm ((hφle x).trans ha.le) (by simpa using hmin x)
    exact ⟨ha.trans hφx.symm, (mem_subdifferential_iff_of_convex hφc hφp hφx).2 hmin⟩
  have hS : subdifferential φ = globalSupportSlopes g :=
    hmax.eq_of_subset (svMonotone_subdifferential_of_convex hφp hφc)
      (fun x u hu ↦ (hA x u hu).2)
  have hgφ : ∀ x, g x = φ x := by
    intro x
    refine le_antisymm ?_ (hφle x)
    by_cases htop : φ x = ⊤
    · rw [htop]
      exact le_top
    have hφx : φ x = ((φ x).toReal : EReal) := (EReal.coe_toReal htop (hφp.2 x).ne').symm
    have hloc : IsLocallyLscAt φ x := isLocallyLscAt_of_lowerSemicontinuousOn isOpen_univ
      (hφl.lowerSemicontinuousOn univ) (mem_univ x) (hφp.2 x).ne' htop
    obtain ⟨y, hy, hyne⟩ := exists_attentive_seq_regularSubdifferential_nonempty hloc hφx
    obtain ⟨hyx, hyφ⟩ := tendsto_attentiveNhds_iff.1 hy
    have hgy : ∀ n, g (y n) = φ (y n) := by
      intro n
      obtain ⟨u, hu⟩ := (hyne n).2
      rw [hS] at hu
      exact (hA _ _ hu).1
    by_contra hlt
    push_neg at hlt
    obtain ⟨α, hα₁, hα₂⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
    have h1 : ∀ᶠ n in atTop, (α : EReal) < g (y n) := hyx.eventually (hl x α hα₂)
    have h2 : ∀ᶠ n in atTop, (φ ∘ y) n < α := hyφ.eventually (gt_mem_nhds hα₁)
    obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
    rw [hgy n] at hn1
    exact lt_asymm hn1 hn2
  have hgeq : g = φ := funext hgφ
  rw [hgeq]
  exact hφc

end Quadratic

section Proposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Proposition 12.19**, (a) ⇔ (b): `Pλf` is maximal monotone exactly when
`f + (2λ)⁻¹‖·‖²` is convex. -/
theorem svMaximalMonotone_proximalMappingEReal_iff_convex {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) {lam : ℝ} (hlam : 0 < lam) :
    SvMaximalMonotone (proximalMappingEReal f lam) ↔
      Convex ℝ (epigraph fun y ↦ f y + (((1 / (2 * lam)) * ‖y‖ ^ 2 : ℝ) : EReal)) := by
  have hf : ∀ y, f y ≠ ⊥ := fun y ↦ (hp.2 y).ne'
  have hgp := isProper_add_coe hp fun y : E ↦ 1 / (2 * lam) * ‖y‖ ^ 2
  have hgl : LowerSemicontinuous fun y ↦ f y + (((1 / (2 * lam)) * ‖y‖ ^ 2 : ℝ) : EReal) :=
    lowerSemicontinuous_add_coe hl (by fun_prop)
  rw [svMaximalMonotone_iff_of_mem_iff_inv_smul hlam
    (fun w x ↦ mem_proximalMappingEReal_iff_mem_globalSupportSlopes hf hlam)]
  refine ⟨convex_epigraph_of_svMaximalMonotone_globalSupportSlopes hgl, fun hgc ↦ ?_⟩
  rw [globalSupportSlopes_eq_subdifferential hgp hgc]
  exact svMaximalMonotone_subdifferential_of_convex hgp hgl hgc

/-- **Proposition 12.19**, (b) ⇔ (c): `f + (2λ)⁻¹‖·‖²` is convex exactly when
`I + λ∂f` is monotone. -/
theorem convex_add_half_norm_sq_iff_svMonotone {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) {lam : ℝ} (hlam : 0 < lam) :
    Convex ℝ (epigraph fun y ↦ f y + (((1 / (2 * lam)) * ‖y‖ ^ 2 : ℝ) : EReal)) ↔
      SvMonotone (svAdd (fun y ↦ ({y} : Set E)) (fun y ↦ lam • subdifferential f y)) := by
  have hf : ∀ y, f y ≠ ⊥ := fun y ↦ (hp.2 y).ne'
  have hgp := isProper_add_coe hp fun y : E ↦ 1 / (2 * lam) * ‖y‖ ^ 2
  have hgl : LowerSemicontinuous fun y ↦ f y + (((1 / (2 * lam)) * ‖y‖ ^ 2 : ℝ) : EReal) :=
    lowerSemicontinuous_add_coe hl (by fun_prop)
  rw [convex_epigraph_iff_svMonotone_subdifferential hgp hgl]
  have hmem : ∀ x z, z ∈ svAdd (fun y ↦ ({y} : Set E)) (fun y ↦ lam • subdifferential f y) x ↔
      lam⁻¹ • z ∈ subdifferential (fun y ↦ f y + (((1 / (2 * lam)) * ‖y‖ ^ 2 : ℝ) : EReal)) x := by
    intro x z
    rw [mem_svAdd_id_smul_iff, mem_subdifferential_add_half_norm_sq_iff hf]
    refine exists_congr fun v ↦ and_congr_right fun _ ↦ ?_
    constructor
    · rintro rfl
      rw [smul_add, smul_smul, inv_mul_cancel₀ hlam.ne', one_smul, add_comm]
    · intro h
      have := congrArg (fun u ↦ lam • u) h
      simp only [smul_smul, mul_inv_cancel₀ hlam.ne', one_smul, smul_add] at this
      rw [this, add_comm]
  constructor
  · intro hm x₀ z₀ h₀ x₁ z₁ h₁
    have := hm ((hmem _ _).1 h₀) ((hmem _ _).1 h₁)
    rw [← smul_sub, real_inner_smul_left] at this
    exact nonneg_of_mul_nonneg_right this (inv_pos.2 hlam)
  · intro hm x₀ u₀ h₀ x₁ u₁ h₁
    have hz : ∀ {x u}, u ∈ subdifferential
        (fun y ↦ f y + (((1 / (2 * lam)) * ‖y‖ ^ 2 : ℝ) : EReal)) x →
        lam • u ∈ svAdd (fun y ↦ ({y} : Set E)) (fun y ↦ lam • subdifferential f y) x := by
      intro x u hu
      rw [hmem, smul_smul, inv_mul_cancel₀ hlam.ne', one_smul]
      exact hu
    have := hm (hz h₀) (hz h₁)
    rw [← smul_sub, real_inner_smul_left] at this
    exact nonneg_of_mul_nonneg_right this hlam

omit [FiniteDimensional ℝ E] in
/-- Under (c), proximal points for every `μ ∈ (0, λ)` move at most
`λ/(λ - μ)` times as far as their base points. -/
theorem norm_sub_le_of_mem_proximalMappingEReal_of_svMonotone {f : E → EReal} (hp : IsProper f)
    {lam mu : ℝ} (hmu : 0 < mu) (hmulam : mu < lam)
    (hc : SvMonotone (svAdd (fun y ↦ ({y} : Set E)) (fun y ↦ lam • subdifferential f y)))
    {w₀ w₁ x₀ x₁ : E} (h₀ : x₀ ∈ proximalMappingEReal f mu w₀)
    (h₁ : x₁ ∈ proximalMappingEReal f mu w₁) :
    ‖x₁ - x₀‖ ≤ lam / (lam - mu) * ‖w₁ - w₀‖ := by
  obtain ⟨v₀, hv₀, hx₀⟩ := proximalMappingEReal_subset_inverse_subgradientShift hp hmu w₀ h₀
  obtain ⟨v₁, hv₁, hx₁⟩ := proximalMappingEReal_subset_inverse_subgradientShift hp hmu w₁ h₁
  have hm := hc ((mem_svAdd_id_smul_iff).2 ⟨v₀, hv₀, rfl⟩)
    ((mem_svAdd_id_smul_iff).2 ⟨v₁, hv₁, rfl⟩)
  have hx₀' : x₀ + mu • v₀ = w₀ := hx₀
  have hx₁' : x₁ + mu • v₁ = w₁ := hx₁
  have hdv : mu • (v₁ - v₀) = (w₁ - w₀) - (x₁ - x₀) := by
    rw [smul_sub, ← hx₀', ← hx₁']
    abel
  have hexp : mu • ((x₁ + lam • v₁) - (x₀ + lam • v₀)) =
      mu • (x₁ - x₀) + lam • ((w₁ - w₀) - (x₁ - x₀)) := by
    rw [← hdv, smul_comm lam mu]
    simp only [smul_sub, smul_add]
    abel
  have hm' : 0 ≤ mu * ⟪(x₁ + lam • v₁) - (x₀ + lam • v₀), x₁ - x₀⟫_ℝ := mul_nonneg hmu.le hm
  rw [← real_inner_smul_left, hexp, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    inner_sub_left (w₁ - w₀) (x₁ - x₀), real_inner_self_eq_norm_sq] at hm'
  have hcs := mul_le_mul_of_nonneg_left (real_inner_le_norm (w₁ - w₀) (x₁ - x₀))
    (hmu.trans hmulam).le
  have hpos : 0 < lam - mu := sub_pos.2 hmulam
  have key : (lam - mu) * ‖x₁ - x₀‖ * ‖x₁ - x₀‖ ≤ lam * ‖w₁ - w₀‖ * ‖x₁ - x₀‖ := by
    nlinarith
  rcases (norm_nonneg (x₁ - x₀)).eq_or_lt with ha | ha
  · rw [← ha]
    exact mul_nonneg (div_nonneg (hmu.trans hmulam).le hpos.le) (norm_nonneg _)
  · have key' : (lam - mu) * ‖x₁ - x₀‖ ≤ lam * ‖w₁ - w₀‖ := le_of_mul_le_mul_right key ha
    rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
    linarith

/-! ### The convex case -/

/-- **Example 10.2** in resolvent form: for a proper convex `f` and `λ > 0`,
`Pλf = (I + λ∂f)⁻¹`. -/
theorem proximalMappingEReal_eq_svResolvent_of_convex {f : E → EReal} (hp : IsProper f)
    (hc : Convex ℝ (epigraph f)) {lam : ℝ} (hlam : 0 < lam) :
    proximalMappingEReal f lam = svResolvent (subdifferential f) lam := by
  rw [proximalMappingEReal_eq_inverse_subgradientShift hc hp hlam,
    svInv_subgradientShift_eq_svResolvent]

/-- **Proposition 12.19**, convex case: `Pλf` is maximal monotone. -/
theorem svMaximalMonotone_proximalMappingEReal_of_convex {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) {lam : ℝ} (hlam : 0 < lam) :
    SvMaximalMonotone (proximalMappingEReal f lam) := by
  rw [proximalMappingEReal_eq_svResolvent_of_convex hp hc hlam]
  exact (svMaximalMonotone_subdifferential_of_convex hp hl hc).svMaximalMonotone_svResolvent hlam

/-- **Proposition 12.19**, convex case: `Pλf` is nonexpansive. -/
theorem svNonexpansive_proximalMappingEReal_of_convex {f : E → EReal} (hp : IsProper f)
    (hc : Convex ℝ (epigraph f)) {lam : ℝ} (hlam : 0 < lam) :
    SvNonexpansive (proximalMappingEReal f lam) := by
  rw [proximalMappingEReal_eq_svResolvent_of_convex hp hc hlam]
  exact (svMonotone_subdifferential_of_convex hp hc).svNonexpansive_svResolvent hlam.le

/-- **Proposition 12.19**, convex case: `Pλf` is single-valued everywhere. -/
theorem proximalMappingEReal_eq_singleton_of_convex {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) {lam : ℝ} (hlam : 0 < lam)
    (z : E) : proximalMappingEReal f lam z = {resolventMap (subdifferential f) lam z} := by
  rw [proximalMappingEReal_eq_svResolvent_of_convex hp hc hlam]
  exact (svMaximalMonotone_subdifferential_of_convex hp hl hc).svResolvent_eq_singleton_resolventMap
    hlam z

/-- The conjugate proximal mapping is the resolvent of the inverse subgradient
mapping (11.3 with 10.2). -/
theorem proximalMappingEReal_fenchelConjugate_eq_svResolvent {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) {lam : ℝ} (hlam : 0 < lam) :
    proximalMappingEReal (fenchelConjugate f) lam =
      svResolvent (svInv (subdifferential f)) lam := by
  rw [proximalMappingEReal_eq_svResolvent_of_convex (isProper_fenchelConjugate hp hl hc)
      (convex_epigraph_fenchelConjugate f) hlam,
    (subdifferential_fenchelConjugate_eq_inverse hp hl hc).1]

/-- **Proposition 12.19**, convex case: `I - P₁f = P₁f*`. -/
theorem sub_proximalMappingEReal_one_eq_fenchelConjugate {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) :
    (fun z ↦ ({z} : Set E) - proximalMappingEReal f 1 z) =
      proximalMappingEReal (fenchelConjugate f) 1 := by
  rw [proximalMappingEReal_eq_svResolvent_of_convex hp hc one_pos,
    proximalMappingEReal_fenchelConjugate_eq_svResolvent hp hl hc one_pos]
  exact sub_svResolvent_eq_svResolvent_svInv _

/-- **Proposition 12.19**, convex case: the parameterization of `gph ∂f`,
`(P₁f(z), P₁f*(z)) = (x, v) ⟺ z = x + v, v ∈ ∂f(x)`. -/
theorem proximalMappingEReal_one_eq_pair_iff {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) {z x v : E} :
    (proximalMappingEReal f 1 z = {x} ∧ proximalMappingEReal (fenchelConjugate f) 1 z = {v}) ↔
      z = x + v ∧ v ∈ subdifferential f x := by
  have hT := svMaximalMonotone_subdifferential_of_convex hp hl hc
  rw [proximalMappingEReal_eq_svResolvent_of_convex hp hc one_pos,
    proximalMappingEReal_fenchelConjugate_eq_svResolvent hp hl hc one_pos,
    hT.svResolvent_eq_singleton_resolventMap one_pos, hT.inv.svResolvent_eq_singleton_resolventMap
      one_pos, singleton_eq_singleton_iff, singleton_eq_singleton_iff, ← Prod.mk.injEq]
  exact hT.mintyMap_eq_iff

/-- **Proposition 12.19**, convex case: the parameterization of `gph ∂f` by
`(P₁f, P₁f*)` is Lipschitz continuous. -/
theorem exists_lipschitzWith_proximal_parameterization {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) :
    ∃ P Q : E → E, LipschitzWith 1 (fun z ↦ (P z, Q z)) ∧
      ∀ z, proximalMappingEReal f 1 z = {P z} ∧
        proximalMappingEReal (fenchelConjugate f) 1 z = {Q z} := by
  have hT := svMaximalMonotone_subdifferential_of_convex hp hl hc
  refine ⟨resolventMap (subdifferential f) 1, resolventMap (svInv (subdifferential f)) 1,
    hT.lipschitzWith_mintyMap, fun z ↦ ⟨?_, ?_⟩⟩
  · rw [proximalMappingEReal_eq_svResolvent_of_convex hp hc one_pos]
    exact hT.svResolvent_eq_singleton_resolventMap one_pos z
  · rw [proximalMappingEReal_fenchelConjugate_eq_svResolvent hp hl hc one_pos]
    exact hT.inv.svResolvent_eq_singleton_resolventMap one_pos z

/-! ### Consequences of (a)–(c) -/

/-- Under (b), `f` is prox-bounded with threshold at least every `μ ∈ (0, λ)`:
an affine minorant of `f + (2λ)⁻¹‖·‖²` bounds `f + (2μ)⁻¹‖·‖²` from below. -/
theorem coe_le_proxThreshold_of_convex_add_half_norm_sq {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) {lam mu : ℝ} (hmu : 0 < mu) (hmulam : mu < lam)
    (hb : Convex ℝ (epigraph fun y ↦ f y + (((1 / (2 * lam)) * ‖y‖ ^ 2 : ℝ) : EReal))) :
    (mu : EReal) ≤ proxThreshold f := by
  have hf : ∀ y, f y ≠ ⊥ := fun y ↦ (hp.2 y).ne'
  have hgp := isProper_add_coe hp fun y : E ↦ 1 / (2 * lam) * ‖y‖ ^ 2
  have hgl : LowerSemicontinuous fun y ↦ f y + (((1 / (2 * lam)) * ‖y‖ ^ 2 : ℝ) : EReal) :=
    lowerSemicontinuous_add_coe hl (by fun_prop)
  obtain ⟨l, b, hlb⟩ := exists_continuousAffineMinorant_of_convex_lsc_isProper hb hgl hgp
  set c : ℝ := 1 / (2 * mu) - 1 / (2 * lam) with hcdef
  have hc : 0 < c := by
    rw [hcdef, sub_pos]
    exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
  set L := ‖l‖
  unfold proxThreshold
  refine le_iSup₂_of_le mu ⟨hmu, 0, ?_⟩ le_rfl
  refine lt_of_lt_of_le (EReal.bot_lt_coe (b - L ^ 2 / (4 * c))) (le_iInf fun y ↦ ?_)
  by_cases htop : f y = ⊤
  · rw [htop, EReal.top_add_coe]
    exact le_top
  have hfy : f y = ((f y).toReal : EReal) := (EReal.coe_toReal htop (hf y)).symm
  have h1 := hlb y
  rw [hfy, ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
  rw [hfy, ← EReal.coe_add, EReal.coe_le_coe_iff, sub_zero]
  have h2 : -(L * ‖y‖) ≤ l y := by
    have := l.le_opNorm y
    rw [Real.norm_eq_abs] at this
    linarith [neg_abs_le (l y)]
  have h3 : L ^ 2 / (4 * c) + (c * ‖y‖ ^ 2 - L * ‖y‖) = (2 * c * ‖y‖ - L) ^ 2 / (4 * c) := by
    field_simp
    ring
  have h4 : 0 ≤ (2 * c * ‖y‖ - L) ^ 2 / (4 * c) := div_nonneg (sq_nonneg _) (by positivity)
  have h5 : 1 / (2 * mu) * ‖y‖ ^ 2 = 1 / (2 * lam) * ‖y‖ ^ 2 + c * ‖y‖ ^ 2 := by
    rw [hcdef]
    ring
  linarith

/-- Under (b), the threshold of prox-boundedness of `f` is at least `λ`. -/
theorem coe_le_proxThreshold_of_convex_add_half_norm_sq' {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) {lam : ℝ} (hlam : 0 < lam)
    (hb : Convex ℝ (epigraph fun y ↦ f y + (((1 / (2 * lam)) * ‖y‖ ^ 2 : ℝ) : EReal))) :
    (lam : EReal) ≤ proxThreshold f := by
  refine le_of_forall_lt_imp_le_of_dense fun a ha ↦ ?_
  induction a using EReal.rec with
  | bot => exact bot_le
  | top => exact absurd ha (not_lt.2 le_top)
  | coe r =>
    have hr : r < lam := EReal.coe_lt_coe_iff.1 ha
    have hm := coe_le_proxThreshold_of_convex_add_half_norm_sq hp hl (mu := max r (lam / 2))
      ((half_pos hlam).trans_le (le_max_right _ _)) (max_lt hr (half_lt_self hlam)) hb
    exact (EReal.coe_le_coe_iff.2 (le_max_left _ _)).trans hm

/-- **Proposition 12.19**: conditions (a)–(c) force `Pλf = (I + λ∂f)⁻¹`. -/
theorem proximalMappingEReal_eq_svResolvent_of_svMaximalMonotone {f : E → EReal}
    (hp : IsProper f) (hl : LowerSemicontinuous f) {lam : ℝ} (hlam : 0 < lam)
    (ha : SvMaximalMonotone (proximalMappingEReal f lam)) :
    proximalMappingEReal f lam = svResolvent (subdifferential f) lam := by
  have hb := (svMaximalMonotone_proximalMappingEReal_iff_convex hp hl hlam).1 ha
  have hc := (convex_add_half_norm_sq_iff_svMonotone hp hl hlam).1 hb
  have hmono : SvMonotone (svResolvent (subdifferential f) lam) := hc.inv
  refine (ha.eq_of_subset hmono fun z ↦ ?_).symm
  rw [← svInv_subgradientShift_eq_svResolvent]
  exact proximalMappingEReal_subset_inverse_subgradientShift hp hlam z

/-- **Proposition 12.19**: under (b), for every `μ ∈ (0, λ)` the proximal mapping
`Pμf` is single-valued and Lipschitz continuous with constant `λ/(λ - μ)`. -/
theorem exists_lipschitzWith_proximalMappingEReal_of_convex_add {f : E → EReal}
    (hp : IsProper f) (hl : LowerSemicontinuous f) {lam mu : ℝ} (hmu : 0 < mu)
    (hmulam : mu < lam)
    (hb : Convex ℝ (epigraph fun y ↦ f y + (((1 / (2 * lam)) * ‖y‖ ^ 2 : ℝ) : EReal))) :
    ∃ P : E → E, LipschitzWith (Real.toNNReal (lam / (lam - mu))) P ∧
      ∀ w, proximalMappingEReal f mu w = {P w} := by
  have hc := (convex_add_half_norm_sq_iff_svMonotone hp hl (hmu.trans hmulam)).1 hb
  have hthr : (mu : EReal) < proxThreshold f :=
    (EReal.coe_lt_coe_iff.2 (by linarith : mu < (mu + lam) / 2)).trans_le
      (coe_le_proxThreshold_of_convex_add_half_norm_sq hp hl (by linarith) (by linarith) hb)
  have hne : ∀ w, (proximalMappingEReal f mu w).Nonempty :=
    proximalMappingEReal_nonempty_of_lt_proxThreshold hp hl hmu hthr
  choose P hP using hne
  have hle : ∀ w₀ w₁ x₀ x₁, x₀ ∈ proximalMappingEReal f mu w₀ →
      x₁ ∈ proximalMappingEReal f mu w₁ → ‖x₁ - x₀‖ ≤ lam / (lam - mu) * ‖w₁ - w₀‖ :=
    fun _ _ _ _ h₀ h₁ ↦ norm_sub_le_of_mem_proximalMappingEReal_of_svMonotone hp hmu hmulam hc h₀ h₁
  refine ⟨P, LipschitzWith.of_dist_le' fun x y ↦ ?_, fun w ↦ ?_⟩
  · rw [dist_eq_norm, dist_eq_norm]
    exact hle y x (P y) (P x) (hP y) (hP x)
  · refine eq_singleton_iff_unique_mem.2 ⟨hP w, fun x hx ↦ ?_⟩
    have h := hle w w (P w) x (hP w) hx
    rw [sub_self, norm_zero, mul_zero] at h
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h)

/-- **Proposition 12.19 (proximal mappings).**  For a proper lsc `f` on a
finite-dimensional space:
* every `Pλf` with `λ > 0` is monotone;
* if `f` is convex, every `Pλf` is maximal monotone, nonexpansive and
  single-valued, `I - P₁f = P₁f*`, and `(P₁f, P₁f*)` is a Lipschitz
  parameterization of `gph ∂f`;
* for each `λ > 0` the conditions (a) `Pλf` maximal monotone, (b)
  `f + (2λ)⁻¹‖·‖²` convex, (c) `I + λ∂f` monotone are equivalent, and they
  imply `Pλf = (I + λ∂f)⁻¹` and that `Pμf` is single-valued and Lipschitz with
  constant `λ/(λ - μ)` for every `μ ∈ (0, λ)`. -/
theorem proximal_mappings {f : E → EReal} (hp : IsProper f) (hl : LowerSemicontinuous f) :
    (∀ lam : ℝ, 0 < lam → SvMonotone (proximalMappingEReal f lam)) ∧
    (Convex ℝ (epigraph f) →
      (∀ lam : ℝ, 0 < lam → SvMaximalMonotone (proximalMappingEReal f lam) ∧
        SvNonexpansive (proximalMappingEReal f lam) ∧
        ∀ z, ∃ x, proximalMappingEReal f lam z = {x}) ∧
      (fun z ↦ ({z} : Set E) - proximalMappingEReal f 1 z) =
        proximalMappingEReal (fenchelConjugate f) 1 ∧
      (∀ z x v, (proximalMappingEReal f 1 z = {x} ∧
          proximalMappingEReal (fenchelConjugate f) 1 z = {v}) ↔
        z = x + v ∧ v ∈ subdifferential f x) ∧
      ∃ P Q : E → E, LipschitzWith 1 (fun z ↦ (P z, Q z)) ∧
        ∀ z, proximalMappingEReal f 1 z = {P z} ∧
          proximalMappingEReal (fenchelConjugate f) 1 z = {Q z}) ∧
    (∀ lam : ℝ, 0 < lam →
      List.TFAE [SvMaximalMonotone (proximalMappingEReal f lam),
        Convex ℝ (epigraph fun y ↦ f y + (((1 / (2 * lam)) * ‖y‖ ^ 2 : ℝ) : EReal)),
        SvMonotone (svAdd (fun y ↦ ({y} : Set E)) (fun y ↦ lam • subdifferential f y))] ∧
      (SvMaximalMonotone (proximalMappingEReal f lam) →
        proximalMappingEReal f lam = svResolvent (subdifferential f) lam ∧
        ∀ mu : ℝ, 0 < mu → mu < lam → ∃ P : E → E,
          LipschitzWith (Real.toNNReal (lam / (lam - mu))) P ∧
            ∀ w, proximalMappingEReal f mu w = {P w})) := by
  refine ⟨fun lam hlam ↦ svMonotone_proximalMappingEReal hp hlam, fun hc ↦ ⟨fun lam hlam ↦
    ⟨svMaximalMonotone_proximalMappingEReal_of_convex hp hl hc hlam,
      svNonexpansive_proximalMappingEReal_of_convex hp hc hlam,
      fun z ↦ ⟨_, proximalMappingEReal_eq_singleton_of_convex hp hl hc hlam z⟩⟩,
    sub_proximalMappingEReal_one_eq_fenchelConjugate hp hl hc,
    fun z x v ↦ proximalMappingEReal_one_eq_pair_iff hp hl hc,
    exists_lipschitzWith_proximal_parameterization hp hl hc⟩, fun lam hlam ↦ ⟨?_, fun ha ↦
    ⟨proximalMappingEReal_eq_svResolvent_of_svMaximalMonotone hp hl hlam ha,
      fun mu hmu hmulam ↦ exists_lipschitzWith_proximalMappingEReal_of_convex_add hp hl hmu hmulam
        ((svMaximalMonotone_proximalMappingEReal_iff_convex hp hl hlam).1 ha)⟩⟩⟩
  tfae_have 1 ↔ 2 := svMaximalMonotone_proximalMappingEReal_iff_convex hp hl hlam
  tfae_have 2 ↔ 3 := convex_add_half_norm_sq_iff_svMonotone hp hl hlam
  tfae_finish

end Proposition

end RW
