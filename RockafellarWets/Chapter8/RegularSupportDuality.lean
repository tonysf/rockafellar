/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Subderivative–subgradient duality at regular points
-/

import RockafellarWets.Chapter8.HorizontalEpigraphNormals
import RockafellarWets.Chapter8.SubderivativeRegularityCriterion
import RockafellarWets.Chapter8.SupportCorrespondence

open Filter Set Topology
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {x : E}

/-- **Theorem 8.30.** At a regular point the limiting subgradients are all
linear minorants of the subderivative, even when this set is empty. -/
theorem IsSubdifferentiallyRegularAt.subdifferential_eq_linearMinorantSet
    (h : IsSubdifferentiallyRegularAt f x) :
    subdifferential f x = linearMinorantSet (subderivative f x) := by
  let c := (f x).toReal
  have hx : f x = (c : EReal) := (EReal.coe_toReal h.2.1 h.1).symm
  have hcones : normalCone (euclideanEpigraph f) (WithLp.toLp 2 (x,c)) =
      regularNormalCone (euclideanEpigraph f) (WithLp.toLp 2 (x,c)) := h.2.2.2
  ext v
  rw [mem_subdifferential_iff_epigraph_normal hx, hcones,
    ← mem_regularSubdifferential_iff_epigraph_normal hx, regularSubdifferential_eq_setOf_inner_le_subderivative hx]
  rfl

/-- At regular points a nonvertical subderivative at zero guarantees that the
entire subderivative is proper. -/
theorem IsSubdifferentiallyRegularAt.isProper_subderivative (h : IsSubdifferentiallyRegularAt f x)
    (h₀ : subderivative f x 0 ≠ ⊥) : IsProper (subderivative f x) := by
  obtain ⟨hc,hk,hh,hl⟩ := h.subderivative_properties
  have hz := hh.zero_eq_zero_or_bot.resolve_right h₀
  have hfin : subderivative f x 0 = ((0 : ℝ) : EReal) := hz
  exact ⟨⟨0,hfin.trans_lt (EReal.coe_lt_top _)⟩,
    has_no_bot_of_closed_convex_cone_epigraph_of_finite (isClosed_epigraph_of_lsc_ereal _ hl) hc hk hfin⟩

/-- **Theorem 8.30.** Nonemptiness of the limiting subdifferential is exactly
the exclusion of a downward vertical tangent. -/
theorem IsSubdifferentiallyRegularAt.subdifferential_nonempty_iff (h : IsSubdifferentiallyRegularAt f x) :
    (subdifferential f x).Nonempty ↔ subderivative f x 0 ≠ ⊥ := by
  rw [h.subdifferential_eq_linearMinorantSet]
  constructor
  · rintro ⟨v,hv⟩
    exact ((EReal.bot_lt_coe _).trans_le (hv 0)).ne'
  · intro h₀
    have hp := h.isProper_subderivative h₀
    have hrepr := supportFunction_linearMinorantSet (h.sublinear_subderivative fun w ↦ (hp.2 w).ne')
      h.subderivative_properties.2.2.2 hp
    by_contra! he
    exact h₀ (by simpa only [he,supportFunction_empty] using (congrFun hrepr 0).symm)

/-- **Theorem 8.30.** Under its equivalent nondegeneracy conditions the
subderivative is a proper epi-derivative, lsc, sublinear, and the support
function of the closed convex subdifferential. -/
theorem IsSubdifferentiallyRegularAt.subderivative_support_duality (h : IsSubdifferentiallyRegularAt f x)
    (hn : (subdifferential f x).Nonempty) :
    ProperlyEpiDifferentiableAt f x ∧
      PKConvergesAlong (𝓝[>] (0 : ℝ)) (fun t ↦ epigraph (differenceQuotient f x t))
        (epigraph (subderivative f x)) ∧
      subderivative f x = supportFunction (subdifferential f x) ∧
      IsClosed (subdifferential f x) ∧ Convex ℝ (subdifferential f x) ∧
      LowerSemicontinuous (subderivative f x) ∧ Sublinear (subderivative f x) := by
  have hp := h.isProper_subderivative (h.subdifferential_nonempty_iff.1 hn)
  obtain ⟨_,_,g,hg⟩ := h.epiDifferentiableAt
  obtain rfl := eq_subderivative_of_pkConvergesAlong hg
  have hs := h.sublinear_subderivative fun w ↦ (hp.2 w).ne'
  have hl := h.subderivative_properties.2.2.2
  refine ⟨⟨h.1,h.2.1,_,hp,hg⟩,hg,?_⟩
  rw [h.subdifferential_eq_linearMinorantSet]
  exact ⟨(supportFunction_linearMinorantSet hs hl hp).symm,isClosed_linearMinorantSet _,
    convex_linearMinorantSet _,hl,hs⟩

/-- **Theorem 8.30.** The horizon subdifferential is the polar of the
subderivative domain without any additional properness condition. -/
theorem IsSubdifferentiallyRegularAt.horizonSubdifferential_eq_polar_domain
    (h : IsSubdifferentiallyRegularAt f x) :
    horizonSubdifferential f x = polarCone (effectiveDomain (subderivative f x)) := by
  let c := (f x).toReal
  have hx : f x = (c : EReal) := (EReal.coe_toReal h.2.1 h.1).symm
  have hcones : normalCone (euclideanEpigraph f) (WithLp.toLp 2 (x,c)) =
      regularNormalCone (euclideanEpigraph f) (WithLp.toLp 2 (x,c)) := h.2.2.2
  ext v
  rw [mem_horizonSubdifferential_iff_epigraph_normal_of_locallyLsc h.isLocallyLscAt hx,
    hcones,horizontal_regularNormal_iff_polar_subderivative_domain hx]

/-- At regular points the domain of the subderivative is already a convex cone. -/
theorem IsSubdifferentiallyRegularAt.convex_cone_subderivative_domain (h : IsSubdifferentiallyRegularAt f x) :
    Convex ℝ (effectiveDomain (subderivative f x)) ∧ IsCone (effectiveDomain (subderivative f x)) := by
  rw [← epigraph_proj_eq_effectiveDomain]
  exact ⟨h.subderivative_properties.1.linear_image (LinearMap.fst ℝ E ℝ),
    LinearMap.isCone_image (LinearMap.fst ℝ E ℝ) h.subderivative_properties.2.1⟩

/-- The polar in the reverse direction is the closure of the effective
domain, including when the subdifferential is empty. -/
theorem IsSubdifferentiallyRegularAt.polar_horizonSubdifferential_eq_closure_domain
    (h : IsSubdifferentiallyRegularAt f x) :
    polarCone (horizonSubdifferential f x) = closure (effectiveDomain (subderivative f x)) := by
  obtain ⟨hc,hk⟩ := h.convex_cone_subderivative_domain
  rw [h.horizonSubdifferential_eq_polar_domain,polarCone_bipolar,conicHull_eq_self_of_convex_isCone hc hk]

end RW
