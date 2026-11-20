/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Subderivative criteria for regularity
-/

import RockafellarWets.Chapter6.RegularTangentChangeOfCoordinates
import RockafellarWets.Chapter8.SubderivativeRelationships

open Filter Function Metric Set Topology

namespace RW

variable {E : Type*} [NormedAddCommGroup E]

/-- At a finite base value a locally closed epigraph gives local lower
semicontinuity in the truncated-sublevel sense of Definition 1.33. -/
theorem isLocallyLscAt_of_isLocallyClosedAt_epigraph {f : E → EReal} {x : E} {c : ℝ}
    (hx : f x = c) (hlc : IsLocallyClosedAt (epigraph f) (x, c)) : IsLocallyLscAt f x := by
  obtain ⟨V, hV, _, hclosed⟩ := hlc
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hV
  have hrect : closedBall x r ×ˢ closedBall c r ⊆ V := closedBall_prod_same x c r ▸ hsub
  let d := c - r / 2
  have hd : d ∈ closedBall c r := by
    rw [Real.closedBall_eq_Icc]
    exact ⟨by dsimp [d]; linarith, by dsimp [d]; linarith⟩
  have hd0 : d < c := by dsimp [d]; linarith
  let S := (fun y : E ↦ (y, d)) ⁻¹' (epigraph f ∩ V)
  have hS : IsClosed S := hclosed.preimage (continuous_id.prodMk continuous_const)
  have hxS : x ∈ Sᶜ := fun h ↦ (EReal.coe_lt_coe_iff.mpr hd0).not_ge (hx ▸ h.1)
  obtain ⟨s, hs, hsS⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hS.isOpen_compl.mem_nhds hxS)
  refine ⟨hx ▸ EReal.coe_ne_bot c, hx ▸ EReal.coe_ne_top c, min s r, lt_min hs hr, ?_⟩
  intro a ha
  rw [hx, EReal.toReal_coe] at ha
  by_cases had : a < d
  · have hempty : closedBall x (min s r) ∩ {y | f y ≤ a} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro y ⟨hy, hfy⟩
      apply hsS (closedBall_subset_closedBall (min_le_left ..) hy)
      exact ⟨hfy.trans (EReal.coe_le_coe_iff.mpr had.le),
        hrect ⟨closedBall_subset_closedBall (min_le_right ..) hy, hd⟩⟩
    rw [hempty]
    exact isClosed_empty
  · have hac : a ∈ closedBall c r := by
      rw [Real.closedBall_eq_Icc]
      have hda := le_of_not_gt had
      exact ⟨by dsimp [d] at hda; linarith, by linarith [min_le_right s r]⟩
    have he : closedBall x (min s r) ∩ {y | f y ≤ a} =
        closedBall x (min s r) ∩ (fun y : E ↦ (y, a)) ⁻¹' (epigraph f ∩ V) := by
      ext y
      exact ⟨fun h ↦ ⟨h.1, h.2, hrect ⟨closedBall_subset_closedBall (min_le_right ..) h.1, hac⟩⟩,
        fun h ↦ ⟨h.1, h.2.1⟩⟩
    rw [he]
    exact isClosed_closedBall.inter (hclosed.preimage (continuous_id.prodMk continuous_const))

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem IsSubdifferentiallyRegularAt.isLocallyLscAt {f : E → EReal} {x : E}
    (h : IsSubdifferentiallyRegularAt f x) : IsLocallyLscAt f x := by
  let L := l2ProdEquiv E
  have hx := (EReal.coe_toReal h.2.1 h.1).symm
  apply isLocallyLscAt_of_isLocallyClosedAt_epigraph hx
  have ht : IsLocallyClosedAt (L.symm ⁻¹' (L ⁻¹' epigraph f)) (x, (f x).toReal) :=
    IsLocallyClosedAt.preimage_continuousLinearEquiv L.symm h.2.2.1
  simpa only [preimage_preimage, ContinuousLinearEquiv.self_comp_symm, preimage_id_eq] using ht

/-- **Corollary 8.19.** A finite locally lsc function is regular precisely
when its two subderivative functions agree. -/
theorem isSubdifferentiallyRegularAt_iff_subderivative_eq_regularSubderivative {f : E → EReal} {x : E} :
    IsSubdifferentiallyRegularAt f x ↔
      IsLocallyLscAt f x ∧ subderivative f x = regularSubderivative f x := by
  have equiv (hl : IsLocallyLscAt f x) : IsSubdifferentiallyRegularAt f x ↔
      subderivative f x = regularSubderivative f x := by
    let L := l2ProdEquiv E
    let p := WithLp.toLp 2 (x, (f x).toReal)
    have hx := (EReal.coe_toReal hl.2.1 hl.1).symm
    have hr : L p ∈ epigraph f := hx.le
    have hreg : IsSubdifferentiallyRegularAt f x ↔ IsClarkeRegularAt (L ⁻¹' epigraph f) p :=
      ⟨fun h ↦ h.2.2, fun h ↦ ⟨hl.1, hl.2.1, h⟩⟩
    have hpre : regularTangentCone (L ⁻¹' epigraph f) p = L ⁻¹' regularTangentCone (epigraph f) (L p) :=
      regularTangentCone_preimage (Φ' := L) L.toContinuousLinearMap.hasStrictFDerivAt _ hr
    rw [hreg, isClarkeRegularAt_iff_tangentCone_eq_regularTangentCone (show p ∈ L ⁻¹' epigraph f from hr)
      (IsLocallyClosedAt.preimage_continuousLinearEquiv L hl.isLocallyClosedAt_epigraph),
      tangentCone_preimage_continuousLinearEquiv, hpre]
    change L ⁻¹' tangentCone (epigraph f) (x, (f x).toReal) =
      L ⁻¹' regularTangentCone (epigraph f) (x, (f x).toReal) ↔ _
    rw [L.surjective.preimage_injective.eq_iff, ← epigraph_subderivative_eq_tangentCone hx,
      ← epigraph_regularSubderivative_eq_regularTangentCone hx hl.lowerSemicontinuousAt]
    exact ⟨eq_of_epigraph_eq, congrArg epigraph⟩
  exact ⟨fun h ↦ ⟨h.isLocallyLscAt, (equiv h.isLocallyLscAt).mp h⟩,
    fun ⟨hl, hd⟩ ↦ (equiv hl).mpr hd⟩

/-- The equivalent neighboring-subderivative criterion of 8.19 in epigraph form. -/
theorem isSubdifferentiallyRegularAt_iff_attentive_inner_epigraph {f : E → EReal} {x : E} :
    IsSubdifferentiallyRegularAt f x ↔ IsLocallyLscAt f x ∧
      epigraph (subderivative f x) =
        innerSetLimitAlong (attentiveNhds f x) (fun y ↦ epigraph (subderivative f y)) := by
  rw [isSubdifferentiallyRegularAt_iff_subderivative_eq_regularSubderivative]
  apply and_congr_right
  intro hl
  rw [← epigraph_regularSubderivative_eq_inner_epigraph_subderivative hl]
  exact ⟨congrArg epigraph, eq_of_epigraph_eq⟩

end RW
