/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Regularity under smooth perturbations
-/

import RockafellarWets.Chapter8.SubderivativeRegularityCriterion
import Mathlib.Analysis.Calculus.Gradient.Basic

open Filter Function Metric Set Topology
open scoped InnerProductSpace

namespace RW

private theorem locallyClosedAt_preimage_of_continuousOn {E F : Type*} [PseudoMetricSpace E]
    [TopologicalSpace F] {C : Set F} {P : E → F} {U : Set E} {x : E}
    (hU : U ∈ 𝓝 x) (hP : ContinuousOn P U) (hC : IsLocallyClosedAt C (P x)) :
    IsLocallyClosedAt (P ⁻¹' C) x := by
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hU
  obtain ⟨V, hV, hVc, hCV⟩ := hC
  have hc := hP.mono hsub
  refine ⟨closedBall x r ∩ P ⁻¹' V, inter_mem (closedBall_mem_nhds x hr)
    (hP.continuousAt hU hV), hc.preimage_isClosed_of_isClosed isClosed_closedBall hVc, ?_⟩
  simpa only [preimage_inter, inter_left_comm] using hc.preimage_isClosed_of_isClosed isClosed_closedBall hCV

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

private theorem regular_iff_ordinary_epigraph {g : E → EReal} {x : E} {c : ℝ} (hx : g x = c) :
    IsSubdifferentiallyRegularAt g x ↔ IsLocallyClosedAt (epigraph g) (x, c) ∧
      tangentCone (epigraph g) (x, c) = regularTangentCone (epigraph g) (x, c) := by
  rw [isSubdifferentiallyRegularAt_iff_subderivative_eq_regularSubderivative]
  have hbase : (g x).toReal = c := by simp [hx]
  constructor
  · rintro ⟨hl, he⟩
    refine ⟨hbase ▸ hl.isLocallyClosedAt_epigraph, ?_⟩
    rw [← epigraph_subderivative_eq_tangentCone hx, he,
      epigraph_regularSubderivative_eq_regularTangentCone hx hl.lowerSemicontinuousAt]
  · rintro ⟨hc, ht⟩
    have hl := isLocallyLscAt_of_isLocallyClosedAt_epigraph hx hc
    refine ⟨hl, eq_of_epigraph_eq ?_⟩
    rw [epigraph_subderivative_eq_tangentCone hx,
      epigraph_regularSubderivative_eq_regularTangentCone hx hl.lowerSemicontinuousAt, ht]

private theorem regular_add_of_strictFDerivAt {g : E → EReal} {k : E → ℝ} {x : E} {U : Set E}
    {A : E →L[ℝ] ℝ} (hU : U ∈ 𝓝 x) (hk : ContinuousOn k U) (hA : HasStrictFDerivAt k A x)
    (hg : IsSubdifferentiallyRegularAt g x) :
    IsSubdifferentiallyRegularAt (fun y ↦ g y + (k y : EReal)) x := by
  let c := (g x).toReal
  have hx : g x = (c : EReal) := (EReal.coe_toReal hg.2.1 hg.1).symm
  let f := fun y ↦ g y + (k y : EReal)
  have hfx : f x = ((c + k x : ℝ) : EReal) := by simp only [f, hx, EReal.coe_add]
  let P := fun p : E × ℝ ↦ (p.1, p.2 - k p.1)
  let L := (ContinuousLinearEquiv.refl ℝ E).skewProd (ContinuousLinearEquiv.refl ℝ ℝ) (-A)
  let p := (x, c + k x)
  have hP : HasStrictFDerivAt P (L : (E × ℝ) →L[ℝ] E × ℝ) p := by
    have hfst : HasStrictFDerivAt (Prod.fst : E × ℝ → E) (ContinuousLinearMap.fst ℝ E ℝ) p := hasStrictFDerivAt_fst
    have hAt : HasStrictFDerivAt k A p.1 := hA
    convert hfst.prodMk (hasStrictFDerivAt_snd.sub (hAt.comp p hfst)) using 1
  have hpe : P p = (x, c) := by simp [P, p]
  have he : epigraph f = P ⁻¹' epigraph g := by
    ext ⟨y, b⟩
    change g y + (k y : EReal) ≤ (b : EReal) ↔ g y ≤ ((b - k y : ℝ) : EReal)
    cases g y using EReal.rec with
    | bot => simp
    | top => simp only [EReal.top_add_coe, top_le_iff, EReal.coe_ne_top]
    | coe z => simp only [← EReal.coe_add, EReal.coe_le_coe_iff, le_sub_iff_add_le]
  obtain ⟨hclosed, htan⟩ := (regular_iff_ordinary_epigraph hx).mp hg
  rw [← hpe] at hclosed htan
  apply (regular_iff_ordinary_epigraph hfx).mpr
  rw [he]
  change IsLocallyClosedAt (P ⁻¹' epigraph g) p ∧
    tangentCone (P ⁻¹' epigraph g) p = regularTangentCone (P ⁻¹' epigraph g) p
  have hnhds : Prod.fst ⁻¹' U ∈ 𝓝 p := continuous_fst.continuousAt hU
  have hcont : ContinuousOn P (Prod.fst ⁻¹' U) := continuous_fst.continuousOn.prodMk
    (continuous_snd.continuousOn.sub (hk.comp continuous_fst.continuousOn fun _ h ↦ h))
  refine ⟨locallyClosedAt_preimage_of_continuousOn hnhds hcont hclosed, ?_⟩
  rw [tangentCone_preimage hP, regularTangentCone_preimage hP _ (show P p ∈ epigraph g by
    rw [hpe]; exact hx.le), htan]

/-- **Exercise 8.20(b).** Adding a smooth real-valued function preserves
and reflects subdifferential regularity. Smoothness on a neighborhood of
the base point suffices. -/
theorem isSubdifferentiallyRegularAt_add_smooth_iff {g : E → EReal} {k : E → ℝ} {x : E} {U : Set E}
    (hU : U ∈ 𝓝 x) (hk : ContDiffOn ℝ 1 k U) :
    IsSubdifferentiallyRegularAt (fun y ↦ g y + (k y : EReal)) x ↔ IsSubdifferentiallyRegularAt g x := by
  have hd := (hk.contDiffAt hU).hasStrictFDerivAt one_ne_zero
  constructor
  · intro h
    have h' := regular_add_of_strictFDerivAt hU hk.continuousOn.neg hd.neg h
    simpa only [EReal.coe_neg, add_assoc, ← EReal.coe_neg, ← EReal.coe_add, add_neg_cancel,
      EReal.coe_zero, add_zero] using h'
  · exact regular_add_of_strictFDerivAt hU hk.continuousOn hd

/-- **Exercise 8.20(a).** At every point of an open smoothness set a smooth
function is regular, and both subderivatives are its differential. -/
theorem regularSubderivatives_of_smooth {k : E → ℝ} {x : E} {U : Set E} (hU : U ∈ 𝓝 x)
    (hk : ContDiffOn ℝ 1 k U) : IsSubdifferentiallyRegularAt (fun y ↦ (k y : EReal)) x ∧
      subderivative (fun y ↦ (k y : EReal)) x = (fun w ↦ (fderiv ℝ k x w : EReal)) ∧
      regularSubderivative (fun y ↦ (k y : EReal)) x = (fun w ↦ (fderiv ℝ k x w : EReal)) := by
  have hl : IsLocallyLscAt (fun _ : E ↦ (0 : EReal)) x := by
    refine ⟨by simp, by simp, 1, one_pos, fun a _ ↦ ?_⟩
    by_cases ha : (0 : EReal) ≤ a <;> simp [ha, isClosed_closedBall]
  have hconv : Convex ℝ (epigraph (fun _ : E ↦ (0 : EReal))) := by
    change Convex ℝ {p : E × ℝ | (0 : EReal) ≤ (p.2 : EReal)}
    simpa only [EReal.coe_nonneg] using (convex_Ici (0 : ℝ)).linear_preimage (LinearMap.snd ℝ E ℝ)
  have hreg0 := (isSubdifferentiallyRegularAt_of_convex hconv hl).1
  have hreg : IsSubdifferentiallyRegularAt (fun y ↦ (k y : EReal)) x := by
    simpa only [zero_add] using (isSubdifferentiallyRegularAt_add_smooth_iff (g := fun _ ↦ 0) hU hk).mpr hreg0
  have hd := (hk.contDiffAt hU).hasStrictFDerivAt one_ne_zero
  have hdif (w : E) : HasSemiderivative (fun y ↦ (k y : EReal)) x w ((fderiv ℝ k x w : ℝ) : EReal) := by
    exact ⟨EReal.coe_ne_bot _, EReal.coe_ne_top _, tendsto_of_isLittleO (f := fun y ↦ (k y : EReal)) (x := x) (g := fderiv ℝ k x) rfl (fderiv ℝ k x).continuous
      (fun a _ v ↦ by simp) (Eventually.of_forall fun y ↦ ⟨EReal.coe_ne_bot _, EReal.coe_ne_top _⟩)
      (by simpa only [EReal.toReal_coe] using hd.hasFDerivAt.isLittleO) w⟩
  have hsub := funext fun w ↦ (hdif w).subderivative_eq
  exact ⟨hreg, hsub, ((isSubdifferentiallyRegularAt_iff_subderivative_eq_regularSubderivative.mp hreg).2).symm.trans hsub⟩

/-- The gradient-inner-product form of the two identities in 8.20(a). -/
theorem smooth_subderivatives_eq_inner_gradient {k : E → ℝ} {x : E} {U : Set E} (hU : U ∈ 𝓝 x)
    (hk : ContDiffOn ℝ 1 k U) (w : E) :
    subderivative (fun y ↦ (k y : EReal)) x w = (⟪gradient k x,w⟫_ℝ : EReal) ∧
      regularSubderivative (fun y ↦ (k y : EReal)) x w = (⟪gradient k x,w⟫_ℝ : EReal) := by
  obtain ⟨-, hs, hr⟩ := regularSubderivatives_of_smooth hU hk
  rw [inner_gradient_left ((hk.contDiffAt hU).differentiableAt one_ne_zero), hs, hr]
  exact ⟨rfl, rfl⟩

end RW
