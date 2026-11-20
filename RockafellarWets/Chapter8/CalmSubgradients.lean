/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: The sharp calmness modulus as a subgradient norm
-/

import RockafellarWets.Chapter8.Calmness
import RockafellarWets.Chapter8.SubderivativeRegularityCriterion
import RockafellarWets.Chapter6.NormalsToTangentCones
import RockafellarWets.Chapter6.SmoothGradientWitness

open Filter Set Topology Metric
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {x : E}

omit [FiniteDimensional ℝ E] in
/-- The Euclidean epigraph version of the subderivative–tangent identity. -/
theorem euclideanEpigraph_subderivative {c : ℝ} (hx : f x = c) :
    euclideanEpigraph (subderivative f x) =
      tangentCone (euclideanEpigraph f) (WithLp.toLp 2 (x,c)) := by
  change (l2ProdEquiv E) ⁻¹' epigraph (subderivative f x) = tangentCone ((l2ProdEquiv E) ⁻¹' epigraph f) _
  rw [tangentCone_preimage_continuousLinearEquiv,l2ProdEquiv_toLp,epigraph_subderivative_eq_tangentCone hx]

/-- A subgradient of the subderivative at a finite direction gives a subgradient
of the original function. The finite value at the chosen direction is essential. -/
theorem subdifferential_subderivative_subset_of_localLsc (hl : IsLocallyLscAt f x) {w : E} {b : ℝ}
    (hw : subderivative f x w = b) :
    subdifferential (subderivative f x) w ⊆ subdifferential f x := by
  let c := (f x).toReal
  have hx : f x = (c : EReal) := (EReal.coe_toReal hl.2.1 hl.1).symm
  have he : WithLp.toLp 2 (x,c) ∈ euclideanEpigraph f := hx.le
  have hc : IsLocallyClosedAt (euclideanEpigraph f) (WithLp.toLp 2 (x,c)) :=
    IsLocallyClosedAt.preimage_continuousLinearEquiv (l2ProdEquiv E) hl.isLocallyClosedAt_epigraph
  intro v hv
  rw [mem_subdifferential_iff_epigraph_normal hw,euclideanEpigraph_subderivative hx] at hv
  exact (mem_subdifferential_iff_epigraph_normal hx).2 (normalCone_tangentCone_subset he hc _ hv)

/-- **Proposition 8.32.** A locally lower semicontinuous function calm from below
has a limiting subgradient whose norm is precisely its sharp lower modulus. -/
theorem IsCalmFromBelowAt.exists_subgradient_norm_eq (h : IsCalmFromBelowAt f x) (hl : IsLocallyLscAt f x) :
    ∃ v ∈ subdifferential f x, ‖v‖ = calmFromBelowModulus f x := by
  letI := FiniteDimensional.complete ℝ E
  let k := calmFromBelowModulus f x
  have hk : 0 ≤ k := h.modulus_nonneg
  have hx := (EReal.coe_toReal hl.2.1 hl.1).symm
  have hbound (w : E) : ((-k*‖w‖ : ℝ) : EReal) ≤ subderivative f x w := h.sharp_le_subderivative w
  rcases eq_or_lt_of_le hk with hz | hkpos
  · refine ⟨0,regularSubdifferential_subset_subdifferential _ _ ((mem_regularSubdifferential_iff_inner_le_subderivative hx).2 ?_),by simpa only [norm_zero] using hz⟩
    intro w
    simpa only [← hz,neg_zero,zero_mul,inner_zero_left] using hbound w
  · obtain ⟨u,hu,hval,_⟩ := h.exists_unitBall_subderivative_minimizer
    have hkval : subderivative f x u = ((-k : ℝ) : EReal) := hval
    have hlen : ‖u‖ = 1 := by
      have hle := EReal.coe_le_coe_iff.1 ((hbound u).trans_eq hkval)
      exact le_antisymm (mem_closedBall_zero_iff.1 hu) (by nlinarith)
    have hune : u ≠ 0 := by intro he; simp [he] at hlen
    have hgrad : HasGradientAt (fun y : E ↦ -k*‖y‖) ((-k) • u) u := by
      apply hasGradientAt_iff_hasFDerivAt.2
      have hh := (hasFDerivAt_norm_of_ne_zero hune).const_smul (-k)
      apply hh.congr_fderiv
      ext z
      simp [hlen]
    have hreg := (mem_regularSubdifferential_iff_exists_hasGradientAt hkval).2
      ⟨fun y ↦ -k*‖y‖, Eventually.of_forall hbound, by simp [hlen], hgrad⟩
    exact ⟨(-k) • u,subdifferential_subderivative_subset_of_localLsc hl hkval
      (regularSubdifferential_subset_subdifferential _ _ hreg),by simp [norm_smul,hlen,abs_of_nonneg hk,k]⟩

/-- **Proposition 8.32.** At a regular point, calmness from below is equivalent
to nonemptiness of the limiting subdifferential. -/
theorem IsSubdifferentiallyRegularAt.isCalmFromBelowAt_iff (h : IsSubdifferentiallyRegularAt f x) :
    IsCalmFromBelowAt f x ↔ (subdifferential f x).Nonempty := by
  rw [isCalmFromBelowAt_iff_subderivative_zero (EReal.coe_toReal h.2.1 h.1).symm,
    h.subdifferential_nonempty_iff]
  exact ⟨fun h0 ↦ h0 ▸ EReal.zero_ne_bot, h.subderivative_properties.2.2.1.zero_eq_zero_or_bot.resolve_right⟩

/-- **Proposition 8.32.** The sharp lower calmness modulus of a regular function
is its distance to the limiting subgradient set. -/
theorem IsSubdifferentiallyRegularAt.calmFromBelowModulus_eq_infDist
    (h : IsSubdifferentiallyRegularAt f x) (hc : IsCalmFromBelowAt f x) :
    calmFromBelowModulus f x = infDist 0 (subdifferential f x) := by
  obtain ⟨v,hv,hvn⟩ := hc.exists_subgradient_norm_eq h.isLocallyLscAt
  obtain ⟨u,hu,hval,_⟩ := hc.exists_unitBall_subderivative_minimizer
  refine le_antisymm ((le_infDist ⟨v,hv⟩).2 ?_) ?_
  · intro z hz
    rw [h.subdifferential_eq_linearMinorantSet] at hz
    have hle := EReal.coe_le_coe_iff.1 ((hz u).trans_eq hval)
    have hlower := (neg_le_abs ⟪z,u⟫_ℝ).trans (abs_real_inner_le_norm z u)
    rw [dist_zero_left]
    nlinarith [mul_nonneg (norm_nonneg z) (sub_nonneg.2 (mem_closedBall_zero_iff.1 hu))]
  · simpa only [dist_zero_left,hvn] using infDist_le_dist_of_mem (x := (0:E)) hv

end RW
