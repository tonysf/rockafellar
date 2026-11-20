/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Exact calculus in an amenable representation
-/
import RockafellarWets.Chapter10.AmenableRegularity
import RockafellarWets.Chapter10.BasicChainSubderivatives
import RockafellarWets.Chapter10.PLQCalculus
import RockafellarWets.Chapter10.FiniteInfimumSubderivatives

open Set Filter Topology
open scoped InnerProductSpace

namespace RW
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- An amenable representation has exact first-order calculus, including
for a locally defined smooth inner map. -/
theorem AmenableFunctionModel.derivatives {f : E → EReal} {x : E} {r : ℕ} {full : Bool}
    (M : AmenableFunctionModel f x r full) (hr : 1 ≤ r) :
    subdifferential f x = (fderiv ℝ M.inner x).adjoint '' subdifferential M.outer (M.inner x) ∧
    horizonSubdifferential f x = (fderiv ℝ M.inner x).adjoint '' horizonSubdifferential M.outer (M.inner x) ∧
    (∀w, subderivative f x w = subderivative M.outer (M.inner x) (fderiv ℝ M.inner x w)) := by
  have hs : ContDiffOn ℝ 1 M.inner M.neighborhood := M.smooth.of_le (by exact_mod_cast hr)
  obtain ⟨G,hG,he⟩ := exists_contDiff_eventuallyEq_of_contDiffOn M.isOpen M.mem hs
  have hepoint := he.self_of_nhds
  have hval : M.outer (G x) = ((f x).toReal : EReal) := by
    rw [hepoint,← M.eqOn x M.mem]
    exact (EReal.coe_toReal M.finite.2 M.finite.1).symm
  have hlocal := locallyLscAt_of_lowerSemicontinuous_finite M.lsc hval
  have hreg := (isSubdifferentiallyRegularAt_of_convex M.convex hlocal).1
  have hQ : ∀ y ∈ horizonSubdifferential M.outer (G x), (fderiv ℝ G x).adjoint y = 0 → y = 0 := by
    intro y hy hzero
    have hn := normalCone_subset_closure (effectiveDomain M.outer) (G x)
      (horizonSubdifferential_subset_normalCone_domain M.convex M.proper hval hy)
    rw [hepoint] at hn
    rw [he.fderiv_eq] at hzero
    exact M.qualification y hn hzero
  have hgerm : M.outer ∘ G =ᶠ[𝓝 x] f := by
    filter_upwards [he,M.isOpen.mem_nhds M.mem] with y hy hyV
    change M.outer (G y) = f y
    rw [hy,← M.eqOn y hyV]
  have hlcomp := (hreg.comp_of_horizon_qualification hG M.lsc hQ).isLocallyLscAt
  refine ⟨?_,?_,?_⟩
  · rw [← subdifferential_congr_nhds_of_finite (f := M.outer ∘ G) hval hgerm,
      subdifferential_comp_eq_of_regular hG M.lsc hreg hQ,he.fderiv_eq,hepoint]
  · rw [← horizonSubdifferential_congr_nhds_of_locallyLsc (f := M.outer ∘ G) hval hlcomp
      (hlcomp.congr_nhds hgerm) hgerm,
      horizonSubdifferential_comp_eq_of_regular hG M.lsc hreg hQ,he.fderiv_eq,hepoint]
  · intro w
    rw [← subderivative_congr_nhds hgerm w,subderivative_comp_eq_of_regular hG M.lsc hreg hQ,
      he.fderiv_eq,hepoint]

/-- Piecewise linear functions remain piecewise linear under arbitrary
linear composition. -/
theorem IsPiecewiseLinear.compLinear {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {g : F → EReal}
    (hg : IsPiecewiseLinear g) (A : E →L[ℝ] F) :
    IsPiecewiseLinear (fun x ↦ g (A x)) := by
  obtain ⟨m,C,a,b,hC,hdom,hg⟩ := hg
  refine ⟨m,fun i ↦ A ⁻¹' C i,fun i ↦ A.adjoint (a i),b,
    fun i ↦ (hC i).continuousLinear_preimage A,?_,?_⟩
  · ext x
    change A x ∈ effectiveDomain g ↔ _
    rw [hdom]
    simp
  · intro i x hx
    change g (A x) = _
    rw [hg i (A x) hx,ContinuousLinearMap.adjoint_inner_left]

/-- **Theorem 10.25(a)**: the fully amenable case has a locally closed
domain, nonempty polyhedral subgradients, polyhedral horizon subgradients,
and a piecewise linear subderivative. -/
theorem FullyAmenableAt.polyhedral_properties {f : E → EReal} {x : E}
    (h : FullyAmenableAt f x) :
    IsLocallyClosedAt (effectiveDomain f) x ∧
    (subdifferential f x).Nonempty ∧ IsPolyhedral (subdifferential f x) ∧
    IsPolyhedral (horizonSubdifferential f x) ∧ IsPiecewiseLinear (subderivative f x) := by
  obtain ⟨M⟩ := h
  have hp := M.plq rfl
  have hx : M.inner x ∈ effectiveDomain M.outer := by
    change M.outer (M.inner x) < ⊤
    rw [← M.eqOn x M.mem]
    exact lt_top_iff_ne_top.mpr M.finite.2
  have hsub := hp.convex_subgradient_properties M.convex hx
  have hform := M.derivatives (by norm_num)
  refine ⟨?_,?_,?_,?_,?_⟩
  · obtain ⟨G,hG,he⟩ := exists_contDiff_eventuallyEq_of_contDiffOn M.isOpen M.mem M.smooth
    have heD : G ⁻¹' effectiveDomain M.outer =ᶠ[𝓝 x] effectiveDomain f := by
      filter_upwards [he,M.isOpen.mem_nhds M.mem] with y hy hyV
      apply propext
      change M.outer (G y) < ⊤ ↔ f y < ⊤
      rw [hy,← M.eqOn y hyV]
    exact (RW.IsClosed.isLocallyClosedAt (hp.isClosed_effectiveDomain.preimage hG.continuous) x).congr_nhds heD
  · rw [hform.1]
    exact hsub.1.image _
  · rw [hform.1]
    exact hsub.2.1.linear_image _
  · rw [hform.2.1]
    exact hsub.2.2.linear_image _
  · have he : subderivative f x = fun w ↦ subderivative M.outer (M.inner x) (fderiv ℝ M.inner x w) :=
      funext hform.2.2
    rw [he]
    exact (hp.subderivative_piecewiseLinear hx).1.compLinear _

end RW
