/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Regularity of amenable functions and sets
-/
import RockafellarWets.Chapter10.Amenability
import RockafellarWets.Chapter10.SmoothLocalExtension
import RockafellarWets.Chapter10.BasicChainRule
import RockafellarWets.Chapter10.SubgradientGerms
import RockafellarWets.Chapter8.ConvexSubgradients
import RockafellarWets.Chapter6.BoundaryNormals
import RockafellarWets.Chapter6.PolyhedralCones
import RockafellarWets.Chapter9.LocalizationDerivatives
import RockafellarWets.Chapter9.LipschitzSubgradientLimits

open Set Filter Topology
open scoped Pointwise

namespace RW
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Clarke regularity depends only on the local set germ. -/
theorem IsClarkeRegularAt.congr_nhds {C D : Set E} {x : E}
    (h : IsClarkeRegularAt C x) (he : C =ᶠ[𝓝 x] D) : IsClarkeRegularAt D x := by
  refine ⟨h.1.congr_nhds he,?_⟩
  rw [← normalCone_congr_nhds he,← regularNormalCone_congr_nhds he]
  exact h.2

/-- **Theorem 10.25(a)**, regularity of every amenable function. -/
theorem AmenableAt.isSubdifferentiallyRegularAt {f : E → EReal} {x : E}
    (h : AmenableAt f x) : IsSubdifferentiallyRegularAt f x := by
  obtain ⟨M⟩ := h
  obtain ⟨G,hG,he⟩ := exists_contDiff_eventuallyEq_of_contDiffOn M.isOpen M.mem M.smooth
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
  apply (hreg.comp_of_horizon_qualification hG M.lsc hQ).congr_nhds
  filter_upwards [he,M.isOpen.mem_nhds M.mem] with y hy hyV
  change M.outer (G y) = f y
  rw [hy,← M.eqOn y hyV]

/-- The local representation of an amenable set yields the exact normal
and tangent formulas, as well as regularity. -/
theorem AmenableSetModel.cones {C : Set E} {x : E} {r : ℕ} {full : Bool}
    (M : AmenableSetModel C x r full) (hr : 1 ≤ r) :
    IsClarkeRegularAt C x ∧
      normalCone C x = (fderiv ℝ M.inner x).adjoint '' normalCone M.constraint (M.inner x) ∧
      tangentCone C x = (fderiv ℝ M.inner x) ⁻¹' tangentCone M.constraint (M.inner x) := by
  have hs : ContDiffOn ℝ 1 M.inner M.neighborhood := M.smooth.of_le (by exact_mod_cast hr)
  obtain ⟨G,hG,he⟩ := exists_contDiff_eventuallyEq_of_contDiffOn M.isOpen M.mem hs
  have hepoint := he.self_of_nhds
  have hbase : G x ∈ M.constraint := by rw [hepoint]; exact (M.eqOn x M.mem).mp M.base
  have hQ : NormalConstraintQualification univ M.constraint (fderiv ℝ G x) x (G x) := by
    intro v hv hzero
    rw [normalCone_univ,mem_singleton_iff,neg_eq_zero] at hzero
    rw [hepoint] at hv
    rw [he.fderiv_eq] at hzero
    exact M.qualification v hv hzero
  have hregD := isClarkeRegularAt_of_convex M.convex hbase (RW.IsClosed.isLocallyClosedAt M.closed _)
  have hnormal := clarkeRegularity_constraints isClosed_univ M.closed hG
    (show x ∈ univ ∩ G ⁻¹' M.constraint from ⟨mem_univ _,hbase⟩) hQ (isClarkeRegularAt_univ x) hregD
  have htangent := (tangentCone_constraints_of_isClarkeRegularAt isClosed_univ M.closed hG
    (show x ∈ univ ∩ G ⁻¹' M.constraint from ⟨mem_univ _,hbase⟩) hQ (isClarkeRegularAt_univ x) hregD).1
  have hgerm : (show Set E from univ ∩ G ⁻¹' M.constraint) =ᶠ[𝓝 x] C := by
    filter_upwards [he,M.isOpen.mem_nhds M.mem] with y hy hyV
    apply propext
    change (y ∈ (univ : Set E) ∧ G y ∈ M.constraint) ↔ y ∈ C
    simpa only [mem_univ,true_and,hy] using (M.eqOn y hyV).symm
  refine ⟨hnormal.1.congr_nhds hgerm,?_,?_⟩
  · rw [← normalCone_congr_nhds hgerm,hnormal.2,he.fderiv_eq,hepoint,normalCone_univ]
    simp
  · rw [← tangentCone_congr_nhds hgerm,htangent,he.fderiv_eq,hepoint,tangentCone_univ,univ_inter]

/-- **Theorem 10.25(c)**: amenable sets are Clarke regular. -/
theorem SetAmenableAt.isClarkeRegularAt {C : Set E} {x : E}
    (h : SetAmenableAt C x) : IsClarkeRegularAt C x := by
  obtain ⟨M⟩ := h
  exact (M.cones le_rfl).1

/-- **Theorem 10.25(c)**: the normal and tangent cones of a fully amenable
set are polyhedral. Local closedness is already included in regularity. -/
theorem SetFullyAmenableAt.polyhedral_cones {C : Set E} {x : E}
    (h : SetFullyAmenableAt C x) :
    IsLocallyClosedAt C x ∧ IsPolyhedral (normalCone C x) ∧ IsPolyhedral (tangentCone C x) := by
  obtain ⟨M⟩ := h
  have hcone := M.cones (by norm_num)
  have hbase := (M.eqOn x M.mem).mp M.base
  refine ⟨hcone.1.1,?_,?_⟩
  · rw [hcone.2.1]
    exact ((M.polyhedral rfl).isPolyhedral_normalCone hbase).linear_image _
  · rw [hcone.2.2]
    exact ((M.polyhedral rfl).isPolyhedral_tangentCone hbase).continuousLinear_preimage _

end RW
