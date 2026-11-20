/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Amenability of domain closures
-/
import RockafellarWets.Chapter10.ConvexDomainDensity
import RockafellarWets.Chapter10.AmenabilityGerms
import RockafellarWets.Chapter10.AmenableHorizonDomain

open Set Filter Topology

noncomputable section
namespace RW
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Taking closure preserves equality of set germs. -/
theorem closure_eventuallyEq_of_eventuallyEq {C D : Set E} {x : E} (he : C =ᶠ[𝓝 x] D) :
    closure C =ᶠ[𝓝 x] (show Set E from closure D) := by
  obtain ⟨U,hU,hUo,hxU⟩ := mem_nhds_iff.mp he
  have hint : U ∩ C = U ∩ D := by
    ext y
    constructor
    · rintro ⟨hy,hc⟩; exact ⟨hy,(Iff.of_eq (hU hy)).mp hc⟩
    · rintro ⟨hy,hd⟩; exact ⟨hy,(Iff.of_eq (hU hy)).mpr hd⟩
  filter_upwards [hUo.mem_nhds hxU] with y hy
  apply propext
  constructor
  · intro hc
    have hh := hUo.inter_closure ⟨hy,hc⟩
    rw [hint] at hh
    exact closure_mono inter_subset_right hh
  · intro hd
    have hh := hUo.inter_closure ⟨hy,hd⟩
    rw [← hint] at hh
    exact closure_mono inter_subset_right hh

/-- The closure of the domain agrees locally with the inverse image of the
closed outer domain in the original representation. -/
theorem AmenableFunctionModel.closure_domain_eventuallyEq {f : E → EReal} {x : E} {r : ℕ} {full : Bool}
    (M : AmenableFunctionModel f x r full) (hr : 1 ≤ r) :
    closure (effectiveDomain f) =ᶠ[𝓝 x]
      (show Set E from M.inner ⁻¹' closure (effectiveDomain M.outer)) := by
  obtain ⟨G,hG,he⟩ := exists_contDiff_eventuallyEq_of_contDiffOn M.isOpen M.mem M.smooth
  have hG1 : ContDiff ℝ 1 G := hG.of_le (by exact_mod_cast hr)
  have hQ : ∀v ∈ normalCone (closure (effectiveDomain M.outer)) (G x),
      (fderiv ℝ G x).adjoint v = 0 → v = 0 := by
    simpa only [he.self_of_nhds,he.fderiv_eq] using M.qualification
  have hqual := normalKernelQualification_eventually isClosed_closure hG.continuous.continuousAt
    (ContinuousLinearMap.adjoint.continuous.continuousAt.comp
      (hG1.continuous_fderiv (by norm_num)).continuousAt) hQ
  have hinv : (G ⁻¹' closure (effectiveDomain M.outer)) =ᶠ[𝓝 x]
      (show Set E from closure (G ⁻¹' effectiveDomain M.outer)) := by
    filter_upwards [hqual] with y hy
    apply propext
    constructor
    · intro hD
      exact mem_closure_preimage_of_convex_qualification
        (convex_effectiveDomain_of_convex_epigraph M.convex) hG1 hD hy
    · intro hD
      have hsub : G ⁻¹' effectiveDomain M.outer ⊆ G ⁻¹' closure (effectiveDomain M.outer) :=
        fun z hz ↦ subset_closure hz
      exact closure_minimal hsub (isClosed_closure.preimage hG.continuous) hD
  have hdom : (G ⁻¹' effectiveDomain M.outer) =ᶠ[𝓝 x] (show Set E from effectiveDomain f) := by
    filter_upwards [he,M.isOpen.mem_nhds M.mem] with y hy hyV
    apply propext
    change M.outer (G y) < ⊤ ↔ f y < ⊤
    rw [hy,← M.eqOn y hyV]
  have hh := hinv.trans (closure_eventuallyEq_of_eventuallyEq hdom)
  filter_upwards [hh,he] with y hy hGy
  change (y ∈ closure (effectiveDomain f)) = (M.inner y ∈ closure (effectiveDomain M.outer))
  change (G y ∈ closure (effectiveDomain M.outer)) = (y ∈ closure (effectiveDomain f)) at hy
  rw [hGy] at hy
  exact hy.symm

/-- The domain-closure model retains the original inner map and target. -/
def AmenableFunctionModel.closure_domain {f : E → EReal} {x : E} {r : ℕ} {full : Bool}
    (M : AmenableFunctionModel f x r full) (hr : 1 ≤ r) :
    AmenableSetModel (closure (effectiveDomain f)) x r full := by
  let h := mem_nhds_iff.mp (M.closure_domain_eventuallyEq hr)
  let U := Classical.choose h
  have hU := Classical.choose_spec h
  exact {
    Target := M.Target
    constraint := closure (effectiveDomain M.outer)
    inner := M.inner
    neighborhood := M.neighborhood ∩ U
    isOpen := M.isOpen.inter hU.2.1
    mem := ⟨M.mem,hU.2.2⟩
    base := subset_closure (lt_top_iff_ne_top.mpr M.finite.2)
    closed := isClosed_closure
    convex := (convex_effectiveDomain_of_convex_epigraph M.convex).closure
    smooth := M.smooth.mono inter_subset_left
    eqOn := fun y hy ↦ Iff.of_eq (hU.1 hy.2)
    qualification := M.qualification
    polyhedral := by
      intro hfull
      rw [(M.plq hfull).isClosed_effectiveDomain.closure_eq]
      exact (M.plq hfull).isPolyhedral_effectiveDomain M.convex }

/-- At a finite amenable point, closing the domain leaves its normal cone unchanged. -/
theorem AmenableFunctionModel.normal_closure_domain_eq {f : E → EReal} {x : E} {r : ℕ} {full : Bool}
    (M : AmenableFunctionModel f x r full) (hr : 1 ≤ r) :
    normalCone (closure (effectiveDomain f)) x = normalCone (effectiveDomain f) x := by
  rw [← M.horizon_eq_normal_domain hr,(M.derivatives hr).2.1,
    ((M.closure_domain hr).cones hr).2.1]
  change (fderiv ℝ M.inner x).adjoint '' normalCone (closure (effectiveDomain M.outer)) (M.inner x) =
    (fderiv ℝ M.inner x).adjoint '' horizonSubdifferential M.outer (M.inner x)
  rw [horizonSubdifferential_eq_normalCone_closure_domain M.proper M.lsc M.convex
    (c := (f x).toReal) (by rw [← M.eqOn x M.mem]; exact (EReal.coe_toReal M.finite.2 M.finite.1).symm)]

theorem AmenableAt.normal_closure_domain_eq {f : E → EReal} {x : E} (h : AmenableAt f x) :
    normalCone (closure (effectiveDomain f)) x = normalCone (effectiveDomain f) x := by
  obtain ⟨M⟩ := h
  exact M.normal_closure_domain_eq le_rfl

/-- **Definition 10.23**, the closure of an amenable function's domain is amenable. -/
theorem AmenableAt.closure_domain {f : E → EReal} {x : E} (h : AmenableAt f x) :
    SetAmenableAt (closure (effectiveDomain f)) x := by
  obtain ⟨M⟩ := h
  exact ⟨M.closure_domain le_rfl⟩

/-- **Definition 10.23**, the same closure claim preserves strong amenability. -/
theorem StronglyAmenableAt.closure_domain {f : E → EReal} {x : E} (h : StronglyAmenableAt f x) :
    SetStronglyAmenableAt (closure (effectiveDomain f)) x := by
  obtain ⟨M⟩ := h
  exact ⟨M.closure_domain (by norm_num)⟩

end RW
end
