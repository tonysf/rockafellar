/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Local normal graphs and nearby amenable preimage calculus
-/
import RockafellarWets.Chapter10.AmenablePreimages

open Set Filter Topology

namespace RW
variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Locally closed sets have the same nearby normal mapping as a closed set. -/
theorem IsLocallyClosedAt.exists_closed_normalCone_eventuallyEq {C : Set F} {x : F}
    (h : IsLocallyClosedAt C x) :
    ∃D : Set F, IsClosed D ∧ normalCone C =ᶠ[𝓝 x] normalCone D := by
  obtain ⟨V,hV,_,hCV⟩ := h
  have he : C =ᶠ[𝓝 x] (show Set F from C ∩ V) := by
    filter_upwards [hV] with y hy
    exact propext ⟨fun hc ↦ ⟨hc,hy⟩,fun hc ↦ hc.1⟩
  refine ⟨C ∩ V,hCV,?_⟩
  filter_upwards [he.eventuallyEq_nhds] with y hy
  exact normalCone_congr_nhds hy

/-- The normal-kernel qualification is local in the constraint set. -/
theorem normalKernelQualification_eventually_of_locallyClosed {D : Set F}
    {f : E → F} {A : E → F →L[ℝ] G} {x : E}
    (hD : IsLocallyClosedAt D (f x)) (hf : ContinuousAt f x) (hA : ContinuousAt A x)
    (hQ : ∀v ∈ normalCone D (f x), A x v = 0 → v = 0) :
    ∀ᶠ y in 𝓝 x, ∀v ∈ normalCone D (f y), A y v = 0 → v = 0 := by
  obtain ⟨D',hD',he⟩ := hD.exists_closed_normalCone_eventuallyEq
  have hQ' : ∀v ∈ normalCone D' (f x), A x v = 0 → v = 0 := by
    simpa only [← he.self_of_nhds] using hQ
  filter_upwards [normalKernelQualification_eventually hD' hf hA hQ',hf.tendsto.eventually he] with y hy heq
  simpa only [heq] using hy

/-- **Exercise 10.25(d)**: near an amenable point the normal graph is
closed relative to the open neighborhood times the normal-vector space. -/
theorem SetAmenableAt.normalGraph_closed_relative {C : Set E} {x : E}
    (h : SetAmenableAt C x) :
    ∃V : Set E, IsOpen V ∧ x ∈ V ∧
      IsClosed {p : V × E | p.2 ∈ normalCone C p.1} := by
  obtain ⟨D,hD,he⟩ := h.isClarkeRegularAt.1.exists_closed_normalCone_eventuallyEq
  obtain ⟨V,hVsub,hVo,hxV⟩ := mem_nhds_iff.mp he
  refine ⟨V,hVo,hxV,?_⟩
  have hclosed : IsClosed (svGraph (normalCone D)) := by rw [svGraph_normalCone hD]; exact isClosed_closure
  have heq : {p : V × E | p.2 ∈ normalCone C p.1} =
      (fun p : V × E ↦ ((p.1:E),p.2)) ⁻¹' svGraph (normalCone D) := by
    ext p
    change p.2 ∈ normalCone C p.1 ↔ p.2 ∈ normalCone D p.1
    rw [hVsub p.1.property]
  rw [heq]
  exact hclosed.preimage (by fun_prop)

end RW

namespace RW
universe u
variable {E F : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- **Exercise 10.26(d)**: the normal and tangent formulas hold throughout
a neighborhood on the inverse-image set. -/
theorem SetAmenableAt.preimage_cones_eventually {D : Set F} {f : E → F} {x : E}
    (hD : SetAmenableAt D (f x)) (hf : ContDiff ℝ 1 f)
    (hQ : ∀v ∈ normalCone D (f x), (fderiv ℝ f x).adjoint v = 0 → v = 0) :
    ∀ᶠ y in 𝓝 x, y ∈ f ⁻¹' D →
      normalCone (f ⁻¹' D) y = (fderiv ℝ f y).adjoint '' normalCone D (f y) ∧
      tangentCone (f ⁻¹' D) y = (fderiv ℝ f y) ⁻¹' tangentCone D (f y) := by
  have hnear := hf.continuous.continuousAt.tendsto.eventually hD.eventually
  have hqual := normalKernelQualification_eventually_of_locallyClosed hD.isClarkeRegularAt.1
    hf.continuous.continuousAt
    (ContinuousLinearMap.adjoint.continuous.continuousAt.comp (hf.continuous_fderiv (by norm_num)).continuousAt) hQ
  filter_upwards [hnear,hqual] with y hy hqy hDy
  exact (hy hDy).preimage_cones hf hqy

end RW
