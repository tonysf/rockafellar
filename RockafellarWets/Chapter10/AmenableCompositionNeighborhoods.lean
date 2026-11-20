/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Nearby calculus for amenable composition
-/
import RockafellarWets.Chapter10.AmenableDomainNormals

open Set Filter Topology

noncomputable section
namespace RW
universe u
variable {E F : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The actual qualification of a fixed model holds at all nearby points,
including points where the represented function is infinite. -/
theorem AmenableFunctionModel.qualification_eventually {f : E → EReal} {x : E} {r : ℕ} {full : Bool}
    (M : AmenableFunctionModel f x r full) (hr : 1 ≤ r) :
    ∀ᶠ y in 𝓝 x, ∀v ∈ normalCone (closure (effectiveDomain M.outer)) (M.inner y),
      (fderiv ℝ M.inner y).adjoint v = 0 → v = 0 := by
  have hcont := M.smooth.continuousOn.continuousAt (M.isOpen.mem_nhds M.mem)
  have hder := (M.smooth.continuousOn_fderiv_of_isOpen M.isOpen (by exact_mod_cast hr)).continuousAt
    (M.isOpen.mem_nhds M.mem)
  exact normalKernelQualification_eventually isClosed_closure hcont
    (ContinuousLinearMap.adjoint.continuous.continuousAt.comp hder) M.qualification

/-- The local model proves the chain formulas uniformly nearby without a
global lower-semicontinuity assumption on the outer represented function. -/
theorem AmenableFunctionModel.comp_derivatives_eventually
    {g : F → EReal} {G : E → F} {x : E} {r : ℕ} {full : Bool}
    (M : AmenableFunctionModel g (G x) r full) (hr : 1 ≤ r) (hG : ContDiff ℝ r G)
    (hQ : ∀v ∈ horizonSubdifferential g (G x), (fderiv ℝ G x).adjoint v = 0 → v = 0) :
    ∀ᶠ y in 𝓝 x, y ∈ effectiveDomain (g ∘ G) →
      subdifferential (g ∘ G) y = (fderiv ℝ G y).adjoint '' subdifferential g (G y) ∧
      (∀w, subderivative (g ∘ G) y w = subderivative g (G y) (fderiv ℝ G y w)) := by
  let L := M.comp hr hG hQ
  have hM := hG.continuous.continuousAt.tendsto.eventually (M.qualification_eventually hr)
  have hL := L.qualification_eventually hr
  have hV := hG.continuous.continuousAt.tendsto.eventually (M.isOpen.mem_nhds M.mem)
  filter_upwards [hM,hL,hV] with y hyM hyL hyV hyDom
  have hyfinite : g (G y) ≠ ⊥ ∧ g (G y) ≠ ⊤ := by
    refine ⟨?_,ne_of_lt hyDom⟩
    rw [M.eqOn (G y) hyV]
    exact (M.proper.2 _).ne'
  let N : AmenableFunctionModel g (G y) r full := { M with mem := hyV, finite := hyfinite, qualification := hyM }
  have hQy : ∀v ∈ horizonSubdifferential g (G y), (fderiv ℝ G y).adjoint v = 0 → v = 0 := by
    intro v hv hz
    rw [(N.derivatives hr).2.1] at hv
    obtain ⟨w,hw,rfl⟩ := hv
    have hval : M.outer (M.inner (G y)) = ((g (G y)).toReal:EReal) := by
      rw [← M.eqOn (G y) hyV]
      exact (EReal.coe_toReal hyfinite.2 hyfinite.1).symm
    have hwN : w ∈ normalCone (closure (effectiveDomain M.outer)) (M.inner (G y)) := by
      rwa [← horizonSubdifferential_eq_normalCone_closure_domain M.proper M.lsc M.convex hval]
    have hmd := ((M.smooth (G y) hyV).contDiffAt (M.isOpen.mem_nhds hyV)).differentiableAt
      (by exact_mod_cast (show r ≠ 0 by omega))
    have hgd := hG.differentiable (by exact_mod_cast (show r ≠ 0 by omega)) y
    have hw0 : w = 0 := by
      apply hyL w hwN
      change (fderiv ℝ (M.inner ∘ G) y).adjoint w = 0
      rw [fderiv_comp y hmd hgd,ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.comp_apply]
      exact hz
    simp [hw0]
  exact N.comp_derivatives hr hG hQy

/-- **Exercise 10.26(b)**, amenability under the printed domain-normal qualification. -/
theorem AmenableAt.comp {g : F → EReal} {G : E → F} {x : E}
    (hg : AmenableAt g (G x)) (hG : ContDiff ℝ 1 G)
    (hQ : ∀v ∈ normalCone (effectiveDomain g) (G x), (fderiv ℝ G x).adjoint v = 0 → v = 0) :
    AmenableAt (g ∘ G) x := by
  have hH := fun v hv ↦ hQ v (hg.horizon_subset_normal_domain hv)
  obtain ⟨M⟩ := hg
  exact ⟨M.comp le_rfl hG hH⟩

/-- **Exercise 10.26(b)**, preservation of strong amenability under C² maps. -/
theorem StronglyAmenableAt.comp {g : F → EReal} {G : E → F} {x : E}
    (hg : StronglyAmenableAt g (G x)) (hG : ContDiff ℝ 2 G)
    (hQ : ∀v ∈ normalCone (effectiveDomain g) (G x), (fderiv ℝ G x).adjoint v = 0 → v = 0) :
    StronglyAmenableAt (g ∘ G) x := by
  have hH := fun v hv ↦ hQ v (hg.amenableAt.horizon_subset_normal_domain hv)
  obtain ⟨M⟩ := hg
  exact ⟨M.comp (by norm_num) hG hH⟩

/-- **Exercise 10.26(b)**, the nearby subgradient and subderivative formulas. -/
theorem AmenableAt.comp_derivatives_eventually {g : F → EReal} {G : E → F} {x : E}
    (hg : AmenableAt g (G x)) (hG : ContDiff ℝ 1 G)
    (hQ : ∀v ∈ normalCone (effectiveDomain g) (G x), (fderiv ℝ G x).adjoint v = 0 → v = 0) :
    ∀ᶠ y in 𝓝 x, y ∈ effectiveDomain (g ∘ G) →
      subdifferential (g ∘ G) y = (fderiv ℝ G y).adjoint '' subdifferential g (G y) ∧
      (∀w, subderivative (g ∘ G) y w = subderivative g (G y) (fderiv ℝ G y w)) := by
  have hH := fun v hv ↦ hQ v (hg.horizon_subset_normal_domain hv)
  obtain ⟨M⟩ := hg
  exact M.comp_derivatives_eventually le_rfl hG hH

end RW
end
