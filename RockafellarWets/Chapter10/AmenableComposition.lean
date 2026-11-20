/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Qualified compositions of amenable functions
-/
import RockafellarWets.Chapter10.FullyAmenableDomains
import RockafellarWets.Chapter10.AmenableLocalGeometry

open Set Filter Topology

noncomputable section
namespace RW
universe u
variable {E F : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Convex horizon subgradients are normals to the closed domain at a finite point. -/
theorem horizonSubdifferential_eq_normalCone_closure_domain {g : F → EReal}
    (hp : IsProper g) (hl : LowerSemicontinuous g) (hc : Convex ℝ (epigraph g))
    {z : F} {c : ℝ} (hz : g z = c) :
    horizonSubdifferential g z = normalCone (closure (effectiveDomain g)) z := by
  have hzd : z ∈ effectiveDomain g := hz.trans_lt (EReal.coe_lt_top _)
  have hdc := convex_effectiveDomain_of_convex_epigraph hc
  rw [horizonSubdifferential_eq_normalCone_domain_of_locallyLsc hc hp
    (locallyLscAt_of_lowerSemicontinuous_finite hl hz) hz,
    normalCone_eq_regularNormalCone_of_convex hdc hzd,
    normalCone_eq_regularNormalCone_of_convex hdc.closure (subset_closure hzd),
    regularNormalCone_closure hzd]

/-- Composing an amenable model with a smooth map preserves all model
orders under the horizon-subgradient qualification. -/
def AmenableFunctionModel.comp {g : F → EReal} {G : E → F} {x : E} {r : ℕ} {full : Bool}
    (M : AmenableFunctionModel g (G x) r full) (hr : 1 ≤ r) (hG : ContDiff ℝ r G)
    (hQ : ∀v ∈ horizonSubdifferential g (G x), (fderiv ℝ G x).adjoint v = 0 → v = 0) :
    AmenableFunctionModel (g ∘ G) x r full where
  Target := M.Target
  outer := M.outer
  inner := M.inner ∘ G
  neighborhood := G ⁻¹' M.neighborhood
  isOpen := M.isOpen.preimage hG.continuous
  mem := M.mem
  finite := M.finite
  proper := M.proper
  lsc := M.lsc
  convex := M.convex
  smooth := M.smooth.comp hG.contDiffOn (fun _ hy ↦ hy)
  eqOn := fun y hy ↦ M.eqOn (G y) hy
  qualification := by
    intro v hv hz
    have hmd := ((M.smooth (G x) M.mem).contDiffAt (M.isOpen.mem_nhds M.mem)).differentiableAt
      (by exact_mod_cast (show r ≠ 0 by omega))
    have hgd := hG.differentiable (by exact_mod_cast (show r ≠ 0 by omega)) x
    rw [fderiv_comp x hmd hgd,ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.comp_apply] at hz
    have hval : M.outer (M.inner (G x)) = ((g (G x)).toReal:EReal) := by
      rw [← M.eqOn (G x) M.mem]
      exact (EReal.coe_toReal M.finite.2 M.finite.1).symm
    have hh : v ∈ horizonSubdifferential M.outer (M.inner (G x)) := by
      rwa [horizonSubdifferential_eq_normalCone_closure_domain M.proper M.lsc M.convex hval]
    have htarget : (fderiv ℝ M.inner (G x)).adjoint v ∈ horizonSubdifferential g (G x) := by
      rw [(M.derivatives hr).2.1]
      exact ⟨v,hh,rfl⟩
    exact M.qualification v hv (hQ _ htarget hz)
  plq := M.plq

/-- Exact chain formulas for the locally defined amenable outer function. -/
theorem AmenableFunctionModel.comp_derivatives {g : F → EReal} {G : E → F} {x : E} {r : ℕ} {full : Bool}
    (M : AmenableFunctionModel g (G x) r full) (hr : 1 ≤ r) (hG : ContDiff ℝ r G)
    (hQ : ∀v ∈ horizonSubdifferential g (G x), (fderiv ℝ G x).adjoint v = 0 → v = 0) :
    subdifferential (g ∘ G) x = (fderiv ℝ G x).adjoint '' subdifferential g (G x) ∧
    (∀w, subderivative (g ∘ G) x w = subderivative g (G x) (fderiv ℝ G x w)) := by
  have hmd := ((M.smooth (G x) M.mem).contDiffAt (M.isOpen.mem_nhds M.mem)).differentiableAt
    (by exact_mod_cast (show r ≠ 0 by omega))
  have hgd := hG.differentiable (by exact_mod_cast (show r ≠ 0 by omega)) x
  have hcomp : fderiv ℝ (M.comp hr hG hQ).inner x =
      (fderiv ℝ M.inner (G x)).comp (fderiv ℝ G x) := fderiv_comp x hmd hgd
  have hc := (M.comp hr hG hQ).derivatives hr
  have ho := M.derivatives hr
  constructor
  · rw [hc.1,ho.1,hcomp,ContinuousLinearMap.adjoint_comp,image_image]
    rfl
  · intro w
    rw [hc.2.2,ho.2.2,hcomp]
    rfl

/-- **Exercise 10.26(b)**, the fully amenable composition with the printed
normal-domain qualification. -/
theorem FullyAmenableAt.comp {g : F → EReal} {G : E → F} {x : E}
    (hg : FullyAmenableAt g (G x)) (hG : ContDiff ℝ 2 G)
    (hQ : ∀v ∈ normalCone (effectiveDomain g) (G x), (fderiv ℝ G x).adjoint v = 0 → v = 0) :
    FullyAmenableAt (g ∘ G) x := by
  have hH : ∀v ∈ horizonSubdifferential g (G x), (fderiv ℝ G x).adjoint v = 0 → v = 0 := by
    simpa only [hg.horizon_eq_normal_domain] using hQ
  obtain ⟨M⟩ := hg
  exact ⟨M.comp (by norm_num) hG hH⟩

/-- The fully amenable chain formulas hold at all nearby domain points. -/
theorem FullyAmenableAt.comp_derivatives_eventually {g : F → EReal} {G : E → F} {x : E}
    (hg : FullyAmenableAt g (G x)) (hG : ContDiff ℝ 2 G)
    (hQ : ∀v ∈ normalCone (effectiveDomain g) (G x), (fderiv ℝ G x).adjoint v = 0 → v = 0) :
    ∀ᶠ y in 𝓝 x, y ∈ effectiveDomain (g ∘ G) →
      subdifferential (g ∘ G) y = (fderiv ℝ G y).adjoint '' subdifferential g (G y) ∧
      (∀w, subderivative (g ∘ G) y w = subderivative g (G y) (fderiv ℝ G y w)) := by
  have hnear := hG.continuous.continuousAt.tendsto.eventually hg.eventually
  have hqual := normalKernelQualification_eventually_of_locallyClosed hg.polyhedral_properties.1
    hG.continuous.continuousAt
    (ContinuousLinearMap.adjoint.continuous.continuousAt.comp (hG.continuous_fderiv (by norm_num)).continuousAt) hQ
  filter_upwards [hnear,hqual] with y hy hqy hDy
  have hgy := hy hDy
  have hH : ∀v ∈ horizonSubdifferential g (G y), (fderiv ℝ G y).adjoint v = 0 → v = 0 := by
    simpa only [hgy.horizon_eq_normal_domain] using hqy
  obtain ⟨M⟩ := hgy
  exact M.comp_derivatives (by norm_num) hG hH

end RW
end
