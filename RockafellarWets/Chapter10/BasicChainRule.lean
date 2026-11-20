/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 10: The basic subgradient chain rule
-/

import RockafellarWets.Chapter10.EpigraphChainMaps

open Set
open scoped InnerProductSpace Pointwise

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  {G : E → F} {g : F → EReal} {x : E} {c : ℝ}

/-- **Theorem 10.6**, the unconditional regular-subgradient inclusion. -/
theorem adjoint_regularSubdifferential_subset_comp {A : E →L[ℝ] F}
    (hG : HasFDerivAt G A x) (hx : g (G x) = c) :
    A.adjoint '' regularSubdifferential g (G x) ⊆ regularSubdifferential (g ∘ G) x := by
  rintro _ ⟨y,hy,rfl⟩
  apply (mem_regularSubdifferential_iff_epigraph_normal (f := g ∘ G) (x := x) hx).mpr
  have hh := adjoint_image_regularNormalCone_subset_preimage (hasFDerivAt_epigraphChainMap hG c)
    (euclideanEpigraph g) ⟨WithLp.toLp 2 (y,(-1:ℝ)),
      (mem_regularSubdifferential_iff_epigraph_normal hx).mp hy,rfl⟩
  simpa only [← euclideanEpigraph_comp,epigraphChainDerivative_adjoint,
    WithLp.toLp_fst,WithLp.toLp_snd] using hh

/-- The normal multiplier representation for the lifted epigraph. -/
theorem exists_epigraph_normal_chain (hG : ContDiff ℝ 1 G) (hl : LowerSemicontinuous g)
    (hx : g (G x) = c)
    (hQ : ∀ y ∈ horizonSubdifferential g (G x), (fderiv ℝ G x).adjoint y = 0 → y = 0)
    {v : E} {b : ℝ}
    (hv : WithLp.toLp 2 (v,b) ∈ normalCone (euclideanEpigraph (g ∘ G)) (WithLp.toLp 2 (x,c))) :
    ∃ y : F, WithLp.toLp 2 (y,b) ∈ normalCone (euclideanEpigraph g) (WithLp.toLp 2 (G x,c)) ∧
      (fderiv ℝ G x).adjoint y = v := by
  have hD : IsClosed (euclideanEpigraph g) :=
    (isClosed_epigraph_of_lsc_ereal g hl).preimage (l2ProdEquiv F).continuous
  have hd : HasFDerivAt G (fderiv ℝ G x) x := (hG.differentiable (by norm_num) x).hasFDerivAt
  obtain ⟨q,hq,z,hz,he⟩ := exists_normal_multipliers_of_mem_normalCone isClosed_univ hD
    (contDiff_epigraphChainMap hG) (epigraphChain_constraintQualification hG hl hx hQ)
    (show WithLp.toLp 2 (v,b) ∈ normalCone (univ ∩ epigraphChainMap G ⁻¹' euclideanEpigraph g)
      (WithLp.toLp 2 (x,c)) by simpa only [univ_inter,← euclideanEpigraph_comp] using hv)
  have hz0 : z = 0 := by simpa only [normalCone_univ,mem_singleton_iff] using hz
  rw [hz0,add_zero,(hasFDerivAt_epigraphChainMap hd c).fderiv,epigraphChainDerivative_adjoint] at he
  have hs : q.snd = b := (congrArg WithLp.snd he).symm
  refine ⟨q.fst,?_,(congrArg WithLp.fst he).symm⟩
  simpa only [← hs] using hq

/-- **Theorem 10.6**, the limiting-subgradient inclusion under the horizon
constraint qualification. -/
theorem subdifferential_comp_subset (hG : ContDiff ℝ 1 G) (hl : LowerSemicontinuous g)
    (hx : g (G x) = c)
    (hQ : ∀ y ∈ horizonSubdifferential g (G x), (fderiv ℝ G x).adjoint y = 0 → y = 0) :
    subdifferential (g ∘ G) x ⊆ (fderiv ℝ G x).adjoint '' subdifferential g (G x) := by
  intro v hv
  obtain ⟨y,hy,he⟩ := exists_epigraph_normal_chain hG hl hx hQ
    ((mem_subdifferential_iff_epigraph_normal (f := g ∘ G) (x := x) hx).mp hv)
  exact ⟨y,(mem_subdifferential_iff_epigraph_normal hx).mpr hy,he⟩

/-- **Theorem 10.6**, the horizon-subgradient inclusion. -/
theorem horizonSubdifferential_comp_subset (hG : ContDiff ℝ 1 G) (hl : LowerSemicontinuous g)
    (hx : g (G x) = c)
    (hQ : ∀ y ∈ horizonSubdifferential g (G x), (fderiv ℝ G x).adjoint y = 0 → y = 0) :
    horizonSubdifferential (g ∘ G) x ⊆ (fderiv ℝ G x).adjoint '' horizonSubdifferential g (G x) := by
  intro v hv
  obtain ⟨y,hy,he⟩ := exists_epigraph_normal_chain hG hl hx hQ
    (horizontal_normal_of_mem_horizonSubdifferential (f := g ∘ G) (x := x) hx hv)
  exact ⟨y,(mem_horizonSubdifferential_iff_epigraph_normal_of_locallyLsc
    (locallyLscAt_of_lowerSemicontinuous_finite hl hx) hx).mpr hy,he⟩

/-- **Theorem 10.6**, preservation of regularity under the qualification. -/
theorem IsSubdifferentiallyRegularAt.comp_of_horizon_qualification
    (hr : IsSubdifferentiallyRegularAt g (G x)) (hG : ContDiff ℝ 1 G) (hl : LowerSemicontinuous g)
    (hQ : ∀ y ∈ horizonSubdifferential g (G x), (fderiv ℝ G x).adjoint y = 0 → y = 0) :
    IsSubdifferentiallyRegularAt (g ∘ G) x := by
  let c := (g (G x)).toReal
  have hx : g (G x) = c := (EReal.coe_toReal hr.2.1 hr.1).symm
  have hD : IsClosed (euclideanEpigraph g) :=
    (isClosed_epigraph_of_lsc_ereal g hl).preimage (l2ProdEquiv F).continuous
  have hreg : IsClarkeRegularAt (euclideanEpigraph g) (WithLp.toLp 2 (G x,c)) := hr.2.2
  have hh := (clarkeRegularity_constraints isClosed_univ hD (contDiff_epigraphChainMap hG)
    (show WithLp.toLp 2 (x,c) ∈ univ ∩ epigraphChainMap G ⁻¹' euclideanEpigraph g from ⟨mem_univ _,hx.le⟩)
    (epigraphChain_constraintQualification hG hl hx hQ) (isClarkeRegularAt_univ _) hreg).1
  refine ⟨hr.1,hr.2.1,?_⟩
  simpa only [univ_inter,← euclideanEpigraph_comp] using hh

/-- **Theorem 10.6**, exact limiting subgradients when the outer function is regular. -/
theorem subdifferential_comp_eq_of_regular (hG : ContDiff ℝ 1 G) (hl : LowerSemicontinuous g)
    (hr : IsSubdifferentiallyRegularAt g (G x))
    (hQ : ∀ y ∈ horizonSubdifferential g (G x), (fderiv ℝ G x).adjoint y = 0 → y = 0) :
    subdifferential (g ∘ G) x = (fderiv ℝ G x).adjoint '' subdifferential g (G x) := by
  have hx := (EReal.coe_toReal hr.2.1 hr.1).symm
  apply Subset.antisymm (subdifferential_comp_subset hG hl hx hQ)
  rw [hr.subdifferential_eq_regularSubdifferential]
  exact (adjoint_regularSubdifferential_subset_comp (hG.differentiable (by norm_num) x).hasFDerivAt hx).trans
    (regularSubdifferential_subset_subdifferential _ _)

/-- **Theorem 10.6**, exact horizon subgradients when the outer function is regular. -/
theorem horizonSubdifferential_comp_eq_of_regular (hG : ContDiff ℝ 1 G) (hl : LowerSemicontinuous g)
    (hr : IsSubdifferentiallyRegularAt g (G x))
    (hQ : ∀ y ∈ horizonSubdifferential g (G x), (fderiv ℝ G x).adjoint y = 0 → y = 0) :
    horizonSubdifferential (g ∘ G) x = (fderiv ℝ G x).adjoint '' horizonSubdifferential g (G x) := by
  have hx := (EReal.coe_toReal hr.2.1 hr.1).symm
  apply Subset.antisymm (horizonSubdifferential_comp_subset hG hl hx hQ)
  rintro _ ⟨y,hy,rfl⟩
  apply ((hr.comp_of_horizon_qualification hG hl hQ).mem_horizonSubdifferential_iff_regularNormal hx).mpr
  have hd : HasFDerivAt G (fderiv ℝ G x) x := (hG.differentiable (by norm_num) x).hasFDerivAt
  have hh := adjoint_image_regularNormalCone_subset_preimage (hasFDerivAt_epigraphChainMap hd (g (G x)).toReal)
    (euclideanEpigraph g) ⟨WithLp.toLp 2 (y,(0:ℝ)),(hr.mem_horizonSubdifferential_iff_regularNormal hx).mp hy,rfl⟩
  simpa only [← euclideanEpigraph_comp,epigraphChainDerivative_adjoint,
    WithLp.toLp_fst,WithLp.toLp_snd] using hh

end RW
