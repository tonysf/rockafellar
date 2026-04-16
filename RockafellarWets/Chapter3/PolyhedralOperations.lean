/- 
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3G*: Polyhedral Function Operations

This file packages the first operation theorem from the polyhedral/function tail
of Chapter 3:
- the horizon function of a proper convex piecewise-linear function is again
  proper with closed polyhedral epigraph.
-/

import RockafellarWets.Chapter3.PolyhedralFunctions
import RockafellarWets.Chapter3.EpiAddition

open Set EReal
open scoped Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_horizonFunction
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hne : (epigraph f).Nonempty) :
    HasClosedPolyhedralEpigraph (horizonFunction f) := by
  have hhorizon : IsClosedPolyhedral (horizonCone (epigraph f)) :=
    IsClosedPolyhedral.horizonCone_isClosedPolyhedral (C := epigraph f) hf hne
  exact (show IsClosedPolyhedral (epigraph (horizonFunction f)) from by
    rw [epigraph_horizonFunction_eq_horizonCone_epigraph hne]
    exact hhorizon)

theorem IsConvexPiecewiseLinear.hasClosedPolyhedralEpigraph_horizonFunction
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    HasClosedPolyhedralEpigraph (horizonFunction f) :=
  hf.hasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_horizonFunction
    (epigraph_nonempty_of_isProper hf.isProper)

/-- The first operation clause in Proposition `3.55(b)`: the horizon function
of a proper convex piecewise-linear function is again proper with closed
polyhedral epigraph. -/
theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_horizonFunction
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    IsConvexPiecewiseLinear (horizonFunction f) := by
  refine ⟨?_, hf.hasClosedPolyhedralEpigraph_horizonFunction⟩
  constructor
  · refine ⟨0, ?_⟩
    rw [horizonFunction_zero_eq_zero_of_convex
      hf.convex_epigraph hf.lowerSemicontinuous hf.isProper]
    simp
  · intro w
    exact bot_lt_horizonFunction_of_convex
      hf.convex_epigraph hf.lowerSemicontinuous hf.isProper w

theorem IsConvexPiecewiseLinear.sublinear_horizonFunction
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    Sublinear (horizonFunction f) := by
  refine sublinear_of_positivelyHomogeneous_of_convex_epigraph_of_ne_bot
    (positivelyHomogeneous_horizonFunction f)
    (convex_epigraph_horizonFunction hf.convex_epigraph)
    ?_
  intro w
  exact ne_of_gt <|
    bot_lt_horizonFunction_of_convex
      hf.convex_epigraph hf.lowerSemicontinuous hf.isProper w

theorem HasPolyhedralEpigraph.epiSumIntegrand
    {f₁ f₂ : E → EReal}
    (hf₁ : HasPolyhedralEpigraph f₁) (hf₂ : HasPolyhedralEpigraph f₂)
    (hbot₁ : ∀ x, f₁ x > ⊥) (hbot₂ : ∀ x, f₂ x > ⊥) :
    HasPolyhedralEpigraph (RW.epiSumIntegrand f₁ f₂) := by
  change IsPolyhedral (epigraph (fun p : E × E => f₁ (p.2 - p.1) + f₂ p.1))
  rw [← image_epiSumLinearMap_eq_epigraph hbot₁ hbot₂]
  exact (IsPolyhedral.prod hf₁ hf₂).linear_image epiSumLinearMap

theorem HasPolyhedralEpigraph.hasClosedPolyhedralEpigraph_epiSumIntegrand
    {f₁ f₂ : E → EReal}
    (hf₁ : HasPolyhedralEpigraph f₁) (hf₂ : HasPolyhedralEpigraph f₂)
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂) :
    HasClosedPolyhedralEpigraph (RW.epiSumIntegrand f₁ f₂) := by
  have hpoly : HasPolyhedralEpigraph (RW.epiSumIntegrand f₁ f₂) :=
    HasPolyhedralEpigraph.epiSumIntegrand
      (f₁ := f₁) (f₂ := f₂) hf₁ hf₂ hproper₁.2 hproper₂.2
  exact HasPolyhedralEpigraph.hasClosedPolyhedralEpigraph_of_lowerSemicontinuous
    hpoly (lowerSemicontinuous_epiSumIntegrand hlsc₁ hlsc₂ hproper₁ hproper₂)

section Parametric

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem HasPolyhedralEpigraph.hasPolyhedralEpigraph_valueFunction_of_lsc_localUniform
    [FiniteDimensional ℝ E]
    {f : E × F → EReal} (hf : HasPolyhedralEpigraph f) (hlsc : LowerSemicontinuous f)
    (hLB : IsLevelBoundedInXLocallyUniformly f) :
    HasPolyhedralEpigraph (valueFunction f) := by
  change IsPolyhedral (epigraph (valueFunction f))
  rw [epigraph_valueFunction_eq_valueProjection_image_epigraph_of_lsc_localUniform
    (f := f) hlsc hLB]
  exact hf.linear_image valueProjection

theorem HasPolyhedralEpigraph.hasClosedPolyhedralEpigraph_valueFunction_of_horizonFunction_pos
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E × F → EReal} (hf : HasPolyhedralEpigraph f) (hlsc : LowerSemicontinuous f)
    (hproper : IsProper f)
    (hpos : ∀ ⦃x : E⦄, x ≠ 0 → 0 < horizonFunction f (x, (0 : F))) :
    HasClosedPolyhedralEpigraph (valueFunction f) := by
  have hpoly : HasPolyhedralEpigraph (valueFunction f) :=
    hf.hasPolyhedralEpigraph_valueFunction_of_lsc_localUniform hlsc
      (isLevelBoundedInXLocallyUniformly_of_horizonFunction_pos hpos)
  exact hpoly.hasClosedPolyhedralEpigraph_of_lowerSemicontinuous
    (lowerSemicontinuous_valueFunction_of_horizonFunction_pos hlsc hproper hpos)

theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_valueFunction_of_horizonFunction_pos
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E × F → EReal} (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f)
    (hpos : ∀ ⦃x : E⦄, x ≠ 0 → 0 < horizonFunction f (x, (0 : F))) :
    HasClosedPolyhedralEpigraph (valueFunction f) := by
  let hlsc : LowerSemicontinuous f := hf.lowerSemicontinuous
  change IsClosedPolyhedral (epigraph (valueFunction f))
  rw [epigraph_valueFunction_eq_valueProjection_image_epigraph_of_lsc_localUniform
    (f := f) hlsc (isLevelBoundedInXLocallyUniformly_of_horizonFunction_pos hpos)]
  exact hf.linear_image valueProjection

theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_valueFunction_of_horizonFunction_pos
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E × F → EReal} (hf : HasPolyhedralEpigraph f) (hlsc : LowerSemicontinuous f)
    (hproper : IsProper f)
    (hpos : ∀ ⦃x : E⦄, x ≠ 0 → 0 < horizonFunction f (x, (0 : F))) :
    IsConvexPiecewiseLinear (valueFunction f) := by
  refine ⟨?_, ?_⟩
  · exact isProper_valueFunction_of_lsc_localUniform hlsc hproper
      (isLevelBoundedInXLocallyUniformly_of_horizonFunction_pos hpos)
  · exact hf.hasClosedPolyhedralEpigraph_valueFunction_of_horizonFunction_pos
      hlsc hproper hpos

theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_valueFunction_of_horizonFunction_pos
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E × F → EReal} (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f)
    (hpos : ∀ ⦃x : E⦄, x ≠ 0 → 0 < horizonFunction f (x, (0 : F))) :
    IsConvexPiecewiseLinear (valueFunction f) := by
  let hlsc : LowerSemicontinuous f := hf.lowerSemicontinuous
  refine ⟨?_, hf.hasClosedPolyhedralEpigraph_valueFunction_of_horizonFunction_pos hproper hpos⟩
  exact isProper_valueFunction_of_lsc_localUniform hlsc hproper
    (isLevelBoundedInXLocallyUniformly_of_horizonFunction_pos hpos)

end Parametric

theorem HasPolyhedralEpigraph.hasClosedPolyhedralEpigraph_epiSum_of_horizon_pos
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hf₁ : HasPolyhedralEpigraph f₁) (hf₂ : HasPolyhedralEpigraph f₂)
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction (RW.epiSumIntegrand f₁ f₂) (w, (0 : E))) :
    HasClosedPolyhedralEpigraph (epiSum f₁ f₂) := by
  exact
    HasPolyhedralEpigraph.hasClosedPolyhedralEpigraph_valueFunction_of_horizonFunction_pos
      (f := RW.epiSumIntegrand f₁ f₂)
      (HasPolyhedralEpigraph.epiSumIntegrand
        (f₁ := f₁) (f₂ := f₂) hf₁ hf₂ hproper₁.2 hproper₂.2)
      (lowerSemicontinuous_epiSumIntegrand hlsc₁ hlsc₂ hproper₁ hproper₂)
      (isProper_epiSumIntegrand hproper₁ hproper₂) hpos

theorem HasPolyhedralEpigraph.hasClosedPolyhedralEpigraph_epiSum_of_pos
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hf₁ : HasPolyhedralEpigraph f₁) (hf₂ : HasPolyhedralEpigraph f₂)
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction f₁ (-w) + horizonFunction f₂ w) :
    HasClosedPolyhedralEpigraph (epiSum f₁ f₂) := by
  apply HasPolyhedralEpigraph.hasClosedPolyhedralEpigraph_epiSum_of_horizon_pos
    (f₁ := f₁) (f₂ := f₂) hf₁ hf₂ hlsc₁ hlsc₂ hproper₁ hproper₂
  exact horizonFunction_epiSumIntegrand_pos_of_pos
    hf₁.convex hf₂.convex hlsc₁ hlsc₂ hproper₁ hproper₂ hpos

theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_epiSum_of_horizon_pos
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hf₁ : HasPolyhedralEpigraph f₁) (hf₂ : HasPolyhedralEpigraph f₂)
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction (RW.epiSumIntegrand f₁ f₂) (w, (0 : E))) :
    IsConvexPiecewiseLinear (epiSum f₁ f₂) := by
  simpa [epiSum] using
    HasPolyhedralEpigraph.isConvexPiecewiseLinear_valueFunction_of_horizonFunction_pos
      (E := E) (F := E)
      (f := RW.epiSumIntegrand f₁ f₂)
      (HasPolyhedralEpigraph.epiSumIntegrand
        (f₁ := f₁) (f₂ := f₂) hf₁ hf₂ hproper₁.2 hproper₂.2)
      (lowerSemicontinuous_epiSumIntegrand hlsc₁ hlsc₂ hproper₁ hproper₂)
      (isProper_epiSumIntegrand hproper₁ hproper₂) hpos

theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_epiSum_of_pos
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hf₁ : HasPolyhedralEpigraph f₁) (hf₂ : HasPolyhedralEpigraph f₂)
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction f₁ (-w) + horizonFunction f₂ w) :
    IsConvexPiecewiseLinear (epiSum f₁ f₂) := by
  apply HasPolyhedralEpigraph.isConvexPiecewiseLinear_epiSum_of_horizon_pos
    (f₁ := f₁) (f₂ := f₂) hf₁ hf₂ hlsc₁ hlsc₂ hproper₁ hproper₂
  exact horizonFunction_epiSumIntegrand_pos_of_pos
    hf₁.convex hf₂.convex hlsc₁ hlsc₂ hproper₁ hproper₂ hpos

theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_epiSum_of_isCoercive
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hf₁ : HasPolyhedralEpigraph f₁) (hf₂ : HasPolyhedralEpigraph f₂)
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hcoercive₂ : RW.IsCoercive f₂) :
    IsConvexPiecewiseLinear (epiSum f₁ f₂) := by
  apply HasPolyhedralEpigraph.isConvexPiecewiseLinear_epiSum_of_pos
    (f₁ := f₁) (f₂ := f₂) hf₁ hf₂ hlsc₁ hlsc₂ hproper₁ hproper₂
  exact horizonFunction_epiSum_pos_of_isCoercive
    hf₁.convex hf₂.convex hlsc₁ hlsc₂ hproper₁ hproper₂ hcoercive₂

theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_epiSum_of_horizon_pos
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hf₁ : IsConvexPiecewiseLinear f₁) (hf₂ : IsConvexPiecewiseLinear f₂)
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction (RW.epiSumIntegrand f₁ f₂) (w, (0 : E))) :
    IsConvexPiecewiseLinear (epiSum f₁ f₂) := by
  exact HasPolyhedralEpigraph.isConvexPiecewiseLinear_epiSum_of_horizon_pos
    (hf₁.hasClosedPolyhedralEpigraph.hasPolyhedralEpigraph)
    (hf₂.hasClosedPolyhedralEpigraph.hasPolyhedralEpigraph)
    hf₁.lowerSemicontinuous hf₂.lowerSemicontinuous hf₁.isProper hf₂.isProper hpos

theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_epiSum_of_pos
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hf₁ : IsConvexPiecewiseLinear f₁) (hf₂ : IsConvexPiecewiseLinear f₂)
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction f₁ (-w) + horizonFunction f₂ w) :
    IsConvexPiecewiseLinear (epiSum f₁ f₂) := by
  exact HasPolyhedralEpigraph.isConvexPiecewiseLinear_epiSum_of_pos
    (hf₁.hasClosedPolyhedralEpigraph.hasPolyhedralEpigraph)
    (hf₂.hasClosedPolyhedralEpigraph.hasPolyhedralEpigraph)
    hf₁.lowerSemicontinuous hf₂.lowerSemicontinuous hf₁.isProper hf₂.isProper hpos

theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_epiSum_of_isCoercive
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hf₁ : IsConvexPiecewiseLinear f₁) (hf₂ : IsConvexPiecewiseLinear f₂)
    (hcoercive₂ : RW.IsCoercive f₂) :
    IsConvexPiecewiseLinear (epiSum f₁ f₂) := by
  exact HasPolyhedralEpigraph.isConvexPiecewiseLinear_epiSum_of_isCoercive
    (hf₁.hasClosedPolyhedralEpigraph.hasPolyhedralEpigraph)
    (hf₂.hasClosedPolyhedralEpigraph.hasPolyhedralEpigraph)
    hf₁.lowerSemicontinuous hf₂.lowerSemicontinuous hf₁.isProper hf₂.isProper hcoercive₂

section AffinePerturbations

private noncomputable def epigraphAddLinearEquiv [FiniteDimensional ℝ E] (l : E →ₗ[ℝ] ℝ) :
    (E × ℝ) ≃L[ℝ] (E × ℝ) :=
  ContinuousLinearEquiv.mk
    { toFun := fun p => (p.1, p.2 + l p.1)
      invFun := fun p => (p.1, p.2 - l p.1)
      left_inv := by
        intro p
        ext <;> simp
      right_inv := by
        intro p
        ext <;> simp
      map_add' := by
        intro p q
        ext <;> simp [add_assoc, add_left_comm, add_comm]
      map_smul' := by
        intro a p
        ext
        · simp
        · simp [smul_add, map_smul, mul_add, add_comm, add_left_comm, add_assoc] }
    (by
      have hl :
          Continuous fun p : E × ℝ => l p.1 :=
        l.continuous_of_finiteDimensional.comp continuous_fst
      exact continuous_fst.prodMk (continuous_snd.add hl))
    (by
      have hl :
          Continuous fun p : E × ℝ => l p.1 :=
        l.continuous_of_finiteDimensional.comp continuous_fst
      exact continuous_fst.prodMk (continuous_snd.sub hl))

@[simp] private theorem epigraphAddLinearEquiv_apply [FiniteDimensional ℝ E]
    (l : E →ₗ[ℝ] ℝ) (p : E × ℝ) :
    epigraphAddLinearEquiv (E := E) l p = (p.1, p.2 + l p.1) :=
  rfl

private noncomputable def epigraphAddAffineMap (l : E →ₗ[ℝ] ℝ) (c : ℝ) :
    (E × ℝ) →ᵃ[ℝ] (E × ℝ) where
  toFun p := (p.1, p.2 + l p.1 + c)
  linear :=
    (LinearMap.fst ℝ E ℝ).prod
      (l.comp (LinearMap.fst ℝ E ℝ) + LinearMap.snd ℝ E ℝ)
  map_vadd' p v := by
    ext <;> simp [add_assoc, add_left_comm, add_comm]

@[simp] private theorem epigraphAddAffineMap_apply
    (l : E →ₗ[ℝ] ℝ) (c : ℝ) (p : E × ℝ) :
    epigraphAddAffineMap (E := E) l c p = (p.1, p.2 + l p.1 + c) :=
  rfl

private theorem image_epigraphAddAffineMap_eq_epigraph_addAffine
    {f : E → EReal} (l : E →ₗ[ℝ] ℝ) (c : ℝ) :
    epigraphAddAffineMap (E := E) l c '' epigraph f =
      epigraph (fun x => f x + (l x + c : ℝ)) := by
  ext z
  rcases z with ⟨x, t⟩
  constructor
  · rintro ⟨⟨x', s⟩, hs, hp⟩
    have hx : x' = x := by
      simpa [epigraphAddAffineMap_apply] using congrArg Prod.fst hp
    have ht : s + l x' + c = t := by
      simpa [epigraphAddAffineMap_apply] using congrArg Prod.snd hp
    subst x'
    rw [mem_epigraph_iff] at hs ⊢
    have hle' : ((l x + c : ℝ) : EReal) + f x ≤ ((l x + c : ℝ) : EReal) + s := by
      exact add_le_add_right hs (((l x + c : ℝ) : EReal))
    have hle : f x + ((l x + c : ℝ) : EReal) ≤ (s : EReal) + (l x + c : ℝ) := by
      simpa [add_assoc, add_left_comm, add_comm] using hle'
    have hleNorm : f x + ((c : EReal) + (l x : ℝ)) ≤ (c : EReal) + ((s : EReal) + (l x : ℝ)) := by
      simpa [EReal.coe_add, add_assoc, add_left_comm, add_comm] using hle
    have ht' : (c : EReal) + ((s : EReal) + (l x : ℝ)) = (t : EReal) := by
      simpa [EReal.coe_add, add_assoc, add_left_comm, add_comm] using
        congrArg (fun u : ℝ => (u : EReal)) ht
    have hfinal : f x + ((c : EReal) + (l x : ℝ)) ≤ (t : EReal) := by
      exact hleNorm.trans (le_of_eq ht')
    simpa [EReal.coe_add, add_assoc, add_left_comm, add_comm] using hfinal
  · intro hz
    refine ⟨(x, t - (l x + c)), ?_, ?_⟩
    · rw [mem_epigraph_iff] at hz ⊢
      exact
        (EReal.le_sub_iff_add_le
          (a := f x) (b := ((l x + c : ℝ) : EReal)) (c := (t : EReal))
          (Or.inl (by simpa [EReal.coe_add] using (EReal.coe_ne_bot (l x + c))))
          (Or.inl (by simpa [EReal.coe_add] using (EReal.coe_ne_top (l x + c))))).2 <|
          by simpa [EReal.coe_add, add_assoc, add_left_comm, add_comm] using hz
    · ext
      · simp [epigraphAddAffineMap_apply]
      · simp [epigraphAddAffineMap_apply]
        ring

/-- Affine perturbations preserve polyhedral epigraphs. -/
theorem HasPolyhedralEpigraph.hasPolyhedralEpigraph_addAffine
    {f : E → EReal} (hf : HasPolyhedralEpigraph f)
    (l : E →ₗ[ℝ] ℝ) (c : ℝ) :
    HasPolyhedralEpigraph (fun x => f x + (l x + c : ℝ)) := by
  change IsPolyhedral (epigraph (fun x => f x + (l x + c : ℝ)))
  rw [← image_epigraphAddAffineMap_eq_epigraph_addAffine (f := f) (l := l) (c := c)]
  exact hf.affine_image (epigraphAddAffineMap (E := E) l c)

/-- Adding a finite affine function preserves closed polyhedral epigraphs. -/
theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_addAffine
    [FiniteDimensional ℝ E]
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f)
    (l : E →ₗ[ℝ] ℝ) (c : ℝ) :
    HasClosedPolyhedralEpigraph (fun x => f x + (l x + c : ℝ)) := by
  have hlin : IsClosedPolyhedral (epigraphAddLinearEquiv (E := E) l '' epigraph f) :=
    hf.image_linearEquiv (epigraphAddLinearEquiv (E := E) l)
  have htrans :
      IsClosedPolyhedral
        ((fun p : E × ℝ => p + ((0 : E), c)) '' (epigraphAddLinearEquiv (E := E) l '' epigraph f)) :=
    hlin.image_add_right ((0 : E), c)
  have himage :
      epigraphAddAffineMap (E := E) l c '' epigraph f =
        (fun p : E × ℝ => p + ((0 : E), c)) '' (epigraphAddLinearEquiv (E := E) l '' epigraph f) := by
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨epigraphAddLinearEquiv (E := E) l p, ⟨p, hp, rfl⟩, ?_⟩
      simp [epigraphAddAffineMap_apply, epigraphAddLinearEquiv_apply, add_assoc, add_left_comm,
        add_comm]
    · rintro ⟨q, ⟨p, hp, rfl⟩, hq⟩
      refine ⟨p, hp, ?_⟩
      simpa [epigraphAddAffineMap_apply, epigraphAddLinearEquiv_apply, add_assoc,
        add_left_comm, add_comm] using hq
  change IsClosedPolyhedral (epigraph (fun x => f x + (l x + c : ℝ)))
  rw [← image_epigraphAddAffineMap_eq_epigraph_addAffine (f := f) (l := l) (c := c)]
  rw [himage]
  exact htrans

/-- Adding a finite affine function preserves properness. -/
theorem isProper_addAffine {f : E → EReal}
    (hproper : IsProper f) (l : E →ₗ[ℝ] ℝ) (c : ℝ) :
    IsProper (fun x => f x + (l x + c : ℝ)) := by
  constructor
  · rcases hproper.1 with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    exact EReal.add_lt_top (ne_of_lt hx) <|
      by simpa [EReal.coe_add] using (EReal.coe_ne_top (l x + c))
  · intro x
    simpa using EReal.add_lt_add_right_coe (hproper.2 x) (l x + c)

/-- Adding a finite affine function preserves lower semicontinuity. -/
theorem lowerSemicontinuous_addAffine {f : E → EReal}
    [FiniteDimensional ℝ E]
    (hlsc : LowerSemicontinuous f) (l : E →ₗ[ℝ] ℝ) (c : ℝ) :
    LowerSemicontinuous (fun x => f x + (l x + c : ℝ)) := by
  have hcont_aff : Continuous (fun x : E => (((l x + c : ℝ) : EReal))) := by
    exact continuous_coe_real_ereal.comp
      (l.continuous_of_finiteDimensional.add continuous_const)
  refine LowerSemicontinuous.add' hlsc hcont_aff.lowerSemicontinuous ?_
  intro x
  exact EReal.continuousAt_add
    (Or.inr (by simpa [EReal.coe_add] using (EReal.coe_ne_bot (l x + c))))
    (Or.inr (by simpa [EReal.coe_add] using (EReal.coe_ne_top (l x + c))))

/-- Affine perturbations preserve convex piecewise-linearity in the project's
epigraph-based sense once properness and lower semicontinuity are available. -/
theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_addAffine
    [FiniteDimensional ℝ E]
    {f : E → EReal} (hf : HasPolyhedralEpigraph f)
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f)
    (l : E →ₗ[ℝ] ℝ) (c : ℝ) :
    IsConvexPiecewiseLinear (fun x => f x + (l x + c : ℝ)) := by
  refine ⟨isProper_addAffine hproper l c, ?_⟩
  exact
    (hf.hasPolyhedralEpigraph_addAffine l c).hasClosedPolyhedralEpigraph_of_lowerSemicontinuous
      (lowerSemicontinuous_addAffine hlsc l c)

/-- Adding a finite affine function preserves convex piecewise-linearity. -/
theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_addAffine
    [FiniteDimensional ℝ E]
    {f : E → EReal} (hf : IsConvexPiecewiseLinear f)
    (l : E →ₗ[ℝ] ℝ) (c : ℝ) :
    IsConvexPiecewiseLinear (fun x => f x + (l x + c : ℝ)) := by
  exact ⟨isProper_addAffine hf.isProper l c,
    hf.hasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_addAffine l c⟩

/-- Finite affine functions are convex piecewise-linear. -/
theorem isConvexPiecewiseLinear_affine
    [FiniteDimensional ℝ E] (l : E →ₗ[ℝ] ℝ) (c : ℝ) :
    IsConvexPiecewiseLinear (fun x : E => (l x + c : ℝ)) := by
  simpa using
    (hasPolyhedralEpigraph_zero (E := E)).isConvexPiecewiseLinear_addAffine
      lowerSemicontinuous_zero isProper_zero l c

end AffinePerturbations

section DomainTranslations

private noncomputable def epigraphTranslateInputMap (u : E) :
    (E × ℝ) →ᵃ[ℝ] (E × ℝ) where
  toFun p := (p.1 - u, p.2)
  linear := LinearMap.id
  map_vadd' p v := by
    ext <;> simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

@[simp] private theorem epigraphTranslateInputMap_apply
    (u : E) (p : E × ℝ) :
    epigraphTranslateInputMap (E := E) u p = (p.1 - u, p.2) :=
  rfl

private theorem image_epigraphTranslateInputMap_eq_epigraph_precompose_add
    {f : E → EReal} (u : E) :
    epigraphTranslateInputMap (E := E) u '' epigraph f =
      epigraph (fun x => f (x + u)) := by
  ext z
  rcases z with ⟨x, t⟩
  constructor
  · rintro ⟨⟨x', s⟩, hs, hp⟩
    have hx : x' - u = x := by
      simpa [epigraphTranslateInputMap_apply] using congrArg Prod.fst hp
    have ht : s = t := by
      simpa [epigraphTranslateInputMap_apply] using congrArg Prod.snd hp
    have hx' : x' = x + u := by
      have hx'' := congrArg (fun y : E => y + u) hx
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hx''
    subst x'
    subst s
    simpa [mem_epigraph_iff, add_assoc, add_left_comm, add_comm] using hs
  · intro hz
    refine ⟨(x + u, t), ?_, ?_⟩
    · simpa [mem_epigraph_iff, add_assoc, add_left_comm, add_comm] using hz
    · ext <;> simp [epigraphTranslateInputMap_apply, sub_eq_add_neg, add_assoc, add_left_comm,
        add_comm]

/-- Translating the argument preserves polyhedral epigraphs. -/
theorem HasPolyhedralEpigraph.hasPolyhedralEpigraph_precompose_add
    {f : E → EReal} (hf : HasPolyhedralEpigraph f) (u : E) :
    HasPolyhedralEpigraph (fun x => f (x + u)) := by
  change IsPolyhedral (epigraph (fun x => f (x + u)))
  rw [← image_epigraphTranslateInputMap_eq_epigraph_precompose_add (f := f) (u := u)]
  exact hf.affine_image (epigraphTranslateInputMap (E := E) u)

/-- Translating the argument preserves closed polyhedral epigraphs. -/
theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_precompose_add
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f) (u : E) :
    HasClosedPolyhedralEpigraph (fun x => f (x + u)) := by
  have htrans :
      IsClosedPolyhedral
        ((fun p : E × ℝ => p + ((-u), (0 : ℝ))) '' epigraph f) :=
    hf.image_add_right ((-u), (0 : ℝ))
  have himage :
      ((fun p : E × ℝ => p + ((-u), (0 : ℝ))) '' epigraph f) =
        epigraph (fun x => f (x + u)) := by
    ext z
    rcases z with ⟨x, t⟩
    constructor
    · rintro ⟨⟨x', s⟩, hs, hz⟩
      have hx : x' + -u = x := by
        simpa [add_comm, add_left_comm, add_assoc] using congrArg Prod.fst hz
      have ht : s = t := by
        simpa using congrArg Prod.snd hz
      have hx' : x' = x + u := by
        have hx'' := congrArg (fun y : E => y + u) hx
        simpa [add_assoc, add_left_comm, add_comm] using hx''
      subst x'
      subst s
      simpa [mem_epigraph_iff, add_assoc, add_left_comm, add_comm] using hs
    · intro hz
      refine ⟨(x + u, t), ?_, ?_⟩
      · simpa [mem_epigraph_iff, add_assoc, add_left_comm, add_comm] using hz
      · ext <;> simp [add_assoc, add_left_comm, add_comm]
  change IsClosedPolyhedral (epigraph (fun x => f (x + u)))
  rw [← himage]
  exact htrans

/-- Translating the argument preserves properness. -/
theorem isProper_precompose_add {f : E → EReal}
    (hproper : IsProper f) (u : E) :
    IsProper (fun x => f (x + u)) := by
  constructor
  · rcases hproper.1 with ⟨x, hx⟩
    refine ⟨x - u, ?_⟩
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hx
  · intro x
    simpa [add_assoc, add_left_comm, add_comm] using hproper.2 (x + u)

/-- Translating the argument preserves lower semicontinuity. -/
theorem lowerSemicontinuous_precompose_add {f : E → EReal}
    (hlsc : LowerSemicontinuous f) (u : E) :
    LowerSemicontinuous (fun x => f (x + u)) := by
  simpa [Function.comp] using hlsc.comp (continuous_id.add continuous_const)

/-- Translating the argument preserves convex piecewise-linearity in the
project's epigraph-based sense. -/
theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_add
    {f : E → EReal} (hf : HasPolyhedralEpigraph f)
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f) (u : E) :
    IsConvexPiecewiseLinear (fun x => f (x + u)) := by
  refine ⟨isProper_precompose_add hproper u, ?_⟩
  exact
    (hf.hasPolyhedralEpigraph_precompose_add u).hasClosedPolyhedralEpigraph_of_lowerSemicontinuous
      (lowerSemicontinuous_precompose_add hlsc u)

/-- Translating the argument preserves convex piecewise-linearity. -/
theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_precompose_add
    {f : E → EReal} (hf : IsConvexPiecewiseLinear f) (u : E) :
    IsConvexPiecewiseLinear (fun x => f (x + u)) := by
  exact ⟨isProper_precompose_add hf.isProper u,
    hf.hasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_precompose_add u⟩

end DomainTranslations

section PositiveScalings

private noncomputable def epigraphScaleSecondLinearEquiv (a : ℝ) (ha : 0 < a) :
    (E × ℝ) ≃L[ℝ] (E × ℝ) :=
  ContinuousLinearEquiv.mk
    { toFun := fun p => (p.1, a * p.2)
      invFun := fun p => (p.1, p.2 / a)
      left_inv := by
        intro p
        ext <;> simp [ha.ne']
      right_inv := by
        intro p
        ext
        · simp
        · exact mul_div_cancel₀ p.2 ha.ne'
      map_add' := by
        intro p q
        ext <;> simp [mul_add]
      map_smul' := by
        intro r p
        ext <;> simp [mul_assoc, mul_left_comm, mul_comm] }
    (by continuity)
    (by continuity)

@[simp] private theorem epigraphScaleSecondLinearEquiv_apply
    (a : ℝ) (ha : 0 < a) (p : E × ℝ) :
    epigraphScaleSecondLinearEquiv (E := E) a ha p = (p.1, a * p.2) :=
  rfl

private noncomputable def epigraphScaleSecondMap (a : ℝ) :
    (E × ℝ) →ᵃ[ℝ] (E × ℝ) where
  toFun p := (p.1, a * p.2)
  linear := (LinearMap.fst ℝ E ℝ).prod (a • LinearMap.snd ℝ E ℝ)
  map_vadd' p v := by
    ext <;> simp [smul_eq_mul, mul_add]

@[simp] private theorem epigraphScaleSecondMap_apply
    (a : ℝ) (p : E × ℝ) :
    epigraphScaleSecondMap (E := E) a p = (p.1, a * p.2) :=
  rfl

private noncomputable def epigraphScaleSecondHomeomorph (a : ℝ) (ha0 : a ≠ 0) :
    (E × ℝ) ≃ₜ (E × ℝ) :=
  (Homeomorph.refl E).prodCongr (Homeomorph.smulOfNeZero a ha0)

@[simp] private theorem epigraphScaleSecondHomeomorph_apply
    (a : ℝ) (ha0 : a ≠ 0) (p : E × ℝ) :
    epigraphScaleSecondHomeomorph (E := E) a ha0 p = (p.1, a * p.2) := by
  cases p
  rfl

private theorem image_epigraphScaleSecondMap_eq_epigraph_const_mul
    {f : E → EReal} {a : ℝ} (ha : 0 < a) :
    epigraphScaleSecondMap (E := E) a '' epigraph f =
      epigraph (fun x => (a : EReal) * f x) := by
  ext z
  rcases z with ⟨x, t⟩
  constructor
  · rintro ⟨⟨x', s⟩, hs, hp⟩
    have hx : x' = x := by
      simpa [epigraphScaleSecondMap_apply] using congrArg Prod.fst hp
    have ht : a * s = t := by
      simpa [epigraphScaleSecondMap_apply] using congrArg Prod.snd hp
    subst x'
    rw [mem_epigraph_iff] at hs ⊢
    have hmul : (a : EReal) * f x ≤ (a : EReal) * s := by
      gcongr
    have ht' : ((a * s : ℝ) : EReal) = (t : EReal) := by
      simpa [EReal.coe_mul] using congrArg (fun u : ℝ => (u : EReal)) ht
    have hmul' : (a : EReal) * f x ≤ ((a * s : ℝ) : EReal) := by
      simpa [EReal.coe_mul] using hmul
    simpa [ht'] using hmul'
  · intro hz
    refine ⟨(x, t / a), ?_, ?_⟩
    · rw [mem_epigraph_iff] at hz ⊢
      exact
        (EReal.le_div_iff_mul_le
          (a := f x) (b := (a : EReal)) (c := (t : EReal))
          (by exact_mod_cast ha) (by simp)).2 <|
          by simpa [mul_comm] using hz
    · ext
      · simp [epigraphScaleSecondMap_apply]
      · simpa [epigraphScaleSecondMap_apply, mul_comm] using div_mul_cancel₀ t ha.ne'

/-- Positive scalar multiples preserve polyhedral epigraphs. -/
theorem HasPolyhedralEpigraph.hasPolyhedralEpigraph_const_mul
    {f : E → EReal} (hf : HasPolyhedralEpigraph f) {a : ℝ} (ha : 0 < a) :
    HasPolyhedralEpigraph (fun x => (a : EReal) * f x) := by
  change IsPolyhedral (epigraph (fun x => (a : EReal) * f x))
  rw [← image_epigraphScaleSecondMap_eq_epigraph_const_mul (f := f) ha]
  exact hf.affine_image (epigraphScaleSecondMap (E := E) a)

/-- Positive scalar multiples preserve closed polyhedral epigraphs. -/
theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_const_mul
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f) {a : ℝ} (ha : 0 < a) :
    HasClosedPolyhedralEpigraph (fun x => (a : EReal) * f x) := by
  have hlin : IsClosedPolyhedral
      (epigraphScaleSecondLinearEquiv (E := E) a ha '' epigraph f) :=
    hf.image_linearEquiv (epigraphScaleSecondLinearEquiv (E := E) a ha)
  change IsClosedPolyhedral (epigraph (fun x => (a : EReal) * f x))
  rw [← image_epigraphScaleSecondMap_eq_epigraph_const_mul (f := f) ha]
  simpa [epigraphScaleSecondMap_apply, epigraphScaleSecondLinearEquiv_apply, mul_comm] using hlin

/-- Positive scalar multiples preserve properness. -/
theorem isProper_const_mul {f : E → EReal}
    (hproper : IsProper f) {a : ℝ} (ha : 0 < a) :
    IsProper (fun x => (a : EReal) * f x) := by
  constructor
  · rcases hproper.1 with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply lt_top_iff_ne_top.mpr
    rw [EReal.mul_ne_top]
    refine ⟨Or.inl (by simp), Or.inl (by exact_mod_cast ha.le), Or.inl (by simp),
      Or.inr (ne_of_lt hx)⟩
  · intro x
    apply bot_lt_iff_ne_bot.mpr
    rw [EReal.mul_ne_bot]
    refine ⟨Or.inl (by simp), Or.inr (ne_of_gt (hproper.2 x)), Or.inl (by simp),
      Or.inl (by exact_mod_cast ha.le)⟩

/-- Positive scalar multiples preserve lower semicontinuity. -/
theorem lowerSemicontinuous_const_mul {f : E → EReal}
    (hlsc : LowerSemicontinuous f) {a : ℝ} (ha : 0 < a) :
    LowerSemicontinuous (fun x => (a : EReal) * f x) := by
  apply lowerSemicontinuous_of_isClosed_epigraph_ereal
  rw [← image_epigraphScaleSecondMap_eq_epigraph_const_mul (f := f) ha]
  have hclosedMap : IsClosedMap (epigraphScaleSecondMap (E := E) a) := by
    simpa [epigraphScaleSecondMap_apply, epigraphScaleSecondHomeomorph_apply, smul_eq_mul] using
      (epigraphScaleSecondHomeomorph (E := E) a ha.ne').isClosedMap
  exact hclosedMap _ (isClosed_epigraph_of_lsc_ereal f hlsc)

/-- Positive scalar multiples preserve convex piecewise-linearity in the
project's epigraph-based sense. -/
theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_const_mul
    {f : E → EReal} (hf : HasPolyhedralEpigraph f)
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f) {a : ℝ} (ha : 0 < a) :
    IsConvexPiecewiseLinear (fun x => (a : EReal) * f x) := by
  refine ⟨isProper_const_mul hproper ha, ?_⟩
  exact
    (hf.hasPolyhedralEpigraph_const_mul ha).hasClosedPolyhedralEpigraph_of_lowerSemicontinuous
      (lowerSemicontinuous_const_mul hlsc ha)

/-- Positive scalar multiples preserve convex piecewise-linearity. -/
theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_const_mul
    {f : E → EReal} (hf : IsConvexPiecewiseLinear f) {a : ℝ} (ha : 0 < a) :
    IsConvexPiecewiseLinear (fun x => (a : EReal) * f x) := by
  exact ⟨isProper_const_mul hf.isProper ha,
    hf.hasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_const_mul ha⟩

end PositiveScalings

section CombinedOperations

/-- Positive vertical scaling, input translation, and finite affine
perturbation preserve convex piecewise-linearity in the project's epigraph-based
sense. -/
theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_affineRescaleTranslate
    [FiniteDimensional ℝ E] {f : E → EReal} (hf : HasPolyhedralEpigraph f)
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f)
    {a : ℝ} (ha : 0 < a) (u : E) (l : E →ₗ[ℝ] ℝ) (c : ℝ) :
    IsConvexPiecewiseLinear (fun x => (a : EReal) * f (x + u) + (l x + c : ℝ)) := by
  have hf₁ : HasPolyhedralEpigraph (fun x => f (x + u)) :=
    hf.hasPolyhedralEpigraph_precompose_add u
  have hlsc₁ : LowerSemicontinuous (fun x => f (x + u)) :=
    lowerSemicontinuous_precompose_add hlsc u
  have hproper₁ : IsProper (fun x => f (x + u)) :=
    isProper_precompose_add hproper u
  have hf₂ : HasPolyhedralEpigraph (fun x => (a : EReal) * f (x + u)) :=
    hf₁.hasPolyhedralEpigraph_const_mul ha
  have hlsc₂ : LowerSemicontinuous (fun x => (a : EReal) * f (x + u)) :=
    lowerSemicontinuous_const_mul hlsc₁ ha
  have hproper₂ : IsProper (fun x => (a : EReal) * f (x + u)) :=
    isProper_const_mul hproper₁ ha
  exact hf₂.isConvexPiecewiseLinear_addAffine hlsc₂ hproper₂ l c

end CombinedOperations

section LinearEquivalences

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private noncomputable def epigraphPrecomposeLinearEquivMap (e : F ≃L[ℝ] E) :
    (E × ℝ) →ᵃ[ℝ] (F × ℝ) where
  toFun p := (e.symm p.1, p.2)
  linear :=
    (e.symm.toLinearMap.comp (LinearMap.fst ℝ E ℝ)).prod (LinearMap.snd ℝ E ℝ)
  map_vadd' p v := by
    ext <;> simp

@[simp] private theorem epigraphPrecomposeLinearEquivMap_apply
    (e : F ≃L[ℝ] E) (p : E × ℝ) :
    epigraphPrecomposeLinearEquivMap (E := E) e p = (e.symm p.1, p.2) :=
  rfl

private theorem image_epigraphPrecomposeLinearEquivMap_eq_epigraph_precompose
    {f : E → EReal} (e : F ≃L[ℝ] E) :
    epigraphPrecomposeLinearEquivMap (E := E) e '' epigraph f =
      epigraph (fun y : F => f (e y)) := by
  ext z
  rcases z with ⟨y, t⟩
  constructor
  · rintro ⟨⟨x, s⟩, hs, hp⟩
    have hy : e.symm x = y := by
      simpa [epigraphPrecomposeLinearEquivMap_apply] using congrArg Prod.fst hp
    have ht : s = t := by
      simpa [epigraphPrecomposeLinearEquivMap_apply] using congrArg Prod.snd hp
    have hx : x = e y := by
      simpa using congrArg e hy
    subst x
    subst s
    simpa [mem_epigraph_iff] using hs
  · intro hz
    refine ⟨(e y, t), ?_, ?_⟩
    · simpa [mem_epigraph_iff] using hz
    · ext <;> simp [epigraphPrecomposeLinearEquivMap_apply]

/-- Precomposition by a continuous linear equivalence preserves polyhedral
epigraphs. -/
theorem HasPolyhedralEpigraph.hasPolyhedralEpigraph_precompose_linearEquiv
    {f : E → EReal} (hf : HasPolyhedralEpigraph f) (e : F ≃L[ℝ] E) :
    HasPolyhedralEpigraph (fun y : F => f (e y)) := by
  change IsPolyhedral (epigraph (fun y : F => f (e y)))
  rw [← image_epigraphPrecomposeLinearEquivMap_eq_epigraph_precompose (E := E) (f := f) e]
  exact hf.affine_image (epigraphPrecomposeLinearEquivMap (E := E) e)

/-- Precomposition by a continuous linear equivalence preserves closed
polyhedral epigraphs. -/
theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_precompose_linearEquiv
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f) (e : F ≃L[ℝ] E) :
    HasClosedPolyhedralEpigraph (fun y : F => f (e y)) := by
  let e' : (F × ℝ) ≃L[ℝ] (E × ℝ) :=
    e.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)
  have himage : e'.symm '' epigraph f = epigraph (fun y : F => f (e y)) := by
    ext z
    rcases z with ⟨y, t⟩
    constructor
    · rintro ⟨⟨x, s⟩, hs, hz⟩
      have hy : e.symm x = y := by
        simpa [e', ContinuousLinearEquiv.prodCongr_symm] using congrArg Prod.fst hz
      have ht : s = t := by
        simpa [e', ContinuousLinearEquiv.prodCongr_symm] using congrArg Prod.snd hz
      have hx : x = e y := by
        simpa using congrArg e hy
      subst x
      subst s
      simpa [mem_epigraph_iff] using hs
    · intro hz
      refine ⟨(e y, t), ?_, ?_⟩
      · simpa [mem_epigraph_iff] using hz
      · ext <;> simp [e', ContinuousLinearEquiv.prodCongr_symm]
  change IsClosedPolyhedral (epigraph (fun y : F => f (e y)))
  rw [← himage]
  exact hf.image_linearEquiv e'.symm

/-- Precomposition by a continuous linear equivalence preserves properness. -/
theorem isProper_precompose_linearEquiv {f : E → EReal}
    (hproper : IsProper f) (e : F ≃L[ℝ] E) :
    IsProper (fun y : F => f (e y)) := by
  constructor
  · rcases hproper.1 with ⟨x, hx⟩
    refine ⟨e.symm x, ?_⟩
    simpa using hx
  · intro y
    simpa using hproper.2 (e y)

/-- Precomposition by a continuous linear equivalence preserves lower
semicontinuity. -/
theorem lowerSemicontinuous_precompose_linearEquiv {f : E → EReal}
    (hlsc : LowerSemicontinuous f) (e : F ≃L[ℝ] E) :
    LowerSemicontinuous (fun y : F => f (e y)) := by
  simpa [Function.comp] using hlsc.comp e.continuous

/-- Precomposition by a continuous linear equivalence preserves convex
piecewise-linearity in the project's epigraph-based sense. -/
theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_linearEquiv
    {f : E → EReal} (hf : HasPolyhedralEpigraph f)
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f) (e : F ≃L[ℝ] E) :
    IsConvexPiecewiseLinear (fun y : F => f (e y)) := by
  refine ⟨isProper_precompose_linearEquiv hproper e, ?_⟩
  have hpoly : HasPolyhedralEpigraph (fun y : F => f (e y)) :=
    hf.hasPolyhedralEpigraph_precompose_linearEquiv e
  exact hpoly.hasClosedPolyhedralEpigraph_of_lowerSemicontinuous
    (lowerSemicontinuous_precompose_linearEquiv hlsc e)

/-- Precomposition by a continuous linear equivalence preserves convex
piecewise-linearity. -/
theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_precompose_linearEquiv
    {f : E → EReal} (hf : IsConvexPiecewiseLinear f) (e : F ≃L[ℝ] E) :
    IsConvexPiecewiseLinear (fun y : F => f (e y)) := by
  exact ⟨isProper_precompose_linearEquiv hf.isProper e,
    (hf.hasClosedPolyhedralEpigraph).hasClosedPolyhedralEpigraph_precompose_linearEquiv e⟩

end LinearEquivalences

section LinearSurjections

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

private noncomputable def epigraphPrecomposeLinearSurjMap
    (L : F →ₗ[ℝ] E) (r : E →L[ℝ] F) :
    ((E × ℝ) × LinearMap.ker L) →ᵃ[ℝ] (F × ℝ) where
  toFun p := (r p.1.1 + p.2, p.1.2)
  linear :=
    let fstPair : ((E × ℝ) × LinearMap.ker L) →ₗ[ℝ] (E × ℝ) :=
      LinearMap.fst ℝ (E × ℝ) (LinearMap.ker L)
    let xPart : ((E × ℝ) × LinearMap.ker L) →ₗ[ℝ] E :=
      (LinearMap.fst ℝ E ℝ).comp fstPair
    let tPart : ((E × ℝ) × LinearMap.ker L) →ₗ[ℝ] ℝ :=
      (LinearMap.snd ℝ E ℝ).comp fstPair
    let kPart : ((E × ℝ) × LinearMap.ker L) →ₗ[ℝ] F :=
      (LinearMap.ker L).subtype.comp (LinearMap.snd ℝ (E × ℝ) (LinearMap.ker L))
    (r.toLinearMap.comp xPart + kPart).prod tPart
  map_vadd' p v := by
    ext <;> simp [add_assoc, add_left_comm, add_comm]

@[simp] private theorem epigraphPrecomposeLinearSurjMap_apply
    (L : F →ₗ[ℝ] E) (r : E →L[ℝ] F) (p : (E × ℝ) × LinearMap.ker L) :
    epigraphPrecomposeLinearSurjMap (E := E) L r p = (r p.1.1 + p.2, p.1.2) :=
  rfl

private theorem image_epigraphPrecomposeLinearSurjMap_eq_epigraph_precompose
    {f : E → EReal} (L : F →ₗ[ℝ] E) (r : E →L[ℝ] F)
    (hr : (L.toContinuousLinearMap).comp r = ContinuousLinearMap.id ℝ E) :
    epigraphPrecomposeLinearSurjMap (E := E) L r ''
        (epigraph f ×ˢ (Set.univ : Set (LinearMap.ker L))) =
      epigraph (fun y : F => f (L y)) := by
  ext z
  rcases z with ⟨y, t⟩
  constructor
  · rintro ⟨⟨⟨x, s⟩, k⟩, hs, hp⟩
    rcases hs with ⟨hxepi, hk⟩
    have hy : r x + (k : F) = y := by
      simpa [epigraphPrecomposeLinearSurjMap_apply] using congrArg Prod.fst hp
    have ht : s = t := by
      simpa [epigraphPrecomposeLinearSurjMap_apply] using congrArg Prod.snd hp
    have hrx : L (r x) = x := by
      simpa using congrArg (fun g : E →L[ℝ] E => g x) hr
    have hkzero : L (k : F) = 0 := k.2
    have hLy : L y = x := by
      calc
        L y = L (r x + (k : F)) := by rw [← hy]
        _ = L (r x) + L (k : F) := by simp
        _ = x := by simp [hrx, hkzero]
    rw [mem_epigraph_iff] at hxepi ⊢
    simpa [ht, hLy] using hxepi
  · intro hz
    rw [mem_epigraph_iff] at hz
    let k : LinearMap.ker L :=
      ⟨y - r (L y), by
        have hry : L (r (L y)) = L y := by
          simpa using congrArg (fun g : E →L[ℝ] E => g (L y)) hr
        change L (y - r (L y)) = 0
        simp [hry]⟩
    refine ⟨((L y, t), k), ?_, ?_⟩
    · exact ⟨by simpa [mem_epigraph_iff] using hz, by simp⟩
    · ext
      · change r (L y) + (y - r (L y)) = y
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      · simp [epigraphPrecomposeLinearSurjMap_apply]

/-- Precomposition by a linear surjection preserves polyhedral epigraphs. -/
theorem HasPolyhedralEpigraph.hasPolyhedralEpigraph_precompose_linearMap_of_surjective
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasPolyhedralEpigraph f) (L : F →ₗ[ℝ] E)
    (hL : LinearMap.range L = ⊤) :
    HasPolyhedralEpigraph (fun y : F => f (L y)) := by
  let Lc : F →L[ℝ] E := L.toContinuousLinearMap
  obtain ⟨r, hr⟩ := ContinuousLinearMap.exists_right_inverse_of_surjective Lc (by
    simpa using hL)
  change IsPolyhedral (epigraph (fun y : F => f (L y)))
  rw [← image_epigraphPrecomposeLinearSurjMap_eq_epigraph_precompose (E := E) (f := f) L r hr]
  exact (hf.prod (IsPolyhedral.univ (E := LinearMap.ker L))).affine_image
    (epigraphPrecomposeLinearSurjMap (E := E) L r)

/-- Precomposition by a linear surjection preserves closed polyhedral
epigraphs. -/
theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_precompose_linearMap_of_surjective
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f) (L : F →ₗ[ℝ] E)
    (hL : LinearMap.range L = ⊤) :
    HasClosedPolyhedralEpigraph (fun y : F => f (L y)) := by
  let M : (F × ℝ) →ₗ[ℝ] (E × ℝ) :=
    (L.comp (LinearMap.fst ℝ F ℝ)).prod (LinearMap.snd ℝ F ℝ)
  have hpre : M ⁻¹' epigraph f = epigraph (fun y : F => f (L y)) := by
    ext z
    rcases z with ⟨y, t⟩
    simp [M, mem_epigraph_iff]
  have hM : LinearMap.range M = ⊤ := by
    ext z
    constructor
    · intro _
      simp
    · intro _
      rcases LinearMap.range_eq_top.mp hL z.1 with ⟨y, hy⟩
      refine ⟨(y, z.2), ?_⟩
      ext <;> simp [M, hy]
  change IsClosedPolyhedral (epigraph (fun y : F => f (L y)))
  rw [← hpre]
  exact hf.preimage_linearMap_of_surjective M hM

/-- Precomposition by a linear map preserves lower semicontinuity in finite
dimension. -/
theorem lowerSemicontinuous_precompose_linearMap
    [FiniteDimensional ℝ F]
    {f : E → EReal} (hlsc : LowerSemicontinuous f) (L : F →ₗ[ℝ] E) :
    LowerSemicontinuous (fun y : F => f (L y)) := by
  simpa [Function.comp] using hlsc.comp L.continuous_of_finiteDimensional

/-- Precomposition by a linear surjection preserves properness. -/
theorem isProper_precompose_linearMap_of_surjective
    {f : E → EReal} (hproper : IsProper f) (L : F →ₗ[ℝ] E)
    (hL : LinearMap.range L = ⊤) :
    IsProper (fun y : F => f (L y)) := by
  have hsurj : Function.Surjective L := LinearMap.range_eq_top.mp hL
  constructor
  · rcases hproper.1 with ⟨x, hx⟩
    rcases hsurj x with ⟨y, rfl⟩
    exact ⟨y, hx⟩
  · intro y
    exact hproper.2 (L y)

/-- Precomposition by a linear surjection preserves convex piecewise-linearity
in the project's epigraph-based sense. -/
theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_linearMap_of_surjective
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasPolyhedralEpigraph f)
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f)
    (L : F →ₗ[ℝ] E) (hL : LinearMap.range L = ⊤) :
    IsConvexPiecewiseLinear (fun y : F => f (L y)) := by
  refine ⟨isProper_precompose_linearMap_of_surjective hproper L hL, ?_⟩
  have hpoly : HasPolyhedralEpigraph (fun y : F => f (L y)) :=
    hf.hasPolyhedralEpigraph_precompose_linearMap_of_surjective L hL
  exact hpoly.hasClosedPolyhedralEpigraph_of_lowerSemicontinuous
    (lowerSemicontinuous_precompose_linearMap hlsc L)

/-- Precomposition by a linear surjection preserves convex
piecewise-linearity. -/
theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_precompose_linearMap_of_surjective
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : IsConvexPiecewiseLinear f)
    (L : F →ₗ[ℝ] E) (hL : LinearMap.range L = ⊤) :
    IsConvexPiecewiseLinear (fun y : F => f (L y)) := by
  have hpoly := IsConvexPiecewiseLinear.hasClosedPolyhedralEpigraph hf
  have hclosed :
      HasClosedPolyhedralEpigraph (fun y : F => f (L y)) :=
    hpoly.hasClosedPolyhedralEpigraph_precompose_linearMap_of_surjective L hL
  exact ⟨isProper_precompose_linearMap_of_surjective hf.isProper L hL, hclosed⟩

end LinearSurjections

section AffineDomainChanges

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Precomposition by an affine change of variables `y ↦ e y + u` preserves
polyhedral epigraphs. -/
theorem HasPolyhedralEpigraph.hasPolyhedralEpigraph_precompose_linearEquiv_add
    {f : E → EReal} (hf : HasPolyhedralEpigraph f) (e : F ≃L[ℝ] E) (u : E) :
    HasPolyhedralEpigraph (fun y : F => f (e y + u)) := by
  have hg : HasPolyhedralEpigraph (fun x : E => f (x + u)) :=
    hf.hasPolyhedralEpigraph_precompose_add u
  simpa [Function.comp] using
    hg.hasPolyhedralEpigraph_precompose_linearEquiv e

/-- Precomposition by an affine change of variables `y ↦ e y + u` preserves
properness. -/
theorem isProper_precompose_linearEquiv_add {f : E → EReal}
    (hproper : IsProper f) (e : F ≃L[ℝ] E) (u : E) :
    IsProper (fun y : F => f (e y + u)) := by
  have hg : IsProper (fun x : E => f (x + u)) :=
    isProper_precompose_add hproper u
  simpa [Function.comp] using isProper_precompose_linearEquiv hg e

/-- Precomposition by an affine change of variables `y ↦ e y + u` preserves
lower semicontinuity. -/
theorem lowerSemicontinuous_precompose_linearEquiv_add {f : E → EReal}
    (hlsc : LowerSemicontinuous f) (e : F ≃L[ℝ] E) (u : E) :
    LowerSemicontinuous (fun y : F => f (e y + u)) := by
  have hg : LowerSemicontinuous (fun x : E => f (x + u)) :=
    lowerSemicontinuous_precompose_add hlsc u
  simpa [Function.comp] using lowerSemicontinuous_precompose_linearEquiv hg e

/-- Precomposition by an affine change of variables `y ↦ e y + u` preserves
convex piecewise-linearity in the project's epigraph-based sense. -/
theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_linearEquiv_add
    {f : E → EReal} (hf : HasPolyhedralEpigraph f)
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f)
    (e : F ≃L[ℝ] E) (u : E) :
    IsConvexPiecewiseLinear (fun y : F => f (e y + u)) := by
  have hg : HasPolyhedralEpigraph (fun x : E => f (x + u)) :=
    hf.hasPolyhedralEpigraph_precompose_add u
  have hg_lsc : LowerSemicontinuous (fun x : E => f (x + u)) :=
    lowerSemicontinuous_precompose_add hlsc u
  have hg_proper : IsProper (fun x : E => f (x + u)) :=
    isProper_precompose_add hproper u
  simpa [Function.comp] using
    hg.isConvexPiecewiseLinear_precompose_linearEquiv hg_lsc hg_proper e

end AffineDomainChanges

section AffineLinearSurjections

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Precomposition by an affine surjective linear change `y ↦ L y + u`
preserves polyhedral epigraphs. -/
theorem HasPolyhedralEpigraph.hasPolyhedralEpigraph_precompose_linearMap_add_of_surjective
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasPolyhedralEpigraph f)
    (L : F →ₗ[ℝ] E) (hL : LinearMap.range L = ⊤) (u : E) :
    HasPolyhedralEpigraph (fun y : F => f (L y + u)) := by
  have hg : HasPolyhedralEpigraph (fun x : E => f (x + u)) :=
    hf.hasPolyhedralEpigraph_precompose_add u
  simpa [Function.comp] using
    hg.hasPolyhedralEpigraph_precompose_linearMap_of_surjective L hL

/-- Precomposition by an affine surjective linear change `y ↦ L y + u`
preserves properness. -/
theorem isProper_precompose_linearMap_add_of_surjective
    [FiniteDimensional ℝ F]
    {f : E → EReal} (hproper : IsProper f)
    (L : F →ₗ[ℝ] E) (hL : LinearMap.range L = ⊤) (u : E) :
    IsProper (fun y : F => f (L y + u)) := by
  have hg : IsProper (fun x : E => f (x + u)) :=
    isProper_precompose_add hproper u
  simpa [Function.comp] using
    isProper_precompose_linearMap_of_surjective hg L hL

/-- Precomposition by an affine surjective linear change `y ↦ L y + u`
preserves lower semicontinuity. -/
theorem lowerSemicontinuous_precompose_linearMap_add
    [FiniteDimensional ℝ F]
    {f : E → EReal} (hlsc : LowerSemicontinuous f)
    (L : F →ₗ[ℝ] E) (u : E) :
    LowerSemicontinuous (fun y : F => f (L y + u)) := by
  have hg : LowerSemicontinuous (fun x : E => f (x + u)) :=
    lowerSemicontinuous_precompose_add hlsc u
  simpa [Function.comp] using lowerSemicontinuous_precompose_linearMap hg L

/-- Precomposition by an affine surjective linear change `y ↦ L y + u`
preserves convex piecewise-linearity. -/
theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_linearMap_add_of_surjective
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasPolyhedralEpigraph f)
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f)
    (L : F →ₗ[ℝ] E) (hL : LinearMap.range L = ⊤) (u : E) :
    IsConvexPiecewiseLinear (fun y : F => f (L y + u)) := by
  have hg : HasPolyhedralEpigraph (fun x : E => f (x + u)) :=
    hf.hasPolyhedralEpigraph_precompose_add u
  have hg_lsc : LowerSemicontinuous (fun x : E => f (x + u)) :=
    lowerSemicontinuous_precompose_add hlsc u
  have hg_proper : IsProper (fun x : E => f (x + u)) :=
    isProper_precompose_add hproper u
  simpa [Function.comp] using
    hg.isConvexPiecewiseLinear_precompose_linearMap_of_surjective
      hg_lsc hg_proper L hL

/-- Affine surjective changes on the domain, positive vertical scaling, and
finite affine perturbations on the codomain preserve convex
piecewise-linearity. -/
theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_affineChange_of_surjective
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasPolyhedralEpigraph f)
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f)
    (L : F →ₗ[ℝ] E) (hL : LinearMap.range L = ⊤) (u : E)
    {a : ℝ} (ha : 0 < a) (l : F →ₗ[ℝ] ℝ) (c : ℝ) :
    IsConvexPiecewiseLinear (fun y : F => (a : EReal) * f (L y + u) + (l y + c : ℝ)) := by
  have hg : HasPolyhedralEpigraph (fun y : F => f (L y + u)) :=
    hf.hasPolyhedralEpigraph_precompose_linearMap_add_of_surjective L hL u
  have hg_lsc : LowerSemicontinuous (fun y : F => f (L y + u)) :=
    lowerSemicontinuous_precompose_linearMap_add hlsc L u
  have hg_proper : IsProper (fun y : F => f (L y + u)) :=
    isProper_precompose_linearMap_add_of_surjective hproper L hL u
  have hh : HasPolyhedralEpigraph (fun y : F => (a : EReal) * f (L y + u)) :=
    hg.hasPolyhedralEpigraph_const_mul ha
  have hh_lsc : LowerSemicontinuous (fun y : F => (a : EReal) * f (L y + u)) :=
    lowerSemicontinuous_const_mul hg_lsc ha
  have hh_proper : IsProper (fun y : F => (a : EReal) * f (L y + u)) :=
    isProper_const_mul hg_proper ha
  exact hh.isConvexPiecewiseLinear_addAffine hh_lsc hh_proper l c

end AffineLinearSurjections

section FullAffineChanges

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Affine changes on the domain, positive vertical scaling, and finite affine
perturbations on the codomain preserve convex piecewise-linearity. -/
theorem HasPolyhedralEpigraph.isConvexPiecewiseLinear_affineChange
    [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasPolyhedralEpigraph f)
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f)
    (e : F ≃L[ℝ] E) (u : E) {a : ℝ} (ha : 0 < a)
    (l : F →ₗ[ℝ] ℝ) (c : ℝ) :
    IsConvexPiecewiseLinear (fun y : F => (a : EReal) * f (e y + u) + (l y + c : ℝ)) := by
  have hg : HasPolyhedralEpigraph (fun y : F => f (e y + u)) :=
    hf.hasPolyhedralEpigraph_precompose_linearEquiv_add e u
  have hg_lsc : LowerSemicontinuous (fun y : F => f (e y + u)) :=
    lowerSemicontinuous_precompose_linearEquiv_add hlsc e u
  have hg_proper : IsProper (fun y : F => f (e y + u)) :=
    isProper_precompose_linearEquiv_add hproper e u
  have hh : HasPolyhedralEpigraph (fun y : F => (a : EReal) * f (e y + u)) :=
    hg.hasPolyhedralEpigraph_const_mul ha
  have hh_lsc : LowerSemicontinuous (fun y : F => (a : EReal) * f (e y + u)) :=
    lowerSemicontinuous_const_mul hg_lsc ha
  have hh_proper : IsProper (fun y : F => (a : EReal) * f (e y + u)) :=
    isProper_const_mul hg_proper ha
  exact hh.isConvexPiecewiseLinear_addAffine hh_lsc hh_proper l c

end FullAffineChanges

theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_addAffine
    [FiniteDimensional ℝ E]
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f)
    (hproper : IsProper f) (l : E →ₗ[ℝ] ℝ) (c : ℝ) :
    IsConvexPiecewiseLinear (fun x : E => f x + (l x + c : ℝ)) := by
  exact HasPolyhedralEpigraph.isConvexPiecewiseLinear_addAffine
    hf.hasPolyhedralEpigraph hf.lowerSemicontinuous hproper l c

theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_add
    [FiniteDimensional ℝ E]
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f)
    (hproper : IsProper f) (u : E) :
    IsConvexPiecewiseLinear (fun x : E => f (x + u)) := by
  exact HasPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_add
    hf.hasPolyhedralEpigraph hf.lowerSemicontinuous hproper u

theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_const_mul
    [FiniteDimensional ℝ E]
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f)
    (hproper : IsProper f) {a : ℝ} (ha : 0 < a) :
    IsConvexPiecewiseLinear (fun x : E => (a : EReal) * f x) := by
  exact HasPolyhedralEpigraph.isConvexPiecewiseLinear_const_mul
    hf.hasPolyhedralEpigraph hf.lowerSemicontinuous hproper ha

theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_affineChange_of_surjective
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f)
    (hproper : IsProper f)
    (L : F →ₗ[ℝ] E) (hL : LinearMap.range L = ⊤) (u : E)
    {a : ℝ} (ha : 0 < a) (l : F →ₗ[ℝ] ℝ) (c : ℝ) :
    IsConvexPiecewiseLinear (fun y : F => (a : EReal) * f (L y + u) + (l y + c : ℝ)) := by
  exact HasPolyhedralEpigraph.isConvexPiecewiseLinear_affineChange_of_surjective
    hf.hasPolyhedralEpigraph hf.lowerSemicontinuous hproper L hL u ha l c

theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_affineChange_of_surjective
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : IsConvexPiecewiseLinear f)
    (L : F →ₗ[ℝ] E) (hL : LinearMap.range L = ⊤) (u : E)
    {a : ℝ} (ha : 0 < a) (l : F →ₗ[ℝ] ℝ) (c : ℝ) :
    IsConvexPiecewiseLinear (fun y : F => (a : EReal) * f (L y + u) + (l y + c : ℝ)) := by
  exact hf.hasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_affineChange_of_surjective
    hf.isProper L hL u ha l c

theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_affineChange
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f)
    (hproper : IsProper f)
    (e : F ≃L[ℝ] E) (u : E) {a : ℝ} (ha : 0 < a)
    (l : F →ₗ[ℝ] ℝ) (c : ℝ) :
    IsConvexPiecewiseLinear (fun y : F => (a : EReal) * f (e y + u) + (l y + c : ℝ)) := by
  exact HasPolyhedralEpigraph.isConvexPiecewiseLinear_affineChange
    hf.hasPolyhedralEpigraph hf.lowerSemicontinuous hproper e u ha l c

theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_affineChange
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : IsConvexPiecewiseLinear f)
    (e : F ≃L[ℝ] E) (u : E) {a : ℝ} (ha : 0 < a)
    (l : F →ₗ[ℝ] ℝ) (c : ℝ) :
    IsConvexPiecewiseLinear (fun y : F => (a : EReal) * f (e y + u) + (l y + c : ℝ)) := by
  exact hf.hasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_affineChange
    hf.isProper e u ha l c

end RW
