/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3G*: Epigraphical Polyhedral Operations

This file packages epigraphical addition, value functions, and their polyhedral regularity.
-/

import RockafellarWets.Chapter3.PolyhedralOperations.Horizon

open Set EReal
open scoped Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

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

theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_epiSumIntegrand
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hf₁ : HasClosedPolyhedralEpigraph f₁) (hf₂ : HasClosedPolyhedralEpigraph f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂) :
    HasClosedPolyhedralEpigraph (RW.epiSumIntegrand f₁ f₂) := by
  exact HasPolyhedralEpigraph.hasClosedPolyhedralEpigraph_epiSumIntegrand
    hf₁.hasPolyhedralEpigraph hf₂.hasPolyhedralEpigraph
    hf₁.lowerSemicontinuous hf₂.lowerSemicontinuous
    hproper₁ hproper₂

theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_epiSumIntegrand
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hf₁ : HasClosedPolyhedralEpigraph f₁) (hf₂ : HasClosedPolyhedralEpigraph f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂) :
    IsConvexPiecewiseLinear (RW.epiSumIntegrand f₁ f₂) := by
  refine ⟨isProper_epiSumIntegrand hproper₁ hproper₂, ?_⟩
  exact hf₁.hasClosedPolyhedralEpigraph_epiSumIntegrand hf₂ hproper₁ hproper₂

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

theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_valueFunction_of_lsc_localUniform
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E × F → EReal} (hf : HasClosedPolyhedralEpigraph f)
    (hLB : IsLevelBoundedInXLocallyUniformly f) :
    HasClosedPolyhedralEpigraph (valueFunction f) := by
  let hlsc : LowerSemicontinuous f := hf.lowerSemicontinuous
  change IsClosedPolyhedral (epigraph (valueFunction f))
  rw [epigraph_valueFunction_eq_valueProjection_image_epigraph_of_lsc_localUniform
    (f := f) hlsc hLB]
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

theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_valueFunction_of_lsc_localUniform
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E × F → EReal} (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f)
    (hLB : IsLevelBoundedInXLocallyUniformly f) :
    IsConvexPiecewiseLinear (valueFunction f) := by
  let hlsc : LowerSemicontinuous f := hf.lowerSemicontinuous
  refine ⟨isProper_valueFunction_of_lsc_localUniform hlsc hproper hLB, ?_⟩
  exact hf.hasClosedPolyhedralEpigraph_valueFunction_of_lsc_localUniform hLB

theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_valueFunction_of_lsc_localUniform
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E × F → EReal} (hf : IsConvexPiecewiseLinear f)
    (hLB : IsLevelBoundedInXLocallyUniformly f) :
    IsConvexPiecewiseLinear (valueFunction f) := by
  exact hf.hasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_valueFunction_of_lsc_localUniform
    hf.isProper hLB

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

theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_epiSum_of_horizon_pos
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hf₁ : HasClosedPolyhedralEpigraph f₁) (hf₂ : HasClosedPolyhedralEpigraph f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction (RW.epiSumIntegrand f₁ f₂) (w, (0 : E))) :
    HasClosedPolyhedralEpigraph (epiSum f₁ f₂) := by
  exact HasPolyhedralEpigraph.hasClosedPolyhedralEpigraph_epiSum_of_horizon_pos
    hf₁.hasPolyhedralEpigraph hf₂.hasPolyhedralEpigraph
    hf₁.lowerSemicontinuous hf₂.lowerSemicontinuous
    hproper₁ hproper₂ hpos

theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_epiSum_of_pos
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hf₁ : HasClosedPolyhedralEpigraph f₁) (hf₂ : HasClosedPolyhedralEpigraph f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction f₁ (-w) + horizonFunction f₂ w) :
    HasClosedPolyhedralEpigraph (epiSum f₁ f₂) := by
  exact HasPolyhedralEpigraph.hasClosedPolyhedralEpigraph_epiSum_of_pos
    hf₁.hasPolyhedralEpigraph hf₂.hasPolyhedralEpigraph
    hf₁.lowerSemicontinuous hf₂.lowerSemicontinuous
    hproper₁ hproper₂ hpos

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

theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_epiSum_of_horizon_pos
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hf₁ : HasClosedPolyhedralEpigraph f₁) (hf₂ : HasClosedPolyhedralEpigraph f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction (RW.epiSumIntegrand f₁ f₂) (w, (0 : E))) :
    IsConvexPiecewiseLinear (epiSum f₁ f₂) := by
  exact HasPolyhedralEpigraph.isConvexPiecewiseLinear_epiSum_of_horizon_pos
    hf₁.hasPolyhedralEpigraph hf₂.hasPolyhedralEpigraph
    hf₁.lowerSemicontinuous hf₂.lowerSemicontinuous
    hproper₁ hproper₂ hpos

theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_epiSum_of_pos
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hf₁ : HasClosedPolyhedralEpigraph f₁) (hf₂ : HasClosedPolyhedralEpigraph f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction f₁ (-w) + horizonFunction f₂ w) :
    IsConvexPiecewiseLinear (epiSum f₁ f₂) := by
  exact HasPolyhedralEpigraph.isConvexPiecewiseLinear_epiSum_of_pos
    hf₁.hasPolyhedralEpigraph hf₂.hasPolyhedralEpigraph
    hf₁.lowerSemicontinuous hf₂.lowerSemicontinuous
    hproper₁ hproper₂ hpos

theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_epiSum_of_isCoercive
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hf₁ : HasClosedPolyhedralEpigraph f₁) (hf₂ : HasClosedPolyhedralEpigraph f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hcoercive₂ : RW.IsCoercive f₂) :
    IsConvexPiecewiseLinear (epiSum f₁ f₂) := by
  exact HasPolyhedralEpigraph.isConvexPiecewiseLinear_epiSum_of_isCoercive
    hf₁.hasPolyhedralEpigraph hf₂.hasPolyhedralEpigraph
    hf₁.lowerSemicontinuous hf₂.lowerSemicontinuous
    hproper₁ hproper₂ hcoercive₂

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

end RW
