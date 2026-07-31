/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3D: Completion of Corollary 3.33

This file supplies the nonconvex clauses of the epi-addition corollary.  The
convex equalities remain in `EpiAddition.lean`.
-/

import RockafellarWets.Chapter3.HorizonAddition

open Set EReal Topology

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section PrecompositionLemmas

variable {F G : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A non-counter-coercive function remains non-counter-coercive after
precomposition by a linear map from a finite-dimensional space. -/
theorem not_isCounterCoercive_precompose_linearMap
    {f : G → EReal} (hf : ¬ IsCounterCoercive f) (L : F →ₗ[ℝ] G) :
    ¬ IsCounterCoercive (fun x : F => f (L x)) := by
  rcases exists_affineNormLowerBound_of_not_isCounterCoercive hf with
    ⟨γ, β, hminor⟩
  let δ : ℝ := min γ 0
  let Lc : F →L[ℝ] G := L.toContinuousLinearMap
  intro hcounter
  apply hcounter (δ * ‖Lc‖)
  refine ⟨β, ?_⟩
  intro x
  have hδ : δ ≤ 0 := min_le_right _ _
  have hnorm : ‖L x‖ ≤ ‖Lc‖ * ‖x‖ := Lc.le_opNorm x
  have hreal : δ * ‖Lc‖ * ‖x‖ ≤ δ * ‖L x‖ := by
    simpa [mul_assoc] using mul_le_mul_of_nonpos_left hnorm hδ
  have hbase := (hminor.mono_slope (min_le_left γ 0)) (L x)
  apply le_trans ?_ hbase
  exact_mod_cast (by linarith [hreal])

omit [FiniteDimensional ℝ F] in
/-- Properness is preserved by precomposition with a surjective linear map. -/
theorem isProper_precompose_surjective_linearMap
    {f : G → EReal} (hf : IsProper f) (L : F →ₗ[ℝ] G)
    (hL : Function.Surjective L) :
    IsProper (fun x : F => f (L x)) := by
  constructor
  · rcases hf.1 with ⟨y, hy⟩
    rcases hL y with ⟨x, rfl⟩
    exact ⟨x, hy⟩
  · exact fun x => hf.2 (L x)

/-- Lower semicontinuity is preserved by finite-dimensional linear
precomposition. -/
theorem lowerSemicontinuous_precompose_finiteDimensional_linearMap
    {f : G → EReal} (hf : LowerSemicontinuous f) (L : F →ₗ[ℝ] G) :
    LowerSemicontinuous (fun x : F => f (L x)) := by
  simpa [Function.comp] using hf.comp L.continuous_of_finiteDimensional

/-- The general (nonconvex) horizon inequality under linear precomposition. -/
theorem horizonFunction_comp_linearMap_le
    {f : G → EReal} (L : F →ₗ[ℝ] G) (w : F) :
    horizonFunction f (L w) ≤ horizonFunction (fun x : F => f (L x)) w := by
  let M : (F × ℝ) →ₗ[ℝ] (G × ℝ) :=
    (L.comp (LinearMap.fst ℝ F ℝ)).prod (LinearMap.snd ℝ F ℝ)
  refine le_iInf ?_
  intro a
  apply horizonFunction_le_of_mem_horizonCone_epigraph
  have haimg : M (w, (a : ℝ)) ∈
      horizonCone (M '' epigraph (fun x : F => f (L x))) :=
    linearMap_image_horizonCone_subset M ⟨(w, (a : ℝ)), a.property, rfl⟩
  have hsubset : M '' epigraph (fun x : F => f (L x)) ⊆ epigraph f := by
    rintro _ ⟨⟨x, t⟩, hxt, rfl⟩
    simpa [M, mem_epigraph_iff] using hxt
  have := horizonCone_mono hsubset haimg
  simpa [M] using this

end PrecompositionLemmas

section IntegrandInequality

variable [FiniteDimensional ℝ E]

private def epiDifferenceLinearMap : E × E →ₗ[ℝ] E :=
  LinearMap.snd ℝ E E - LinearMap.fst ℝ E E

private def epiFirstLinearMap : E × E →ₗ[ℝ] E :=
  LinearMap.fst ℝ E E

omit [FiniteDimensional ℝ E] in
private theorem epiDifferenceLinearMap_surjective :
    Function.Surjective (epiDifferenceLinearMap : E × E → E) := by
  intro x
  exact ⟨(0, x), by simp [epiDifferenceLinearMap]⟩

omit [FiniteDimensional ℝ E] in
private theorem epiFirstLinearMap_surjective :
    Function.Surjective (epiFirstLinearMap : E × E → E) := by
  intro x
  exact ⟨(x, 0), by simp [epiFirstLinearMap]⟩

/-- The nonconvex estimate used in the proof of Corollary 3.33. -/
theorem add_horizonFunction_le_horizonFunction_epiSumIntegrand
    {f₁ f₂ : E → EReal}
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hnot₁ : ¬ IsCounterCoercive f₁) (hnot₂ : ¬ IsCounterCoercive f₂) :
    (fun p : E × E =>
      horizonFunction f₁ (p.2 - p.1) + horizonFunction f₂ p.1) ≤
      horizonFunction (epiSumIntegrand f₁ f₂) := by
  let A : E × E → EReal := fun p => f₁ (epiDifferenceLinearMap p)
  let B : E × E → EReal := fun p => f₂ (epiFirstLinearMap p)
  have hAproper : IsProper A :=
    isProper_precompose_surjective_linearMap hproper₁ _ epiDifferenceLinearMap_surjective
  have hBproper : IsProper B :=
    isProper_precompose_surjective_linearMap hproper₂ _ epiFirstLinearMap_surjective
  have hAlsc : LowerSemicontinuous A :=
    lowerSemicontinuous_precompose_finiteDimensional_linearMap hlsc₁ _
  have hBlsc : LowerSemicontinuous B :=
    lowerSemicontinuous_precompose_finiteDimensional_linearMap hlsc₂ _
  have hAnot : ¬ IsCounterCoercive A :=
    not_isCounterCoercive_precompose_linearMap hnot₁ _
  have hBnot : ¬ IsCounterCoercive B :=
    not_isCounterCoercive_precompose_linearMap hnot₂ _
  have hadd := add_horizonFunction_le_horizonFunction_pointwiseAdd
    hAlsc hBlsc hAproper hBproper hAnot hBnot
  intro p
  calc
    horizonFunction f₁ (p.2 - p.1) + horizonFunction f₂ p.1 ≤
        horizonFunction A p + horizonFunction B p :=
      add_le_add
        (by simpa [A, epiDifferenceLinearMap] using
          horizonFunction_comp_linearMap_le epiDifferenceLinearMap p)
        (by simpa [B, epiFirstLinearMap] using
          horizonFunction_comp_linearMap_le epiFirstLinearMap p)
    _ ≤ horizonFunction (fun p => A p + B p) p := hadd p
    _ = horizonFunction (epiSumIntegrand f₁ f₂) p := by
      rfl

end IntegrandInequality

section Corollary333a

variable [FiniteDimensional ℝ E]

/-- Corollary 3.33(a): the book's positivity condition implies the parametric
positivity condition without convexity. -/
theorem horizonFunction_epiSumIntegrand_pos_of_pos_nonconvex
    {f₁ f₂ : E → EReal}
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hnot₁ : ¬ IsCounterCoercive f₁) (hnot₂ : ¬ IsCounterCoercive f₂)
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction f₁ (-w) + horizonFunction f₂ w) :
    ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction (epiSumIntegrand f₁ f₂) (w, (0 : E)) := by
  intro w hw
  apply (hpos hw).trans_le
  simpa using
    add_horizonFunction_le_horizonFunction_epiSumIntegrand
      hlsc₁ hlsc₂ hproper₁ hproper₂ hnot₁ hnot₂ (w, (0 : E))

/-- Under the direct parametric positivity condition, epi-addition is proper. -/
theorem isProper_epiSum_of_horizon_pos
    {f₁ f₂ : E → EReal}
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction (epiSumIntegrand f₁ f₂) (w, (0 : E))) :
    IsProper (epiSum f₁ f₂) := by
  have hLB : IsLevelBoundedInXLocallyUniformly (epiSumIntegrand f₁ f₂) :=
    isLevelBoundedInXLocallyUniformly_of_horizonFunction_pos hpos
  simpa [epiSum] using
    isProper_valueFunction_of_lsc_localUniform
      (lowerSemicontinuous_epiSumIntegrand hlsc₁ hlsc₂ hproper₁ hproper₂)
      (isProper_epiSumIntegrand hproper₁ hproper₂) hLB

/-- Corollary 3.33(a), nonconvex properness clause. -/
theorem isProper_epiSum_of_pos_nonconvex
    {f₁ f₂ : E → EReal}
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hnot₁ : ¬ IsCounterCoercive f₁) (hnot₂ : ¬ IsCounterCoercive f₂)
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction f₁ (-w) + horizonFunction f₂ w) :
    IsProper (epiSum f₁ f₂) :=
  isProper_epiSum_of_horizon_pos hlsc₁ hlsc₂ hproper₁ hproper₂
    (horizonFunction_epiSumIntegrand_pos_of_pos_nonconvex
      hlsc₁ hlsc₂ hproper₁ hproper₂ hnot₁ hnot₂ hpos)

/-- Corollary 3.33(a), nonconvex lower-semicontinuity clause. -/
theorem lowerSemicontinuous_epiSum_of_pos_nonconvex
    {f₁ f₂ : E → EReal}
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hnot₁ : ¬ IsCounterCoercive f₁) (hnot₂ : ¬ IsCounterCoercive f₂)
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction f₁ (-w) + horizonFunction f₂ w) :
    LowerSemicontinuous (epiSum f₁ f₂) :=
  lowerSemicontinuous_epiSum_of_horizon_pos hlsc₁ hlsc₂ hproper₁ hproper₂
    (horizonFunction_epiSumIntegrand_pos_of_pos_nonconvex
      hlsc₁ hlsc₂ hproper₁ hproper₂ hnot₁ hnot₂ hpos)

/-- Corollary 3.33(a), nonconvex finite-attainment clause. -/
theorem exists_eq_epiSum_of_finite_of_pos_nonconvex
    {f₁ f₂ : E → EReal}
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hnot₁ : ¬ IsCounterCoercive f₁) (hnot₂ : ¬ IsCounterCoercive f₂)
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction f₁ (-w) + horizonFunction f₂ w)
    {x : E} (htop : epiSum f₁ f₂ x < ⊤) (hbot : epiSum f₁ f₂ x > ⊥) :
    ∃ w : E, epiSum f₁ f₂ x = f₁ (x - w) + f₂ w :=
  exists_eq_epiSum_of_finite_of_horizon_pos hlsc₁ hlsc₂ hproper₁ hproper₂
    (horizonFunction_epiSumIntegrand_pos_of_pos_nonconvex
      hlsc₁ hlsc₂ hproper₁ hproper₂ hnot₁ hnot₂ hpos) htop hbot

/-- Corollary 3.33(a), general horizon inequality. -/
theorem epiSum_horizonFunction_le_horizonFunction_epiSum_nonconvex
    {f₁ f₂ : E → EReal}
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hnot₁ : ¬ IsCounterCoercive f₁) (hnot₂ : ¬ IsCounterCoercive f₂)
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction f₁ (-w) + horizonFunction f₂ w) :
    epiSum (horizonFunction f₁) (horizonFunction f₂) ≤
      horizonFunction (epiSum f₁ f₂) := by
  have hposI := horizonFunction_epiSumIntegrand_pos_of_pos_nonconvex
    hlsc₁ hlsc₂ hproper₁ hproper₂ hnot₁ hnot₂ hpos
  have hEq := horizonFunction_epiSum_eq_valueFunction_horizonIntegrand
    hlsc₁ hlsc₂ hproper₁ hproper₂ hposI
  intro x
  rw [hEq]
  refine le_iInf ?_
  intro w
  exact (iInf_le
    (fun v : E => horizonFunction f₁ (x - v) + horizonFunction f₂ v) w).trans
      (add_horizonFunction_le_horizonFunction_epiSumIntegrand
        hlsc₁ hlsc₂ hproper₁ hproper₂ hnot₁ hnot₂ (w, x))

end Corollary333a

section Corollary333b

variable [FiniteDimensional ℝ E]

/-- The coercive horizon conclusion of Theorem 3.26(b), without convexity. -/
theorem horizonFunction_eq_top_of_isCoercive_nonconvex
    {f : E → EReal} (hf : IsCoercive f) {w : E} (hw : w ≠ 0) :
    horizonFunction f w = ⊤ := by
  have hpos : 0 < horizonFunction f w := by
    rcases hf 1 zero_lt_one with ⟨β, hβ⟩
    have hle := hβ.le_horizonFunction w
    have : (0 : EReal) < ((‖w‖ : ℝ) : EReal) := by
      exact_mod_cast norm_pos_iff.mpr hw
    exact this.trans_le (by simpa using hle)
  by_contra htop
  have hbot : horizonFunction f w ≠ ⊥ :=
    ne_of_gt ((show (⊥ : EReal) < 0 by simp).trans hpos)
  let γ : ℝ := ((horizonFunction f w).toReal + 1) / ‖w‖
  have hγ : 0 < γ := by
    have hreal : 0 < (horizonFunction f w).toReal :=
      EReal.toReal_pos hpos htop
    dsimp [γ]
    positivity
  rcases hf γ hγ with ⟨β, hβ⟩
  have hle := hβ.le_horizonFunction w
  have hcoe : (((γ * ‖w‖ : ℝ)) : EReal) ≤ horizonFunction f w := hle
  rw [← EReal.coe_toReal htop hbot] at hcoe
  have hreal : γ * ‖w‖ ≤ (horizonFunction f w).toReal := by
    exact_mod_cast hcoe
  dsimp [γ] at hreal
  field_simp [norm_ne_zero_iff.mpr hw] at hreal
  linarith

/-- A non-counter-coercive function has no bottom-valued horizon directions. -/
theorem bot_lt_horizonFunction_of_not_isCounterCoercive
    {f : E → EReal} (hf : ¬ IsCounterCoercive f) (w : E) :
    ⊥ < horizonFunction f w := by
  rcases exists_affineNormLowerBound_of_not_isCounterCoercive hf with
    ⟨γ, β, hβ⟩
  exact (EReal.bot_lt_coe (γ * ‖w‖)).trans_le (hβ.le_horizonFunction w)

/-- A non-counter-coercive function has horizon value zero at the origin. -/
theorem horizonFunction_zero_eq_zero_of_not_isCounterCoercive
    {f : E → EReal} (hf : ¬ IsCounterCoercive f) :
    horizonFunction f (0 : E) = 0 := by
  apply le_antisymm
  · exact horizonFunction_le_of_mem_horizonCone_epigraph
      (zero_mem_horizonCone (epigraph f))
  · rcases exists_affineNormLowerBound_of_not_isCounterCoercive hf with
      ⟨γ, β, hβ⟩
    simpa using hβ.le_horizonFunction (0 : E)

/-- In the nonconvex coercive case, epi-addition of horizon functions still
collapses to the left horizon function. -/
theorem epiSum_horizonFunction_eq_left_of_isCoercive_nonconvex
    {f₁ f₂ : E → EReal}
    (hnot₁ : ¬ IsCounterCoercive f₁) (hcoercive₂ : IsCoercive f₂) :
    epiSum (horizonFunction f₁) (horizonFunction f₂) = horizonFunction f₁ := by
  ext x
  rw [epiSum_apply]
  apply le_antisymm
  · have h := iInf_le
      (fun w : E => horizonFunction f₁ (x - w) + horizonFunction f₂ w) (0 : E)
    simpa [horizonFunction_zero_eq_zero_of_not_isCounterCoercive
      (not_isCounterCoercive_of_isLevelCoercive
        (isLevelCoercive_of_isCoercive hcoercive₂))] using h
  · refine le_iInf ?_
    intro w
    by_cases hw : w = 0
    · simp [hw, horizonFunction_zero_eq_zero_of_not_isCounterCoercive
        (not_isCounterCoercive_of_isLevelCoercive
          (isLevelCoercive_of_isCoercive hcoercive₂))]
    · have htop : horizonFunction f₂ w = ⊤ :=
        horizonFunction_eq_top_of_isCoercive_nonconvex hcoercive₂ hw
      have hnebot : horizonFunction f₁ (x - w) ≠ ⊥ :=
        ne_of_gt (bot_lt_horizonFunction_of_not_isCounterCoercive hnot₁ (x - w))
      rw [htop, EReal.add_top_of_ne_bot hnebot]
      exact le_top

/-- Corollary 3.33(b): coercivity and non-counter-coercivity imply the
positivity hypothesis in part (a), without convexity. -/
theorem horizonFunction_epiSum_pos_of_isCoercive_nonconvex
    {f₁ f₂ : E → EReal}
    (hnot₁ : ¬ IsCounterCoercive f₁) (hcoercive₂ : IsCoercive f₂) :
    ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction f₁ (-w) + horizonFunction f₂ w := by
  intro w hw
  have htop := horizonFunction_eq_top_of_isCoercive_nonconvex hcoercive₂ hw
  have hnebot : horizonFunction f₁ (-w) ≠ ⊥ :=
    ne_of_gt (bot_lt_horizonFunction_of_not_isCounterCoercive hnot₁ (-w))
  rw [htop, EReal.add_top_of_ne_bot hnebot]
  exact EReal.coe_lt_top 0

/-- Corollary 3.33(b), bundled nonconvex conclusion. -/
theorem epiSum_regular_of_isCoercive_nonconvex
    {f₁ f₂ : E → EReal}
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hnot₁ : ¬ IsCounterCoercive f₁) (hcoercive₂ : IsCoercive f₂) :
    IsProper (epiSum f₁ f₂) ∧ LowerSemicontinuous (epiSum f₁ f₂) ∧
      horizonFunction f₁ ≤ horizonFunction (epiSum f₁ f₂) := by
  have hnot₂ : ¬ IsCounterCoercive f₂ :=
    not_isCounterCoercive_of_isLevelCoercive
      (isLevelCoercive_of_isCoercive hcoercive₂)
  have hpos := horizonFunction_epiSum_pos_of_isCoercive_nonconvex hnot₁ hcoercive₂
  refine ⟨isProper_epiSum_of_pos_nonconvex
      hlsc₁ hlsc₂ hproper₁ hproper₂ hnot₁ hnot₂ hpos,
    lowerSemicontinuous_epiSum_of_pos_nonconvex
      hlsc₁ hlsc₂ hproper₁ hproper₂ hnot₁ hnot₂ hpos, ?_⟩
  rw [← epiSum_horizonFunction_eq_left_of_isCoercive_nonconvex hnot₁ hcoercive₂]
  exact epiSum_horizonFunction_le_horizonFunction_epiSum_nonconvex
    hlsc₁ hlsc₂ hproper₁ hproper₂ hnot₁ hnot₂ hpos

/-- Corollary 3.33(b), nonconvex finite-attainment clause. -/
theorem exists_eq_epiSum_of_finite_of_isCoercive_nonconvex
    {f₁ f₂ : E → EReal}
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hnot₁ : ¬ IsCounterCoercive f₁) (hcoercive₂ : IsCoercive f₂)
    {x : E} (htop : epiSum f₁ f₂ x < ⊤) (hbot : epiSum f₁ f₂ x > ⊥) :
    ∃ w : E, epiSum f₁ f₂ x = f₁ (x - w) + f₂ w := by
  have hnot₂ : ¬ IsCounterCoercive f₂ :=
    not_isCounterCoercive_of_isLevelCoercive
      (isLevelCoercive_of_isCoercive hcoercive₂)
  exact exists_eq_epiSum_of_finite_of_pos_nonconvex
    hlsc₁ hlsc₂ hproper₁ hproper₂ hnot₁ hnot₂
      (horizonFunction_epiSum_pos_of_isCoercive_nonconvex hnot₁ hcoercive₂)
      htop hbot

end Corollary333b

end RW
