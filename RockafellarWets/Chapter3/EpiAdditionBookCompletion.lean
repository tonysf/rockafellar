/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3D: Book-form completion of Corollary 3.33(a)

The first nonconvex implementation of Corollary 3.33(a) carried explicit
non-counter-coercivity hypotheses.  For proper lower-semicontinuous functions
these follow from the book's horizon-sum positivity condition: positivity
rules out a bottom horizon value in every nonzero direction, compactness of
the unit sphere makes the exclusion uniform, and Theorem 3.26 identifies the
uniform bound with non-counter-coercivity.
-/

import RockafellarWets.Chapter3.CoercivityHorizonEquivalence
import RockafellarWets.Chapter3.EpiAdditionCompletion

open Set EReal Filter Topology Metric

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section SphereInf

variable [FiniteDimensional ℝ E]

/-- Pointwise non-bottom values of a horizon function on the unit sphere give
a uniform non-bottom unit-sphere infimum. -/
private theorem bot_lt_unitSphereHorizonInf_of_forall_ne_zero
    {f : E → EReal}
    (hbot : ∀ ⦃w : E⦄, w ≠ 0 → ⊥ < horizonFunction f w) :
    ⊥ < unitSphereHorizonInf f := by
  by_cases hne : (sphere (0 : E) 1).Nonempty
  · obtain ⟨u, hu, humin⟩ :=
      LowerSemicontinuousOn.exists_isMinOn hne
        (isCompact_sphere (0 : E) 1)
        ((lowerSemicontinuous_horizonFunction f).lowerSemicontinuousOn _)
    have hu0 : u ≠ 0 := by
      intro hz
      rw [hz, mem_sphere, dist_zero_right, norm_zero] at hu
      norm_num at hu
    have heq :
        unitSphereHorizonInf f = horizonFunction f u := by
      unfold unitSphereHorizonInf
      apply le_antisymm
      · exact iInf_le
          (fun w : sphere (0 : E) 1 ↦ horizonFunction f (w : E))
          (⟨u, hu⟩ : sphere (0 : E) 1)
      · exact le_iInf fun w ↦ humin w.property
    rw [heq]
    exact hbot hu0
  · have hempty : sphere (0 : E) 1 = ∅ :=
      not_nonempty_iff_eq_empty.mp hne
    letI : IsEmpty (sphere (0 : E) 1) :=
      Set.isEmpty_coe_sort.mpr hempty
    unfold unitSphereHorizonInf
    rw [iInf_of_empty]
    simp

/-- The book's paired horizon positivity condition forces the first summand
to be non-counter-coercive. -/
theorem not_isCounterCoercive_left_of_horizon_sum_pos
    {f₁ f₂ : E → EReal}
    (hlsc₁ : LowerSemicontinuous f₁) (hproper₁ : IsProper f₁)
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction f₁ (-w) + horizonFunction f₂ w) :
    ¬ IsCounterCoercive f₁ := by
  apply (not_isCounterCoercive_iff_bot_lt_unitSphereHorizonInf
    hlsc₁ hproper₁).2
  apply bot_lt_unitSphereHorizonInf_of_forall_ne_zero
  intro w hw
  have hsum := hpos (neg_ne_zero.mpr hw)
  have hne : horizonFunction f₁ w ≠ ⊥ := by
    intro hbot
    rw [neg_neg, hbot] at hsum
    simp at hsum
  exact bot_lt_iff_ne_bot.mpr hne

/-- The book's paired horizon positivity condition forces the second summand
to be non-counter-coercive. -/
theorem not_isCounterCoercive_right_of_horizon_sum_pos
    {f₁ f₂ : E → EReal}
    (hlsc₂ : LowerSemicontinuous f₂) (hproper₂ : IsProper f₂)
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction f₁ (-w) + horizonFunction f₂ w) :
    ¬ IsCounterCoercive f₂ := by
  apply (not_isCounterCoercive_iff_bot_lt_unitSphereHorizonInf
    hlsc₂ hproper₂).2
  apply bot_lt_unitSphereHorizonInf_of_forall_ne_zero
  intro w hw
  have hsum := hpos hw
  have hne : horizonFunction f₂ w ≠ ⊥ := by
    intro hbot
    rw [hbot] at hsum
    simp at hsum
  exact bot_lt_iff_ne_bot.mpr hne

end SphereInf

section Corollary333a

variable [FiniteDimensional ℝ E]

/-- Corollary 3.33(a), exact book form: paired horizon positivity implies the
parametric horizon positivity needed for epi-addition, without separately
assuming either summand is non-counter-coercive. -/
theorem horizonFunction_epiSumIntegrand_pos_of_pos_book
    {f₁ f₂ : E → EReal}
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction f₁ (-w) + horizonFunction f₂ w) :
    ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction (epiSumIntegrand f₁ f₂) (w, (0 : E)) := by
  exact horizonFunction_epiSumIntegrand_pos_of_pos_nonconvex
    hlsc₁ hlsc₂ hproper₁ hproper₂
    (not_isCounterCoercive_left_of_horizon_sum_pos hlsc₁ hproper₁ hpos)
    (not_isCounterCoercive_right_of_horizon_sum_pos hlsc₂ hproper₂ hpos)
    hpos

/-- Corollary 3.33(a), properness in the exact book form. -/
theorem isProper_epiSum_of_pos_book
    {f₁ f₂ : E → EReal}
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction f₁ (-w) + horizonFunction f₂ w) :
    IsProper (epiSum f₁ f₂) :=
  isProper_epiSum_of_horizon_pos hlsc₁ hlsc₂ hproper₁ hproper₂
    (horizonFunction_epiSumIntegrand_pos_of_pos_book
      hlsc₁ hlsc₂ hproper₁ hproper₂ hpos)

/-- Corollary 3.33(a), lower semicontinuity in the exact book form. -/
theorem lowerSemicontinuous_epiSum_of_pos_book
    {f₁ f₂ : E → EReal}
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction f₁ (-w) + horizonFunction f₂ w) :
    LowerSemicontinuous (epiSum f₁ f₂) :=
  lowerSemicontinuous_epiSum_of_horizon_pos
    hlsc₁ hlsc₂ hproper₁ hproper₂
    (horizonFunction_epiSumIntegrand_pos_of_pos_book
      hlsc₁ hlsc₂ hproper₁ hproper₂ hpos)

/-- Corollary 3.33(a), finite attainment in the exact book form. -/
theorem exists_eq_epiSum_of_finite_of_pos_book
    {f₁ f₂ : E → EReal}
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction f₁ (-w) + horizonFunction f₂ w)
    {x : E} (htop : epiSum f₁ f₂ x < ⊤)
    (hbot : epiSum f₁ f₂ x > ⊥) :
    ∃ w : E, epiSum f₁ f₂ x = f₁ (x - w) + f₂ w :=
  exists_eq_epiSum_of_finite_of_horizon_pos
    hlsc₁ hlsc₂ hproper₁ hproper₂
    (horizonFunction_epiSumIntegrand_pos_of_pos_book
      hlsc₁ hlsc₂ hproper₁ hproper₂ hpos)
    htop hbot

/-- Corollary 3.33(a), general horizon inequality in the exact book form. -/
theorem epiSum_horizonFunction_le_horizonFunction_epiSum_book
    {f₁ f₂ : E → EReal}
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction f₁ (-w) + horizonFunction f₂ w) :
    epiSum (horizonFunction f₁) (horizonFunction f₂) ≤
      horizonFunction (epiSum f₁ f₂) := by
  exact epiSum_horizonFunction_le_horizonFunction_epiSum_nonconvex
    hlsc₁ hlsc₂ hproper₁ hproper₂
    (not_isCounterCoercive_left_of_horizon_sum_pos hlsc₁ hproper₁ hpos)
    (not_isCounterCoercive_right_of_horizon_sum_pos hlsc₂ hproper₂ hpos)
    hpos

end Corollary333a

end RW
