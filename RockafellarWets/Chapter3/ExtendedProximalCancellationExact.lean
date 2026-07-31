/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3: Exact extended-real proximal cancellation

This file proves the exact extended-real form of Corollary 3.37.  Equality of
one positive-parameter proximal mapping determines proper closed convex
functions up to addition of a finite constant, without coercivity or
full-domain assumptions.
-/

import RockafellarWets.Chapter3.ExtendedProximalCancellationCompletion
import RockafellarWets.Chapter3.ERealFunctionShift
import Mathlib.Analysis.Calculus.MeanValue

open Bornology EReal Set Topology

noncomputable section

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The real representative of a finite extended-real Moreau envelope. -/
private def finiteMoreauEnvelope
    (f : E → EReal) (lam : ℝ) (x : E) : ℝ :=
  (moreauEnvelopeEReal f lam x).toReal

/-- Comparing an extended-real Moreau minimizer at `x` with the same
candidate at `y` bounds the increment of the finite real representatives of
the envelopes. -/
private theorem finiteMoreauEnvelope_increment_le_of_mem_proximal
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {f : E → EReal}
    (hconv : Convex ℝ (epigraph f))
    (hlsc : LowerSemicontinuous f)
    (hproper : IsProper f)
    {lam : ℝ} (hlam : 0 < lam)
    {P : E → E} {x y : E}
    (hx : P x ∈ proximalMappingEReal f lam x) :
    finiteMoreauEnvelope f lam y - finiteMoreauEnvelope f lam x ≤
      (1 / (2 * lam)) * (‖P x - y‖ ^ 2 - ‖P x - x‖ ^ 2) := by
  let fp : ℝ := (f (P x)).toReal
  have hPxDom := mem_effectiveDomain_of_mem_proximalMappingEReal
    hconv hlsc hproper hlam hx
  have hfpTop : f (P x) ≠ ⊤ :=
    ne_of_lt ((mem_effectiveDomain_iff f (P x)).mp hPxDom)
  have hfpBot : f (P x) ≠ ⊥ := ne_of_gt (hproper.2 (P x))
  have hfp : f (P x) = (fp : EReal) :=
    (EReal.coe_toReal hfpTop hfpBot).symm
  have henvxFin := moreauEnvelopeEReal_finite
    hconv hlsc hproper hlam x
  have henvyFin := moreauEnvelopeEReal_finite
    hconv hlsc hproper hlam y
  have henvx : moreauEnvelopeEReal f lam x =
      (finiteMoreauEnvelope f lam x : EReal) :=
    (EReal.coe_toReal (ne_of_lt henvxFin.2) (ne_of_gt henvxFin.1)).symm
  have henvy : moreauEnvelopeEReal f lam y =
      (finiteMoreauEnvelope f lam y : EReal) :=
    (EReal.coe_toReal (ne_of_lt henvyFin.2) (ne_of_gt henvyFin.1)).symm
  have hcandE : moreauEnvelopeEReal f lam y ≤
      proximalObjectiveEReal f lam y (P x) := by
    rw [moreauEnvelopeEReal]
    exact iInf_le _ (P x)
  have hcand : finiteMoreauEnvelope f lam y ≤
      fp + (1 / (2 * lam)) * ‖P x - y‖ ^ 2 := by
    rw [henvy, proximalObjectiveEReal, hfp, ← EReal.coe_add] at hcandE
    exact EReal.coe_le_coe_iff.mp hcandE
  have hminE : proximalObjectiveEReal f lam x (P x) =
      moreauEnvelopeEReal f lam x :=
    mem_proximalMappingEReal_iff.mp hx
  have hmin : fp + (1 / (2 * lam)) * ‖P x - x‖ ^ 2 =
      finiteMoreauEnvelope f lam x := by
    rw [proximalObjectiveEReal, hfp, ← EReal.coe_add, henvx] at hminE
    exact EReal.coe_eq_coe_iff.mp hminE
  linarith

/-- A common Lipschitz extended-real proximal selection gives a quadratic
increment bound for the difference of the finite envelope representatives. -/
private theorem finiteMoreauEnvelope_sub_quadratic_bound_of_common_selection
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {f₁ f₂ : E → EReal}
    (hconv₁ : Convex ℝ (epigraph f₁))
    (hlsc₁ : LowerSemicontinuous f₁)
    (hproper₁ : IsProper f₁)
    (hconv₂ : Convex ℝ (epigraph f₂))
    (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₂ : IsProper f₂)
    {lam : ℝ} (hlam : 0 < lam)
    {K : NNReal} {P : E → E} (hP : LipschitzWith K P)
    (hP₁ : ∀ x : E, P x ∈ proximalMappingEReal f₁ lam x)
    (hP₂ : ∀ x : E, P x ∈ proximalMappingEReal f₂ lam x)
    (x y : E) :
    |(finiteMoreauEnvelope f₁ lam y - finiteMoreauEnvelope f₂ lam y) -
        (finiteMoreauEnvelope f₁ lam x - finiteMoreauEnvelope f₂ lam x)| ≤
      ((K : ℝ) / lam) * ‖y - x‖ ^ 2 := by
  let a : ℝ := 1 / (2 * lam)
  let A : ℝ := a * (‖P x - y‖ ^ 2 - ‖P x - x‖ ^ 2)
  let B : ℝ := a * (‖P y - y‖ ^ 2 - ‖P y - x‖ ^ 2)
  have h₁upper :
      finiteMoreauEnvelope f₁ lam y - finiteMoreauEnvelope f₁ lam x ≤ A := by
    simpa only [a, A] using
      finiteMoreauEnvelope_increment_le_of_mem_proximal
        hconv₁ hlsc₁ hproper₁ hlam (hP₁ x : _)
  have h₁lower : B ≤
      finiteMoreauEnvelope f₁ lam y - finiteMoreauEnvelope f₁ lam x := by
    have h := finiteMoreauEnvelope_increment_le_of_mem_proximal
      hconv₁ hlsc₁ hproper₁ hlam
      (hP₁ y : P y ∈ proximalMappingEReal f₁ lam y)
      (y := x)
    dsimp only [a, B]
    linarith
  have h₂upper :
      finiteMoreauEnvelope f₂ lam y - finiteMoreauEnvelope f₂ lam x ≤ A := by
    simpa only [a, A] using
      finiteMoreauEnvelope_increment_le_of_mem_proximal
        hconv₂ hlsc₂ hproper₂ hlam (hP₂ x : _)
  have h₂lower : B ≤
      finiteMoreauEnvelope f₂ lam y - finiteMoreauEnvelope f₂ lam x := by
    have h := finiteMoreauEnvelope_increment_le_of_mem_proximal
      hconv₂ hlsc₂ hproper₂ hlam
      (hP₂ y : P y ∈ proximalMappingEReal f₂ lam y)
      (y := x)
    dsimp only [a, B]
    linarith
  have habs :
      |(finiteMoreauEnvelope f₁ lam y - finiteMoreauEnvelope f₂ lam y) -
          (finiteMoreauEnvelope f₁ lam x - finiteMoreauEnvelope f₂ lam x)| ≤
        A - B := by
    rw [abs_le]
    constructor <;> linarith
  have hgap : A - B =
      (1 / lam) * inner ℝ (y - x) (P y - P x) := by
    dsimp only [a, A, B]
    simp only [norm_sub_sq_real, inner_sub_left, inner_sub_right]
    rw [real_inner_comm (P x) y, real_inner_comm (P x) x,
      real_inner_comm (P y) y, real_inner_comm (P y) x]
    field_simp [ne_of_gt hlam]
    ring
  calc
    |(finiteMoreauEnvelope f₁ lam y - finiteMoreauEnvelope f₂ lam y) -
        (finiteMoreauEnvelope f₁ lam x - finiteMoreauEnvelope f₂ lam x)|
        ≤ A - B := habs
    _ = (1 / lam) * inner ℝ (y - x) (P y - P x) := hgap
    _ ≤ (1 / lam) * |inner ℝ (y - x) (P y - P x)| := by
      gcongr
      exact le_abs_self _
    _ ≤ (1 / lam) * (‖y - x‖ * ‖P y - P x‖) := by
      gcongr
      exact abs_real_inner_le_norm _ _
    _ ≤ (1 / lam) * (‖y - x‖ * ((K : ℝ) * ‖y - x‖)) := by
      gcongr
      simpa only [dist_eq_norm] using hP.dist_le_mul y x
    _ = ((K : ℝ) / lam) * ‖y - x‖ ^ 2 := by ring

/-- A real-valued function with a global quadratic increment bound has zero
Fréchet derivative. -/
private theorem hasFDerivAt_zero_of_quadratic_bound_ereal
    {D : E → ℝ} {K : ℝ} (x : E)
    (hD : ∀ y : E, |D y - D x| ≤ K * ‖y - x‖ ^ 2) :
    HasFDerivAt D (0 : E →L[ℝ] ℝ) x := by
  rw [hasFDerivAt_iff_tendsto]
  apply squeeze_zero (g := fun y : E ↦ K * ‖y - x‖)
  · intro y
    positivity
  · intro y
    simp only [ContinuousLinearMap.zero_apply, sub_zero, Real.norm_eq_abs]
    by_cases hy : y = x
    · simp [hy]
    · have hnorm : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hy)
      calc
        ‖y - x‖⁻¹ * |D y - D x| ≤
            ‖y - x‖⁻¹ * (K * ‖y - x‖ ^ 2) := by
          gcongr
          exact hD y
        _ = K * ‖y - x‖ := by
          field_simp
  · simpa only [mul_zero] using
      tendsto_const_nhds.mul (tendsto_norm_sub_self x)

/-- A common finite-Lipschitz proximal selection forces two finite
extended-real Moreau envelopes to differ by a real constant. -/
theorem moreauEnvelopeEReal_eq_add_const_of_common_lipschitz_proximalSelection
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {f₁ f₂ : E → EReal}
    (hconv₁ : Convex ℝ (epigraph f₁))
    (hlsc₁ : LowerSemicontinuous f₁)
    (hproper₁ : IsProper f₁)
    (hconv₂ : Convex ℝ (epigraph f₂))
    (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₂ : IsProper f₂)
    {lam : ℝ} (hlam : 0 < lam)
    {K : NNReal} {P : E → E} (hP : LipschitzWith K P)
    (hP₁ : ∀ x : E, P x ∈ proximalMappingEReal f₁ lam x)
    (hP₂ : ∀ x : E, P x ∈ proximalMappingEReal f₂ lam x) :
    ∃ c : ℝ, moreauEnvelopeEReal f₁ lam =
      fun x ↦ moreauEnvelopeEReal f₂ lam x + (c : EReal) := by
  let D : E → ℝ := fun x ↦
    finiteMoreauEnvelope f₁ lam x - finiteMoreauEnvelope f₂ lam x
  have hquad (x y : E) : |D y - D x| ≤
      ((K : ℝ) / lam) * ‖y - x‖ ^ 2 := by
    exact finiteMoreauEnvelope_sub_quadratic_bound_of_common_selection
      hconv₁ hlsc₁ hproper₁ hconv₂ hlsc₂ hproper₂
      hlam hP hP₁ hP₂ x y
  have hderiv (x : E) : HasFDerivAt D 0 x :=
    hasFDerivAt_zero_of_quadratic_bound_ereal x (hquad x)
  have hdiff : Differentiable ℝ D := fun x ↦ (hderiv x).differentiableAt
  have hfderiv : ∀ x : E, fderiv ℝ D x = 0 :=
    fun x ↦ (hderiv x).fderiv
  let x₀ : E := 0
  let c : ℝ := D x₀
  have hconst (x : E) : D x = c :=
    is_const_of_fderiv_eq_zero hdiff hfderiv x x₀
  refine ⟨c, funext fun x ↦ ?_⟩
  have henv₁Fin := moreauEnvelopeEReal_finite
    hconv₁ hlsc₁ hproper₁ hlam x
  have henv₂Fin := moreauEnvelopeEReal_finite
    hconv₂ hlsc₂ hproper₂ hlam x
  have henv₁ : moreauEnvelopeEReal f₁ lam x =
      (finiteMoreauEnvelope f₁ lam x : EReal) :=
    (EReal.coe_toReal (ne_of_lt henv₁Fin.2) (ne_of_gt henv₁Fin.1)).symm
  have henv₂ : moreauEnvelopeEReal f₂ lam x =
      (finiteMoreauEnvelope f₂ lam x : EReal) :=
    (EReal.coe_toReal (ne_of_lt henv₂Fin.2) (ne_of_gt henv₂Fin.1)).symm
  rw [henv₁, henv₂, ← EReal.coe_add]
  apply congrArg (fun r : ℝ ↦ (r : EReal))
  have hx := hconst x
  dsimp only [D] at hx
  linarith

/-- **Corollary 3.37 (exact extended-real form, forward direction).** Equality
of one positive-parameter proximal mapping determines two proper closed convex
functions up to addition of a finite real constant. -/
theorem corollary337_eq_add_const_of_proximalMappingEReal_eq
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {f₁ f₂ : E → EReal}
    (hconv₁ : Convex ℝ (epigraph f₁))
    (hlsc₁ : LowerSemicontinuous f₁)
    (hproper₁ : IsProper f₁)
    (hconv₂ : Convex ℝ (epigraph f₂))
    (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₂ : IsProper f₂)
    {lam : ℝ} (hlam : 0 < lam)
    (hprox : proximalMappingEReal f₁ lam = proximalMappingEReal f₂ lam) :
    ∃ c : ℝ, f₁ = fun x ↦ f₂ x + (c : EReal) := by
  rcases hasLipschitzProximalSelectionEReal
      hconv₁ hlsc₁ hproper₁ hlam with ⟨K, P, hP, hP₁⟩
  have hP₂ : ∀ x : E, P x ∈ proximalMappingEReal f₂ lam x := by
    intro x
    rw [← congrFun hprox x]
    exact hP₁ x
  obtain ⟨c, henv⟩ :=
    moreauEnvelopeEReal_eq_add_const_of_common_lipschitz_proximalSelection
      hconv₁ hlsc₁ hproper₁ hconv₂ hlsc₂ hproper₂
      hlam hP hP₁ hP₂
  refine ⟨c, ?_⟩
  have hshift := moreauEnvelopeEReal_add_const f₂ c lam
  exact corollary336_eq_of_moreauEnvelopeEReal_eq
    hconv₁ hlsc₁ hproper₁
    (convex_epigraph_add_const_ereal hconv₂ c)
    (lowerSemicontinuous_add_const_ereal hlsc₂ c)
    (isProper_add_const_ereal hproper₂ c)
    hlam (henv.trans hshift.symm)

/-- **Corollary 3.37 (exact extended-real form).** Two proper
lower-semicontinuous convex functions have the same proximal mapping at one
positive parameter exactly when they differ by a finite real constant. -/
theorem corollary337_proximalMappingEReal_eq_iff_eq_add_const
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {f₁ f₂ : E → EReal}
    (hconv₁ : Convex ℝ (epigraph f₁))
    (hlsc₁ : LowerSemicontinuous f₁)
    (hproper₁ : IsProper f₁)
    (hconv₂ : Convex ℝ (epigraph f₂))
    (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₂ : IsProper f₂)
    {lam : ℝ} (hlam : 0 < lam) :
    proximalMappingEReal f₁ lam = proximalMappingEReal f₂ lam ↔
      ∃ c : ℝ, f₁ = fun x ↦ f₂ x + (c : EReal) := by
  constructor
  · exact corollary337_eq_add_const_of_proximalMappingEReal_eq
      hconv₁ hlsc₁ hproper₁ hconv₂ hlsc₂ hproper₂ hlam
  · rintro ⟨c, rfl⟩
    exact proximalMappingEReal_add_const f₂ c lam

end RW
