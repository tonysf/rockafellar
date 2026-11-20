/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Example 10.15: Lagrange multipliers and sensitivity of the value
-/

import RockafellarWets.Chapter10.PerturbedCompositeObjectives
import RockafellarWets.Chapter10.ParametricLipschitzContinuity

open Filter Set Topology
open scoped InnerProductSpace NNReal ENNReal

namespace RW

noncomputable section

variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ P]

/-- Ordinary multipliers in the perturbed composite problem. -/
def lagrangeMultipliers (X : Set E) (k : E → ℝ) (F : E → P) (θ : P → EReal)
    (x : E) (u : P) : Set P :=
  {y | y ∈ subdifferential θ (F x+u) ∧
    -gradient k x-(fderiv ℝ F x).adjoint y ∈ normalCone X x}

/-- Horizon multipliers, written using the normal cone to the domain of θ. -/
def horizonLagrangeMultipliers (X : Set E) (F : E → P) (θ : P → EReal)
    (x : E) (u : P) : Set P :=
  {y | y ∈ normalCone (effectiveDomain θ) (F x+u) ∧
    -(fderiv ℝ F x).adjoint y ∈ normalCone X x}

/-- The union of the multiplier sets over all optimal decisions. -/
def optimalLagrangeMultipliers (X : Set E) (k : E → ℝ) (F : E → P) (θ : P → EReal)
    (u : P) : Set P :=
  {y | ∃ x ∈ parametricMinimizers (perturbedCompositeObjective X k F θ) u,
    y ∈ lagrangeMultipliers X k F θ x u}

theorem parametricMultipliers_eq_optimalLagrangeMultipliers
    {X : Set E} {k : E → ℝ} {F : E → P} {θ : P → EReal} {u : P} {a : ℝ}
    (hX : IsClosed X) (hk : ContDiff ℝ 1 k) (hF : ContDiff ℝ 1 F)
    (hθ : LowerSemicontinuous θ) (hpθ : IsProper θ)
    (hu : parametricValue (perturbedCompositeObjective X k F θ) u = a) :
    parametricMultipliers (perturbedCompositeObjective X k F θ) u =
      optimalLagrangeMultipliers X k F θ u := by
  ext y
  change (∃ x ∈ parametricMinimizers (perturbedCompositeObjective X k F θ) u,
      WithLp.toLp 2 ((0:E),y) ∈ subdifferential _ (WithLp.toLp 2 (x,u))) ↔ _
  apply exists_congr
  intro x
  apply and_congr_right
  intro hx
  have hval := (mem_parametricMinimizers.mp hx).1.trans hu
  obtain ⟨hxX,c,hc⟩ := perturbedCompositeObjective_finite_components hpθ hval
  rw [subdifferential_perturbedCompositeObjective hX hk hF hθ hxX hc]
  simp only [mem_setOf_eq,WithLp.toLp_fst,WithLp.toLp_snd,zero_sub,lagrangeMultipliers]

private theorem horizonParametricMultipliers_perturbed_eq_zero
    {X : Set E} {k : E → ℝ} {F : E → P} {θ : P → EReal} {u : P} {a : ℝ}
    (hX : IsClosed X) (hne : X.Nonempty) (hk : ContDiff ℝ 1 k) (hF : ContDiff ℝ 1 F)
    (hθ : LowerSemicontinuous θ) (hpθ : IsProper θ) (hcθ : Convex ℝ (epigraph θ))
    (hb : IsParametricallyLevelBounded (perturbedCompositeObjective X k F θ))
    (hu : parametricValue (perturbedCompositeObjective X k F θ) u = a)
    (hQ : ∀ x ∈ parametricMinimizers (perturbedCompositeObjective X k F θ) u,
      horizonLagrangeMultipliers X F θ x u = {0}) :
    horizonParametricMultipliers (perturbedCompositeObjective X k F θ) u = {0} := by
  have hl := lowerSemicontinuous_perturbedCompositeObjective hX hne hk.continuous hF.continuous hθ hpθ
  have hp := isProper_perturbedCompositeObjective (k := k) (F := F) hne hpθ
  apply Subset.antisymm
  · rintro y ⟨x,hx,hy⟩
    have hval := (mem_parametricMinimizers.mp hx).1.trans hu
    obtain ⟨hxX,c,hc⟩ := perturbedCompositeObjective_finite_components hpθ hval
    have hv := horizonSubdifferential_perturbedCompositeObjective_subset hX hk hF hθ hpθ hxX hc hy
    have hmem : y ∈ horizonLagrangeMultipliers X F θ x u :=
      ⟨horizonSubdifferential_subset_normalCone_domain hcθ hpθ hc hv.1,
        by simpa only [WithLp.toLp_fst,WithLp.toLp_snd,zero_sub] using hv.2⟩
    rwa [hQ x hx] at hmem
  · obtain ⟨x,hx⟩ := parametricMinimizers_nonempty hl hp hb (hu.trans_lt (EReal.coe_lt_top _))
    apply singleton_subset_iff.mpr
    refine ⟨x,hx,?_⟩
    have hval := (mem_parametricMinimizers.mp hx).1.trans hu
    simpa only [WithLp.toLp_zero] using (subdifferential_properties hval).2.2.2.2.1.1

/-- **Example 10.15**: the value is locally Lipschitz, its subgradients are
multipliers, and the largest multiplier norm is attained and bounds its modulus.
The triangular coordinate proof does not require regularity of X. -/
theorem lagrange_multiplier_sensitivity
    {X : Set E} {k : E → ℝ} {F : E → P} {θ : P → EReal} {u : P} {a : ℝ}
    (hX : IsClosed X) (hne : X.Nonempty) (hk : ContDiff ℝ 1 k) (hF : ContDiff ℝ 1 F)
    (hθ : LowerSemicontinuous θ) (hpθ : IsProper θ) (hcθ : Convex ℝ (epigraph θ))
    (hb : IsParametricallyLevelBounded (perturbedCompositeObjective X k F θ))
    (hu : parametricValue (perturbedCompositeObjective X k F θ) u = a)
    (hQ : ∀ x ∈ parametricMinimizers (perturbedCompositeObjective X k F θ) u,
      horizonLagrangeMultipliers X F θ x u = {0}) :
    ERealStrictlyContinuousAt (parametricValue (perturbedCompositeObjective X k F θ)) u ∧
    subdifferential (parametricValue (perturbedCompositeObjective X k F θ)) u ⊆
      optimalLagrangeMultipliers X k F θ u ∧
    ∃ y ∈ optimalLagrangeMultipliers X k F θ u,
      lipschitzModulus (fun v ↦ (parametricValue (perturbedCompositeObjective X k F θ) v).toReal) u ≤
        (‖y‖₊ : ℝ≥0∞) ∧ ∀ z ∈ optimalLagrangeMultipliers X k F θ u, ‖z‖ ≤ ‖y‖ := by
  have hl := lowerSemicontinuous_perturbedCompositeObjective hX hne hk.continuous hF.continuous hθ hpθ
  have hp := isProper_perturbedCompositeObjective (k := k) (F := F) hne hpθ
  have hzero := horizonParametricMultipliers_perturbed_eq_zero hX hne hk hF hθ hpθ hcθ hb hu hQ
  have he := parametricMultipliers_eq_optimalLagrangeMultipliers hX hk hF hθ hpθ hu
  refine ⟨eRealStrictlyContinuousAt_parametricValue hl hp hb hu hzero,?_,?_⟩
  · rw [← he]
    exact subdifferential_parametricValue_subset hl hb hu
  · simpa only [he] using parametricValue_modulus_le_max_multiplier hl hp hb hu hzero

/-- **Example 10.15**, a unique optimal multiplier is the strict gradient
of the optimal value function. -/
theorem lagrange_multiplier_strict_gradient
    {X : Set E} {k : E → ℝ} {F : E → P} {θ : P → EReal} {u y : P} {a : ℝ}
    (hX : IsClosed X) (hne : X.Nonempty) (hk : ContDiff ℝ 1 k) (hF : ContDiff ℝ 1 F)
    (hθ : LowerSemicontinuous θ) (hpθ : IsProper θ) (hcθ : Convex ℝ (epigraph θ))
    (hb : IsParametricallyLevelBounded (perturbedCompositeObjective X k F θ))
    (hu : parametricValue (perturbedCompositeObjective X k F θ) u = a)
    (hQ : ∀ x ∈ parametricMinimizers (perturbedCompositeObjective X k F θ) u,
      horizonLagrangeMultipliers X F θ x u = {0})
    (hY : optimalLagrangeMultipliers X k F θ u = {y}) :
    HasStrictGradientAt (parametricValue (perturbedCompositeObjective X k F θ)) y u := by
  have hl := lowerSemicontinuous_perturbedCompositeObjective hX hne hk.continuous hF.continuous hθ hpθ
  have hp := isProper_perturbedCompositeObjective (k := k) (F := F) hne hpθ
  exact hasStrictGradientAt_parametricValue hl hp hb hu
    (horizonParametricMultipliers_perturbed_eq_zero hX hne hk hF hθ hpθ hcθ hb hu hQ)
    ((parametricMultipliers_eq_optimalLagrangeMultipliers hX hk hF hθ hpθ hu).trans hY)

end

end RW
