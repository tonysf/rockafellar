/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The exact graphical modulus of a feasible-set mapping
-/

import RockafellarWets.Chapter9.FeasibleSetSemidifferentiability
import RockafellarWets.Chapter9.ConeMultiplierNorms

open Metric Set
open scoped InnerProductSpace NNReal ENNReal

namespace RW

variable {E P G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    {X : Set E} {D : Set G} {F : E × P → G} {t : P} {x : E}

/-- The coderivative in 8.42 is precisely a cone-multiplier mapping. -/
theorem parameterConstraintMapping_coderivative_eq_multiplier
    (hX : IsClosed X) (hD : IsClosed D) (hF : ContDiff ℝ 1 F)
    (hx : x ∈ parameterConstraintMapping X D F t) (hXreg : IsClarkeRegularAt X x)
    (hDreg : IsClarkeRegularAt D (F (x,t)))
    (hCQ : let Ax := (fderiv ℝ F (x,t)).comp (ContinuousLinearMap.inl ℝ E P)
      ∀ y ∈ normalCone D (F (x,t)), -(Ax.adjoint y) ∈ normalCone X x → y = 0) :
    coderivative (parameterConstraintMapping X D F) t x =
      coneMultiplierMapping (normalCone X x) (normalCone D (F (x,t)))
        ((fderiv ℝ F (x,t)).comp (ContinuousLinearMap.inl ℝ E P)).adjoint
        ((fderiv ℝ F (x,t)).comp (ContinuousLinearMap.inr ℝ E P)).adjoint := by
  obtain ⟨_,_,_,hc⟩ := parameterConstraintMapping_derivatives hX hD hF hx hXreg hDreg
    (fun y hy hn _ ↦ hCQ y hy hn)
  exact funext hc

/-- **Example 9.51**, the sharp multiplier quotient for the graphical modulus.
The supremum is zero if the normal cone has no unit multiplier. -/
theorem parameterConstraintMapping_modulus_eq
    (hX : IsClosed X) (hD : IsClosed D) (hF : ContDiff ℝ 1 F)
    (hx : x ∈ parameterConstraintMapping X D F t) (hXreg : IsClarkeRegularAt X x)
    (hDreg : IsClarkeRegularAt D (F (x,t)))
    (hCQ : let Ax := (fderiv ℝ F (x,t)).comp (ContinuousLinearMap.inl ℝ E P)
      ∀ y ∈ normalCone D (F (x,t)), -(Ax.adjoint y) ∈ normalCone X x → y = 0) :
    let A := fderiv ℝ F (x,t)
    let Ax := A.comp (ContinuousLinearMap.inl ℝ E P)
    let At := A.comp (ContinuousLinearMap.inr ℝ E P)
    graphicalLipschitzModulus (parameterConstraintMapping X D F) t x =
      ⨆ y : {y : G // y ∈ normalCone D (F (x,t)) ∧ ‖y‖ = 1},
        ENNReal.ofReal (‖At.adjoint y‖ / infDist (-(Ax.adjoint y)) (normalCone X x)) := by
  have hgraph : IsClosed (svGraph (parameterConstraintMapping X D F)) :=
    (hX.preimage continuous_snd).inter (hD.preimage (hF.continuous.comp (continuous_snd.prodMk continuous_fst)))
  dsimp only
  rw [graphicalLipschitzModulus_eq_svOuterNorm_coderivative hx (RW.IsClosed.isLocallyClosedAt hgraph _),
    parameterConstraintMapping_coderivative_eq_multiplier hX hD hF hx hXreg hDreg hCQ]
  exact svOuterNorm_coneMultiplierMapping (isCone_normalCone hx.1) (isClosed_normalCone X x)
    (isCone_normalCone hx.2) hCQ

/-- **Example 9.51**, attainment of the displayed maximum whenever a unit
normal multiplier exists. -/
theorem exists_max_parameterConstraintMapping_modulus
    (hX : IsClosed X) (hD : IsClosed D) (hF : ContDiff ℝ 1 F)
    (hx : x ∈ parameterConstraintMapping X D F t) (hXreg : IsClarkeRegularAt X x)
    (hDreg : IsClarkeRegularAt D (F (x,t)))
    (hCQ : let Ax := (fderiv ℝ F (x,t)).comp (ContinuousLinearMap.inl ℝ E P)
      ∀ y ∈ normalCone D (F (x,t)), -(Ax.adjoint y) ∈ normalCone X x → y = 0)
    (hne : (normalCone D (F (x,t)) ∩ sphere (0:G) 1).Nonempty) :
    let A := fderiv ℝ F (x,t)
    let Ax := A.comp (ContinuousLinearMap.inl ℝ E P)
    let At := A.comp (ContinuousLinearMap.inr ℝ E P)
    ∃ y ∈ normalCone D (F (x,t)), ‖y‖ = 1 ∧
      graphicalLipschitzModulus (parameterConstraintMapping X D F) t x =
        ENNReal.ofReal (‖At.adjoint y‖ / infDist (-(Ax.adjoint y)) (normalCone X x)) := by
  have hgraph : IsClosed (svGraph (parameterConstraintMapping X D F)) :=
    (hX.preimage continuous_snd).inter (hD.preimage (hF.continuous.comp (continuous_snd.prodMk continuous_fst)))
  dsimp only
  rw [graphicalLipschitzModulus_eq_svOuterNorm_coderivative hx (RW.IsClosed.isLocallyClosedAt hgraph _),
    parameterConstraintMapping_coderivative_eq_multiplier hX hD hF hx hXreg hDreg hCQ]
  exact exists_max_coneMultiplierMapping (isCone_normalCone hx.1) (isClosed_normalCone X x)
    (isCone_normalCone hx.2) (isClosed_normalCone D (F (x,t))) hCQ hne

end RW
