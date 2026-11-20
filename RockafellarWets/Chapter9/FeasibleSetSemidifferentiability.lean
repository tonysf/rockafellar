/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Semidifferentiability of parameter-dependent feasible sets
-/

import RockafellarWets.Chapter8.FeasibleSetDerivatives
import RockafellarWets.Chapter9.MordukhovichCriterion
import RockafellarWets.Chapter9.SemidifferentiabilityFromAubin

open Set
open scoped InnerProductSpace NNReal ENNReal

namespace RW

variable {E P G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

/-- **Example 9.51**, the Aubin property and the displayed semiderivative
formula under the state-constraint qualification 9(26). -/
theorem parameterConstraintMapping_semidifferentiability {X : Set E} {D : Set G} {F : E × P → G}
    (hX : IsClosed X) (hD : IsClosed D) (hF : ContDiff ℝ 1 F) {t : P} {x : E}
    (hx : x ∈ parameterConstraintMapping X D F t) (hXreg : IsClarkeRegularAt X x)
    (hDreg : IsClarkeRegularAt D (F (x,t)))
    (hCQ : let Ax := (fderiv ℝ F (x,t)).comp (ContinuousLinearMap.inl ℝ E P)
      ∀ y ∈ normalCone D (F (x,t)), -(Ax.adjoint y) ∈ normalCone X x → y = 0) :
    let S := parameterConstraintMapping X D F
    let A := fderiv ℝ F (x,t)
    let Ax := A.comp (ContinuousLinearMap.inl ℝ E P)
    let At := A.comp (ContinuousLinearMap.inr ℝ E P)
    HasAubinPropertyAt S t x ∧
      HasMappingSemiderivative S t x (fun s ↦ {w | w ∈ tangentCone X x ∧
        Ax w + At s ∈ tangentCone D (F (x,t))}) := by
  let S := parameterConstraintMapping X D F
  let A := fderiv ℝ F (x,t)
  let Ax := A.comp (ContinuousLinearMap.inl ℝ E P)
  let At := A.comp (ContinuousLinearMap.inr ℝ E P)
  obtain ⟨hreg,hproto,hder,hcoder⟩ := parameterConstraintMapping_derivatives hX hD hF hx hXreg hDreg
    (fun y hy hn _ ↦ hCQ y hy hn)
  have hgraph : IsClosed (svGraph S) :=
    (hX.preimage continuous_snd).inter (hD.preimage (hF.continuous.comp (continuous_snd.prodMk continuous_fst)))
  have hzero : coderivative S t x 0 = {0} := by
    rw [hcoder]
    ext v
    constructor
    · rintro ⟨y,hy,rfl⟩
      have hy0 := hCQ y hy.1 (by simpa only [zero_add] using hy.2)
      simp [hy0]
    · intro hv
      obtain rfl := mem_singleton_iff.mp hv
      refine ⟨0,⟨(isCone_normalCone hx.2).1,?_⟩,by simp⟩
      simpa using (isCone_normalCone hx.1).1
  have hAubin : HasAubinPropertyAt S t x :=
    (hasAubinPropertyAt_iff_coderivative_zero hx (RW.IsClosed.isLocallyClosedAt hgraph _)).mpr hzero
  refine ⟨hAubin,?_⟩
  have hsemi := hAubin.hasMappingSemiderivative hproto
  have heq : graphicalDerivative S t x = fun s ↦ {w | w ∈ tangentCone X x ∧
      Ax w + At s ∈ tangentCone D (F (x,t))} := funext hder
  rwa [heq] at hsemi

end RW
