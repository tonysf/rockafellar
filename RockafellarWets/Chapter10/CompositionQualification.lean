/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Sufficient conditions for the coderivative chain qualification
-/

import RockafellarWets.Chapter10.CompositionLipschitz

open Set

namespace RW

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  {S : E → Set F} {T : F → Set G} {x : E} {w : F} {u : G}

theorem compositionCoderivativeQualification_iff (hw : w ∈ S x) (hu : u ∈ T w) :
    CompositionCoderivativeQualification T S x w u ↔
      coderivative T w u 0 ∩ svInv (coderivative S x w) 0 = {0} := by
  constructor
  · intro h
    apply Subset.antisymm
    · exact fun z hz ↦ h z hz.1 hz.2
    · rintro z rfl
      exact ⟨(graphicalDerivative_properties hu).2.2.1.2.1,
        (graphicalDerivative_properties hw).2.2.1.2.1⟩
  · intro h z hz hv
    have hz0 : z ∈ coderivative T w u 0 ∩ svInv (coderivative S x w) 0 := ⟨hz,hv⟩
    simpa only [h,mem_singleton_iff] using hz0

/-- The parenthetical sufficient condition in 10.37(b), with strict
continuity at the intermediate point (the printed base points are mistyped). -/
theorem compositionCoderivativeQualification_of_strict_outer
    (h : SvStrictlyContinuousAt T w) (hu : u ∈ T w) :
    CompositionCoderivativeQualification T S x w u :=
  compositionCoderivativeQualification_of_aubin_outer (h.hasAubinPropertyAt hu)

theorem compositionCoderivativeQualification_of_strict_inverse
    (h : SvStrictlyContinuousAt (svInv S) w) (hw : w ∈ S x) :
    CompositionCoderivativeQualification T S x w u :=
  compositionCoderivativeQualification_of_aubin_inverse (h.hasAubinPropertyAt hw)

end RW
