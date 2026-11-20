/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The convex nonseparation alternative in the basic chain rule
-/

import RockafellarWets.Chapter10.CoordinateSubgradients
import RockafellarWets.Chapter8.ConvexSubgradients

open Set
open scoped InnerProductSpace

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- A supporting hyperplane through `z` that weakly separates `D` from
the affine linearization `z + range A`. The common point forces the
linearized range to lie in the hyperplane. -/
def HasSeparatingLinearizationNormal (D : Set F) (z : F) (A : E →L[ℝ] F) : Prop :=
  ∃ y : F, y ≠ 0 ∧ (∀ u ∈ D, ⟪y,u-z⟫_ℝ ≤ 0) ∧ ∀ w : E, ⟪y,A w⟫_ℝ = 0

/-- **Theorem 10.6**, the convex qualification is precisely the absence
of a hyperplane separating the effective domain from the linearized range. -/
theorem convex_chainQualification_iff_not_separated {g : F → EReal} {z : F} {c : ℝ}
    (hc : Convex ℝ (epigraph g)) (hp : IsProper g) (hl : LowerSemicontinuous g)
    (hz : g z = c) (A : E →L[ℝ] F) :
    (∀ y ∈ horizonSubdifferential g z, A.adjoint y = 0 → y = 0) ↔
      ¬ HasSeparatingLinearizationNormal (effectiveDomain g) z A := by
  have hh := horizonSubdifferential_eq_normalCone_domain_of_locallyLsc hc hp
    (locallyLscAt_of_lowerSemicontinuous_finite hl hz) hz
  have hzD : z ∈ effectiveDomain g := hz.trans_lt (EReal.coe_lt_top _)
  rw [hh,normalCone_eq_of_convex (convex_effectiveDomain_of_convex_epigraph hc) hzD]
  constructor
  · intro h ⟨y,hy,hs,ha⟩
    apply hy (h y hs ?_)
    apply ext_inner_right ℝ
    intro w
    simpa only [ContinuousLinearMap.adjoint_inner_left,inner_zero_left] using ha w
  · intro h y hy ha
    by_contra hne
    apply h ⟨y,hne,hy,?_⟩
    intro w
    rw [← ContinuousLinearMap.adjoint_inner_left,ha,inner_zero_left]

end RW
