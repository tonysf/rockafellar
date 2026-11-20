/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Subgradients of elementary maxima
-/

import RockafellarWets.Chapter8.FiniteMaxDerivatives
import RockafellarWets.Chapter8.RegularSupportDuality

open Set
open scoped InnerProductSpace Gradient

namespace RW

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [Nonempty ι] {fs : ι → E → ℝ}

/-- **Exercise 8.31.** The limiting subdifferential of a finite smooth maximum
is the convex hull of its active gradients. -/
theorem subdifferential_finiteMax (hs : ∀ i, ContDiff ℝ 1 (fs i)) (x : E) :
    subdifferential (fun y ↦ (finiteMax fs y : EReal)) x = convexHull ℝ (maxActiveGradients fs x) := by
  have hfinite : (maxActiveGradients fs x).Finite := (maxActiveIndices fs x).finite_toSet.image _
  rw [(isSubdifferentiallyRegularAt_finiteMax hs x).subdifferential_eq_linearMinorantSet,
    subderivative_finiteMax_eq_supportFunction hs,linearMinorantSet_supportFunction,
    hfinite.isCompact_convexHull.isClosed.closure_eq]

/-- The horizon subdifferential of an elementary smooth maximum vanishes. -/
theorem horizonSubdifferential_finiteMax (hs : ∀ i, ContDiff ℝ 1 (fs i)) (x : E) :
    horizonSubdifferential (fun y ↦ (finiteMax fs y : EReal)) x = {0} := by
  have hd : effectiveDomain (subderivative (fun y ↦ (finiteMax fs y : EReal)) x) = univ := by
    apply eq_univ_of_forall
    intro w
    change subderivative _ x w < ⊤
    rw [subderivative_finiteMax hs]
    exact EReal.coe_lt_top _
  rw [(isSubdifferentiallyRegularAt_finiteMax hs x).horizonSubdifferential_eq_polar_domain,hd,polarCone_univ]

end RW
