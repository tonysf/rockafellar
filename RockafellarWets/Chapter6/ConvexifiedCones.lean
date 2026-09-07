/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Convexified Normal and Tangent Cones

Exercise 6.38: the closed convex hull of the tangent cone and the regular
normal cone are polar to each other, and so are the closed convex hull of the
normal cone and the regular tangent cone.

All four identities are the bipolar theorem of 6.21 applied to the two
polarity relations of 6.28.  Polarizing `N̂_C(x̄) = T_C(x̄)*` once more turns
the regular normal cone into `cl con T_C(x̄)`, and polarity does not see the
closed convex conic hull, so polarizing that hull returns the regular normal
cone; clause (a) is the same computation run on `T̂_C(x̄) = N_C(x̄)*`, which is
why it asks for local closedness and clause (b) does not.
-/

import RockafellarWets.Chapter6.NormalsToTangentCones

open Set

namespace RW

section ConvexifiedCones

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **Exercise 6.38(b)**: `cl con T_C(x̄) = N̂_C(x̄)*`. -/
theorem closure_conicHull_tangentCone_eq_polarCone_regularNormalCone {C : Set E}
    {x : E} (hx : x ∈ C) :
    closure (conicHull (tangentCone C x)) = polarCone (regularNormalCone C x) := by
  rw [regularNormalCone_eq_polarCone_tangentCone hx, polarCone_bipolar]

/-- **Exercise 6.38(b)**: `N̂_C(x̄) = [cl con T_C(x̄)]*`. -/
theorem regularNormalCone_eq_polarCone_closure_conicHull_tangentCone {C : Set E}
    {x : E} (hx : x ∈ C) :
    regularNormalCone C x = polarCone (closure (conicHull (tangentCone C x))) := by
  rw [polarCone_closure_conicHull, regularNormalCone_eq_polarCone_tangentCone hx]

/-- **Exercise 6.38(a)**: `cl con N_C(x̄) = T̂_C(x̄)*`. -/
theorem closure_conicHull_normalCone_eq_polarCone_regularTangentCone {C : Set E}
    {x : E} (hx : x ∈ C) (hlc : IsLocallyClosedAt C x) :
    closure (conicHull (normalCone C x)) = polarCone (regularTangentCone C x) := by
  rw [regularTangentCone_eq_polarCone_normalCone hx hlc, polarCone_bipolar]

/-- **Exercise 6.38(a)**: `T̂_C(x̄) = [cl con N_C(x̄)]*`. -/
theorem regularTangentCone_eq_polarCone_closure_conicHull_normalCone {C : Set E}
    {x : E} (hx : x ∈ C) (hlc : IsLocallyClosedAt C x) :
    regularTangentCone C x = polarCone (closure (conicHull (normalCone C x))) := by
  rw [polarCone_closure_conicHull, regularTangentCone_eq_polarCone_normalCone hx hlc]

end ConvexifiedCones

end RW
