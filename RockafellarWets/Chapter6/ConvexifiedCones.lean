/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Convexified Normal and Tangent Cones

Exercise 6.38(b): the closed convex hull of the tangent cone and the regular
normal cone are polar to each other.

Both identities are the bipolar theorem of 6.21 applied to the polarity
6.28(a), `N̂_C(x̄) = T_C(x̄)*`: polarizing once more turns the regular normal
cone into `cl con T_C(x̄)`, and polarity does not see the closed convex conic
hull, so polarizing that hull returns the regular normal cone.
-/

import RockafellarWets.Chapter6.ClarkeRegularityCharacterizations

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

end ConvexifiedCones

end RW
