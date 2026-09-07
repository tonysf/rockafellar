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

/-- For a closed pointed cone the closed convex conic hull is just the convex
hull: `con K` is already closed by 3.15, and the conic hull of a cone is its
convex hull. -/
theorem closure_conicHull_eq_convexHull_of_isClosed_isPointed {K : Set E}
    (hclosed : IsClosed K) (hcone : IsCone K) (hpointed : IsPointed K) :
    closure (conicHull K) = convexHull ℝ K := by
  have hch : conicHull K = convexHull ℝ K := by
    rw [conicHull_eq_convexHull_positiveHull, positiveHull_eq_self hcone]
  rw [hch, (isClosed_convexHull_of_isClosed_isPointed hclosed hcone hpointed).closure_eq]

/-- **Exercise 6.38(b)**, the pointedness criterion: `T_C(x̄)` is pointed exactly
when `N̂_C(x̄)` has nonempty interior.  This is 6.22 read through 6.28(a). -/
theorem isPointed_tangentCone_iff_interior_regularNormalCone_nonempty {C : Set E}
    {x : E} (hx : x ∈ C) :
    IsPointed (tangentCone C x) ↔ (interior (regularNormalCone C x)).Nonempty := by
  rw [regularNormalCone_eq_polarCone_tangentCone hx]
  exact (interior_polarCone_nonempty_iff_isPointed (isClosed_tangentCone C x)
    (isCone_tangentCone hx)).symm

/-- **Exercise 6.38(b)**, the Caratheodory clause: when `T_C(x̄)` is pointed, its
convexified cone consists of the sums of `n` of its members. -/
theorem mem_closure_conicHull_tangentCone_iff {C : Set E} {x : E} (hx : x ∈ C)
    (hpointed : IsPointed (tangentCone C x)) {w : E} :
    w ∈ closure (conicHull (tangentCone C x)) ↔
      ∃ z : Fin (Module.finrank ℝ E) → E,
        (∀ i, z i ∈ tangentCone C x) ∧ ∑ i, z i = w := by
  rw [closure_conicHull_eq_convexHull_of_isClosed_isPointed (isClosed_tangentCone C x)
      (isCone_tangentCone hx) hpointed,
    mem_convexHull_iff_exists_finrank_sum_mem (isCone_tangentCone hx)]

/-- **Exercise 6.38(a)**, the pointedness criterion: `N_C(x̄)` is pointed exactly
when `T̂_C(x̄)` has nonempty interior.  This is 6.22 read through 6.28(b). -/
theorem isPointed_normalCone_iff_interior_regularTangentCone_nonempty {C : Set E}
    {x : E} (hx : x ∈ C) (hlc : IsLocallyClosedAt C x) :
    IsPointed (normalCone C x) ↔ (interior (regularTangentCone C x)).Nonempty := by
  rw [regularTangentCone_eq_polarCone_normalCone hx hlc]
  exact (interior_polarCone_nonempty_iff_isPointed (isClosed_normalCone C x)
    (isCone_normalCone hx)).symm

/-- **Exercise 6.38(a)**, the Caratheodory clause. -/
theorem mem_closure_conicHull_normalCone_iff {C : Set E} {x : E} (hx : x ∈ C)
    (hpointed : IsPointed (normalCone C x)) {v : E} :
    v ∈ closure (conicHull (normalCone C x)) ↔
      ∃ z : Fin (Module.finrank ℝ E) → E,
        (∀ i, z i ∈ normalCone C x) ∧ ∑ i, z i = v := by
  rw [closure_conicHull_eq_convexHull_of_isClosed_isPointed (isClosed_normalCone C x)
      (isCone_normalCone hx) hpointed,
    mem_convexHull_iff_exists_finrank_sum_mem (isCone_normalCone hx)]

end ConvexifiedCones

end RW
