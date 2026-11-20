/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Convexified Normal and Tangent Cones

Formula 6(19) and Exercise 6.38. The closed convex hulls are defined using
the ordinary convex hull, exactly as printed. At points of the set, the
underlying sets are cones, so the conic-hull and bipolar descriptions agree.
The sharp finite-sum representations use Theorem 3.15, including its bound
by the ambient dimension and the empty sum in dimension zero.
-/

import RockafellarWets.Chapter6.TangentNormalPolarity
import RockafellarWets.Chapter3.FiniteConeSetOperations

open Set
open scoped BigOperators

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Formula 6(19): the convexified normal cone is the closed convex hull of
the limiting normal cone. -/
def convexifiedNormalCone (C : Set E) (x : E) : Set E :=
  closure (convexHull ℝ (normalCone C x))

/-- Formula 6(19): the convexified tangent cone is the closed convex hull of
the tangent cone. -/
def convexifiedTangentCone (C : Set E) (x : E) : Set E :=
  closure (convexHull ℝ (tangentCone C x))

theorem isClosed_convexifiedNormalCone (C : Set E) (x : E) :
    IsClosed (convexifiedNormalCone C x) := isClosed_closure

theorem isClosed_convexifiedTangentCone (C : Set E) (x : E) :
    IsClosed (convexifiedTangentCone C x) := isClosed_closure

theorem convex_convexifiedNormalCone (C : Set E) (x : E) :
    Convex ℝ (convexifiedNormalCone C x) :=
  (convex_convexHull ℝ (normalCone C x)).closure

theorem convex_convexifiedTangentCone (C : Set E) (x : E) :
    Convex ℝ (convexifiedTangentCone C x) :=
  (convex_convexHull ℝ (tangentCone C x)).closure

theorem normalCone_subset_convexifiedNormalCone (C : Set E) (x : E) :
    normalCone C x ⊆ convexifiedNormalCone C x :=
  (subset_convexHull ℝ _).trans subset_closure

theorem tangentCone_subset_convexifiedTangentCone (C : Set E) (x : E) :
    tangentCone C x ⊆ convexifiedTangentCone C x :=
  (subset_convexHull ℝ _).trans subset_closure

/-- At a point of `C`, the convexified normal cone also has the conic-hull
description. -/
theorem convexifiedNormalCone_eq_closure_conicHull
    {C : Set E} {x : E} (hx : x ∈ C) :
    convexifiedNormalCone C x = closure (conicHull (normalCone C x)) := by
  rw [conicHull_eq_convexHull_positiveHull, positiveHull_eq_self (isCone_normalCone hx)]
  rfl

/-- At a point of `C`, the convexified tangent cone also has the conic-hull
description. -/
theorem convexifiedTangentCone_eq_closure_conicHull
    {C : Set E} {x : E} (hx : x ∈ C) :
    convexifiedTangentCone C x = closure (conicHull (tangentCone C x)) := by
  rw [conicHull_eq_convexHull_positiveHull, positiveHull_eq_self (isCone_tangentCone hx)]
  rfl

section FiniteDimensional

variable [FiniteDimensional ℝ E]

theorem convexifiedNormalCone_eq_bipolar
    {C : Set E} {x : E} (hx : x ∈ C) :
    convexifiedNormalCone C x = polarCone (polarCone (normalCone C x)) := by
  rw [polarCone_bipolar, convexifiedNormalCone_eq_closure_conicHull hx]

theorem convexifiedTangentCone_eq_bipolar
    {C : Set E} {x : E} (hx : x ∈ C) :
    convexifiedTangentCone C x = polarCone (polarCone (tangentCone C x)) := by
  rw [polarCone_bipolar, convexifiedTangentCone_eq_closure_conicHull hx]

theorem isCone_convexifiedNormalCone {C : Set E} {x : E} (hx : x ∈ C) :
    IsCone (convexifiedNormalCone C x) := by
  rw [convexifiedNormalCone_eq_bipolar hx]
  exact isCone_polarCone _

theorem isCone_convexifiedTangentCone {C : Set E} {x : E} (hx : x ∈ C) :
    IsCone (convexifiedTangentCone C x) := by
  rw [convexifiedTangentCone_eq_bipolar hx]
  exact isCone_polarCone _

/-- **Exercise 6.38(a)**, first polarity: the convexified normal cone is
the polar of the regular tangent cone. Local closedness suffices. -/
theorem convexifiedNormalCone_eq_polarCone_regularTangentCone
    {C : Set E} {x : E} (hx : x ∈ C) (hlc : IsLocallyClosedAt C x) :
    convexifiedNormalCone C x = polarCone (regularTangentCone C x) := by
  rw [regularTangentCone_eq_polarCone_normalCone hx hlc,
    convexifiedNormalCone_eq_bipolar hx]

/-- **Exercise 6.38(a)**, reverse polarity: the regular tangent cone is
the polar of the convexified normal cone. Local closedness suffices. -/
theorem regularTangentCone_eq_polarCone_convexifiedNormalCone
    {C : Set E} {x : E} (hx : x ∈ C) (hlc : IsLocallyClosedAt C x) :
    regularTangentCone C x = polarCone (convexifiedNormalCone C x) := by
  rw [convexifiedNormalCone_eq_closure_conicHull hx, polarCone_closure_conicHull,
    regularTangentCone_eq_polarCone_normalCone hx hlc]

/-- **Exercise 6.38(b)**, first polarity: the convexified tangent cone is
the polar of the regular normal cone. -/
theorem convexifiedTangentCone_eq_polarCone_regularNormalCone
    {C : Set E} {x : E} (hx : x ∈ C) :
    convexifiedTangentCone C x = polarCone (regularNormalCone C x) := by
  rw [regularNormalCone_eq_polarCone_tangentCone hx,
    convexifiedTangentCone_eq_bipolar hx]

/-- **Exercise 6.38(b)**, reverse polarity: the regular normal cone is
the polar of the convexified tangent cone. -/
theorem regularNormalCone_eq_polarCone_convexifiedTangentCone
    {C : Set E} {x : E} (hx : x ∈ C) :
    regularNormalCone C x = polarCone (convexifiedTangentCone C x) := by
  rw [convexifiedTangentCone_eq_closure_conicHull hx, polarCone_closure_conicHull,
    regularNormalCone_eq_polarCone_tangentCone hx]

/-- **Exercise 6.38(a)**: pointedness of the limiting normal cone is
equivalent to nonempty interior of the regular tangent cone. -/
theorem isPointed_normalCone_iff_interior_regularTangentCone_nonempty
    {C : Set E} {x : E} (hx : x ∈ C) (hlc : IsLocallyClosedAt C x) :
    IsPointed (normalCone C x) ↔ (interior (regularTangentCone C x)).Nonempty := by
  rw [regularTangentCone_eq_polarCone_normalCone hx hlc]
  exact (interior_polarCone_nonempty_iff_isPointed
    (isClosed_normalCone C x) (isCone_normalCone hx)).symm

/-- **Exercise 6.38(b)**: pointedness of the tangent cone is equivalent to
nonempty interior of the regular normal cone. -/
theorem isPointed_tangentCone_iff_interior_regularNormalCone_nonempty
    {C : Set E} {x : E} (hx : x ∈ C) :
    IsPointed (tangentCone C x) ↔ (interior (regularNormalCone C x)).Nonempty := by
  rw [regularNormalCone_eq_polarCone_tangentCone hx]
  exact (interior_polarCone_nonempty_iff_isPointed
    (isClosed_tangentCone C x) (isCone_tangentCone hx)).symm

private theorem mem_closure_convexHull_iff_exists_sum_of_isPointed
    {K : Set E} (hclosed : IsClosed K) (hcone : IsCone K) (hpointed : IsPointed K)
    {v : E} :
    v ∈ closure (convexHull ℝ K) ↔
      ∃ (r : ℕ) (vs : Fin r → E), r ≤ Module.finrank ℝ E ∧
        (∀ i, vs i ∈ K) ∧ ∑ i, vs i = v := by
  rw [(isClosed_convexHull_of_isClosed_isPointed hclosed hcone hpointed).closure_eq]
  constructor
  · exact exists_sum_finrank_bound_of_mem_convexHull hcone
  · rintro ⟨r, vs, -, hvs, hsum⟩
    exact (mem_convexHull_iff_exists_fintype_sum_mem hcone).2
      ⟨Fin r, inferInstance, vs, hvs, hsum⟩

/-- **Exercise 6.38(a)**, finite-sum clause: when the normal cone is
pointed, every convexified normal is a sum of at most `finrank` original
normal vectors, and every such sum is a convexified normal. -/
theorem mem_convexifiedNormalCone_iff_exists_sum_of_isPointed
    {C : Set E} {x v : E} (hx : x ∈ C) (hpointed : IsPointed (normalCone C x)) :
    v ∈ convexifiedNormalCone C x ↔
      ∃ (r : ℕ) (vs : Fin r → E), r ≤ Module.finrank ℝ E ∧
        (∀ i, vs i ∈ normalCone C x) ∧ ∑ i, vs i = v :=
  mem_closure_convexHull_iff_exists_sum_of_isPointed
    (isClosed_normalCone C x) (isCone_normalCone hx) hpointed

/-- **Exercise 6.38(b)**, finite-sum clause: when the tangent cone is
pointed, every convexified tangent is a sum of at most `finrank` original
tangent vectors, and every such sum is a convexified tangent. -/
theorem mem_convexifiedTangentCone_iff_exists_sum_of_isPointed
    {C : Set E} {x w : E} (hx : x ∈ C) (hpointed : IsPointed (tangentCone C x)) :
    w ∈ convexifiedTangentCone C x ↔
      ∃ (r : ℕ) (ws : Fin r → E), r ≤ Module.finrank ℝ E ∧
        (∀ i, ws i ∈ tangentCone C x) ∧ ∑ i, ws i = w :=
  mem_closure_convexHull_iff_exists_sum_of_isPointed
    (isClosed_tangentCone C x) (isCone_tangentCone hx) hpointed

end FiniteDimensional

end RW
