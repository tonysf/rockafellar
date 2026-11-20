/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 10: The parametric Fermat rule
-/

import RockafellarWets.Chapter10.PartialSubgradients
import RockafellarWets.Chapter10.FermatRule

open Set

namespace RW

variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ P]
  {f : WithLp 2 (E × P) → EReal} {x : E} {p : P} {c : ℝ}

/-- **Example 10.12**, necessary parametric stationarity under the horizon
qualification. The objective need only have a finite local minimum in `x`. -/
theorem exists_parametric_subgradient_of_localMin (hl : LowerSemicontinuous f)
    (hx : f (WithLp.toLp 2 (x,p)) = c) (hm : IsLocalMin (partialFunction f p) x)
    (hQ : ∀ y, WithLp.toLp 2 ((0:E),y) ∈ horizonSubdifferential f (WithLp.toLp 2 (x,p)) → y = 0) :
    ∃ y, WithLp.toLp 2 ((0:E),y) ∈ subdifferential f (WithLp.toLp 2 (x,p)) :=
  subdifferential_partial_subset hl hx hQ (RW.IsLocalMin.zero_mem_subdifferential hm hx)

/-- **Example 10.12**, sufficiency when the joint objective is regular and
the frozen-parameter objective is convex. No qualification is required. -/
theorem mem_argmin_partial_of_parametric_subgradient (hp : IsProper f)
    (hx : f (WithLp.toLp 2 (x,p)) = c)
    (hr : IsSubdifferentiallyRegularAt f (WithLp.toLp 2 (x,p)))
    (hc : Convex ℝ (epigraph (partialFunction f p)))
    (hy : ∃ y, WithLp.toLp 2 ((0:E),y) ∈ subdifferential f (WithLp.toLp 2 (x,p))) :
    x ∈ argmin (partialFunction f p) := by
  have hp' : IsProper (partialFunction f p) :=
    ⟨⟨x,hx.trans_lt (EReal.coe_lt_top _)⟩,fun y ↦ hp.2 (WithLp.toLp 2 (y,p))⟩
  apply (mem_argmin_iff_zero_mem_subdifferential_of_convex hc hp' hx).mpr
  apply regularSubdifferential_subset_subdifferential _ _
  apply regularSubdifferential_partial_superset hx
  simpa only [hr.subdifferential_eq_regularSubdifferential] using hy

end RW
