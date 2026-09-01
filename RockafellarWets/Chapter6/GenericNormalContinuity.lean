/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Generic Continuity of Normal Cones

Proposition 6.49 says that the points of `frontier C` where the normal-cone
mapping is not continuous relative to `frontier C` form a meager set, and
hence that its continuity points are dense there.

The proposition's printed arbitrary-set wording is false for the definitions
used in this development.  Here `normalCone C x = ∅` when `x ∉ C`.  For
example, take `C = ℚ ⊂ ℝ`, so that `frontier C = ℝ`.  At an irrational
point the normal-cone value is empty, but zero belongs to the values at
arbitrarily close rational points, so outer semicontinuity fails.  At a
rational point zero belongs to the value, but arbitrarily close irrational
points have empty value, so inner semicontinuity fails.  Thus the exceptional
set is all of `ℝ`, which is not meager.

The hypothesis-free result below is therefore stated relative to
`C ∩ frontier C`, the strongest restriction supplied directly by
`svOscOn_normalCone C`.  When `C` is closed, `frontier C ⊆ C`, giving the full
frontier statement.  The frontier is itself closed, so in the finite-
dimensional setting its subtype is a Baire space and density follows from
meagerness.
-/

import RockafellarWets.Chapter5.GenericContinuity
import RockafellarWets.Chapter6.NormalCones
import Mathlib.Topology.Baire.CompleteMetrizable

open Filter Set Topology

namespace RW

section GenericNormalContinuity

/-- Outer semicontinuity is preserved when the restricting set is shrunk. -/
private theorem svOscOn_mono {E F : Type*} [TopologicalSpace E]
    [TopologicalSpace F] {S : E → Set F} {X Y : Set E} (hYX : Y ⊆ X)
    (hS : SvOscOn S X) : SvOscOn S Y := by
  intro x hx
  exact
    (outerSetLimitAlong_mono_filter (nhdsWithin_mono x hYX) S).trans
      (hS x (hYX hx))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The hypothesis-free outer-semicontinuity restriction justified by
Proposition 6.6: restrict the boundary to points that actually belong to
`C`. -/
theorem svOscOn_normalCone_inter_frontier (C : Set E) :
    SvOscOn (normalCone C) (C ∩ frontier C) :=
  svOscOn_mono inter_subset_left (svOscOn_normalCone C)

/-- For a closed set, the normal-cone mapping is outer semicontinuous relative
to the whole frontier. -/
theorem svOscOn_normalCone_frontier {C : Set E} (hC : IsClosed C) :
    SvOscOn (normalCone C) (frontier C) :=
  svOscOn_mono hC.frontier_subset (svOscOn_normalCone C)

/-- The arbitrary-set generic-continuity statement supported by the
empty-off-`C` convention: discontinuities relative to `C ∩ frontier C` are
meager in that subtype. -/
theorem isMeagre_not_svContinuousWithinAt_normalCone_inter_frontier
    [FiniteDimensional ℝ E] (C : Set E) :
    IsMeagre
      {x : ↥(C ∩ frontier C) |
        ¬ SvContinuousWithinAt (normalCone C) (C ∩ frontier C) (x : E)} :=
  isMeagre_not_svContinuousWithinAt_of_svOscOn
    (svOscOn_normalCone_inter_frontier C)

/-- **Proposition 6.49**, meagerness clause for a closed set: failures of
continuity of the normal-cone mapping relative to the frontier form a meager
subset of the frontier subtype. -/
theorem isMeagre_not_svContinuousWithinAt_normalCone_frontier
    [FiniteDimensional ℝ E] {C : Set E} (hC : IsClosed C) :
    IsMeagre
      {x : frontier C |
        ¬ SvContinuousWithinAt (normalCone C) (frontier C) (x : E)} :=
  isMeagre_not_svContinuousWithinAt_of_svOscOn
    (svOscOn_normalCone_frontier hC)

/-- **Proposition 6.49**, density clause for a closed set: continuity points
of the normal-cone mapping relative to the frontier are dense in the frontier
subtype. -/
theorem dense_svContinuousWithinAt_normalCone_frontier
    [FiniteDimensional ℝ E] {C : Set E} (hC : IsClosed C) :
    Dense
      {x : frontier C |
        SvContinuousWithinAt (normalCone C) (frontier C) (x : E)} := by
  letI : CompleteSpace (frontier C) := isClosed_frontier.completeSpace_coe
  have hmeagre := isMeagre_not_svContinuousWithinAt_normalCone_frontier hC
  have hdense : Dense
      ({x : frontier C |
        ¬ SvContinuousWithinAt (normalCone C) (frontier C) (x : E)}ᶜ) :=
    dense_of_mem_residual hmeagre
  simpa only [compl_setOf, not_not] using hdense

end GenericNormalContinuity

end RW
