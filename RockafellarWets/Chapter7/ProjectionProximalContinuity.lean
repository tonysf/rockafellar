/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Continuity of projection and proximal mappings
-/

import RockafellarWets.Chapter5.ProjectionMappings
import RockafellarWets.Chapter5.ProximalMappings

open Set

namespace RW

/-- **Example 7.44(a)**. Projection onto a nonempty closed set is outer
semicontinuous and locally bounded. -/
theorem projection_osc_and_locallyBounded {E : Type*} [NormedAddCommGroup E]
    {C : Set E} (hne : C.Nonempty) (hc : IsClosed C) :
    SvOsc (projMapping C) ∧ SvLocallyBounded (projMapping C) :=
  ⟨svOsc_projMapping hc, svLocallyBounded_projMapping hne⟩

/-- **Example 7.44(b)**. At a positive parameter below the prox-threshold,
the proximal mapping of a proper lower semicontinuous objective is outer
semicontinuous and locally bounded. -/
theorem proximalMappingEReal_osc_and_locallyBounded {E : Type*} [NormedAddCommGroup E]
    {f : E → EReal} (hp : IsProper f) (hl : LowerSemicontinuous f)
    {t : ℝ} (ht : 0 < t) (hthr : (t : EReal) < proxThreshold f) :
    SvOsc (proximalMappingEReal f t) ∧ SvLocallyBounded (proximalMappingEReal f t) :=
  svOsc_and_svLocallyBounded_proxMappingEReal hp hl ht hthr

end RW
