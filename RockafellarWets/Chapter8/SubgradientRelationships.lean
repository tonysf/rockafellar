/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Closedness, convexity, and inclusions for subdifferentials
-/

import RockafellarWets.Chapter8.RegularSubgradientBridge
import RockafellarWets.Chapter8.SubgradientLimits
import RockafellarWets.Chapter8.SupportFunctions
import RockafellarWets.Chapter8.SubderivativeFormulas

open Filter Set Topology
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {f : E → EReal} {x : E} {c : ℝ}

/-- **Theorem 8.6**. The regular subdifferential embeds in the limiting one. -/
theorem regularSubdifferential_subset_subdifferential (f : E → EReal) (x : E) :
    regularSubdifferential f x ⊆ subdifferential f x := by
  intro v hv
  obtain ⟨c, hx⟩ : ∃ c : ℝ, f x = c := ⟨hv.choose, hv.choose_spec.1⟩
  exact mem_subdifferential_iff_exists_seq.mpr ⟨⟨c, hx⟩, fun _ ↦ x, fun _ ↦ v,
    tendsto_const_nhds, tendsto_const_nhds, fun _ ↦ hv, tendsto_const_nhds⟩

/-- The horizon cone to the regular subdifferential is contained in the
horizon subdifferential. -/
theorem horizonCone_regularSubdifferential_subset [FiniteDimensional ℝ E] (hx : f x = c) :
    horizonCone (regularSubdifferential f x) ⊆ horizonSubdifferential f x := by
  rw [horizonSubdifferential_of_finite hx]
  have hinc : regularSubdifferential f x ⊆ innerSetLimitAlong (pure x)
      (regularSubdifferential f) := fun v hv V hV ↦ show _ from
        (mem_pure.mpr ⟨v, hv, mem_of_mem_nhds hV⟩)
  exact (horizonCone_subset_horizonInnerSetLimitAlong hinc).trans
    ((horizonInnerSetLimitAlong_subset_horizonOuterSetLimitAlong _ _).trans
      (cosmicDirectionCone_mono (outerSetLimitAlong_mono_filter (pure_le_attentiveNhds f x) _)))

/-- **Theorem 8.6.** The regular subdifferential is closed and convex, the
limiting subdifferential is closed, and both horizon cones are closed, with
the horizon of the regular subdifferential also convex. -/
theorem subdifferential_properties [FiniteDimensional ℝ E] (hx : f x = c) :
    IsClosed (regularSubdifferential f x) ∧ Convex ℝ (regularSubdifferential f x) ∧
    IsClosed (subdifferential f x) ∧ IsClosed (horizonSubdifferential f x) ∧
    IsCone (horizonSubdifferential f x) ∧ IsClosed (horizonCone (regularSubdifferential f x)) ∧
    IsCone (horizonCone (regularSubdifferential f x)) ∧
    Convex ℝ (horizonCone (regularSubdifferential f x)) := by
  have heq : regularSubdifferential f x = linearMinorantSet (subderivative f x) :=
    regularSubdifferential_eq_setOf_inner_le_subderivative hx
  have hc : Convex ℝ (regularSubdifferential f x) := heq ▸ convex_linearMinorantSet _
  rw [subdifferential_of_finite hx, horizonSubdifferential_of_finite hx]
  exact ⟨heq ▸ isClosed_linearMinorantSet _, hc, isClosed_outerSetLimitAlong _ _,
    isClosed_horizonOuterSetLimitAlong _ _, isCone_horizonOuterSetLimitAlong _ _,
    isClosed_horizonCone _, isCone_horizonCone _, convex_horizonCone hc⟩

end RW
