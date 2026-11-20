/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Support functions of reachable gradients
-/

import RockafellarWets.Chapter9.ReachableDerivatives
import RockafellarWets.Chapter9.LipschitzSubderivatives
import RockafellarWets.Chapter8.ClarkeSubgradientRepresentations
import RockafellarWets.Chapter2.ConvexHulls

open Filter Metric Set Topology MeasureTheory
open scoped NNReal InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- At a strictly continuous point, Clarke subgradients are exactly the
convex hull of limiting subgradients; compactness removes the closure. -/
theorem ERealStrictlyContinuousAt.clarkeSubdifferential_eq_convexHull
    {f : E → EReal} {x : E} (hf : ERealStrictlyContinuousAt f x) :
    clarkeSubdifferential f x = convexHull ℝ (subdifferential f x) := by
  rw [clarkeSubdifferential_eq_setOf_inner_le_regularSubderivative hf.finite hf.isLocallyLscAt,
    funext hf.regularSubderivative_eq_supportFunction]
  change linearMinorantSet (supportFunction (subdifferential f x)) = _
  rw [linearMinorantSet_supportFunction]
  exact (isCompact_convexHull hf.subdifferential_nonempty_compact.2).isClosed.closure_eq

/-- The support function of a compact set of reachable gradients attains
its value. This includes arbitrary prescribed dense approach sets. -/
theorem exists_max_inner_reachableGradients {f : E → ℝ} {D : Set E} {x : E}
    (hf : StrictlyContinuousAt f x) (hx : x ∈ closure D) (w : E) :
    ∃ v ∈ reachableGradients f D x,
      supportFunction (reachableGradients f D x) w = (⟪v,w⟫_ℝ : EReal) ∧
      ∀ z ∈ reachableGradients f D x, ⟪z,w⟫_ℝ ≤ ⟪v,w⟫_ℝ := by
  obtain ⟨hne,hcomp⟩ := reachableGradients_nonempty_compact hf hx
  obtain ⟨v,hv,hmax⟩ := hcomp.exists_isMaxOn hne
    ((continuous_id.inner continuous_const : Continuous (fun z : E ↦ ⟪z,w⟫_ℝ)).continuousOn)
  exact ⟨v,hv,le_antisymm ((supportFunction_le_iff _ _ _).mpr fun z hz ↦
    EReal.coe_le_coe_iff.mpr (hmax hz)) (inner_le_supportFunction hv w),hmax⟩

/-- Any strict upper bound on all reachable directional gradients is an
upper bound on the gradients sufficiently near the base point. -/
theorem eventually_inner_gradient_lt_of_reachableGradients {f : E → ℝ} {D : Set E} {x : E}
    (hf : StrictlyContinuousAt f x) {w : E} {a : ℝ}
    (ha : ∀ v ∈ reachableGradients f D x, ⟪v,w⟫_ℝ < a) :
    ∀ᶠ y in 𝓝[D] x, ⟪gradient f y,w⟫_ℝ < a := by
  obtain ⟨k,hk⟩ := hf.eventually_norm_fderiv_le
  apply eventually_mem_of_clusterValuesWithin_subset (isCompact_closedBall 0 k)
    (U := {v : E | ⟪v,w⟫_ℝ < a})
  · filter_upwards [mem_nhdsWithin_of_mem_nhds hk] with y hy
    simpa only [mem_closedBall,dist_zero_right,gradient,LinearIsometryEquiv.norm_map] using hy
  · exact isOpen_lt (continuous_id.inner continuous_const) continuous_const
  · exact ha

/-- Equality of compact support functions identifies the actual convex
hulls, without inserting any closures. -/
theorem convexHull_eq_of_supportFunction_eq {C D : Set E}
    (hC : IsCompact C) (hD : IsCompact D) (he : supportFunction C = supportFunction D) :
    convexHull ℝ C = convexHull ℝ D := by
  have he' := congrArg linearMinorantSet he
  simpa only [linearMinorantSet_supportFunction,
    (isCompact_convexHull hC).isClosed.closure_eq,
    (isCompact_convexHull hD).isClosed.closure_eq] using he'

/-- A strict support bound on reachable gradients becomes an almost
everywhere directional-gradient bound on a Lipschitz ball. The approach
set may omit any null subset of the differentiability points. -/
theorem exists_lipschitz_ball_ae_inner_gradient_lt
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {f : E → ℝ} {O D : Set E} (hO : IsOpen O)
    (hf : ∀ y ∈ O, StrictlyContinuousAt f y) (hD : ∀ y ∈ D, DifferentiableAt ℝ f y)
    (hnull : μ ({y ∈ O | DifferentiableAt ℝ f y} \ D) = 0)
    {x w : E} (hx : x ∈ O) {a : ℝ}
    (ha : ∀ v ∈ reachableGradients f D x, ⟪v,w⟫_ℝ < a) :
    ∃ r : ℝ, 0 < r ∧ ball x r ⊆ O ∧ ∃ k : ℝ≥0,
      LipschitzOnWith k f (ball x r) ∧
      ∀ᵐ y ∂μ, y ∈ ball x r → DifferentiableAt ℝ f y ∧ ⟪gradient f y,w⟫_ℝ < a := by
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ D → ⟪gradient f y,w⟫_ℝ < a :=
    mem_nhdsWithin_iff_eventually.mp (eventually_inner_gradient_lt_of_reachableGradients (hf x hx) ha)
  obtain ⟨k,U,hU,hL⟩ := strictlyContinuousAt_iff.mp (hf x hx)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (inter_mem (hO.mem_nhds hx) (inter_mem hU hnear))
  refine ⟨r,hr,fun y hy ↦ (hball hy).1,k,
    hL.mono (fun y hy ↦ (hball hy).2.1),?_⟩
  filter_upwards [ae_mem_differentiability_set_of_null_complement μ hf hnull] with y hy hyball
  have hyD := hy (hball hyball).1
  exact ⟨hD y hyD,(hball hyball).2.2 hyD⟩

/-- A uniform eventual bound on moving-base increments bounds the regular
subderivative in the same direction. -/
theorem regularSubderivative_le_of_eventual_increment_bound
    {f : E → ℝ} {x w : E} (hf : StrictlyContinuousAt f x) {a : ℝ}
    (hbound : ∀ᶠ p : E × ℝ in 𝓝 x ×ˢ 𝓝[>] (0 : ℝ),
      f (p.1 + p.2 • w) - f p.1 ≤ p.2 * a) :
    regularSubderivative (fun y ↦ (f y : EReal)) x w ≤ (a : EReal) := by
  have hsc : ERealStrictlyContinuousAt (fun y ↦ (f y : EReal)) x :=
    ⟨by simp,by simpa only [EReal.toReal_coe] using hf⟩
  rw [hsc.regularSubderivative_eq_limsup_differenceQuotient]
  apply limsup_le_of_le (by isBoundedDefault)
  filter_upwards [hbound,
    (show Tendsto (Prod.snd : E × ℝ → ℝ) (𝓝 x ×ˢ 𝓝[>] (0 : ℝ)) (𝓝[>] 0)
      from tendsto_snd).eventually self_mem_nhdsWithin] with p hp hpos
  rw [differenceQuotient_eq_coe (f := fun y ↦ (f y : EReal)) rfl rfl,
    EReal.coe_le_coe_iff,inv_mul_le_iff₀ hpos]
  exact hp

/-- The support bound supplies the remaining inclusion in the reachable
gradient representation. The reverse inequality is already guaranteed by
the inclusion of reachable gradients in the limiting subdifferential. -/
theorem regularSubderivative_eq_support_reachableGradients_of_le
    {f : E → ℝ} {D : Set E} {x : E} (hf : StrictlyContinuousAt f x)
    (hD : ∀ y ∈ D, DifferentiableAt ℝ f y)
    (hle : ∀ w, regularSubderivative (fun y ↦ (f y : EReal)) x w ≤
      supportFunction (reachableGradients f D x) w) :
    regularSubderivative (fun y ↦ (f y : EReal)) x =
      supportFunction (reachableGradients f D x) := by
  have hsc : ERealStrictlyContinuousAt (fun y ↦ (f y : EReal)) x :=
    ⟨by simp,by simpa only [EReal.toReal_coe] using hf⟩
  funext w
  apply le_antisymm (hle w)
  rw [hsc.regularSubderivative_eq_supportFunction]
  exact supportFunction_mono (reachableGradients_subset_subdifferential hf.continuousAt hD) w

/-- Compact support equality yields both convex-hull identities in the
Clarke reachable-gradient representation. -/
theorem convexHull_reachableGradients_eq_of_support_eq
    {f : E → ℝ} {D : Set E} {x : E} (hf : StrictlyContinuousAt f x) (hx : x ∈ closure D)
    (he : regularSubderivative (fun y ↦ (f y : EReal)) x =
      supportFunction (reachableGradients f D x)) :
    convexHull ℝ (reachableGradients f D x) = convexHull ℝ (subdifferential (fun y ↦ (f y : EReal)) x) ∧
      convexHull ℝ (reachableGradients f D x) = clarkeSubdifferential (fun y ↦ (f y : EReal)) x := by
  have hsc : ERealStrictlyContinuousAt (fun y ↦ (f y : EReal)) x :=
    ⟨by simp,by simpa only [EReal.toReal_coe] using hf⟩
  have hh : convexHull ℝ (reachableGradients f D x) =
      convexHull ℝ (subdifferential (fun y ↦ (f y : EReal)) x) :=
    convexHull_eq_of_supportFunction_eq (reachableGradients_nonempty_compact hf hx).2
      hsc.subdifferential_nonempty_compact.2
      (he.symm.trans (funext hsc.regularSubderivative_eq_supportFunction))
  exact ⟨hh,hh.trans hsc.clarkeSubdifferential_eq_convexHull.symm⟩

end RW
