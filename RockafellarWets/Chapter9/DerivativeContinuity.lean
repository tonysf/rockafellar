/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Derivative continuity at points of strict differentiability
-/

import RockafellarWets.Chapter9.ReachableDerivatives
import RockafellarWets.Chapter9.SmoothLipschitzModulus
import RockafellarWets.Chapter9.ReachableJacobianDuality
import RockafellarWets.Chapter9.StrictDerivativeLinearity

open Filter Metric Set Topology
open scoped NNReal

namespace RW

section Normed

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The forward implication of **Exercise 9.64**, in arbitrary real normed
spaces: at a point of strict differentiability, the derivatives converge to
the strict derivative along any set of differentiability points. -/
theorem HasStrictFDerivAt.tendsto_fderiv {f : E → F} {A : E →L[ℝ] F} {x : E}
    (hf : HasStrictFDerivAt f A x) {D : Set E}
    (hD : ∀ y ∈ D, DifferentiableAt ℝ f y) :
    Tendsto (fderiv ℝ f) (𝓝[D] x) (𝓝 A) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let k : ℝ≥0 := ⟨ε / 2,(half_pos hε).le⟩
  have hres : HasStrictFDerivAt (fun y ↦ f y - A y) (0 : E →L[ℝ] F) x := by
    simpa only [sub_self] using hf.sub A.hasStrictFDerivAt
  obtain ⟨U,hU,hL⟩ := hres.exists_lipschitzOnWith_of_nnnorm_lt k
    (by simpa only [nnnorm_zero,NNReal.coe_pos] using half_pos hε)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hU
  filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hr),self_mem_nhdsWithin]
    with y hy hyD
  have hdy : HasFDerivAt (fun z ↦ f z - A z) (fderiv ℝ f y - A) y :=
    (hD y hyD).hasFDerivAt.sub A.hasFDerivAt
  have hnorm := hdy.le_of_lipschitzOn (isOpen_ball.mem_nhds hy) (hL.mono hball)
  rw [dist_eq_norm]
  exact (show ‖fderiv ℝ f y - A‖ ≤ ε/2 from hnorm).trans_lt (half_lt_self hε)

/-- **Exercise 9.64**, (a) ⇒ (b). -/
theorem HasStrictFDerivAt.continuousWithinAt_fderiv {f : E → F} {A : E →L[ℝ] F} {x : E}
    (hf : HasStrictFDerivAt f A x) :
    DifferentiableAt ℝ f x ∧
      ContinuousWithinAt (fderiv ℝ f) {y | DifferentiableAt ℝ f y} x := by
  refine ⟨hf.differentiableAt,?_⟩
  change Tendsto _ _ (𝓝 (fderiv ℝ f x))
  rw [hf.hasFDerivAt.fderiv]
  exact HasStrictFDerivAt.tendsto_fderiv hf fun _ hy ↦ hy

end Normed

section FiniteDimensional

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Relative derivative continuity collapses the entire reachable-Jacobian
set to the derivative at the base point. -/
theorem reachableJacobians_eq_singleton_of_continuousWithinAt
    {f : E → F} {D : Set E} {x : E} (hx : x ∈ D)
    (hc : ContinuousWithinAt (fderiv ℝ f) D x) :
    reachableJacobians f D x = {fderiv ℝ f x} := by
  ext A
  constructor
  · intro hA
    obtain ⟨y,hy,hyt,hAt⟩ := mem_clusterValuesWithin_iff.mp hA
    have hct : Tendsto (fderiv ℝ f) (𝓝[D] x) (𝓝 (fderiv ℝ f x)) := hc
    exact tendsto_nhds_unique hAt (hct.comp (tendsto_nhdsWithin_of_forall_mem hy hyt))
  · intro hA
    have he : A = fderiv ℝ f x := hA
    subst A
    exact mem_clusterValuesWithin_iff.mpr ⟨fun _ ↦ x,fun _ ↦ hx,tendsto_const_nhds,tendsto_const_nhds⟩

/-- For a strictly continuous mapping, having a unique reachable Jacobian
is equivalent to continuity of the derivative along the approach set. -/
theorem reachableJacobians_eq_singleton_iff_continuousWithinAt
    {f : E → F} {D : Set E} {x : E} (hf : StrictlyContinuousAt f x) (hx : x ∈ D) :
    reachableJacobians f D x = {fderiv ℝ f x} ↔
      ContinuousWithinAt (fderiv ℝ f) D x := by
  constructor
  · intro he
    obtain ⟨k,hk⟩ := hf.eventually_norm_fderiv_le
    apply tendsto_of_clusterValuesWithin_subset_singleton (isCompact_closedBall 0 k)
    · filter_upwards [mem_nhdsWithin_of_mem_nhds hk] with y hy
      simpa only [mem_closedBall,dist_zero_right] using hy
    · exact he.subset
  · exact reachableJacobians_eq_singleton_of_continuousWithinAt hx

/-- **Exercise 9.64**: strict differentiability is equivalent to
differentiability and continuity of the derivative relative to the set of
differentiability points in the open domain. -/
theorem hasStrictFDerivAt_iff_differentiableAt_continuousWithinAt_fderiv
    [MeasurableSpace E] [BorelSpace E] {f : E → F} {O : Set E} (hO : IsOpen O)
    (hf : ∀ y ∈ O, StrictlyContinuousAt f y) {x : E} (hx : x ∈ O) :
    HasStrictFDerivAt f (fderiv ℝ f x) x ↔ DifferentiableAt ℝ f x ∧
      ContinuousWithinAt (fderiv ℝ f) {y ∈ O | DifferentiableAt ℝ f y} x := by
  constructor
  · intro hs
    exact ⟨hs.differentiableAt,HasStrictFDerivAt.tendsto_fderiv hs fun _ hy ↦ hy.2⟩
  · rintro ⟨hd,hc⟩
    have hxD : x ∈ {y ∈ O | DifferentiableAt ℝ f y} := ⟨hx,hd⟩
    have hJ := reachableJacobians_eq_singleton_of_continuousWithinAt hxD hc
    apply (hasStrictFDerivAt_iff_strictGraphicalDerivative_linear (hf x hx).continuousAt).mpr
    funext w
    change strictGraphicalDerivative (svSingleton f) x (f x) w = {fderiv ℝ f x w}
    have hh := (convexHull_strictGraphicalDerivative_eq_reachableJacobians hO hf
      (D := {y ∈ O | DifferentiableAt ℝ f y}) (fun _ hy ↦ hy.2) (by simp) hx w).2
    rw [hJ,convexHull_singleton,image_singleton] at hh
    have hsub : strictGraphicalDerivative (svSingleton f) x (f x) w ⊆ {fderiv ℝ f x w} :=
      (subset_convexHull ℝ _).trans hh.subset
    obtain ⟨v,hv⟩ := ((hf x hx).strictGraphicalDerivative_nonempty_compact w).1
    exact hsub.antisymm (singleton_subset_iff.mpr ((mem_singleton_iff.mp (hsub hv)) ▸ hv))

/-- The existence form of **Exercise 9.64**, matching strict
differentiability without prescribing the derivative in advance. -/
theorem strictlyDifferentiable_iff_differentiableAt_continuousWithinAt_fderiv
    [MeasurableSpace E] [BorelSpace E] {f : E → F} {O : Set E} (hO : IsOpen O)
    (hf : ∀ y ∈ O, StrictlyContinuousAt f y) {x : E} (hx : x ∈ O) :
    (∃ A : E →L[ℝ] F, HasStrictFDerivAt f A x) ↔ DifferentiableAt ℝ f x ∧
      ContinuousWithinAt (fderiv ℝ f) {y ∈ O | DifferentiableAt ℝ f y} x := by
  rw [← hasStrictFDerivAt_iff_differentiableAt_continuousWithinAt_fderiv hO hf hx]
  exact ⟨fun ⟨A,hA⟩ ↦ hA.hasFDerivAt.fderiv.symm ▸ hA,fun h ↦ ⟨_,h⟩⟩

end FiniteDimensional

end RW
