/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A coderivative criterion for Lipschitz invertibility
-/

import RockafellarWets.Chapter9.ReachableJacobianDuality
import RockafellarWets.Chapter9.InverseLocalizations

open Filter Metric Set Topology MeasureTheory
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Corollary 9.63**: if zero belongs to the convex hull of the limiting
subgradients of a scalarization only for the zero covector, the inverse has
a Lipschitz single-valued localization. -/
theorem hasLipschitzInverseLocalization_of_convexHull_subdifferential_kernel_zero
    {f : E → E} {x : E} (hf : StrictlyContinuousAt f x)
    (hkernel : ∀ y : E, (0 : E) ∈ convexHull ℝ
      (subdifferential (fun a ↦ (⟪y,f a⟫_ℝ : EReal)) x) → y = 0) :
    HasLipschitzSingleValuedLocalization (svInv (svSingleton f)) (f x) x := by
  let O := {a | StrictlyContinuousAt f a}
  let D := {a ∈ O | DifferentiableAt ℝ f a}
  have hO : IsOpen O := isOpen_setOf_strictlyContinuousAt f
  have hx : x ∈ O := hf
  have hstrict : ∀ a ∈ O, StrictlyContinuousAt f a := fun _ ha ↦ ha
  have hdiff : ∀ a ∈ D, DifferentiableAt ℝ f a := fun _ ha ↦ ha.2
  have hnull : volume ({a ∈ O | DifferentiableAt ℝ f a} \ D) = 0 := by simp [D]
  have hAdj (A : E →L[ℝ] E) (hA : A ∈ convexHull ℝ (reachableJacobians f D x))
      (y : E) (hy : A.adjoint y = 0) : y = 0 := by
    apply hkernel y
    rw [← coderivative_svSingleton_eq_subdifferential hf y,
      (convexHull_coderivative_eq_reachableJacobians hO hstrict hdiff hnull hx y).2]
    exact ⟨A,hA,hy⟩
  have hKer (A : E →L[ℝ] E) (hA : A ∈ convexHull ℝ (reachableJacobians f D x))
      (w : E) (hw : A w = 0) : w = 0 := by
    have hi : Function.Injective A.adjoint := by
      intro y z he
      apply sub_eq_zero.mp
      apply hAdj A hA
      rw [map_sub,he,sub_self]
    obtain ⟨y,hy⟩ := LinearMap.surjective_of_injective (f := A.adjoint.toLinearMap) hi w
    change A.adjoint y = w at hy
    apply real_inner_self_nonpos.mp
    apply le_of_eq
    calc ⟪w,w⟫_ℝ = ⟪A.adjoint y,w⟫_ℝ := by rw [hy]
      _ = ⟪y,A w⟫_ℝ := ContinuousLinearMap.adjoint_inner_left A w y
      _ = 0 := by rw [hw,inner_zero_right]
  have hzero : svInv (strictGraphicalDerivative (fun a ↦ {f a}) x (f x)) 0 = {0} := by
    ext w
    constructor
    · intro hw
      have hw' : (0 : E) ∈ strictGraphicalDerivative (svSingleton f) x (f x) w := hw
      have hm := subset_convexHull ℝ _ hw'
      rw [(convexHull_strictGraphicalDerivative_eq_reachableJacobians hO hstrict hdiff hnull hx w).2] at hm
      obtain ⟨A,hA,hAw⟩ := hm
      exact hKer A hA w hAw
    · intro hw
      have hw0 : w = 0 := hw
      subst w
      exact (svPositivelyHomogeneous_strictGraphicalDerivative
        (S := fun a ↦ {f a}) (mem_singleton (f x))).1
  exact (hasLipschitzInverseLocalization_iff_strictKernel_zero hO hx
    (fun a ha ↦ (hstrict a ha).continuousAt.continuousWithinAt)).mpr hzero

end RW
