/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Coderivative duality and reachable Jacobians

Theorem 9.62, including the negligible-set exclusion refinement.
-/

import RockafellarWets.Chapter9.ClarkeReachableGradients
import RockafellarWets.Chapter9.StrictDerivativeSupport

open Filter Metric Set Topology MeasureTheory
open scoped NNReal InnerProductSpace

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The same negligible exceptional set may be used for every scalarization. -/
theorem scalarization_differentiability_complement_null
    {f : E → F} {O D : Set E} (hf : ∀ x ∈ O, StrictlyContinuousAt f x)
    (hnull : volume ({x ∈ O | DifferentiableAt ℝ f x} \ D) = 0) (y : F) :
    volume ({x ∈ O | DifferentiableAt ℝ (fun a ↦ ⟪y,f a⟫_ℝ) x} \ D) = 0 :=
  measure_mono_null (show {x ∈ O | DifferentiableAt ℝ (fun a ↦ ⟪y,f a⟫_ℝ) x} \ D ⊆ O \ D
    from fun _ h ↦ ⟨h.1.1,h.2⟩)
    (measure_compl_differentiability_approach_set_eq_zero volume hf hnull)

/-- **Theorem 9.62**, the common support value is attained by a reachable
Jacobian, with any negligible subset of differentiability points excluded. -/
theorem exists_max_inner_reachableJacobian
    {f : E → F} {O D : Set E} (hO : IsOpen O)
    (hf : ∀ x ∈ O, StrictlyContinuousAt f x) (hD : ∀ x ∈ D, DifferentiableAt ℝ f x)
    (hnull : volume ({x ∈ O | DifferentiableAt ℝ f x} \ D) = 0)
    {x : E} (hx : x ∈ O) (w : E) (y : F) :
    ∃ A ∈ reachableJacobians f D x,
      regularSubderivative (fun a ↦ (⟪y,f a⟫_ℝ : EReal)) x w = (⟪y,A w⟫_ℝ : EReal) ∧
      ∀ B ∈ reachableJacobians f D x, ⟪y,B w⟫_ℝ ≤ ⟪y,A w⟫_ℝ := by
  have hDs : ∀ a ∈ D, DifferentiableAt ℝ (fun z ↦ ⟪y,f z⟫_ℝ) a := fun a ha ↦
    ((innerSL ℝ y).hasFDerivAt.comp a (hD a ha).hasFDerivAt).differentiableAt
  obtain ⟨v,hv,he,hm⟩ := exists_max_reachableGradient_regularSubderivative hO
    (fun a ha ↦ (hf a ha).inner_const y) hDs
    (scalarization_differentiability_complement_null hf hnull y) hx w
  rw [reachableGradients_inner_comp (hf x hx) hD y] at hv hm
  obtain ⟨A,hA,rfl⟩ := hv
  refine ⟨A,hA,?_,fun B hB ↦ ?_⟩
  · simpa only [ContinuousLinearMap.adjoint_inner_left] using he
  · simpa only [ContinuousLinearMap.adjoint_inner_left] using hm _ ⟨B,hB,rfl⟩

/-- **Theorem 9.62**, all three equal maxima, with their witnesses. -/
theorem strictGraphicalDerivative_coderivative_reachableJacobian_maxima
    {f : E → F} {O D : Set E} (hO : IsOpen O)
    (hf : ∀ x ∈ O, StrictlyContinuousAt f x) (hD : ∀ x ∈ D, DifferentiableAt ℝ f x)
    (hnull : volume ({x ∈ O | DifferentiableAt ℝ f x} \ D) = 0)
    {x : E} (hx : x ∈ O) (w : E) (y : F) :
    ∃ z ∈ strictGraphicalDerivative (svSingleton f) x (f x) w,
      ∃ v ∈ coderivative (svSingleton f) x (f x) y,
        ∃ A ∈ reachableJacobians f D x,
          ⟪y,z⟫_ℝ = ⟪v,w⟫_ℝ ∧ ⟪y,z⟫_ℝ = ⟪y,A w⟫_ℝ ∧
          (∀ z' ∈ strictGraphicalDerivative (svSingleton f) x (f x) w,
            ⟪y,z'⟫_ℝ ≤ ⟪y,z⟫_ℝ) ∧
          (∀ v' ∈ coderivative (svSingleton f) x (f x) y, ⟪v',w⟫_ℝ ≤ ⟪v,w⟫_ℝ) ∧
          ∀ B ∈ reachableJacobians f D x, ⟪y,B w⟫_ℝ ≤ ⟪y,A w⟫_ℝ := by
  obtain ⟨z,hz,v,hv,hzv,hzm,hvm⟩ := (hf x hx).strictGraphicalDerivative_coderivative_max_duality w y
  obtain ⟨A,hA,he,hAm⟩ := exists_max_inner_reachableJacobian hO hf hD hnull hx w y
  have hsc : ERealStrictlyContinuousAt (fun a ↦ (⟪y,f a⟫_ℝ : EReal)) x :=
    ⟨by simp,by simpa only [EReal.toReal_coe] using (hf x hx).inner_const y⟩
  have hvalue : regularSubderivative (fun a ↦ (⟪y,f a⟫_ℝ : EReal)) x w = (⟪v,w⟫_ℝ : EReal) := by
    rw [hsc.regularSubderivative_eq_supportFunction]
    rw [coderivative_svSingleton_eq_subdifferential (hf x hx) y] at hv hvm
    exact le_antisymm ((supportFunction_le_iff _ _ _).mpr fun u hu ↦ EReal.coe_le_coe_iff.mpr (hvm u hu))
      (inner_le_supportFunction hv w)
  exact ⟨z,hz,v,hv,A,hA,hzv,hzv.trans (EReal.coe_injective (hvalue.symm.trans he)),hzm,hvm,hAm⟩

/-- **Theorem 9.62**, the convex-hull formula for coderivatives. -/
theorem convexHull_coderivative_eq_reachableJacobians
    {f : E → F} {O D : Set E} (hO : IsOpen O)
    (hf : ∀ x ∈ O, StrictlyContinuousAt f x) (hD : ∀ x ∈ D, DifferentiableAt ℝ f x)
    (hnull : volume ({x ∈ O | DifferentiableAt ℝ f x} \ D) = 0)
    {x : E} (hx : x ∈ O) (y : F) :
    convexHull ℝ (coderivative (svSingleton f) x (f x) y) =
      convexHull ℝ ((fun A : E →L[ℝ] F ↦ A.adjoint y) '' reachableJacobians f D x) ∧
    convexHull ℝ (coderivative (svSingleton f) x (f x) y) =
      (fun A : E →L[ℝ] F ↦ A.adjoint y) '' convexHull ℝ (reachableJacobians f D x) := by
  have hDs : ∀ a ∈ D, DifferentiableAt ℝ (fun z ↦ ⟪y,f z⟫_ℝ) a := fun a ha ↦
    ((innerSL ℝ y).hasFDerivAt.comp a (hD a ha).hasFDerivAt).differentiableAt
  have he := (clarke_reachableGradient_representation hO (fun a ha ↦ (hf a ha).inner_const y)
    hDs (scalarization_differentiability_complement_null hf hnull y) hx).2.2.2.1
  rw [reachableGradients_inner_comp (hf x hx) hD y] at he
  rw [coderivative_svSingleton_eq_subdifferential (hf x hx) y]
  exact ⟨he.symm,he.symm.trans (convexHull_image_adjoint_apply _ y)⟩

/-- **Theorem 9.62**, the convex-hull formula for strict graphical derivatives. -/
theorem convexHull_strictGraphicalDerivative_eq_reachableJacobians
    {f : E → F} {O D : Set E} (hO : IsOpen O)
    (hf : ∀ x ∈ O, StrictlyContinuousAt f x) (hD : ∀ x ∈ D, DifferentiableAt ℝ f x)
    (hnull : volume ({x ∈ O | DifferentiableAt ℝ f x} \ D) = 0)
    {x : E} (hx : x ∈ O) (w : E) :
    convexHull ℝ (strictGraphicalDerivative (svSingleton f) x (f x) w) =
      convexHull ℝ ((fun A : E →L[ℝ] F ↦ A w) '' reachableJacobians f D x) ∧
    convexHull ℝ (strictGraphicalDerivative (svSingleton f) x (f x) w) =
      (fun A : E →L[ℝ] F ↦ A w) '' convexHull ℝ (reachableJacobians f D x) := by
  have hxD := subset_closure_differentiability_set_of_null_complement volume hO hf hnull hx
  have hK := (reachableJacobians_nonempty_compact (hf x hx) hxD).2
  have he : convexHull ℝ (strictGraphicalDerivative (svSingleton f) x (f x) w) =
      convexHull ℝ ((fun A : E →L[ℝ] F ↦ A w) '' reachableJacobians f D x) := by
    apply convexHull_eq_of_supportFunction_eq ((hf x hx).strictGraphicalDerivative_nonempty_compact w).2
      (hK.image (continuous_id.clm_apply continuous_const))
    funext y
    rw [← (hf x hx).regularSubderivative_scalar_eq_support_strictGraphicalDerivative w y]
    obtain ⟨A,hA,he,hm⟩ := exists_max_inner_reachableJacobian hO hf hD hnull hx w y
    rw [he]
    apply le_antisymm
    · simpa only [real_inner_comm (A w) y] using
        inner_le_supportFunction (mem_image_of_mem (fun B : E →L[ℝ] F ↦ B w) hA) y
    · apply (supportFunction_le_iff _ _ _).mpr
      rintro z ⟨B,hB,rfl⟩
      exact EReal.coe_le_coe_iff.mpr (by simpa only [real_inner_comm (B w) y] using hm B hB)
  exact ⟨he,he.trans (convexHull_image_apply _ w)⟩

end RW
