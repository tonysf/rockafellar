/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Strictly differentiable inner compositions
-/

import RockafellarWets.Chapter10.InnerCompositionRegularity
import RockafellarWets.Chapter9.SingleValuedStrictDifferentiability

open Filter Set Topology

namespace RW

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  {S : F → Set G} {f : E → F} {x : E} {u : G} {A : E →L[ℝ] F}

/-- The strictly differentiable specialization of 10.40 does not require
continuous differentiability on a neighborhood. -/
theorem inner_comp_regular_of_hasStrictFDerivAt (hS : SvOsc S)
    (hf : HasStrictFDerivAt f A x) (hu : u ∈ S (f x))
    (hQ : ∀ z ∈ coderivative S (f x) u 0, A.adjoint z = 0 → z = 0)
    (hrS : IsGraphicallyRegularAt S (f x) u) :
    IsGraphicallyRegularAt (fun a ↦ S (f a)) x u ∧
      ∀ y, coderivative (fun a ↦ S (f a)) x u y = A.adjoint '' coderivative S (f x) u y := by
  have hfc : StrictlyContinuousAt f x := strictlyContinuousAt_iff.mpr hf.exists_lipschitzOnWith
  have hQ' : ∀ z ∈ coderivative S (f x) u 0,
      (0:E) ∈ coderivative (svSingleton f) x (f x) z → z = 0 := by
    intro z hz hv
    rw [coderivative_singleton_of_hasStrictFDerivAt hf,mem_svSingleton] at hv
    exact hQ z hz hv.symm
  have heS := (isGraphicallyRegularAt_iff_coderivative_eq_regular hrS.1).mp hrS
  have hlower (y : G) : A.adjoint '' coderivative S (f x) u y ⊆
      regularCoderivative (fun a ↦ S (f a)) x u y := by
    rintro v ⟨z,hz,rfl⟩
    apply regularCoderivative_inner_comp_superset hfc hu y
    refine mem_svComp.mpr ⟨z,heS ▸ hz,?_⟩
    rw [regularCoderivative_singleton_of_hasStrictFDerivAt hf]
    rfl
  have hupper (y : G) : coderivative (fun a ↦ S (f a)) x u y ⊆
      A.adjoint '' coderivative S (f x) u y := by
    intro v hv
    obtain ⟨z,hz,hv⟩ := mem_svComp.mp (coderivative_inner_comp_subset hS hfc hQ' y hv)
    rw [coderivative_singleton_of_hasStrictFDerivAt hf,mem_svSingleton] at hv
    exact ⟨z,hz,hv.symm⟩
  have he : coderivative (fun a ↦ S (f a)) x u = regularCoderivative (fun a ↦ S (f a)) x u := by
    funext y
    exact Subset.antisymm ((hupper y).trans (hlower y))
      ((graphicalDerivative_properties (S := fun a ↦ S (f a)) hu).2.2.2.2.2 y)
  exact ⟨(isGraphicallyRegularAt_iff_coderivative_eq_regular
    (isLocallyClosedAt_euclideanGraph_inner_comp hS hfc)).mpr he,
    fun y ↦ Subset.antisymm (hupper y) (by rw [he]; exact hlower y)⟩

end RW
