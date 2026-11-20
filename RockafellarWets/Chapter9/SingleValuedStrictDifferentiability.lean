/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: Strict differentiability of single-valued mappings

Exercise 9.25(c,d). Scalar strict gradients assemble in an orthonormal basis;
the resulting coderivative is the adjoint of the ordinary derivative.
-/

import RockafellarWets.Chapter9.SingleValuedDifferentiability
import RockafellarWets.Chapter9.SingleValuedGraphicalDerivatives
import RockafellarWets.Chapter9.CoderivativeNorms
import RockafellarWets.Chapter9.SmoothnessCriteria
import Mathlib.Analysis.Calculus.FDeriv.Prod

open Filter Metric Set Topology
open scoped InnerProductSpace NNReal ENNReal

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  {f : E → F} {x : E} {L : E →L[ℝ] F}

omit [FiniteDimensional ℝ E] in
/-- Scalar strict derivatives assemble into a vector strict derivative. -/
theorem exists_hasStrictFDerivAt_of_inner
    (h : ∀ y : F, ∃ v : E, HasStrictFDerivAt (fun z ↦ ⟪y,f z⟫_ℝ) (innerSL ℝ v) x) :
    ∃ L : E →L[ℝ] F, HasStrictFDerivAt f L x := by
  classical
  let b := stdOrthonormalBasis ℝ F
  let Q : F ≃L[ℝ] (Fin (Module.finrank ℝ F) → ℝ) := b.toBasis.equivFun.toContinuousLinearEquiv
  have hQ (y : F) (i : Fin (Module.finrank ℝ F)) : Q y i = ⟪b i,y⟫_ℝ := by
    change b.toBasis.equivFun y i = _
    rw [b.coe_toBasis_repr]
    exact b.repr_apply_apply y i
  choose v hv using fun i ↦ h (b i)
  let B : E →L[ℝ] (Fin (Module.finrank ℝ F) → ℝ) := ContinuousLinearMap.pi (fun i ↦ innerSL ℝ (v i))
  have hB : HasStrictFDerivAt (fun z i ↦ ⟪b i,f z⟫_ℝ) B x := hasStrictFDerivAt_pi.mpr hv
  refine ⟨Q.symm.toContinuousLinearMap.comp B,?_⟩
  have hh := Q.symm.toContinuousLinearMap.hasStrictFDerivAt.comp x hB
  convert hh using 1
  funext z
  have heq : (fun i ↦ ⟪b i,f z⟫_ℝ) = Q (f z) := funext (fun i ↦ (hQ (f z) i).symm)
  rw [heq]
  exact (Q.symm_apply_apply (f z)).symm

/-- A strict vector derivative yields the strict gradient of every
scalarization, with the adjoint formula. -/
theorem hasStrictGradientAt_inner_of_hasStrictFDerivAt (h : HasStrictFDerivAt f L x) (y : F) :
    HasStrictGradientAt (fun z ↦ ((⟪y,f z⟫_ℝ:ℝ):EReal)) (L.adjoint y) x := by
  refine ⟨.of_forall (fun _ ↦ by simp),?_⟩
  have heq : (innerSL ℝ y).comp L = innerSL ℝ (L.adjoint y) := by
    ext w
    exact (ContinuousLinearMap.adjoint_inner_left L w y).symm
  have hh := (innerSL ℝ y).hasStrictFDerivAt.comp x h
  simpa only [EReal.toReal_coe,heq,innerSL_apply_apply] using hh

/-- **Exercise 9.25(c)**, the adjoint coderivative formula. -/
theorem coderivative_singleton_of_hasStrictFDerivAt (h : HasStrictFDerivAt f L x) :
    coderivative (svSingleton f) x (f x) = svSingleton L.adjoint := by
  have hsc : StrictlyContinuousAt f x := strictlyContinuousAt_iff.mpr h.exists_lipschitzOnWith
  funext y
  rw [coderivative_svSingleton_eq_subdifferential hsc y]
  exact (hasStrictGradientAt_inner_of_hasStrictFDerivAt h y).subdifferential_eq

/-- The regular coderivative has the same adjoint formula. -/
theorem regularCoderivative_singleton_of_hasStrictFDerivAt (h : HasStrictFDerivAt f L x) :
    regularCoderivative (svSingleton f) x (f x) = svSingleton L.adjoint := by
  have hsc : StrictlyContinuousAt f x := strictlyContinuousAt_iff.mpr h.exists_lipschitzOnWith
  funext y
  rw [regularCoderivative_svSingleton_eq_regularSubdifferential hsc y]
  have hg := hasStrictGradientAt_inner_of_hasStrictFDerivAt h y
  change regularSubdifferential _ x = {L.adjoint y}
  apply Subset.antisymm
  · rw [← hg.subdifferential_eq]
    exact regularSubdifferential_subset_subdifferential _ _
  · exact singleton_subset_iff.mpr hg.mem_regularSubdifferential

/-- **Exercise 9.25(c)**. Under strict continuity, singleton coderivative
fibers force strict differentiability. -/
theorem exists_hasStrictFDerivAt_iff_coderivative_singleValued :
    (∃ L : E →L[ℝ] F, HasStrictFDerivAt f L x) ↔
      StrictlyContinuousAt f x ∧ ∀ y, (coderivative (svSingleton f) x (f x) y).Subsingleton := by
  constructor
  · rintro ⟨L,hL⟩
    refine ⟨strictlyContinuousAt_iff.mpr hL.exists_lipschitzOnWith,fun y ↦ ?_⟩
    rw [coderivative_singleton_of_hasStrictFDerivAt hL]
    exact subsingleton_singleton
  · rintro ⟨hsc,hs⟩
    apply exists_hasStrictFDerivAt_of_inner
    intro y
    obtain ⟨v,hv⟩ := (coderivative_svSingleton_nonempty_compact hsc y).1
    have heq := (hs y).eq_singleton_of_mem hv
    rw [coderivative_svSingleton_eq_subdifferential hsc y] at heq
    have hg := hasStrictGradientAt_of_subdifferential_eq (hsc.eRealStrictlyContinuousAt_inner y) heq
    exact ⟨v,by simpa only [EReal.toReal_coe] using hg.2⟩

/-- Strict differentiability gives graphical regularity even without a
neighborhood `C¹` assumption. -/
theorem isGraphicallyRegularAt_singleton_of_hasStrictFDerivAt (h : HasStrictFDerivAt f L x) :
    IsGraphicallyRegularAt (svSingleton f) x (f x) := by
  have hsc : StrictlyContinuousAt f x := strictlyContinuousAt_iff.mpr h.exists_lipschitzOnWith
  have hl := hsc.hasAubinProperty_singleton.2.2.1
  have hl' : IsLocallyClosedAt (euclideanSvGraph (svSingleton f)) (WithLp.toLp 2 (x,f x)) :=
    hl.preimage_continuousLinearEquiv (WithLp.prodContinuousLinearEquiv 2 ℝ E F)
  apply (isGraphicallyRegularAt_iff_coderivative_eq_regular hl').mpr
  rw [coderivative_singleton_of_hasStrictFDerivAt h,regularCoderivative_singleton_of_hasStrictFDerivAt h]

/-- **Exercise 9.25(d)**. Strict continuity and graphical regularity together
are exactly strict differentiability. -/
theorem exists_hasStrictFDerivAt_iff_graphicallyRegular :
    (∃ L : E →L[ℝ] F, HasStrictFDerivAt f L x) ↔
      StrictlyContinuousAt f x ∧ IsGraphicallyRegularAt (svSingleton f) x (f x) := by
  constructor
  · rintro ⟨L,hL⟩
    exact ⟨strictlyContinuousAt_iff.mpr hL.exists_lipschitzOnWith,isGraphicallyRegularAt_singleton_of_hasStrictFDerivAt hL⟩
  · rintro ⟨hsc,hreg⟩
    apply exists_hasStrictFDerivAt_iff_coderivative_singleValued.mpr
    refine ⟨hsc,fun y ↦ ?_⟩
    have heq := (isGraphicallyRegularAt_iff_coderivative_eq_regular hreg.1).mp hreg
    rw [regularCoderivative_eq_upperAdjoint (show f x ∈ svSingleton f x from rfl)] at heq
    obtain ⟨vneg,hvneg⟩ := (coderivative_svSingleton_nonempty_compact hsc (-y)).1
    have hzero (v : E) (hv : v ∈ coderivative (svSingleton f) x (f x) y) : v+vneg = 0 := by
      rw [heq] at hv hvneg
      obtain ⟨z,hz⟩ := hsc.calmAt.graphicalDerivative_nonempty (v+vneg)
      have hh := add_le_add (hv _ _ hz) (hvneg _ _ hz)
      rw [inner_neg_left,add_neg_cancel,← inner_add_left] at hh
      apply (inner_self_eq_zero (𝕜 := ℝ)).mp
      exact le_antisymm hh (inner_self_nonneg (𝕜 := ℝ))
    intro v hv w hw
    exact add_right_cancel ((hzero v hv).trans (hzero w hw).symm)

end RW
