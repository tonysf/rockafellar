/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Inverse Hessians in the classical Legendre transform
-/

import RockafellarWets.Chapter11.ClassicalLegendreGradient

open Filter Set Topology InnerProductSpace
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A positive definite quadratic form makes its linear operator invertible. -/
theorem exists_continuousLinearEquiv_of_inner_pos (A : E →L[ℝ] E)
    (hA : ∀ w, w ≠ 0 → 0 < ⟪A w,w⟫_ℝ) :
    ∃ e : E ≃L[ℝ] E, e.toContinuousLinearMap=A := by
  have hinj : Function.Injective A := by
    intro x y hxy
    have hz : A (x-y)=0 := by rw [map_sub,hxy,sub_self]
    by_contra hn
    have hp := hA (x-y) (sub_ne_zero.mpr hn)
    rw [hz,inner_zero_left] at hp
    exact lt_irrefl _ hp
  let e := (LinearEquiv.ofBijective A.toLinearMap
    ⟨hinj,LinearMap.injective_iff_surjective.mp hinj⟩).toContinuousLinearEquiv
  exact ⟨e,by ext w; rfl⟩

/-- A global left inverse inherits local `C¹` smoothness and the inverse
derivative from the inverse function theorem. -/
theorem leftInverse_contDiffAt_hasStrictFDerivAt {G H : E → E} {x : E}
    (hG : ContDiffAt ℝ 1 G x) {A : E ≃L[ℝ] E}
    (hd : HasFDerivAt G A.toContinuousLinearMap x) (hleft : Function.LeftInverse H G) :
    ContDiffAt ℝ 1 H (G x) ∧ HasStrictFDerivAt H A.symm.toContinuousLinearMap (G x) := by
  have hstrict := hG.hasStrictFDerivAt' hd (by norm_num : (1:WithTop ℕ∞) ≠ 0)
  have he := hstrict.localInverse_unique (Eventually.of_forall hleft)
  refine ⟨?_,hstrict.to_local_left_inverse (Eventually.of_forall hleft)⟩
  exact (hG.to_localInverse hd (by norm_num : (1:WithTop ℕ∞) ≠ 0)).congr_of_eventuallyEq he

/-- **11.9**, second-order smoothness, inverse gradient and Hessian, and
positive definiteness of the conjugate Hessian. -/
theorem classicalLegendre_conjugate_second_order {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : Convex ℝ (epigraph (fun x ↦ (f x:EReal))))
    (hco : IsCoercive (fun x ↦ (f x:EReal)))
    (hpos : ∀ x w, w ≠ 0 → 0 < ⟪fderiv ℝ (gradient f) x w,w⟫_ℝ) :
    let g := fun v ↦ (fenchelConjugate (fun x ↦ (f x:EReal)) v).toReal
    ContDiff ℝ 2 g ∧
      (∀ x, gradient g (gradient f x)=x) ∧ (∀ v, gradient f (gradient g v)=v) ∧
      (∀ x, (fderiv ℝ (gradient g) (gradient f x)).comp (fderiv ℝ (gradient f) x) =
        ContinuousLinearMap.id ℝ E ∧
        (fderiv ℝ (gradient f) x).comp (fderiv ℝ (gradient g) (gradient f x)) =
          ContinuousLinearMap.id ℝ E) ∧
      ∀ v w, w ≠ 0 → 0 < ⟪fderiv ℝ (gradient g) v w,w⟫_ℝ := by
  dsimp only
  let g := fun v ↦ (fenchelConjugate (fun x ↦ (f x:EReal)) v).toReal
  have hdf := hf.differentiable (by norm_num : (2:WithTop ℕ∞) ≠ 0)
  have hG := contDiff_one_gradient hf
  have hbij := classicalLegendre_gradient_bijective hf hc hco hpos
  have hgrad (x : E) : HasGradientAt g x (gradient f x) :=
    conjugate_hasGradientAt_of_gradient_injective hdf hc hbij.1 x
  have hleft : Function.LeftInverse (gradient g) (gradient f) := fun x ↦ (hgrad x).gradient
  have hright : Function.RightInverse (gradient g) (gradient f) := by
    intro v
    obtain ⟨x,rfl⟩ := hbij.2 v
    rw [hleft x]
  have hess (x : E) : ∃ A : E ≃L[ℝ] E,
      A.toContinuousLinearMap=fderiv ℝ (gradient f) x ∧
      ContDiffAt ℝ 1 (gradient g) (gradient f x) ∧
      HasStrictFDerivAt (gradient g) A.symm.toContinuousLinearMap (gradient f x) := by
    obtain ⟨A,hA⟩ := exists_continuousLinearEquiv_of_inner_pos _ (hpos x)
    have hd : HasFDerivAt (gradient f) A.toContinuousLinearMap x := by
      rw [hA]
      exact ((hG.differentiable (by norm_num)) x).hasFDerivAt
    exact ⟨A,hA,leftInverse_contDiffAt_hasStrictFDerivAt hG.contDiffAt hd hleft⟩
  have hgdiff : Differentiable ℝ g := by
    intro v
    obtain ⟨x,rfl⟩ := hbij.2 v
    exact (hgrad x).differentiableAt
  have hgradC : ContDiff ℝ 1 (gradient g) := by
    rw [contDiff_iff_contDiffAt]
    intro v
    obtain ⟨x,rfl⟩ := hbij.2 v
    obtain ⟨_,_,hg,_⟩ := hess x
    exact hg
  have hgc : ContDiff ℝ 2 g := by
    change ContDiff ℝ ((1:WithTop ℕ∞)+1) g
    apply contDiff_succ_iff_fderiv.mpr
    refine ⟨hgdiff,by norm_num,?_⟩
    have he : fderiv ℝ g = fun v ↦ (toDual ℝ E) (gradient g v) := by
      funext v
      simp only [gradient,LinearIsometryEquiv.apply_symm_apply]
    rw [he]
    exact (toDual ℝ E).toContinuousLinearEquiv.contDiff.comp hgradC
  refine ⟨hgc,hleft,hright,?_,?_⟩
  · intro x
    obtain ⟨A,hA,_,hAi⟩ := hess x
    rw [hAi.hasFDerivAt.fderiv,← hA]
    constructor <;> ext w <;> simp
  · intro v w hw
    obtain ⟨x,rfl⟩ := hbij.2 v
    obtain ⟨A,hA,_,hAi⟩ := hess x
    rw [hAi.hasFDerivAt.fderiv]
    have hn : A.symm w ≠ 0 := by intro hz; exact hw (A.symm.injective (by simpa using hz))
    have hp := hpos x (A.symm w) hn
    rw [← hA] at hp
    simpa only [ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply,
      real_inner_comm w (A.symm w)] using hp

end RW
