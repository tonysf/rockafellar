/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Classical Legendre conjugate pairs

The complete finite-dimensional statement of Example 11.9. Hessians are
represented by the continuous linear derivatives of the gradient mappings.
-/

import RockafellarWets.Chapter11.ClassicalLegendreHessian

open Set
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **11.9**, the finite coercive `C²` convex conjugate pair, both Legendre
value formulas, and inverse positive definite Hessians. -/
theorem exists_classicalLegendreTransform {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : Convex ℝ (epigraph (fun x ↦ (f x:EReal))))
    (hco : IsCoercive (fun x ↦ (f x:EReal)))
    (hpos : ∀ x w, w ≠ 0 → 0 < ⟪fderiv ℝ (gradient f) x w,w⟫_ℝ) :
    ∃ g : E → ℝ,
      (∀ v, (g v:EReal) = fenchelConjugate (fun x ↦ (f x:EReal)) v) ∧
      ContDiff ℝ 2 g ∧ IsCoercive (fun v ↦ (g v:EReal)) ∧
      Convex ℝ (epigraph (fun v ↦ (g v:EReal))) ∧
      fenchelConjugate (fun v ↦ (g v:EReal)) = (fun x ↦ (f x:EReal)) ∧
      Function.Bijective (gradient f) ∧ Function.Bijective (gradient g) ∧
      (∀ x, gradient g (gradient f x)=x) ∧ (∀ v, gradient f (gradient g v)=v) ∧
      (∀ v, g v=⟪gradient g v,v⟫_ℝ-f (gradient g v)) ∧
      (∀ x, f x=⟪gradient f x,x⟫_ℝ-g (gradient f x)) ∧
      (∀ x, (fderiv ℝ (gradient g) (gradient f x)).comp (fderiv ℝ (gradient f) x) =
        ContinuousLinearMap.id ℝ E ∧
        (fderiv ℝ (gradient f) x).comp (fderiv ℝ (gradient g) (gradient f x)) =
          ContinuousLinearMap.id ℝ E) ∧
      ∀ v w, w ≠ 0 → 0 < ⟪fderiv ℝ (gradient g) v w,w⟫_ℝ := by
  let g := fun v ↦ (fenchelConjugate (fun x ↦ (f x:EReal)) v).toReal
  have hge : (fun v ↦ (g v:EReal)) = fenchelConjugate (fun x ↦ (f x:EReal)) :=
    funext fun v ↦ (classicalLegendre_conjugate_finite hco v).symm
  have hp := isProper_coe_real f
  have hl : LowerSemicontinuous (fun x ↦ (f x:EReal)) :=
    (continuous_coe_real_ereal.comp hf.continuous).lowerSemicontinuous
  have hpg := isProper_fenchelConjugate hp hl hc
  have hlg := lowerSemicontinuous_fenchelConjugate (fun x ↦ (f x:EReal))
  have hcg := convex_epigraph_fenchelConjugate (fun x ↦ (f x:EReal))
  have hb := fenchelConjugate_fenchelConjugate_eq hp hl hc
  have hgco : IsCoercive (fun v ↦ (g v:EReal)) := by
    rw [hge]
    apply (isCoercive_iff_conjugate_domain_eq_univ hpg hlg hcg).mpr
    rw [hb]
    exact eq_univ_of_forall fun x ↦ EReal.coe_lt_top _
  obtain ⟨hg,hleft,hright,hess,hposg⟩ := classicalLegendre_conjugate_second_order hf hc hco hpos
  change ContDiff ℝ 2 g at hg
  change Function.LeftInverse (gradient g) (gradient f) at hleft
  change Function.RightInverse (gradient g) (gradient f) at hright
  have hval (v : E) : g v=⟪gradient g v,v⟫_ℝ-f (gradient g v) := by
    have hh := classicalLegendre_value_at_gradient (hf.differentiable (by norm_num)) hc (gradient g v)
    rw [hright v,← hge] at hh
    simpa only [real_inner_comm] using EReal.coe_injective hh
  refine ⟨g,fun v ↦ congrFun hge v,hg,hgco,?_,?_,
    classicalLegendre_gradient_bijective hf hc hco hpos,
    ⟨hright.injective,hleft.surjective⟩,hleft,hright,hval,?_,hess,hposg⟩
  · rw [hge]; exact hcg
  · rw [hge]; exact hb
  · intro x
    have hh := hval (gradient f x)
    rw [hleft x] at hh
    have he : ⟪x,gradient f x⟫_ℝ=⟪gradient f x,x⟫_ℝ := real_inner_comm _ _
    linarith

end RW
