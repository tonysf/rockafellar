/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Nonsingularity in the classical implicit mapping criteria
-/

import RockafellarWets.Chapter9.ClassicalImplicitMappings
import RockafellarWets.Chapter9.SingleValuedStrictDifferentiability

open Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]

/-- The two partial derivatives assembled on the Euclidean product. -/
def implicitEuclideanDerivative (A : E →L[ℝ] E) (B : P →L[ℝ] E) : WithLp 2 (E × P) →L[ℝ] E :=
  (A.coprod B).comp (WithLp.prodContinuousLinearEquiv 2 ℝ E P).toContinuousLinearMap

@[simp] theorem implicitEuclideanDerivative_apply (A : E →L[ℝ] E) (B : P →L[ℝ] E)
    (z : WithLp 2 (E × P)) : implicitEuclideanDerivative A B z = A z.fst + B z.snd := rfl

theorem implicitEuclideanDerivative_adjoint (A : E →L[ℝ] E) (B : P →L[ℝ] E) (y : E) :
    (implicitEuclideanDerivative A B).adjoint y = WithLp.toLp 2 (A.adjoint y,B.adjoint y) := by
  apply ext_inner_right ℝ
  intro z
  rw [ContinuousLinearMap.adjoint_inner_left,WithLp.prod_inner_apply,
    implicitEuclideanDerivative_apply,inner_add_right]
  change _ = ⟪A.adjoint y,z.fst⟫_ℝ + ⟪B.adjoint y,z.snd⟫_ℝ
  rw [ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.adjoint_inner_left]

omit [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P] in
theorem adjoint_kernel_zero_iff_bijective (A : E →L[ℝ] E) :
    (∀ y, A.adjoint y = 0 → y = 0) ↔ Function.Bijective A := by
  constructor
  · intro hk
    have hi : Function.Injective A.adjoint := by
      intro y z he
      exact sub_eq_zero.mp (hk (y-z) (by rw [map_sub,he,sub_self]))
    have hs := LinearMap.surjective_of_injective (f := A.adjoint.toLinearMap) hi
    have hAker (w : E) (hw : A w = 0) : w = 0 := by
      obtain ⟨y,hy⟩ := hs w
      change A.adjoint y = w at hy
      apply real_inner_self_nonpos.mp
      apply le_of_eq
      rw [← hy,ContinuousLinearMap.adjoint_inner_left]
      rw [hy,hw,inner_zero_right]
    have hAi : Function.Injective A := by
      intro u v he
      exact sub_eq_zero.mp (hAker (u-v) (by rw [map_sub,he,sub_self]))
    exact ⟨hAi,LinearMap.surjective_of_injective (f := A.toLinearMap) hAi⟩
  · rintro ⟨_,hs⟩ y hy
    obtain ⟨w,hw⟩ := hs y
    apply real_inner_self_nonpos.mp
    apply le_of_eq
    calc ⟪y,y⟫_ℝ = ⟪y,A w⟫_ℝ := by rw [hw]
      _ = ⟪A.adjoint y,w⟫_ℝ := (ContinuousLinearMap.adjoint_inner_left A w y).symm
      _ = 0 := by rw [hy,inner_zero_left]

/-- **Theorem 9.56(d)**: for a square strict derivative `[A B]`,
the coderivative condition in part (a) is precisely nonsingularity of `A`. -/
theorem implicit_coderivative_condition_iff_bijective
    {f : WithLp 2 (E × P) → E} {x : E} {p : P} {A : E →L[ℝ] E} {B : P →L[ℝ] E}
    (hf : HasStrictFDerivAt f (implicitEuclideanDerivative A B) (WithLp.toLp 2 (x,p)))
    (hzero : f (WithLp.toLp 2 (x,p)) = 0) :
    (∀ (y : E) (r : P), WithLp.toLp 2 (0,r) ∈
      coderivative (svSingleton f) (WithLp.toLp 2 (x,p)) 0 y → y = 0 ∧ r = 0) ↔
      Function.Bijective A := by
  have he := coderivative_singleton_of_hasStrictFDerivAt hf
  rw [hzero] at he
  rw [he,← adjoint_kernel_zero_iff_bijective]
  constructor
  · intro h y hy
    apply (h y (B.adjoint y) ?_).1
    change WithLp.toLp 2 (0,B.adjoint y) = (implicitEuclideanDerivative A B).adjoint y
    rw [implicitEuclideanDerivative_adjoint,hy]
  · intro hk y r hm
    change WithLp.toLp 2 (0,r) = (implicitEuclideanDerivative A B).adjoint y at hm
    rw [implicitEuclideanDerivative_adjoint] at hm
    have hfirst : (0 : E) = A.adjoint y := congrArg WithLp.fst hm
    have hy := hk y hfirst.symm
    refine ⟨hy,?_⟩
    have hr : r = B.adjoint y := congrArg WithLp.snd hm
    simpa only [hy,map_zero] using hr

/-- **Theorem 9.56(d)**: for a square strict derivative `[A B]`,
the strict graphical derivative condition in part (b) is also precisely
nonsingularity of `A`. -/
theorem implicit_strictDerivative_condition_iff_bijective
    {f : WithLp 2 (E × P) → E} {x : E} {p : P} {A : E →L[ℝ] E} {B : P →L[ℝ] E}
    (hf : HasStrictFDerivAt f (implicitEuclideanDerivative A B) (WithLp.toLp 2 (x,p)))
    (hzero : f (WithLp.toLp 2 (x,p)) = 0) :
    (∀ w : E, (0 : E) ∈ strictGraphicalDerivative (svSingleton f)
      (WithLp.toLp 2 (x,p)) 0 (WithLp.toLp 2 (w,0)) → w = 0) ↔ Function.Bijective A := by
  have he := strictGraphicalDerivative_singleton_of_hasStrictFDerivAt hf
  change strictGraphicalDerivative (svSingleton f) (WithLp.toLp 2 (x,p))
    (f (WithLp.toLp 2 (x,p))) = fun w ↦ {implicitEuclideanDerivative A B w} at he
  rw [hzero] at he
  rw [he]
  simp only [mem_singleton_iff,implicitEuclideanDerivative_apply,WithLp.toLp_fst,
    WithLp.toLp_snd,map_zero,add_zero]
  constructor
  · intro hk
    have hi : Function.Injective A := by
      intro u v he
      apply sub_eq_zero.mp
      apply hk
      rw [map_sub,he,sub_self]
    exact ⟨hi,LinearMap.surjective_of_injective (f := A.toLinearMap) hi⟩
  · intro h w hw
    exact h.1 (hw.symm.trans (map_zero A).symm)

end RW
