/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Lagrange multipliers for interval constraints

Corollary 6.15 combines the constrained-normal theorem with the four-case
normal formula for a box. The scalar sign predicates include singleton
intervals, rays, bounded intervals, and the whole line.
-/

import RockafellarWets.Chapter6.ConstraintNormals
import RockafellarWets.Chapter6.FiniteBoxes

open Set
open scoped BigOperators InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]

/-- The adjoint of a vector-valued derivative is the sum of its coordinate
gradients weighted by the multiplier coordinates. -/
theorem adjoint_eq_sum_smul_of_coordinate_gradients
    {f : E → EuclideanSpace ℝ ι} {A : E →L[ℝ] EuclideanSpace ℝ ι} {x : E}
    (hf : HasFDerivAt f A x) {g : ι → E}
    (hg : ∀ i, HasGradientAt (fun z ↦ f z i) (g i) x) (y : EuclideanSpace ℝ ι) :
    A.adjoint y = ∑ i, y i • g i := by
  apply ext_inner_right ℝ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_left, PiLp.inner_apply, sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  have hi := ((PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : ι ↦ ℝ) i).hasFDerivAt.comp x hf)
  have heq := hi.unique (hg i).hasFDerivAt
  have hval : (A w) i = ⟪g i, w⟫_ℝ := congrArg (fun B : E →L[ℝ] ℝ ↦ B w) heq
  simp [hval, real_inner_smul_right, real_inner_comm, mul_comm]

/-- **Corollary 6.15**, Lagrange multipliers with the printed interval sign
restrictions. The finite index type may be empty. -/
theorem exists_lagrange_multipliers_of_interval_constraints
    {X : Set E} (hX : IsClosed X) {D : ι → Set ℝ}
    (hD : ∀ i, IsNonemptyClosedInterval (D i))
    {f : E → EuclideanSpace ℝ ι} (hf : ContDiff ℝ 1 f)
    {f₀ : E → ℝ} {x g₀ : E} {g : ι → E}
    (hx : x ∈ X ∩ f ⁻¹' finiteBox D)
    (hmin : IsLocalMinOn f₀ (X ∩ f ⁻¹' finiteBox D) x)
    (hg₀ : HasGradientAt f₀ g₀ x)
    (hg : ∀ i, HasGradientAt (fun z ↦ f z i) (g i) x)
    (hCQ : ∀ y : EuclideanSpace ℝ ι,
      (∀ i, y i ∈ intervalNormalDirections (D i) (f x i)) →
      -(∑ i, y i • g i) ∈ normalCone X x → y = 0) :
    ∃ y : EuclideanSpace ℝ ι,
      (∀ i, y i ∈ intervalNormalDirections (D i) (f x i)) ∧
      -(g₀ + ∑ i, y i • g i) ∈ normalCone X x := by
  have hderiv : HasFDerivAt f (fderiv ℝ f x) x := (hf.differentiable (by norm_num) x).hasFDerivAt
  have hsum := adjoint_eq_sum_smul_of_coordinate_gradients hderiv hg
  have hbox : normalCone (finiteBox D) (f x) =
      {y | ∀ i, y i ∈ intervalNormalDirections (D i) (f x i)} :=
    normalCone_finiteBox_of_closedIntervals hD hx.2
  have hqual : NormalConstraintQualification X (finiteBox D) (fderiv ℝ f x) x (f x) := by
    intro y hy hz
    rw [hsum y] at hz
    exact hCQ y (by simpa only [hbox, mem_setOf_eq] using hy) hz
  obtain ⟨y, hy, z, hz, heq⟩ := exists_normal_multipliers_of_mem_normalCone hX
    (finiteBox_isClosed fun i ↦ (hD i).isClosed) hf hqual
    (IsLocalMinOn.neg_gradient_mem_normalCone hx hmin hg₀)
  refine ⟨y, by simpa only [hbox, mem_setOf_eq] using hy, ?_⟩
  rw [hsum y] at heq
  have hzval : -(g₀ + ∑ i, y i • g i) = z := by
    rw [neg_add, heq]
    abel
  rwa [hzval]

end RW
