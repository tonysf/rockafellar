/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: Operations that preserve monotonicity

Exercise 12.4: inverses, positive multiples, sums, and the composition
`x ↦ A* S(Ax + a)` with a linear map preserve monotonicity, and the stated
operations preserve strict monotonicity.

Sums and multiples use the pointwise set operations of Chapter 5:
`(T₁ + T₂)(x) = T₁(x) + T₂(x)` is `svAdd T₁ T₂` and `(λT)(x) = λ T(x)`.
The matrix `A ∈ ℝ^{m×n}` of 12.4(d) is a continuous linear map `A : E →L[ℝ] F`
with adjoint `A†`; it has rank `n` exactly when it is injective.
-/

import RockafellarWets.Chapter12.MonotoneMappings
import RockafellarWets.Chapter5.MappingOperations
import Mathlib.Analysis.InnerProductSpace.Adjoint

open Set
open scoped InnerProductSpace Pointwise

namespace RW

section Operations

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Exercise 12.4(a).** The inverse of a monotone mapping is monotone. -/
theorem SvMonotone.inv {T : E → Set E} (hT : SvMonotone T) : SvMonotone (svInv T) := by
  intro v₀ x₀ h₀ v₁ x₁ h₁
  rw [real_inner_comm]
  exact hT h₀ h₁

/-- Monotonicity of a mapping and of its inverse are equivalent. -/
theorem svMonotone_svInv_iff {T : E → Set E} : SvMonotone (svInv T) ↔ SvMonotone T :=
  ⟨fun h ↦ by simpa only [svInv_svInv] using h.inv, SvMonotone.inv⟩

theorem mem_smul_mapping {T : E → Set E} {lam : ℝ} {x v : E} :
    v ∈ lam • T x ↔ ∃ w ∈ T x, lam • w = v :=
  mem_smul_set

/-- **Exercise 12.4(b).** A nonnegative multiple of a monotone mapping is
monotone; the book states the case `λ > 0`. -/
theorem SvMonotone.smul {T : E → Set E} (hT : SvMonotone T) {lam : ℝ} (hlam : 0 ≤ lam) :
    SvMonotone (fun x ↦ lam • T x) := by
  intro x₀ v₀ h₀ x₁ v₁ h₁
  obtain ⟨w₀, hw₀, rfl⟩ := mem_smul_set.1 h₀
  obtain ⟨w₁, hw₁, rfl⟩ := mem_smul_set.1 h₁
  rw [← smul_sub, real_inner_smul_left]
  exact mul_nonneg hlam (hT hw₀ hw₁)

/-- **Exercise 12.4(b)**, strict monotonicity. -/
theorem SvStrictlyMonotone.smul {T : E → Set E} (hT : SvStrictlyMonotone T) {lam : ℝ}
    (hlam : 0 < lam) : SvStrictlyMonotone (fun x ↦ lam • T x) := by
  intro x₀ v₀ h₀ x₁ v₁ h₁ hx
  obtain ⟨w₀, hw₀, rfl⟩ := mem_smul_set.1 h₀
  obtain ⟨w₁, hw₁, rfl⟩ := mem_smul_set.1 h₁
  rw [← smul_sub, real_inner_smul_left]
  exact mul_pos hlam (hT hw₀ hw₁ hx)

private theorem inner_add_sub_add (a₀ b₀ a₁ b₁ d : E) :
    ⟪(a₁ + b₁) - (a₀ + b₀), d⟫_ℝ = ⟪a₁ - a₀, d⟫_ℝ + ⟪b₁ - b₀, d⟫_ℝ := by
  rw [add_sub_add_comm, inner_add_left]

/-- **Exercise 12.4(c).** The sum of two monotone mappings is monotone. -/
theorem SvMonotone.add {T₁ T₂ : E → Set E} (h₁ : SvMonotone T₁) (h₂ : SvMonotone T₂) :
    SvMonotone (svAdd T₁ T₂) := by
  intro x₀ v₀ hv₀ x₁ v₁ hv₁
  obtain ⟨a₀, ha₀, b₀, hb₀, rfl⟩ := mem_svAdd.1 hv₀
  obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := mem_svAdd.1 hv₁
  rw [inner_add_sub_add]
  exact add_nonneg (h₁ ha₀ ha₁) (h₂ hb₀ hb₁)

/-- **Exercise 12.4(c)**, strict monotonicity: adding a monotone mapping to a
strictly monotone one gives a strictly monotone mapping. -/
theorem SvStrictlyMonotone.add_left {T₁ T₂ : E → Set E} (h₁ : SvStrictlyMonotone T₁)
    (h₂ : SvMonotone T₂) : SvStrictlyMonotone (svAdd T₁ T₂) := by
  intro x₀ v₀ hv₀ x₁ v₁ hv₁ hx
  obtain ⟨a₀, ha₀, b₀, hb₀, rfl⟩ := mem_svAdd.1 hv₀
  obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := mem_svAdd.1 hv₁
  rw [inner_add_sub_add]
  exact add_pos_of_pos_of_nonneg (h₁ ha₀ ha₁ hx) (h₂ hb₀ hb₁)

/-- **Exercise 12.4(c)**, strict monotonicity of the second summand. -/
theorem SvStrictlyMonotone.add_right {T₁ T₂ : E → Set E} (h₁ : SvMonotone T₁)
    (h₂ : SvStrictlyMonotone T₂) : SvStrictlyMonotone (svAdd T₁ T₂) := by
  intro x₀ v₀ hv₀ x₁ v₁ hv₁ hx
  obtain ⟨a₀, ha₀, b₀, hb₀, rfl⟩ := mem_svAdd.1 hv₀
  obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := mem_svAdd.1 hv₁
  rw [inner_add_sub_add]
  exact add_pos_of_nonneg_of_pos (h₁ ha₀ ha₁) (h₂ hb₀ hb₁ hx)

/-- **Exercise 12.4(c)**, strict monotonicity when either summand is strictly
monotone. -/
theorem svStrictlyMonotone_svAdd {T₁ T₂ : E → Set E} (h₁ : SvMonotone T₁) (h₂ : SvMonotone T₂)
    (hstrict : SvStrictlyMonotone T₁ ∨ SvStrictlyMonotone T₂) :
    SvStrictlyMonotone (svAdd T₁ T₂) :=
  hstrict.elim (fun h ↦ h.add_left h₂) (fun h ↦ SvStrictlyMonotone.add_right h₁ h)

variable [CompleteSpace E] [CompleteSpace F]

/-- The mapping `x ↦ A* S(Ax + a)` of Exercise 12.4(d). -/
def svAdjointComp (A : E →L[ℝ] F) (S : F → Set F) (a : F) : E → Set E :=
  fun x ↦ A.adjoint '' S (A x + a)

@[simp]
theorem mem_svAdjointComp {A : E →L[ℝ] F} {S : F → Set F} {a : F} {x v : E} :
    v ∈ svAdjointComp A S a x ↔ ∃ w ∈ S (A x + a), A.adjoint w = v :=
  Iff.rfl

private theorem inner_adjoint_sub (A : E →L[ℝ] F) (a : F) (w₀ w₁ : F) (x₀ x₁ : E) :
    ⟪A.adjoint w₁ - A.adjoint w₀, x₁ - x₀⟫_ℝ = ⟪w₁ - w₀, (A x₁ + a) - (A x₀ + a)⟫_ℝ := by
  rw [← map_sub, ContinuousLinearMap.adjoint_inner_left, add_sub_add_right_eq_sub, map_sub]

/-- **Exercise 12.4(d).** For a monotone `S`, every linear map `A` and every
vector `a`, the mapping `x ↦ A* S(Ax + a)` is monotone; no positive
semidefiniteness of `A` is needed. -/
theorem SvMonotone.adjointComp {S : F → Set F} (hS : SvMonotone S) (A : E →L[ℝ] F) (a : F) :
    SvMonotone (svAdjointComp A S a) := by
  intro x₀ v₀ hv₀ x₁ v₁ hv₁
  obtain ⟨w₀, hw₀, rfl⟩ := hv₀
  obtain ⟨w₁, hw₁, rfl⟩ := hv₁
  rw [inner_adjoint_sub A a]
  exact hS hw₀ hw₁

/-- **Exercise 12.4(d)**, strict monotonicity: if `S` is strictly monotone and
`A` has full column rank, that is, is injective, then `x ↦ A* S(Ax + a)` is
strictly monotone. -/
theorem SvStrictlyMonotone.adjointComp {S : F → Set F} (hS : SvStrictlyMonotone S)
    {A : E →L[ℝ] F} (hA : Function.Injective A) (a : F) :
    SvStrictlyMonotone (svAdjointComp A S a) := by
  intro x₀ v₀ hv₀ x₁ v₁ hv₁ hx
  obtain ⟨w₀, hw₀, rfl⟩ := hv₀
  obtain ⟨w₁, hw₁, rfl⟩ := hv₁
  rw [inner_adjoint_sub A a]
  refine hS hw₀ hw₁ fun h ↦ hx (hA ?_)
  simpa using h

end Operations

end RW
