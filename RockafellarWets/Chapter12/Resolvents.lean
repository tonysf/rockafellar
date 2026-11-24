/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: Resolvents and Yosida regularizations

The resolvent `(I + λT)⁻¹` of Theorem 12.12 and the Yosida
`λ`-regularization `(λI + T⁻¹)⁻¹` of Example 12.13 are defined literally, as
inverses of the pointwise sums `I + λT` and `λI + T⁻¹` of Chapter 5.
Their membership lemmas read `x ∈ (I + λT)⁻¹(z) ↔ ∃ v ∈ T(x), x + λv = z` and
`v ∈ (λI + T⁻¹)⁻¹(z) ↔ ∃ x, v ∈ T(x) ∧ λv + x = z`.

This file proves Lemma 12.14, the inverse-resolvent identity
`I - (I + T)⁻¹ = (I + T⁻¹)⁻¹` and its scaled form
`(λI + T⁻¹)⁻¹ = λ⁻¹[I - (I + λT)⁻¹]`, for every mapping `T`.  It also proves the
formula `(λI + T⁻¹)⁻¹ = (I + λ⁻¹T⁻¹)⁻¹ ∘ λ⁻¹I` of Example 12.13 and the first
assertion of Theorem 12.12: the resolvents of a monotone mapping are monotone
and nonexpansive.
-/

import RockafellarWets.Chapter12.MonotoneOperations
import RockafellarWets.Chapter12.NonexpansiveMappings

open Set
open scoped InnerProductSpace Pointwise

namespace RW

section Resolvents

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The resolvent `(I + λT)⁻¹` of Theorem 12.12. -/
def svResolvent (T : E → Set E) (lam : ℝ) : E → Set E :=
  svInv (svAdd (fun x ↦ ({x} : Set E)) (fun x ↦ lam • T x))

@[simp]
theorem mem_svResolvent {T : E → Set E} {lam : ℝ} {z x : E} :
    x ∈ svResolvent T lam z ↔ ∃ v ∈ T x, x + lam • v = z := by
  simp only [svResolvent, mem_svInv, mem_svAdd, mem_singleton_iff, mem_smul_set]
  constructor
  · rintro ⟨a, rfl, b, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨x, rfl, lam • v, ⟨v, hv, rfl⟩, rfl⟩

/-- The domain of the resolvent is the range of `I + λT`. -/
theorem svDom_svResolvent (T : E → Set E) (lam : ℝ) :
    svDom (svResolvent T lam) = svRange (svAdd (fun x ↦ ({x} : Set E)) (fun x ↦ lam • T x)) :=
  svDom_svInv _

/-- The Yosida `λ`-regularization `(λI + T⁻¹)⁻¹` of Example 12.13. -/
def svYosida (T : E → Set E) (lam : ℝ) : E → Set E :=
  svInv (svAdd (fun v ↦ ({lam • v} : Set E)) (svInv T))

@[simp]
theorem mem_svYosida {T : E → Set E} {lam : ℝ} {z v : E} :
    v ∈ svYosida T lam z ↔ ∃ x, v ∈ T x ∧ lam • v + x = z := by
  simp only [svYosida, mem_svInv, mem_svAdd, mem_singleton_iff]
  constructor
  · rintro ⟨a, rfl, x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨lam • v, rfl, x, hx, rfl⟩

/-- The resolvent with parameter `λ` is the unit resolvent of `λT`. -/
theorem svResolvent_eq_svResolvent_smul (T : E → Set E) (lam : ℝ) :
    svResolvent T lam = svResolvent (fun x ↦ lam • T x) 1 := by
  funext z
  ext x
  simp only [mem_svResolvent, one_smul, mem_smul_set]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨lam • v, ⟨v, hv, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨v, hv, rfl⟩

/-- **Lemma 12.14 (inverse-resolvent identity).** Every mapping satisfies
`I - (I + T)⁻¹ = (I + T⁻¹)⁻¹`. -/
theorem sub_svResolvent_eq_svResolvent_svInv (T : E → Set E) :
    (fun w ↦ ({w} : Set E) - svResolvent T 1 w) = svResolvent (svInv T) 1 := by
  funext w
  ext z
  simp only [mem_sub, mem_singleton_iff, mem_svResolvent, one_smul, mem_svInv]
  constructor
  · rintro ⟨a, rfl, x, ⟨v, hv, hxv⟩, rfl⟩
    refine ⟨x, ?_, by abel⟩
    have e : a - x = v := by rw [← hxv]; abel
    rw [e]
    exact hv
  · rintro ⟨y, hy, hzy⟩
    exact ⟨w, rfl, y, ⟨z, hy, by rw [← hzy]; abel⟩, by rw [← hzy]; abel⟩

/-- **Lemma 12.14**, scaled form: the Yosida regularization is
`(λI + T⁻¹)⁻¹ = λ⁻¹[I - (I + λT)⁻¹]` for every `λ ≠ 0`, in particular for every
`λ > 0`. -/
theorem svYosida_eq_smul_sub_svResolvent (T : E → Set E) {lam : ℝ} (hlam : lam ≠ 0) :
    svYosida T lam = fun w ↦ lam⁻¹ • (({w} : Set E) - svResolvent T lam w) := by
  funext w
  ext z
  simp only [mem_svYosida, mem_smul_set, mem_sub, mem_singleton_iff, mem_svResolvent]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨lam • z, ⟨lam • z + x, rfl, x, ⟨z, hx, by abel⟩, by abel⟩, ?_⟩
    rw [smul_smul, inv_mul_cancel₀ hlam, one_smul]
  · rintro ⟨_, ⟨_, rfl, x, ⟨v, hv, rfl⟩, rfl⟩, rfl⟩
    refine ⟨x, ?_, ?_⟩
    · rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hlam, one_smul]
      exact hv
    · rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hlam, one_smul, add_comm]

/-- **Lemma 12.14**, the unscaled identity read through Yosida regularization:
`(I + T⁻¹)⁻¹` is the Yosida regularization with `λ = 1`. -/
theorem svYosida_one (T : E → Set E) : svYosida T 1 = svResolvent (svInv T) 1 := by
  funext z
  ext v
  simp only [mem_svYosida, mem_svResolvent, one_smul, mem_svInv]

/-- **Example 12.13**, the formula `(λI + T⁻¹)⁻¹ = (I + λ⁻¹T⁻¹)⁻¹ ∘ λ⁻¹I`. -/
theorem svYosida_eq_svComp (T : E → Set E) {lam : ℝ} (hlam : lam ≠ 0) :
    svYosida T lam = svComp (svResolvent (svInv T) lam⁻¹) (fun z ↦ ({lam⁻¹ • z} : Set E)) := by
  funext z
  ext v
  simp only [mem_svYosida, mem_svComp, mem_singleton_iff, exists_eq_left, mem_svResolvent,
    mem_svInv]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x, hx, ?_⟩
    rw [smul_add, smul_smul, inv_mul_cancel₀ hlam, one_smul]
  · rintro ⟨x, hx, hv⟩
    refine ⟨x, hx, ?_⟩
    have := congrArg (lam • ·) hv
    simp only [smul_add, smul_smul, mul_inv_cancel₀ hlam, one_smul] at this
    exact this

/-- The resolvent identity behind Theorem 12.12: if `xᵢ ∈ (I + λT)⁻¹(zᵢ)` with
`zᵢ = xᵢ + λvᵢ`, then the monotonicity inner product of the resolvent splits. -/
private theorem resolvent_inner_identity (lam : ℝ) (x₀ x₁ v₀ v₁ : E) :
    ⟪x₁ - x₀, (x₁ + lam • v₁) - (x₀ + lam • v₀)⟫_ℝ =
      ‖x₁ - x₀‖ ^ 2 + lam * ⟪v₁ - v₀, x₁ - x₀⟫_ℝ := by
  have e : (x₁ + lam • v₁) - (x₀ + lam • v₀) = (x₁ - x₀) + lam • (v₁ - v₀) := by
    rw [smul_sub]; abel
  rw [e, inner_add_right, real_inner_self_eq_norm_sq, real_inner_smul_right, real_inner_comm]

/-- **Theorem 12.12**, first assertion: for monotone `T` and `λ ≥ 0` the
resolvent `(I + λT)⁻¹` is monotone. -/
theorem SvMonotone.svMonotone_svResolvent {T : E → Set E} (hT : SvMonotone T) {lam : ℝ}
    (hlam : 0 ≤ lam) : SvMonotone (svResolvent T lam) := by
  intro z₀ x₀ h₀ z₁ x₁ h₁
  obtain ⟨v₀, hv₀, rfl⟩ := mem_svResolvent.1 h₀
  obtain ⟨v₁, hv₁, rfl⟩ := mem_svResolvent.1 h₁
  rw [resolvent_inner_identity]
  exact add_nonneg (sq_nonneg _) (mul_nonneg hlam (hT hv₀ hv₁))

/-- **Theorem 12.12**, first assertion: for monotone `T` and `λ ≥ 0` the
resolvent `(I + λT)⁻¹` is nonexpansive. -/
theorem SvMonotone.svNonexpansive_svResolvent {T : E → Set E} (hT : SvMonotone T) {lam : ℝ}
    (hlam : 0 ≤ lam) : SvNonexpansive (svResolvent T lam) := by
  intro z₀ x₀ h₀ z₁ x₁ h₁
  obtain ⟨v₀, hv₀, rfl⟩ := mem_svResolvent.1 h₀
  obtain ⟨v₁, hv₁, rfl⟩ := mem_svResolvent.1 h₁
  have hid := resolvent_inner_identity lam x₀ x₁ v₀ v₁
  have hnn : 0 ≤ lam * ⟪v₁ - v₀, x₁ - x₀⟫_ℝ := mul_nonneg hlam (hT hv₀ hv₁)
  have hcs := real_inner_le_norm (x₁ - x₀) ((x₁ + lam • v₁) - (x₀ + lam • v₀))
  have hsq : ‖x₁ - x₀‖ ^ 2 ≤ ‖x₁ - x₀‖ * ‖(x₁ + lam • v₁) - (x₀ + lam • v₀)‖ := by
    nlinarith
  rcases (norm_nonneg (x₁ - x₀)).eq_or_lt with h | h
  · rw [← h]
    exact norm_nonneg _
  · nlinarith

/-- A monotone mapping has single-valued resolvents on their domains. -/
theorem SvMonotone.svResolvent_eq_singleton {T : E → Set E} (hT : SvMonotone T) {lam : ℝ}
    (hlam : 0 ≤ lam) {z x : E} (hx : x ∈ svResolvent T lam z) : svResolvent T lam z = {x} :=
  (hT.svNonexpansive_svResolvent hlam).eq_singleton hx

end Resolvents

end RW
