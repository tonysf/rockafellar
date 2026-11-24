/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Second-order epi-differentiability of conjugate functions

Corollary 13.22.  For `f = φ*` with `φ` lsc, proper and convex, `∂f(x) = argmax_v {⟪v, x⟫ - φ(v)}`;
if `v̄ ∈ ∂f(x̄)` and `φ` is fully amenable at `v̄`, then `φ` is properly twice epi-differentiable at
`v̄` for `x̄` (13.15), so by the duality of Theorem 13.21 `f` is properly twice
epi-differentiable at `x̄` for `v̄` with `d²f(x̄ | v̄)(w) = sup_z {2⟪w, z⟫ - d²φ(v̄ | x̄)(z)}`.
-/

import RockafellarWets.Chapter13.SecondOrderChainRuleAmenable
import RockafellarWets.Chapter13.SecondOrderDuality
import RockafellarWets.Chapter11.ConjugateSubgradientGraph

open Filter Set Topology Metric
open scoped InnerProductSpace

namespace RW

/-- Multiplication by a positive real commutes with suprema in `EReal`. -/
theorem ereal_coe_mul_iSup {ι : Sort*} (a : ι → EReal) {c : ℝ} (hc : 0 < c) :
    (c : EReal) * (⨆ i, a i) = ⨆ i, (c : EReal) * a i := by
  apply le_antisymm
  · have hinv : (⨆ i, a i) ≤ ((c⁻¹ : ℝ) : EReal) * (⨆ i, (c : EReal) * a i) := by
      refine iSup_le fun i ↦ ?_
      calc a i = ((c⁻¹ : ℝ) : EReal) * ((c : EReal) * a i) := by
            rw [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ hc.ne', EReal.coe_one, one_mul]
        _ ≤ ((c⁻¹ : ℝ) : EReal) * (⨆ j, (c : EReal) * a j) := by
            gcongr
            exact le_iSup (fun j ↦ (c : EReal) * a j) i
    calc (c : EReal) * (⨆ i, a i)
        ≤ (c : EReal) * (((c⁻¹ : ℝ) : EReal) * (⨆ i, (c : EReal) * a i)) := by gcongr
      _ = ⨆ i, (c : EReal) * a i := by
          rw [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ hc.ne', EReal.coe_one, one_mul]
  · refine iSup_le fun i ↦ ?_
    gcongr
    exact le_iSup a i

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Corollary 13.22** (conjugates of fully amenable functions).  Let `f = φ*` for `φ` lsc,
proper and convex.  Then `∂f(x) = argmax_v {⟪v, x⟫ - φ(v)}`, and if `v̄ ∈ ∂f(x̄)` with `φ` fully
amenable at `v̄`, then `f` is properly twice epi-differentiable at `x̄` for `v̄` with
`d²f(x̄ | v̄)(w) = sup_z {2⟪w, z⟫ - d²φ(v̄ | x̄)(z)}`. -/
theorem conjugates_of_fully_amenable_functions {φ : E → EReal} (hp : IsProper φ)
    (hl : LowerSemicontinuous φ) (hc : Convex ℝ (epigraph φ)) :
    (∀ x, subdifferential (fenchelConjugate φ) x =
      argmax (fun v ↦ (⟪v, x⟫_ℝ : EReal) - φ v)) ∧
    ∀ x v, v ∈ subdifferential (fenchelConjugate φ) x → FullyAmenableAt φ v →
      ProperlyTwiceEpiDifferentiableAt (fenchelConjugate φ) x v ∧
      ∀ w, secondSubderivative (fenchelConjugate φ) x v w =
        ⨆ z, (((2 * ⟪w, z⟫_ℝ : ℝ) : EReal) - secondSubderivative φ v x z) := by
  refine ⟨fun x ↦ ?_, fun x v hv hfa ↦ ?_⟩
  · rw [subdifferential_fenchelConjugate_eq_argmax hp hl hc x]
    congr 1
    funext v
    rw [real_inner_comm]
  · have hxv : x ∈ subdifferential φ v :=
      (mem_subdifferential_fenchelConjugate_iff hp hl hc v x).1 hv
    have hφ := hfa.properlyTwiceEpiDifferentiableAt hxv
    obtain ⟨h1, h2⟩ := hφ.fenchelConjugate hp hl hc hxv
    refine ⟨h1, fun w ↦ ?_⟩
    have h3 := congrFun h2 w
    simp only [fenchelConjugate] at h3
    calc secondSubderivative (fenchelConjugate φ) x v w
        = ((2 : ℝ) : EReal) * (((1 / 2 : ℝ) : EReal) *
            secondSubderivative (fenchelConjugate φ) x v w) := by
          rw [← mul_assoc, ← EReal.coe_mul]; norm_num
      _ = ((2 : ℝ) : EReal) * ⨆ z, ((⟪w, z⟫_ℝ : ℝ) : EReal) -
            ((1 / 2 : ℝ) : EReal) * secondSubderivative φ v x z := by rw [← h3]
      _ = ⨆ z, ((2 : ℝ) : EReal) * (((⟪w, z⟫_ℝ : ℝ) : EReal) -
            ((1 / 2 : ℝ) : EReal) * secondSubderivative φ v x z) :=
          ereal_coe_mul_iSup _ (by norm_num)
      _ = ⨆ z, (((2 * ⟪w, z⟫_ℝ : ℝ) : EReal) - secondSubderivative φ v x z) := by
          congr 1
          funext z
          rcases ereal_trichotomy (secondSubderivative φ v x z) with h | h | ⟨r, h⟩
          · rw [h, EReal.coe_mul_bot_of_pos (by norm_num), EReal.coe_sub_bot,
              EReal.coe_sub_bot, EReal.coe_mul_top_of_pos (by norm_num)]
          · rw [h, EReal.coe_mul_top_of_pos (by norm_num), EReal.sub_top,
              EReal.sub_top, EReal.coe_mul_bot_of_pos (by norm_num)]
          · rw [h, ← EReal.coe_mul, ← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_sub]
            congr 1
            ring

end RW
