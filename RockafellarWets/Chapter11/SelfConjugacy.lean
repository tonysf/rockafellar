/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Self-conjugacy of the squared norm
-/

import RockafellarWets.Chapter11.FenchelConjugate

open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The conjugate of half the squared norm is half the squared norm. -/
theorem fenchelConjugate_half_norm_sq :
    fenchelConjugate (fun x : E ↦ ((‖x‖ ^ 2 / 2 : ℝ) : EReal)) =
      fun v ↦ ((‖v‖ ^ 2 / 2 : ℝ) : EReal) := by
  funext v
  apply le_antisymm
  · apply (fenchelConjugate_le_iff _ _ _).mpr
    intro x
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
    nlinarith [norm_sub_sq_real v x, sq_nonneg ‖v - x‖]
  · have h := le_fenchelConjugate (fun x : E ↦ ((‖x‖ ^ 2 / 2 : ℝ) : EReal)) v v
    rw [real_inner_self_eq_norm_sq, ← EReal.coe_sub,
      show ‖v‖ ^ 2 - ‖v‖ ^ 2 / 2 = ‖v‖ ^ 2 / 2 by ring] at h
    exact h

/-- **Example 11.11**. Among all extended-real functions, the unique
fixed point of the Legendre–Fenchel transform is half the squared norm. -/
theorem fenchelConjugate_eq_self_iff (f : E → EReal) :
    fenchelConjugate f = f ↔ f = fun v ↦ ((‖v‖ ^ 2 / 2 : ℝ) : EReal) := by
  constructor
  · intro h
    have hminor : (fun x : E ↦ ((‖x‖ ^ 2 / 2 : ℝ) : EReal)) ≤ f := by
      intro x
      have hh := le_fenchelConjugate f x x
      rw [h, real_inner_self_eq_norm_sq] at hh
      generalize f x = a at *
      induction a using EReal.rec with
      | bot => rw [EReal.coe_sub_bot] at hh; exact (not_le_of_gt bot_lt_top hh).elim
      | top => exact le_top
      | coe r =>
        rw [← EReal.coe_sub, EReal.coe_le_coe_iff] at hh
        exact EReal.coe_le_coe_iff.mpr (by linarith)
    apply le_antisymm _ hminor
    simpa only [h, fenchelConjugate_half_norm_sq] using fenchelConjugate_antitone hminor
  · rintro rfl
    exact fenchelConjugate_half_norm_sq

end RW
