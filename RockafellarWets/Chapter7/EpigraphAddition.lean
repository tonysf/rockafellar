/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Inf-addition on the extended real line
-/

import RockafellarWets.Chapter1.Defs

namespace RW

/-- Inf-addition is the convention used by Rockafellar and Wets for
minimization. A summand equal to positive infinity excludes the point from
the effective domain, including when the other summand is negative infinity. -/
noncomputable def infAddition (a b : EReal) : EReal :=
  if a = ⊤ ∨ b = ⊤ then ⊤ else a + b

@[simp] theorem infAddition_zero (a : EReal) : infAddition a 0 = a := by
  cases a <;> simp [infAddition]

theorem add_le_infAddition (a b : EReal) : a + b ≤ infAddition a b := by
  unfold infAddition
  split <;> simp

theorem infAddition_eq_add_of_ne_bot {a b : EReal} (ha : a ≠ ⊥) (hb : b ≠ ⊥) :
    infAddition a b = a + b := by
  cases a <;> cases b <;> simp_all [infAddition]

/-- The epigraph of inf-addition is obtained by allocating a finite height
to each summand, even when one of the summands equals minus infinity. -/
theorem infAddition_le_coe_iff (u v : EReal) (a : ℝ) :
    infAddition u v ≤ (a : EReal) ↔
      ∃ r s : ℝ, u ≤ (r : EReal) ∧ v ≤ (s : EReal) ∧ r + s = a := by
  constructor
  · intro h
    cases u with
    | bot =>
      cases v with
      | bot => exact ⟨a, 0, bot_le, bot_le, add_zero _⟩
      | coe z => exact ⟨a - z, z, bot_le, le_rfl, sub_add_cancel _ _⟩
      | top => simp [infAddition] at h
    | coe y =>
      cases v with
      | bot => exact ⟨y, a - y, le_rfl, bot_le, by ring⟩
      | coe z =>
        have hyz : y + z ≤ a := by simpa [infAddition, ← EReal.coe_add] using h
        exact ⟨y, a - y, le_rfl, EReal.coe_le_coe_iff.mpr (by linarith), by ring⟩
      | top => simp [infAddition] at h
    | top => simp [infAddition] at h
  · rintro ⟨r, s, hu, hv, rfl⟩
    rw [infAddition, if_neg (not_or.mpr
      ⟨(hu.trans_lt (EReal.coe_lt_top _)).ne, (hv.trans_lt (EReal.coe_lt_top _)).ne⟩),
      EReal.coe_add]
    exact add_le_add hu hv

end RW
