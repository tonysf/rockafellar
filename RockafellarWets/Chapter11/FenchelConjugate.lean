/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Legendre–Fenchel conjugate
-/

import RockafellarWets.Chapter8.SupportFunctions

open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Legendre–Fenchel conjugate, as in formula 11(1). -/
noncomputable def fenchelConjugate (f : E → EReal) (v : E) : EReal :=
  ⨆ x : E, (⟪v, x⟫_ℝ : EReal) - f x

theorem le_fenchelConjugate (f : E → EReal) (x v : E) :
    (⟪v, x⟫_ℝ : EReal) - f x ≤ fenchelConjugate f v :=
  le_iSup (fun z : E ↦ (⟪v, z⟫_ℝ : EReal) - f z) x

theorem fenchelConjugate_le_iff (f : E → EReal) (v : E) (a : EReal) :
    fenchelConjugate f v ≤ a ↔ ∀ x, (⟪v, x⟫_ℝ : EReal) - f x ≤ a :=
  iSup_le_iff

theorem fenchelConjugate_antitone : Antitone (fenchelConjugate (E := E)) :=
  fun _ _ h _ ↦ iSup_mono fun x ↦ EReal.sub_le_sub le_rfl (h x)

end RW
