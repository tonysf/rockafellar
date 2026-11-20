/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: The regular subderivative test for lower calmness
-/

import RockafellarWets.Chapter8.CalmSubgradients
import RockafellarWets.Chapter8.RegularSubderivativeSupport

open Set

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {x : E}

/-- **Proposition 8.32.** Local lower semicontinuity gives equivalent tests
for a nonempty subdifferential using the regular subderivative. The second
test includes zero among the directions. -/
theorem IsLocallyLscAt.subdifferential_nonempty_iff_regularSubderivative (hl : IsLocallyLscAt f x) :
    ((subdifferential f x).Nonempty ↔ regularSubderivative f x 0 = 0) ∧
      ((subdifferential f x).Nonempty ↔ ∀ w, ⊥ < regularSubderivative f x w) := by
  have hx := (EReal.coe_toReal hl.2.1 hl.1).symm
  have he := (regularSubderivative_zero_eq_zero_iff hx hl).symm
  have hh := positivelyHomogeneous_regularSubderivative hx
  refine ⟨he,he.trans ⟨hh.bot_lt_of_zero_eq_zero (lowerSemicontinuous_regularSubderivative _ _),?_⟩⟩
  exact fun h ↦ hh.zero_eq_zero_or_bot.resolve_right (h 0).ne'

end RW
