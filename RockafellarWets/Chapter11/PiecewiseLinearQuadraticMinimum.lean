/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 11: minimum of a piecewise linear-quadratic function

**Corollary 11.16**: a proper, convex, piecewise linear-quadratic function with finite infimum
attains its minimum, and the set of minimizers is polyhedral
(`IsPiecewiseLinearQuadratic.argmin_nonempty_and_isPolyhedral`).

As in the book, `argmin f = ∂f*(0)` (11.8(a) with 11.3), where `f*` is piecewise
linear-quadratic by 11.14(b) and `0 ∈ dom f*`, so 10.21 applies.
-/

import RockafellarWets.Chapter11.PiecewiseLinearQuadraticConjugacy
import RockafellarWets.Chapter11.DualMinimizationEquivalences

open Set
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Corollary 11.16** (minimum of a piecewise linear-quadratic function): if a proper, convex,
piecewise linear-quadratic function has a finite infimum, then its set of minimizers is nonempty
and polyhedral. -/
theorem IsPiecewiseLinearQuadratic.argmin_nonempty_and_isPolyhedral {f : E → EReal}
    (hf : IsPiecewiseLinearQuadratic f) (hp : IsProper f) (hc : Convex ℝ (epigraph f))
    (hinf : (⨅ x, f x) ≠ ⊥) : (argmin f).Nonempty ∧ IsPolyhedral (argmin f) := by
  have hl := hf.lowerSemicontinuous
  have h0 : (0 : E) ∈ effectiveDomain (fenchelConjugate f) := by
    change fenchelConjugate f 0 < ⊤
    rw [lt_top_iff_ne_top]
    intro htop
    have he := iInf_eq_neg_fenchelConjugate_zero f
    rw [htop, EReal.neg_top] at he
    exact hinf he
  obtain ⟨hne, hpoly, -⟩ :=
    (hf.isPiecewiseLinearQuadratic_fenchelConjugate hp hl hc).convex_subgradient_properties
      (convex_epigraph_fenchelConjugate f) h0
  rw [argmin_eq_subdifferential_fenchelConjugate_zero hp hl hc]
  exact ⟨hne, hpoly⟩

/-- **Corollary 11.16**, attainment form: a proper, convex, piecewise linear-quadratic function
that is bounded below attains its infimum. -/
theorem IsPiecewiseLinearQuadratic.exists_isMinOn_of_bddBelow {f : E → EReal}
    (hf : IsPiecewiseLinearQuadratic f) (hp : IsProper f) (hc : Convex ℝ (epigraph f))
    {r : ℝ} (hr : ∀ x, (r : EReal) ≤ f x) : ∃ x, ∀ y, f x ≤ f y := by
  have hinf : (⨅ x, f x) ≠ ⊥ := by
    intro h
    have : (r : EReal) ≤ ⨅ x, f x := le_iInf hr
    rw [h] at this
    exact EReal.coe_ne_bot r (le_bot_iff.mp this)
  obtain ⟨x, hx⟩ := (hf.argmin_nonempty_and_isPolyhedral hp hc hinf).1
  exact ⟨x, fun y ↦ hx.1 ▸ iInf_le f y⟩

end RW
