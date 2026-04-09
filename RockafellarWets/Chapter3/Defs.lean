/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3: Cones and Cosmic Closure — Core Definitions

This file introduces the basic set-valued notion needed for Chapter 3:
- Definition 3.3: horizon cones

We realize Rockafellar-Wets horizon cones through Mathlib's
`asymptoticCone`, but adjust the empty-set convention so that the horizon cone
of `∅` is `{0}`, exactly as in the book.
-/

import Mathlib.Analysis.Normed.Affine.AsymptoticCone

open Set Bornology

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A set is a cone if it contains `0` and is closed under multiplication by
positive scalars. This is the unbundled notion used in Chapter 3. -/
def IsCone (C : Set E) : Prop :=
  (0 : E) ∈ C ∧ ∀ ⦃x : E⦄, x ∈ C → ∀ ⦃c : ℝ⦄, 0 < c → c • x ∈ C

/-- **Definition 3.3**: The horizon cone of a set, with the Rockafellar-Wets
convention that `horizonCone ∅ = {0}`. -/
def horizonCone (C : Set E) : Set E :=
  insert 0 (asymptoticCone ℝ C)

@[simp] theorem horizonCone_empty : horizonCone (∅ : Set E) = {0} := by
  simp [horizonCone]

@[simp] theorem zero_mem_horizonCone (C : Set E) : (0 : E) ∈ horizonCone C := by
  simp [horizonCone]

theorem horizonCone_eq_asymptoticCone {C : Set E} (hC : C.Nonempty) :
    horizonCone C = asymptoticCone ℝ C := by
  simp [horizonCone, zero_mem_asymptoticCone.mpr hC]

theorem horizonCone_closure (C : Set E) :
    horizonCone (closure C) = horizonCone C := by
  simp [horizonCone, asymptoticCone_closure]

theorem isClosed_horizonCone (C : Set E) :
    IsClosed (horizonCone C) := by
  by_cases hC : C.Nonempty
  · simpa [horizonCone_eq_asymptoticCone hC] using
      (isClosed_asymptoticCone (k := ℝ) (s := C))
  · have hCempty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hC
    simpa [horizonCone, hCempty] using (isClosed_singleton : IsClosed ({0} : Set E))

end RW
