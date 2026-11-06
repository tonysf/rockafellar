/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 1: Extended-real Moreau and proximal definitions

The definitions of 1.22 need only a normed additive group.  They live here
so that cancellation and set-valued continuity results use the same
extended-real objective, envelope, and proximal mapping.  As for `argmin`,
an identically-`+∞` objective has no minimizers.
-/

import RockafellarWets.Chapter1.Defs

open Set

noncomputable section

namespace RW

variable {E : Type*} [NormedAddCommGroup E]

/-- The extended-real objective minimized in the Moreau envelope. -/
def proximalObjectiveEReal (f : E → EReal) (lam : ℝ) (x w : E) : EReal :=
  f w + (((1 / (2 * lam)) * ‖w - x‖ ^ 2 : ℝ) : EReal)

/-- The Moreau envelope with its natural extended-real codomain. -/
def moreauEnvelopeEReal (f : E → EReal) (lam : ℝ) (x : E) : EReal :=
  ⨅ w : E, f w + (((1 / (2 * lam)) * ‖w - x‖ ^ 2 : ℝ) : EReal)

/-- The envelope is the infimum of the canonical proximal objective. -/
theorem moreauEnvelopeEReal_eq_iInf_proximalObjectiveEReal
    (f : E → EReal) (lam : ℝ) (x : E) :
    moreauEnvelopeEReal f lam x = ⨅ w : E, proximalObjectiveEReal f lam x w := rfl

/-- Prox-boundedness asks for a positive-parameter envelope that is above
`-∞` at some point. -/
theorem isProxBounded_iff_exists_moreauEnvelopeEReal (f : E → EReal) :
    IsProxBounded f ↔ ∃ lam : ℝ, 0 < lam ∧ ∃ x : E,
      ⊥ < moreauEnvelopeEReal f lam x := Iff.rfl

/-- The proximal mapping of an extended-real-valued function. -/
def proximalMappingEReal (f : E → EReal) (lam : ℝ) (x : E) : Set E :=
  argmin (proximalObjectiveEReal f lam x)

@[simp]
theorem mem_proximalMappingEReal_iff
    {f : E → EReal} {lam : ℝ} {x w : E} :
    w ∈ proximalMappingEReal f lam x ↔
      proximalObjectiveEReal f lam x w = moreauEnvelopeEReal f lam x ∧
        moreauEnvelopeEReal f lam x < ⊤ :=
  Iff.rfl

end RW
