/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Finite shifts of extended-real functions

This file records the generic laws for adding a finite real constant to an
`EReal`-valued function.  Such a shift preserves properness, lower
semicontinuity, and convexity of the epigraph.  It also commutes with the
extended-real Moreau envelope, by the finite-translation order isomorphism
from `ERealInfimum.lean`.
-/

import RockafellarWets.Chapter3.ERealInfimum
import RockafellarWets.Chapter3.ExtendedCancellationCompletion
import RockafellarWets.Chapter3.ExtendedProximalCancellationCompletion

open EReal Set Topology

noncomputable section

namespace RW

variable {E : Type*}

/-- Adding a finite real constant preserves properness of an extended-real
function. -/
theorem isProper_add_const_ereal {f : E → EReal}
    (hproper : IsProper f) (c : ℝ) :
    IsProper (fun x ↦ f x + (c : EReal)) := by
  constructor
  · rcases hproper.1 with ⟨x, hx⟩
    refine ⟨x, EReal.add_lt_top (ne_of_lt hx) (EReal.coe_ne_top c)⟩
  · intro x
    simpa using EReal.add_lt_add_right_coe (hproper.2 x) c

section Topological

variable [TopologicalSpace E]

/-- Adding a finite real constant preserves lower semicontinuity of an
extended-real function. -/
theorem lowerSemicontinuous_add_const_ereal {f : E → EReal}
    (hlsc : LowerSemicontinuous f) (c : ℝ) :
    LowerSemicontinuous (fun x ↦ f x + (c : EReal)) := by
  have hc : LowerSemicontinuous (fun _ : E ↦ (c : EReal)) :=
    continuous_const.lowerSemicontinuous
  refine LowerSemicontinuous.add' hlsc hc (fun x ↦ ?_)
  exact EReal.continuousAt_add
    (Or.inr (EReal.coe_ne_bot c))
    (Or.inr (EReal.coe_ne_top c))

end Topological

section Convex

variable [AddCommGroup E] [Module ℝ E]

omit [Module ℝ E] in
/-- The epigraph of a finite constant shift is the corresponding vertical
translation of the original epigraph. -/
private theorem epigraph_add_const_ereal_eq_translate
    (f : E → EReal) (c : ℝ) :
    epigraph (fun x ↦ f x + (c : EReal)) =
      (fun p : E × ℝ ↦ ((0 : E), c) + p) '' epigraph f := by
  ext z
  constructor
  · rcases z with ⟨x, t⟩
    intro hz
    refine ⟨(x, t - c), ?_, ?_⟩
    · rw [mem_epigraph_iff] at hz ⊢
      have hle : f x ≤ (t : EReal) - (c : EReal) :=
        (EReal.le_sub_iff_add_le
          (a := f x) (b := (c : EReal)) (c := (t : EReal))
          (Or.inl (EReal.coe_ne_bot c))
          (Or.inl (EReal.coe_ne_top c))).2 hz
      simpa only [← EReal.coe_sub] using hle
    · ext <;> simp
  · rintro ⟨⟨x, t⟩, ht, rfl⟩
    rw [mem_epigraph_iff] at ht ⊢
    have hle := add_le_add_right ht (c : EReal)
    simpa [EReal.coe_add, add_comm] using hle

/-- Adding a finite real constant preserves convexity of the epigraph. -/
theorem convex_epigraph_add_const_ereal {f : E → EReal}
    (hconv : Convex ℝ (epigraph f)) (c : ℝ) :
    Convex ℝ (epigraph (fun x ↦ f x + (c : EReal))) := by
  rw [epigraph_add_const_ereal_eq_translate]
  exact hconv.translate ((0 : E), c)

end Convex

section Moreau

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
/-- The extended-real Moreau envelope commutes with addition of a finite real
constant.  This holds for every parameter, without positivity assumptions. -/
theorem moreauEnvelopeEReal_add_const
    (f : E → EReal) (c lam : ℝ) :
    moreauEnvelopeEReal (fun x ↦ f x + (c : EReal)) lam =
      fun x ↦ moreauEnvelopeEReal f lam x + (c : EReal) := by
  funext x
  unfold moreauEnvelopeEReal
  calc
    (⨅ w : E, (f w + (c : EReal)) +
        (((1 / (2 * lam)) * ‖w - x‖ ^ 2 : ℝ) : EReal)) =
        ⨅ w : E, (f w +
          (((1 / (2 * lam)) * ‖w - x‖ ^ 2 : ℝ) : EReal)) + (c : EReal) := by
      congr 1
      funext w
      calc
        (f w + (c : EReal)) +
            (((1 / (2 * lam)) * ‖w - x‖ ^ 2 : ℝ) : EReal) =
            f w + ((c : EReal) +
              (((1 / (2 * lam)) * ‖w - x‖ ^ 2 : ℝ) : EReal)) :=
          add_assoc _ _ _
        _ = f w + ((((1 / (2 * lam)) * ‖w - x‖ ^ 2 : ℝ) : EReal) +
              (c : EReal)) := by rw [add_comm (c : EReal)]
        _ = (f w +
              (((1 / (2 * lam)) * ‖w - x‖ ^ 2 : ℝ) : EReal)) + (c : EReal) :=
          (add_assoc _ _ _).symm
    _ = (⨅ w : E, f w +
          (((1 / (2 * lam)) * ‖w - x‖ ^ 2 : ℝ) : EReal)) + (c : EReal) :=
      (iInf_add_coe
        (fun w : E ↦ f w +
          (((1 / (2 * lam)) * ‖w - x‖ ^ 2 : ℝ) : EReal)) c).symm

omit [InnerProductSpace ℝ E] in
/-- A finite shift of the function shifts every extended-real proximal
objective by the same finite constant. -/
theorem proximalObjectiveEReal_add_const
    (f : E → EReal) (c lam : ℝ) (x w : E) :
    proximalObjectiveEReal (fun z ↦ f z + (c : EReal)) lam x w =
      proximalObjectiveEReal f lam x w + (c : EReal) := by
  unfold proximalObjectiveEReal
  calc
    (f w + (c : EReal)) +
        (((1 / (2 * lam)) * ‖w - x‖ ^ 2 : ℝ) : EReal) =
        f w + ((c : EReal) +
          (((1 / (2 * lam)) * ‖w - x‖ ^ 2 : ℝ) : EReal)) :=
      add_assoc _ _ _
    _ = f w + ((((1 / (2 * lam)) * ‖w - x‖ ^ 2 : ℝ) : EReal) +
          (c : EReal)) := by rw [add_comm (c : EReal)]
    _ = (f w +
          (((1 / (2 * lam)) * ‖w - x‖ ^ 2 : ℝ) : EReal)) + (c : EReal) :=
      (add_assoc _ _ _).symm

omit [InnerProductSpace ℝ E] in
/-- Adding a finite real constant does not change the extended-real proximal
mapping.  No positivity, properness, or semicontinuity hypothesis is needed. -/
theorem proximalMappingEReal_add_const
    (f : E → EReal) (c lam : ℝ) :
    proximalMappingEReal (fun x ↦ f x + (c : EReal)) lam =
      proximalMappingEReal f lam := by
  funext x
  ext w
  constructor
  · intro hw
    rcases (mem_proximalMappingEReal_iff.mp hw) with ⟨heq, hfin⟩
    have hobj := proximalObjectiveEReal_add_const f c lam x w
    have henv := congrFun (moreauEnvelopeEReal_add_const f c lam) x
    refine mem_proximalMappingEReal_iff.mpr ⟨?_, ?_⟩
    · apply (erealAddRightOrderIso c).injective
      simpa only [erealAddRightOrderIso_apply, ← hobj, ← henv] using heq
    · rw [henv] at hfin
      exact lt_top_iff_ne_top.2 fun htop ↦ by simp [htop] at hfin
  · intro hw
    rcases (mem_proximalMappingEReal_iff.mp hw) with ⟨heq, hfin⟩
    have hobj := proximalObjectiveEReal_add_const f c lam x w
    have henv := congrFun (moreauEnvelopeEReal_add_const f c lam) x
    refine mem_proximalMappingEReal_iff.mpr ⟨?_, ?_⟩
    · rw [hobj, henv]
      simpa only [erealAddRightOrderIso_apply] using
        congrArg (erealAddRightOrderIso c) heq
    · rw [henv]
      exact EReal.add_lt_top (ne_of_lt hfin) (EReal.coe_ne_top _)

end Moreau

end RW
