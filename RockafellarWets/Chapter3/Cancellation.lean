/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3: Functional Cancellation

This file preserves the common real-valued cancellation infrastructure for
3.34, 3.36, and 3.37.

The book works with proper lower-semicontinuous convex extended-real-valued
functions.  The older Moreau envelope and infimal convolution API in this file
is real-valued, and its cancellation endpoint additionally assumes coercivity
of both left summands.  `EpiCancellation.lean` now proves exact extended-real
3.34, `ExtendedCancellationCompletion.lean` proves exact 3.36, and
`ExtendedProximalCancellationExact.lean` proves exact 3.37.  The real-valued
theorems below remain useful compatibility wrappers.

The results here also establish the two algebraic pieces used by the later
3.37 completion: adding a constant does not change the proximal mapping, and
an envelope equality up to a constant determines the functions up to that
same constant.
-/

import RockafellarWets.Chapter3.Coercivity

open Bornology EReal Set Topology

noncomputable section

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Theorem 3.34 (real-valued coercive adaptation).** Cancellation of a
coercive common summand for finite-dimensional real-valued closed convex
functions.  Compared with the book, the current real-valued endpoint also
requires coercivity of the two left summands. -/
theorem theorem334_eq_of_infConvolution_eq_real_coercive
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {f₁ f₂ g : E → ℝ}
    (hconv₁ : Convex ℝ (epigraph (fun x ↦ (f₁ x : EReal))))
    (hlsc₁ : LowerSemicontinuous (fun x ↦ (f₁ x : EReal)))
    (hconv₂ : Convex ℝ (epigraph (fun x ↦ (f₂ x : EReal))))
    (hlsc₂ : LowerSemicontinuous (fun x ↦ (f₂ x : EReal)))
    (hf₁ : IsCoercive (fun x : E ↦ (f₁ x : EReal)))
    (hf₂ : IsCoercive (fun x : E ↦ (f₂ x : EReal)))
    (hg : IsCoercive (fun x : E ↦ (g x : EReal)))
    (hEq : f₁ □ g = f₂ □ g) :
    f₁ = f₂ :=
  eq_of_infConvolution_eq_of_isCoercive_real_of_convex_lsc
    hconv₁ hlsc₁ hconv₂ hlsc₂ hEq hf₁ hf₂ hg

/-- Convexity is preserved when a real-valued function is shifted by a
constant, expressed in the project's `EReal` epigraph convention. -/
theorem convex_epigraph_add_const_real
    {f : E → ℝ} (hconv : Convex ℝ (epigraph (fun x ↦ (f x : EReal))))
    (c : ℝ) :
    Convex ℝ (epigraph (fun x ↦ ((f x + c : ℝ) : EReal))) := by
  have hconvOn : ConvexOn ℝ Set.univ f := by
    rw [← convex_epigraph_iff_convexOn f Set.univ convex_univ]
    simpa [epigraph, ge_iff_le] using hconv
  have hadd : ConvexOn ℝ Set.univ (fun x ↦ f x + c) :=
    hconvOn.add_const c
  rw [← convex_epigraph_iff_convexOn (fun x ↦ f x + c) Set.univ convex_univ]
    at hadd
  simpa only [epigraph, EReal.coe_le_coe_iff, Set.mem_univ, true_and] using hadd

omit [InnerProductSpace ℝ E] in
/-- Coercivity is invariant under addition of a real constant. -/
theorem isCoercive_add_const_real
    {f : E → ℝ} (hf : IsCoercive (fun x : E ↦ (f x : EReal)))
    (c : ℝ) :
    IsCoercive (fun x : E ↦ ((f x + c : ℝ) : EReal)) := by
  intro γ hγ
  rcases hf γ hγ with ⟨β, hβ⟩
  refine ⟨β + c, ?_⟩
  intro x
  exact EReal.coe_le_coe_iff.mpr <| by
    have hx := EReal.coe_le_coe_iff.mp (hβ x)
    linarith

omit [InnerProductSpace ℝ E] in
/-- The Moreau envelope commutes with addition of a constant when its
defining real-valued slices are bounded below. -/
theorem moreauEnvelope_add_const_of_bddBelow
    {f : E → ℝ} (c : ℝ) {lam : ℝ}
    (hbdd : ∀ x : E, BddBelow (Set.range fun w : E ↦
      f w + (1 / (2 * lam)) * ‖w - x‖ ^ 2)) :
    moreauEnvelope (fun x ↦ f x + c) lam =
      fun x ↦ moreauEnvelope f lam x + c := by
  funext x
  unfold moreauEnvelope
  rw [ciInf_add (hbdd x) c]
  congr 1
  funext w
  ring

omit [InnerProductSpace ℝ E] in
/-- A global lower bound supplies the slice bounds needed to move a constant
through the Moreau envelope. -/
theorem moreauEnvelope_add_const_of_bddBelow_range
    {f : E → ℝ} (c : ℝ) {lam : ℝ} (hlam : 0 < lam)
    (hf : BddBelow (Set.range f)) :
    moreauEnvelope (fun x ↦ f x + c) lam =
      fun x ↦ moreauEnvelope f lam x + c := by
  apply moreauEnvelope_add_const_of_bddBelow c
  obtain ⟨b, hb⟩ := hf
  intro x
  refine ⟨b, ?_⟩
  rintro _ ⟨w, rfl⟩
  have hfw : b ≤ f w := hb ⟨w, rfl⟩
  have hpen : 0 ≤ (1 / (2 * lam)) * ‖w - x‖ ^ 2 := by positivity
  linarith

omit [InnerProductSpace ℝ E] in
/-- Adding a constant does not change the proximal mapping.  This is the
easy, exact invariance direction used in Corollary 3.37. -/
theorem proximalMapping_add_const_of_bddBelow_range
    {f : E → ℝ} (c : ℝ) {lam : ℝ} (hlam : 0 < lam)
    (hf : BddBelow (Set.range f)) :
    proximalMapping (fun x ↦ f x + c) lam = proximalMapping f lam := by
  have henv := moreauEnvelope_add_const_of_bddBelow_range
    (f := f) c hlam hf
  funext x
  ext w
  simp only [proximalMapping, Set.mem_setOf_eq]
  rw [congrFun henv x]
  constructor <;> intro h <;> linarith

/-- **Corollary 3.36 (single-parameter, real-valued coercive adaptation).**
Two finite-dimensional real-valued closed convex coercive functions are
determined by equality of one positive-parameter Moreau envelope. -/
theorem corollary336_eq_of_moreauEnvelope_eq_real_coercive
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {f₁ f₂ : E → ℝ}
    (hconv₁ : Convex ℝ (epigraph (fun x ↦ (f₁ x : EReal))))
    (hlsc₁ : LowerSemicontinuous (fun x ↦ (f₁ x : EReal)))
    (hconv₂ : Convex ℝ (epigraph (fun x ↦ (f₂ x : EReal))))
    (hlsc₂ : LowerSemicontinuous (fun x ↦ (f₂ x : EReal)))
    (hf₁ : IsCoercive (fun x : E ↦ (f₁ x : EReal)))
    (hf₂ : IsCoercive (fun x : E ↦ (f₂ x : EReal)))
    {lam : ℝ} (hlam : 0 < lam)
    (hEq : moreauEnvelope f₁ lam = moreauEnvelope f₂ lam) :
    f₁ = f₂ := by
  let q : E → ℝ := fun x ↦ (1 / (2 * lam)) * ‖x‖ ^ 2
  have hEqInf : f₁ □ q = f₂ □ q := by
    funext x
    calc
      (f₁ □ q) x = moreauEnvelope f₁ lam x :=
        (moreauEnvelope_eq_infConvolution f₁ hlam x).symm
      _ = moreauEnvelope f₂ lam x := congrFun hEq x
      _ = (f₂ □ q) x := moreauEnvelope_eq_infConvolution f₂ hlam x
  apply theorem334_eq_of_infConvolution_eq_real_coercive
    hconv₁ hlsc₁ hconv₂ hlsc₂ hf₁ hf₂
      (g := q) ?_ hEqInf
  simpa only [q] using isCoercive_quadraticKernel_real (E := E) hlam

/-- **Corollary 3.37 (envelope endpoint).** If one
positive-parameter envelope of `f₁` equals the corresponding envelope of
`f₂` plus a constant, then the functions differ by that constant. -/
theorem corollary337_eq_add_const_of_moreauEnvelope_eq_add_const_real_coercive
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {f₁ f₂ : E → ℝ}
    (hconv₁ : Convex ℝ (epigraph (fun x ↦ (f₁ x : EReal))))
    (hlsc₁ : LowerSemicontinuous (fun x ↦ (f₁ x : EReal)))
    (hconv₂ : Convex ℝ (epigraph (fun x ↦ (f₂ x : EReal))))
    (_hlsc₂ : LowerSemicontinuous (fun x ↦ (f₂ x : EReal)))
    (hf₁ : IsCoercive (fun x : E ↦ (f₁ x : EReal)))
    (hf₂ : IsCoercive (fun x : E ↦ (f₂ x : EReal)))
    {lam c : ℝ} (hlam : 0 < lam)
    (hEq : moreauEnvelope f₁ lam =
      fun x ↦ moreauEnvelope f₂ lam x + c) :
    f₁ = fun x ↦ f₂ x + c := by
  have hbdd₂ : BddBelow (Set.range f₂) :=
    bddBelow_of_isCoercive_real hf₂
  have hshift :
      moreauEnvelope (fun x ↦ f₂ x + c) lam =
        fun x ↦ moreauEnvelope f₂ lam x + c :=
    moreauEnvelope_add_const_of_bddBelow_range c hlam hbdd₂
  apply corollary336_eq_of_moreauEnvelope_eq_real_coercive
    hconv₁ hlsc₁
    (convex_epigraph_add_const_real hconv₂ c)
    (lowerSemicontinuous_coe_real_of_convex_epigraph
      (convex_epigraph_add_const_real hconv₂ c))
    hf₁ (isCoercive_add_const_real hf₂ c) hlam
  exact hEq.trans hshift.symm

omit [InnerProductSpace ℝ E] in
/-- If two functions already differ by a constant, their positive-parameter
proximal mappings agree. -/
theorem proximalMapping_eq_of_eq_add_const_real
    {f₁ f₂ : E → ℝ} {c lam : ℝ} (hlam : 0 < lam)
    (hf₂ : BddBelow (Set.range f₂))
    (hEq : f₁ = fun x ↦ f₂ x + c) :
    proximalMapping f₁ lam = proximalMapping f₂ lam := by
  rw [hEq]
  exact proximalMapping_add_const_of_bddBelow_range c hlam hf₂

end RW
