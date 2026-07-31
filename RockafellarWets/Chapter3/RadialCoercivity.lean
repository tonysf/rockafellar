/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3D: Book-facing radial coercivity

The older Chapter 3 API deliberately encoded coercivity by the affine norm
minorants furnished by Theorem 3.26.  This file adds the literal definitions
from 3.25.  The extended-real radial lower limit is characterized by its real
lower slopes, avoiding division by zero and the indeterminate quotients
involving `⊥` and `⊤`.
-/

import RockafellarWets.Chapter3.CoercivityHorizonEquivalence
import RockafellarWets.Chapter3.CoercivityCompletion
import RockafellarWets.Chapter3.ParametricCoercivity

open Bornology EReal Filter Metric Set Topology

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A function is bounded below on bounded sets when each bounded set admits
a finite constant lower bound.  This is the local boundedness clause occurring
literally in Definition 3.25. -/
def IsBoundedBelowOnBoundedSets (f : E → EReal) : Prop :=
  ∀ S : Set E, Bornology.IsBounded S →
    ∃ β : ℝ, ∀ x ∈ S, (β : EReal) ≤ f x

/-- The book's `liminf_{‖x‖ → ∞} f(x) / ‖x‖`, as an `EReal`.

Its finite lower bounds are represented by `HasSequentialRadialSlopeAtLeast`.
This gives the literal extended-real value while remaining meaningful when
`f` assumes either infinity and without making a convention for `0 / 0`. -/
noncomputable def radialSlopeLiminf (f : E → EReal) : EReal :=
  ⨆ γ : ℝ, ⨆ _ : HasSequentialRadialSlopeAtLeast f γ, (γ : EReal)

/-- Definition 3.25, literal radial form of level coercivity. -/
def IsRadiallyLevelCoercive (f : E → EReal) : Prop :=
  IsBoundedBelowOnBoundedSets f ∧ 0 < radialSlopeLiminf f

/-- Definition 3.25, literal radial form of coercivity. -/
def IsRadiallyCoercive (f : E → EReal) : Prop :=
  IsBoundedBelowOnBoundedSets f ∧ radialSlopeLiminf f = ⊤

/-- Definition 3.25, literal radial form of counter-coercivity. -/
def IsRadiallyCounterCoercive (f : E → EReal) : Prop :=
  radialSlopeLiminf f = ⊥

omit [NormedSpace ℝ E] in
/-- Every certified sequential lower slope lies below the radial liminf. -/
theorem coe_le_radialSlopeLiminf_of_hasSequentialRadialSlopeAtLeast
    {f : E → EReal} {γ : ℝ}
    (hγ : HasSequentialRadialSlopeAtLeast f γ) :
    (γ : EReal) ≤ radialSlopeLiminf f := by
  exact le_iSup_of_le γ (le_iSup_of_le hγ le_rfl)

/-- Proper lsc functions in finite dimension are bounded below on every
bounded set.  This is the parenthetical appeal to 1.10 in Definition 3.25. -/
theorem isBoundedBelowOnBoundedSets_of_lowerSemicontinuous_isProper
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f) :
    IsBoundedBelowOnBoundedSets f := by
  intro S hS
  by_cases hSne : S.Nonempty
  · have hclosureNe : (closure S).Nonempty := hSne.mono subset_closure
    obtain ⟨y, hy, hymin⟩ :=
      LowerSemicontinuousOn.exists_isMinOn hclosureNe hS.isCompact_closure
        (hlsc.lowerSemicontinuousOn (closure S))
    let β : ℝ := if f y = ⊤ then 0 else (f y).toReal
    have hβ : (β : EReal) ≤ f y := by
      by_cases hytop : f y = ⊤
      · simp [β, hytop]
      · rw [show f y = ((f y).toReal : EReal) by
          exact (EReal.coe_toReal hytop (ne_of_gt (hproper.2 y))).symm]
        simp [β, hytop]
    refine ⟨β, fun x hx ↦ hβ.trans (hymin (subset_closure hx))⟩
  · refine ⟨0, ?_⟩
    intro x hx
    exact (hSne ⟨x, hx⟩).elim

/-- Formula 3(7): the literal radial lower limit equals the lower envelope of
the horizon function on the unit sphere. -/
theorem radialSlopeLiminf_eq_unitSphereHorizonInf
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f) :
    radialSlopeLiminf f = unitSphereHorizonInf f := by
  apply le_antisymm
  · unfold radialSlopeLiminf
    refine iSup_le fun γ ↦ iSup_le fun hγ ↦ ?_
    exact sequentialRadialSlope_le_unitSphereHorizonInf hlsc hproper hγ
  · by_contra hnot
    have hlt : radialSlopeLiminf f < unitSphereHorizonInf f :=
      lt_of_not_ge hnot
    obtain ⟨γ, hrad, hhor⟩ := EReal.exists_between_coe_real hlt
    have hseq : HasSequentialRadialSlopeAtLeast f γ :=
      (hasSequentialRadialSlopeAtLeast_iff_coe_le_unitSphereHorizonInf
        hlsc hproper).2 hhor.le
    exact (not_le_of_gt hrad)
      (coe_le_radialSlopeLiminf_of_hasSequentialRadialSlopeAtLeast hseq)

/-- Under the hypotheses of Theorem 3.26, a real number is a lower radial
slope exactly when it lies below the literal radial liminf. -/
theorem hasSequentialRadialSlopeAtLeast_iff_coe_le_radialSlopeLiminf
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f) {γ : ℝ} :
    HasSequentialRadialSlopeAtLeast f γ ↔
      (γ : EReal) ≤ radialSlopeLiminf f := by
  rw [radialSlopeLiminf_eq_unitSphereHorizonInf hlsc hproper]
  exact hasSequentialRadialSlopeAtLeast_iff_coe_le_unitSphereHorizonInf
    hlsc hproper

/-- Definition 3.25 and Theorem 3.26(a): the literal and affine-minorant
notions of level coercivity agree for proper lsc functions. -/
theorem isRadiallyLevelCoercive_iff_isLevelCoercive
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f) :
    IsRadiallyLevelCoercive f ↔ IsLevelCoercive f := by
  rw [IsRadiallyLevelCoercive,
    radialSlopeLiminf_eq_unitSphereHorizonInf hlsc hproper,
    ← isLevelCoercive_iff_unitSphereHorizonInf_pos hlsc hproper]
  simp [isBoundedBelowOnBoundedSets_of_lowerSemicontinuous_isProper hlsc hproper]

/-- Definition 3.25 and Theorem 3.26(b): the literal and affine-minorant
notions of coercivity agree for proper lsc functions. -/
theorem isRadiallyCoercive_iff_isCoercive
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f) :
    IsRadiallyCoercive f ↔ IsCoercive f := by
  rw [IsRadiallyCoercive,
    radialSlopeLiminf_eq_unitSphereHorizonInf hlsc hproper,
    ← isCoercive_iff_unitSphereHorizonInf_eq_top hlsc hproper]
  simp [isBoundedBelowOnBoundedSets_of_lowerSemicontinuous_isProper hlsc hproper]

/-- Definition 3.25 and Theorem 3.26(c): the literal and affine-minorant
notions of counter-coercivity agree for proper lsc functions. -/
theorem isRadiallyCounterCoercive_iff_isCounterCoercive
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f) :
    IsRadiallyCounterCoercive f ↔ IsCounterCoercive f := by
  rw [IsRadiallyCounterCoercive,
    radialSlopeLiminf_eq_unitSphereHorizonInf hlsc hproper]
  exact (isCounterCoercive_iff_unitSphereHorizonInf_eq_bot
    hlsc hproper).symm

/-! ## Exact book-facing wrappers for 3.27--3.31 -/

/-- Corollary 3.27 in literal terminology. -/
theorem IsRadiallyLevelCoercive.isLevelBounded
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsRadiallyLevelCoercive f)
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f) :
    IsLevelBounded f :=
  ((isRadiallyLevelCoercive_iff_isLevelCoercive hlsc hproper).1 hf).isLevelBounded

/-- Corollary 3.27, convex equivalence in literal terminology. -/
theorem isLevelBounded_iff_isRadiallyLevelCoercive
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hconv : Convex ℝ (epigraph f))
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f) :
    IsLevelBounded f ↔ IsRadiallyLevelCoercive f := by
  rw [isRadiallyLevelCoercive_iff_isLevelCoercive hlsc hproper]
  exact isLevelBounded_iff_isLevelCoercive hconv hlsc hproper

/-- The final assertion of Corollary 3.27 in literal terminology. -/
theorem not_isRadiallyCounterCoercive_of_convex_lsc_isProper
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {f : E → EReal} (hconv : Convex ℝ (epigraph f))
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f) :
    ¬ IsRadiallyCounterCoercive f := by
  rw [isRadiallyCounterCoercive_iff_isCounterCoercive hlsc hproper]
  exact not_isCounterCoercive_of_convex_lsc_isProper hconv hlsc hproper

/-- Example 3.28 in the literal radial terminology: a proper lsc function
which is not counter-coercive has infinite prox-threshold. -/
theorem proxThreshold_eq_top_of_not_isRadiallyCounterCoercive
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f)
    (hf : ¬ IsRadiallyCounterCoercive f) :
    proxThreshold f = ⊤ := by
  apply proxThreshold_eq_top_of_not_isCounterCoercive
  rwa [← isRadiallyCounterCoercive_iff_isCounterCoercive hlsc hproper]

/-- Exercise 3.29(a), literal terminology: adding a real-bounded-below
function preserves level coercivity.  Regularity of the sum is precisely what
is needed to pass back from the affine conclusion to Definition 3.25. -/
theorem IsRadiallyLevelCoercive.add_of_hasRealLowerBound
    [FiniteDimensional ℝ E] {f g : E → EReal}
    (hf : IsRadiallyLevelCoercive f)
    (hlscf : LowerSemicontinuous f) (hproperf : IsProper f)
    {β : ℝ} (hg : ∀ x, (β : EReal) ≤ g x)
    (hlscsum : LowerSemicontinuous (fun x ↦ f x + g x))
    (hpropersum : IsProper (fun x ↦ f x + g x)) :
    IsRadiallyLevelCoercive (fun x ↦ f x + g x) := by
  apply (isRadiallyLevelCoercive_iff_isLevelCoercive
    hlscsum hpropersum).2
  exact ((isRadiallyLevelCoercive_iff_isLevelCoercive
    hlscf hproperf).1 hf).add_of_hasRealLowerBound hg

/-- Exercise 3.29(b), literal terminology. -/
theorem IsRadiallyCoercive.add_of_not_isRadiallyCounterCoercive
    [FiniteDimensional ℝ E] {f g : E → EReal}
    (hf : IsRadiallyCoercive f)
    (hlscf : LowerSemicontinuous f) (hproperf : IsProper f)
    (hg : ¬ IsRadiallyCounterCoercive g)
    (hlscg : LowerSemicontinuous g) (hproperg : IsProper g)
    (hlscsum : LowerSemicontinuous (fun x ↦ f x + g x))
    (hpropersum : IsProper (fun x ↦ f x + g x)) :
    IsRadiallyCoercive (fun x ↦ f x + g x) := by
  apply (isRadiallyCoercive_iff_isCoercive hlscsum hpropersum).2
  exact ((isRadiallyCoercive_iff_isCoercive hlscf hproperf).1 hf).add_of_not_isCounterCoercive
    (by
      rwa [← isRadiallyCounterCoercive_iff_isCounterCoercive
        hlscg hproperg])

section ValueFunction

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Theorem 3.31, level-coercive clause in literal terminology. -/
theorem IsRadiallyLevelCoercive.valueFunction
    [FiniteDimensional ℝ (E × F)] [FiniteDimensional ℝ F]
    {f : E × F → EReal} (hf : IsRadiallyLevelCoercive f)
    (hlscf : LowerSemicontinuous f) (hproperf : IsProper f)
    (hlscp : LowerSemicontinuous (valueFunction f))
    (hproperp : IsProper (valueFunction f)) :
    IsRadiallyLevelCoercive (valueFunction f) := by
  apply (isRadiallyLevelCoercive_iff_isLevelCoercive hlscp hproperp).2
  exact ((isRadiallyLevelCoercive_iff_isLevelCoercive
    hlscf hproperf).1 hf).valueFunction

/-- Theorem 3.31, coercive clause in literal terminology. -/
theorem IsRadiallyCoercive.valueFunction
    [FiniteDimensional ℝ (E × F)] [FiniteDimensional ℝ F]
    {f : E × F → EReal} (hf : IsRadiallyCoercive f)
    (hlscf : LowerSemicontinuous f) (hproperf : IsProper f)
    (hlscp : LowerSemicontinuous (valueFunction f))
    (hproperp : IsProper (valueFunction f)) :
    IsRadiallyCoercive (valueFunction f) := by
  apply (isRadiallyCoercive_iff_isCoercive hlscp hproperp).2
  exact ((isRadiallyCoercive_iff_isCoercive hlscf hproperf).1 hf).valueFunction

end ValueFunction

/-! ## Regression examples from Definition 3.25 -/

/-- The norm is level-coercive in the literal radial sense. -/
theorem isRadiallyLevelCoercive_norm [FiniteDimensional ℝ E] :
    IsRadiallyLevelCoercive (fun x : E ↦ ((‖x‖ : ℝ) : EReal)) := by
  let f : E → EReal := fun x ↦ ((‖x‖ : ℝ) : EReal)
  have hlsc : LowerSemicontinuous f :=
    (continuous_coe_real_ereal.comp continuous_norm).lowerSemicontinuous
  have hproper : IsProper f := by
    refine ⟨⟨0, by simp [f]⟩, fun x ↦ EReal.bot_lt_coe _⟩
  apply (isRadiallyLevelCoercive_iff_isLevelCoercive hlsc hproper).2
  exact ⟨1, zero_lt_one, 0, by intro x; simp [f]⟩

/-- The squared norm is coercive in the literal radial sense. -/
theorem isRadiallyCoercive_norm_sq [FiniteDimensional ℝ E] :
    IsRadiallyCoercive (fun x : E ↦ ((‖x‖ ^ 2 : ℝ) : EReal)) := by
  let f : E → EReal := fun x ↦ ((‖x‖ ^ 2 : ℝ) : EReal)
  have hlsc : LowerSemicontinuous f := by
    exact (continuous_coe_real_ereal.comp (continuous_norm.pow 2)).lowerSemicontinuous
  have hproper : IsProper f := by
    refine ⟨⟨0, by simp [f]⟩, fun x ↦ EReal.bot_lt_coe _⟩
  apply (isRadiallyCoercive_iff_isCoercive hlsc hproper).2
  intro γ hγ
  refine ⟨-(γ ^ 2 / 4), ?_⟩
  intro x
  have hs : 0 ≤ (‖x‖ - γ / 2) ^ 2 := sq_nonneg _
  have hreal : γ * ‖x‖ - γ ^ 2 / 4 ≤ ‖x‖ ^ 2 := by nlinarith
  have hrealE :
      (((γ * ‖x‖ - γ ^ 2 / 4 : ℝ) : EReal) ≤
        ((‖x‖ ^ 2 : ℝ) : EReal)) := by
    exact_mod_cast hreal
  simpa [f, sub_eq_add_neg] using hrealE

/-- The indicator of a nonempty closed bounded set is coercive, exactly as
stated after Definition 3.25. -/
theorem isRadiallyCoercive_indicatorVA
    [FiniteDimensional ℝ E] {C : Set E}
    (hCclosed : IsClosed C) (hCne : C.Nonempty)
    (hCbounded : Bornology.IsBounded C) :
    IsRadiallyCoercive (indicatorVA C) := by
  have hlsc : LowerSemicontinuous (indicatorVA C) :=
    lowerSemicontinuous_indicatorVA hCclosed
  have hproper : IsProper (indicatorVA C) :=
    (indicatorVA_isProper_iff C).2 hCne
  apply (isRadiallyCoercive_iff_isCoercive hlsc hproper).2
  obtain ⟨R, hR⟩ := hCbounded.exists_norm_le
  intro γ hγ
  refine ⟨-γ * |R|, ?_⟩
  intro x
  by_cases hx : x ∈ C
  · rw [indicatorVA_apply_mem hx]
    have hxR : ‖x‖ ≤ |R| := (hR x hx).trans (le_abs_self R)
    have : γ * ‖x‖ - γ * |R| ≤ 0 := by
      nlinarith [mul_le_mul_of_nonneg_left hxR hγ.le]
    have thisE :
        (((γ * ‖x‖ - γ * |R| : ℝ) : EReal) ≤ (0 : EReal)) := by
      exact_mod_cast this
    simpa [sub_eq_add_neg] using thisE
  · simp [indicatorVA_apply_not_mem hx]

/-- The negative squared norm on `ℝ` is counter-coercive. -/
theorem isRadiallyCounterCoercive_neg_sq :
    IsRadiallyCounterCoercive
      (fun x : ℝ ↦ ((-(x ^ 2) : ℝ) : EReal)) := by
  let f : ℝ → EReal := fun x ↦ ((-(x ^ 2) : ℝ) : EReal)
  have hlsc : LowerSemicontinuous f := by
    exact (continuous_coe_real_ereal.comp
      ((continuous_id.pow 2).neg)).lowerSemicontinuous
  have hproper : IsProper f := by
    refine ⟨⟨0, by simp [f]⟩, fun x ↦ EReal.bot_lt_coe _⟩
  apply (isRadiallyCounterCoercive_iff_isCounterCoercive hlsc hproper).2
  intro γ
  rintro ⟨β, hminor⟩
  let A : ℝ := |γ| + |β| + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have h := hminor (2 * A)
  have hreal : γ * |2 * A| + β ≤ -(2 * A) ^ 2 := by
    have h' :
        (((γ * |2 * A| + β : ℝ) : EReal) ≤
          ((-(2 * A) ^ 2 : ℝ) : EReal)) := by
      simpa [f, Real.norm_eq_abs] using h
    exact_mod_cast h'
  have habsA : |2 * A| = 2 * A := abs_of_pos (mul_pos (by norm_num) hA)
  rw [habsA] at hreal
  have hγ : -|γ| ≤ γ := neg_abs_le γ
  have hβ : -|β| ≤ β := neg_abs_le β
  have hleft : -(2 * A * |γ|) - |β| ≤ γ * (2 * A) + β := by
    have hmul := mul_le_mul_of_nonneg_left hγ
      (show 0 ≤ 2 * A by positivity)
    nlinarith
  dsimp [A] at hA hreal hleft
  nlinarith [abs_nonneg γ, abs_nonneg β]

end RW
