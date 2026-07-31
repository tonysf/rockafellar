/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3D: Radial growth and horizon slopes

This file formalizes formula 3(7) of Theorem 3.26 in a sequential,
extended-real-safe form.  Instead of dividing a possibly infinite value of
`f` by `‖x‖`, the statement says that every real slope strictly below the
radial lower limit eventually gives a homogeneous lower bound along every
sequence escaping to infinity.
-/

import RockafellarWets.Chapter3.HorizonAddition
import Mathlib.Topology.Semicontinuity.Basic

open Set EReal Filter Topology Metric
open scoped BigOperators

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The sequential assertion that the radial lower growth of `f` is at least
`γ`.  This is the subtraction- and division-free meaning of
`liminf_{‖x‖→∞} f(x) / ‖x‖ ≥ γ` for an `EReal`-valued function. -/
def HasSequentialRadialSlopeAtLeast (f : E → EReal) (γ : ℝ) : Prop :=
  ∀ x : ℕ → E, Tendsto (fun n ↦ ‖x n‖) atTop atTop →
    ∀ a : ℝ, a < γ →
      ∀ᶠ n in atTop, (((a * ‖x n‖ : ℝ) : EReal) ≤ f (x n))

/-- The lower envelope of the horizon function on the unit sphere. -/
noncomputable def unitSphereHorizonInf (f : E → EReal) : EReal :=
  ⨅ w : Metric.sphere (0 : E) 1, horizonFunction f w

omit [NormedSpace ℝ E] in
/-- Affine minorants of every slope below `γ` imply the sequential radial
lower bound `γ`.  This direction requires no regularity of `f`. -/
theorem hasSequentialRadialSlopeAtLeast_of_forall_lt_affineNormLowerBound
    {f : E → EReal} {γ : ℝ}
    (hminor : ∀ a : ℝ, a < γ →
      ∃ β : ℝ, HasAffineNormLowerBound f a β) :
    HasSequentialRadialSlopeAtLeast f γ := by
  intro x hx a ha
  obtain ⟨c, hac, hcγ⟩ := exists_between ha
  obtain ⟨β, hβ⟩ := hminor c hcγ
  have hca : 0 < c - a := sub_pos.mpr hac
  filter_upwards [hx.eventually (eventually_ge_atTop
    (-β / (c - a)))] with n hn
  have hreal : a * ‖x n‖ ≤ c * ‖x n‖ + β := by
    have hmul : -β ≤ (c - a) * ‖x n‖ := by
      simpa [mul_comm] using (div_le_iff₀ hca).mp hn
    linarith
  have hrealE :
      ((a * ‖x n‖ : ℝ) : EReal) ≤ ((c * ‖x n‖ + β : ℝ) : EReal) := by
    exact_mod_cast hreal
  exact hrealE.trans (hβ (x n))

/-- In finite dimension, proper lower-semicontinuous functions satisfy the
converse: the sequential radial lower bound is equivalent to affine norm
minorants at every strictly smaller slope.  The strict inequality is the
standard exact encoding of a liminf lower bound. -/
theorem hasSequentialRadialSlopeAtLeast_iff_forall_lt_affineNormLowerBound
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f) {γ : ℝ} :
    HasSequentialRadialSlopeAtLeast f γ ↔
      ∀ a : ℝ, a < γ → ∃ β : ℝ, HasAffineNormLowerBound f a β := by
  constructor
  · intro hseq a ha
    obtain ⟨c, hac, hcγ⟩ := exists_between ha
    have hexterior :
        ∃ R₀ : ℝ, ∀ x : E, R₀ ≤ ‖x‖ →
          (((c * ‖x‖ : ℝ) : EReal) ≤ f x) := by
      by_contra hnot
      push_neg at hnot
      choose x hxnorm hxfail using fun n : ℕ ↦ hnot (n : ℝ)
      have hxescape : Tendsto (fun n ↦ ‖x n‖) atTop atTop :=
        tendsto_atTop_mono' atTop
          (Eventually.of_forall hxnorm) tendsto_natCast_atTop_atTop
      have hevent := hseq x hxescape c hcγ
      obtain ⟨n, hn⟩ := hevent.exists
      exact (not_le_of_gt (hxfail n)) hn
    obtain ⟨R₀, hR₀⟩ := hexterior
    let R : ℝ := max R₀ 0
    have hRnonneg : 0 ≤ R := le_max_right _ _
    have hRext : ∀ x : E, R ≤ ‖x‖ →
        (((c * ‖x‖ : ℝ) : EReal) ≤ f x) := by
      intro x hx
      exact hR₀ x ((le_max_left R₀ 0).trans hx)
    let K : Set E := Metric.closedBall 0 R
    have hKne : K.Nonempty := by
      refine ⟨0, ?_⟩
      simp [K, hRnonneg]
    obtain ⟨y, hyK, hymin⟩ :=
      LowerSemicontinuousOn.exists_isMinOn hKne
        (isCompact_closedBall (0 : E) R)
        (hlsc.lowerSemicontinuousOn K)
    let b : ℝ := if f y = ⊤ then 0 else (f y).toReal
    have hb : (b : EReal) ≤ f y := by
      by_cases hytop : f y = ⊤
      · simp [b, hytop]
      · rw [show f y = ((f y).toReal : EReal) by
          exact (EReal.coe_toReal hytop (ne_of_gt (hproper.2 y))).symm]
        simp [b, hytop]
    let β : ℝ := min (b - |a| * R) 0
    refine ⟨β, ?_⟩
    intro x
    by_cases hx : ‖x‖ ≤ R
    · have hxK : x ∈ K := by simpa [K] using hx
      have hnorm : a * ‖x‖ + β ≤ b := by
        have ha_norm : a * ‖x‖ ≤ |a| * R := by
          calc
            a * ‖x‖ ≤ |a| * ‖x‖ := by
              exact mul_le_mul_of_nonneg_right (le_abs_self a) (norm_nonneg x)
            _ ≤ |a| * R := mul_le_mul_of_nonneg_left hx (abs_nonneg a)
        have hβ : β ≤ b - |a| * R := min_le_left _ _
        linarith
      have hnormE :
          ((a * ‖x‖ + β : ℝ) : EReal) ≤ (b : EReal) := by
        exact_mod_cast hnorm
      exact hnormE.trans (hb.trans (hymin hxK))
    · have hxR : R ≤ ‖x‖ := le_of_not_ge hx
      have hreal : a * ‖x‖ + β ≤ c * ‖x‖ := by
        have hβ : β ≤ 0 := min_le_right _ _
        have hac' : a * ‖x‖ ≤ c * ‖x‖ :=
          mul_le_mul_of_nonneg_right hac.le (norm_nonneg x)
        linarith
      have hrealE :
          ((a * ‖x‖ + β : ℝ) : EReal) ≤ ((c * ‖x‖ : ℝ) : EReal) := by
        exact_mod_cast hreal
      exact hrealE.trans (hRext x hxR)
  · exact hasSequentialRadialSlopeAtLeast_of_forall_lt_affineNormLowerBound

/-! ## Comparison with the horizon function -/

/-- Every affine radial slope is a lower bound for the horizon function on
the unit sphere. -/
theorem affineNormLowerBound_le_unitSphereHorizonInf
    [FiniteDimensional ℝ E] {f : E → EReal} {γ β : ℝ}
    (hminor : HasAffineNormLowerBound f γ β) :
    (γ : EReal) ≤ unitSphereHorizonInf f := by
  unfold unitSphereHorizonInf
  refine le_iInf fun w ↦ ?_
  have h := hminor.le_horizonFunction (w : E)
  have hw : ‖(w : E)‖ = 1 := by
    have hp := w.property
    rw [Metric.mem_sphere, dist_zero_right] at hp
    exact hp
  simpa [hw] using h

/-- Formula 3(7), lower-bound direction, in exact sequential form: the radial
sequential liminf cannot exceed the infimum of `f∞` on the unit sphere.
The compactness-based converse and resulting equivalence are proved in
`CoercivityHorizonEquivalence.lean`. -/
theorem sequentialRadialSlope_le_unitSphereHorizonInf
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f) {γ : ℝ}
    (hseq : HasSequentialRadialSlopeAtLeast f γ) :
    (γ : EReal) ≤ unitSphereHorizonInf f := by
  have hminor :=
    (hasSequentialRadialSlopeAtLeast_iff_forall_lt_affineNormLowerBound
      hlsc hproper).mp hseq
  by_contra hnot
  have hlt : unitSphereHorizonInf f < (γ : EReal) := lt_of_not_ge hnot
  obtain ⟨a, hinf, haγ⟩ := EReal.exists_between_coe_real hlt
  have haγreal : a < γ := by exact_mod_cast haγ
  obtain ⟨β, hβ⟩ := hminor a haγreal
  exact (not_le_of_gt hinf)
    (affineNormLowerBound_le_unitSphereHorizonInf hβ)

/-! ## Coercivity predicates -/

/-- The project's affine-minorant definition of level coercivity is exactly
positive sequential radial slope. -/
theorem isLevelCoercive_iff_exists_pos_sequentialRadialSlope
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f) :
    IsLevelCoercive f ↔
      ∃ γ : ℝ, 0 < γ ∧ HasSequentialRadialSlopeAtLeast f γ := by
  constructor
  · rintro ⟨γ, hγ, β, hminor⟩
    refine ⟨γ, hγ, ?_⟩
    apply hasSequentialRadialSlopeAtLeast_of_forall_lt_affineNormLowerBound
    intro a ha
    exact ⟨β, hminor.mono_slope ha.le⟩
  · rintro ⟨γ, hγ, hseq⟩
    have hminor :=
      (hasSequentialRadialSlopeAtLeast_iff_forall_lt_affineNormLowerBound
        hlsc hproper).mp hseq
    obtain ⟨β, hβ⟩ := hminor (γ / 2) (half_lt_self hγ)
    exact ⟨γ / 2, half_pos hγ, β, hβ⟩

/-- Coercivity is equivalent to arbitrarily large sequential radial slopes. -/
theorem isCoercive_iff_forall_pos_sequentialRadialSlope
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f) :
    IsCoercive f ↔
      ∀ γ : ℝ, 0 < γ → HasSequentialRadialSlopeAtLeast f γ := by
  constructor
  · intro hf γ hγ
    apply hasSequentialRadialSlopeAtLeast_of_forall_lt_affineNormLowerBound
    intro a ha
    by_cases ha0 : 0 < a
    · exact hf a ha0
    · obtain ⟨β, hβ⟩ := hf γ hγ
      exact ⟨β, hβ.mono_slope ha.le⟩
  · intro hseq γ hγ
    have htwo : 0 < 2 * γ := by positivity
    have hminor :=
      (hasSequentialRadialSlopeAtLeast_iff_forall_lt_affineNormLowerBound
        hlsc hproper).mp (hseq (2 * γ) htwo)
    exact hminor γ (by linarith)

/-- Non-counter-coercivity is equivalent to the existence of some finite
sequential radial lower slope. -/
theorem not_isCounterCoercive_iff_exists_sequentialRadialSlope
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f) :
    ¬ IsCounterCoercive f ↔
      ∃ γ : ℝ, HasSequentialRadialSlopeAtLeast f γ := by
  constructor
  · intro hf
    obtain ⟨γ, β, hβ⟩ :=
      exists_affineNormLowerBound_of_not_isCounterCoercive hf
    refine ⟨γ, ?_⟩
    apply hasSequentialRadialSlopeAtLeast_of_forall_lt_affineNormLowerBound
    intro a ha
    exact ⟨β, hβ.mono_slope ha.le⟩
  · rintro ⟨γ, hseq⟩
    have hminor :=
      (hasSequentialRadialSlopeAtLeast_iff_forall_lt_affineNormLowerBound
        hlsc hproper).mp hseq
    obtain ⟨β, hβ⟩ := hminor (γ - 1) (by linarith)
    intro hcounter
    exact hcounter (γ - 1) ⟨β, hβ⟩

/-- Level coercivity forces a strictly positive unit-sphere horizon infimum. -/
theorem unitSphereHorizonInf_pos_of_isLevelCoercive
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsLevelCoercive f) :
    0 < unitSphereHorizonInf f := by
  obtain ⟨γ, hγ, β, hβ⟩ := hf
  have hpos : (0 : EReal) < (γ : EReal) := by exact_mod_cast hγ
  exact hpos.trans_le
    (affineNormLowerBound_le_unitSphereHorizonInf hβ)

/-- Coercivity forces the unit-sphere horizon infimum to be `⊤`. -/
theorem unitSphereHorizonInf_eq_top_of_isCoercive
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsCoercive f) :
    unitSphereHorizonInf f = ⊤ := by
  rw [EReal.eq_top_iff_forall_lt]
  intro a
  let γ : ℝ := max (a + 1) 1
  have hγ : 0 < γ := zero_lt_one.trans_le (le_max_right _ _)
  obtain ⟨β, hβ⟩ := hf γ hγ
  have haγ : a < γ :=
    (lt_add_one a).trans_le (le_max_left (a + 1) 1)
  have haγE : (a : EReal) < (γ : EReal) := by exact_mod_cast haγ
  exact haγE.trans_le
    (affineNormLowerBound_le_unitSphereHorizonInf hβ)

/-- A non-counter-coercive function has unit-sphere horizon infimum above
bottom. -/
theorem bot_lt_unitSphereHorizonInf_of_not_isCounterCoercive
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : ¬ IsCounterCoercive f) :
    ⊥ < unitSphereHorizonInf f := by
  obtain ⟨γ, β, hβ⟩ :=
    exists_affineNormLowerBound_of_not_isCounterCoercive hf
  exact (EReal.bot_lt_coe γ).trans_le
    (affineNormLowerBound_le_unitSphereHorizonInf hβ)

end RW
