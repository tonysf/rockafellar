/- 
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3D: Coercivity Properties

This file formalizes the affine-minorant side of Section D:
- Definition 3.25: level coercivity, coercivity, counter-coercivity
- Theorem 3.26: horizon-function consequences of coercive lower bounds
- Corollary 3.27: level coercivity implies level boundedness in the convex case
- Example 3.28: non-counter-coercive functions have infinite prox-threshold

We encode the coercivity notions through the equivalent affine lower bounds from
Theorem 3.26, which are much more robust in Lean than the liminf-based
formulation.
-/

import RockafellarWets.Chapter3.HorizonFunctions
import Mathlib.Analysis.Normed.Module.FiniteDimension

open Set EReal Bornology Topology Metric

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `f` admits an affine lower bound in the norm with slope `γ` and intercept
`β`. -/
def HasAffineNormLowerBound (f : E → EReal) (γ β : ℝ) : Prop :=
  ∀ x : E, ((γ * ‖x‖ + β : ℝ) : EReal) ≤ f x

/-- **Definition 3.25 / Theorem 3.26(a)**: the affine-minorant form of level
coercivity. -/
def IsLevelCoercive (f : E → EReal) : Prop :=
  ∃ γ > 0, ∃ β : ℝ, HasAffineNormLowerBound f γ β

/-- **Definition 3.25 / Theorem 3.26(b)**: the affine-minorant form of
coercivity. -/
def IsCoercive (f : E → EReal) : Prop :=
  ∀ γ > 0, ∃ β : ℝ, HasAffineNormLowerBound f γ β

/-- **Definition 3.25 / Theorem 3.26(c)**: the affine-minorant form of
counter-coercivity. -/
def IsCounterCoercive (f : E → EReal) : Prop :=
  ∀ γ : ℝ, ¬ ∃ β : ℝ, HasAffineNormLowerBound f γ β

theorem isLevelCoercive_of_isCoercive {f : E → EReal} (hf : IsCoercive f) :
    IsLevelCoercive f := by
  obtain ⟨β, hβ⟩ := hf 1 zero_lt_one
  exact ⟨1, zero_lt_one, β, hβ⟩

theorem not_isCounterCoercive_of_isLevelCoercive {f : E → EReal}
    (hf : IsLevelCoercive f) :
    ¬ IsCounterCoercive f := by
  rintro hcounter
  rcases hf with ⟨γ, hγ, β, hβ⟩
  exact hcounter γ ⟨β, hβ⟩

/-- Unfolding `¬ IsCounterCoercive` produces an affine norm lower bound. -/
theorem exists_affineNormLowerBound_of_not_isCounterCoercive {f : E → EReal}
    (hf : ¬ IsCounterCoercive f) :
    ∃ γ β : ℝ, HasAffineNormLowerBound f γ β := by
  rw [IsCounterCoercive] at hf
  push_neg at hf
  exact hf

/-- Completing the square gives a global quadratic lower bound for every affine
minorant and every positive prox-parameter. -/
private theorem quadratic_lower_bound_of_affine {γ lam t : ℝ} (hlam : 0 < lam) :
    -(lam * γ ^ 2) / 2 ≤ γ * t + (1 / (2 * lam)) * t ^ 2 := by
  have h2lam : 0 < 2 * lam := by positivity
  have hs : 0 ≤ ((t + lam * γ) ^ 2) / (2 * lam) := by
    exact div_nonneg (sq_nonneg _) h2lam.le
  have hEq :
      ((t + lam * γ) ^ 2) / (2 * lam) =
        (1 / (2 * lam)) * t ^ 2 + γ * t + (lam * γ ^ 2) / 2 := by
    field_simp [hlam.ne']
    ring
  rw [hEq] at hs
  nlinarith

/-- An affine norm lower bound gives a witness showing every positive
prox-parameter belongs to the prox-threshold set. -/
theorem exists_proxThreshold_witness_of_affineNormLowerBound
    {f : E → EReal} {γ β lam : ℝ} (hlam : 0 < lam)
    (hminor : HasAffineNormLowerBound f γ β) :
    ∃ x : E, (⨅ w : E, f w + ((1 / (2 * lam)) * ‖w - x‖ ^ 2 : ℝ)) > ⊥ := by
  refine ⟨0, ?_⟩
  have hLower :
      (((β - lam * γ ^ 2 / 2 : ℝ) : EReal) ≤
        ⨅ w : E, f w + ((1 / (2 * lam)) * ‖w - (0 : E)‖ ^ 2 : ℝ)) := by
    refine le_iInf ?_
    intro w
    have hminorw : (((γ * ‖w‖ + β : ℝ) : EReal) ≤ f w) := hminor w
    have hquad :
        -(lam * γ ^ 2) / 2 ≤
          γ * ‖w‖ + (1 / (2 * lam)) * ‖w - (0 : E)‖ ^ 2 := by
      simpa using quadratic_lower_bound_of_affine (γ := γ) (lam := lam) (t := ‖w‖) hlam
    have hreal :
        β - lam * γ ^ 2 / 2 ≤
          γ * ‖w‖ + β + (1 / (2 * lam)) * ‖w - (0 : E)‖ ^ 2 := by
      linarith
    have hreal' :
        (((β - lam * γ ^ 2 / 2 : ℝ) : EReal) ≤
          (((γ * ‖w‖ + β + (1 / (2 * lam)) * ‖w - (0 : E)‖ ^ 2 : ℝ) : ℝ) : EReal)) := by
      exact_mod_cast hreal
    calc
      (((β - lam * γ ^ 2 / 2 : ℝ) : EReal)
          ≤ (((γ * ‖w‖ + β + (1 / (2 * lam)) * ‖w - (0 : E)‖ ^ 2 : ℝ) : ℝ) : EReal)) := hreal'
      _ = ((γ * ‖w‖ + β : ℝ) : EReal) + ((1 / (2 * lam)) * ‖w - (0 : E)‖ ^ 2 : ℝ) := by
            simp [EReal.coe_add]
      _ ≤ f w + ((1 / (2 * lam)) * ‖w - (0 : E)‖ ^ 2 : ℝ) := by
            exact add_le_add hminorw le_rfl
  exact (EReal.bot_lt_coe _).trans_le hLower

/-- Every positive parameter lies below the prox-threshold once an affine norm
lower bound is available. -/
theorem le_proxThreshold_of_affineNormLowerBound
    {f : E → EReal} {γ β lam : ℝ} (hlam : 0 < lam)
    (hminor : HasAffineNormLowerBound f γ β) :
    (lam : EReal) ≤ proxThreshold f := by
  unfold proxThreshold
  exact le_iSup_of_le lam <|
    le_iSup_of_le
      ⟨hlam, exists_proxThreshold_witness_of_affineNormLowerBound hlam hminor⟩
      le_rfl

/-- **Example 3.28** in the project's affine-minorant encoding: any function
with an affine norm lower bound has infinite prox-threshold. -/
theorem proxThreshold_eq_top_of_affineNormLowerBound
    {f : E → EReal} {γ β : ℝ} (hminor : HasAffineNormLowerBound f γ β) :
    proxThreshold f = ⊤ := by
  rw [EReal.eq_top_iff_forall_lt]
  intro y
  have hle : (((max (y + 1) 1 : ℝ) : EReal) ≤ proxThreshold f) :=
    le_proxThreshold_of_affineNormLowerBound
      (lam := max (y + 1) 1)
      (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) hminor
  have hlt : (y : EReal) < ((max (y + 1) 1 : ℝ) : EReal) := by
    exact_mod_cast lt_of_lt_of_le (lt_add_of_pos_right y zero_lt_one) (le_max_left _ _)
  exact lt_of_lt_of_le hlt hle

/-- **Example 3.28**: a non-counter-coercive function has infinite
prox-threshold. -/
theorem proxThreshold_eq_top_of_not_isCounterCoercive
    {f : E → EReal} (hf : ¬ IsCounterCoercive f) :
    proxThreshold f = ⊤ := by
  rcases exists_affineNormLowerBound_of_not_isCounterCoercive hf with ⟨γ, β, hminor⟩
  exact proxThreshold_eq_top_of_affineNormLowerBound hminor

/-- A level-coercive function has infinite prox-threshold. -/
theorem proxThreshold_eq_top_of_isLevelCoercive
    {f : E → EReal} (hf : IsLevelCoercive f) :
    proxThreshold f = ⊤ := by
  exact proxThreshold_eq_top_of_not_isCounterCoercive
    (not_isCounterCoercive_of_isLevelCoercive hf)

/-- A coercive function has infinite prox-threshold. -/
theorem proxThreshold_eq_top_of_isCoercive
    {f : E → EReal} (hf : IsCoercive f) :
    proxThreshold f = ⊤ := by
  exact proxThreshold_eq_top_of_isLevelCoercive
    (isLevelCoercive_of_isCoercive hf)

/-- An affine lower bound on `f` forces the same lower bound on its horizon
function. -/
theorem affineNormLowerBound_le_horizonFunction
    {f : E → EReal} (hconv : Convex ℝ (epigraph f)) (hlsc : LowerSemicontinuous f)
    (hproper : IsProper f) {γ β : ℝ} (hγ : 0 ≤ γ)
    (hminor : HasAffineNormLowerBound f γ β) {w : E} :
    ((γ * ‖w‖ : ℝ) : EReal) ≤ horizonFunction f w := by
  rcases hproper.1 with ⟨x₀, hx₀⟩
  have hbot₀ : f x₀ ≠ ⊥ := ne_of_gt (hproper.2 x₀)
  have htop₀ : f x₀ ≠ ⊤ := ne_of_lt hx₀
  have hx₀_epi : (x₀, (f x₀).toReal) ∈ epigraph f := by
    rw [mem_epigraph_iff]
    simpa [EReal.coe_toReal htop₀ hbot₀] using (le_rfl : f x₀ ≤ f x₀)
  refine le_iInf ?_
  intro a
  have ha_le : (γ * ‖w‖ : ℝ) ≤ (a : ℝ) := by
    by_contra hlt
    have hc : 0 < γ * ‖w‖ - (a : ℝ) := sub_pos.mpr (lt_of_not_ge hlt)
    let M : ℝ := (f x₀).toReal - β + γ * ‖x₀‖
    let τ : ℝ := (|M| + 1) / (γ * ‖w‖ - (a : ℝ))
    have hτ : 0 ≤ τ := by
      unfold τ
      positivity
    have hray :
        τ • (w, (a : ℝ)) + (x₀, (f x₀).toReal) ∈ epigraph f :=
      smul_add_mem_of_mem_horizonCone (C := epigraph f) hconv
        (isClosed_epigraph_of_lsc_ereal f hlsc) hx₀_epi a.property hτ
    have hupper : f (τ • w + x₀) ≤ ((f x₀).toReal + τ * (a : ℝ) : ℝ) := by
      rw [mem_epigraph_iff] at hray
      simpa [Prod.smul_mk, smul_eq_mul, add_comm, add_left_comm, add_assoc] using hray
    have hlower : ((γ * ‖τ • w + x₀‖ + β : ℝ) : EReal) ≤ f (τ • w + x₀) :=
      hminor (τ • w + x₀)
    have hreal :
        γ * ‖τ • w + x₀‖ + β ≤ (f x₀).toReal + τ * (a : ℝ) := by
      exact_mod_cast le_trans hlower hupper
    have hnorm :
        τ * ‖w‖ - ‖x₀‖ ≤ ‖τ • w + x₀‖ := by
      have htri : ‖τ • w‖ ≤ ‖τ • w + x₀‖ + ‖x₀‖ := by
        simpa [sub_eq_add_neg, add_assoc, norm_neg] using
          (norm_sub_le (τ • w + x₀) x₀)
      have hsmul : ‖τ • w‖ = τ * ‖w‖ := by
        simp [norm_smul, Real.norm_of_nonneg hτ]
      linarith
    have hlin :
        γ * (τ * ‖w‖ - ‖x₀‖) + β ≤ (f x₀).toReal + τ * (a : ℝ) := by
      nlinarith [hγ, hnorm, hreal]
    have hτbound : τ * (γ * ‖w‖ - (a : ℝ)) ≤ M := by
      unfold M at *
      nlinarith
    have hτeq : τ * (γ * ‖w‖ - (a : ℝ)) = |M| + 1 := by
      have hdenom : γ * ‖w‖ - (a : ℝ) ≠ 0 := ne_of_gt hc
      unfold τ
      field_simp [hdenom]
    have habs : M ≤ |M| := le_abs_self M
    linarith
  exact_mod_cast ha_le

/-- A level-coercive proper lsc convex function has strictly positive horizon
function away from `0`. -/
theorem horizonFunction_pos_of_isLevelCoercive
    {f : E → EReal} (hconv : Convex ℝ (epigraph f)) (hlsc : LowerSemicontinuous f)
    (hproper : IsProper f) (hf : IsLevelCoercive f) {w : E} (hw : w ≠ 0) :
    0 < horizonFunction f w := by
  rcases hf with ⟨γ, hγ, β, hβ⟩
  have hbound :
      ((γ * ‖w‖ : ℝ) : EReal) ≤ horizonFunction f w :=
    affineNormLowerBound_le_horizonFunction hconv hlsc hproper hγ.le hβ
  have hpos : (0 : EReal) < ((γ * ‖w‖ : ℝ) : EReal) := by
    exact_mod_cast mul_pos hγ (norm_pos_iff.mpr hw)
  exact hpos.trans_le hbound

/-- A coercive proper lsc convex function has horizon function equal to `⊤` in
every nonzero direction. -/
theorem horizonFunction_eq_top_of_isCoercive
    {f : E → EReal} (hconv : Convex ℝ (epigraph f)) (hlsc : LowerSemicontinuous f)
    (hproper : IsProper f) (hf : IsCoercive f) {w : E} (hw : w ≠ 0) :
    horizonFunction f w = ⊤ := by
  have hbound₁ :
      ((‖w‖ : ℝ) : EReal) ≤ horizonFunction f w := by
    obtain ⟨β, hβ⟩ := hf 1 zero_lt_one
    simpa using
      (affineNormLowerBound_le_horizonFunction hconv hlsc hproper (γ := 1) (β := β)
        (by norm_num) hβ (w := w))
  have hpos : (0 : EReal) < horizonFunction f w := by
    have hnorm : (0 : EReal) < ((‖w‖ : ℝ) : EReal) := by
      exact_mod_cast norm_pos_iff.mpr hw
    exact hnorm.trans_le hbound₁
  by_contra htop
  have hne_bot : horizonFunction f w ≠ ⊥ := by
    intro hbot
    simpa [hbot] using hpos
  let γ : ℝ := ((horizonFunction f w).toReal + 1) / ‖w‖
  have hγ : 0 < γ := by
    unfold γ
    have htoReal : 0 < (horizonFunction f w).toReal :=
      EReal.toReal_pos hpos htop
    positivity
  obtain ⟨β, hβ⟩ := hf γ hγ
  have hbound :
      ((γ * ‖w‖ : ℝ) : EReal) ≤ horizonFunction f w :=
    affineNormLowerBound_le_horizonFunction hconv hlsc hproper hγ.le hβ
  have hγeq : γ * ‖w‖ = (horizonFunction f w).toReal + 1 := by
    have hnorm : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
    unfold γ
    field_simp [hnorm]
  have hlt_real : (horizonFunction f w).toReal < γ * ‖w‖ := by
    rw [hγeq]
    linarith
  have hlt :
      horizonFunction f w < ((γ * ‖w‖ : ℝ) : EReal) := by
    rw [← EReal.coe_toReal htop hne_bot]
    exact_mod_cast hlt_real
  exact not_lt_of_ge hbound hlt

/-- If the horizon function is strictly positive away from `0`, then a proper
lsc convex function is level-bounded. This is the level-boundedness half of
Corollary 3.27. -/
theorem isLevelBounded_of_horizonFunction_pos [FiniteDimensional ℝ E]
    {f : E → EReal} (hconv : Convex ℝ (epigraph f)) (hlsc : LowerSemicontinuous f)
    (hf : ∀ ⦃w : E⦄, w ≠ 0 → 0 < horizonFunction f w) :
    IsLevelBounded f := by
  intro α
  by_cases hlevel : (levelSet f α).Nonempty
  · have hzero :
        levelSet (horizonFunction f) (0 : EReal) = ({0} : Set E) := by
      apply le_antisymm
      · intro w hw
        by_contra hw0
        have hpos := hf hw0
        have hle : horizonFunction f w ≤ 0 := by
          simpa [levelSet] using hw
        exact not_le_of_gt hpos hle
      · intro w hw
        simp at hw
        subst hw
        simpa [levelSet] using (positivelyHomogeneous_horizonFunction f).map_zero_le_zero
    have hhcone : horizonCone (levelSet f α) = ({0} : Set E) := by
      calc
        horizonCone (levelSet f α) = levelSet (horizonFunction f) (0 : EReal) := by
          exact horizonCone_levelSet_eq_levelSet_horizonFunction hconv hlsc hlevel
        _ = ({0} : Set E) := hzero
    exact (isBounded_iff_horizonCone_eq_singleton_zero).2 hhcone
  · have hempty : levelSet f α = ∅ := Set.not_nonempty_iff_eq_empty.mp hlevel
    simpa [hempty] using (isBounded_empty : Bornology.IsBounded (∅ : Set E))

/-- A level-coercive proper lsc convex function is level-bounded. -/
theorem isLevelBounded_of_isLevelCoercive [FiniteDimensional ℝ E]
    {f : E → EReal} (hconv : Convex ℝ (epigraph f)) (hlsc : LowerSemicontinuous f)
    (hproper : IsProper f) (hf : IsLevelCoercive f) :
    IsLevelBounded f := by
  apply isLevelBounded_of_horizonFunction_pos hconv hlsc
  intro w hw
  exact horizonFunction_pos_of_isLevelCoercive hconv hlsc hproper hf hw

end RW
