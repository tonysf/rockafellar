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

import RockafellarWets.Chapter1.MoreauEnvelope
import RockafellarWets.Chapter2.Separation
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

/-- The quadratic Moreau kernel dominates every affine function after completing
the square. -/
private theorem affine_le_quadratic_kernel {γ lam t : ℝ} (hlam : 0 < lam) :
    γ * t + (-(lam * γ ^ 2) / 2) ≤ (1 / (2 * lam)) * t ^ 2 := by
  have h2lam : 0 < 2 * lam := by positivity
  have hs : 0 ≤ ((t - lam * γ) ^ 2) / (2 * lam) := by
    exact div_nonneg (sq_nonneg _) h2lam.le
  have hEq :
      ((t - lam * γ) ^ 2) / (2 * lam) =
        (1 / (2 * lam)) * t ^ 2 - γ * t + (lam * γ ^ 2) / 2 := by
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

/-- A coercive real-valued function admits an affine norm lower bound whose
slope dominates any prescribed continuous linear functional norm. -/
theorem exists_affineNormLowerBound_ge_opNorm_of_isCoercive_real
    {g : E → ℝ} (hg : IsCoercive fun x => (g x : EReal)) (l : E →L[ℝ] ℝ) :
    ∃ γ β : ℝ, ‖l‖ ≤ γ ∧ ∀ x : E, γ * ‖x‖ + β ≤ g x := by
  obtain ⟨β, hβ⟩ := hg (‖l‖ + 1) (by positivity)
  refine ⟨‖l‖ + 1, β, ?_, ?_⟩
  · linarith
  · intro x
    exact EReal.coe_le_coe_iff.mp (by simpa using hβ x)

/-- Coercivity of a real-valued common summand gives the bounded-below shifted
functional hypothesis needed in the algebraic cancellation lemmas. -/
theorem bddBelow_sub_continuousLinear_of_isCoercive_real
    {g : E → ℝ} (hg : IsCoercive (fun x : E => (g x : EReal))) (l : E →L[ℝ] ℝ) :
    BddBelow (Set.range fun x : E => g x - l x) := by
  rcases exists_affineNormLowerBound_ge_opNorm_of_isCoercive_real hg l
    with ⟨γ, β, hγ, hminor⟩
  exact RW.bddBelow_sub_continuousLinear_of_affineNormLowerBound g l hminor hγ

/-- Algebraic common-summand cancellation for shifted continuous-linear infima,
with coercivity supplying the bounded-below hypothesis on the common
summand. This packages the Chapter 1 cancellation identity in Chapter 3 terms. -/
theorem iInf_sub_continuousLinear_eq_of_infConvolution_eq_of_isCoercive_real
    {f₁ f₂ g : E → ℝ} (l : E →L[ℝ] ℝ)
    (hEq : f₁ □ g = f₂ □ g)
    (hbdd₁ : BddBelow (Set.range fun w : E => f₁ w - l w))
    (hbdd₂ : BddBelow (Set.range fun w : E => f₂ w - l w))
    (hg : IsCoercive (fun x : E => (g x : EReal))) :
    (⨅ w : E, f₁ w - l w) = (⨅ w : E, f₂ w - l w) := by
  rcases exists_affineNormLowerBound_ge_opNorm_of_isCoercive_real hg l
    with ⟨γ, β, hγ, hminor⟩
  exact RW.iInf_sub_continuousLinear_eq_of_infConvolution_eq_of_affineNormLowerBound
    f₁ f₂ g l hEq hbdd₁ hbdd₂ hminor hγ

/-- Quantified common-summand cancellation for shifted continuous-linear infima:
under a coercive common summand, the shifted infima of `f₁` and `f₂` agree for
every continuous linear functional as soon as both shifted functions are bounded
below. -/
theorem forall_iInf_sub_continuousLinear_eq_of_infConvolution_eq_of_isCoercive_real
    {f₁ f₂ g : E → ℝ}
    (hEq : f₁ □ g = f₂ □ g)
    (hg : IsCoercive (fun x : E => (g x : EReal))) :
    ∀ l : E →L[ℝ] ℝ,
      BddBelow (Set.range fun w : E => f₁ w - l w) →
      BddBelow (Set.range fun w : E => f₂ w - l w) →
      (⨅ w : E, f₁ w - l w) = (⨅ w : E, f₂ w - l w) := by
  intro l hbdd₁ hbdd₂
  exact iInf_sub_continuousLinear_eq_of_infConvolution_eq_of_isCoercive_real
    l hEq hbdd₁ hbdd₂ hg

/-- If all three real-valued summands are coercive, then the shifted
continuous-linear infima agree for every continuous linear functional. -/
theorem forall_iInf_sub_continuousLinear_eq_of_infConvolution_eq_of_isCoercive_real_of_isCoercive
    {f₁ f₂ g : E → ℝ}
    (hEq : f₁ □ g = f₂ □ g)
    (hf₁ : IsCoercive (fun x : E => (f₁ x : EReal)))
    (hf₂ : IsCoercive (fun x : E => (f₂ x : EReal)))
    (hg : IsCoercive (fun x : E => (g x : EReal))) :
    ∀ l : E →L[ℝ] ℝ,
      (⨅ w : E, f₁ w - l w) = (⨅ w : E, f₂ w - l w) := by
  intro l
  exact forall_iInf_sub_continuousLinear_eq_of_infConvolution_eq_of_isCoercive_real
    hEq hg l
    (bddBelow_sub_continuousLinear_of_isCoercive_real hf₁ l)
    (bddBelow_sub_continuousLinear_of_isCoercive_real hf₂ l)

/-- A coercive real-valued function is bounded below. -/
theorem bddBelow_of_isCoercive_real
    {g : E → ℝ} (hg : IsCoercive fun x => (g x : EReal)) :
    BddBelow (Set.range g) := by
  obtain ⟨β, hβ⟩ := hg 1 zero_lt_one
  refine ⟨β, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hx : ‖x‖ + β ≤ g x := by
    exact EReal.coe_le_coe_iff.mp (by simpa using hβ x)
  linarith [norm_nonneg x]

/-- Two globally bounded-below functions have bounded-below translated sums. -/
theorem bddBelow_add_slice_of_bddBelow_of_bddBelow
    {f g : E → ℝ} (hf : BddBelow (Set.range f)) (hg : BddBelow (Set.range g))
    (u : E) :
    BddBelow (Set.range fun w : E => f w + g (u - w)) := by
  rcases hf with ⟨c, hc⟩
  rcases hg with ⟨d, hd⟩
  refine ⟨c + d, ?_⟩
  rintro _ ⟨w, rfl⟩
  have hwf : c ≤ f w := hc ⟨w, rfl⟩
  have hwg : d ≤ g (u - w) := hd ⟨u - w, rfl⟩
  linarith

/-- The quadratic kernel in the Moreau envelope is coercive. -/
theorem isCoercive_quadraticKernel_real
    {lam : ℝ} (hlam : 0 < lam) :
    IsCoercive (fun x : E => (((1 / (2 * lam)) * ‖x‖ ^ 2 : ℝ) : EReal)) := by
  intro γ hγ
  refine ⟨-(lam * γ ^ 2) / 2, ?_⟩
  intro x
  have hquad :=
    affine_le_quadratic_kernel (γ := γ) (lam := lam) (t := ‖x‖) hlam
  have hreal :
      γ * ‖x‖ + (-(lam * γ ^ 2) / 2) ≤ (1 / (2 * lam)) * ‖x‖ ^ 2 := by
    exact hquad
  show (((γ * ‖x‖ + (-(lam * γ ^ 2) / 2) : ℝ) : EReal) ≤
      (((1 / (2 * lam)) * ‖x‖ ^ 2 : ℝ) : EReal))
  exact_mod_cast hreal

/-- A globally bounded-below function plus a coercive summand has bounded-below
infimal-convolution slices. -/
theorem bddBelow_infConvolution_slice_of_bddBelow_of_isCoercive_real
    {f g : E → ℝ} (hf : BddBelow (Set.range f))
    (hg : IsCoercive fun x => (g x : EReal)) (u : E) :
    BddBelow (Set.range fun w : E => f w + g (u - w)) := by
  rcases hf with ⟨c, hc⟩
  rcases bddBelow_of_isCoercive_real hg with ⟨β, hβ⟩
  refine ⟨c + β, ?_⟩
  rintro _ ⟨w, rfl⟩
  have hwf : c ≤ f w := hc ⟨w, rfl⟩
  have hwg : β ≤ g (u - w) := hβ ⟨u - w, rfl⟩
  linarith

/-- If `f` is bounded below and `g` is coercive, then `f □ g` is bounded
below. -/
theorem bddBelow_infConvolution_of_bddBelow_of_isCoercive_real
    {f g : E → ℝ} (hf : BddBelow (Set.range f))
    (hg : IsCoercive fun x => (g x : EReal)) :
    BddBelow (Set.range fun x : E => (f □ g) x) := by
  rcases hf with ⟨c, hc⟩
  rcases bddBelow_of_isCoercive_real hg with ⟨β, hβ⟩
  refine ⟨c + β, ?_⟩
  rintro _ ⟨x, rfl⟩
  unfold infConvolution
  refine le_ciInf ?_
  intro w
  have hwf : c ≤ f w := hc ⟨w, rfl⟩
  have hwg : β ≤ g (x - w) := hβ ⟨x - w, rfl⟩
  linarith

/-- Coercivity gives a uniform lower bound on the Moreau envelope. -/
theorem bddBelow_moreauEnvelope_of_isCoercive_real
    {g : E → ℝ} (hg : IsCoercive fun x => (g x : EReal))
    {lam : ℝ} (hlam : 0 < lam) :
    BddBelow (Set.range fun x : E => moreauEnvelope g lam x) := by
  rcases bddBelow_of_isCoercive_real hg with ⟨β, hβ⟩
  refine ⟨β, ?_⟩
  rintro _ ⟨x, rfl⟩
  unfold moreauEnvelope
  refine le_ciInf ?_
  intro w
  have hwg : β ≤ g w := hβ ⟨w, rfl⟩
  have hquad : 0 ≤ (1 / (2 * lam)) * ‖w - x‖ ^ 2 := by
    have hcoeff : 0 ≤ (1 / (2 * lam) : ℝ) := by positivity
    exact mul_nonneg hcoeff (sq_nonneg _)
  linarith

/-- Coercivity of the right summand discharges the bounded-below hypotheses
needed to reassociate a Moreau envelope across infimal convolution, provided
the left summand is globally bounded below. -/
theorem moreauEnvelope_infConvolution_assoc_of_bddBelow_of_isCoercive_real
    {f g : E → ℝ} (hf : BddBelow (Set.range f))
    (hg : IsCoercive fun x => (g x : EReal))
    {lam : ℝ} (hlam : 0 < lam) :
    moreauEnvelope (f □ g) lam = f □ moreauEnvelope g lam := by
  apply moreauEnvelope_infConvolution_assoc_of_bddBelow (f₁ := f) (f₂ := g) hlam
  · intro u
    exact bddBelow_infConvolution_slice_of_bddBelow_of_isCoercive_real hf hg u
  · intro u
    rcases bddBelow_of_isCoercive_real hg with ⟨β, hβ⟩
    refine ⟨β, ?_⟩
    rintro _ ⟨z, rfl⟩
    have hgz : β ≤ g z := hβ ⟨z, rfl⟩
    have hquad : 0 ≤ (1 / (2 * lam)) * ‖u - z‖ ^ 2 := by
      have hcoeff : 0 ≤ (1 / (2 * lam) : ℝ) := by positivity
      exact mul_nonneg hcoeff (sq_nonneg _)
    linarith
  · intro x
    rcases bddBelow_infConvolution_of_bddBelow_of_isCoercive_real hf hg with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    rintro _ ⟨u, rfl⟩
    have hfg : m ≤ (f □ g) u := hm ⟨u, rfl⟩
    have hquad : 0 ≤ (1 / (2 * lam)) * ‖x - u‖ ^ 2 := by
      have hcoeff : 0 ≤ (1 / (2 * lam) : ℝ) := by positivity
      exact mul_nonneg hcoeff (sq_nonneg _)
    linarith
  · intro x
    rcases hf with ⟨c, hc⟩
    rcases bddBelow_moreauEnvelope_of_isCoercive_real hg hlam with ⟨m, hm⟩
    refine ⟨c + m, ?_⟩
    rintro _ ⟨w, rfl⟩
    have hwf : c ≤ f w := hc ⟨w, rfl⟩
    have hmw : m ≤ moreauEnvelope g lam (x - w) := hm ⟨x - w, rfl⟩
    linarith

/-- In the presence of a coercive common summand, the Moreau envelope can be
reassociated in the book's preferred form `e_λ(f □ g) = e_λ f □ g` as soon as
`f` is bounded below. -/
theorem moreauEnvelope_infConvolution_eq_infConvolution_moreauEnvelope_of_bddBelow_of_isCoercive_real
    {f g : E → ℝ} (hf : BddBelow (Set.range f))
    (hg : IsCoercive fun x => (g x : EReal))
    {lam : ℝ} (hlam : 0 < lam) :
    moreauEnvelope (f □ g) lam = moreauEnvelope f lam □ g := by
  let q : E → ℝ := fun y => (1 / (2 * lam)) * ‖y‖ ^ 2
  have hmeq_fg : moreauEnvelope (f □ g) lam = (f □ g) □ q := by
    funext x
    simpa [q] using (moreauEnvelope_eq_infConvolution (f := f □ g) hlam x)
  have hmeq_f : moreauEnvelope f lam = f □ q := by
    funext x
    simpa [q] using (moreauEnvelope_eq_infConvolution (f := f) hlam x)
  have hqCoercive : IsCoercive (fun x : E => ((q x : ℝ) : EReal)) := by
    simpa [q] using (isCoercive_quadraticKernel_real (E := E) hlam)
  have hqBdd : BddBelow (Set.range q) := by
    simpa [q] using (bddBelow_of_isCoercive_real (E := E) hqCoercive)
  have hgBdd : BddBelow (Set.range g) := bddBelow_of_isCoercive_real hg
  have hfgBdd : BddBelow (Set.range fun x : E => (f □ g) x) :=
    bddBelow_infConvolution_of_bddBelow_of_isCoercive_real hf hg
  have hqgBdd : BddBelow (Set.range fun x : E => (q □ g) x) :=
    bddBelow_infConvolution_of_bddBelow_of_isCoercive_real hqBdd hg
  have hgqBdd : BddBelow (Set.range fun x : E => (g □ q) x) :=
    bddBelow_infConvolution_of_bddBelow_of_isCoercive_real hgBdd hqCoercive
  have hfgq :
      ((f □ g) □ q) = f □ (g □ q) := by
    exact infConvolution_assoc_of_bddBelow
      (f₁ := f) (f₂ := g) (f₃ := q)
      (fun u => bddBelow_infConvolution_slice_of_bddBelow_of_isCoercive_real hf hg u)
      (fun u => bddBelow_infConvolution_slice_of_bddBelow_of_isCoercive_real hgBdd hqCoercive u)
      (fun x => bddBelow_infConvolution_slice_of_bddBelow_of_isCoercive_real hfgBdd hqCoercive x)
      (fun x => bddBelow_add_slice_of_bddBelow_of_bddBelow hf hgqBdd x)
  have hfqg :
      ((f □ q) □ g) = f □ (q □ g) := by
    exact infConvolution_assoc_of_bddBelow
      (f₁ := f) (f₂ := q) (f₃ := g)
      (fun u => bddBelow_infConvolution_slice_of_bddBelow_of_isCoercive_real hf hqCoercive u)
      (fun u => bddBelow_infConvolution_slice_of_bddBelow_of_isCoercive_real hqBdd hg u)
      (fun x =>
        bddBelow_infConvolution_slice_of_bddBelow_of_isCoercive_real
          (bddBelow_infConvolution_of_bddBelow_of_isCoercive_real hf hqCoercive) hg x)
      (fun x => bddBelow_add_slice_of_bddBelow_of_bddBelow hf hqgBdd x)
  calc
    moreauEnvelope (f □ g) lam = ((f □ g) □ q) := hmeq_fg
    _ = f □ (g □ q) := hfgq
    _ = f □ (q □ g) := by
      congr 1
      funext x
      simpa [q] using (infConvolution_comm g q x)
    _ = ((f □ q) □ g) := hfqg.symm
    _ = (moreauEnvelope f lam) □ g := by rw [hmeq_f]

/-- Equality of infimal convolutions with a coercive common summand persists
after Moreau regularization of the left summand, provided both left summands are
globally bounded below. -/
theorem infConvolution_moreauEnvelope_eq_of_infConvolution_eq_of_bddBelow_of_isCoercive_real
    {f₁ f₂ g : E → ℝ}
    (hEq : f₁ □ g = f₂ □ g)
    (hf₁ : BddBelow (Set.range f₁)) (hf₂ : BddBelow (Set.range f₂))
    (hg : IsCoercive fun x => (g x : EReal))
    {lam : ℝ} (hlam : 0 < lam) :
    moreauEnvelope f₁ lam □ g = moreauEnvelope f₂ lam □ g := by
  calc
    moreauEnvelope f₁ lam □ g = moreauEnvelope (f₁ □ g) lam := by
      symm
      exact
        moreauEnvelope_infConvolution_eq_infConvolution_moreauEnvelope_of_bddBelow_of_isCoercive_real
          hf₁ hg hlam
    _ = moreauEnvelope (f₂ □ g) lam := by rw [hEq]
    _ = moreauEnvelope f₂ lam □ g :=
      moreauEnvelope_infConvolution_eq_infConvolution_moreauEnvelope_of_bddBelow_of_isCoercive_real
        hf₂ hg hlam

/-- Fully coercive wrapper for Moreau-regularized common-summand equality. -/
theorem infConvolution_moreauEnvelope_eq_of_infConvolution_eq_of_isCoercive_real_of_isCoercive
    {f₁ f₂ g : E → ℝ}
    (hEq : f₁ □ g = f₂ □ g)
    (hf₁ : IsCoercive fun x => (f₁ x : EReal))
    (hf₂ : IsCoercive fun x => (f₂ x : EReal))
    (hg : IsCoercive fun x => (g x : EReal))
    {lam : ℝ} (hlam : 0 < lam) :
    moreauEnvelope f₁ lam □ g = moreauEnvelope f₂ lam □ g := by
  exact
    infConvolution_moreauEnvelope_eq_of_infConvolution_eq_of_bddBelow_of_isCoercive_real
      hEq
      (bddBelow_of_isCoercive_real hf₁)
      (bddBelow_of_isCoercive_real hf₂)
      hg hlam

/-- If `f - l` is bounded below, then so is the shifted Moreau envelope
`e_λ f - l`. -/
theorem bddBelow_sub_continuousLinear_moreauEnvelope_of_bddBelow
    {f : E → ℝ} (l : E →L[ℝ] ℝ)
    (hf : BddBelow (Set.range fun w : E => f w - l w))
    {lam : ℝ} (hlam : 0 < lam) :
    BddBelow (Set.range fun x : E => moreauEnvelope f lam x - l x) := by
  let q : E → ℝ := fun y => (1 / (2 * lam)) * ‖y‖ ^ 2
  have hqCoercive : IsCoercive (fun x : E => ((q x : ℝ) : EReal)) := by
    simpa [q] using (isCoercive_quadraticKernel_real (E := E) hlam)
  have hq : BddBelow (Set.range fun w : E => q w - l w) :=
    bddBelow_sub_continuousLinear_of_isCoercive_real hqCoercive l
  rcases hf with ⟨c, hc⟩
  rcases hq with ⟨d, hd⟩
  refine ⟨c + d, ?_⟩
  rintro _ ⟨x, rfl⟩
  change c + d ≤ moreauEnvelope f lam x - l x
  rw [moreauEnvelope_eq_infConvolution (f := f) hlam x]
  unfold infConvolution
  have hLower : c + d + l x ≤ ⨅ w : E, f w + q (x - w) := by
    refine le_ciInf ?_
    intro w
    have hwf : c ≤ f w - l w := hc ⟨w, rfl⟩
    have hwq : d ≤ q (x - w) - l (x - w) := hd ⟨x - w, rfl⟩
    have hx : x = w + (x - w) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    have hlx : l x = l w + l (x - w) := by
      calc
        l x = l (w + (x - w)) := congrArg l hx
        _ = l w + l (x - w) := by rw [map_add]
    have hreal : c + d + l x ≤ f w + q (x - w) := by
      rw [hlx]
      linarith
    exact hreal
  linarith

/-- A coercive real-valued function remains bounded below after Moreau
regularization and subtraction of any continuous linear functional. -/
theorem bddBelow_sub_continuousLinear_moreauEnvelope_of_isCoercive_real
    {f : E → ℝ} (hf : IsCoercive fun x => (f x : EReal))
    (l : E →L[ℝ] ℝ) {lam : ℝ} (hlam : 0 < lam) :
    BddBelow (Set.range fun x : E => moreauEnvelope f lam x - l x) := by
  exact
    bddBelow_sub_continuousLinear_moreauEnvelope_of_bddBelow l
      (bddBelow_sub_continuousLinear_of_isCoercive_real hf l) hlam

/-- Coercive common-summand cancellation persists after Moreau regularization:
the shifted continuous-linear infima of the envelopes agree for every
`λ > 0`. This packages the algebraic `3(10)` step from Theorem `3.34`
under explicit bounded-below hypotheses on the original summands. -/
theorem iInf_sub_continuousLinear_eq_of_moreauEnvelope_infConvolution_eq_of_bddBelow_of_isCoercive_real
    {f₁ f₂ g : E → ℝ} (l : E →L[ℝ] ℝ)
    (hEq : f₁ □ g = f₂ □ g)
    (hf₁ : BddBelow (Set.range f₁)) (hf₂ : BddBelow (Set.range f₂))
    (hbdd₁ : BddBelow (Set.range fun w : E => f₁ w - l w))
    (hbdd₂ : BddBelow (Set.range fun w : E => f₂ w - l w))
    (hg : IsCoercive (fun x : E => (g x : EReal)))
    {lam : ℝ} (hlam : 0 < lam) :
    (⨅ w : E, moreauEnvelope f₁ lam w - l w) =
      (⨅ w : E, moreauEnvelope f₂ lam w - l w) := by
  have hEqME : moreauEnvelope f₁ lam □ g = moreauEnvelope f₂ lam □ g :=
    infConvolution_moreauEnvelope_eq_of_infConvolution_eq_of_bddBelow_of_isCoercive_real
      hEq hf₁ hf₂ hg hlam
  have hmbdd₁ : BddBelow (Set.range fun w : E => moreauEnvelope f₁ lam w - l w) :=
    bddBelow_sub_continuousLinear_moreauEnvelope_of_bddBelow l hbdd₁ hlam
  have hmbdd₂ : BddBelow (Set.range fun w : E => moreauEnvelope f₂ lam w - l w) :=
    bddBelow_sub_continuousLinear_moreauEnvelope_of_bddBelow l hbdd₂ hlam
  exact
    iInf_sub_continuousLinear_eq_of_infConvolution_eq_of_isCoercive_real
      l hEqME hmbdd₁ hmbdd₂ hg

/-- Quantified `3(10)`-style cancellation after Moreau regularization: under a
coercive common summand, the shifted continuous-linear infima of the Moreau
envelopes agree for every continuous linear functional. -/
theorem forall_iInf_sub_continuousLinear_eq_of_moreauEnvelope_infConvolution_eq_of_bddBelow_of_isCoercive_real
    {f₁ f₂ g : E → ℝ}
    (hEq : f₁ □ g = f₂ □ g)
    (hf₁ : BddBelow (Set.range f₁)) (hf₂ : BddBelow (Set.range f₂))
    (hg : IsCoercive (fun x : E => (g x : EReal)))
    {lam : ℝ} (hlam : 0 < lam) :
    ∀ l : E →L[ℝ] ℝ,
      BddBelow (Set.range fun w : E => f₁ w - l w) →
      BddBelow (Set.range fun w : E => f₂ w - l w) →
      (⨅ w : E, moreauEnvelope f₁ lam w - l w) =
        (⨅ w : E, moreauEnvelope f₂ lam w - l w) := by
  intro l hbdd₁ hbdd₂
  exact
    iInf_sub_continuousLinear_eq_of_moreauEnvelope_infConvolution_eq_of_bddBelow_of_isCoercive_real
      l hEq hf₁ hf₂ hbdd₁ hbdd₂ hg hlam

/-- Fully coercive `3(10)`-style cancellation after Moreau regularization:
if `f₁`, `f₂`, and the common summand `g` are coercive, then for every
`λ > 0` and every continuous linear functional `l`, the shifted
continuous-linear infima of `moreauEnvelope f₁ lam` and
`moreauEnvelope f₂ lam` agree. -/
theorem forall_iInf_sub_continuousLinear_eq_of_moreauEnvelope_infConvolution_eq_of_isCoercive_real_of_isCoercive
    {f₁ f₂ g : E → ℝ}
    (hEq : f₁ □ g = f₂ □ g)
    (hf₁ : IsCoercive (fun x : E => (f₁ x : EReal)))
    (hf₂ : IsCoercive (fun x : E => (f₂ x : EReal)))
    (hg : IsCoercive (fun x : E => (g x : EReal)))
    {lam : ℝ} (hlam : 0 < lam) :
    ∀ l : E →L[ℝ] ℝ,
      (⨅ w : E, moreauEnvelope f₁ lam w - l w) =
        (⨅ w : E, moreauEnvelope f₂ lam w - l w) := by
  intro l
  exact
    forall_iInf_sub_continuousLinear_eq_of_moreauEnvelope_infConvolution_eq_of_bddBelow_of_isCoercive_real
      hEq
      (bddBelow_of_isCoercive_real hf₁)
      (bddBelow_of_isCoercive_real hf₂)
      hg hlam l
      (bddBelow_sub_continuousLinear_of_isCoercive_real hf₁ l)
      (bddBelow_sub_continuousLinear_of_isCoercive_real hf₂ l)

section ConvexAnalyticEndpoint

variable [FiniteDimensional ℝ E] [CompleteSpace E]

/-- A point strictly below the epigraph of a real-valued closed convex function
admits a continuous affine minorant that is still strictly above that point. -/
theorem exists_affine_minorant_gt_of_lt_of_convex_lsc
    {f : E → ℝ}
    (hconv : Convex ℝ (epigraph (fun x => (f x : EReal))))
    (hlsc : LowerSemicontinuous (fun x => (f x : EReal)))
    {x : E} {r : ℝ} (hr : r < f x) :
    ∃ l : E →L[ℝ] ℝ, ∃ b : ℝ, r < l x + b ∧ ∀ y : E, l y + b ≤ f y := by
  let p : E × ℝ := (x, r)
  have hTne : (epigraph (fun y => (f y : EReal))).Nonempty := by
    refine ⟨(x, f x), ?_⟩
    rw [mem_epigraph_iff]
  have hdisj : Disjoint ({p} : Set (E × ℝ)) (epigraph (fun y => (f y : EReal))) := by
    rw [Set.disjoint_singleton_left]
    intro hp
    rw [mem_epigraph_iff] at hp
    exact not_le_of_gt hr (EReal.coe_le_coe_iff.mp hp)
  obtain ⟨φ, c₁, c₂, hc, hpoint, hepigraph⟩ :=
    strict_separation_of_convex_compact
      (E := E × ℝ)
      (S := ({p} : Set (E × ℝ)))
      (T := epigraph (fun y => (f y : EReal)))
      (convex_singleton p)
      (by simpa using Set.singleton_nonempty p)
      isCompact_singleton
      hconv
      hTne
      (isClosed_epigraph_of_lsc_ereal (fun y => (f y : EReal)) hlsc)
      hdisj
  let l₀ : E →L[ℝ] ℝ := φ.comp (ContinuousLinearMap.inl ℝ E ℝ)
  let a : ℝ := φ (0, 1)
  have hφ_apply : ∀ y : E, ∀ s : ℝ, φ (y, s) = l₀ y + a * s := by
    intro y s
    have hsplit : (y, s) = (y, (0 : ℝ)) + (0, s) := by
      ext <;> simp
    rw [hsplit, map_add]
    have hright : φ (0, s) = a * s := by
      have hs : ((0 : E), s) = s • ((0 : E), (1 : ℝ)) := by
        ext <;> simp
      rw [hs, map_smul]
      simp [a, mul_comm]
    simp [l₀, hright]
  have hpoint_apply : φ (x, r) < c₁ := hpoint p (by simp [p])
  have hepi_apply : c₂ < φ (x, f x) := by
    refine hepigraph (x, f x) ?_
    rw [mem_epigraph_iff]
  have ha_pos : 0 < a := by
    have hpoint_apply' := hpoint_apply
    have hepi_apply' := hepi_apply
    rw [hφ_apply x r] at hpoint_apply'
    rw [hφ_apply x (f x)] at hepi_apply'
    have hmul : 0 < a * f x - a * r := by
      linarith [hpoint_apply', hepi_apply', hc]
    have hfr : 0 < f x - r := sub_pos.mpr hr
    have hmul' : 0 < a * (f x - r) := by
      simpa [mul_sub] using hmul
    by_contra ha_nonpos
    have ha_le : a ≤ 0 := le_of_not_gt ha_nonpos
    have hnonpos : a * (f x - r) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha_le hfr.le
    exact not_le_of_gt hmul' hnonpos
  refine ⟨(-a⁻¹ : ℝ) • l₀, c₂ / a, ?_, ?_⟩
  · have hxr : φ (x, r) < c₂ := lt_trans hpoint_apply hc
    rw [hφ_apply x r] at hxr
    have hlt : a * r < c₂ - l₀ x := by
      linarith
    have hdiv : r < (c₂ - l₀ x) / a := by
      exact (lt_div_iff₀ ha_pos).2 (by simpa [mul_comm] using hlt)
    have hform : (((-a⁻¹ : ℝ) • l₀) x + c₂ / a) = (c₂ - l₀ x) / a := by
      simp [ContinuousLinearMap.smul_apply, div_eq_mul_inv, sub_eq_add_neg]
      ring
    rw [hform]
    exact hdiv
  · intro y
    have hyepi : c₂ < φ (y, f y) := by
      refine hepigraph (y, f y) ?_
      rw [mem_epigraph_iff]
    rw [hφ_apply y (f y)] at hyepi
    have hlt : c₂ - l₀ y < a * f y := by
      linarith
    have hdiv : (c₂ - l₀ y) / a < f y := by
      exact (div_lt_iff₀ ha_pos).2 (by simpa [mul_comm] using hlt)
    have hminor :
        (((-a⁻¹ : ℝ) • l₀) y + c₂ / a) < f y := by
      have hform : (((-a⁻¹ : ℝ) • l₀) y + c₂ / a) = (c₂ - l₀ y) / a := by
        simp [ContinuousLinearMap.smul_apply, div_eq_mul_inv, sub_eq_add_neg]
        ring
      rw [hform]
      exact hdiv
    exact le_of_lt hminor

/-- If every shifted continuous-linear infimum of `f₁` agrees with that of
`f₂`, then a real-valued closed convex `f₁` lies below `f₂`. The proof goes by
strictly separating any point below `epi f₁` from the epigraph. -/
theorem le_of_forall_iInf_sub_continuousLinear_eq_of_convex_lsc
    {f₁ f₂ : E → ℝ}
    (hconv₁ : Convex ℝ (epigraph (fun x => (f₁ x : EReal))))
    (hlsc₁ : LowerSemicontinuous (fun x => (f₁ x : EReal)))
    (hbdd₂ : ∀ l : E →L[ℝ] ℝ, BddBelow (Set.range fun w : E => f₂ w - l w))
    (hEqInf : ∀ l : E →L[ℝ] ℝ,
      (⨅ w : E, f₁ w - l w) = (⨅ w : E, f₂ w - l w)) :
    ∀ x : E, f₁ x ≤ f₂ x := by
  intro x
  by_contra hle
  have hxlt : f₂ x < f₁ x := lt_of_not_ge hle
  obtain ⟨l, b, hbx, hminor⟩ :=
    exists_affine_minorant_gt_of_lt_of_convex_lsc hconv₁ hlsc₁ (x := x) (r := f₂ x) hxlt
  have hb_le_inf₁ : b ≤ ⨅ w : E, f₁ w - l w := by
    refine le_ciInf ?_
    intro w
    have hw : l w + b ≤ f₁ w := hminor w
    linarith
  have hb_le_inf₂ : b ≤ ⨅ w : E, f₂ w - l w := by
    rw [← hEqInf l]
    exact hb_le_inf₁
  have hbx_le : b ≤ f₂ x - l x := le_trans hb_le_inf₂ (ciInf_le (hbdd₂ l) x)
  have hminor_x : l x + b ≤ f₂ x := by
    linarith
  exact not_le_of_gt hbx hminor_x

/-- Equality of all shifted continuous-linear infima characterizes a real-valued
closed convex function among functions with the same lower-bounded shifts. -/
theorem eq_of_forall_iInf_sub_continuousLinear_eq_of_convex_lsc
    {f₁ f₂ : E → ℝ}
    (hconv₁ : Convex ℝ (epigraph (fun x => (f₁ x : EReal))))
    (hlsc₁ : LowerSemicontinuous (fun x => (f₁ x : EReal)))
    (hconv₂ : Convex ℝ (epigraph (fun x => (f₂ x : EReal))))
    (hlsc₂ : LowerSemicontinuous (fun x => (f₂ x : EReal)))
    (hbdd₁ : ∀ l : E →L[ℝ] ℝ, BddBelow (Set.range fun w : E => f₁ w - l w))
    (hbdd₂ : ∀ l : E →L[ℝ] ℝ, BddBelow (Set.range fun w : E => f₂ w - l w))
    (hEqInf : ∀ l : E →L[ℝ] ℝ,
      (⨅ w : E, f₁ w - l w) = (⨅ w : E, f₂ w - l w)) :
    f₁ = f₂ := by
  funext x
  apply le_antisymm
  · exact le_of_forall_iInf_sub_continuousLinear_eq_of_convex_lsc
      hconv₁ hlsc₁ hbdd₂ hEqInf x
  · have hEqInf' : ∀ l : E →L[ℝ] ℝ,
        (⨅ w : E, f₂ w - l w) = (⨅ w : E, f₁ w - l w) := by
      intro l
      symm
      exact hEqInf l
    exact le_of_forall_iInf_sub_continuousLinear_eq_of_convex_lsc
      hconv₂ hlsc₂ hbdd₁ hEqInf' x

/-- Coercive common-summand cancellation for real-valued closed convex
functions: if `f₁ □ g = f₂ □ g` and all three functions are coercive, then
`f₁ = f₂`. This is the real-valued endpoint of Theorem `3.34` in the current
development. -/
theorem eq_of_infConvolution_eq_of_isCoercive_real_of_convex_lsc
    {f₁ f₂ g : E → ℝ}
    (hconv₁ : Convex ℝ (epigraph (fun x => (f₁ x : EReal))))
    (hlsc₁ : LowerSemicontinuous (fun x => (f₁ x : EReal)))
    (hconv₂ : Convex ℝ (epigraph (fun x => (f₂ x : EReal))))
    (hlsc₂ : LowerSemicontinuous (fun x => (f₂ x : EReal)))
    (hEq : f₁ □ g = f₂ □ g)
    (hf₁ : IsCoercive (fun x : E => (f₁ x : EReal)))
    (hf₂ : IsCoercive (fun x : E => (f₂ x : EReal)))
    (hg : IsCoercive (fun x : E => (g x : EReal))) :
    f₁ = f₂ := by
  apply eq_of_forall_iInf_sub_continuousLinear_eq_of_convex_lsc
    hconv₁ hlsc₁ hconv₂ hlsc₂
    (fun l => bddBelow_sub_continuousLinear_of_isCoercive_real hf₁ l)
    (fun l => bddBelow_sub_continuousLinear_of_isCoercive_real hf₂ l)
  intro l
  exact
    forall_iInf_sub_continuousLinear_eq_of_infConvolution_eq_of_isCoercive_real_of_isCoercive
      hEq hf₁ hf₂ hg l

end ConvexAnalyticEndpoint

end RW
