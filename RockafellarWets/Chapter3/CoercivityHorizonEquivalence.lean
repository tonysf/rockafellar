/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3: Coercivity from the Unit-Sphere Horizon Bound

This file supplies the compactness direction missing from the first version
of `CoercivityLimit.lean`.  If a real slope lies strictly below every
unit-direction horizon value, failure of a global affine norm minorant would
produce an escaping sequence.  Cosmic compactness extracts a limiting
direction, and the normalized epigraph points contradict the strict horizon
bound.
-/

import RockafellarWets.Chapter3.CoercivityLimit
import RockafellarWets.Chapter3.NonlinearImages

open Bornology EReal Filter Metric Set Topology

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A slope strictly below the unit-sphere infimum of the horizon function
admits a global affine norm minorant.  This is the compactness direction of
Theorem 3.26, formula 3(7). -/
theorem exists_affineNormLowerBound_of_coe_lt_unitSphereHorizonInf
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f)
    {a : ℝ} (ha : (a : EReal) < unitSphereHorizonInf f) :
    ∃ β : ℝ, HasAffineNormLowerBound f a β := by
  by_contra hminor
  have hminor' :
      ∀ β : ℝ, ∃ x : E,
        f x < ((a * ‖x‖ + β : ℝ) : EReal) := by
    intro β
    have hnot : ¬ HasAffineNormLowerBound f a β := by
      intro hβ
      exact hminor ⟨β, hβ⟩
    rw [HasAffineNormLowerBound] at hnot
    push_neg at hnot
    exact hnot
  choose x hx using fun n : ℕ ↦ hminor' (-(n : ℝ))
  have hxescape : Tendsto (fun n ↦ ‖x n‖) atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro R
    let R' : ℝ := max R 0
    have hR' : 0 ≤ R' := le_max_right _ _
    let K : Set E := closedBall 0 R'
    have hKne : K.Nonempty := by
      refine ⟨0, ?_⟩
      simp [K, hR']
    obtain ⟨y, hyK, hymin⟩ :=
      LowerSemicontinuousOn.exists_isMinOn hKne
        (isCompact_closedBall (0 : E) R')
        (hlsc.lowerSemicontinuousOn K)
    let m : ℝ := if f y = ⊤ then 0 else (f y).toReal
    have hm : (m : EReal) ≤ f y := by
      by_cases hytop : f y = ⊤
      · simp [m, hytop]
      · rw [show f y = ((f y).toReal : EReal) by
          exact (EReal.coe_toReal hytop
            (ne_of_gt (hproper.2 y))).symm]
        simp [m, hytop]
    have hlarge :
        ∀ᶠ n : ℕ in atTop,
          |a| * R' - m + 1 ≤ (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually
        (eventually_ge_atTop (|a| * R' - m + 1))
    filter_upwards [hlarge] with n hn
    have hRleR' : R ≤ R' := le_max_left _ _
    refine hRleR'.trans ?_
    by_contra hnorm
    have hnorm' : ‖x n‖ < R' := lt_of_not_ge hnorm
    have hxK : x n ∈ K := by
      change dist (x n) 0 ≤ R'
      simpa [dist_zero_right] using hnorm'.le
    have hmlower : (m : EReal) ≤ f (x n) :=
      hm.trans (hymin hxK)
    have hupper :
        f (x n) <
          ((a * ‖x n‖ - (n : ℝ) : ℝ) : EReal) := by
      simpa [sub_eq_add_neg] using hx n
    have hreal :
        m < a * ‖x n‖ - (n : ℝ) := by
      exact_mod_cast hmlower.trans_lt hupper
    have haNorm : a * ‖x n‖ ≤ |a| * R' := by
      calc
        a * ‖x n‖ ≤ |a| * ‖x n‖ := by
          exact mul_le_mul_of_nonneg_right
            (le_abs_self a) (norm_nonneg _)
        _ ≤ |a| * R' :=
          mul_le_mul_of_nonneg_left hnorm'.le (abs_nonneg a)
    linarith
  have hxunbounded : ¬ IsBounded (Set.range x) := by
    intro hbdd
    obtain ⟨R, hR⟩ := hbdd.exists_norm_le
    have hevent :=
      hxescape.eventually (eventually_ge_atTop (R + 1))
    obtain ⟨n, hn⟩ := hevent.exists
    have hxR : ‖x n‖ ≤ R :=
      hR (x n) (Set.mem_range_self n)
    linarith
  obtain ⟨u, φ, hφ, hcosmic⟩ :=
    exists_cosmicDirection_subsequence_of_not_isBounded
      (x := x) hxunbounded
  rcases exists_scaling_of_tendsto_cosmicDirection hcosmic with
    ⟨lam, hlamPos, hlamZero, hlamX⟩
  have hlamWithin :
      Tendsto lam atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hlamZero, Eventually.of_forall hlamPos⟩
  have hInv : Tendsto (fun n ↦ (lam n)⁻¹) atTop atTop :=
    hlamWithin.inv_tendsto_nhdsGT_zero
  let p : ℕ → E × ℝ :=
    fun n ↦ (x (φ n), a * ‖x (φ n)‖)
  have hp : ∀ n, p n ∈ epigraph f := by
    intro n
    change f (x (φ n)) ≤
      ((a * ‖x (φ n)‖ : ℝ) : EReal)
    have hstrict := hx (φ n)
    have hle :
        ((a * ‖x (φ n)‖ - (φ n : ℝ) : ℝ) : EReal) ≤
          ((a * ‖x (φ n)‖ : ℝ) : EReal) := by
      exact_mod_cast (sub_le_self _ (Nat.cast_nonneg _))
    exact hstrict.le.trans hle
  have hlamNorm :
      Tendsto (fun n ↦ lam n * ‖x (φ n)‖)
        atTop (𝓝 1) := by
    have hnorm := hlamX.norm
    simpa [norm_smul, Real.norm_eq_abs,
      abs_of_pos (hlamPos _),
      mem_sphere_zero_iff_norm.mp u.property] using hnorm
  have hlamP :
      Tendsto (fun n ↦ lam n • p n)
        atTop (𝓝 ((u : E), a)) := by
    have hsecond :
        Tendsto (fun n ↦ lam n * (a * ‖x (φ n)‖))
          atTop (𝓝 a) := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        (tendsto_const_nhds (x := a)).mul hlamNorm
    simpa [p, Prod.smul_mk, smul_eq_mul] using
      hlamX.prodMk_nhds hsecond
  have hdirAsymptotic :
      ((u : E), a) ∈ asymptoticCone ℝ (epigraph f) := by
    apply mem_asymptoticCone_of_seq_smul
      (c := fun n ↦ (lam n)⁻¹)
      (u := fun n ↦ lam n • p n)
      hInv hlamP
    intro n
    simpa [smul_smul, (hlamPos n).ne'] using hp n
  have hdir :
      ((u : E), a) ∈ horizonCone (epigraph f) :=
    Set.mem_insert_of_mem 0 hdirAsymptotic
  have hfa : horizonFunction f (u : E) ≤ (a : EReal) :=
    horizonFunction_le_of_mem_horizonCone_epigraph hdir
  have hinf :
      unitSphereHorizonInf f ≤ horizonFunction f (u : E) :=
    iInf_le (fun w : sphere (0 : E) 1 ↦
      horizonFunction f (w : E)) u
  exact (not_lt_of_ge (hinf.trans hfa)) ha

/-- **Theorem 3.26, formula (3(7)).**  For proper lower-semicontinuous
functions, the sequential radial lower slope `γ` is equivalent to `γ` lying
below the infimum of the horizon function on the unit sphere.  This is an
extended-real-safe formulation of the book's radial liminf identity. -/
theorem hasSequentialRadialSlopeAtLeast_iff_coe_le_unitSphereHorizonInf
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f) {γ : ℝ} :
    HasSequentialRadialSlopeAtLeast f γ ↔
      (γ : EReal) ≤ unitSphereHorizonInf f := by
  constructor
  · exact sequentialRadialSlope_le_unitSphereHorizonInf
      hlsc hproper
  · intro hγ
    apply
      (hasSequentialRadialSlopeAtLeast_iff_forall_lt_affineNormLowerBound
        hlsc hproper).2
    intro a ha
    apply exists_affineNormLowerBound_of_coe_lt_unitSphereHorizonInf
      hlsc hproper
    have hacoe : (a : EReal) < (γ : EReal) := by
      exact_mod_cast ha
    exact hacoe.trans_le hγ

/-- Strict unit-sphere horizon positivity implies level coercivity for proper
lsc functions.  Together with the converse in `CoercivityLimit.lean`, this is
Theorem 3.26(a) and the convex converse in Corollary 3.27. -/
theorem isLevelCoercive_of_unitSphereHorizonInf_pos
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f)
    (hpos : 0 < unitSphereHorizonInf f) :
    IsLevelCoercive f := by
  obtain ⟨γ, hγ0, hγinf⟩ :=
    EReal.exists_between_coe_real hpos
  have hγ : 0 < γ := by
    exact_mod_cast hγ0
  obtain ⟨β, hβ⟩ :=
    exists_affineNormLowerBound_of_coe_lt_unitSphereHorizonInf
      hlsc hproper hγinf
  exact ⟨γ, hγ, β, hβ⟩

/-- Proper lsc functions are level-coercive exactly when their horizon
function is uniformly positive on the unit sphere. -/
theorem isLevelCoercive_iff_unitSphereHorizonInf_pos
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f) :
    IsLevelCoercive f ↔ 0 < unitSphereHorizonInf f :=
  ⟨unitSphereHorizonInf_pos_of_isLevelCoercive,
    isLevelCoercive_of_unitSphereHorizonInf_pos hlsc hproper⟩

/-- Proper lower-semicontinuous functions are coercive exactly when their
unit-sphere horizon infimum is `⊤`. -/
theorem isCoercive_iff_unitSphereHorizonInf_eq_top
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f) :
    IsCoercive f ↔ unitSphereHorizonInf f = ⊤ := by
  constructor
  · exact unitSphereHorizonInf_eq_top_of_isCoercive
  · intro hinf γ hγ
    apply exists_affineNormLowerBound_of_coe_lt_unitSphereHorizonInf
      hlsc hproper
    rw [hinf]
    exact EReal.coe_lt_top γ

/-- Proper lower-semicontinuous functions fail to be counter-coercive exactly
when their unit-sphere horizon infimum is strictly above `⊥`. -/
theorem not_isCounterCoercive_iff_bot_lt_unitSphereHorizonInf
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f) :
    ¬ IsCounterCoercive f ↔
      ⊥ < unitSphereHorizonInf f := by
  constructor
  · exact bot_lt_unitSphereHorizonInf_of_not_isCounterCoercive
  · intro hinf hcounter
    obtain ⟨γ, hγbot, hγinf⟩ :=
      EReal.exists_between_coe_real hinf
    obtain ⟨β, hβ⟩ :=
      exists_affineNormLowerBound_of_coe_lt_unitSphereHorizonInf
        hlsc hproper hγinf
    exact hcounter γ ⟨β, hβ⟩

/-- Proper lower-semicontinuous functions are counter-coercive exactly when
the unit-sphere horizon infimum is `⊥`. -/
theorem isCounterCoercive_iff_unitSphereHorizonInf_eq_bot
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f) :
    IsCounterCoercive f ↔ unitSphereHorizonInf f = ⊥ := by
  constructor
  · intro hcounter
    apply bot_unique
    by_contra hnot
    have hbot :
        ⊥ < unitSphereHorizonInf f :=
      lt_of_not_ge hnot
    exact
      ((not_isCounterCoercive_iff_bot_lt_unitSphereHorizonInf
        hlsc hproper).2 hbot) hcounter
  · intro heq
    by_contra hnot
    have hbot :
        ⊥ < unitSphereHorizonInf f :=
      (not_isCounterCoercive_iff_bot_lt_unitSphereHorizonInf
        hlsc hproper).1 hnot
    rw [heq] at hbot
    exact (lt_irrefl ⊥) hbot

/-- For proper lsc convex functions, level boundedness and level coercivity
are equivalent.  This completes Corollary 3.27 in the project's affine
minorant encoding. -/
theorem isLevelBounded_iff_isLevelCoercive
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hconv : Convex ℝ (epigraph f))
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f) :
    IsLevelBounded f ↔ IsLevelCoercive f := by
  constructor
  · intro hlevel
    have h :=
      (isLevelBounded_iff_horizonFunction_pos
        hconv hlsc hproper).mp hlevel
    apply isLevelCoercive_of_unitSphereHorizonInf_pos
      hlsc hproper
    by_cases hne : (sphere (0 : E) 1).Nonempty
    · have hcompact :
          IsCompact (sphere (0 : E) 1) :=
        isCompact_sphere _ _
      obtain ⟨u, hu, humin⟩ :=
        LowerSemicontinuousOn.exists_isMinOn hne hcompact
          ((lowerSemicontinuous_horizonFunction f).lowerSemicontinuousOn _)
      have hu0 : u ≠ 0 := by
        intro hz
        rw [hz, mem_sphere, dist_zero_right, norm_zero] at hu
        norm_num at hu
      have hupos : 0 < horizonFunction f u :=
        h hu0
      have heq :
          unitSphereHorizonInf f =
            horizonFunction f u := by
        unfold unitSphereHorizonInf
        apply le_antisymm
        · exact iInf_le
            (fun w : sphere (0 : E) 1 ↦
              horizonFunction f (w : E))
            (⟨u, hu⟩ : sphere (0 : E) 1)
        · exact le_iInf fun w ↦ humin w.property
      rwa [heq]
    · have hempty : sphere (0 : E) 1 = ∅ :=
        not_nonempty_iff_eq_empty.mp hne
      letI : IsEmpty (sphere (0 : E) 1) :=
        Set.isEmpty_coe_sort.mpr hempty
      unfold unitSphereHorizonInf
      rw [iInf_of_empty]
      exact EReal.coe_lt_top 0
  · exact isLevelBounded_of_isLevelCoercive
      hconv hlsc hproper

end RW
