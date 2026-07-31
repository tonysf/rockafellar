/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3: The Cosmic Space

This file gives a closed-unit-ball model for the cosmic space in Definition
3.1 and Theorem 3.2 of Rockafellar--Wets.

Mathlib's canonical homeomorphism identifies a real normed space `E` with its
open unit ball by

`x ↦ (sqrt (1 + ‖x‖ ^ 2))⁻¹ • x`.

We compactify by including that open ball in the closed unit ball.  Its sphere
is the boundary of directions.  In finite dimension the resulting space is
compact.  We prove:

* ordinary points form an embedded copy of `E`;
* convergence to an ordinary point is exactly ordinary convergence in `E`;
* convergence to a direction is equivalent to the positive-vanishing-scaling
  criterion in Definition 3.1;
* every cosmic point is either ordinary or a direction point, and the two
  cases are disjoint;
* ordinary points are dense in the ambient closed ball;
* every sequence of ordinary points has a cosmically convergent subsequence;
* every direction point is the limit of an explicit radial sequence of
  ordinary points.
-/

import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Sequences

open Bornology Filter Function Metric Set Topology

namespace RW

section CosmicSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Definition 3.1 (closed-ball model).** The cosmic compactification of
`E`, realized as its closed unit ball. -/
abbrev CosmicSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  closedBall (0 : E) 1

/-- The ordinary (open-ball) part of the cosmic compactification. -/
abbrev CosmicInterior (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  ball (0 : E) 1

/-- The direction boundary of the cosmic compactification. -/
abbrev CosmicBoundary (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  sphere (0 : E) 1

/-- The canonical homeomorphism from `E` to the ordinary part of its cosmic
compactification. -/
noncomputable def cosmicInteriorHomeomorph : E ≃ₜ CosmicInterior E :=
  Homeomorph.unitBall

/-- Inclusion of the ordinary part into the full cosmic space. -/
def cosmicInteriorInclusion : CosmicInterior E → CosmicSpace E :=
  Set.inclusion ball_subset_closedBall

/-- The ordinary-point embedding of `E` into its cosmic compactification. -/
noncomputable def cosmicEmbed (x : E) : CosmicSpace E :=
  cosmicInteriorInclusion (cosmicInteriorHomeomorph x)

/-- The positive scaling coefficient used by the ordinary-point chart. -/
noncomputable def cosmicScale (x : E) : ℝ :=
  (Real.sqrt (1 + ‖x‖ ^ 2))⁻¹

/-- Comparison coefficient for a positive rescaling of an ordinary point. -/
noncomputable def cosmicComparisonScale (r : ℝ) (x : E) : ℝ :=
  (Real.sqrt (r ^ 2 + ‖r • x‖ ^ 2))⁻¹

/-- Inclusion of a unit direction into the boundary of the cosmic space. -/
def cosmicDirection (u : CosmicBoundary E) : CosmicSpace E :=
  Set.inclusion sphere_subset_closedBall u

@[simp]
theorem coe_cosmicInteriorInclusion (x : CosmicInterior E) :
    ((cosmicInteriorInclusion x : CosmicSpace E) : E) = x := by
  rfl

@[simp]
theorem coe_cosmicEmbed (x : E) :
    ((cosmicEmbed x : CosmicSpace E) : E) = cosmicInteriorHomeomorph x := by
  rfl

theorem coe_cosmicEmbed_eq_cosmicScale_smul (x : E) :
    ((cosmicEmbed x : CosmicSpace E) : E) = cosmicScale x • x := by
  rfl

omit [NormedSpace ℝ E] in
theorem cosmicScale_pos (x : E) : 0 < cosmicScale x := by
  exact inv_pos.mpr (Real.sqrt_pos.2 (by positivity))

/-- The chart coefficient and the norm of the embedded point satisfy the
Pythagorean identity used at the cosmic boundary. -/
theorem cosmicScale_sq_add_norm_sq (x : E) :
    cosmicScale x ^ 2 + ‖cosmicScale x • x‖ ^ 2 = 1 := by
  have hspos : 0 < Real.sqrt (1 + ‖x‖ ^ 2) :=
    Real.sqrt_pos.2 (by positivity)
  have hsquare :
      Real.sqrt (1 + ‖x‖ ^ 2) ^ 2 = 1 + ‖x‖ ^ 2 :=
    Real.sq_sqrt (by positivity)
  rw [norm_smul_of_nonneg (cosmicScale_pos x).le]
  simp only [cosmicScale]
  field_simp
  nlinarith

/-- Re-express the canonical chart image through any positive rescaling of
the original vector. -/
theorem cosmicScale_smul_eq_comparisonScale_smul (x : E) {r : ℝ}
    (hr : 0 < r) :
    cosmicScale x • x = cosmicComparisonScale r x • (r • x) := by
  have hsqrt :
      Real.sqrt (r ^ 2 + ‖r • x‖ ^ 2) =
        r * Real.sqrt (1 + ‖x‖ ^ 2) := by
    rw [norm_smul_of_nonneg hr.le]
    have harg :
        r ^ 2 + (r * ‖x‖) ^ 2 = r ^ 2 * (1 + ‖x‖ ^ 2) := by
      ring
    rw [harg, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs,
      abs_of_pos hr]
  rw [cosmicScale, cosmicComparisonScale, hsqrt, smul_smul]
  have hs : Real.sqrt (1 + ‖x‖ ^ 2) ≠ 0 :=
    (Real.sqrt_pos.2 (by positivity)).ne'
  field_simp

@[simp]
theorem coe_cosmicDirection (u : CosmicBoundary E) :
    ((cosmicDirection u : CosmicSpace E) : E) = u := by
  rfl

/-- Ordinary cosmic points lie strictly inside the closed unit ball. -/
theorem norm_cosmicEmbed_lt_one (x : E) :
    ‖((cosmicEmbed x : CosmicSpace E) : E)‖ < 1 := by
  exact mem_ball_zero_iff.mp (cosmicInteriorHomeomorph x).property

/-- Direction points lie on the unit sphere. -/
theorem norm_cosmicDirection (u : CosmicBoundary E) :
    ‖((cosmicDirection u : CosmicSpace E) : E)‖ = 1 := by
  exact mem_sphere_zero_iff_norm.mp u.property

/-- The inclusion of the open ball into the closed ball is an embedding. -/
theorem isEmbedding_cosmicInteriorInclusion :
    IsEmbedding (cosmicInteriorInclusion : CosmicInterior E → CosmicSpace E) := by
  exact IsEmbedding.inclusion ball_subset_closedBall

/-- Ordinary points form an embedded copy of `E` in the cosmic space. -/
theorem isEmbedding_cosmicEmbed :
    IsEmbedding (cosmicEmbed : E → CosmicSpace E) := by
  simpa only [cosmicEmbed] using
    isEmbedding_cosmicInteriorInclusion.comp
      (cosmicInteriorHomeomorph (E := E)).isEmbedding

theorem continuous_cosmicEmbed :
    Continuous (cosmicEmbed : E → CosmicSpace E) :=
  isEmbedding_cosmicEmbed.continuous

theorem injective_cosmicEmbed :
    Injective (cosmicEmbed : E → CosmicSpace E) :=
  isEmbedding_cosmicEmbed.injective

theorem injective_cosmicDirection :
    Injective (cosmicDirection : CosmicBoundary E → CosmicSpace E) := by
  exact Set.inclusion_injective sphere_subset_closedBall

/-- Direction points form an embedded copy of the unit sphere in cosmic
space. -/
theorem isEmbedding_cosmicDirection :
    IsEmbedding (cosmicDirection : CosmicBoundary E → CosmicSpace E) := by
  exact IsEmbedding.inclusion sphere_subset_closedBall

/-- Ordinary-point clause of **Definition 3.1**: cosmic convergence to an
ordinary point agrees exactly with convergence in the original normed space. -/
theorem tendsto_cosmicEmbed_iff {α : Type*} {l : Filter α} {x : α → E} {x₀ : E} :
    Tendsto (fun i ↦ cosmicEmbed (x i)) l (𝓝 (cosmicEmbed x₀)) ↔
      Tendsto x l (𝓝 x₀) := by
  simpa only [Function.comp_def] using
    ((isEmbedding_cosmicEmbed (E := E)).tendsto_nhds_iff
      (f := x) (l := l) (y := x₀)).symm

/-- The underlying range of the ordinary embedding is the open unit ball. -/
theorem range_coe_cosmicEmbed :
    Set.range (fun x : E ↦ ((cosmicEmbed x : CosmicSpace E) : E)) =
      ball (0 : E) 1 := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact (cosmicInteriorHomeomorph x).property
  · intro hy
    let y' : CosmicInterior E := ⟨y, hy⟩
    refine ⟨(cosmicInteriorHomeomorph (E := E)).symm y', ?_⟩
    change
      (((cosmicInteriorHomeomorph (E := E))
        ((cosmicInteriorHomeomorph (E := E)).symm y') : CosmicInterior E) : E) = y
    simp [y']

/-- A cosmic point is ordinary exactly when its norm is strictly less than
one. -/
theorem exists_cosmicEmbed_eq_iff (p : CosmicSpace E) :
    (∃ x : E, cosmicEmbed x = p) ↔ ‖(p : E)‖ < 1 := by
  constructor
  · rintro ⟨x, rfl⟩
    exact norm_cosmicEmbed_lt_one x
  · intro hp
    let p' : CosmicInterior E :=
      ⟨p, mem_ball_zero_iff.mpr hp⟩
    refine ⟨(cosmicInteriorHomeomorph (E := E)).symm p', ?_⟩
    apply Subtype.ext
    change
      (((cosmicInteriorHomeomorph (E := E))
        ((cosmicInteriorHomeomorph (E := E)).symm p') : CosmicInterior E) : E) = p
    simp [p']

/-- A cosmic point is a direction point exactly when its norm is one. -/
theorem exists_cosmicDirection_eq_iff (p : CosmicSpace E) :
    (∃ u : CosmicBoundary E, cosmicDirection u = p) ↔ ‖(p : E)‖ = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    exact norm_cosmicDirection u
  · intro hp
    let u : CosmicBoundary E :=
      ⟨p, mem_sphere_zero_iff_norm.mpr hp⟩
    exact ⟨u, Subtype.ext (by simp [u])⟩

/-- Every cosmic point is either ordinary or a direction point. -/
theorem cosmicEmbed_or_cosmicDirection (p : CosmicSpace E) :
    (∃ x : E, cosmicEmbed x = p) ∨
      (∃ u : CosmicBoundary E, cosmicDirection u = p) := by
  have hp : ‖(p : E)‖ ≤ 1 := mem_closedBall_zero_iff.mp p.property
  rcases hp.lt_or_eq with hp | hp
  · exact Or.inl ((exists_cosmicEmbed_eq_iff p).mpr hp)
  · exact Or.inr ((exists_cosmicDirection_eq_iff p).mpr hp)

/-- Ordinary and direction points are disjoint. -/
theorem cosmicEmbed_ne_cosmicDirection (x : E) (u : CosmicBoundary E) :
    cosmicEmbed x ≠ cosmicDirection u := by
  intro h
  have hnorm :
      ‖((cosmicEmbed x : CosmicSpace E) : E)‖ =
        ‖((cosmicDirection u : CosmicSpace E) : E)‖ :=
    congrArg (fun p : CosmicSpace E ↦ ‖(p : E)‖) h
  rw [norm_cosmicDirection u] at hnorm
  exact (norm_cosmicEmbed_lt_one x).ne hnorm

/-- If ordinary points converge to a direction, their canonical chart
coefficients tend to zero. -/
theorem tendsto_cosmicScale_of_tendsto_cosmicDirection
    {x : ℕ → E} {u : CosmicBoundary E}
    (h : Tendsto (fun n ↦ cosmicEmbed (x n)) atTop
      (𝓝 (cosmicDirection u))) :
    Tendsto (fun n ↦ cosmicScale (x n)) atTop (𝓝 0) := by
  have hscaled :
      Tendsto (fun n ↦ cosmicScale (x n) • x n) atTop (𝓝 (u : E)) := by
    simpa only [coe_cosmicEmbed_eq_cosmicScale_smul,
      coe_cosmicDirection] using tendsto_subtype_rng.mp h
  have hnormsq :
      Tendsto (fun n ↦ ‖cosmicScale (x n) • x n‖ ^ 2)
        atTop (𝓝 1) := by
    convert hscaled.norm.pow 2 using 1
    simp only [mem_sphere_zero_iff_norm.mp u.property, one_pow]
  have hsquare :
      Tendsto (fun n ↦ cosmicScale (x n) ^ 2) atTop (𝓝 0) := by
    have hsub :
        Tendsto (fun n ↦ 1 - ‖cosmicScale (x n) • x n‖ ^ 2)
          atTop (𝓝 (1 - 1)) :=
      tendsto_const_nhds.sub hnormsq
    rw [sub_self] at hsub
    exact hsub.congr' (Eventually.of_forall fun n ↦ by
      nlinarith [cosmicScale_sq_add_norm_sq (x n)])
  have hroot :
      Tendsto (fun n ↦ Real.sqrt (cosmicScale (x n) ^ 2))
        atTop (𝓝 (Real.sqrt 0)) :=
    hsquare.sqrt
  simpa only [Real.sqrt_sq_eq_abs, abs_of_pos (cosmicScale_pos _),
    Real.sqrt_zero] using hroot

/-- Forward direction of the direction clause of **Definition 3.1**.  The
canonical chart coefficients provide the required positive vanishing
scalars. -/
theorem exists_scaling_of_tendsto_cosmicDirection
    {x : ℕ → E} {u : CosmicBoundary E}
    (h : Tendsto (fun n ↦ cosmicEmbed (x n)) atTop
      (𝓝 (cosmicDirection u))) :
    ∃ scale : ℕ → ℝ, (∀ n, 0 < scale n) ∧
      Tendsto scale atTop (𝓝 0) ∧
      Tendsto (fun n ↦ scale n • x n) atTop (𝓝 (u : E)) := by
  refine ⟨fun n ↦ cosmicScale (x n), fun n ↦ cosmicScale_pos (x n),
    tendsto_cosmicScale_of_tendsto_cosmicDirection h, ?_⟩
  simpa only [coe_cosmicEmbed_eq_cosmicScale_smul,
    coe_cosmicDirection] using tendsto_subtype_rng.mp h

/-- If a positive rescaling tends to a unit vector while its coefficients
tend to zero, the comparison coefficient between that rescaling and the
canonical cosmic chart tends to one. -/
theorem tendsto_cosmicComparisonScale
    {x : ℕ → E} {u : CosmicBoundary E} {scale : ℕ → ℝ}
    (hscale : Tendsto scale atTop (𝓝 0))
    (hscaled : Tendsto (fun n ↦ scale n • x n) atTop (𝓝 (u : E))) :
    Tendsto (fun n ↦ cosmicComparisonScale (scale n) (x n))
      atTop (𝓝 1) := by
  have hsumsq :
      Tendsto
        (fun n ↦ scale n ^ 2 + ‖scale n • x n‖ ^ 2)
        atTop (𝓝 (0 ^ 2 + ‖(u : E)‖ ^ 2)) :=
    (hscale.pow 2).add (hscaled.norm.pow 2)
  have hsqrt :
      Tendsto
        (fun n ↦ Real.sqrt (scale n ^ 2 + ‖scale n • x n‖ ^ 2))
        atTop (𝓝 1) := by
    convert hsumsq.sqrt using 1
    norm_num [mem_sphere_zero_iff_norm.mp u.property]
  simpa only [cosmicComparisonScale, inv_one] using hsqrt.inv₀ one_ne_zero

/-- Converse direction of the direction clause of **Definition 3.1**. -/
theorem tendsto_cosmicDirection_of_scaling
    {x : ℕ → E} {u : CosmicBoundary E} {scale : ℕ → ℝ}
    (hpos : ∀ n, 0 < scale n)
    (hscale : Tendsto scale atTop (𝓝 0))
    (hscaled : Tendsto (fun n ↦ scale n • x n) atTop (𝓝 (u : E))) :
    Tendsto (fun n ↦ cosmicEmbed (x n)) atTop
      (𝓝 (cosmicDirection u)) := by
  have hcomparison :
      Tendsto (fun n ↦
        cosmicComparisonScale (scale n) (x n) • (scale n • x n))
        atTop (𝓝 (u : E)) := by
    simpa only [one_smul] using
      (tendsto_cosmicComparisonScale hscale hscaled).smul hscaled
  have hcanonical :
      Tendsto (fun n ↦ cosmicScale (x n) • x n)
        atTop (𝓝 (u : E)) :=
    hcomparison.congr' (Eventually.of_forall fun n ↦
      (cosmicScale_smul_eq_comparisonScale_smul (x n) (hpos n)).symm)
  apply tendsto_subtype_rng.mpr
  simpa only [coe_cosmicEmbed_eq_cosmicScale_smul,
    coe_cosmicDirection] using hcanonical

/-- Direction-point clause of **Definition 3.1** in the closed-ball model:
cosmic convergence to `u` is equivalent to the existence of positive
vanishing scalars whose rescaled vectors converge to `u`. -/
theorem tendsto_cosmicEmbed_cosmicDirection_iff
    {x : ℕ → E} {u : CosmicBoundary E} :
    Tendsto (fun n ↦ cosmicEmbed (x n)) atTop
        (𝓝 (cosmicDirection u)) ↔
      ∃ scale : ℕ → ℝ, (∀ n, 0 < scale n) ∧
        Tendsto scale atTop (𝓝 0) ∧
        Tendsto (fun n ↦ scale n • x n) atTop (𝓝 (u : E)) := by
  constructor
  · exact exists_scaling_of_tendsto_cosmicDirection
  · rintro ⟨scale, hpos, hscale, hscaled⟩
    exact tendsto_cosmicDirection_of_scaling hpos hscale hscaled

/-- Direction-point-to-direction-point clause of **Definition 3.1** in the
closed-ball model.  Unit vectors are canonical representatives of direction
points, so convergence in the boundary sphere is precisely convergence after
some positive rescaling. -/
theorem tendsto_cosmicDirection_iff_exists_scaling
    {u : ℕ → CosmicBoundary E} {u₀ : CosmicBoundary E} :
    Tendsto (fun n ↦ cosmicDirection (u n)) atTop
        (𝓝 (cosmicDirection u₀)) ↔
      ∃ scale : ℕ → ℝ, (∀ n, 0 < scale n) ∧
        Tendsto (fun n ↦ scale n • (u n : E)) atTop (𝓝 (u₀ : E)) := by
  constructor
  · intro h
    refine ⟨fun _ ↦ 1, fun _ ↦ zero_lt_one, ?_⟩
    simpa only [one_smul, coe_cosmicDirection] using
      tendsto_subtype_rng.mp h
  · rintro ⟨scale, hscale_pos, hscaled⟩
    have hscale :
        Tendsto scale atTop (𝓝 1) := by
      have hnorm :=
        hscaled.norm
      simpa only [norm_smul, Real.norm_eq_abs,
        abs_of_pos (hscale_pos _), mem_sphere_zero_iff_norm.mp (u _).property,
        mul_one, mem_sphere_zero_iff_norm.mp u₀.property] using hnorm
    have hinv :
        Tendsto (fun n ↦ (scale n)⁻¹) atTop (𝓝 1) := by
      simpa using hscale.inv₀ one_ne_zero
    have hu :
        Tendsto (fun n ↦ (u n : E)) atTop (𝓝 (u₀ : E)) := by
      have hrescaled :
          Tendsto
            (fun n ↦ (scale n)⁻¹ • (scale n • (u n : E)))
            atTop (𝓝 (u₀ : E)) := by
        simpa only [one_smul] using hinv.smul hscaled
      exact hrescaled.congr' (Eventually.of_forall fun n ↦ by
        rw [smul_smul, inv_mul_cancel₀ (hscale_pos n).ne', one_smul])
    apply tendsto_subtype_rng.mpr
    simpa only [coe_cosmicDirection] using hu

/-- Ordinary points are dense in the ambient closed-ball carrier. -/
theorem closure_range_coe_cosmicEmbed :
    closure (Set.range (fun x : E ↦ ((cosmicEmbed x : CosmicSpace E) : E))) =
      closedBall (0 : E) 1 := by
  rw [range_coe_cosmicEmbed, closure_ball (0 : E) one_ne_zero]

/-- The unit vector representing the positive ray through a nonzero vector. -/
noncomputable def cosmicDirectionOf (x : E) (hx : x ≠ 0) : CosmicBoundary E :=
  ⟨NormedSpace.normalize x,
    mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize hx)⟩

@[simp]
theorem coe_cosmicDirectionOf (x : E) (hx : x ≠ 0) :
    ((cosmicDirectionOf x hx : CosmicBoundary E) : E) =
      NormedSpace.normalize x := by
  rfl

/-- Positive rescaling does not change the represented cosmic direction. -/
theorem cosmicDirectionOf_smul_of_pos (x : E) (hx : x ≠ 0) {r : ℝ}
    (hr : 0 < r) :
    cosmicDirectionOf (r • x) (smul_ne_zero hr.ne' hx) =
      cosmicDirectionOf x hx := by
  apply Subtype.ext
  exact NormedSpace.normalize_smul_of_pos hr x

/-- A scalar in `[0, 1)` tending to `1`, used to approach the cosmic boundary
radially. -/
noncomputable def cosmicRadialCoefficient (n : ℕ) : ℝ :=
  1 - (((n + 1 : ℕ) : ℝ))⁻¹

theorem cosmicRadialCoefficient_nonneg (n : ℕ) :
    0 ≤ cosmicRadialCoefficient n := by
  have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  simp only [cosmicRadialCoefficient]
  exact sub_nonneg.mpr ((inv_le_one₀ (by positivity : (0 : ℝ) <
    ((n + 1 : ℕ) : ℝ))).mpr hn)

theorem cosmicRadialCoefficient_lt_one (n : ℕ) :
    cosmicRadialCoefficient n < 1 := by
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  simp only [cosmicRadialCoefficient]
  linarith [inv_pos.mpr hn]

theorem tendsto_cosmicRadialCoefficient :
    Tendsto cosmicRadialCoefficient atTop (𝓝 1) := by
  have hinv :
      Tendsto (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) := by
    convert
      (tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).comp
        (tendsto_add_atTop_nat 1) using 1
  simpa only [cosmicRadialCoefficient, sub_zero] using
    tendsto_const_nhds.sub hinv

/-- The open-ball point at radial coefficient `cosmicRadialCoefficient n`. -/
noncomputable def cosmicRadialInterior (u : CosmicBoundary E) (n : ℕ) :
    CosmicInterior E :=
  ⟨cosmicRadialCoefficient n • (u : E), by
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (cosmicRadialCoefficient_nonneg n),
      mem_sphere_zero_iff_norm.mp u.property, mul_one]
    exact cosmicRadialCoefficient_lt_one n⟩

/-- An ordinary point whose image approaches the direction `u` radially. -/
noncomputable def cosmicRadialOrdinary (u : CosmicBoundary E) (n : ℕ) : E :=
  (cosmicInteriorHomeomorph (E := E)).symm (cosmicRadialInterior u n)

@[simp]
theorem coe_cosmicEmbed_cosmicRadialOrdinary (u : CosmicBoundary E) (n : ℕ) :
    ((cosmicEmbed (cosmicRadialOrdinary u n) : CosmicSpace E) : E) =
      cosmicRadialCoefficient n • (u : E) := by
  change
    (((cosmicInteriorHomeomorph (E := E))
      ((cosmicInteriorHomeomorph (E := E)).symm
        (cosmicRadialInterior u n)) : CosmicInterior E) : E) =
      cosmicRadialCoefficient n • (u : E)
  simp [cosmicRadialInterior]

/-- Every direction point is a limit of ordinary points in the cosmic
compactification. -/
theorem tendsto_cosmicRadialOrdinary (u : CosmicBoundary E) :
    Tendsto (fun n ↦ cosmicEmbed (cosmicRadialOrdinary u n))
      atTop (𝓝 (cosmicDirection u)) := by
  apply tendsto_subtype_rng.mpr
  simpa only [coe_cosmicEmbed_cosmicRadialOrdinary, coe_cosmicDirection,
    one_smul] using tendsto_cosmicRadialCoefficient.smul_const (u : E)

omit [NormedSpace ℝ E] in
/-- A sequence whose `n`th norm exceeds `n` has unbounded range. -/
private theorem not_isBounded_range_of_nat_lt_norm
    {x : ℕ → E} (hx : ∀ n : ℕ, (n : ℝ) < ‖x n‖) :
    ¬ IsBounded (Set.range x) := by
  intro hbounded
  obtain ⟨R, hR⟩ := hbounded.exists_norm_le
  obtain ⟨n, hn⟩ := exists_nat_gt R
  have hupper : ‖x n‖ ≤ R := hR (x n) (Set.mem_range_self n)
  exact (not_lt_of_ge (hupper.trans hn.le)) (hx n)

omit [NormedSpace ℝ E] in
/-- Every unbounded sequence has a genuine subsequence whose norms escape
past the natural-number scale. -/
private theorem exists_strictMono_norm_escaping
    {x : ℕ → E} (hx : ¬ IsBounded (Set.range x)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ n : ℕ, (n : ℝ) < ‖x (φ n)‖ := by
  have htail :
      ∀ N n : ℕ, ∃ k : ℕ, N ≤ k ∧ (n : ℝ) < ‖x k‖ := by
    intro N n
    by_contra h
    push_neg at h
    apply hx
    rw [isBounded_iff_forall_norm_le]
    refine
      ⟨max (n : ℝ) ((Finset.range N).sum fun k ↦ ‖x k‖), ?_⟩
    rintro _ ⟨k, rfl⟩
    by_cases hk : k < N
    · have hterm :
          ‖x k‖ ≤ (Finset.range N).sum fun i ↦ ‖x i‖ :=
        Finset.single_le_sum
          (fun i _ ↦ norm_nonneg (x i)) (Finset.mem_range.mpr hk)
      exact hterm.trans (le_max_right _ _)
    · exact (h k (Nat.le_of_not_gt hk)).trans (le_max_left _ _)
  let pick : ℕ → ℕ → ℕ :=
    fun N n ↦ Classical.choose (htail N n)
  have hpick_index (N n : ℕ) : N ≤ pick N n :=
    (Classical.choose_spec (htail N n)).1
  have hpick_norm (N n : ℕ) : (n : ℝ) < ‖x (pick N n)‖ :=
    (Classical.choose_spec (htail N n)).2
  let φ : ℕ → ℕ :=
    fun n ↦ Nat.rec (pick 0 0)
      (fun j k ↦ pick (k + 1) (j + 1)) n
  have hφ_succ (n : ℕ) :
      φ (n + 1) = pick (φ n + 1) (n + 1) := by
    simp [φ]
  have hφ_step (n : ℕ) : φ n < φ (n + 1) := by
    rw [hφ_succ]
    exact Nat.lt_of_succ_le (hpick_index (φ n + 1) (n + 1))
  refine ⟨φ, strictMono_nat_of_lt_succ hφ_step, ?_⟩
  intro n
  cases n with
  | zero =>
      simpa [φ] using hpick_norm 0 0
  | succ n =>
      rw [hφ_succ]
      exact hpick_norm (φ n + 1) (n + 1)

/-- In finite dimension the closed-ball model of cosmic space is compact. -/
theorem isCompact_cosmicSpace [FiniteDimensional ℝ E] :
    IsCompact (closedBall (0 : E) 1) :=
  isCompact_closedBall _ _

/-- **Theorem 3.2 (sequential compactness, closed-ball model).** Every
sequence of cosmic points, including mixed ordinary and direction points,
admits a convergent subsequence. -/
theorem exists_cosmicSpace_convergent_subsequence [FiniteDimensional ℝ E]
    (p : ℕ → CosmicSpace E) :
    ∃ (q : CosmicSpace E) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (p ∘ φ) atTop (𝓝 q) := by
  letI : CompactSpace (CosmicSpace E) :=
    isCompact_iff_compactSpace.mp (isCompact_cosmicSpace (E := E))
  exact CompactSpace.tendsto_subseq p

/-- Specialization of cosmic sequential compactness to a sequence of
ordinary points. -/
theorem exists_cosmic_convergent_subsequence [FiniteDimensional ℝ E]
    (x : ℕ → E) :
    ∃ (p : CosmicSpace E) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto ((fun n ↦ cosmicEmbed (x n)) ∘ φ) atTop (𝓝 p) := by
  exact exists_cosmicSpace_convergent_subsequence
    (fun n ↦ cosmicEmbed (x n))

/-- A convergent cosmic subsequence has either an ordinary limit or a
direction limit. -/
theorem exists_cosmic_subsequence_with_classified_limit
    [FiniteDimensional ℝ E] (x : ℕ → E) :
    ∃ (p : CosmicSpace E) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto ((fun n ↦ cosmicEmbed (x n)) ∘ φ) atTop (𝓝 p) ∧
      ((∃ y : E, cosmicEmbed y = p) ∨
        (∃ u : CosmicBoundary E, cosmicDirection u = p)) := by
  rcases exists_cosmic_convergent_subsequence x with ⟨p, φ, hφ, hp⟩
  exact ⟨p, φ, hφ, hp, cosmicEmbed_or_cosmicDirection p⟩

/-- An unbounded sequence of ordinary points has a subsequence converging
to a direction point in cosmic space. -/
theorem exists_cosmicDirection_subsequence_of_not_isBounded
    [FiniteDimensional ℝ E] {x : ℕ → E}
    (hx : ¬ IsBounded (Set.range x)) :
    ∃ (u : CosmicBoundary E) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun n ↦ cosmicEmbed (x (φ n))) atTop
        (𝓝 (cosmicDirection u)) := by
  rcases exists_strictMono_norm_escaping hx with
    ⟨φ, hφ, hφnorm⟩
  rcases exists_cosmic_subsequence_with_classified_limit (x ∘ φ) with
    ⟨p, ψ, hψ, hp, hpclass⟩
  rcases hpclass with ⟨x₀, hx₀⟩ | ⟨u, hu⟩
  · have hord :
        Tendsto ((x ∘ φ) ∘ ψ) atTop (𝓝 x₀) := by
      apply (tendsto_cosmicEmbed_iff (x₀ := x₀)).mp
      simpa only [Function.comp_apply, hx₀] using hp
    have hbounded :
        IsBounded (Set.range ((x ∘ φ) ∘ ψ)) :=
      Metric.isBounded_range_of_tendsto _ hord
    have hlarge :
        ∀ n : ℕ, (n : ℝ) < ‖((x ∘ φ) ∘ ψ) n‖ := by
      intro n
      have hnψ : (n : ℝ) ≤ (ψ n : ℝ) := by
        exact_mod_cast hψ.id_le n
      exact hnψ.trans_lt (hφnorm (ψ n))
    exact (not_isBounded_range_of_nat_lt_norm hlarge hbounded).elim
  · refine ⟨u, φ ∘ ψ, hφ.comp hψ, ?_⟩
    simpa only [Function.comp_apply, hu] using hp

/-- **Theorem 3.2 (bounded-sequence characterization).** A sequence in the
ordinary space is bounded exactly when none of its cosmic cluster points is
a direction point. -/
theorem isBounded_range_iff_no_cosmicDirection_cluster
    [FiniteDimensional ℝ E] (x : ℕ → E) :
    IsBounded (Set.range x) ↔
      ∀ u : CosmicBoundary E,
        ¬ MapClusterPt (cosmicDirection u) atTop
          (fun n ↦ cosmicEmbed (x n)) := by
  constructor
  · intro hx u hu
    rcases TopologicalSpace.FirstCountableTopology.tendsto_subseq hu with
      ⟨φ, hφ, hsub⟩
    have hsub' :
        Tendsto (fun n ↦ cosmicEmbed (x (φ n))) atTop
          (𝓝 (cosmicDirection u)) := by
      simpa only [Function.comp_apply] using hsub
    rcases exists_scaling_of_tendsto_cosmicDirection hsub' with
      ⟨scale, -, hscale, hscaled⟩
    have hxφ : IsBounded (Set.range (x ∘ φ)) :=
      hx.subset <| by
        rintro _ ⟨n, rfl⟩
        exact ⟨φ n, rfl⟩
    obtain ⟨R, hR⟩ := hxφ.exists_norm_le
    have hnorm_bdd :
        BddAbove (Set.range (norm ∘ (x ∘ φ))) := by
      refine ⟨R, ?_⟩
      rintro _ ⟨n, rfl⟩
      exact hR ((x ∘ φ) n) (Set.mem_range_self n)
    have hzero :
        Tendsto (fun n ↦ scale n • x (φ n)) atTop (𝓝 0) := by
      simpa only [Pi.smul_apply, Function.comp_apply] using
        NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded
          hscale hnorm_bdd.isBoundedUnder_of_range
    have hu0 : (u : E) = 0 :=
      tendsto_nhds_unique hscaled hzero
    have hunorm : ‖(u : E)‖ = 1 :=
      mem_sphere_zero_iff_norm.mp u.property
    simp [hu0] at hunorm
  · intro hno
    by_contra hx
    rcases exists_cosmicDirection_subsequence_of_not_isBounded hx with
      ⟨u, φ, hφ, hsub⟩
    apply hno u
    have hsub' :
        Tendsto
          ((fun n ↦ cosmicEmbed (x n)) ∘ φ) atTop
          (𝓝 (cosmicDirection u)) := by
      simpa only [Function.comp_apply] using hsub
    exact MapClusterPt.of_comp hφ.tendsto_atTop hsub'.mapClusterPt

end CosmicSpace

end RW
