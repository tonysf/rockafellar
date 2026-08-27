/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Horizon Limits

The horizon inner and outer limits from formula 4(6), represented through
the direction part of the closed-ball cosmic compactification.
-/

import RockafellarWets.Chapter3.CosmicSetClosure
import RockafellarWets.Chapter4.ClusterLimits
import RockafellarWets.Chapter4.ConeLimits

open Filter Function Metric Set Topology

namespace RW

section DirectionConeLemmas

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Unit representatives detect membership in the direction cone. -/
theorem cosmicDirection_mem_iff_mem_cosmicDirectionCone
    {S : Set (CosmicSpace E)} {u : CosmicBoundary E} :
    cosmicDirection u ∈ S ↔ (u : E) ∈ cosmicDirectionCone S := by
  constructor
  · intro hu
    right
    exact ⟨u, hu, 1, zero_lt_one, by simp⟩
  · rintro (hu0 | ⟨v, hvS, r, hr, huv⟩)
    · have hunorm : ‖(u : E)‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
      simp [hu0] at hunorm
    · have hunorm : ‖(u : E)‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
      have hvnorm : ‖(v : E)‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
      have hrOne : r = 1 := by
        have hnorm := congrArg norm huv
        rw [hunorm, norm_smul, Real.norm_eq_abs, abs_of_pos hr, hvnorm, mul_one] at hnorm
        linarith
      have huv' : u = v := by
        apply Subtype.ext
        simpa [hrOne] using huv
      simpa [huv'] using hvS

/-- The direction cone of a closed cosmic set is closed. -/
theorem IsClosed.isClosed_cosmicDirectionCone [FiniteDimensional ℝ E]
    {S : Set (CosmicSpace E)} (hS : IsClosed S) :
    IsClosed (cosmicDirectionCone S) := by
  have hparts : IsClosed
      (cosmicSet (cosmicOrdinaryPart S) (cosmicDirectionCone S)) := by
    simpa only [cosmicSet_parts] using hS
  exact ((isClosed_cosmicSet_iff (isCone_cosmicDirectionCone S)).1 hparts).2.1

end DirectionConeLemmas

section Definitions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The sequence of ordinary sets viewed in cosmic space, with no direction
points inserted beforehand. -/
noncomputable def ordinaryCosmicSequence (C : ℕ → Set E) :
    ℕ → Set (CosmicSpace E) :=
  fun n ↦ cosmicSet (C n) ({0} : Set E)

/-- Formula 4(6), outer form: the cone represented by direction points in
the cosmic outer limit. -/
noncomputable def horizonOuterSetLimit (C : ℕ → Set E) : Set E :=
  cosmicDirectionCone (outerSetLimit (ordinaryCosmicSequence C))

/-- Formula 4(6), inner form: the cone represented by direction points in
the cosmic inner limit. -/
noncomputable def horizonInnerSetLimit (C : ℕ → Set E) : Set E :=
  cosmicDirectionCone (innerSetLimit (ordinaryCosmicSequence C))

/-- The horizon limit exists with value `K` when its inner and outer limits
both equal `K`. -/
def HorizonConverges (C : ℕ → Set E) (K : Set E) : Prop :=
  horizonInnerSetLimit C = K ∧ horizonOuterSetLimit C = K

@[simp]
theorem cosmicDirection_mem_outer_ordinaryCosmicSequence_iff
    {C : ℕ → Set E} {u : CosmicBoundary E} :
    cosmicDirection u ∈ outerSetLimit (ordinaryCosmicSequence C) ↔
      (u : E) ∈ horizonOuterSetLimit C := by
  exact cosmicDirection_mem_iff_mem_cosmicDirectionCone

@[simp]
theorem cosmicDirection_mem_inner_ordinaryCosmicSequence_iff
    {C : ℕ → Set E} {u : CosmicBoundary E} :
    cosmicDirection u ∈ innerSetLimit (ordinaryCosmicSequence C) ↔
      (u : E) ∈ horizonInnerSetLimit C := by
  exact cosmicDirection_mem_iff_mem_cosmicDirectionCone

theorem isCone_horizonOuterSetLimit (C : ℕ → Set E) :
    IsCone (horizonOuterSetLimit C) :=
  isCone_cosmicDirectionCone _

theorem isCone_horizonInnerSetLimit (C : ℕ → Set E) :
    IsCone (horizonInnerSetLimit C) :=
  isCone_cosmicDirectionCone _

theorem isClosed_horizonOuterSetLimit [FiniteDimensional ℝ E]
    (C : ℕ → Set E) : IsClosed (horizonOuterSetLimit C) :=
  IsClosed.isClosed_cosmicDirectionCone (isClosed_outerSetLimit _)

theorem isClosed_horizonInnerSetLimit [FiniteDimensional ℝ E]
    (C : ℕ → Set E) : IsClosed (horizonInnerSetLimit C) :=
  IsClosed.isClosed_cosmicDirectionCone (isClosed_innerSetLimit _)

end Definitions

section Properties

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mem_innerSetLimit_iff_forall_subsequence_outerSetLimit
    {X : Type*} [PseudoMetricSpace X] {A : ℕ → Set X} {x : X} :
    x ∈ innerSetLimit A ↔
      ∀ (φ : ℕ → ℕ), StrictMono φ → x ∈ outerSetLimit (A ∘ φ) := by
  constructor
  · intro hx φ hφ
    exact innerSetLimit_subset_outerSetLimit _
      (innerSetLimit_subset_subsequence hφ hx)
  · intro hx
    by_contra hnot
    simp only [mem_innerSetLimit] at hnot
    push_neg at hnot
    rcases hnot with ⟨V, hV, hmiss⟩
    rcases extraction_of_frequently_atTop hmiss with ⟨φ, hφ, hφmiss⟩
    rcases (hx φ hφ V hV).exists with ⟨n, hn⟩
    have hn' : (A (φ n) ∩ V).Nonempty := hn
    rw [hφmiss n] at hn'
    exact Set.not_nonempty_empty hn'

/-- Ordinary points in a cosmic outer limit are exactly the ordinary outer
limit points. -/
theorem cosmicEmbed_mem_outer_ordinaryCosmicSequence_iff {C : ℕ → Set E}
    {x : E} :
    cosmicEmbed x ∈ outerSetLimit (ordinaryCosmicSequence C) ↔
      x ∈ outerSetLimit C := by
  constructor
  · intro hx
    rcases mem_outerSetLimit_iff_exists_subsequence.1 hx with
      ⟨φ, z, hφ, hz, hzx⟩
    have hz' : ∀ n, z n ∈ cosmicEmbed '' C (φ n) := by
      intro n
      simpa only [ordinaryCosmicSequence, cosmicSet, cosmicDirections_zero,
        union_empty] using hz n
    choose y hyC hyz using hz'
    have hyx : Tendsto y atTop (nhds x) := by
      apply tendsto_cosmicEmbed_iff.1
      apply hzx.congr'
      exact Eventually.of_forall fun n ↦ (hyz n).symm
    exact mem_outerSetLimit_iff_exists_subsequence.2 ⟨φ, y, hφ, hyC, hyx⟩
  · intro hx
    rcases mem_outerSetLimit_iff_exists_subsequence.1 hx with
      ⟨φ, y, hφ, hyC, hyx⟩
    apply mem_outerSetLimit_iff_exists_subsequence.2
    refine ⟨φ, fun n ↦ cosmicEmbed (y n), hφ, ?_, ?_⟩
    · intro n
      exact (cosmicEmbed_mem_cosmicSet_iff).2 (hyC n)
    · exact tendsto_cosmicEmbed_iff.2 hyx

/-- Ordinary points in a cosmic inner limit are exactly the ordinary inner
limit points. -/
theorem cosmicEmbed_mem_inner_ordinaryCosmicSequence_iff {C : ℕ → Set E}
    {x : E} :
    cosmicEmbed x ∈ innerSetLimit (ordinaryCosmicSequence C) ↔
      x ∈ innerSetLimit C := by
  rw [mem_innerSetLimit_iff_forall_subsequence_outerSetLimit,
    mem_innerSetLimit_iff_forall_subsequence_outerSetLimit]
  constructor <;> intro h φ hφ
  · exact cosmicEmbed_mem_outer_ordinaryCosmicSequence_iff.1 <| by
      simpa only [ordinaryCosmicSequence, Function.comp_def] using h φ hφ
  · apply cosmicEmbed_mem_outer_ordinaryCosmicSequence_iff.2
    simpa only [ordinaryCosmicSequence, Function.comp_def] using h φ hφ

/-- Exercise 4.20 for ordinary cosmic sets: the cosmic outer limit splits
into the ordinary outer limit and the horizon outer limit. -/
theorem outerSetLimit_ordinaryCosmicSequence (C : ℕ → Set E) :
    outerSetLimit (ordinaryCosmicSequence C) =
      cosmicSet (outerSetLimit C) (horizonOuterSetLimit C) := by
  calc
    outerSetLimit (ordinaryCosmicSequence C) =
        cosmicSet
          (cosmicOrdinaryPart (outerSetLimit (ordinaryCosmicSequence C)))
          (cosmicDirectionCone (outerSetLimit (ordinaryCosmicSequence C))) :=
      (cosmicSet_parts _).symm
    _ = cosmicSet (outerSetLimit C) (horizonOuterSetLimit C) := by
      congr 2
      ext x
      exact cosmicEmbed_mem_outer_ordinaryCosmicSequence_iff

/-- Exercise 4.20 for ordinary cosmic sets: the cosmic inner limit splits
into the ordinary inner limit and the horizon inner limit. -/
theorem innerSetLimit_ordinaryCosmicSequence (C : ℕ → Set E) :
    innerSetLimit (ordinaryCosmicSequence C) =
      cosmicSet (innerSetLimit C) (horizonInnerSetLimit C) := by
  calc
    innerSetLimit (ordinaryCosmicSequence C) =
        cosmicSet
          (cosmicOrdinaryPart (innerSetLimit (ordinaryCosmicSequence C)))
          (cosmicDirectionCone (innerSetLimit (ordinaryCosmicSequence C))) :=
      (cosmicSet_parts _).symm
    _ = cosmicSet (innerSetLimit C) (horizonInnerSetLimit C) := by
      congr 2
      ext x
      exact cosmicEmbed_mem_inner_ordinaryCosmicSequence_iff

/-- Exercise 4.21(a). -/
theorem horizonInnerSetLimit_subset_horizonOuterSetLimit (C : ℕ → Set E) :
    horizonInnerSetLimit C ⊆ horizonOuterSetLimit C :=
  cosmicDirectionCone_mono (innerSetLimit_subset_outerSetLimit _)

/-- Horizon inner limits are monotone under passage to subsequences. -/
theorem horizonInnerSetLimit_subset_subsequence {C : ℕ → Set E} {φ : ℕ → ℕ}
    (hφ : StrictMono φ) :
    horizonInnerSetLimit C ⊆ horizonInnerSetLimit (C ∘ φ) := by
  apply cosmicDirectionCone_mono
  simpa only [ordinaryCosmicSequence, Function.comp_def] using
    (innerSetLimit_subset_subsequence
      (C := ordinaryCosmicSequence C) hφ)

/-- Horizon outer limits shrink under passage to subsequences. -/
theorem horizonOuterSetLimit_subsequence_subset {C : ℕ → Set E} {φ : ℕ → ℕ}
    (hφ : StrictMono φ) :
    horizonOuterSetLimit (C ∘ φ) ⊆ horizonOuterSetLimit C := by
  apply cosmicDirectionCone_mono
  simpa only [ordinaryCosmicSequence, Function.comp_def] using
    (outerSetLimit_subsequence_subset
      (C := ordinaryCosmicSequence C) hφ)

/-- Exercise 4.21(c). If the ordinary inner limit contains `C`, then its
horizon cone is contained in the horizon inner limit. -/
theorem horizonCone_subset_horizonInnerSetLimit [FiniteDimensional ℝ E]
    {Cseq : ℕ → Set E} {C : Set E} (hC : C ⊆ innerSetLimit Cseq) :
    horizonCone C ⊆ horizonInnerSetLimit Cseq := by
  have hraw : cosmicSet C ({0} : Set E) ⊆
      innerSetLimit (ordinaryCosmicSequence Cseq) := by
    intro p hp
    rw [mem_cosmicSet] at hp
    rcases hp with ⟨x, hx, rfl⟩ | ⟨u, hu0, rfl⟩
    · exact cosmicEmbed_mem_inner_ordinaryCosmicSequence_iff.2 (hC hx)
    · have huZero : (u : E) = 0 := by simpa using hu0
      have huNorm : ‖(u : E)‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
      simp [huZero] at huNorm
  have hclosure : closure (cosmicSet C ({0} : Set E)) ⊆
      innerSetLimit (ordinaryCosmicSequence Cseq) :=
    closure_minimal hraw (isClosed_innerSetLimit _)
  intro w hw
  by_cases hw0 : w = 0
  · simpa [hw0] using (isCone_horizonInnerSetLimit Cseq).1
  · let u : CosmicBoundary E := cosmicDirectionOf w hw0
    have huHor : (u : E) ∈ horizonCone C := by
      change NormedSpace.normalize w ∈ horizonCone C
      exact (isCone_horizonCone C).smul_mem hw
        (inv_nonneg.mpr (norm_nonneg w))
    have huClosure : cosmicDirection u ∈
        closure (cosmicSet C ({0} : Set E)) :=
      cosmicDirection_mem_closure_cosmicSet_of_mem_horizonCone huHor
    have huInner : (u : E) ∈ horizonInnerSetLimit Cseq :=
      cosmicDirection_mem_inner_ordinaryCosmicSequence_iff.1 (hclosure huClosure)
    have hscaled := (isCone_horizonInnerSetLimit Cseq).smul_mem huInner
      (norm_nonneg w)
    simpa only [u, coe_cosmicDirectionOf,
      NormedSpace.norm_smul_normalize w] using hscaled

/-- Exercise 4.21: horizon outer limits depend only on the termwise
closures. -/
theorem horizonOuterSetLimit_closure [FiniteDimensional ℝ E]
    (C : ℕ → Set E) :
    horizonOuterSetLimit (fun n ↦ closure (C n)) = horizonOuterSetLimit C := by
  have hzero : IsCone ({0} : Set E) := ⟨by simp, by simp⟩
  apply congrArg cosmicDirectionCone
  rw [← outerSetLimit_closure
      (ordinaryCosmicSequence (fun n ↦ closure (C n))),
    ← outerSetLimit_closure (ordinaryCosmicSequence C)]
  congr 1
  funext n
  unfold ordinaryCosmicSequence
  rw [closure_cosmicSet hzero, closure_cosmicSet hzero,
    closure_closure, horizonCone_closure]

/-- Exercise 4.21: horizon inner limits depend only on the termwise
closures. -/
theorem horizonInnerSetLimit_closure [FiniteDimensional ℝ E]
    (C : ℕ → Set E) :
    horizonInnerSetLimit (fun n ↦ closure (C n)) = horizonInnerSetLimit C := by
  have hzero : IsCone ({0} : Set E) := ⟨by simp, by simp⟩
  apply congrArg cosmicDirectionCone
  rw [← innerSetLimit_closure
      (ordinaryCosmicSequence (fun n ↦ closure (C n))),
    ← innerSetLimit_closure (ordinaryCosmicSequence C)]
  congr 1
  funext n
  unfold ordinaryCosmicSequence
  rw [closure_cosmicSet hzero, closure_cosmicSet hzero,
    closure_closure, horizonCone_closure]

/-- Exercise 4.21(d), outer half. -/
theorem horizonOuterSetLimit_const [FiniteDimensional ℝ E] (C : Set E) :
    horizonOuterSetLimit (fun _ : ℕ ↦ C) = horizonCone C := by
  have hzero : IsCone ({0} : Set E) := ⟨by simp, by simp⟩
  unfold horizonOuterSetLimit ordinaryCosmicSequence
  rw [outerSetLimit_const, closure_cosmicSet hzero]
  rw [closure_singleton]
  rw [Set.union_eq_left.mpr (Set.singleton_subset_iff.mpr (zero_mem_horizonCone C))]
  exact cosmicDirectionCone_cosmicSet (isCone_horizonCone C)

/-- Exercise 4.21(d), inner half. -/
theorem horizonInnerSetLimit_const [FiniteDimensional ℝ E] (C : Set E) :
    horizonInnerSetLimit (fun _ : ℕ ↦ C) = horizonCone C := by
  have hzero : IsCone ({0} : Set E) := ⟨by simp, by simp⟩
  unfold horizonInnerSetLimit ordinaryCosmicSequence
  rw [innerSetLimit_const, closure_cosmicSet hzero]
  rw [closure_singleton]
  rw [Set.union_eq_left.mpr (Set.singleton_subset_iff.mpr (zero_mem_horizonCone C))]
  exact cosmicDirectionCone_cosmicSet (isCone_horizonCone C)

/-- Exercise 4.21(d): a constant sequence has horizon limit `C∞`. -/
theorem horizonConverges_const [FiniteDimensional ℝ E] (C : Set E) :
    HorizonConverges (fun _ : ℕ ↦ C) (horizonCone C) :=
  ⟨horizonInnerSetLimit_const C, horizonOuterSetLimit_const C⟩

end Properties

end RW
