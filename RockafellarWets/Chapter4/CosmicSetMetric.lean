/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: The Cosmic Set Metric

This file implements 4(14) through Theorem 4.46 using the equivalent
unit-ball truncation of the ray-space cone from Example 4.44.  This backend is
independent of the still-developing integrated-distance API.
-/

import Mathlib.Topology.UniformSpace.HeineCantor
import RockafellarWets.Chapter4.ConvexTruncations
import RockafellarWets.Chapter4.CosmicPointMetric

open Filter Metric Set Topology

namespace RW

section CosmicSetMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

local instance : CompactSpace (CosmicSpace E) :=
  isCompact_iff_compactSpace.mp (isCompact_cosmicSpace (E := E))

/-- A closed cosmic set, regarded as a compact set in the closed-ball model. -/
noncomputable def cosmicClosedCompact
    (S : TopologicalSpace.Closeds (CosmicSpace E)) :
    TopologicalSpace.Compacts (CosmicSpace E) where
  carrier := S
  isCompact' := S.isClosed.isCompact

theorem isometry_cosmicClosedCompact :
    Isometry (cosmicClosedCompact :
      TopologicalSpace.Closeds (CosmicSpace E) →
        TopologicalSpace.Compacts (CosmicSpace E)) := by
  intro S T
  rfl

/-- The compact parameter interval `[0,1]`. -/
noncomputable def cosmicScaleParameters :
    TopologicalSpace.Compacts (Set.Icc (0 : ℝ) 1) :=
  ⟨Set.univ, isCompact_univ⟩

/-- Scale a cosmic unit-ray representative by a parameter in `[0,1]`. -/
noncomputable def cosmicRayScale
    (z : Set.Icc (0 : ℝ) 1 × CosmicSpace E) : CosmicRayAmbient E :=
  (z.1 : ℝ) • cosmicRayRepresentative z.2

omit [FiniteDimensional ℝ E] in
theorem continuous_cosmicRayScale :
    Continuous (cosmicRayScale :
      Set.Icc (0 : ℝ) 1 × CosmicSpace E → CosmicRayAmbient E) := by
  have ht : Continuous (fun z : Set.Icc (0 : ℝ) 1 × CosmicSpace E ↦ (z.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hp : Continuous (fun z : Set.Icc (0 : ℝ) 1 × CosmicSpace E ↦
      cosmicRayRepresentative z.2) :=
    continuous_cosmicRayRepresentative.comp continuous_snd
  exact ht.smul hp

/-- The union of unit ray segments associated with a closed cosmic set. -/
noncomputable def cosmicScaledRays
    (S : TopologicalSpace.Closeds (CosmicSpace E)) :
    TopologicalSpace.Compacts (CosmicRayAmbient E) :=
  TopologicalSpace.Compacts.map cosmicRayScale continuous_cosmicRayScale
    (cosmicScaleParameters ×ˢ cosmicClosedCompact S)

/-- The compact truncation of the ray-space cone.  The origin is inserted
explicitly, so the empty cosmic set is represented by `{0}`. -/
noncomputable def cosmicConeTruncationCompacts
    (S : TopologicalSpace.Closeds (CosmicSpace E)) :
    TopologicalSpace.Compacts (CosmicRayAmbient E) :=
  cosmicScaledRays S ⊔ {(0 : CosmicRayAmbient E)}

/-- The nonempty-compact packaging of the truncated ray-space cone. -/
noncomputable def cosmicConeTruncation
    (S : TopologicalSpace.Closeds (CosmicSpace E)) :
    TopologicalSpace.NonemptyCompacts (CosmicRayAmbient E) where
  toCompacts := cosmicConeTruncationCompacts S
  nonempty' := by
    refine ⟨0, ?_⟩
    simp [cosmicConeTruncationCompacts]

theorem mem_cosmicConeTruncation_iff
    {S : TopologicalSpace.Closeds (CosmicSpace E)}
    {z : CosmicRayAmbient E} :
    z ∈ cosmicConeTruncation S ↔
      z = 0 ∨ ∃ p : CosmicSpace E, p ∈ S ∧
        ∃ t : ℝ, t ∈ Set.Icc 0 1 ∧ z = t • cosmicRayRepresentative p := by
  change z ∈
      (cosmicRayScale '' ((Set.univ : Set (Set.Icc (0 : ℝ) 1)) ×ˢ
        (S : Set (CosmicSpace E))) ∪ {0}) ↔ _
  rw [mem_union, mem_singleton_iff]
  constructor
  · rintro (⟨⟨⟨t, ht⟩, p⟩, ⟨-, hp⟩, rfl⟩ | rfl)
    · exact Or.inr ⟨p, hp, t, ht, rfl⟩
    · exact Or.inl rfl
  · rintro (rfl | ⟨p, hp, t, ht, rfl⟩)
    · exact Or.inr rfl
    · exact Or.inl ⟨⟨⟨t, ht⟩, p⟩, ⟨mem_univ _, hp⟩, rfl⟩

theorem continuous_cosmicConeTruncation :
    Continuous (fun S : TopologicalSpace.Closeds (CosmicSpace E) ↦
      cosmicConeTruncation S) := by
  apply TopologicalSpace.NonemptyCompacts.isUniformEmbedding_toCompacts.isInducing.continuous_iff.2
  change Continuous (fun S : TopologicalSpace.Closeds (CosmicSpace E) ↦
    cosmicConeTruncationCompacts S)
  have hscaled : Continuous (fun S : TopologicalSpace.Closeds (CosmicSpace E) ↦
      cosmicScaledRays S) := by
    have hprod : Continuous (fun S : TopologicalSpace.Closeds (CosmicSpace E) ↦
        cosmicScaleParameters ×ˢ cosmicClosedCompact S) :=
      (TopologicalSpace.Compacts.lipschitz_prod
        (α := Set.Icc (0 : ℝ) 1) (β := CosmicSpace E)).continuous.comp
          (continuous_const.prodMk isometry_cosmicClosedCompact.continuous)
    apply (CompactSpace.uniformContinuous_of_continuous
      continuous_cosmicRayScale).compacts_map.continuous.comp
    exact hprod
  exact TopologicalSpace.Compacts.uniformContinuous_sup.continuous.comp
    (hscaled.prodMk continuous_const)

theorem injective_cosmicConeTruncation :
    Function.Injective (cosmicConeTruncation :
      TopologicalSpace.Closeds (CosmicSpace E) →
        TopologicalSpace.NonemptyCompacts (CosmicRayAmbient E)) := by
  intro S T hST
  apply TopologicalSpace.Closeds.ext
  ext p
  constructor
  · intro hpS
    have hpTrunc : cosmicRayRepresentative p ∈ cosmicConeTruncation S :=
      (mem_cosmicConeTruncation_iff).2
        (Or.inr ⟨p, hpS, 1, right_mem_Icc.2 zero_le_one, by simp⟩)
    rw [hST, mem_cosmicConeTruncation_iff] at hpTrunc
    rcases hpTrunc with hp0 | ⟨q, hqT, t, ht, hpq⟩
    · have := congrArg norm hp0
      simp at this
    · have hrep : cosmicRayRepresentative p = cosmicRayRepresentative q :=
        endpoint_eq_of_mem_segment_of_norm_eq_one
          (norm_cosmicRayRepresentative p) (norm_cosmicRayRepresentative q) <| by
            rw [segment_eq_image]
            exact ⟨t, ht, by simpa using hpq.symm⟩
      simpa [injective_cosmicRayRepresentative hrep] using hqT
  · intro hpT
    have hpTrunc : cosmicRayRepresentative p ∈ cosmicConeTruncation T :=
      (mem_cosmicConeTruncation_iff).2
        (Or.inr ⟨p, hpT, 1, right_mem_Icc.2 zero_le_one, by simp⟩)
    rw [← hST, mem_cosmicConeTruncation_iff] at hpTrunc
    rcases hpTrunc with hp0 | ⟨q, hqS, t, ht, hpq⟩
    · have := congrArg norm hp0
      simp at this
    · have hrep : cosmicRayRepresentative p = cosmicRayRepresentative q :=
        endpoint_eq_of_mem_segment_of_norm_eq_one
          (norm_cosmicRayRepresentative p) (norm_cosmicRayRepresentative q) <| by
            rw [segment_eq_image]
            exact ⟨t, ht, by simpa using hpq.symm⟩
      simpa [injective_cosmicRayRepresentative hrep] using hqS

/-- Formula 4(14), using the unit-ball cone formula from 4.44. -/
noncomputable def cosmicSetDistance
    (S T : TopologicalSpace.Closeds (CosmicSpace E)) : ℝ :=
  dist (cosmicConeTruncation S) (cosmicConeTruncation T)

theorem cosmicSetDistance_nonneg (S T : TopologicalSpace.Closeds (CosmicSpace E)) :
    0 ≤ cosmicSetDistance S T :=
  dist_nonneg

@[simp]
theorem cosmicSetDistance_self (S : TopologicalSpace.Closeds (CosmicSpace E)) :
    cosmicSetDistance S S = 0 :=
  dist_self _

theorem cosmicSetDistance_comm (S T : TopologicalSpace.Closeds (CosmicSpace E)) :
    cosmicSetDistance S T = cosmicSetDistance T S :=
  dist_comm _ _

theorem cosmicSetDistance_triangle (S T U :
    TopologicalSpace.Closeds (CosmicSpace E)) :
    cosmicSetDistance S U ≤ cosmicSetDistance S T + cosmicSetDistance T U :=
  dist_triangle _ _ _

@[simp]
theorem cosmicSetDistance_eq_zero_iff
    {S T : TopologicalSpace.Closeds (CosmicSpace E)} :
    cosmicSetDistance S T = 0 ↔ S = T := by
  rw [cosmicSetDistance, dist_eq_zero]
  exact injective_cosmicConeTruncation.eq_iff

/-- The metric axioms in Theorem 4.46. -/
noncomputable def cosmicClosedSetMetric :
    PseudoMetric (TopologicalSpace.Closeds (CosmicSpace E)) ℝ where
  toFun := cosmicSetDistance
  refl' := cosmicSetDistance_self
  symm' := cosmicSetDistance_comm
  triangle' := cosmicSetDistance_triangle

theorem isClosedEmbedding_cosmicConeTruncation :
    IsClosedEmbedding (cosmicConeTruncation :
      TopologicalSpace.Closeds (CosmicSpace E) →
        TopologicalSpace.NonemptyCompacts (CosmicRayAmbient E)) :=
  continuous_cosmicConeTruncation.isClosedEmbedding
    injective_cosmicConeTruncation

/-- Theorem 4.46: the cosmic set metric characterizes cosmic set
convergence. -/
theorem pkConverges_iff_tendsto_cosmicSetDistance
    {Sseq : ℕ → TopologicalSpace.Closeds (CosmicSpace E)}
    {S : TopologicalSpace.Closeds (CosmicSpace E)} :
    PKConverges (fun n ↦ (Sseq n : Set (CosmicSpace E))) (S : Set (CosmicSpace E)) ↔
      Tendsto (fun n ↦ cosmicSetDistance (Sseq n) S) atTop (nhds 0) := by
  rw [pkConverges_iff_tendsto_pompeiuHausdorffEDist_of_common_bounded
    (E := CosmicSpace E) (Aseq := fun n ↦ (Sseq n : Set (CosmicSpace E)))
    (A := (S : Set (CosmicSpace E))) (B := Set.univ)
    S.isClosed isCompact_univ.isBounded
    (fun n x _hx ↦ Set.mem_univ x) (fun x _hx ↦ Set.mem_univ x)]
  have hclosedTendsto :
      Tendsto Sseq atTop (nhds S) ↔
        Tendsto (fun n ↦ cosmicConeTruncation (Sseq n)) atTop
          (nhds (cosmicConeTruncation S)) :=
    by
      simpa only [Function.comp_apply] using
        (isClosedEmbedding_cosmicConeTruncation (E := E)).isEmbedding.tendsto_nhds_iff
          (f := Sseq) (l := atTop) (y := S)
  change Tendsto (fun n ↦ edist (Sseq n) S) atTop (nhds 0) ↔ _
  have hedist :
      Tendsto (fun n ↦ edist (Sseq n) S) atTop (nhds 0) ↔
        Tendsto Sseq atTop (nhds S) := by
    constructor
    · intro h
      rw [EMetric.tendsto_nhds]
      intro ε hε
      exact h.eventually (Iio_mem_nhds hε)
    · intro h
      simpa using h.edist
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ S) atTop (nhds S))
  rw [hedist, hclosedTendsto, tendsto_iff_dist_tendsto_zero]
  rfl

/-- The compactness clause of Theorem 4.46, in the existing cosmic
hyperspace topology characterized above. -/
theorem isCompact_univ_cosmicClosedSets :
    IsCompact (Set.univ : Set (TopologicalSpace.Closeds (CosmicSpace E))) :=
  isCompact_univ

/-- The separability clause of Theorem 4.46. -/
theorem separableSpace_cosmicClosedSets :
    TopologicalSpace.SeparableSpace
      (TopologicalSpace.Closeds (CosmicSpace E)) := by
  infer_instance

/-- A singleton as an element of the closed cosmic hyperspace. -/
def cosmicSingleton (p : CosmicSpace E) :
    TopologicalSpace.Closeds (CosmicSpace E) :=
  ⟨{p}, isClosed_singleton⟩

@[simp]
theorem cosmicConeTruncation_singleton (p : CosmicSpace E) :
    cosmicConeTruncation (cosmicSingleton p) = cosmicRaySegment p := by
  apply TopologicalSpace.NonemptyCompacts.ext
  ext z
  rw [show z ∈ (cosmicConeTruncation (cosmicSingleton p) :
      Set (CosmicRayAmbient E)) ↔ _ from
    (mem_cosmicConeTruncation_iff (E := E)
      (S := cosmicSingleton p) (z := z))]
  change (z = 0 ∨ ∃ q : CosmicSpace E, q ∈ ({p} : Set (CosmicSpace E)) ∧
      ∃ t : ℝ, t ∈ Icc 0 1 ∧ z = t • cosmicRayRepresentative q) ↔
    z ∈ segment ℝ 0 (cosmicRayRepresentative p)
  rw [segment_eq_image]
  constructor
  · rintro (rfl | ⟨q, hq, t, ht, rfl⟩)
    · exact ⟨0, left_mem_Icc.2 zero_le_one, by simp⟩
    · simp only [mem_singleton_iff] at hq
      subst q
      exact ⟨t, ht, by simp⟩
  · rintro ⟨t, ht, rfl⟩
    right
    exact ⟨p, mem_singleton p, t, ht, by simp⟩

/-- Formula 4(18): the cosmic point metric is the restriction of the cosmic
set metric to singleton sets. -/
@[simp]
theorem cosmicSetDistance_singleton (p q : CosmicSpace E) :
    cosmicSetDistance (cosmicSingleton p) (cosmicSingleton q) =
      cosmicPointDistance p q := by
  simp only [cosmicSetDistance, cosmicConeTruncation_singleton,
    cosmicPointDistance]

end CosmicSetMetric

end RW
