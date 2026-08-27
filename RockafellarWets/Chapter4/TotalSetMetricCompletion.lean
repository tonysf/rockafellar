/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Completion Properties of the Total Set Metric

This file completes the valid metric-completion clauses surrounding Corollary
4.47 and records the obstruction to its printed openness claim for the literal
closed-ball embedding used in this development.
-/

import RockafellarWets.Chapter4.FiniteSetApproximation
import RockafellarWets.Chapter4.TotalSetMetric
import RockafellarWets.Chapter3.PointedCones

open Filter Function Metric Set Topology

namespace RW

section RangeCharacterization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

@[simp]
theorem coe_totalCosmicEmbedding
    (C : TopologicalSpace.Closeds E) :
    (totalCosmicEmbedding C : Set (CosmicSpace E)) =
      cosmicSet (C : Set E) (horizonCone (C : Set E)) := by
  have hzero : IsCone ({0} : Set E) := ⟨by simp, by simp⟩
  change closure (cosmicSet (C : Set E) ({0} : Set E)) = _
  rw [closure_cosmicSet hzero, C.isClosed.closure_eq, closure_singleton]
  simp only [union_singleton, insert_eq_of_mem (zero_mem_horizonCone (C : Set E))]

/-- The literal range of `totalCosmicEmbedding` consists precisely of closed
cosmic sets whose direction cone is the horizon cone of their ordinary part. -/
theorem mem_range_totalCosmicEmbedding_iff
    (S : TopologicalSpace.Closeds (CosmicSpace E)) :
    S ∈ Set.range (totalCosmicEmbedding :
      TopologicalSpace.Closeds E →
        TopologicalSpace.Closeds (CosmicSpace E)) ↔
      cosmicDirectionCone (S : Set (CosmicSpace E)) =
        horizonCone (cosmicOrdinaryPart (S : Set (CosmicSpace E))) := by
  constructor
  · rintro ⟨C, rfl⟩
    rw [coe_totalCosmicEmbedding,
      cosmicDirectionCone_cosmicSet (isCone_horizonCone (C : Set E)),
      cosmicOrdinaryPart_cosmicSet]
  · intro hdir
    have hOrdClosed : IsClosed
        (cosmicOrdinaryPart (S : Set (CosmicSpace E))) :=
      S.isClosed.preimage continuous_cosmicEmbed
    let C : TopologicalSpace.Closeds E :=
      ⟨cosmicOrdinaryPart (S : Set (CosmicSpace E)), hOrdClosed⟩
    refine ⟨C, ?_⟩
    apply TopologicalSpace.Closeds.ext
    rw [coe_totalCosmicEmbedding]
    rw [show (C : Set E) = cosmicOrdinaryPart
      (S : Set (CosmicSpace E)) from rfl, ← hdir]
    exact cosmicSet_parts (S : Set (CosmicSpace E))

omit [FiniteDimensional ℝ E] in
/-- The ordinary cosmic points are dense in the closed-ball cosmic space. -/
theorem denseRange_cosmicEmbed :
    DenseRange (cosmicEmbed : E → CosmicSpace E) := by
  intro p
  rcases cosmicEmbed_or_cosmicDirection p with ⟨x, rfl⟩ | ⟨u, rfl⟩
  · exact subset_closure (Set.mem_range_self x)
  · exact mem_closure_iff_seq_limit.mpr
      ⟨fun n ↦ cosmicEmbed (cosmicRadialOrdinary u n),
        fun n ↦ Set.mem_range_self (cosmicRadialOrdinary u n),
        tendsto_cosmicRadialOrdinary u⟩

/-- Every closed cosmic set is a cosmic-set-metric limit of literal total
embeddings of closed ordinary sets.  This is the density clause required for
the completion assertion in Corollary 4.47. -/
theorem exists_totalCosmicEmbedding_approximation
    (S : TopologicalSpace.Closeds (CosmicSpace E)) :
    ∃ C : ℕ → TopologicalSpace.Closeds E,
      Tendsto (fun n ↦ cosmicSetDistance (totalCosmicEmbedding (C n)) S)
        atTop (nhds 0) := by
  letI : Nonempty (CosmicSpace E) :=
    ⟨⟨0, by simp⟩⟩
  rcases RW.IsClosed.exists_finite_subset_dense_pkConverges
      (E := CosmicSpace E) (denseRange_cosmicEmbed (E := E)) S.isClosed with
    ⟨F, hFfinite, hFrange, hFlim⟩
  have hCfinite : ∀ n,
      (cosmicOrdinaryPart (F n)).Finite := by
    intro n
    exact Set.Finite.preimage injective_cosmicEmbed.injOn (hFfinite n)
  let C : ℕ → TopologicalSpace.Closeds E := fun n ↦
    ⟨cosmicOrdinaryPart (F n), (hCfinite n).isClosed⟩
  have hEmbed : ∀ n,
      totalCosmicEmbedding (C n) =
        ⟨F n, (hFfinite n).isClosed⟩ := by
    intro n
    apply TopologicalSpace.Closeds.ext
    change closure (cosmicSet (cosmicOrdinaryPart (F n)) ({0} : Set E)) = F n
    have hset : cosmicSet (cosmicOrdinaryPart (F n)) ({0} : Set E) = F n := by
      rw [cosmicSet, cosmicDirections_zero, union_empty]
      exact Set.image_preimage_eq_of_subset (hFrange n)
    rw [hset, (hFfinite n).isClosed.closure_eq]
  refine ⟨C, ?_⟩
  have hmetric :=
    (pkConverges_iff_tendsto_cosmicSetDistance
      (Sseq := fun n ↦ (⟨F n, (hFfinite n).isClosed⟩ :
        TopologicalSpace.Closeds (CosmicSpace E))) (S := S)).1 hFlim
  simpa only [hEmbed] using hmetric

/-- The literal total embedding has dense range in the cosmic closed-set
hyperspace. -/
theorem denseRange_totalCosmicEmbedding :
    DenseRange (totalCosmicEmbedding :
      TopologicalSpace.Closeds E →
        TopologicalSpace.Closeds (CosmicSpace E)) := by
  intro S
  rcases exists_totalCosmicEmbedding_approximation S with ⟨C, hdist⟩
  have hpk : PKConverges
      (fun n ↦ (totalCosmicEmbedding (C n) : Set (CosmicSpace E)))
      (S : Set (CosmicSpace E)) :=
    (pkConverges_iff_tendsto_cosmicSetDistance
      (Sseq := fun n ↦ totalCosmicEmbedding (C n)) (S := S)).2 hdist
  have hedist :=
    (pkConverges_iff_tendsto_pompeiuHausdorffEDist_of_common_bounded
      (E := CosmicSpace E)
      (Aseq := fun n ↦ (totalCosmicEmbedding (C n) : Set (CosmicSpace E)))
      (A := (S : Set (CosmicSpace E))) (B := Set.univ)
      S.isClosed isCompact_univ.isBounded
      (fun n x _hx ↦ Set.mem_univ x) (fun x _hx ↦ Set.mem_univ x)).1 hpk
  have htendsto : Tendsto (fun n ↦ totalCosmicEmbedding (C n)) atTop
      (nhds S) := by
    rw [EMetric.tendsto_nhds]
    intro ε hε
    change Tendsto
      (fun n ↦ edist (totalCosmicEmbedding (C n)) S) atTop (nhds 0) at hedist
    exact hedist.eventually (Iio_mem_nhds hε)
  exact mem_closure_iff_seq_limit.mpr
    ⟨fun n ↦ totalCosmicEmbedding (C n),
      fun n ↦ Set.mem_range_self (C n), htendsto⟩

/-- The total embedding preserves the two explicitly bundled distances. -/
theorem totalCosmicEmbedding_isometry (C D : TopologicalSpace.Closeds E) :
    cosmicSetDistance (totalCosmicEmbedding C) (totalCosmicEmbedding D) =
      totalSetDistance C D :=
  rfl

/-- Cauchy sequences for the cosmic closed-set metric, stated independently
of installing a second metric-space instance on the hyperspace. -/
def CosmicSetCauchy
    (S : ℕ → TopologicalSpace.Closeds (CosmicSpace E)) : Prop :=
  ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
    cosmicSetDistance (S m) (S n) < ε

/-- The cosmic closed-set metric is complete.  Together with
`totalCosmicEmbedding_isometry` and
`exists_totalCosmicEmbedding_approximation`, this packages the book's
completion statement without replacing the hyperspace's existing metric
instance. -/
theorem exists_cosmicSetMetric_limit_of_cauchy
    {S : ℕ → TopologicalSpace.Closeds (CosmicSpace E)}
    (hS : CosmicSetCauchy S) :
    ∃ T : TopologicalSpace.Closeds (CosmicSpace E),
      Tendsto (fun n ↦ cosmicSetDistance (S n) T) atTop (nhds 0) := by
  have htrunc : CauchySeq (fun n ↦ cosmicConeTruncation (S n)) :=
    Metric.cauchySeq_iff.mpr hS
  rcases cauchySeq_tendsto_of_complete htrunc with ⟨K, hK⟩
  have hKrange : K ∈ Set.range (cosmicConeTruncation :
      TopologicalSpace.Closeds (CosmicSpace E) →
        TopologicalSpace.NonemptyCompacts (CosmicRayAmbient E)) := by
    apply (isClosedEmbedding_cosmicConeTruncation (E := E)).isClosed_range.mem_of_tendsto hK
    exact Eventually.of_forall fun n ↦ Set.mem_range_self (S n)
  rcases hKrange with ⟨T, rfl⟩
  refine ⟨T, ?_⟩
  simpa only [cosmicSetDistance] using
    (tendsto_iff_dist_tendsto_zero.mp hK)

/-- The metric-completion target is separable; consequently so is the
subspace occupied by literal total embeddings. -/
theorem separableSpace_totalCosmicEmbeddingRange :
    TopologicalSpace.SeparableSpace
      (Set.range (totalCosmicEmbedding :
        TopologicalSpace.Closeds E →
          TopologicalSpace.Closeds (CosmicSpace E))) := by
  infer_instance

/-- Closed cosmic sets supported entirely on ordinary cosmic points form an
open subset of the hyperspace. -/
theorem isOpen_ordinarySupportedCosmicClosedSets :
    IsOpen {S : TopologicalSpace.Closeds (CosmicSpace E) |
      (S : Set (CosmicSpace E)) ⊆
        Set.range (cosmicEmbed : E → CosmicSpace E)} := by
  have hopen : IsOpen (Set.range (cosmicEmbed : E → CosmicSpace E)) := by
    have hrange : Set.range (cosmicEmbed : E → CosmicSpace E) =
        {p : CosmicSpace E | ‖(p : E)‖ < 1} := by
      ext p
      exact exists_cosmicEmbed_eq_iff (E := E) p
    rw [hrange]
    exact isOpen_lt continuous_subtype_val.norm continuous_const
  have h := TopologicalSpace.Compacts.isOpen_subsets_of_isOpen
    (α := CosmicSpace E) hopen
  exact h.preimage (isometry_cosmicClosedCompact (E := E)).continuous

omit [FiniteDimensional ℝ E] in
/-- Every ordinary-supported closed cosmic set is in the literal range of
`totalCosmicEmbedding`.  Thus the preceding theorem gives a genuine open
subspace contained in the range, even though the full range need not be open. -/
theorem ordinarySupportedCosmicClosedSets_subset_range :
    {S : TopologicalSpace.Closeds (CosmicSpace E) |
      (S : Set (CosmicSpace E)) ⊆
        Set.range (cosmicEmbed : E → CosmicSpace E)} ⊆
      Set.range (totalCosmicEmbedding :
        TopologicalSpace.Closeds E →
          TopologicalSpace.Closeds (CosmicSpace E)) := by
  intro S hS
  have hOrdClosed : IsClosed
      (cosmicOrdinaryPart (S : Set (CosmicSpace E))) :=
    S.isClosed.preimage continuous_cosmicEmbed
  let C : TopologicalSpace.Closeds E :=
    ⟨cosmicOrdinaryPart (S : Set (CosmicSpace E)), hOrdClosed⟩
  refine ⟨C, ?_⟩
  apply TopologicalSpace.Closeds.ext
  change closure (cosmicSet (C : Set E) ({0} : Set E)) =
    (S : Set (CosmicSpace E))
  have hcosmic : cosmicSet (C : Set E) ({0} : Set E) =
      (S : Set (CosmicSpace E)) := by
    rw [cosmicSet, cosmicDirections_zero, union_empty]
    exact Set.image_preimage_eq_of_subset hS
  rw [hcosmic, S.isClosed.closure_eq]

end RangeCharacterization

section OpennessObstruction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A precise obstruction to the printed openness claim in Corollary 4.47.
If an embedded set contains a direction point which can be approached by
distinct direction points outside that embedded set, adjoining those points
produces non-range closed cosmic sets converging to the range point. -/
theorem not_isOpen_range_totalCosmicEmbedding_of_direction_perturbation
    {C : TopologicalSpace.Closeds E} {u : CosmicBoundary E}
    {v : ℕ → CosmicBoundary E}
    (hu : cosmicDirection u ∈ totalCosmicEmbedding C)
    (hv : Tendsto v atTop (nhds u))
    (hvout : ∀ n, cosmicDirection (v n) ∉ totalCosmicEmbedding C) :
    ¬ IsOpen (Set.range (totalCosmicEmbedding :
      TopologicalSpace.Closeds E →
        TopologicalSpace.Closeds (CosmicSpace E))) := by
  let S : TopologicalSpace.Closeds (CosmicSpace E) := totalCosmicEmbedding C
  let T : ℕ → TopologicalSpace.Closeds (CosmicSpace E) := fun n ↦
    S ⊔ cosmicSingleton (cosmicDirection (v n))
  have hTlim : Tendsto T atTop (nhds S) := by
    have hdir : Tendsto (fun n ↦ cosmicDirection (v n)) atTop
        (nhds (cosmicDirection u)) :=
      ((isEmbedding_cosmicDirection (E := E)).continuous.tendsto u).comp hv
    have hsingle : Tendsto
        (fun n ↦ cosmicSingleton (cosmicDirection (v n))) atTop
        (nhds (cosmicSingleton (cosmicDirection u))) :=
      (TopologicalSpace.Closeds.continuous_singleton.tendsto
        (cosmicDirection u)).comp hdir
    have hsup : Tendsto T atTop
        (nhds (S ⊔ cosmicSingleton (cosmicDirection u))) := by
      have hpair : Tendsto
          (fun n ↦ (S, cosmicSingleton (cosmicDirection (v n)))) atTop
          (nhds (S, cosmicSingleton (cosmicDirection u))) := by
        rw [nhds_prod_eq]
        exact (tendsto_const_nhds (x := S)).prodMk hsingle
      exact (continuous_sup.tendsto
        (S, cosmicSingleton (cosmicDirection u))).comp hpair
    have hle : cosmicSingleton (cosmicDirection u) ≤ S := by
      change ({cosmicDirection u} : Set (CosmicSpace E)) ⊆ S
      exact Set.singleton_subset_iff.mpr hu
    simpa only [sup_eq_left.mpr hle] using hsup
  have hTout : ∀ n, T n ∉ Set.range (totalCosmicEmbedding :
      TopologicalSpace.Closeds E →
        TopologicalSpace.Closeds (CosmicSpace E)) := by
    intro n hTrange
    rcases hTrange with ⟨D, hD⟩
    have hDC : D = C := by
      apply TopologicalSpace.Closeds.ext
      ext x
      have hne : cosmicEmbed x ≠ cosmicDirection (v n) :=
        cosmicEmbed_ne_cosmicDirection x (v n)
      constructor
      · intro hxD
        have hxCosmic : cosmicEmbed x ∈ totalCosmicEmbedding D :=
          cosmicEmbed_mem_totalCosmicEmbedding_iff.2 hxD
        rw [hD] at hxCosmic
        change cosmicEmbed x ∈
          (S : Set (CosmicSpace E)) ∪ {cosmicDirection (v n)} at hxCosmic
        rw [mem_union, mem_singleton_iff] at hxCosmic
        exact cosmicEmbed_mem_totalCosmicEmbedding_iff.1
          (show cosmicEmbed x ∈ totalCosmicEmbedding C by
            simpa only [hne, or_false, S] using hxCosmic)
      · intro hxC
        have hxCosmic : cosmicEmbed x ∈ T n := by
          exact Set.mem_union_left _
            (show cosmicEmbed x ∈ S by
              simpa only [S] using
                (cosmicEmbed_mem_totalCosmicEmbedding_iff.2 hxC))
        rw [← hD] at hxCosmic
        exact cosmicEmbed_mem_totalCosmicEmbedding_iff.1 hxCosmic
    subst D
    have hEq : T n = S := hD.symm
    have hvT : cosmicDirection (v n) ∈ T n := by
      exact Set.mem_union_right _ (Set.mem_singleton _)
    rw [hEq] at hvT
    exact hvout n hvT
  intro hopen
  have hSrange : S ∈ Set.range (totalCosmicEmbedding :
      TopologicalSpace.Closeds E →
        TopologicalSpace.Closeds (CosmicSpace E)) :=
    ⟨C, rfl⟩
  have hevent := hTlim.eventually (hopen.mem_nhds hSrange)
  exact (hevent.and (Eventually.of_forall hTout)).exists.elim fun _ h ↦ h.2 h.1

end OpennessObstruction

section PlaneCounterexample

/-- The horizontal axis, used for the concrete two-dimensional obstruction
to the printed openness claim in Corollary 4.47. -/
def horizontalAxisClosed : TopologicalSpace.Closeds (ℝ × ℝ) :=
  ⟨{p | p.2 = 0}, isClosed_eq continuous_snd continuous_const⟩

theorem isCone_horizontalAxisClosed :
    IsCone (horizontalAxisClosed : Set (ℝ × ℝ)) := by
  constructor
  · simp [horizontalAxisClosed]
  · intro p hp c hc
    change p.2 = 0 at hp
    change (c • p).2 = 0
    simp [hp]

/-- The positive horizontal direction. -/
def horizontalBoundaryDirection : CosmicBoundary (ℝ × ℝ) :=
  ⟨(1, 0), by
    rw [mem_sphere_zero_iff_norm, Prod.norm_def]
    norm_num⟩

/-- Nearby max-norm unit directions with a small positive vertical
component. -/
noncomputable def perturbedHorizontalBoundaryDirection (n : ℕ) :
    CosmicBoundary (ℝ × ℝ) :=
  ⟨(1, 1 / ((n : ℝ) + 1)), by
    rw [mem_sphere_zero_iff_norm, Prod.norm_def]
    simp only [Real.norm_eq_abs, abs_one]
    rw [max_eq_left]
    rw [abs_of_nonneg (by positivity)]
    calc
      1 / ((n : ℝ) + 1) ≤ 1 / (1 : ℝ) :=
        one_div_le_one_div_of_le (by norm_num) (by
          have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
          linarith)
      _ = 1 := by norm_num⟩

theorem tendsto_perturbedHorizontalBoundaryDirection :
    Tendsto perturbedHorizontalBoundaryDirection atTop
      (nhds horizontalBoundaryDirection) := by
  apply tendsto_subtype_rng.mpr
  have hpair : Tendsto
      (fun n : ℕ ↦ ((1 : ℝ), 1 / ((n : ℝ) + 1))) atTop
      (nhds ((1 : ℝ), 0)) := by
    rw [nhds_prod_eq]
    exact (tendsto_const_nhds (x := (1 : ℝ))).prodMk
      tendsto_one_div_add_atTop_nhds_zero_nat
  simpa only [perturbedHorizontalBoundaryDirection,
    horizontalBoundaryDirection] using hpair

theorem horizontalBoundaryDirection_mem_totalCosmicEmbedding :
    cosmicDirection horizontalBoundaryDirection ∈
      totalCosmicEmbedding horizontalAxisClosed := by
  change cosmicDirection horizontalBoundaryDirection ∈
    (totalCosmicEmbedding horizontalAxisClosed : Set (CosmicSpace (ℝ × ℝ)))
  rw [coe_totalCosmicEmbedding,
    horizonCone_eq_self_of_isClosed_isCone
      horizontalAxisClosed.isClosed isCone_horizontalAxisClosed]
  rw [mem_cosmicSet]
  right
  exact ⟨horizontalBoundaryDirection, by simp [horizontalAxisClosed,
    horizontalBoundaryDirection], rfl⟩

theorem perturbedHorizontalBoundaryDirection_not_mem_totalCosmicEmbedding
    (n : ℕ) :
    cosmicDirection (perturbedHorizontalBoundaryDirection n) ∉
      totalCosmicEmbedding horizontalAxisClosed := by
  change cosmicDirection (perturbedHorizontalBoundaryDirection n) ∉
    (totalCosmicEmbedding horizontalAxisClosed : Set (CosmicSpace (ℝ × ℝ)))
  rw [coe_totalCosmicEmbedding,
    horizonCone_eq_self_of_isClosed_isCone
      horizontalAxisClosed.isClosed isCone_horizontalAxisClosed]
  intro hmem
  rw [mem_cosmicSet] at hmem
  rcases hmem with ⟨x, -, hx⟩ | ⟨u, hu, huv⟩
  · exact cosmicEmbed_ne_cosmicDirection x
      (perturbedHorizontalBoundaryDirection n) hx
  · have hueq : u = perturbedHorizontalBoundaryDirection n :=
      injective_cosmicDirection huv
    subst u
    change (1 / ((n : ℝ) + 1) : ℝ) = 0 at hu
    exact one_div_ne_zero (by positivity) hu

/-- In the literal closed-ball model used by this project, the full range of
`totalCosmicEmbedding` is not open already in dimension two.  The sequence
adjoining `perturbedHorizontalBoundaryDirection n` is the promised concrete
Lean-level counterexample. -/
theorem not_isOpen_range_totalCosmicEmbedding_plane :
    ¬ IsOpen (Set.range (totalCosmicEmbedding :
      TopologicalSpace.Closeds (ℝ × ℝ) →
        TopologicalSpace.Closeds (CosmicSpace (ℝ × ℝ)))) :=
  not_isOpen_range_totalCosmicEmbedding_of_direction_perturbation
    horizontalBoundaryDirection_mem_totalCosmicEmbedding
    tendsto_perturbedHorizontalBoundaryDirection
    perturbedHorizontalBoundaryDirection_not_mem_totalCosmicEmbedding

end PlaneCounterexample

end RW
