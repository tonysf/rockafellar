/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Explicit Cosmic Metric Formulas and Completion

This file completes the inner-product formulas in Exercise 4.48, separately
from the metric-independent ray-segment backend.
-/

import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Topology.MetricSpace.Completion
import RockafellarWets.Chapter4.CosmicSetMetric

open Filter Metric Set Topology
open InnerProductGeometry
open RealInnerProductSpace

namespace RW

section RaySineDistance

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The piecewise sine-of-angle function `s` in Exercise 4.48. -/
noncomputable def bookRaySineDistance (u v : V) : ℝ :=
  if angle u v < Real.pi / 2 then Real.sin (angle u v) else 1

/-- The compact unit segment on the ray through `u`. -/
noncomputable def unitRaySegment (u : V) :
    TopologicalSpace.NonemptyCompacts V where
  carrier := segment ℝ 0 u
  isCompact' := by
    rw [segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  nonempty' := ⟨0, left_mem_segment ℝ _ _⟩

@[simp]
theorem coe_unitRaySegment (u : V) :
    (unitRaySegment u : Set V) = segment ℝ 0 u :=
  rfl

private theorem angle_lt_pi_div_two_iff_inner_pos
    {u v : V} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    angle u v < Real.pi / 2 ↔ 0 < ⟪u, v⟫ := by
  rw [angle, Real.arccos_lt_pi_div_two]
  simp [hu, hv]

private theorem sin_angle_eq_sqrt_one_sub_inner_sq
    {u v : V} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    Real.sin (angle u v) = Real.sqrt (1 - ⟪u, v⟫ ^ 2) := by
  have h := sin_angle_mul_norm_mul_norm u v
  rw [hu, hv, mul_one, mul_one, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, hu, hv, one_pow, one_mul] at h
  simpa only [sq] using h

private theorem norm_sub_inner_smul_eq_sin_angle
    {u v : V} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖u - ⟪u, v⟫ • v‖ = Real.sin (angle u v) := by
  rw [sin_angle_eq_sqrt_one_sub_inner_sq hu hv, ← Real.sqrt_sq (norm_nonneg _)]
  congr 1
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
    inner_smul_right, hu, hv, mul_one, sq_abs]
  ring

private theorem raySine_le_dist_unit_to_ray
    {u v : V} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    bookRaySineDistance u v ≤ dist u (t • v) := by
  let c := ⟪u, v⟫
  rw [bookRaySineDistance]
  split_ifs with hacute
  · rw [← sq_le_sq₀ (sin_angle_nonneg u v) dist_nonneg, dist_eq_norm,
      sin_angle_eq_sqrt_one_sub_inner_sq hu hv,
      Real.sq_sqrt]
    · rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg ht.1, inner_smul_right,
        hu, hv]
      nlinarith [sq_nonneg (t - ⟪u, v⟫)]
    · rcases real_inner_mem_Icc_of_norm_eq_one hu hv with ⟨hcneg, hcle⟩
      nlinarith [mul_nonneg (sub_nonneg.mpr hcle) (sub_nonneg.mpr <| by linarith)]
  · rw [← sq_le_sq₀ zero_le_one dist_nonneg, one_pow, dist_eq_norm,
      norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht.1, inner_smul_right,
      hu, hv]
    have hc : ⟪u, v⟫ ≤ 0 := by
      rw [angle_lt_pi_div_two_iff_inner_pos hu hv] at hacute
      exact le_of_not_gt hacute
    nlinarith [sq_nonneg t, mul_nonpos_of_nonneg_of_nonpos ht.1 hc]

private theorem hausdorffEDist_unitRaySegment_ne_top (u v : V) :
    hausdorffEDist (unitRaySegment u : Set V) (unitRaySegment v : Set V) ≠ ⊤ :=
  hausdorffEDist_ne_top_of_nonempty_of_bounded
    (unitRaySegment u).nonempty (unitRaySegment v).nonempty
    (unitRaySegment u).isCompact.isBounded
    (unitRaySegment v).isCompact.isBounded

/-- The ray-segment distance is exactly the book's piecewise sine-of-angle
function for unit vectors. -/
theorem dist_unitRaySegment_eq_bookRaySine
    {u v : V} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    dist (unitRaySegment u) (unitRaySegment v) =
      bookRaySineDistance u v := by
  let c := ⟪u, v⟫
  apply le_antisymm
  · rw [Metric.NonemptyCompacts.dist_eq]
    apply hausdorffDist_le_of_mem_dist
    · rw [bookRaySineDistance]
      split_ifs
      · exact sin_angle_nonneg u v
      · exact zero_le_one
    · intro x hx
      change x ∈ segment ℝ 0 u at hx
      rw [segment_eq_image] at hx
      rcases hx with ⟨a, ha, rfl⟩
      simp only [smul_zero, zero_add]
      rw [bookRaySineDistance]
      split_ifs with hacute
      · have hcpos : 0 < c :=
          (angle_lt_pi_div_two_iff_inner_pos hu hv).mp hacute
        have hcle : c ≤ 1 := real_inner_le_one_of_norm_eq_one hu hv
        refine ⟨(a * c) • v, ?_, ?_⟩
        · change (a * c) • v ∈ segment ℝ 0 v
          rw [segment_eq_image]
          exact ⟨a * c, ⟨mul_nonneg ha.1 hcpos.le,
            (mul_le_of_le_one_left hcpos.le ha.2).trans hcle⟩, by simp⟩
        · rw [dist_eq_norm]
          have hsub : a • u - (a * c) • v = a • (u - c • v) := by module
          rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha.1,
            norm_sub_inner_smul_eq_sin_angle hu hv]
          exact mul_le_of_le_one_left (sin_angle_nonneg u v) ha.2
      · refine ⟨0, left_mem_segment ℝ _ _, ?_⟩
        simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha.1, hu] using ha.2
    · intro x hx
      change x ∈ segment ℝ 0 v at hx
      rw [segment_eq_image] at hx
      rcases hx with ⟨a, ha, rfl⟩
      simp only [smul_zero, zero_add]
      rw [bookRaySineDistance]
      split_ifs with hacute
      · have hcpos : 0 < c :=
          (angle_lt_pi_div_two_iff_inner_pos hu hv).mp hacute
        have hcle : c ≤ 1 := real_inner_le_one_of_norm_eq_one hu hv
        refine ⟨(a * c) • u, ?_, ?_⟩
        · change (a * c) • u ∈ segment ℝ 0 u
          rw [segment_eq_image]
          exact ⟨a * c, ⟨mul_nonneg ha.1 hcpos.le,
            (mul_le_of_le_one_left hcpos.le ha.2).trans hcle⟩, by simp⟩
        · rw [dist_eq_norm]
          have hsub : a • v - (a * c) • u =
              a • (v - ⟪v, u⟫ • u) := by
            have hinner : ⟪v, u⟫ = c := by
              dsimp only [c]
              exact (real_inner_comm v u).symm
            rw [hinner]
            module
          rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha.1,
            norm_sub_inner_smul_eq_sin_angle hv hu, angle_comm]
          exact mul_le_of_le_one_left (sin_angle_nonneg u v) ha.2
      · refine ⟨0, left_mem_segment ℝ _ _, ?_⟩
        simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha.1, hv] using ha.2
  · rw [bookRaySineDistance]
    split_ifs with hacute
    · calc
        Real.sin (angle u v) ≤
            infDist u (unitRaySegment v : Set V) := by
          rw [le_infDist (unitRaySegment v).nonempty]
          intro y hy
          change y ∈ segment ℝ 0 v at hy
          rw [segment_eq_image] at hy
          rcases hy with ⟨t, ht, rfl⟩
          simpa [bookRaySineDistance, hacute] using
            (raySine_le_dist_unit_to_ray hu hv ht)
        _ ≤ hausdorffDist (unitRaySegment u : Set V)
              (unitRaySegment v : Set V) :=
          infDist_le_hausdorffDist_of_mem (right_mem_segment ℝ _ _)
            (hausdorffEDist_unitRaySegment_ne_top u v)
        _ = dist (unitRaySegment u) (unitRaySegment v) := rfl
    · calc
        1 ≤ infDist u (unitRaySegment v : Set V) := by
          rw [le_infDist (unitRaySegment v).nonempty]
          intro y hy
          change y ∈ segment ℝ 0 v at hy
          rw [segment_eq_image] at hy
          rcases hy with ⟨t, ht, rfl⟩
          simpa [bookRaySineDistance, hacute] using
            (raySine_le_dist_unit_to_ray hu hv ht)
        _ ≤ hausdorffDist (unitRaySegment u : Set V)
              (unitRaySegment v : Set V) :=
          infDist_le_hausdorffDist_of_mem (right_mem_segment ℝ _ _)
            (hausdorffEDist_unitRaySegment_ne_top u v)
        _ = dist (unitRaySegment u) (unitRaySegment v) := rfl

end RaySineDistance

section CosmicPointFormulas

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The unnormalized lower ray `(x, -1)` in formulas 4(16)--4(17). -/
def ordinaryCosmicRay (x : E) : CosmicRayAmbient E :=
  WithLp.toLp 2 (x, (-1 : ℝ))

/-- The horizontal ray `(u, 0)` representing a cosmic direction. -/
def directionCosmicRay (u : CosmicBoundary E) : CosmicRayAmbient E :=
  WithLp.toLp 2 ((u : E), (0 : ℝ))

theorem bookRaySineDistance_smul_left_of_pos
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u v : V) {r : ℝ} (hr : 0 < r) :
    bookRaySineDistance (r • u) v = bookRaySineDistance u v := by
  simp only [bookRaySineDistance, angle_smul_left_of_pos u v hr]

theorem bookRaySineDistance_smul_right_of_pos
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u v : V) {r : ℝ} (hr : 0 < r) :
    bookRaySineDistance u (r • v) = bookRaySineDistance u v := by
  simp only [bookRaySineDistance, angle_smul_right_of_pos u v hr]

theorem cosmicRayRepresentative_cosmicEmbed_eq_smul_ordinaryRay (x : E) :
    cosmicRayRepresentative (cosmicEmbed x) =
      cosmicScale x • ordinaryCosmicRay x := by
  rw [cosmicRayRepresentative_cosmicEmbed]
  rw [ordinaryCosmicRay, ← WithLp.toLp_smul]
  congr 1
  simp

@[simp]
theorem cosmicRayRepresentative_cosmicDirection_eq_directionRay
    (u : CosmicBoundary E) :
    cosmicRayRepresentative (cosmicDirection u) = directionCosmicRay u := by
  simp [directionCosmicRay]

theorem cosmicRaySegment_eq_unitRaySegment (p : CosmicSpace E) :
    cosmicRaySegment p = unitRaySegment (cosmicRayRepresentative p) := by
  rfl

/-- Exercise 4.48: the cosmic point metric is the piecewise sine-of-angle
function of the corresponding unit ray representatives. -/
theorem cosmicPointDistance_eq_bookRaySine (p q : CosmicSpace E) :
    cosmicPointDistance p q =
      bookRaySineDistance (cosmicRayRepresentative p)
        (cosmicRayRepresentative q) := by
  rw [cosmicPointDistance, cosmicRaySegment_eq_unitRaySegment,
    cosmicRaySegment_eq_unitRaySegment,
    dist_unitRaySegment_eq_bookRaySine
      (norm_cosmicRayRepresentative p) (norm_cosmicRayRepresentative q)]

/-- Formula 4(16), ordinary--ordinary case. -/
theorem cosmicPointDistance_cosmicEmbed (x y : E) :
    cosmicPointDistance (cosmicEmbed x) (cosmicEmbed y) =
      bookRaySineDistance (ordinaryCosmicRay x) (ordinaryCosmicRay y) := by
  rw [cosmicPointDistance_eq_bookRaySine,
    cosmicRayRepresentative_cosmicEmbed_eq_smul_ordinaryRay,
    cosmicRayRepresentative_cosmicEmbed_eq_smul_ordinaryRay,
    bookRaySineDistance_smul_left_of_pos _ _ (cosmicScale_pos x),
    bookRaySineDistance_smul_right_of_pos _ _ (cosmicScale_pos y)]

/-- First formula in 4(17), ordinary--direction case. -/
theorem cosmicPointDistance_cosmicEmbed_cosmicDirection
    (x : E) (u : CosmicBoundary E) :
    cosmicPointDistance (cosmicEmbed x) (cosmicDirection u) =
      bookRaySineDistance (ordinaryCosmicRay x) (directionCosmicRay u) := by
  rw [cosmicPointDistance_eq_bookRaySine,
    cosmicRayRepresentative_cosmicEmbed_eq_smul_ordinaryRay,
    cosmicRayRepresentative_cosmicDirection_eq_directionRay,
    bookRaySineDistance_smul_left_of_pos _ _ (cosmicScale_pos x)]

/-- Second formula in 4(17), direction--direction case. -/
theorem cosmicPointDistance_cosmicDirection
    (u v : CosmicBoundary E) :
    cosmicPointDistance (cosmicDirection u) (cosmicDirection v) =
      bookRaySineDistance (directionCosmicRay u) (directionCosmicRay v) := by
  rw [cosmicPointDistance_eq_bookRaySine,
    cosmicRayRepresentative_cosmicDirection_eq_directionRay,
    cosmicRayRepresentative_cosmicDirection_eq_directionRay]

end CosmicPointFormulas

section PointCompletion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A wrapper carrying the metric of Exercise 4.48, without replacing the
project's closed-ball metric instance on `CosmicSpace`. -/
@[ext]
structure CosmicPointModel (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toCosmicSpace : CosmicSpace E

/-- The ordinary point space equipped with the restriction of the metric in
Exercise 4.48. -/
@[ext]
structure OrdinaryPointModel (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toNormedSpace : E

noncomputable instance : MetricSpace (CosmicPointModel E) :=
  MetricSpace.induced
    (fun p : CosmicPointModel E ↦ cosmicRaySegment p.toCosmicSpace)
    (fun _ _ h ↦ CosmicPointModel.ext <| injective_cosmicRaySegment h)
    inferInstance

@[simp]
theorem dist_cosmicPointModel (p q : CosmicPointModel E) :
    dist p q = cosmicPointDistance p.toCosmicSpace q.toCosmicSpace :=
  rfl

/-- The canonical inclusion of ordinary points into the point-metric cosmic
model. -/
noncomputable def ordinaryPointToCosmicPoint (x : OrdinaryPointModel E) :
    CosmicPointModel E :=
  ⟨cosmicEmbed x.toNormedSpace⟩

theorem injective_ordinaryPointToCosmicPoint :
    Function.Injective
      (ordinaryPointToCosmicPoint : OrdinaryPointModel E → CosmicPointModel E) := by
  intro x y h
  apply OrdinaryPointModel.ext
  exact injective_cosmicEmbed (congrArg CosmicPointModel.toCosmicSpace h)

noncomputable instance : MetricSpace (OrdinaryPointModel E) :=
  MetricSpace.induced ordinaryPointToCosmicPoint
    injective_ordinaryPointToCosmicPoint inferInstance

@[simp]
theorem dist_ordinaryPointModel (x y : OrdinaryPointModel E) :
    dist x y = ordinaryCosmicPointDistance x.toNormedSpace y.toNormedSpace :=
  rfl

theorem isometry_ordinaryPointToCosmicPoint :
    Isometry
      (ordinaryPointToCosmicPoint : OrdinaryPointModel E → CosmicPointModel E) :=
  fun _ _ ↦ rfl

section FiniteDimensional

variable [FiniteDimensional ℝ E]

noncomputable instance : CompleteSpace (CosmicPointModel E) :=
  Metric.complete_of_cauchySeq_tendsto fun p hp ↦ by
    have hpRW : CosmicPointCauchy (fun n ↦ (p n).toCosmicSpace) := by
      intro ε hε
      rcases Metric.cauchySeq_iff.mp hp ε hε with ⟨N, hN⟩
      exact ⟨N, fun m hm n hn ↦ by simpa using hN m hm n hn⟩
    rcases exists_pointMetric_limit_of_cauchy hpRW with ⟨q, hq⟩
    refine ⟨⟨q⟩, tendsto_iff_dist_tendsto_zero.mpr ?_⟩
    simpa using hq

omit [FiniteDimensional ℝ E] in
/-- Ordinary points have dense range in the point-metric cosmic model. -/
theorem denseRange_ordinaryPointToCosmicPoint :
    DenseRange
      (ordinaryPointToCosmicPoint : OrdinaryPointModel E → CosmicPointModel E) := by
  change Dense (range
    (ordinaryPointToCosmicPoint : OrdinaryPointModel E → CosmicPointModel E))
  rw [Metric.dense_iff]
  intro p r hr
  rcases exists_ordinary_pointMetric_approximation p.toCosmicSpace with ⟨x, hx⟩
  have hev := hx.eventually (Iio_mem_nhds hr)
  rcases hev.exists with ⟨n, hn⟩
  refine ⟨ordinaryPointToCosmicPoint ⟨x n⟩, ?_, ⟨⟨x n⟩, rfl⟩⟩
  rw [mem_ball]
  change cosmicPointDistance (cosmicEmbed (x n)) p.toCosmicSpace < r
  exact hn

/-- The cosmic point model, with its explicit metric, is an abstract
completion of the ordinary point-metric space. -/
noncomputable def cosmicPointAbstractCompletion :
    AbstractCompletion (OrdinaryPointModel E) where
  space := CosmicPointModel E
  coe := ordinaryPointToCosmicPoint
  uniformStruct := inferInstance
  complete := inferInstance
  separation := inferInstance
  isUniformInducing :=
    isometry_ordinaryPointToCosmicPoint.isUniformEmbedding.isUniformInducing
  dense := denseRange_ordinaryPointToCosmicPoint

/-- Exercise 4.48: Mathlib's uniform completion of the ordinary point metric
is uniformly equivalent to the cosmic point model. -/
noncomputable def completionOrdinaryPointModelEquivCosmic :
    UniformSpace.Completion (OrdinaryPointModel E) ≃ᵤ CosmicPointModel E :=
  AbstractCompletion.compareEquiv UniformSpace.Completion.cPkg
    (cosmicPointAbstractCompletion (E := E))

end FiniteDimensional

end PointCompletion

section CosmicHausdorffFormula

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

local instance : CompactSpace (CosmicSpace E) :=
  isCompact_iff_compactSpace.mp (isCompact_cosmicSpace (E := E))

omit [FiniteDimensional ℝ E] in
/-- The ray-segment map is continuous in the original cosmic topology. -/
theorem continuous_cosmicRaySegment :
    Continuous (cosmicRaySegment : CosmicSpace E →
      TopologicalSpace.NonemptyCompacts (CosmicRayAmbient E)) := by
  rw [continuous_iff_seqContinuous]
  intro p q hp
  rw [tendsto_iff_dist_tendsto_zero]
  simpa only [cosmicPointDistance] using
    (tendsto_cosmicPointDistance_iff.mp hp)

/-- The compact family of ray segments indexed by a closed cosmic set. -/
def cosmicRaySegmentsSet
    (S : TopologicalSpace.Closeds (CosmicSpace E)) :
    Set (TopologicalSpace.NonemptyCompacts (CosmicRayAmbient E)) :=
  cosmicRaySegment '' (S : Set (CosmicSpace E))

theorem isCompact_cosmicRaySegmentsSet
    (S : TopologicalSpace.Closeds (CosmicSpace E)) :
    IsCompact (cosmicRaySegmentsSet S) :=
  S.isClosed.isCompact.image continuous_cosmicRaySegment

omit [FiniteDimensional ℝ E] in
theorem cosmicRaySegmentsSet_nonempty
    {S : TopologicalSpace.Closeds (CosmicSpace E)}
    (hS : (S : Set (CosmicSpace E)).Nonempty) :
    (cosmicRaySegmentsSet S).Nonempty :=
  hS.image cosmicRaySegment

/-- Point-to-set distance generated by the point metric of Exercise 4.48. -/
noncomputable def cosmicPointToSetDistance
    (p : CosmicSpace E) (S : TopologicalSpace.Closeds (CosmicSpace E)) : ℝ :=
  infDist (cosmicRaySegment p) (cosmicRaySegmentsSet S)

omit [FiniteDimensional ℝ E] in
theorem cosmicPointToSetDistance_eq_zero_of_mem
    {p : CosmicSpace E} {S : TopologicalSpace.Closeds (CosmicSpace E)}
    (hp : p ∈ S) :
    cosmicPointToSetDistance p S = 0 := by
  apply infDist_zero_of_mem
  exact ⟨p, hp, rfl⟩

omit [FiniteDimensional ℝ E] in
theorem continuous_cosmicPointToSetDistance
    (S : TopologicalSpace.Closeds (CosmicSpace E)) :
    Continuous (fun p : CosmicSpace E ↦ cosmicPointToSetDistance p S) := by
  exact (continuous_infDist_pt (cosmicRaySegmentsSet S)).comp
    continuous_cosmicRaySegment

omit [FiniteDimensional ℝ E] in
theorem continuous_abs_cosmicPointToSetDistance_sub
    (S T : TopologicalSpace.Closeds (CosmicSpace E)) :
    Continuous (fun p : CosmicSpace E ↦
      |cosmicPointToSetDistance p S - cosmicPointToSetDistance p T|) :=
  ((continuous_cosmicPointToSetDistance S).sub
    (continuous_cosmicPointToSetDistance T)).abs

private theorem hausdorffEDist_raySegments_ne_top
    (S T : TopologicalSpace.Closeds (CosmicSpace E))
    (hS : (S : Set (CosmicSpace E)).Nonempty)
    (hT : (T : Set (CosmicSpace E)).Nonempty) :
    hausdorffEDist (cosmicRaySegmentsSet S) (cosmicRaySegmentsSet T) ≠ ⊤ :=
  hausdorffEDist_ne_top_of_nonempty_of_bounded
    (cosmicRaySegmentsSet_nonempty hS) (cosmicRaySegmentsSet_nonempty hT)
    (isCompact_cosmicRaySegmentsSet S).isBounded
    (isCompact_cosmicRaySegmentsSet T).isBounded

/-- The Hausdorff metric generated by the cosmic point metric has the
distance-function supremum formula appearing in 4(19), initially over all
cosmic points. -/
theorem hausdorffDist_raySegments_eq_iSup_pointToSetDistance
    (S T : TopologicalSpace.Closeds (CosmicSpace E))
    (hS : (S : Set (CosmicSpace E)).Nonempty)
    (hT : (T : Set (CosmicSpace E)).Nonempty) :
    hausdorffDist (cosmicRaySegmentsSet S) (cosmicRaySegmentsSet T) =
      ⨆ p : CosmicSpace E,
        |cosmicPointToSetDistance p S - cosmicPointToSetDistance p T| := by
  let H := hausdorffDist (cosmicRaySegmentsSet S) (cosmicRaySegmentsSet T)
  let f : CosmicSpace E → ℝ := fun p ↦
    |cosmicPointToSetDistance p S - cosmicPointToSetDistance p T|
  have hfin := hausdorffEDist_raySegments_ne_top S T hS hT
  have hf_le : ∀ p, f p ≤ H := by
    intro p
    rw [abs_le]
    constructor
    · have h := infDist_le_infDist_add_hausdorffDist
          (x := cosmicRaySegment p) (s := cosmicRaySegmentsSet S)
          (t := cosmicRaySegmentsSet T) hfin
      dsimp only [f, cosmicPointToSetDistance, H]
      linarith
    · have h := infDist_le_infDist_add_hausdorffDist
          (x := cosmicRaySegment p) (s := cosmicRaySegmentsSet T)
          (t := cosmicRaySegmentsSet S) (by simpa [hausdorffEDist_comm] using hfin)
      rw [hausdorffDist_comm] at h
      dsimp only [f, cosmicPointToSetDistance, H]
      linarith
  have hfBdd : BddAbove (range f) := ⟨H, forall_mem_range.mpr hf_le⟩
  letI : Nonempty (CosmicSpace E) := ⟨⟨0, by simp⟩⟩
  apply le_antisymm
  · apply hausdorffDist_le_of_infDist
    · exact le_ciSup_of_le hfBdd (⟨0, by simp⟩ : CosmicSpace E) (abs_nonneg _)
    · intro z hz
      rcases hz with ⟨p, hp, rfl⟩
      have hzS : cosmicPointToSetDistance p S = 0 :=
        cosmicPointToSetDistance_eq_zero_of_mem hp
      change cosmicPointToSetDistance p T ≤ ⨆ q, f q
      calc
        cosmicPointToSetDistance p T = f p := by
          dsimp only [f]
          rw [hzS, zero_sub, abs_neg,
            abs_of_nonneg (show 0 ≤ cosmicPointToSetDistance p T from infDist_nonneg)]
        _ ≤ ⨆ q, f q := le_ciSup hfBdd p
    · intro z hz
      rcases hz with ⟨p, hp, rfl⟩
      have hzT : cosmicPointToSetDistance p T = 0 :=
        cosmicPointToSetDistance_eq_zero_of_mem hp
      change cosmicPointToSetDistance p S ≤ ⨆ q, f q
      calc
        cosmicPointToSetDistance p S = f p := by
          dsimp only [f]
          rw [hzT, sub_zero,
            abs_of_nonneg (show 0 ≤ cosmicPointToSetDistance p S from infDist_nonneg)]
        _ ≤ ⨆ q, f q := le_ciSup hfBdd p
  · exact ciSup_le hf_le

/-- The supremum in 4(19) can be taken over ordinary embedded points because
ordinary points are dense and the distance-function difference is continuous
on cosmic space. -/
theorem iSup_pointToSetDistance_eq_iSup_cosmicEmbed
    (S T : TopologicalSpace.Closeds (CosmicSpace E)) :
    (⨆ p : CosmicSpace E,
        |cosmicPointToSetDistance p S - cosmicPointToSetDistance p T|) =
      ⨆ x : E,
        |cosmicPointToSetDistance (cosmicEmbed x) S -
          cosmicPointToSetDistance (cosmicEmbed x) T| := by
  let f : CosmicSpace E → ℝ := fun p ↦
    |cosmicPointToSetDistance p S - cosmicPointToSetDistance p T|
  let g : E → ℝ := fun x ↦ f (cosmicEmbed x)
  have hfcont : Continuous f :=
    continuous_abs_cosmicPointToSetDistance_sub S T
  have hfBdd : BddAbove (range f) := by
    simpa only [image_univ] using
      isCompact_univ.bddAbove_image hfcont.continuousOn
  have hgsub : range g ⊆ range f := by
    rintro y ⟨x, rfl⟩
    exact ⟨cosmicEmbed x, rfl⟩
  have hgBdd : BddAbove (range g) := hfBdd.mono hgsub
  letI : Nonempty (CosmicSpace E) := ⟨⟨0, by simp⟩⟩
  change (⨆ p, f p) = ⨆ x, g x
  apply le_antisymm
  · apply ciSup_le
    intro p
    rcases exists_ordinary_pointMetric_approximation p with ⟨x, hx⟩
    have hxcosmic : Tendsto (fun n ↦ cosmicEmbed (x n)) atTop (nhds p) :=
      tendsto_cosmicPointDistance_iff.mpr hx
    have hfx : Tendsto (fun n ↦ g (x n)) atTop (nhds (f p)) :=
      hfcont.continuousAt.tendsto.comp hxcosmic
    exact le_of_tendsto hfx <| Eventually.of_forall fun n ↦
      le_ciSup hgBdd (x n)
  · exact ciSup_le fun x ↦ le_ciSup hfBdd (cosmicEmbed x)

/-- Formula 4(19) for the Hausdorff metric generated by the cosmic point
metric, with the supremum taken exactly over ordinary points. -/
theorem hausdorffDist_raySegments_eq_iSup_cosmicEmbed
    (S T : TopologicalSpace.Closeds (CosmicSpace E))
    (hS : (S : Set (CosmicSpace E)).Nonempty)
    (hT : (T : Set (CosmicSpace E)).Nonempty) :
    hausdorffDist (cosmicRaySegmentsSet S) (cosmicRaySegmentsSet T) =
      ⨆ x : E,
        |cosmicPointToSetDistance (cosmicEmbed x) S -
          cosmicPointToSetDistance (cosmicEmbed x) T| := by
  rw [hausdorffDist_raySegments_eq_iSup_pointToSetDistance S T hS hT,
    iSup_pointToSetDistance_eq_iSup_cosmicEmbed]

omit [FiniteDimensional ℝ E] in
theorem cosmicPointDistance_le_one (p q : CosmicSpace E) :
    cosmicPointDistance p q ≤ 1 := by
  rw [cosmicPointDistance_eq_bookRaySine, bookRaySineDistance]
  split_ifs
  · exact Real.sin_le_one _
  · exact le_rfl

omit [FiniteDimensional ℝ E] in
theorem cosmicPointDistance_le_dist_representative_smul
    (p q : CosmicSpace E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    cosmicPointDistance p q ≤
      dist (cosmicRayRepresentative p) (t • cosmicRayRepresentative q) := by
  rw [cosmicPointDistance_eq_bookRaySine]
  exact raySine_le_dist_unit_to_ray
    (norm_cosmicRayRepresentative p) (norm_cosmicRayRepresentative q) ht

private theorem mem_cosmicConeTruncation_of_mem_raySegment
    {S : TopologicalSpace.Closeds (CosmicSpace E)}
    {p : CosmicSpace E} (hp : p ∈ S) {z : CosmicRayAmbient E}
    (hz : z ∈ cosmicRaySegment p) :
    z ∈ cosmicConeTruncation S := by
  change z ∈ segment ℝ 0 (cosmicRayRepresentative p) at hz
  rw [segment_eq_image] at hz
  rcases hz with ⟨t, ht, rfl⟩
  exact mem_cosmicConeTruncation_iff.mpr
    (Or.inr ⟨p, hp, t, ht, by simp⟩)

private theorem hausdorffEDist_cosmicConeTruncation_ne_top
    (S T : TopologicalSpace.Closeds (CosmicSpace E)) :
    hausdorffEDist (cosmicConeTruncation S : Set (CosmicRayAmbient E))
      (cosmicConeTruncation T : Set (CosmicRayAmbient E)) ≠ ⊤ :=
  hausdorffEDist_ne_top_of_nonempty_of_bounded
    (cosmicConeTruncation S).nonempty (cosmicConeTruncation T).nonempty
    (cosmicConeTruncation S).isCompact.isBounded
    (cosmicConeTruncation T).isCompact.isBounded

/-- The unit-truncation set metric is exactly the Hausdorff metric generated
by the point metric on nonempty closed cosmic sets. -/
theorem cosmicSetDistance_eq_hausdorffDist_raySegments
    (S T : TopologicalSpace.Closeds (CosmicSpace E))
    (hS : (S : Set (CosmicSpace E)).Nonempty)
    (hT : (T : Set (CosmicSpace E)).Nonempty) :
    cosmicSetDistance S T =
      hausdorffDist (cosmicRaySegmentsSet S) (cosmicRaySegmentsSet T) := by
  let Hc := hausdorffDist
    (cosmicConeTruncation S : Set (CosmicRayAmbient E))
    (cosmicConeTruncation T : Set (CosmicRayAmbient E))
  let Hp := hausdorffDist (cosmicRaySegmentsSet S) (cosmicRaySegmentsSet T)
  have hfinC := hausdorffEDist_cosmicConeTruncation_ne_top S T
  have hfinP := hausdorffEDist_raySegments_ne_top S T hS hT
  have hHp0 : 0 ≤ Hp := by
    change 0 ≤ hausdorffDist (cosmicRaySegmentsSet S) (cosmicRaySegmentsSet T)
    exact hausdorffDist_nonneg
  have hle_cp : Hc ≤ Hp := by
    apply hausdorffDist_le_of_mem_dist hHp0
    · intro z hz
      rw [show z ∈ (cosmicConeTruncation S : Set (CosmicRayAmbient E)) ↔ _ from
        (mem_cosmicConeTruncation_iff (S := S) (z := z))] at hz
      rcases hz with rfl | ⟨p, hp, t, ht, rfl⟩
      · exact ⟨0, (mem_cosmicConeTruncation_iff.mpr <| Or.inl rfl), by simpa using hHp0⟩
      · have hpSeg : cosmicRaySegment p ∈ cosmicRaySegmentsSet S :=
          ⟨p, hp, rfl⟩
        rcases (isCompact_cosmicRaySegmentsSet T).exists_infDist_eq_dist
            (cosmicRaySegmentsSet_nonempty hT) (cosmicRaySegment p) with
          ⟨B, hBT, hBdist⟩
        rcases hBT with ⟨q, hq, rfl⟩
        have hinf : infDist (cosmicRaySegment p) (cosmicRaySegmentsSet T) ≤ Hp :=
          infDist_le_hausdorffDist_of_mem hpSeg hfinP
        have hseg : dist (cosmicRaySegment p) (cosmicRaySegment q) ≤ Hp := by
          rw [← hBdist]
          exact hinf
        have hzSeg : t • cosmicRayRepresentative p ∈ cosmicRaySegment p := by
          change t • cosmicRayRepresentative p ∈
            segment ℝ 0 (cosmicRayRepresentative p)
          rw [segment_eq_image]
          exact ⟨t, ht, by simp⟩
        rcases (cosmicRaySegment q).isCompact.exists_infDist_eq_dist
            (cosmicRaySegment q).nonempty (t • cosmicRayRepresentative p) with
          ⟨y, hyq, hydist⟩
        refine ⟨y, mem_cosmicConeTruncation_of_mem_raySegment hq hyq, ?_⟩
        calc
          dist (t • cosmicRayRepresentative p) y =
              infDist (t • cosmicRayRepresentative p) (cosmicRaySegment q) :=
            hydist.symm
          _ ≤ hausdorffDist (cosmicRaySegment p : Set _)
              (cosmicRaySegment q : Set _) :=
            infDist_le_hausdorffDist_of_mem hzSeg <|
              hausdorffEDist_ne_top_of_nonempty_of_bounded
                (cosmicRaySegment p).nonempty (cosmicRaySegment q).nonempty
                (cosmicRaySegment p).isCompact.isBounded
                (cosmicRaySegment q).isCompact.isBounded
          _ = dist (cosmicRaySegment p) (cosmicRaySegment q) := by
            rw [Metric.NonemptyCompacts.dist_eq]
          _ ≤ Hp := hseg
    · intro z hz
      rw [show z ∈ (cosmicConeTruncation T : Set (CosmicRayAmbient E)) ↔ _ from
        (mem_cosmicConeTruncation_iff (S := T) (z := z))] at hz
      rcases hz with rfl | ⟨q, hq, t, ht, rfl⟩
      · exact ⟨0, (mem_cosmicConeTruncation_iff.mpr <| Or.inl rfl), by simpa using hHp0⟩
      · have hqSeg : cosmicRaySegment q ∈ cosmicRaySegmentsSet T :=
          ⟨q, hq, rfl⟩
        rcases (isCompact_cosmicRaySegmentsSet S).exists_infDist_eq_dist
            (cosmicRaySegmentsSet_nonempty hS) (cosmicRaySegment q) with
          ⟨A, hAS, hAdist⟩
        rcases hAS with ⟨p, hp, rfl⟩
        have hinf : infDist (cosmicRaySegment q) (cosmicRaySegmentsSet S) ≤ Hp := by
          have hfinP' : hausdorffEDist (cosmicRaySegmentsSet T)
              (cosmicRaySegmentsSet S) ≠ ⊤ := by
            simpa only [hausdorffEDist_comm] using hfinP
          have h := infDist_le_hausdorffDist_of_mem hqSeg hfinP'
          rw [hausdorffDist_comm] at h
          exact h
        have hseg : dist (cosmicRaySegment q) (cosmicRaySegment p) ≤ Hp := by
          rw [← hAdist]
          exact hinf
        have hzSeg : t • cosmicRayRepresentative q ∈ cosmicRaySegment q := by
          change t • cosmicRayRepresentative q ∈
            segment ℝ 0 (cosmicRayRepresentative q)
          rw [segment_eq_image]
          exact ⟨t, ht, by simp⟩
        rcases (cosmicRaySegment p).isCompact.exists_infDist_eq_dist
            (cosmicRaySegment p).nonempty (t • cosmicRayRepresentative q) with
          ⟨y, hyp, hydist⟩
        refine ⟨y, mem_cosmicConeTruncation_of_mem_raySegment hp hyp, ?_⟩
        calc
          dist (t • cosmicRayRepresentative q) y =
              infDist (t • cosmicRayRepresentative q) (cosmicRaySegment p) :=
            hydist.symm
          _ ≤ hausdorffDist (cosmicRaySegment q : Set _)
              (cosmicRaySegment p : Set _) :=
            infDist_le_hausdorffDist_of_mem hzSeg <|
              hausdorffEDist_ne_top_of_nonempty_of_bounded
                (cosmicRaySegment q).nonempty (cosmicRaySegment p).nonempty
                (cosmicRaySegment q).isCompact.isBounded
                (cosmicRaySegment p).isCompact.isBounded
          _ = dist (cosmicRaySegment q) (cosmicRaySegment p) := by
            rw [Metric.NonemptyCompacts.dist_eq]
          _ ≤ Hp := hseg
  have hle_pc : Hp ≤ Hc := by
    apply hausdorffDist_le_of_mem_dist hausdorffDist_nonneg
    · intro A hAS
      rcases hAS with ⟨p, hp, rfl⟩
      have hup : cosmicRayRepresentative p ∈ cosmicConeTruncation S :=
        mem_cosmicConeTruncation_iff.mpr <|
          Or.inr ⟨p, hp, 1, right_mem_Icc.mpr zero_le_one, by simp⟩
      rcases (cosmicConeTruncation T).isCompact.exists_infDist_eq_dist
          (cosmicConeTruncation T).nonempty (cosmicRayRepresentative p) with
        ⟨y, hyT, hydist⟩
      have hy_le : dist (cosmicRayRepresentative p) y ≤ Hc := by
        rw [← hydist]
        exact infDist_le_hausdorffDist_of_mem hup hfinC
      rw [show y ∈ (cosmicConeTruncation T : Set (CosmicRayAmbient E)) ↔ _ from
        (mem_cosmicConeTruncation_iff (S := T) (z := y))] at hyT
      rcases hyT with rfl | ⟨q, hq, t, ht, rfl⟩
      · rcases hT with ⟨q, hq⟩
        refine ⟨cosmicRaySegment q, ⟨q, hq, rfl⟩, ?_⟩
        change cosmicPointDistance p q ≤ Hc
        calc
          cosmicPointDistance p q ≤ 1 := cosmicPointDistance_le_one p q
          _ = dist (cosmicRayRepresentative p) 0 := by
            simp [norm_cosmicRayRepresentative]
          _ ≤ Hc := hy_le
      · refine ⟨cosmicRaySegment q, ⟨q, hq, rfl⟩, ?_⟩
        change cosmicPointDistance p q ≤ Hc
        exact (cosmicPointDistance_le_dist_representative_smul p q ht).trans hy_le
    · intro B hBT
      rcases hBT with ⟨q, hq, rfl⟩
      have huq : cosmicRayRepresentative q ∈ cosmicConeTruncation T :=
        mem_cosmicConeTruncation_iff.mpr <|
          Or.inr ⟨q, hq, 1, right_mem_Icc.mpr zero_le_one, by simp⟩
      rcases (cosmicConeTruncation S).isCompact.exists_infDist_eq_dist
          (cosmicConeTruncation S).nonempty (cosmicRayRepresentative q) with
        ⟨y, hyS, hydist⟩
      have hy_le : dist (cosmicRayRepresentative q) y ≤ Hc := by
        rw [← hydist]
        have hfinC' : hausdorffEDist
            (cosmicConeTruncation T : Set (CosmicRayAmbient E))
            (cosmicConeTruncation S : Set (CosmicRayAmbient E)) ≠ ⊤ := by
          simpa only [hausdorffEDist_comm] using hfinC
        have hinf := infDist_le_hausdorffDist_of_mem huq hfinC'
        rw [hausdorffDist_comm] at hinf
        exact hinf
      rw [show y ∈ (cosmicConeTruncation S : Set (CosmicRayAmbient E)) ↔ _ from
        (mem_cosmicConeTruncation_iff (S := S) (z := y))] at hyS
      rcases hyS with rfl | ⟨p, hp, t, ht, rfl⟩
      · rcases hS with ⟨p, hp⟩
        refine ⟨cosmicRaySegment p, ⟨p, hp, rfl⟩, ?_⟩
        change cosmicPointDistance q p ≤ Hc
        calc
          cosmicPointDistance q p ≤ 1 := cosmicPointDistance_le_one q p
          _ = dist (cosmicRayRepresentative q) 0 := by
            simp [norm_cosmicRayRepresentative]
          _ ≤ Hc := hy_le
      · refine ⟨cosmicRaySegment p, ⟨p, hp, rfl⟩, ?_⟩
        change cosmicPointDistance q p ≤ Hc
        exact (cosmicPointDistance_le_dist_representative_smul q p ht).trans hy_le
  change Hc = Hp
  exact le_antisymm hle_cp hle_pc

/-- Formula 4(19) for the cosmic set metric itself. -/
theorem cosmicSetDistance_eq_iSup_cosmicEmbed
    (S T : TopologicalSpace.Closeds (CosmicSpace E))
    (hS : (S : Set (CosmicSpace E)).Nonempty)
    (hT : (T : Set (CosmicSpace E)).Nonempty) :
    cosmicSetDistance S T =
      ⨆ x : E,
        |cosmicPointToSetDistance (cosmicEmbed x) S -
          cosmicPointToSetDistance (cosmicEmbed x) T| := by
  rw [cosmicSetDistance_eq_hausdorffDist_raySegments S T hS hT,
    hausdorffDist_raySegments_eq_iSup_cosmicEmbed S T hS hT]

end CosmicHausdorffFormula

end RW
