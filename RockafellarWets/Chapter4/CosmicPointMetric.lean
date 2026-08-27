/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: The Cosmic Point Metric

This file gives the ray-segment realization of the point metric in Exercise
4.48.  Working with unit segments is the coordinate-free form of the book's
piecewise `sin(angle)` formula and is also the form used in its proof guide.
-/

import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Topology.MetricSpace.BundledFun
import Mathlib.Topology.MetricSpace.Closeds
import RockafellarWets.Chapter3.CosmicSpace

open Filter Metric Set Topology

namespace RW

section CosmicPointMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Euclidean ray-space ambient used in 4.48.  `WithLp 2` equips the
product with the square-sum norm, rather than Lean's default max norm. -/
abbrev CosmicRayAmbient (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  WithLp 2 (E × ℝ)

/-- The unit lower-hemisphere representative of a cosmic point. -/
noncomputable def cosmicRayRepresentative (p : CosmicSpace E) :
    CosmicRayAmbient E :=
  WithLp.toLp 2 ((p : E), -Real.sqrt (1 - ‖(p : E)‖ ^ 2))

theorem one_sub_norm_sq_nonneg (p : CosmicSpace E) :
    0 ≤ 1 - ‖(p : E)‖ ^ 2 := by
  have hp : ‖(p : E)‖ ≤ 1 := mem_closedBall_zero_iff.mp p.property
  nlinarith [norm_nonneg (p : E)]

@[simp]
theorem norm_cosmicRayRepresentative (p : CosmicSpace E) :
    ‖cosmicRayRepresentative p‖ = 1 := by
  have hsq : ‖cosmicRayRepresentative p‖ ^ 2 = 1 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    simp only [cosmicRayRepresentative, WithLp.toLp_fst, WithLp.toLp_snd,
      norm_neg, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (one_sub_norm_sq_nonneg p)]
    ring
  nlinarith [norm_nonneg (cosmicRayRepresentative p)]

theorem continuous_cosmicRayRepresentative :
    Continuous (cosmicRayRepresentative : CosmicSpace E → CosmicRayAmbient E) := by
  apply (WithLp.homeomorphProd 2 E ℝ).symm.continuous.comp
  apply Continuous.prodMk continuous_subtype_val
  exact (continuous_const.sub (continuous_subtype_val.norm.pow 2)).sqrt.neg

theorem injective_cosmicRayRepresentative :
    Function.Injective (cosmicRayRepresentative : CosmicSpace E → CosmicRayAmbient E) := by
  intro p q hpq
  apply Subtype.ext
  have := congrArg WithLp.fst hpq
  simpa only [cosmicRayRepresentative, WithLp.toLp_fst] using this

/-- The representative of an ordinary point is the normalization of the
lower ray `(x, -1)` used in formula 4(16). -/
theorem cosmicRayRepresentative_cosmicEmbed (x : E) :
    cosmicRayRepresentative (cosmicEmbed x) =
      WithLp.toLp 2 (cosmicScale x • x, -cosmicScale x) := by
  have hsqrt :
      Real.sqrt (1 - ‖cosmicScale x • x‖ ^ 2) =
        cosmicScale x := by
    have hsq := cosmicScale_sq_add_norm_sq x
    have harg : 1 - ‖cosmicScale x • x‖ ^ 2 = cosmicScale x ^ 2 := by
      linarith
    rw [harg, Real.sqrt_sq_eq_abs, abs_of_pos (cosmicScale_pos x)]
  simp only [cosmicRayRepresentative, coe_cosmicEmbed_eq_cosmicScale_smul,
    hsqrt]

/-- The representative of a direction is the horizontal unit ray `(u, 0)`
used in formula 4(17). -/
@[simp]
theorem cosmicRayRepresentative_cosmicDirection (u : CosmicBoundary E) :
    cosmicRayRepresentative (cosmicDirection u) =
      WithLp.toLp 2 ((u : E), 0) := by
  simp only [cosmicRayRepresentative, coe_cosmicDirection,
    mem_sphere_zero_iff_norm.mp u.property, one_pow, sub_self,
    Real.sqrt_zero, neg_zero]

/-- The compact unit segment on the ray representing `p`. -/
noncomputable def cosmicRaySegment (p : CosmicSpace E) :
    TopologicalSpace.NonemptyCompacts (CosmicRayAmbient E) where
  carrier := segment ℝ 0 (cosmicRayRepresentative p)
  isCompact' := by
    rw [segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  nonempty' := ⟨0, left_mem_segment ℝ _ _⟩

@[simp]
theorem coe_cosmicRaySegment (p : CosmicSpace E) :
    (cosmicRaySegment p : Set (CosmicRayAmbient E)) =
      segment ℝ 0 (cosmicRayRepresentative p) :=
  rfl

theorem endpoint_eq_of_mem_segment_of_norm_eq_one
    {u v : CosmicRayAmbient E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hmem : u ∈ segment ℝ 0 v) : u = v := by
  rw [segment_eq_image] at hmem
  rcases hmem with ⟨t, ht, hut⟩
  simp only [smul_zero, zero_add] at hut
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t = 1 := by
    have hnorm := congrArg norm hut
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0, hv, mul_one, hu] at hnorm
    linarith
  simpa [ht1] using hut.symm

theorem injective_cosmicRaySegment :
    Function.Injective (cosmicRaySegment : CosmicSpace E →
      TopologicalSpace.NonemptyCompacts (CosmicRayAmbient E)) := by
  intro p q hpq
  apply injective_cosmicRayRepresentative
  apply endpoint_eq_of_mem_segment_of_norm_eq_one
    (norm_cosmicRayRepresentative p) (norm_cosmicRayRepresentative q)
  have hp : cosmicRayRepresentative p ∈
      (cosmicRaySegment p : Set (CosmicRayAmbient E)) := right_mem_segment ℝ _ _
  rw [hpq] at hp
  exact hp

/-- Formula 4(16)--4(17), in the equivalent ray-segment form from the guide
to Exercise 4.48. -/
noncomputable def cosmicPointDistance (p q : CosmicSpace E) : ℝ :=
  dist (cosmicRaySegment p) (cosmicRaySegment q)

theorem cosmicPointDistance_nonneg (p q : CosmicSpace E) :
    0 ≤ cosmicPointDistance p q :=
  dist_nonneg

@[simp]
theorem cosmicPointDistance_self (p : CosmicSpace E) :
    cosmicPointDistance p p = 0 :=
  dist_self _

theorem cosmicPointDistance_comm (p q : CosmicSpace E) :
    cosmicPointDistance p q = cosmicPointDistance q p :=
  dist_comm _ _

theorem cosmicPointDistance_triangle (p q r : CosmicSpace E) :
    cosmicPointDistance p r ≤
      cosmicPointDistance p q + cosmicPointDistance q r :=
  dist_triangle _ _ _

@[simp]
theorem cosmicPointDistance_eq_zero_iff {p q : CosmicSpace E} :
    cosmicPointDistance p q = 0 ↔ p = q := by
  rw [cosmicPointDistance, dist_eq_zero]
  exact injective_cosmicRaySegment.eq_iff

/-- The metric axioms in Exercise 4.48, packaged without replacing the
closed-ball model's existing metric instance. -/
noncomputable def cosmicPointMetric : PseudoMetric (CosmicSpace E) ℝ where
  toFun := cosmicPointDistance
  refl' := cosmicPointDistance_self
  symm' := cosmicPointDistance_comm
  triangle' := cosmicPointDistance_triangle

/-- The ray-segment metric is bounded by the endpoint distance. -/
theorem cosmicPointDistance_le_dist_representative (p q : CosmicSpace E) :
    cosmicPointDistance p q ≤
      dist (cosmicRayRepresentative p) (cosmicRayRepresentative q) := by
  rw [cosmicPointDistance, Metric.NonemptyCompacts.dist_eq]
  apply hausdorffDist_le_of_mem_dist dist_nonneg
  · intro x hx
    change x ∈ segment ℝ 0 (cosmicRayRepresentative p) at hx
    rw [segment_eq_image] at hx
    rcases hx with ⟨t, ht, rfl⟩
    refine ⟨t • cosmicRayRepresentative q, ?_, ?_⟩
    · change t • cosmicRayRepresentative q ∈
          segment ℝ 0 (cosmicRayRepresentative q)
      rw [segment_eq_image]
      exact ⟨t, ht, by simp⟩
    · simp only [smul_zero, zero_add]
      rw [dist_eq_norm, ← smul_sub]
      calc
        ‖t • (cosmicRayRepresentative p - cosmicRayRepresentative q)‖ =
            t * ‖cosmicRayRepresentative p - cosmicRayRepresentative q‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        _ ≤ ‖cosmicRayRepresentative p - cosmicRayRepresentative q‖ := by
          exact mul_le_of_le_one_left (norm_nonneg _) ht.2
        _ = dist (cosmicRayRepresentative p) (cosmicRayRepresentative q) := by
          rw [dist_eq_norm]
  · intro x hx
    change x ∈ segment ℝ 0 (cosmicRayRepresentative q) at hx
    rw [segment_eq_image] at hx
    rcases hx with ⟨t, ht, rfl⟩
    refine ⟨t • cosmicRayRepresentative p, ?_, ?_⟩
    · change t • cosmicRayRepresentative p ∈
          segment ℝ 0 (cosmicRayRepresentative p)
      rw [segment_eq_image]
      exact ⟨t, ht, by simp⟩
    · simp only [smul_zero, zero_add]
      rw [dist_eq_norm, ← smul_sub]
      calc
        ‖t • (cosmicRayRepresentative q - cosmicRayRepresentative p)‖ =
            t * ‖cosmicRayRepresentative q - cosmicRayRepresentative p‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        _ ≤ ‖cosmicRayRepresentative q - cosmicRayRepresentative p‖ := by
          exact mul_le_of_le_one_left (norm_nonneg _) ht.2
        _ = ‖cosmicRayRepresentative p - cosmicRayRepresentative q‖ := norm_sub_rev _ _
        _ = dist (cosmicRayRepresentative p) (cosmicRayRepresentative q) := by
          rw [dist_eq_norm]

/-- The ambient closed-ball distance is controlled by the distance between
the unit ray representatives. -/
theorem dist_le_dist_cosmicRayRepresentative (p q : CosmicSpace E) :
    dist p q ≤ dist (cosmicRayRepresentative p) (cosmicRayRepresentative q) := by
  simpa only [cosmicRayRepresentative, WithLp.toLp_fst] using
    (WithLp.dist_fst_le
      (cosmicRayRepresentative p) (cosmicRayRepresentative q))

private theorem dist_representative_le_two_mul_cosmicPointDistance
    (p q : CosmicSpace E) :
    dist (cosmicRayRepresentative p) (cosmicRayRepresentative q) ≤
      2 * cosmicPointDistance p q := by
  let S : Set (CosmicRayAmbient E) := segment ℝ 0 (cosmicRayRepresentative q)
  have hSc : IsCompact S := by
    dsimp only [S]
    rw [segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  have hSne : S.Nonempty := ⟨0, left_mem_segment ℝ _ _⟩
  rcases hSc.exists_infDist_eq_dist hSne (cosmicRayRepresentative p) with
    ⟨z, hzS, hz⟩
  have hinf : infDist (cosmicRayRepresentative p) S ≤ cosmicPointDistance p q := by
    rw [cosmicPointDistance, Metric.NonemptyCompacts.dist_eq]
    exact infDist_le_hausdorffDist_of_mem (right_mem_segment ℝ _ _)
      (hausdorffEDist_ne_top_of_nonempty_of_bounded
        (cosmicRaySegment p).nonempty (cosmicRaySegment q).nonempty
        (cosmicRaySegment p).isCompact.isBounded
        (cosmicRaySegment q).isCompact.isBounded)
  change z ∈ segment ℝ 0 (cosmicRayRepresentative q) at hzS
  rw [segment_eq_image] at hzS
  rcases hzS with ⟨t, ht, rfl⟩
  simp only [smul_zero, zero_add] at hz
  have hnormdiff : |1 - t| ≤
      dist (cosmicRayRepresentative p) (t • cosmicRayRepresentative q) := by
    simpa only [dist_eq_norm, norm_cosmicRayRepresentative, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg ht.1, mul_one] using
        (abs_norm_sub_norm_le (cosmicRayRepresentative p)
          (t • cosmicRayRepresentative q))
  calc
    dist (cosmicRayRepresentative p) (cosmicRayRepresentative q) ≤
        dist (cosmicRayRepresentative p) (t • cosmicRayRepresentative q) +
          dist (t • cosmicRayRepresentative q) (cosmicRayRepresentative q) :=
      dist_triangle _ _ _
    _ = dist (cosmicRayRepresentative p) (t • cosmicRayRepresentative q) +
        |1 - t| := by
      congr 1
      rw [dist_eq_norm]
      have hsub : t • cosmicRayRepresentative q - cosmicRayRepresentative q =
          (t - 1) • cosmicRayRepresentative q := by module
      rw [hsub, norm_smul, Real.norm_eq_abs,
        norm_cosmicRayRepresentative q, mul_one, abs_sub_comm]
    _ ≤ 2 * dist (cosmicRayRepresentative p) (t • cosmicRayRepresentative q) := by
      linarith
    _ = 2 * infDist (cosmicRayRepresentative p) S := by rw [hz]
    _ ≤ 2 * cosmicPointDistance p q := mul_le_mul_of_nonneg_left hinf (by norm_num)

/-- Exercise 4.48: the ray metric induces exactly the existing cosmic
topology.  This sequential form is the metric completion/topology bridge used
by the set-metric results. -/
theorem tendsto_cosmicPointDistance_iff
    {p : ℕ → CosmicSpace E} {q : CosmicSpace E} :
    Tendsto p atTop (nhds q) ↔
      Tendsto (fun n ↦ cosmicPointDistance (p n) q) atTop (nhds 0) := by
  constructor
  · intro hp
    have hrep : Tendsto (fun n ↦ cosmicRayRepresentative (p n)) atTop
        (nhds (cosmicRayRepresentative q)) :=
      (continuous_cosmicRayRepresentative.tendsto q).comp hp
    exact squeeze_zero (fun n ↦ cosmicPointDistance_nonneg _ _)
      (fun n ↦ cosmicPointDistance_le_dist_representative _ _) <| by
        simpa using hrep.dist
          (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ cosmicRayRepresentative q)
            atTop (nhds (cosmicRayRepresentative q)))
  · intro hd
    have hrepDist : Tendsto
        (fun n ↦ dist (cosmicRayRepresentative (p n))
          (cosmicRayRepresentative q)) atTop (nhds 0) :=
      squeeze_zero (fun n ↦ dist_nonneg)
        (fun n ↦ dist_representative_le_two_mul_cosmicPointDistance _ _)
        (by simpa using (tendsto_const_nhds.mul hd :
          Tendsto (fun n ↦ 2 * cosmicPointDistance (p n) q) atTop (nhds (2 * 0))))
    have hrep : Tendsto (fun n ↦ cosmicRayRepresentative (p n)) atTop
        (nhds (cosmicRayRepresentative q)) :=
      tendsto_iff_dist_tendsto_zero.2 hrepDist
    apply tendsto_subtype_rng.mpr
    have hfst := (WithLp.continuous_fst (p := 2) (α := E) (β := ℝ)).tendsto
      (cosmicRayRepresentative q) |>.comp hrep
    simpa only [cosmicRayRepresentative, WithLp.toLp_fst] using hfst

/-- The restriction of the cosmic point distance to ordinary points. -/
noncomputable def ordinaryCosmicPointDistance (x y : E) : ℝ :=
  cosmicPointDistance (cosmicEmbed x) (cosmicEmbed y)

@[simp]
theorem ordinaryCosmicPointDistance_eq_zero_iff {x y : E} :
    ordinaryCosmicPointDistance x y = 0 ↔ x = y := by
  rw [ordinaryCosmicPointDistance, cosmicPointDistance_eq_zero_iff]
  exact injective_cosmicEmbed.eq_iff

/-- The ordinary-point map is isometric for the restricted point distance. -/
theorem ordinaryCosmicPointDistance_isometry (x y : E) :
    cosmicPointDistance (cosmicEmbed x) (cosmicEmbed y) =
      ordinaryCosmicPointDistance x y :=
  rfl

/-- Cauchy sequences for the metric in Exercise 4.48, written independently
of a global replacement of the closed-ball model's metric instance. -/
def CosmicPointCauchy (p : ℕ → CosmicSpace E) : Prop :=
  ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
    cosmicPointDistance (p m) (p n) < ε

/-- Every cosmic point is a point-metric limit of ordinary points.  This is
the density clause in the completion statement of Exercise 4.48. -/
theorem exists_ordinary_pointMetric_approximation (p : CosmicSpace E) :
    ∃ x : ℕ → E,
      Tendsto (fun n ↦ cosmicPointDistance (cosmicEmbed (x n)) p)
        atTop (nhds 0) := by
  rcases cosmicEmbed_or_cosmicDirection p with ⟨x, rfl⟩ | ⟨u, rfl⟩
  · refine ⟨fun _ ↦ x, ?_⟩
    simp
  · refine ⟨cosmicRadialOrdinary u, ?_⟩
    exact tendsto_cosmicPointDistance_iff.mp (tendsto_cosmicRadialOrdinary u)

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- Every Cauchy sequence for the metric in Exercise 4.48 converges for that
metric.  Together with `ordinaryCosmicPointDistance_isometry` and
`exists_ordinary_pointMetric_approximation`, this gives the completion of the
ordinary point-metric space as `CosmicSpace E`. -/
theorem exists_pointMetric_limit_of_cauchy
    {p : ℕ → CosmicSpace E} (hp : CosmicPointCauchy p) :
    ∃ q : CosmicSpace E,
      Tendsto (fun n ↦ cosmicPointDistance (p n) q) atTop (nhds 0) := by
  have hp' : CauchySeq p := Metric.cauchySeq_iff.mpr fun ε hε ↦ by
    rcases hp (ε / 2) (half_pos hε) with ⟨N, hN⟩
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    calc
      dist (p m) (p n) ≤
          dist (cosmicRayRepresentative (p m))
            (cosmicRayRepresentative (p n)) :=
        dist_le_dist_cosmicRayRepresentative _ _
      _ ≤ 2 * cosmicPointDistance (p m) (p n) :=
        dist_representative_le_two_mul_cosmicPointDistance _ _
      _ < ε := by linarith [hN m hm n hn]
  rcases cauchySeq_tendsto_of_complete hp' with ⟨q, hq⟩
  exact ⟨q, tendsto_cosmicPointDistance_iff.mp hq⟩

end FiniteDimensional

end CosmicPointMetric

end RW
