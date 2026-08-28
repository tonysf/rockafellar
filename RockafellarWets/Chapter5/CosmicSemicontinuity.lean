/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Cosmic Semicontinuity

Proposition 5.27, together with the version of Exercise 4.20 that it needs.

The book says 5.27 "is obvious from 4.20", but 4.20 is available here only
for sequences: its proof extracts convergent subsequences, and there are no
subsequences along a neighborhood filter.  The whole of Exercise 4.20 is
therefore reproved along an arbitrary index filter.

The replacement for subsequence extraction is a pair of *neighborhood
transfer* lemmas.  Near a direction point `dir u`, the mixed cosmic set
`C ∪ dir K` and the purely ordinary set `C ∪ K` are interchangeable: a
direction of the cone `K` is approximated by faraway ordinary points of `K`,
and conversely an ordinary point close enough to the boundary is close to
the direction it points in.  Each transfer shrinks one neighborhood to
another, so it applies verbatim under `∃ᶠ` and under `∀ᶠ`, which is what
makes the outer and inner halves come out together.

The printed inner condition of 5.27 does not agree with 4.20 and is
corrected here; see `not_svIscAt_cosmicSet_of_printed_condition`.
-/

import RockafellarWets.Chapter5.HorizonSetLimitsAlong
import RockafellarWets.Chapter5.Semicontinuity

open Filter Metric Set Topology

namespace RW

section CosmicGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The cosmic distance from an ordinary point to the direction it points in
is exactly how far its cosmic norm falls short of one. -/
theorem dist_cosmicEmbed_cosmicDirectionOf {y : E} (hy : y ≠ 0) :
    dist (cosmicEmbed y) (cosmicDirection (cosmicDirectionOf y hy)) =
      1 - ‖((cosmicEmbed y : CosmicSpace E) : E)‖ := by
  have hs := cosmicScale_pos y
  have hny : (0 : ℝ) < ‖y‖ := norm_pos_iff.2 hy
  have hnorm : ‖((cosmicEmbed y : CosmicSpace E) : E)‖ = cosmicScale y * ‖y‖ := by
    rw [coe_cosmicEmbed_eq_cosmicScale_smul, norm_smul_of_nonneg hs.le]
  have hlt : cosmicScale y * ‖y‖ < 1 := hnorm ▸ norm_cosmicEmbed_lt_one y
  have hinv : ‖y‖⁻¹ * ‖y‖ = 1 := inv_mul_cancel₀ hny.ne'
  have hle : cosmicScale y - ‖y‖⁻¹ ≤ 0 := by nlinarith
  rw [Subtype.dist_eq, coe_cosmicDirection, coe_cosmicDirectionOf,
    NormedSpace.normalize, coe_cosmicEmbed_eq_cosmicScale_smul, dist_eq_norm,
    ← sub_smul, norm_smul, Real.norm_eq_abs, abs_of_nonpos hle,
    norm_smul_of_nonneg hs.le]
  nlinarith

/-- Normalization is continuous away from the origin, so every neighborhood
of a unit vector contains a neighborhood on which normalization stays inside
a prescribed neighborhood. -/
theorem normalize_mem_nhds {u : E} (hu : ‖u‖ = 1) {V : Set E} (hV : V ∈ 𝓝 u) :
    {y : E | y ≠ 0 ∧ ‖y‖⁻¹ • y ∈ V} ∈ 𝓝 u := by
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu
    exact zero_ne_one hu
  have hcont : ContinuousAt (fun y : E ↦ ‖y‖⁻¹ • y) u :=
    ((continuous_norm.continuousAt).inv₀ (by rw [hu]; exact one_ne_zero)).smul
      continuousAt_id
  have hmem : (fun y : E ↦ ‖y‖⁻¹ • y) ⁻¹' V ∈ 𝓝 u :=
    hcont.preimage_mem_nhds (by simpa [hu] using hV)
  have hne : ({0}ᶜ : Set E) ∈ 𝓝 u :=
    isOpen_compl_singleton.mem_nhds (by simpa using hu0)
  filter_upwards [hmem, hne] with y hy hy0
  exact ⟨by simpa using hy0, hy⟩

/-- The radial approximants of a direction of a cone stay in that cone. -/
theorem cosmicRadialOrdinary_mem_of_isCone {K : Set E} (hK : IsCone K)
    {u : CosmicBoundary E} (hu : (u : E) ∈ K) (n : ℕ) :
    cosmicRadialOrdinary u n ∈ K := by
  have hs := cosmicScale_pos (cosmicRadialOrdinary u n)
  have hcoe : cosmicScale (cosmicRadialOrdinary u n) • cosmicRadialOrdinary u n =
      cosmicRadialCoefficient n • (u : E) := by
    rw [← coe_cosmicEmbed_eq_cosmicScale_smul]
    exact coe_cosmicEmbed_cosmicRadialOrdinary u n
  have hzeq : cosmicRadialOrdinary u n =
      (cosmicRadialCoefficient n / cosmicScale (cosmicRadialOrdinary u n)) • (u : E) := by
    rw [div_eq_inv_mul, mul_smul, ← hcoe, inv_smul_smul₀ hs.ne']
  rcases (cosmicRadialCoefficient_nonneg n).eq_or_lt with h0 | hpos
  · rw [hzeq, ← h0, zero_div, zero_smul]
    exact hK.1
  · rw [hzeq]
    exact hK.smul_mem hu (by positivity)

/-- **Neighborhood transfer, mixed to ordinary.**  Near a direction point the
directions of a cone can be traded for faraway ordinary points of the same
cone. -/
theorem exists_nhds_cosmicSet_subset_ordinary {u : CosmicBoundary E}
    {V : Set (CosmicSpace E)} (hV : V ∈ 𝓝 (cosmicDirection u)) :
    ∃ V' ∈ 𝓝 (cosmicDirection u), ∀ C K : Set E, IsCone K →
      (cosmicSet C K ∩ V').Nonempty →
        (cosmicSet (C ∪ K) ({0} : Set E) ∩ V).Nonempty := by
  obtain ⟨U, hUV, hUopen, hUmem⟩ := _root_.mem_nhds_iff.1 hV
  refine ⟨U, hUopen.mem_nhds hUmem, ?_⟩
  rintro C K hK ⟨p, hpS, hpU⟩
  rcases mem_cosmicSet.1 hpS with ⟨y, hyC, rfl⟩ | ⟨v, hvK, rfl⟩
  · exact ⟨cosmicEmbed y, cosmicEmbed_mem_cosmicSet_iff.2 (Or.inl hyC), hUV hpU⟩
  · obtain ⟨n, hn⟩ := ((tendsto_cosmicRadialOrdinary v).eventually
      (hUopen.mem_nhds hpU)).exists
    exact ⟨cosmicEmbed (cosmicRadialOrdinary v n),
      cosmicEmbed_mem_cosmicSet_iff.2
        (Or.inr (cosmicRadialOrdinary_mem_of_isCone hK hvK n)), hUV hn⟩

/-- **Neighborhood transfer, ordinary to mixed.**  Close enough to a
direction point, an ordinary point of a cone can be traded for the direction
it points in. -/
theorem exists_nhds_ordinary_subset_cosmicSet {u : CosmicBoundary E}
    {V : Set (CosmicSpace E)} (hV : V ∈ 𝓝 (cosmicDirection u)) :
    ∃ V' ∈ 𝓝 (cosmicDirection u), ∀ C K : Set E, IsCone K →
      (cosmicSet (C ∪ K) ({0} : Set E) ∩ V').Nonempty →
        (cosmicSet C K ∩ V).Nonempty := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hV
  refine ⟨ball (cosmicDirection u) (min δ 1 / 2),
    ball_mem_nhds _ (by positivity), ?_⟩
  rintro C K hK ⟨p, hpS, hpV⟩
  rcases mem_cosmicSet.1 hpS with ⟨y, hyCK, rfl⟩ | ⟨v, hv0, rfl⟩
  · have hpV' : dist (cosmicEmbed y) (cosmicDirection u) < min δ 1 / 2 := hpV
    have hεle : min δ 1 / 2 ≤ 1 / 2 := by
      have : min δ 1 ≤ 1 := min_le_right _ _
      linarith
    have hgap : 1 - ‖((cosmicEmbed y : CosmicSpace E) : E)‖ < min δ 1 / 2 := by
      have hd : dist ((cosmicDirection u : CosmicSpace E) : E)
          ((cosmicEmbed y : CosmicSpace E) : E) < min δ 1 / 2 := by
        rw [← Subtype.dist_eq, dist_comm]
        exact hpV'
      rw [dist_eq_norm] at hd
      have hsub := norm_sub_norm_le ((cosmicDirection u : CosmicSpace E) : E)
        ((cosmicEmbed y : CosmicSpace E) : E)
      rw [norm_cosmicDirection u] at hsub
      linarith
    have hy : y ≠ 0 := by
      rintro rfl
      rw [coe_cosmicEmbed_eq_cosmicScale_smul, smul_zero, norm_zero] at hgap
      linarith
    rcases hyCK with hyC | hyK
    · exact ⟨cosmicEmbed y, cosmicEmbed_mem_cosmicSet_iff.2 hyC,
        hball (mem_ball.2 (lt_of_lt_of_le hpV'
          (by have : min δ 1 ≤ δ := min_le_left _ _; linarith)))⟩
    · refine ⟨cosmicDirection (cosmicDirectionOf y hy), mem_cosmicSet.2 (Or.inr
        ⟨cosmicDirectionOf y hy, ?_, rfl⟩), hball (mem_ball.2 ?_)⟩
      · rw [coe_cosmicDirectionOf, NormedSpace.normalize]
        exact hK.smul_mem hyK (by positivity)
      · have h1 : dist (cosmicDirection (cosmicDirectionOf y hy))
            (cosmicEmbed y) < min δ 1 / 2 := by
          rw [dist_comm, dist_cosmicEmbed_cosmicDirectionOf hy]
          exact hgap
        have := dist_triangle (cosmicDirection (cosmicDirectionOf y hy))
          (cosmicEmbed y) (cosmicDirection u)
        have hmin : min δ 1 ≤ δ := min_le_left _ _
        linarith
  · have hv0' : (v : E) = 0 := by simpa using hv0
    have hvnorm : ‖(v : E)‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
    rw [hv0', norm_zero] at hvnorm
    exact absurd hvnorm zero_ne_one

/-- **Neighborhood transfer for pure direction sets**, from cosmic space down
to `E`. -/
theorem exists_nhds_cosmicDirections_subset {u : CosmicBoundary E} {V : Set E}
    (hV : V ∈ 𝓝 ((u : E))) :
    ∃ V' ∈ 𝓝 (cosmicDirection u), ∀ K : Set E,
      (cosmicDirections K ∩ V').Nonempty → (K ∩ V).Nonempty := by
  refine ⟨(Subtype.val : CosmicSpace E → E) ⁻¹' V,
    continuous_subtype_val.continuousAt.preimage_mem_nhds (by simpa using hV), ?_⟩
  rintro K ⟨p, hpK, hpV⟩
  rcases mem_cosmicDirections.1 hpK with ⟨v, hvK, rfl⟩
  exact ⟨(v : E), hvK, hpV⟩

/-- **Neighborhood transfer for pure direction sets**, from `E` up to cosmic
space. -/
theorem exists_nhds_subset_cosmicDirections {u : CosmicBoundary E}
    {V' : Set (CosmicSpace E)} (hV' : V' ∈ 𝓝 (cosmicDirection u)) :
    ∃ V ∈ 𝓝 ((u : E)), ∀ K : Set E, IsCone K →
      (K ∩ V).Nonempty → (cosmicDirections K ∩ V').Nonempty := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hV'
  refine ⟨{y : E | y ≠ 0 ∧ ‖y‖⁻¹ • y ∈ ball ((u : E)) δ},
    normalize_mem_nhds (mem_sphere_zero_iff_norm.mp u.property)
      (ball_mem_nhds _ hδ), ?_⟩
  rintro K hK ⟨y, hyK, hy0, hyball⟩
  refine ⟨cosmicDirection (cosmicDirectionOf y hy0),
    mem_cosmicDirections.2 ⟨cosmicDirectionOf y hy0, ?_, rfl⟩, hball ?_⟩
  · rw [coe_cosmicDirectionOf, NormedSpace.normalize]
    exact hK.smul_mem hyK (by positivity)
  · rw [mem_ball, Subtype.dist_eq, coe_cosmicDirection, coe_cosmicDirectionOf,
      NormedSpace.normalize]
    exact mem_ball.1 hyball

end CosmicGeometry

section CosmicLimits

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Along a nontrivial filter, outer limits of cones are cones. -/
theorem isCone_outerSetLimitAlong {l : Filter ι} [l.NeBot] {K : ι → Set E}
    (hK : ∀ i, IsCone (K i)) : IsCone (outerSetLimitAlong l K) := by
  refine ⟨fun V hV ↦ Filter.Eventually.frequently
    (Filter.Eventually.of_forall fun i ↦ ⟨0, (hK i).1, mem_of_mem_nhds hV⟩), ?_⟩
  intro w hw c hc V hV
  have hpre : (fun y : E ↦ c • y) ⁻¹' V ∈ 𝓝 w :=
    (continuous_const_smul c).continuousAt.preimage_mem_nhds hV
  exact (hw _ hpre).mono fun i ⟨y, hyK, hyV⟩ ↦
    ⟨c • y, (hK i).smul_mem hyK hc.le, hyV⟩

/-- **Exercise 4.20, direction part.**  At a direction point the cosmic outer
limit of `C(i) ∪ dir K(i)` agrees with that of the ordinary family
`C(i) ∪ K(i)`. -/
theorem cosmicDirection_mem_outerSetLimitAlong_cosmicSet_iff {l : Filter ι}
    {C K : ι → Set E} (hK : ∀ i, IsCone (K i)) {u : CosmicBoundary E} :
    cosmicDirection u ∈ outerSetLimitAlong l (fun i ↦ cosmicSet (C i) (K i)) ↔
      (u : E) ∈ horizonOuterSetLimitAlong l (fun i ↦ C i ∪ K i) := by
  rw [← cosmicDirection_mem_outer_ordinaryCosmicFamily_iff]
  constructor
  · intro h V hV
    obtain ⟨V', hV', htr⟩ := exists_nhds_cosmicSet_subset_ordinary hV
    exact (h V' hV').mono fun i hi ↦ htr (C i) (K i) (hK i) hi
  · intro h V hV
    obtain ⟨V', hV', htr⟩ := exists_nhds_ordinary_subset_cosmicSet hV
    exact (h V' hV').mono fun i hi ↦ htr (C i) (K i) (hK i) hi

/-- **Exercise 4.20, direction part**, inner form. -/
theorem cosmicDirection_mem_innerSetLimitAlong_cosmicSet_iff {l : Filter ι}
    {C K : ι → Set E} (hK : ∀ i, IsCone (K i)) {u : CosmicBoundary E} :
    cosmicDirection u ∈ innerSetLimitAlong l (fun i ↦ cosmicSet (C i) (K i)) ↔
      (u : E) ∈ horizonInnerSetLimitAlong l (fun i ↦ C i ∪ K i) := by
  rw [← cosmicDirection_mem_inner_ordinaryCosmicFamily_iff]
  constructor
  · intro h V hV
    obtain ⟨V', hV', htr⟩ := exists_nhds_cosmicSet_subset_ordinary hV
    exact (h V' hV').mono fun i hi ↦ htr (C i) (K i) (hK i) hi
  · intro h V hV
    obtain ⟨V', hV', htr⟩ := exists_nhds_ordinary_subset_cosmicSet hV
    exact (h V' hV').mono fun i hi ↦ htr (C i) (K i) (hK i) hi

/-- A cosmic limit of pure direction sets is read off the ordinary limit of
the cones. -/
theorem cosmicDirection_mem_outerSetLimitAlong_cosmicDirections_iff
    {l : Filter ι} {K : ι → Set E} (hK : ∀ i, IsCone (K i))
    {u : CosmicBoundary E} :
    cosmicDirection u ∈
        outerSetLimitAlong l (fun i ↦ cosmicDirections (K i)) ↔
      (u : E) ∈ outerSetLimitAlong l K := by
  constructor
  · intro h V hV
    obtain ⟨V', hV', htr⟩ := exists_nhds_cosmicDirections_subset hV
    exact (h V' hV').mono fun i hi ↦ htr (K i) hi
  · intro h V hV
    obtain ⟨W, hW, htr⟩ := exists_nhds_subset_cosmicDirections hV
    exact (h W hW).mono fun i hi ↦ htr (K i) (hK i) hi

theorem cosmicDirection_mem_innerSetLimitAlong_cosmicDirections_iff
    {l : Filter ι} {K : ι → Set E} (hK : ∀ i, IsCone (K i))
    {u : CosmicBoundary E} :
    cosmicDirection u ∈
        innerSetLimitAlong l (fun i ↦ cosmicDirections (K i)) ↔
      (u : E) ∈ innerSetLimitAlong l K := by
  constructor
  · intro h V hV
    obtain ⟨V', hV', htr⟩ := exists_nhds_cosmicDirections_subset hV
    exact (h V' hV').mono fun i hi ↦ htr (K i) hi
  · intro h V hV
    obtain ⟨W, hW, htr⟩ := exists_nhds_subset_cosmicDirections hV
    exact (h W hW).mono fun i hi ↦ htr (K i) (hK i) hi

/-- Two subsets of cosmic space with the same direction points have the same
direction cone. -/
theorem cosmicDirectionCone_congr {S T : Set (CosmicSpace E)}
    (h : ∀ u : CosmicBoundary E, cosmicDirection u ∈ S ↔ cosmicDirection u ∈ T) :
    cosmicDirectionCone S = cosmicDirectionCone T := by
  ext w
  constructor <;> rintro (rfl | ⟨v, hv, r, hr, rfl⟩)
  · exact mem_insert 0 _
  · exact Or.inr ⟨v, (h v).1 hv, r, hr, rfl⟩
  · exact mem_insert 0 _
  · exact Or.inr ⟨v, (h v).2 hv, r, hr, rfl⟩

theorem cosmicDirectionCone_union (S T : Set (CosmicSpace E)) :
    cosmicDirectionCone (S ∪ T) =
      cosmicDirectionCone S ∪ cosmicDirectionCone T := by
  ext w
  constructor
  · rintro (rfl | ⟨v, hv | hv, r, hr, rfl⟩)
    · exact Or.inl (mem_insert 0 _)
    · exact Or.inl (Or.inr ⟨v, hv, r, hr, rfl⟩)
    · exact Or.inr (Or.inr ⟨v, hv, r, hr, rfl⟩)
  · rintro ((rfl | ⟨v, hv, r, hr, rfl⟩) | (rfl | ⟨v, hv, r, hr, rfl⟩))
    · exact mem_insert 0 _
    · exact Or.inr ⟨v, Or.inl hv, r, hr, rfl⟩
    · exact mem_insert 0 _
    · exact Or.inr ⟨v, Or.inr hv, r, hr, rfl⟩

/-- For a family of cones the horizon outer limit is the ordinary outer
limit.  This is the elementary observation used in the cone case of 4.25. -/
theorem horizonOuterSetLimitAlong_of_isCone {l : Filter ι} [l.NeBot]
    {K : ι → Set E} (hK : ∀ i, IsCone (K i)) :
    horizonOuterSetLimitAlong l K = outerSetLimitAlong l K := by
  have key : ∀ v : CosmicBoundary E,
      cosmicDirection v ∈ outerSetLimitAlong l (ordinaryCosmicFamily K) ↔
        (v : E) ∈ outerSetLimitAlong l K := by
    intro v
    rw [← cosmicDirection_mem_outerSetLimitAlong_cosmicDirections_iff hK]
    constructor
    · intro h V hV
      obtain ⟨V', hV', htr⟩ := exists_nhds_ordinary_subset_cosmicSet hV
      refine (h V' hV').mono fun i hi ↦ ?_
      simpa [cosmicSet] using htr ∅ (K i) (hK i) (by simpa [ordinaryCosmicFamily] using hi)
    · intro h V hV
      obtain ⟨V', hV', htr⟩ := exists_nhds_cosmicSet_subset_ordinary hV
      refine (h V' hV').mono fun i hi ↦ ?_
      simpa [ordinaryCosmicFamily] using
        htr ∅ (K i) (hK i) (by simpa [cosmicSet] using hi)
  refine Subset.antisymm ?_ ?_
  · rintro w (rfl | ⟨v, hv, r, hr, rfl⟩)
    · exact (isCone_outerSetLimitAlong hK).1
    · exact (isCone_outerSetLimitAlong hK).smul_mem ((key v).1 hv) hr.le
  · intro w hw
    by_cases hw0 : w = 0
    · rw [hw0]
      exact (isCone_horizonOuterSetLimitAlong l K).1
    · right
      refine ⟨cosmicDirectionOf w hw0, (key _).2 ?_, ‖w‖, norm_pos_iff.2 hw0, ?_⟩
      · rw [coe_cosmicDirectionOf, NormedSpace.normalize]
        exact (isCone_outerSetLimitAlong hK).smul_mem hw (by positivity)
      · rw [coe_cosmicDirectionOf, NormedSpace.norm_smul_normalize w]

/-- The same for a family that is only eventually cone-valued, which is the
form 5.29 needs. -/
theorem horizonOuterSetLimitAlong_of_eventually_isCone {l : Filter ι} [l.NeBot]
    {K : ι → Set E} (hK : ∀ᶠ i in l, IsCone (K i)) :
    horizonOuterSetLimitAlong l K = outerSetLimitAlong l K := by
  classical
  have hK' : ∀ i, IsCone (if IsCone (K i) then K i else ({0} : Set E)) := by
    intro i
    split
    · assumption
    · exact ⟨rfl, fun x hx c _ ↦ by
        rw [mem_singleton_iff] at hx ⊢
        rw [hx, smul_zero]⟩
  have heq : (fun i ↦ if IsCone (K i) then K i else ({0} : Set E)) =ᶠ[l] K :=
    hK.mono fun i hi ↦ by simp [hi]
  rw [← horizonOuterSetLimitAlong_congr heq, ← outerSetLimitAlong_congr heq,
    horizonOuterSetLimitAlong_of_isCone hK']

/-- The ordinary family of a termwise union splits. -/
theorem ordinaryCosmicFamily_union (C K : ι → Set E) :
    ordinaryCosmicFamily (fun i ↦ C i ∪ K i) =
      fun i ↦ ordinaryCosmicFamily C i ∪ ordinaryCosmicFamily K i := by
  funext i
  simp [ordinaryCosmicFamily, cosmicSet, image_union]

/-- **Exercise 4.20**: the horizon outer limit of the termwise union splits
into the horizon outer limit of the sets and the ordinary outer limit of the
cones. -/
theorem horizonOuterSetLimitAlong_union_cones {l : Filter ι} [l.NeBot]
    (C K : ι → Set E) (hK : ∀ i, IsCone (K i)) :
    horizonOuterSetLimitAlong l (fun i ↦ C i ∪ K i) =
      horizonOuterSetLimitAlong l C ∪ outerSetLimitAlong l K := by
  rw [horizonOuterSetLimitAlong, ordinaryCosmicFamily_union,
    outerSetLimitAlong_union, cosmicDirectionCone_union,
    ← horizonOuterSetLimitAlong, ← horizonOuterSetLimitAlong,
    horizonOuterSetLimitAlong_of_isCone hK]

/-- **Exercise 4.20 (cosmic outer limit)** along an arbitrary index
filter. -/
theorem outerSetLimitAlong_cosmicSet {l : Filter ι} [l.NeBot]
    (C K : ι → Set E) (hK : ∀ i, IsCone (K i)) :
    outerSetLimitAlong l (fun i ↦ cosmicSet (C i) (K i)) =
      cosmicSet (outerSetLimitAlong l C)
        (horizonOuterSetLimitAlong l C ∪ outerSetLimitAlong l K) := by
  conv_lhs =>
    rw [← cosmicSet_parts (outerSetLimitAlong l (fun i ↦ cosmicSet (C i) (K i)))]
  rw [cosmicOrdinaryPart_outerSetLimitAlong_cosmicSet,
    ← horizonOuterSetLimitAlong_union_cones C K hK, horizonOuterSetLimitAlong]
  congr 1
  exact cosmicDirectionCone_congr fun u ↦
    (cosmicDirection_mem_outerSetLimitAlong_cosmicSet_iff hK).trans
      cosmicDirection_mem_outer_ordinaryCosmicFamily_iff.symm

/-- **Exercise 4.20 (cosmic inner limit)** along an arbitrary index filter.
The direction part is the *mixed* horizon inner limit of `C(i) ∪ K(i)`, which
is in general strictly larger than the union of the two separate inner
limits. -/
theorem innerSetLimitAlong_cosmicSet {l : Filter ι}
    (C K : ι → Set E) (hK : ∀ i, IsCone (K i)) :
    innerSetLimitAlong l (fun i ↦ cosmicSet (C i) (K i)) =
      cosmicSet (innerSetLimitAlong l C)
        (horizonInnerSetLimitAlong l (fun i ↦ C i ∪ K i)) := by
  conv_lhs =>
    rw [← cosmicSet_parts (innerSetLimitAlong l (fun i ↦ cosmicSet (C i) (K i)))]
  rw [cosmicOrdinaryPart_innerSetLimitAlong_cosmicSet, horizonInnerSetLimitAlong]
  congr 1
  exact cosmicDirectionCone_congr fun u ↦
    (cosmicDirection_mem_innerSetLimitAlong_cosmicSet_iff hK).trans
      cosmicDirection_mem_inner_ordinaryCosmicFamily_iff.symm

end CosmicLimits


section Proposition527

variable {E F : Type*} [TopologicalSpace E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- Formula 5(1) in the horizon sense: `lim sup∞ S(x)` as `x → x̄`, taken like
5(1) along the full neighborhood filter. -/
noncomputable def svHorizonOuterLimit (S : E → Set F) (x : E) : Set F :=
  horizonOuterSetLimitAlong (nhds x) S

/-- Formula 5(1) in the horizon sense: `lim inf∞ S(x)` as `x → x̄`. -/
noncomputable def svHorizonInnerLimit (S : E → Set F) (x : E) : Set F :=
  horizonInnerSetLimitAlong (nhds x) S

theorem isCone_svHorizonOuterLimit (S : E → Set F) (x : E) :
    IsCone (svHorizonOuterLimit S x) :=
  isCone_horizonOuterSetLimitAlong _ _

theorem isCone_svHorizonInnerLimit (S : E → Set F) (x : E) :
    IsCone (svHorizonInnerLimit S x) :=
  isCone_horizonInnerSetLimitAlong _ _

/-- The union of two cones is a cone. -/
theorem IsCone.union {A B : Set F} (hA : IsCone A) (hB : IsCone B) :
    IsCone (A ∪ B) := by
  refine ⟨Or.inl hA.1, ?_⟩
  rintro w (hw | hw) c hc
  · exact Or.inl (hA.2 hw hc)
  · exact Or.inr (hB.2 hw hc)

/-- **Proposition 5.27 (cosmic semicontinuity), outer half.**  A mapping
`S(x) = C(x) ∪ dir K(x)` into cosmic space is outer semicontinuous at `x̄`
exactly when `C(x̄) ⊃ lim sup C(x)` and `K(x̄) ⊃ lim sup∞ C(x) ∪ lim sup K(x)`. -/
theorem svOscAt_cosmicSet_iff {C K : E → Set F} (hK : ∀ y, IsCone (K y))
    {x : E} :
    SvOscAt (fun y ↦ cosmicSet (C y) (K y)) x ↔
      svOuterLimit C x ⊆ C x ∧
        svHorizonOuterLimit C x ∪ svOuterLimit K x ⊆ K x := by
  rw [SvOscAt, svOuterLimit, outerSetLimitAlong_cosmicSet C K hK]
  exact cosmicSet_subset_iff
    ((isCone_horizonOuterSetLimitAlong _ _).union (isCone_outerSetLimitAlong hK))
    (hK x)

/-- **Proposition 5.27 (cosmic semicontinuity), inner half.**  The direction
condition is the *mixed* horizon inner limit `lim inf∞ (C(x) ∪ K(x))` that
Exercise 4.20 produces, not the union of the two separate inner limits that
the book prints; see `not_subset_svHorizonInnerLimit_union_of_svIscAt`. -/
theorem svIscAt_cosmicSet_iff {C K : E → Set F} (hK : ∀ y, IsCone (K y))
    {x : E} :
    SvIscAt (fun y ↦ cosmicSet (C y) (K y)) x ↔
      C x ⊆ svInnerLimit C x ∧
        K x ⊆ svHorizonInnerLimit (fun y ↦ C y ∪ K y) x := by
  rw [SvIscAt, svInnerLimit, innerSetLimitAlong_cosmicSet C K hK]
  exact cosmicSet_subset_iff (hK x) (isCone_horizonInnerSetLimitAlong _ _)

/-- **Proposition 5.27**, continuity form. -/
theorem svContinuousAt_cosmicSet_iff {C K : E → Set F} (hK : ∀ y, IsCone (K y))
    {x : E} :
    SvContinuousAt (fun y ↦ cosmicSet (C y) (K y)) x ↔
      (svOuterLimit C x ⊆ C x ∧
          svHorizonOuterLimit C x ∪ svOuterLimit K x ⊆ K x) ∧
        (C x ⊆ svInnerLimit C x ∧
          K x ⊆ svHorizonInnerLimit (fun y ↦ C y ∪ K y) x) := by
  rw [SvContinuousAt, svOscAt_cosmicSet_iff hK, svIscAt_cosmicSet_iff hK]

end Proposition527

section PrintedInnerCondition

/-- The unit direction `1` of the real line. -/
def cosmicUnitOne : CosmicBoundary ℝ := ⟨1, by simp⟩

@[simp]
theorem coe_cosmicUnitOne : ((cosmicUnitOne : CosmicBoundary ℝ) : ℝ) = 1 := rfl

private theorem isCone_Ici_zero : IsCone (Ici (0 : ℝ)) :=
  ⟨Set.self_mem_Ici, fun _ hx _ hc ↦ mem_Ici.2 (smul_nonneg hc.le (mem_Ici.1 hx))⟩

/-- The ordinary part of the counterexample: a single point escaping to the
direction `1` on the right of the origin, and nothing at all elsewhere. -/
noncomputable def alternatingOrdinary : ℝ → Set ℝ := fun y ↦
  if 0 < y then {cosmicRadialOrdinary cosmicUnitOne ⌊y⁻¹⌋₊} else ∅

/-- The direction part of the counterexample: the trivial cone on the right
of the origin, and the whole nonnegative ray elsewhere. -/
def alternatingCone : ℝ → Set ℝ := fun y ↦
  if 0 < y then {(0 : ℝ)} else Ici 0

theorem isCone_alternatingCone (y : ℝ) : IsCone (alternatingCone y) := by
  unfold alternatingCone
  split
  · refine ⟨rfl, fun x hx c _ ↦ ?_⟩
    rw [mem_singleton_iff] at hx ⊢
    rw [hx, smul_zero]
  · exact isCone_Ici_zero

theorem alternatingOrdinary_of_nonpos {y : ℝ} (hy : ¬ 0 < y) :
    alternatingOrdinary y = ∅ := by
  simp [alternatingOrdinary, hy]

theorem alternatingCone_of_nonpos {y : ℝ} (hy : ¬ 0 < y) :
    alternatingCone y = Ici 0 := by
  simp [alternatingCone, hy]

/-- Both branches of the counterexample contain the radial approximant, which
is exactly what makes the *mixed* horizon inner limit see the direction `1`
while neither separate inner limit does. -/
theorem cosmicRadialOrdinary_mem_alternating_union (y : ℝ) :
    cosmicRadialOrdinary cosmicUnitOne ⌊y⁻¹⌋₊ ∈
      alternatingOrdinary y ∪ alternatingCone y := by
  by_cases hy : 0 < y
  · exact Or.inl (by simp [alternatingOrdinary, hy])
  · refine Or.inr ?_
    rw [alternatingCone_of_nonpos hy]
    exact cosmicRadialOrdinary_mem_of_isCone isCone_Ici_zero (by simp) _

/-- Radial approximants indexed by `⌊y⁻¹⌋` escape to the direction `1` as `y`
decreases to `0`.  This is the one convergence the counterexamples of this
chapter need, and it needs no computation with the chart. -/
theorem tendsto_cosmicEmbed_radial_floor_inv :
    Filter.Tendsto
      (fun y : ℝ ↦ cosmicEmbed (cosmicRadialOrdinary cosmicUnitOne ⌊y⁻¹⌋₊))
      (nhdsWithin 0 (Ioi 0)) (nhds (cosmicDirection cosmicUnitOne)) :=
  (tendsto_cosmicRadialOrdinary cosmicUnitOne).comp
    (tendsto_nat_floor_atTop.comp tendsto_inv_nhdsGT_zero)

/-- The counterexample mapping *is* cosmically inner semicontinuous at the
origin: the direction `1` is reached from the right by escaping ordinary
points and from the left by the direction points of `IR₊`. -/
theorem svIscAt_alternating :
    SvIscAt (fun y ↦ cosmicSet (alternatingOrdinary y) (alternatingCone y))
      (0 : ℝ) := by
  intro p hp
  have hp' : p ∈ cosmicSet (∅ : Set ℝ) (Ici (0 : ℝ)) := by
    have hp0 : p ∈ cosmicSet (alternatingOrdinary 0) (alternatingCone 0) := hp
    rwa [alternatingOrdinary_of_nonpos (lt_irrefl 0),
      alternatingCone_of_nonpos (lt_irrefl 0)] at hp0
  obtain ⟨v, hv, rfl⟩ : ∃ v : CosmicBoundary ℝ, (v : ℝ) ∈ Ici (0 : ℝ) ∧
      cosmicDirection v = p := by
    rcases mem_cosmicSet.1 hp' with ⟨z, hz, _⟩ | h
    · exact absurd hz (notMem_empty z)
    · exact h
  have hvone : v = cosmicUnitOne := by
    apply Subtype.ext
    have hnorm : ‖(v : ℝ)‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
    rw [Real.norm_eq_abs, abs_of_nonneg (mem_Ici.1 hv)] at hnorm
    exact hnorm
  subst hvone
  intro V hV
  rw [← nhdsLE_sup_nhdsGT (0 : ℝ), Filter.eventually_sup]
  constructor
  · filter_upwards [self_mem_nhdsWithin] with y hy
    refine ⟨cosmicDirection cosmicUnitOne, ?_, mem_of_mem_nhds hV⟩
    rw [alternatingCone_of_nonpos (not_lt.2 hy)]
    exact mem_cosmicSet.2 (Or.inr ⟨cosmicUnitOne, by simp, rfl⟩)
  · filter_upwards [tendsto_cosmicEmbed_radial_floor_inv.eventually hV, self_mem_nhdsWithin]
      with y hyV hy
    exact ⟨cosmicEmbed (cosmicRadialOrdinary cosmicUnitOne ⌊y⁻¹⌋₊),
      cosmicEmbed_mem_cosmicSet_iff.2
        (by simp [alternatingOrdinary, mem_Ioi.1 hy]), hyV⟩

/-- Yet the condition printed in 5.27 fails for it: neither separate inner
limit contains the direction `1`. -/
theorem not_subset_svHorizonInnerLimit_union_alternating :
    ¬ alternatingCone 0 ⊆
        svHorizonInnerLimit alternatingOrdinary 0 ∪
          svInnerLimit alternatingCone 0 := by
  intro h
  have h1 : (1 : ℝ) ∈ alternatingCone 0 := by
    rw [alternatingCone_of_nonpos (lt_irrefl 0)]
    exact mem_Ici.2 zero_le_one
  rcases h h1 with hhor | hinner
  · rcases hhor with h0 | ⟨v, hv, r, hr, hrv⟩
    · exact one_ne_zero h0
    · have hev : ∀ᶠ y in nhdsWithin (0 : ℝ) (Iic 0),
          (ordinaryCosmicFamily alternatingOrdinary y ∩ univ).Nonempty :=
        (hv univ univ_mem).filter_mono nhdsWithin_le_nhds
      obtain ⟨y, hy, hyle⟩ := (hev.and self_mem_nhdsWithin).exists
      rw [ordinaryCosmicFamily,
        alternatingOrdinary_of_nonpos (not_lt.2 hyle)] at hy
      simp at hy
  · have hev : ∀ᶠ y in nhdsWithin (0 : ℝ) (Ioi 0),
        (alternatingCone y ∩ ball (1 : ℝ) (1 / 2)).Nonempty :=
      (hinner (ball (1 : ℝ) (1 / 2)) (ball_mem_nhds _ (by norm_num))).filter_mono
        nhdsWithin_le_nhds
    obtain ⟨y, hy, hypos⟩ := (hev.and self_mem_nhdsWithin).exists
    rw [show alternatingCone y = {(0 : ℝ)} by
      simp [alternatingCone, hypos]] at hy
    obtain ⟨z, hz0, hzV⟩ := hy
    rw [mem_singleton_iff] at hz0
    subst hz0
    rw [mem_ball, Real.dist_eq] at hzV
    norm_num at hzV

/-- **The inner condition printed in 5.27 is not equivalent to cosmic inner
semicontinuity.**  The book states it as `K(x̄) ⊂ lim inf∞ C(x) ∪ lim inf K(x)`
and proves 5.27 by citing 4.20, but 4.20 delivers the mixed horizon inner
limit `lim inf∞ (C(x) ∪ K(x))`, which is strictly larger here. -/
theorem printed_inner_condition_of_527_fails :
    ∃ C K : ℝ → Set ℝ, (∀ y, IsCone (K y)) ∧
      SvIscAt (fun y ↦ cosmicSet (C y) (K y)) 0 ∧
        ¬ K 0 ⊆ svHorizonInnerLimit C 0 ∪ svInnerLimit K 0 :=
  ⟨alternatingOrdinary, alternatingCone, isCone_alternatingCone,
    svIscAt_alternating, not_subset_svHorizonInnerLimit_union_alternating⟩

end PrintedInnerCondition

end RW
