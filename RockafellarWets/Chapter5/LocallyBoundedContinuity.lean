/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Consequences of the Neighborhood Criterion

Corollaries 5.20 and 5.21 both read off Theorem 5.19.

For a single-valued mapping `F` viewed set-valued as `x ↦ {F(x)}`, inner
semicontinuity is nothing but continuity -- it unfolds to the statement that
every neighborhood of `F(x̄)` eventually contains `F(x)` -- while outer
semicontinuity alone is weaker.  What repairs it is local boundedness, and
the repair is exactly the neighborhood property of 5.19 applied to a ball
around `F(x̄)`.  The book's counterexample, `F(x) = 1/x` with `F(0) = 0`, is
formalized here too; in Lean it needs no case split, since `(0 : ℝ)⁻¹ = 0`
already.

Between 5.20 and 5.21 the book records that the neighborhood property fails
for mappings with unbounded values, and that the repair is to truncate: `S`
is osc exactly when every truncation `S∩B : x ↦ S(x) ∩ B` by a compact `B` is
osc.  Truncations are bounded, hence locally bounded, so 5.19 applies to each
of them and yields the corrected characterization.

Corollary 5.21 identifies continuity at a point of local boundedness with
convergence to `0` of the Pompeiu--Hausdorff distance of 4.13.  The book
derives it from the sequential statement 4.40, but no sequences are needed:
Proposition 5.12 already states semicontinuity as a two-sided `ε`-inclusion
on bounded balls, and local boundedness makes the balls disappear, so the
two clauses of 5.12 are precisely the two halves of a Hausdorff estimate.
-/

import RockafellarWets.Chapter4.HausdorffConvergence
import RockafellarWets.Chapter5.LocalBoundedness
import RockafellarWets.Chapter5.UniformSemicontinuity

open Bornology Filter Metric Set Topology

namespace RW

section SingleValued

variable {E F : Type*} [TopologicalSpace E] [MetricSpace F]

/-- A single-valued mapping viewed as a set-valued mapping, as in 5.20. -/
def svSingleton (f : E → F) : E → Set F := fun x ↦ {f x}

omit [TopologicalSpace E] [MetricSpace F] in
@[simp]
theorem mem_svSingleton {f : E → F} {x : E} {u : F} :
    u ∈ svSingleton f x ↔ u = f x := Iff.rfl

omit [TopologicalSpace E] [MetricSpace F] in
@[simp]
theorem svImage_svSingleton (f : E → F) (V : Set E) :
    svImage (svSingleton f) V = f '' V := by
  ext u
  simp only [mem_svImage, mem_svSingleton, mem_image]
  exact ⟨fun ⟨y, hy, hu⟩ ↦ ⟨y, hy, hu.symm⟩, fun ⟨y, hy, hu⟩ ↦ ⟨y, hy, hu.symm⟩⟩

/-- **Corollary 5.20**, the equivalence of (a) and (c): for a single-valued
mapping, inner semicontinuity *is* continuity.  Both sides say that every
neighborhood of `F(x̄)` eventually contains `F(x)`. -/
theorem svIscAt_svSingleton_iff (f : E → F) (x : E) :
    SvIscAt (svSingleton f) x ↔ ContinuousAt f x := by
  constructor
  · intro h
    rw [ContinuousAt, Filter.tendsto_def]
    intro W hW
    filter_upwards [h rfl W hW] with y hy
    obtain ⟨z, hz, hzW⟩ := hy
    rwa [mem_svSingleton.1 hz] at hzW
  · intro h u hu W hW
    rw [mem_svSingleton.1 hu] at hW
    filter_upwards [h hW] with y hy
    exact ⟨f y, rfl, hy⟩

/-- **Corollary 5.20**, (a) implies the outer half of (b). -/
theorem svOscAt_svSingleton_of_continuousAt {f : E → F} {x : E}
    (h : ContinuousAt f x) : SvOscAt (svSingleton f) x := by
  intro u hu
  rw [mem_svSingleton]
  by_contra hne
  have hpos : 0 < dist u (f x) / 2 := by
    have := dist_pos.2 hne
    linarith
  obtain ⟨y, ⟨z, hz, hzball⟩, hy⟩ :=
    ((hu (ball u (dist u (f x) / 2)) (ball_mem_nhds u hpos)).and_eventually
      (Metric.tendsto_nhds.1 h _ hpos)).exists
  rw [mem_svSingleton.1 hz] at hzball
  have h₁ : dist (f y) u < dist u (f x) / 2 := by
    simpa [dist_comm] using mem_ball.1 hzball
  have h₂ : dist u (f x) ≤ dist u (f y) + dist (f y) (f x) := dist_triangle _ _ _
  rw [dist_comm u (f y)] at h₂
  linarith

/-- **Corollary 5.20**, (a) implies the boundedness half of (b). -/
theorem svLocallyBoundedAt_svSingleton_of_continuousAt {f : E → F} {x : E}
    (h : ContinuousAt f x) : SvLocallyBoundedAt (svSingleton f) x := by
  refine ⟨f ⁻¹' ball (f x) 1, h (ball_mem_nhds (f x) one_pos), ?_⟩
  rw [svImage_svSingleton]
  exact isBounded_ball.subset (image_preimage_subset _ _)

variable [ProperSpace F]

/-- **Corollary 5.20**, (b) implies (a): this is where 5.19 does the work.
Outer semicontinuity plus local boundedness push a whole neighborhood of `x̄`
into the ball `IB(F(x̄), ε)`, which is continuity. -/
theorem continuousAt_of_svOscAt_svSingleton {f : E → F} {x : E}
    (hosc : SvOscAt (svSingleton f) x)
    (hlb : SvLocallyBoundedAt (svSingleton f) x) : ContinuousAt f x := by
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨V, hV, hVsub⟩ :=
    hosc.exists_nhds_svImage_subset hlb isOpen_ball
      (singleton_subset_iff.2 (mem_ball_self hε))
  rw [svImage_svSingleton] at hVsub
  filter_upwards [hV] with y hy
  exact mem_ball.1 (hVsub (mem_image_of_mem f hy))

/-- **Corollary 5.20.**  For a single-valued mapping the three properties are
equivalent: continuity, outer semicontinuity together with local boundedness,
and inner semicontinuity. -/
theorem svSingleton_tfae (f : E → F) (x : E) :
    List.TFAE
      [ContinuousAt f x,
        SvOscAt (svSingleton f) x ∧ SvLocallyBoundedAt (svSingleton f) x,
        SvIscAt (svSingleton f) x] := by
  tfae_have 1 → 2 := fun h ↦
    ⟨svOscAt_svSingleton_of_continuousAt h,
      svLocallyBoundedAt_svSingleton_of_continuousAt h⟩
  tfae_have 2 → 3 := fun h ↦
    (svIscAt_svSingleton_iff f x).2 (continuousAt_of_svOscAt_svSingleton h.1 h.2)
  tfae_have 3 → 1 := fun h ↦ (svIscAt_svSingleton_iff f x).1 h
  tfae_finish

omit [ProperSpace F] in
/-- Set-valued continuity of a single-valued mapping is ordinary
continuity. -/
theorem svContinuousAt_svSingleton_iff (f : E → F) (x : E) :
    SvContinuousAt (svSingleton f) x ↔ ContinuousAt f x :=
  ⟨fun h ↦ (svIscAt_svSingleton_iff f x).1 h.2,
    fun h ↦ ⟨svOscAt_svSingleton_of_continuousAt h,
      (svIscAt_svSingleton_iff f x).2 h⟩⟩

end SingleValued

section Counterexample

/-- The book's example after 5.20: `F(x) = 1/x` with `F(0) = 0`, which in Lean
is just `x ↦ x⁻¹`.  It is outer semicontinuous at `0` as a set-valued mapping.

A candidate limit `u ≠ 0` forces `|1/y| ≤ 3|u|/2`, hence `|y| ≥ 2/(3|u|)`, so
the values near `u` come only from arguments bounded away from `0`. -/
theorem svOscAt_svSingleton_inv : SvOscAt (svSingleton (fun y : ℝ ↦ y⁻¹)) 0 := by
  intro u hu
  simp only [mem_svSingleton, inv_zero]
  by_contra hne
  have hu0 : 0 < |u| := abs_pos.2 hne
  have hr : 0 < |u| / 2 := by linarith
  have hδ : (0 : ℝ) < 2 / (3 * |u|) := by positivity
  obtain ⟨y, ⟨z, hz, hzball⟩, hyball⟩ :=
    ((hu (ball u (|u| / 2)) (ball_mem_nhds u hr)).and_eventually
      (Filter.eventually_mem_set.2 (ball_mem_nhds (0 : ℝ) hδ))).exists
  rw [mem_svSingleton.1 hz] at hzball
  have hdist : |y⁻¹ - u| < |u| / 2 := by
    simpa [Real.dist_eq] using mem_ball.1 hzball
  -- The value is far from `0`, so the argument is too.
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [inv_zero, zero_sub, abs_neg] at hdist
    linarith
  have hyabs : 0 < |y| := abs_pos.2 hy0
  have hbound : |y⁻¹| < 3 * |u| / 2 := by
    have := abs_sub_abs_le_abs_sub y⁻¹ u
    linarith
  rw [abs_inv, inv_eq_one_div] at hbound
  rw [div_lt_iff₀ hyabs] at hbound
  have hylt : |y| * (3 * |u|) < 2 := by
    have : |y| < 2 / (3 * |u|) := by
      simpa [Real.dist_eq] using mem_ball.1 hyball
    rwa [lt_div_iff₀ (by positivity : (0 : ℝ) < 3 * |u|)] at this
  linarith

/-- The book's example after 5.20: the same mapping is *not* locally bounded
at `0`, which is why outer semicontinuity alone does not give continuity. -/
theorem not_svLocallyBoundedAt_svSingleton_inv :
    ¬ SvLocallyBoundedAt (svSingleton (fun y : ℝ ↦ y⁻¹)) 0 := by
  rintro ⟨V, hV, hbdd⟩
  obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.1 hV
  obtain ⟨R, hR⟩ := hbdd.exists_norm_le
  set R' : ℝ := max R 1 with hR'def
  have hR'1 : (1 : ℝ) ≤ R' := le_max_right _ _
  set y : ℝ := min (δ / 2) (1 / (R' + 1)) with hydef
  have hy0 : 0 < y := lt_min (by linarith) (by positivity)
  have hyV : y ∈ V := hδV (by
    rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hy0]
    calc y ≤ δ / 2 := min_le_left _ _
      _ < δ := by linarith)
  have hle : ‖y⁻¹‖ ≤ R :=
    hR _ (by rw [svImage_svSingleton]; exact mem_image_of_mem _ hyV)
  have hbig : R' + 1 ≤ y⁻¹ := by
    rw [← one_div, le_div_iff₀ hy0]
    calc (R' + 1) * y ≤ (R' + 1) * (1 / (R' + 1)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (by linarith)
      _ = 1 := by field_simp
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hy0)] at hle
  have : R ≤ R' := le_max_left _ _
  linarith

end Counterexample

section Truncations

variable {E F : Type*} [TopologicalSpace E] [MetricSpace F] [ProperSpace F]
variable {S : E → Set F} {B : Set F} {x : E}

/-- The truncation `S∩B : x ↦ S(x) ∩ B` of the paragraph after 5.20. -/
def svTrunc (S : E → Set F) (B : Set F) : E → Set F := fun x ↦ S x ∩ B

omit [TopologicalSpace E] [MetricSpace F] [ProperSpace F] in
@[simp]
theorem mem_svTrunc {u : F} : u ∈ svTrunc S B x ↔ u ∈ S x ∧ u ∈ B := Iff.rfl

omit [ProperSpace F] in
/-- A truncation by a bounded set is a bounded mapping, hence locally
bounded. -/
theorem svLocallyBoundedAt_svTrunc (hB : IsBounded B) :
    SvLocallyBoundedAt (svTrunc S B) x := by
  refine ⟨univ, univ_mem, hB.subset fun u hu ↦ ?_⟩
  obtain ⟨y, -, hy⟩ := mem_svImage.1 hu
  exact hy.2

omit [ProperSpace F] in
/-- Outer semicontinuity passes to truncations by closed sets. -/
theorem SvOscAt.svTrunc (hosc : SvOscAt S x) (hB : IsClosed B) :
    SvOscAt (svTrunc S B) x := by
  intro u hu
  refine ⟨hosc (outerSetLimitAlong_mono (fun _ ↦ inter_subset_left) hu), ?_⟩
  rw [← hB.closure_eq]
  refine _root_.mem_closure_iff.2 fun o hoopen hou ↦ ?_
  obtain ⟨_, z, hzS, hzo⟩ := (hu o (hoopen.mem_nhds hou)).exists
  exact ⟨z, hzo, hzS.2⟩

/-- The book's assertion after 5.20: `S` is osc exactly when all of its
truncations by compact sets are osc.

For the converse a single truncation suffices at each candidate point: a
point of the outer limit outside `S(x̄)` is already in the outer limit of the
truncation by the closed unit ball around it. -/
theorem svOscAt_iff_forall_svTrunc :
    SvOscAt S x ↔ ∀ B : Set F, IsCompact B → SvOscAt (svTrunc S B) x := by
  refine ⟨fun h B hB ↦ h.svTrunc hB.isClosed, fun h u hu ↦ ?_⟩
  have hmem : u ∈ svOuterLimit (svTrunc S (closedBall u 1)) x := by
    intro W hW
    have hW' : W ∩ ball u 1 ∈ nhds u := Filter.inter_mem hW (ball_mem_nhds u one_pos)
    exact (hu _ hW').mono fun y ⟨z, hzS, hzW, hzball⟩ ↦
      ⟨z, ⟨hzS, ball_subset_closedBall hzball⟩, hzW⟩
  exact (h _ (isCompact_closedBall u 1) hmem).1

/-- The corrected form of the neighborhood property of 5.19 for a mapping
with possibly unbounded values: apply 5.19 to each compact truncation, which
is locally bounded whatever `S` does. -/
theorem svOscAt_iff_forall_svTrunc_exists_nhds :
    SvOscAt S x ↔
      ∀ B : Set F, IsCompact B →
        IsClosed (S x ∩ B) ∧
          ∀ O : Set F, IsOpen O → S x ∩ B ⊆ O →
            ∃ V ∈ nhds x, svImage (svTrunc S B) V ⊆ O := by
  rw [svOscAt_iff_forall_svTrunc]
  exact forall_congr' fun B ↦ forall_congr' fun hB ↦
    svOscAt_iff_of_svLocallyBoundedAt (svLocallyBoundedAt_svTrunc hB.isBounded)

end Truncations

section HausdorffContinuity

variable {E F : Type*} [TopologicalSpace E] [NormedAddCommGroup F] [ProperSpace F]

/-- **Corollary 5.21.**  At a point of local boundedness where `S(x̄)` is
closed and the nearby values are nonempty, continuity is convergence to `0`
of the Pompeiu--Hausdorff distance `dl∞(S(x), S(x̄))` as `x → x̄`.

Necessity comes from both clauses of 5.12 at a radius `ρ` that local
boundedness makes contain every nearby value: the outer clause bounds
`infEdist z (S(x̄))` for `z ∈ S(x)`, the inner clause bounds
`infEdist w (S(x))` for `w ∈ S(x̄)`, and together they bound the Hausdorff
distance.  Sufficiency needs neither local boundedness nor 5.12.

The book also asks that `S(x)` be nonempty near `x̄`.  That hypothesis is not
needed: a finite Pompeiu--Hausdorff distance to a nonempty set already forces
nonemptiness, and where `S(x̄)` itself is empty both sides fail together. -/
theorem svContinuousAt_iff_tendsto_pompeiuHausdorffEDist {S : E → Set F} {x : E}
    (hlb : SvLocallyBoundedAt S x) (hclosed : IsClosed (S x)) :
    SvContinuousAt S x ↔
      Tendsto (fun y ↦ pompeiuHausdorffEDist (S y) (S x)) (nhds x) (nhds 0) := by
  constructor
  · rintro ⟨hosc, hisc⟩
    obtain ⟨V₀, hV₀, hbdd⟩ := hlb
    obtain ⟨ρ₀, hρ₀⟩ := (isBounded_iff_subset_closedBall (0 : F)).1 hbdd
    have hρ : (0 : ℝ) < max ρ₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hsub : svImage S V₀ ⊆ closedBall 0 (max ρ₀ 1) :=
      hρ₀.trans (closedBall_subset_closedBall (le_max_left _ _))
    have hSx : S x ⊆ closedBall (0 : F) (max ρ₀ 1) :=
      (subset_svImage (mem_of_mem_nhds hV₀)).trans hsub
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    obtain ⟨δ, hδ0, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ≤ ε := by
      rcases eq_or_ne ε ⊤ with rfl | hne'
      · exact ⟨1, one_pos, le_top⟩
      · exact ⟨ε.toReal, ENNReal.toReal_pos hε.ne' hne',
          (ENNReal.ofReal_toReal hne').le⟩
    have hA := (svOscWithinAt_iff_eventually_inter_closedBall_subset
      (X := univ) hclosed).1 (svOscWithinAt_univ.2 hosc) _ hρ δ hδ0
    have hB := (svIscWithinAt_iff_eventually_inter_closedBall_subset
      (X := univ) hclosed).1 (svIscWithinAt_univ.2 hisc) _ hρ δ hδ0
    rw [nhdsWithin_univ] at hA hB
    filter_upwards [hA, hB, hV₀] with y hy₁ hy₂ hyV
    refine le_trans (hausdorffEDist_le_of_infEDist ?_ ?_) hδε
    · intro z hz
      exact (Metric.mem_thickening_iff_infEDist_lt.1
        (hy₁ ⟨hz, hsub (mem_svImage.2 ⟨y, hyV, hz⟩)⟩)).le
    · intro w hw
      exact (Metric.mem_thickening_iff_infEDist_lt.1 (hy₂ ⟨hw, hSx hw⟩)).le
  · intro hH
    constructor
    · intro u hu
      rw [← hclosed.closure_eq, EMetric.mem_closure_iff]
      intro ε hε
      have hhalf : 0 < ε / 2 := ENNReal.half_pos hε.ne'
      obtain ⟨y, ⟨z, hzS, hzball⟩, hy⟩ :=
        ((hu (eball u (ε / 2)) (Metric.eball_mem_nhds u hhalf)).and_eventually
          (hH.eventually_lt_const hhalf)).exists
      obtain ⟨w, hwS, hwd⟩ :=
        infEDist_lt_iff.1
          (lt_of_le_of_lt (infEDist_le_hausdorffEDist_of_mem hzS) hy)
      refine ⟨w, hwS, ?_⟩
      calc edist u w ≤ edist u z + edist z w := edist_triangle _ _ _
        _ < ε / 2 + ε / 2 := ENNReal.add_lt_add
              (by rw [edist_comm]; exact Metric.mem_eball.1 hzball) hwd
        _ = ε := ENNReal.add_halves ε
    · intro u hu W hW
      obtain ⟨ε, hε, hball⟩ := EMetric.mem_nhds_iff.1 hW
      filter_upwards [hH.eventually_lt_const hε] with y hy
      have h₁ : infEDist u (S y) < ε := by
        have hle := infEDist_le_hausdorffEDist_of_mem (s := S x) (t := S y) hu
        rw [hausdorffEDist_comm] at hle
        exact lt_of_le_of_lt hle hy
      obtain ⟨z, hzS, hzd⟩ := infEDist_lt_iff.1 h₁
      exact ⟨z, hzS, hball (Metric.mem_eball.2 (by rwa [edist_comm]))⟩

/-- **Corollary 5.21** with the book's literal hypotheses, which ask for
`S(x)` to be nonempty and closed throughout a neighborhood of `x̄`.  Only
closedness at `x̄` itself is used. -/
theorem svContinuousAt_iff_tendsto_pompeiuHausdorffEDist_of_eventually
    {S : E → Set F} {x : E} (hlb : SvLocallyBoundedAt S x)
    (h : ∀ᶠ y in nhds x, (S y).Nonempty ∧ IsClosed (S y)) :
    SvContinuousAt S x ↔
      Tendsto (fun y ↦ pompeiuHausdorffEDist (S y) (S x)) (nhds x) (nhds 0) :=
  svContinuousAt_iff_tendsto_pompeiuHausdorffEDist hlb h.self_of_nhds.2

end HausdorffContinuity

section Relativization

variable {E F : Type*} [TopologicalSpace E] [PseudoMetricSpace F]
variable {S : E → Set F} {X : Set E} {x : E}

/-- The restriction `S|X` of the paragraph after 5.21: `S(x)` for `x ∈ X`, and
`∅` elsewhere. -/
def svRestrict (S : E → Set F) (X : Set E) : E → Set F :=
  fun x ↦ {u | u ∈ S x ∧ x ∈ X}

omit [TopologicalSpace E] [PseudoMetricSpace F] in
@[simp]
theorem mem_svRestrict {u : F} : u ∈ svRestrict S X x ↔ u ∈ S x ∧ x ∈ X := Iff.rfl

omit [TopologicalSpace E] [PseudoMetricSpace F] in
theorem svRestrict_apply (hx : x ∈ X) : svRestrict S X x = S x := by
  ext u; simp [hx]

omit [TopologicalSpace E] [PseudoMetricSpace F] in
theorem svRestrict_eq_empty (hx : x ∉ X) : svRestrict S X x = ∅ := by
  ext u; simp [hx]

omit [TopologicalSpace E] [PseudoMetricSpace F] in
/-- The book's remark that `S|X` is an inverse truncation, `S|X = (S⁻¹∩X)⁻¹`. -/
theorem svRestrict_eq_svInv_svTrunc (S : E → Set F) (X : Set E) :
    svRestrict S X = svInv (svTrunc (svInv S) X) := rfl

omit [TopologicalSpace E] [PseudoMetricSpace F] in
theorem svImage_svRestrict (S : E → Set F) (X V : Set E) :
    svImage (svRestrict S X) V = svImage S (X ∩ V) := by
  ext u
  simp only [mem_svImage, mem_svRestrict, mem_inter_iff]
  exact ⟨fun ⟨y, hyV, hyS, hyX⟩ ↦ ⟨y, ⟨hyX, hyV⟩, hyS⟩,
    fun ⟨y, ⟨hyX, hyV⟩, hyS⟩ ↦ ⟨y, hyV, hyS, hyX⟩⟩

/-- Relativizing the limit of 5(1) is the same as taking the absolute limit of
the restricted mapping: the values of `S|X` off `X` are empty, so they never
contribute to a frequency statement. -/
theorem svOuterLimit_svRestrict (S : E → Set F) (X : Set E) (x : E) :
    svOuterLimit (svRestrict S X) x = svOuterLimitWithin S X x := by
  ext u
  simp only [svOuterLimit, svOuterLimitWithin, mem_outerSetLimitAlong]
  refine forall₂_congr fun W _ ↦ ?_
  rw [nhdsWithin, Filter.frequently_inf_principal]
  constructor
  · exact fun h ↦ h.mono fun y ⟨z, ⟨hzS, hyX⟩, hzW⟩ ↦ ⟨hyX, z, hzS, hzW⟩
  · exact fun h ↦ h.mono fun y ⟨hyX, z, hzS, hzW⟩ ↦ ⟨z, ⟨hzS, hyX⟩, hzW⟩

/-- Outer semicontinuity relative to `X` is outer semicontinuity of `S|X`. -/
theorem svOscAt_svRestrict_iff (hx : x ∈ X) :
    SvOscAt (svRestrict S X) x ↔ SvOscWithinAt S X x := by
  rw [SvOscAt, SvOscWithinAt, svOuterLimit_svRestrict, svRestrict_apply hx]

/-- **Definition 5.14** relative to a set `X`, obtained by replacing the
neighborhood `V` with `X ∩ V`. -/
def SvLocallyBoundedWithinAt (S : E → Set F) (X : Set E) (x : E) : Prop :=
  ∃ V ∈ nhds x, IsBounded (svImage S (X ∩ V))

/-- Relative local boundedness is the ordinary local boundedness of `S|X`. -/
theorem svLocallyBoundedWithinAt_iff_svRestrict :
    SvLocallyBoundedWithinAt S X x ↔ SvLocallyBoundedAt (svRestrict S X) x := by
  constructor
  · rintro ⟨V, hV, hbdd⟩
    exact ⟨V, hV, by rwa [svImage_svRestrict]⟩
  · rintro ⟨V, hV, hbdd⟩
    exact ⟨V, hV, by rwa [svImage_svRestrict] at hbdd⟩

/-- Local boundedness relative to the whole space is local boundedness. -/
theorem svLocallyBoundedWithinAt_univ :
    SvLocallyBoundedWithinAt S univ x ↔ SvLocallyBoundedAt S x := by
  simp only [SvLocallyBoundedWithinAt, SvLocallyBoundedAt, univ_inter]

/-- **Theorem 5.19** relative to a set `X`, which the book says carries over
"in the obvious manner, through application to `S|X`".  That is exactly how it
is obtained here. -/
theorem SvOscWithinAt.exists_nhds_svImage_inter_subset [ProperSpace F]
    (hlb : SvLocallyBoundedWithinAt S X x) (hosc : SvOscWithinAt S X x)
    (hx : x ∈ X) {O : Set F} (hO : IsOpen O) (hSO : S x ⊆ O) :
    ∃ V ∈ nhds x, svImage S (X ∩ V) ⊆ O := by
  obtain ⟨V, hV, hVsub⟩ :=
    ((svOscAt_svRestrict_iff hx).2 hosc).exists_nhds_svImage_subset
      (svLocallyBoundedWithinAt_iff_svRestrict.1 hlb) hO
      (by rw [svRestrict_apply hx]; exact hSO)
  exact ⟨V, hV, by rwa [svImage_svRestrict] at hVsub⟩

end Relativization

end RW
