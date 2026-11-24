/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 14: Semicontinuity and limit operations

Exercise 14.9 (measurability from semicontinuity), Theorem 14.20 (graphical and pointwise
limits), Proposition 14.22 (limits of simple mappings) and Proposition 14.23 (convergence of
measurable selections) of Rockafellar–Wets.

For 14.9 and the graphical part of 14.20, the parameter space is any topological space `T`
whose σ-field contains the Borel sets (`OpensMeasurableSpace T`); for a Borel set `T ⊂ ℝᵈ`
this covers both `A = B(T)` and `A = L(T)`.  The relative form, for a subset `X` of a
topological space with semicontinuity relative to `X`, is stated on the subtype `↥X`.
-/

import RockafellarWets.Chapter14.MeasurableCompositions
import RockafellarWets.Chapter4.SetLimitDistances
import RockafellarWets.Chapter5.GraphicalLimits
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

open Set Filter Topology Metric TopologicalSpace
open scoped ENNReal NNReal Pointwise

open scoped Set.Notation

noncomputable section

namespace RW

section Exercise149

variable {F : Type*} [MetricSpace F] [ProperSpace F]

omit [ProperSpace F] in
/-- **Exercise 14.9**, inner semicontinuous case (no closedness needed). -/
theorem SvIsc.svMeasurable {T : Type*} [TopologicalSpace T] [MeasurableSpace T]
    [OpensMeasurableSpace T] {S : T → Set F} (hS : SvIsc S) : SvMeasurable S :=
  fun O hO ↦ (svIsc_iff_isOpen_svPreimage.1 hS O hO).measurableSet

/-- **Exercise 14.9**, outer semicontinuous case. -/
theorem SvOsc.svMeasurable {T : Type*} [TopologicalSpace T] [MeasurableSpace T]
    [OpensMeasurableSpace T] {S : T → Set F} (hS : SvOsc S) : SvMeasurable S := by
  have hval : ∀ t, IsClosed (S t) := fun t ↦ by
    have hc := isClosed_svGraph_iff_svOsc.2 hS
    have : S t = (fun u ↦ (t, u)) ⁻¹' svGraph S := rfl
    rw [this]
    exact hc.preimage (Continuous.prodMk_right t)
  exact svMeasurable_of_measurableSet_svPreimage_isCompact fun K hK ↦
    ((svOsc_iff_isClosed_svPreimage hval).1 hS K hK).measurableSet

/-- **Exercise 14.9 (measurability from semicontinuity)**, relative form: if `S` is osc relative
to `X` (in particular continuous relative to `X`), its restriction to `X` is measurable for every
σ-field on `X` containing the Borel sets. -/
theorem SvOscOn.svMeasurable_restrict {E : Type*} [TopologicalSpace E] {X : Set E}
    [MeasurableSpace X] [OpensMeasurableSpace X] {S : E → Set F} (hS : SvOscOn S X) :
    SvMeasurable (fun t : X ↦ S t) :=
  svMeasurable_of_measurableSet_svPreimage_isCompact fun _ hK ↦
    (hS.isClosed_svPreimage hK).measurableSet

omit [ProperSpace F] in
/-- **Exercise 14.9**, relative form, inner semicontinuous case. -/
theorem SvIscOn.svMeasurable_restrict {E : Type*} [TopologicalSpace E] {X : Set E}
    [MeasurableSpace X] [OpensMeasurableSpace X] {S : E → Set F} (hS : SvIscOn S X) :
    SvMeasurable (fun t : X ↦ S t) :=
  fun _ hO ↦ (hS.isOpen_svPreimage hO).measurableSet

/-- **Exercise 14.9 (measurability from semicontinuity)**: a mapping that is osc or isc relative
to `X` (in particular continuous relative to `X`) is measurable on `X` for every σ-field
containing the Borel sets of `X`, e.g. `B(T)` or `L(T)` for a Borel set `T = X ⊂ ℝᵈ`. -/
theorem measurability_from_semicontinuity {E : Type*} [TopologicalSpace E] {X : Set E}
    [MeasurableSpace X] [OpensMeasurableSpace X] {S : E → Set F}
    (hS : SvOscOn S X ∨ SvIscOn S X) : SvMeasurable (fun t : X ↦ S t) :=
  hS.elim SvOscOn.svMeasurable_restrict SvIscOn.svMeasurable_restrict

end Exercise149

section Thickenings

variable {T F : Type*} [MeasurableSpace T] [MetricSpace F] [ProperSpace F]

omit [MeasurableSpace T] in
theorem cthickening_inter_nonempty_iff {C K : Set F} (hC : IsClosed C) (hK : IsCompact K)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    (cthickening δ C ∩ K).Nonempty ↔ (C ∩ cthickening δ K).Nonempty := by
  constructor
  · rintro ⟨x, hxC, hxK⟩
    have hCne : C.Nonempty := by
      by_contra h
      rw [not_nonempty_iff_eq_empty] at h
      rw [h, cthickening_empty] at hxC
      exact hxC
    obtain ⟨c, hc, hdist⟩ := hC.exists_infDist_eq_dist hCne x
    have hle : infDist x C ≤ δ := by
      have h1 := mem_cthickening_iff.1 hxC
      have h2 : infEDist x C ≠ ⊤ := infEDist_ne_top hCne
      exact ENNReal.toReal_le_of_le_ofReal hδ h1
    refine ⟨c, hc, mem_cthickening_of_dist_le c x δ K hxK ?_⟩
    rw [dist_comm, ← hdist]
    exact hle
  · rintro ⟨c, hcC, hcK⟩
    have hKne : K.Nonempty := by
      by_contra h
      rw [not_nonempty_iff_eq_empty] at h
      rw [h, cthickening_empty] at hcK
      exact hcK
    obtain ⟨x, hx, hdist⟩ := hK.exists_infDist_eq_dist hKne c
    have hle : infDist c K ≤ δ := by
      have h1 := mem_cthickening_iff.1 hcK
      exact ENNReal.toReal_le_of_le_ofReal hδ h1
    refine ⟨x, mem_cthickening_of_dist_le x c δ C hcC ?_, hx⟩
    rw [dist_comm, ← hdist]
    exact hle

/-- Closed `δ`-thickenings `t ↦ S(t) + δ IB` of a measurable mapping are measurable. -/
theorem SvMeasurable.cthickening {S : T → Set F} (hS : SvMeasurable S) (δ : ℝ) :
    SvMeasurable (fun t ↦ Metric.cthickening δ (S t)) := by
  rcases le_or_gt δ 0 with hδ | hδ
  · have : (fun t ↦ Metric.cthickening δ (S t)) = fun t ↦ _root_.closure (S t) :=
      funext fun t ↦ cthickening_of_nonpos hδ _
    rw [this]
    exact hS.closure
  have heq : (fun t ↦ Metric.cthickening δ (S t)) =
      fun t ↦ Metric.cthickening δ (_root_.closure (S t)) :=
    funext fun t ↦ (cthickening_closure).symm
  rw [heq]
  refine svMeasurable_of_measurableSet_svPreimage_isCompact fun K hK ↦ ?_
  have : svPreimage (fun t ↦ Metric.cthickening δ (_root_.closure (S t))) K =
      svPreimage (fun t ↦ _root_.closure (S t)) (Metric.cthickening δ K) := by
    ext t
    exact cthickening_inter_nonempty_iff isClosed_closure hK hδ.le
  rw [this]
  exact hS.closure.measurableSet_svPreimage_of_isCompact (fun _ ↦ isClosed_closure)
    (hK.cthickening)

end Thickenings

section Theorem1420

variable {T F : Type*} [MeasurableSpace T] [MetricSpace F] [ProperSpace F]

omit [MeasurableSpace T] [ProperSpace F] in
/-- The closure form of the thickening formula for inner limits used in the proof of 14.20. -/
theorem innerSetLimit_eq_iInter_closure_iUnion_iInter_cthickening (C : ℕ → Set F) :
    innerSetLimit C = ⋂ j : ℕ, _root_.closure
      (⋃ N : ℕ, ⋂ n : ℕ, ⋂ (_ : N ≤ n), Metric.cthickening (1 / ((j : ℝ) + 1)) (C n)) := by
  rw [innerSetLimit_eq_iInter_iUnion_iInter_cthickening]
  ext x
  simp only [mem_iInter]
  constructor
  · intro hx j
    exact subset_closure (hx _ (by positivity))
  · intro hx ε hε
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt (half_pos hε)
    have hxj := hx j
    rw [Metric.mem_closure_iff] at hxj
    obtain ⟨y, hy, hxy⟩ := hxj (1 / ((j : ℝ) + 1)) (by positivity)
    obtain ⟨N, hN⟩ := mem_iUnion.1 hy
    refine mem_iUnion.2 ⟨N, mem_iInter₂.2 fun n hn ↦ ?_⟩
    have hyn : y ∈ Metric.cthickening (1 / ((j : ℝ) + 1)) (C n) := mem_iInter₂.1 hN n hn
    have hx' : x ∈ Metric.cthickening (1 / ((j : ℝ) + 1))
        (Metric.cthickening (1 / ((j : ℝ) + 1)) (C n)) :=
      mem_cthickening_of_dist_le x y _ _ hyn hxy.le
    have := cthickening_cthickening_subset (by positivity) (by positivity) (C n) hx'
    exact cthickening_mono (by linarith) (C n) this

/-- **Theorem 14.20**, pointwise outer limit: `p-lim sup Sν` is closed-valued and measurable. -/
theorem SvMeasurable.pointwiseOuterLimit {S : ℕ → T → Set F} (h : ∀ n, SvMeasurable (S n)) :
    SvMeasurable (RW.pointwiseOuterLimit S) := by
  have heq : RW.pointwiseOuterLimit S =
      fun t ↦ ⋂ N : ℕ, _root_.closure (⋃ n : ℕ, ⋃ _ : N ≤ n, S n t) :=
    funext fun t ↦ outerSetLimit_eq_iInter_closure_iUnion_tail _
  rw [heq]
  refine SvMeasurable.iInter (fun N ↦ (SvMeasurable.iUnion fun n ↦ ?_).closure)
    (fun _ _ ↦ isClosed_closure)
  by_cases hn : N ≤ n
  · simp only [hn, iUnion_true]
    exact h n
  · simp only [hn, iUnion_false]
    exact svMeasurable_const ∅

/-- **Theorem 14.20**, pointwise inner limit: `p-lim inf Sν` is closed-valued and measurable. -/
theorem SvMeasurable.pointwiseInnerLimit {S : ℕ → T → Set F} (h : ∀ n, SvMeasurable (S n)) :
    SvMeasurable (RW.pointwiseInnerLimit S) := by
  have heq : RW.pointwiseInnerLimit S = fun t ↦ ⋂ j : ℕ, _root_.closure
      (⋃ N : ℕ, ⋂ n : ℕ, ⋂ (_ : N ≤ n), Metric.cthickening (1 / ((j : ℝ) + 1)) (S n t)) :=
    funext fun t ↦ innerSetLimit_eq_iInter_closure_iUnion_iInter_cthickening _
  rw [heq]
  refine SvMeasurable.iInter (fun j ↦ (SvMeasurable.iUnion fun N ↦ ?_).closure)
    (fun _ _ ↦ isClosed_closure)
  refine SvMeasurable.iInter (fun n ↦ ?_) (fun n t ↦ ?_)
  · by_cases hn : N ≤ n
    · simp only [hn, iInter_true]
      exact (h n).cthickening _
    · simp only [hn, iInter_false]
      exact svMeasurable_const univ
  · by_cases hn : N ≤ n
    · simp only [hn, iInter_true]
      exact isClosed_cthickening
    · simp only [hn, iInter_false]
      exact isClosed_univ

/-- **Theorem 14.20 (graphical and pointwise limits)**, pointwise part: the pointwise outer and
inner limits, and the pointwise limit when it exists, are closed-valued and measurable. -/
theorem pointwise_limits {S : ℕ → T → Set F} (h : ∀ n, SvMeasurable (S n)) :
    ((∀ t, IsClosed (RW.pointwiseOuterLimit S t)) ∧ SvMeasurable (RW.pointwiseOuterLimit S)) ∧
      ((∀ t, IsClosed (RW.pointwiseInnerLimit S t)) ∧
        SvMeasurable (RW.pointwiseInnerLimit S)) ∧
      ∀ L : T → Set F, PointwiseConverges S L → (∀ t, IsClosed (L t)) ∧ SvMeasurable L := by
  refine ⟨⟨fun t ↦ isClosed_outerSetLimit _, SvMeasurable.pointwiseOuterLimit h⟩,
    ⟨fun t ↦ isClosed_innerSetLimit _, SvMeasurable.pointwiseInnerLimit h⟩, fun L hL ↦ ?_⟩
  have heq : L = RW.pointwiseInnerLimit S := funext fun t ↦ ((hL t).inner_eq).symm
  rw [heq]
  exact ⟨fun t ↦ isClosed_innerSetLimit _, SvMeasurable.pointwiseInnerLimit h⟩

/-- **Theorem 14.20 (graphical and pointwise limits)**, graphical part: for a topological
parameter space whose σ-field contains the Borel sets (e.g. `T ∈ B(ℝᵈ)` with `A = B(T)` or
`L(T)`), the graphical outer and inner limits, and the graphical limit when it exists, are
closed-valued and measurable; no measurability of the `Sν` is needed. -/
theorem graphical_limits [TopologicalSpace T] [OpensMeasurableSpace T] (S : ℕ → T → Set F) :
    SvMeasurable (graphicalOuterLimit S) ∧ SvMeasurable (graphicalInnerLimit S) ∧
      ∀ L : T → Set F, GraphicalConverges S L → (∀ t, IsClosed (L t)) ∧ SvMeasurable L := by
  refine ⟨(svOsc_graphicalOuterLimit S).svMeasurable,
    (svOsc_graphicalInnerLimit S).svMeasurable, fun L hL ↦ ?_⟩
  have hgraph : svGraph L = svGraph (graphicalOuterLimit S) := by
    rw [svGraph_graphicalOuterLimit, hL.outer_eq]
  have heq : L = graphicalOuterLimit S := by
    funext t
    ext u
    have := Set.ext_iff.1 hgraph (t, u)
    simpa using this
  rw [heq]
  refine ⟨fun t ↦ ?_, (svOsc_graphicalOuterLimit S).svMeasurable⟩
  have hc := isClosed_svGraph_iff_svOsc.2 (svOsc_graphicalOuterLimit S)
  have : graphicalOuterLimit S t = (fun u ↦ (t, u)) ⁻¹' svGraph (graphicalOuterLimit S) := rfl
  rw [this]
  exact hc.preimage (Continuous.prodMk_right t)

end Theorem1420


section Proposition1422

variable {T F : Type*} [MeasurableSpace T] [MetricSpace F] [ProperSpace F]

/-- A **simple mapping**: its range consists of only finitely many sets. -/
def SvSimple (S : T → Set F) : Prop := (range S).Finite

omit [MeasurableSpace T] [ProperSpace F] in
theorem pkConverges_of_outer_subset_of_subset_inner {C : ℕ → Set F} {D : Set F}
    (h1 : outerSetLimit C ⊆ D) (h2 : D ⊆ innerSetLimit C) : PKConverges C D :=
  ⟨Subset.antisymm ((innerSetLimit_subset_outerSetLimit C).trans h1) h2,
    Subset.antisymm h1 (h2.trans (innerSetLimit_subset_outerSetLimit C))⟩

/-- **Proposition 14.22 (limits of simple mappings)**: a closed-valued mapping is measurable if
and only if it is the pointwise limit of a sequence of simple measurable mappings.  The
approximants are `Sν(t) = Dν ∩ (S(t) + ν⁻¹ IB)` for finite `ν⁻¹`-nets `Dν` of `ν IB` (the
book's `ν IB ∩ ν⁻¹ ℤⁿ`). -/
theorem limits_of_simple_mappings {S : T → Set F} (hSc : ∀ t, IsClosed (S t)) :
    SvMeasurable S ↔ ∃ Sseq : ℕ → T → Set F,
      (∀ n, SvSimple (Sseq n) ∧ SvMeasurable (Sseq n)) ∧ PointwiseConverges Sseq S := by
  constructor
  · intro hS
    rcases isEmpty_or_nonempty F with hF | ⟨⟨x₀⟩⟩
    · refine ⟨fun _ _ ↦ ∅, fun n ↦ ⟨(finite_singleton ∅).subset ?_, svMeasurable_const ∅⟩,
        fun t ↦ ?_⟩
      · rintro _ ⟨t, rfl⟩
        rfl
      · rw [eq_empty_of_isEmpty (S t)]
        exact ⟨eq_empty_of_isEmpty _, eq_empty_of_isEmpty _⟩
    set r : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1) with hr
    have hrpos : ∀ n, 0 < r n := fun n ↦ by positivity
    have hnet : ∀ n : ℕ, ∃ D ⊆ closedBall x₀ n, D.Finite ∧ closedBall x₀ n ⊆ ⋃ z ∈ D, ball z (r n) :=
      fun n ↦ finite_cover_balls_of_compact (isCompact_closedBall x₀ n) (hrpos n)
    choose D hDsub hDfin hDcover using hnet
    refine ⟨fun n t ↦ D n ∩ Metric.cthickening (r n) (S t), fun n ↦ ⟨?_, ?_⟩, fun t ↦ ?_⟩
    · exact (hDfin n).finite_subsets.subset (by rintro _ ⟨t, rfl⟩; exact inter_subset_left)
    · exact (svMeasurable_const (D n)).inter (hS.cthickening (r n)) (fun _ ↦ (hDfin n).isClosed)
        (fun _ ↦ isClosed_cthickening)
    · refine pkConverges_of_outer_subset_of_subset_inner ?_ ?_
      · intro x hx
        rw [← (hSc t).closure_eq, Metric.mem_closure_iff]
        intro ε hε
        have hfreq := hx (ball x (ε / 2)) (ball_mem_nhds x (half_pos hε))
        have hev : ∀ᶠ n in atTop, r n < ε / 2 := by
          have : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
          exact this.eventually (gt_mem_nhds (half_pos hε))
        obtain ⟨n, ⟨z, ⟨-, hzS⟩, hzx⟩, hrn⟩ := (hfreq.and_eventually hev).exists
        have hzS' : z ∈ thickening (ε / 2) (S t) :=
          cthickening_subset_thickening' (half_pos hε) hrn _ hzS
        obtain ⟨b, hb, hzb⟩ := mem_thickening_iff.1 hzS'
        refine ⟨b, hb, ?_⟩
        have hzx' : dist z x < ε / 2 := hzx
        calc dist x b ≤ dist x z + dist z b := dist_triangle _ _ _
          _ < ε / 2 + ε / 2 := by rw [dist_comm] at hzx'; linarith
          _ = ε := by ring
      · intro x hx
        rw [mem_innerSetLimit_iff_eventually_ball]
        intro ε hε
        obtain ⟨N, hN⟩ := exists_nat_ge (dist x x₀)
        have hev : ∀ᶠ n in atTop, r n < ε := by
          have : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
          exact this.eventually (gt_mem_nhds hε)
        filter_upwards [hev, eventually_ge_atTop N] with n hrn hn
        have hxball : x ∈ closedBall x₀ n := by
          rw [mem_closedBall]
          exact hN.trans (by exact_mod_cast hn)
        obtain ⟨z, hzD, hxz⟩ := mem_iUnion₂.1 (hDcover n hxball)
        have hxz' : dist x z < r n := hxz
        refine ⟨z, ⟨hzD, mem_cthickening_of_dist_le z x (r n) (S t) hx ?_⟩, ?_⟩
        · rw [dist_comm]
          exact hxz'.le
        · rw [mem_ball, dist_comm]
          linarith
  · rintro ⟨Sseq, hseq, hconv⟩
    have heq : S = RW.pointwiseInnerLimit Sseq := funext fun t ↦ ((hconv t).inner_eq).symm
    rw [heq]
    exact SvMeasurable.pointwiseInnerLimit fun n ↦ (hseq n).2

end Proposition1422

section Proposition1423

variable {T F : Type*} [MeasurableSpace T] [MetricSpace F] [ProperSpace F]
  [MeasurableSpace F] [BorelSpace F]

omit [ProperSpace F] in
/-- **Proposition 14.23(a)**: a pointwise limit of measurable selections of the `Sν` is a
measurable selection of `p-lim inf Sν`, and also of the graphical inner limit when `T` is a
topological space. -/
theorem measurable_selection_of_tendsto {S : ℕ → T → Set F} {s : ℕ → T → F} {s₀ : T → F}
    (hs : ∀ n, Measurable (s n)) (hsS : ∀ n t, s n t ∈ S n t)
    (hlim : ∀ t, Tendsto (fun n ↦ s n t) atTop (𝓝 (s₀ t))) :
    Measurable s₀ ∧ (∀ t, s₀ t ∈ RW.pointwiseInnerLimit S t) ∧
      ∀ [TopologicalSpace T] (t : T), s₀ t ∈ graphicalInnerLimit S t := by
  have hmem : ∀ t, s₀ t ∈ RW.pointwiseInnerLimit S t := by
    intro t V hV
    filter_upwards [(hlim t).eventually_mem hV] with n hn
    exact ⟨s n t, hsS n t, hn⟩
  refine ⟨measurable_of_tendsto_metrizable hs (tendsto_pi_nhds.2 hlim), hmem, fun t ↦ ?_⟩
  exact pointwiseInnerLimit_subset_graphicalInnerLimit S t (hmem t)

/-- The infimal distance `t ↦ d(σ(t), S(t))` to a measurable mapping along a measurable function
is measurable (joint measurability of the Carathéodory function `(t, y) ↦ d(y, S(t))`). -/
theorem SvMeasurable.measurable_infDist_comp {S : T → Set F} (hS : SvMeasurable S) {σ : T → F}
    (hσ : Measurable σ) : Measurable fun t ↦ infDist (σ t) (S t) := by
  have hcont : ∀ t, Continuous fun y : F ↦ infDist y (S t) := fun t ↦ continuous_infDist_pt (S t)
  have hmeas : ∀ y : F, Measurable fun t ↦ infDist y (S t) := fun y ↦
    (hS.measurable_infEDist y).ennreal_toReal
  have hjoint : Measurable (Function.uncurry fun (y : F) (t : T) ↦ infDist y (S t)) :=
    MeasureTheory.measurable_uncurry_of_continuous_of_measurable hcont hmeas
  have h2 : Measurable ((Function.uncurry fun (y : F) (t : T) ↦ infDist y (S t)) ∘
      fun t ↦ (σ t, t)) := hjoint.comp (hσ.prodMk measurable_id)
  exact h2

/-- Proposition 14.23(b), first step: for every measurable `σ` there are measurable selections
`rν` of the `Sν` converging to `σ(t)` wherever `σ(t) ∈ p-lim inf Sν (t)`. -/
theorem exists_selections_tendsto {S : ℕ → T → Set F} (hS : ∀ n, SvMeasurable (S n))
    (hSc : ∀ n t, IsClosed (S n t)) (hdom : ∀ n t, (S n t).Nonempty) {σ : T → F}
    (hσ : Measurable σ) :
    ∃ r : ℕ → T → F, (∀ n, Measurable (r n)) ∧ (∀ n t, r n t ∈ S n t) ∧
      ∀ t, σ t ∈ RW.pointwiseInnerLimit S t → Tendsto (fun n ↦ r n t) atTop (𝓝 (σ t)) := by
  rcases isEmpty_or_nonempty T with hT | ⟨⟨t₀⟩⟩
  · exact ⟨fun _ t ↦ isEmptyElim t, fun _ ↦ Subsingleton.measurable, fun _ t ↦ isEmptyElim t,
      fun t ↦ isEmptyElim t⟩
  haveI : Nonempty F := ⟨(hdom 0 t₀).some⟩
  have hR : ∀ n : ℕ, ∃ r : T → F, Measurable r ∧ ∀ t, r t ∈ S n t ∧
      dist (r t) (σ t) ≤ infDist (σ t) (S n t) + 1 / ((n : ℝ) + 1) := by
    intro n
    set φ : T → F → ℝ := fun t x ↦ dist x (σ t) - infDist (σ t) (S n t) - 1 / ((n : ℝ) + 1)
    have hφ : IsCaratheodory φ := by
      refine ⟨fun x ↦ ?_, fun t ↦ ?_⟩
      · exact ((measurable_const.dist hσ).sub ((hS n).measurable_infDist_comp hσ)).sub
          measurable_const
      · exact ((continuous_id.dist continuous_const).sub continuous_const).sub continuous_const
    obtain ⟨hLc, hL⟩ := hφ.svMeasurable_preimage (S := fun _ ↦ Iic (0 : ℝ))
      (svMeasurable_const _) (fun _ ↦ isClosed_Iic)
    have hRm := (hS n).inter hL (hSc n) hLc
    have hRne : ∀ t, t ∈ svDom (fun t ↦ S n t ∩ {x | φ t x ∈ Iic 0}) := by
      intro t
      obtain ⟨y, hy, hyd⟩ := (hSc n t).exists_infDist_eq_dist (hdom n t) (σ t)
      refine ⟨y, hy, ?_⟩
      simp only [φ, mem_setOf_eq, mem_Iic]
      rw [dist_comm, ← hyd]
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    obtain ⟨r, hrm, hrS⟩ := hRm.exists_measurable_selection
      (fun t ↦ (hSc n t).inter (hLc t))
    refine ⟨r, hrm, fun t ↦ ⟨(hrS t (hRne t)).1, ?_⟩⟩
    have := (hrS t (hRne t)).2
    simp only [φ, mem_setOf_eq, mem_Iic] at this
    linarith
  choose r hrm hr using hR
  refine ⟨r, hrm, fun n t ↦ (hr n t).1, fun t ht ↦ ?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  have hinf : Tendsto (fun n ↦ infDist (σ t) (S n t)) atTop (𝓝 0) := by
    have h := (mem_innerSetLimit_iff_tendsto_infEDist).1 ht
    have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    simpa [infDist] using h2
  have hsum : Tendsto (fun n : ℕ ↦ infDist (σ t) (S n t) + 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa using hinf.add tendsto_one_div_add_atTop_nhds_zero_nat
  exact squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ (hr n t).2) hsum

/-- **Proposition 14.23(b) (convergence of measurable selections)**: for closed-valued
measurable `Sν` with `dom Sν = T` and any Castaing representation `{sκ}` of
`S = p-lim inf Sν`, there are Castaing representations `{sν,κ}` of the `Sν` with
`sν,κ(t) → sκ(t)` for every `κ` and every `t ∈ dom S`. -/
theorem convergence_of_castaing_representations {S : ℕ → T → Set F}
    (hS : ∀ n, SvMeasurable (S n)) (hSc : ∀ n t, IsClosed (S n t))
    (hdom : ∀ n t, (S n t).Nonempty) {s : ℕ → T → F}
    (hs : IsCastaingRepresentation (RW.pointwiseInnerLimit S) s) :
    ∃ x : ℕ → ℕ → T → F, (∀ ν, IsCastaingRepresentation (S ν) (x ν)) ∧
      ∀ κ, ∀ t ∈ svDom (RW.pointwiseInnerLimit S),
        Tendsto (fun ν ↦ x ν κ t) atTop (𝓝 (s κ t)) := by
  rcases isEmpty_or_nonempty T with hT | ⟨⟨t₀⟩⟩
  · refine ⟨fun _ _ t ↦ isEmptyElim t, fun ν ↦ ⟨fun κ ↦ Subsingleton.measurable,
      fun t ↦ isEmptyElim t⟩, fun κ t ↦ isEmptyElim t⟩
  haveI : Nonempty F := ⟨(hdom 0 t₀).some⟩
  have hr : ∀ κ, ∃ r : ℕ → T → F, (∀ n, Measurable (r n)) ∧ (∀ n t, r n t ∈ S n t) ∧
      ∀ t, s κ t ∈ RW.pointwiseInnerLimit S t → Tendsto (fun n ↦ r n t) atTop (𝓝 (s κ t)) :=
    fun κ ↦ exists_selections_tendsto hS hSc hdom (hs.1 κ)
  choose r hrm hrS hrt using hr
  have hc : ∀ ν, ∃ c : ℕ → T → F, IsCastaingRepresentation (S ν) c := fun ν ↦
    (hS ν).exists_castaingRepresentation (hSc ν)
  choose c hc using hc
  have hcS : ∀ ν j t, c ν j t ∈ S ν t := fun ν j t ↦ by
    rw [(hc ν).2 t (hdom ν t)]
    exact subset_closure ⟨j, rfl⟩
  refine ⟨fun ν κ ↦ if κ ≤ ν then r κ ν else c ν (κ - ν - 1), fun ν ↦ ⟨fun κ ↦ ?_, fun t _ ↦ ?_⟩,
    fun κ t ht ↦ ?_⟩
  · by_cases h : κ ≤ ν
    · simp only [h, if_true]
      exact hrm κ ν
    · simp only [h, if_false]
      exact (hc ν).1 _
  · apply Subset.antisymm
    · rw [(hc ν).2 t (hdom ν t)]
      refine closure_mono ?_
      rintro _ ⟨j, rfl⟩
      refine ⟨j + ν + 1, ?_⟩
      have h1 : ¬ (j + ν + 1 ≤ ν) := by omega
      have h2 : j + ν + 1 - ν - 1 = j := by omega
      simp only [h1, if_false, h2]
    · refine closure_minimal ?_ (hSc ν t)
      rintro _ ⟨κ, rfl⟩
      by_cases h : κ ≤ ν
      · simp only [h, if_true]
        exact hrS κ ν t
      · simp only [h, if_false]
        exact hcS ν _ t
  · have hmem : s κ t ∈ RW.pointwiseInnerLimit S t := by
      rw [hs.2 t ht]
      exact subset_closure ⟨κ, rfl⟩
    refine (hrt κ t hmem).congr' ?_
    filter_upwards [eventually_ge_atTop κ] with ν hν
    simp only [hν, if_true]

end Proposition1423

end RW
