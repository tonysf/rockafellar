/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 14: Almost everywhere and almost uniform convergence

Propositions 14.24 and 14.25 of Rockafellar–Wets for closed-valued measurable mappings
`S, Sν : T ⇉ F` (`F` finite-dimensional) and a measure `μ`.

* 14.24: a.e. pointwise convergence `Sν →p S` is equivalent to the hit-and-miss conditions (b),
  their ball versions (c) and a.e. convergence of distance functions (d); with
  `A₁ ⊂₀ A₂` written `A₁ ≤ᵐ[μ] A₂` and `*lim inf`, `*lim sup` the sets of `t` lying eventually,
  resp. frequently, in the given sets.  Condition (e) on the excess mappings `R^ν_ε` implies
  a.e. convergence for every measure; the converse needs `μ` finite (more precisely, continuity
  from above), which is the correction: on `ℕ` with the counting measure,
  `Sν(t) = {1}` for `t ≥ ν` and `{0}` otherwise converge everywhere to `S ≡ {0}`, while
  `μ((R^ν_ε)⁻¹(2𝔹)) = ∞` for all `ν` (`almost_everywhere_convergence_counterexample`).  For an
  arbitrary measure, (e) holds iff (a) holds and each `μ((R^ν_ε)⁻¹(𝔹(x, ρ)))` is eventually
  finite (`tendsto_measure_svExcessMap_iff`).
* 14.25: when `μ(T) < ∞`, a.e. convergence is equivalent to almost uniform convergence
  (Egorov's argument with the measurable sets `(R^ν_ε)⁻¹(ρ𝔹)`).

`S(t) + ε𝔹` is written `cthickening ε (S t)`, which is the same set for closed `S(t)`
(`add_closedBall_zero_eq_cthickening`).
-/

import RockafellarWets.Chapter14.MeasurableSelections
import RockafellarWets.Chapter4.HitAndMiss
import RockafellarWets.Chapter4.DistanceConvergence
import RockafellarWets.Chapter4.UniformApproximation
import RockafellarWets.Chapter5.ContinuousUniformConvergence
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Measure.Count

open Set Filter Topology Metric MeasureTheory
open scoped ENNReal NNReal Pointwise

noncomputable section

namespace RW

section Helpers

variable {F : Type*} [NormedAddCommGroup F] [ProperSpace F]

/-- `C + ε𝔹` is the closed `ε`-thickening of a closed set `C`. -/
theorem add_closedBall_zero_eq_cthickening {C : Set F} (hC : IsClosed C) {ε : ℝ} (hε : 0 ≤ ε) :
    C + closedBall (0 : F) ε = cthickening ε C := by
  rw [hC.cthickening_eq_biUnion_closedBall hε]
  ext x
  simp only [Set.mem_add, mem_iUnion, exists_prop]
  constructor
  · rintro ⟨c, hc, b, hb, rfl⟩
    refine ⟨c, hc, ?_⟩
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    rwa [mem_closedBall, dist_zero_right] at hb
  · rintro ⟨c, hc, hx⟩
    refine ⟨c, hc, x - c, ?_, add_sub_cancel c x⟩
    rw [mem_closedBall, dist_zero_right]
    rwa [mem_closedBall, dist_eq_norm] at hx

omit [NormedAddCommGroup F] [ProperSpace F] in
theorem pkConverges_of_subset_of_subset {E : Type*} [TopologicalSpace E] {C : ℕ → Set E}
    {D : Set E} (hin : D ⊆ innerSetLimit C) (hout : outerSetLimit C ⊆ D) : PKConverges C D :=
  ⟨le_antisymm ((innerSetLimit_subset_outerSetLimit C).trans hout) hin,
    le_antisymm hout (hin.trans (innerSetLimit_subset_outerSetLimit C))⟩

end Helpers

variable {T F : Type*} [MeasurableSpace T] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

section Excess

/-- For closed-valued measurable `K` and measurable `S`, the set of `t` such that `K(t)` contains
a point at distance more than `ε` from `S(t)` is measurable: the condition is open in the point,
and the points of a Castaing representation are dense in `K(t)`. -/
theorem measurableSet_exists_mem_lt_infEDist {K S : T → Set F} (hK : SvMeasurable K)
    (hKc : ∀ t, IsClosed (K t)) (hS : SvMeasurable S) (ε : ℝ≥0∞) :
    MeasurableSet {t | ∃ y ∈ K t, ε < infEDist y (S t)} := by
  obtain ⟨x, hxm, hx⟩ := hK.exists_castaingRepresentation hKc
  have hjoint : ∀ i, Measurable fun t ↦ infEDist (x i t) (S t) := fun i ↦ by
    have h : Measurable (Function.uncurry fun (y : F) (t : T) ↦ infEDist y (S t)) :=
      measurable_uncurry_of_continuous_of_measurable (fun _ ↦ continuous_infEDist)
        fun y ↦ hS.measurable_infEDist y
    exact h.comp ((hxm i).prodMk measurable_id)
  have heq : {t | ∃ y ∈ K t, ε < infEDist y (S t)} =
      svDom K ∩ ⋃ i, {t | ε < infEDist (x i t) (S t)} := by
    ext t
    simp only [mem_setOf_eq, mem_inter_iff, mem_iUnion]
    constructor
    · rintro ⟨y, hyK, hy⟩
      refine ⟨⟨y, hyK⟩, ?_⟩
      have hyc : y ∈ _root_.closure (range fun i ↦ x i t) := by
        rw [← hx t ⟨y, hyK⟩]
        exact hyK
      have hU : {z | ε < infEDist z (S t)} ∈ 𝓝 y :=
        (isOpen_lt continuous_const continuous_infEDist).mem_nhds hy
      obtain ⟨_, hz, ⟨i, rfl⟩⟩ := mem_closure_iff_nhds.1 hyc _ hU
      exact ⟨i, hz⟩
    · rintro ⟨hdom, i, hi⟩
      refine ⟨x i t, ?_, hi⟩
      rw [hx t hdom]
      exact subset_closure ⟨i, rfl⟩
  rw [heq]
  exact hK.measurableSet_svDom.inter
    (MeasurableSet.iUnion fun i ↦ measurableSet_lt measurable_const (hjoint i))

omit [MeasurableSpace T] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F]
  [BorelSpace F] in
/-- The excess mappings of Proposition 14.24(e):
`R^ν_ε(t) = ⋃_{κ ≥ ν} [Sκ(t) \ (S(t) + ε𝔹)] ∪ [S(t) \ (Sκ(t) + ε𝔹)]`. -/
def svExcessMap (Sseq : ℕ → T → Set F) (S : T → Set F) (ε : ℝ) (ν : ℕ) (t : T) : Set F :=
  ⋃ κ ≥ ν, ((Sseq κ t \ cthickening ε (S t)) ∪ (S t \ cthickening ε (Sseq κ t)))

omit [MeasurableSpace T] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F]
  [BorelSpace F] in
theorem svPreimage_svExcessMap (Sseq : ℕ → T → Set F) (S : T → Set F) (ε : ℝ) (ν : ℕ)
    (B : Set F) :
    svPreimage (svExcessMap Sseq S ε ν) B = ⋃ κ ≥ ν,
      ({t | ∃ y ∈ Sseq κ t ∩ B, ENNReal.ofReal ε < infEDist y (S t)} ∪
        {t | ∃ y ∈ S t ∩ B, ENNReal.ofReal ε < infEDist y (Sseq κ t)}) := by
  ext t
  simp only [svPreimage, svExcessMap, mem_setOf_eq, mem_iUnion, mem_union, exists_prop]
  constructor
  · rintro ⟨y, hy, hyB⟩
    simp only [mem_iUnion, mem_union, mem_diff, mem_cthickening_iff, not_le,
      exists_prop] at hy
    obtain ⟨κ, hκ, h | h⟩ := hy
    · exact ⟨κ, hκ, Or.inl ⟨y, ⟨h.1, hyB⟩, h.2⟩⟩
    · exact ⟨κ, hκ, Or.inr ⟨y, ⟨h.1, hyB⟩, h.2⟩⟩
  · rintro ⟨κ, hκ, ⟨y, hy, hlt⟩ | ⟨y, hy, hlt⟩⟩
    · refine ⟨y, ?_, hy.2⟩
      simp only [mem_iUnion, mem_union, mem_diff, mem_cthickening_iff, not_le, exists_prop]
      exact ⟨κ, hκ, Or.inl ⟨hy.1, hlt⟩⟩
    · refine ⟨y, ?_, hy.2⟩
      simp only [mem_iUnion, mem_union, mem_diff, mem_cthickening_iff, not_le, exists_prop]
      exact ⟨κ, hκ, Or.inr ⟨hy.1, hlt⟩⟩

/-- The sets `(R^ν_ε)⁻¹(B)`, `B` closed, are measurable. -/
theorem measurableSet_svPreimage_svExcessMap {Sseq : ℕ → T → Set F} {S : T → Set F}
    (hSseq : ∀ n, SvMeasurable (Sseq n)) (hSseqc : ∀ n t, IsClosed (Sseq n t))
    (hS : SvMeasurable S) (hSc : ∀ t, IsClosed (S t)) (ε : ℝ) (ν : ℕ) {B : Set F}
    (hB : IsClosed B) : MeasurableSet (svPreimage (svExcessMap Sseq S ε ν) B) := by
  rw [svPreimage_svExcessMap]
  refine MeasurableSet.iUnion fun κ ↦ MeasurableSet.iUnion fun _ ↦ MeasurableSet.union ?_ ?_
  · exact measurableSet_exists_mem_lt_infEDist ((hSseq κ).inter_isClosed (hSseqc κ) hB)
      (fun t ↦ (hSseqc κ t).inter hB) hS _
  · exact measurableSet_exists_mem_lt_infEDist (hS.inter_isClosed hSc hB)
      (fun t ↦ (hSc t).inter hB) (hSseq κ) _

omit [MeasurableSpace T] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F]
  [BorelSpace F] in
theorem svPreimage_svExcessMap_antitone (Sseq : ℕ → T → Set F) (S : T → Set F) (ε : ℝ)
    (B : Set F) : Antitone fun ν ↦ svPreimage (svExcessMap Sseq S ε ν) B := by
  intro ν ν' hνν' t
  simp only [svPreimage_svExcessMap, mem_iUnion, exists_prop]
  rintro ⟨κ, hκ, h⟩
  exact ⟨κ, hνν'.trans hκ, h⟩

omit [MeasurableSpace T] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F]
  [BorelSpace F] in
/-- Outside `(R^ν_ε)⁻¹(B)`, the `ε`-inclusions hold on `B` for all `κ ≥ ν`. -/
theorem subset_cthickening_of_not_mem_svPreimage_svExcessMap {Sseq : ℕ → T → Set F}
    {S : T → Set F} {ε : ℝ} {ν : ℕ} {B : Set F} {t : T}
    (h : t ∉ svPreimage (svExcessMap Sseq S ε ν) B) {κ : ℕ} (hκ : ν ≤ κ) :
    Sseq κ t ∩ B ⊆ cthickening ε (S t) ∧ S t ∩ B ⊆ cthickening ε (Sseq κ t) := by
  rw [svPreimage_svExcessMap] at h
  simp only [mem_iUnion, mem_union, mem_setOf_eq, exists_prop, not_exists, not_and,
    not_or] at h
  refine ⟨fun y hy ↦ ?_, fun y hy ↦ ?_⟩
  · by_contra hyc
    rw [mem_cthickening_iff, not_le] at hyc
    exact (h κ hκ).1 y hy hyc
  · by_contra hyc
    rw [mem_cthickening_iff, not_le] at hyc
    exact (h κ hκ).2 y hy hyc

omit [MeasurableSpace T] [MeasurableSpace F] [BorelSpace F] in
/-- Pointwise convergence at `t` makes `t` eventually leave `(R^ν_ε)⁻¹(𝔹(x, ρ))`
(Theorem 4.10). -/
theorem eventually_not_mem_svPreimage_svExcessMap {Sseq : ℕ → T → Set F} {S : T → Set F}
    {t : T} (hSc : IsClosed (S t)) (h : PKConverges (fun n ↦ Sseq n t) (S t)) {ε : ℝ}
    (hε : 0 < ε) (x : F) (ρ : ℝ) :
    ∀ᶠ ν in atTop, t ∉ svPreimage (svExcessMap Sseq S ε ν) (closedBall x ρ) := by
  obtain ⟨hin, hout⟩ :=
    (pkConverges_iff_eventuallyInnerApproximates_and_eventuallyOuterApproximates hSc).1 h
  set ρ' : ℝ := ‖x‖ + |ρ| + 1
  have hρ' : 0 < ρ' := by positivity
  have hball : closedBall x ρ ⊆ closedBall 0 ρ' := by
    intro y hy
    rw [mem_closedBall, dist_eq_norm] at hy
    rw [mem_closedBall, dist_zero_right]
    calc ‖y‖ = ‖(y - x) + x‖ := by rw [sub_add_cancel]
      _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
      _ ≤ ρ' := by have := le_abs_self ρ; simp only [ρ']; linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((hin ρ' hρ' ε hε).and (hout ρ' hρ' ε hε))
  refine eventually_atTop.2 ⟨N, fun ν hν ht ↦ ?_⟩
  rw [svPreimage_svExcessMap] at ht
  simp only [mem_iUnion, mem_union, mem_setOf_eq, exists_prop] at ht
  obtain ⟨κ, hκ, ⟨y, hy, hlt⟩ | ⟨y, hy, hlt⟩⟩ := ht
  · have hyt : y ∈ thickening ε (S t) := (hN κ (hν.trans hκ)).2 ⟨hy.1, hball hy.2⟩
    have := thickening_subset_cthickening ε (S t) hyt
    rw [mem_cthickening_iff] at this
    exact (not_le.2 hlt) this
  · have hyt : y ∈ thickening ε (Sseq κ t) := (hN κ (hν.trans hκ)).1 ⟨hy.1, hball hy.2⟩
    have := thickening_subset_cthickening ε (Sseq κ t) hyt
    rw [mem_cthickening_iff] at this
    exact (not_le.2 hlt) this

end Excess

section Proposition1424

omit [MeasurableSpace F] [BorelSpace F] in
/-- **Proposition 14.24**, (e) ⇒ (a), for any measure. -/
theorem ae_pkConverges_of_tendsto_measure_svExcessMap (μ : Measure T) {Sseq : ℕ → T → Set F}
    {S : T → Set F} (hSc : ∀ t, IsClosed (S t))
    (he : ∀ x : F, ∀ ε ρ : ℝ, 0 < ε → 0 < ρ →
      Tendsto (fun ν ↦ μ (svPreimage (svExcessMap Sseq S ε ν) (closedBall x ρ))) atTop (𝓝 0)) :
    ∀ᵐ t ∂μ, PKConverges (fun n ↦ Sseq n t) (S t) := by
  set W : ℕ → Set T := fun k ↦ ⋂ ν, svPreimage (svExcessMap Sseq S (1 / ((k : ℝ) + 1)) ν)
    (closedBall 0 ((k : ℝ) + 1)) with hWdef
  have hW0 : ∀ k, μ (W k) = 0 := by
    intro k
    have h := he 0 (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) (by positivity) (by positivity)
    refine le_antisymm (ge_of_tendsto' h fun ν ↦ measure_mono (iInter_subset _ ν)) (zero_le _)
  have hN : μ (⋃ k, W k) = 0 := measure_iUnion_null hW0
  refine ae_iff.2 (measure_mono_null (fun t ht ↦ ?_) hN)
  simp only [mem_setOf_eq] at ht
  by_contra htN
  simp only [mem_iUnion, not_exists, hWdef, mem_iInter, not_forall] at htN
  choose ν hν using htN
  apply ht
  rw [pkConverges_iff_eventuallyInnerApproximates_and_eventuallyOuterApproximates (hSc t)]
  have key : ∀ ρ > 0, ∀ ε > 0, ∀ᶠ n in atTop,
      S t ∩ closedBall 0 ρ ⊆ thickening ε (Sseq n t) ∧
        Sseq n t ∩ closedBall 0 ρ ⊆ thickening ε (S t) := by
    intro ρ _ ε hε
    obtain ⟨k, hk⟩ := exists_nat_gt (max ρ (1 / ε))
    have hk1 : ρ ≤ (k : ℝ) + 1 := by linarith [le_max_left ρ (1 / ε)]
    have hk2 : 1 / ((k : ℝ) + 1) < ε := by
      have h1 : 1 / ε < (k : ℝ) + 1 := by linarith [le_max_right ρ (1 / ε)]
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hε] at h1
      linarith
    refine eventually_atTop.2 ⟨ν k, fun n hn ↦ ?_⟩
    have h := subset_cthickening_of_not_mem_svPreimage_svExcessMap (hν k) hn
    refine ⟨fun y hy ↦ ?_, fun y hy ↦ ?_⟩
    · exact cthickening_subset_thickening' hε hk2 _
        (h.2 ⟨hy.1, closedBall_subset_closedBall hk1 hy.2⟩)
    · exact cthickening_subset_thickening' hε hk2 _
        (h.1 ⟨hy.1, closedBall_subset_closedBall hk1 hy.2⟩)
  exact ⟨fun ρ hρ ε hε ↦ (key ρ hρ ε hε).mono fun _ h ↦ h.1,
    fun ρ hρ ε hε ↦ (key ρ hρ ε hε).mono fun _ h ↦ h.2⟩

/-- **Proposition 14.24**, (a) ⇒ (e), for any measure, provided one of the measures
`μ((R^ν_ε)⁻¹(𝔹(x, ρ)))` is finite: continuity from above needs only one finite term. -/
theorem tendsto_measure_svExcessMap_of_ae_of_exists_ne_top (μ : Measure T)
    {Sseq : ℕ → T → Set F} {S : T → Set F} (hSseq : ∀ n, SvMeasurable (Sseq n))
    (hSseqc : ∀ n t, IsClosed (Sseq n t)) (hS : SvMeasurable S) (hSc : ∀ t, IsClosed (S t))
    (hae : ∀ᵐ t ∂μ, PKConverges (fun n ↦ Sseq n t) (S t)) (x : F) {ε : ℝ} (hε : 0 < ε)
    (ρ : ℝ) (hfin : ∃ ν, μ (svPreimage (svExcessMap Sseq S ε ν) (closedBall x ρ)) ≠ ⊤) :
    Tendsto (fun ν ↦ μ (svPreimage (svExcessMap Sseq S ε ν) (closedBall x ρ))) atTop (𝓝 0) := by
  have h := tendsto_measure_iInter_atTop (μ := μ)
    (fun ν ↦ (measurableSet_svPreimage_svExcessMap hSseq hSseqc hS hSc ε ν
      isClosed_closedBall).nullMeasurableSet)
    (svPreimage_svExcessMap_antitone Sseq S ε (closedBall x ρ)) hfin
  have h0 : μ (⋂ ν, svPreimage (svExcessMap Sseq S ε ν) (closedBall x ρ)) = 0 := by
    refine measure_mono_null (fun t ht ↦ ?_) (ae_iff.1 hae)
    simp only [mem_setOf_eq]
    intro hpk
    obtain ⟨ν, hν⟩ := (eventually_not_mem_svPreimage_svExcessMap (hSc t) hpk hε x ρ).exists
    exact hν (mem_iInter.1 ht ν)
  rw [h0] at h
  exact h

/-- **Proposition 14.24**, (a) ⇒ (e), for a finite measure (continuity from above). -/
theorem tendsto_measure_svExcessMap_of_ae (μ : Measure T) [IsFiniteMeasure μ]
    {Sseq : ℕ → T → Set F} {S : T → Set F} (hSseq : ∀ n, SvMeasurable (Sseq n))
    (hSseqc : ∀ n t, IsClosed (Sseq n t)) (hS : SvMeasurable S) (hSc : ∀ t, IsClosed (S t))
    (hae : ∀ᵐ t ∂μ, PKConverges (fun n ↦ Sseq n t) (S t)) (x : F) {ε : ℝ} (hε : 0 < ε)
    (ρ : ℝ) :
    Tendsto (fun ν ↦ μ (svPreimage (svExcessMap Sseq S ε ν) (closedBall x ρ))) atTop (𝓝 0) :=
  tendsto_measure_svExcessMap_of_ae_of_exists_ne_top μ hSseq hSseqc hS hSc hae x hε ρ
    ⟨0, measure_ne_top _ _⟩

/-- **Proposition 14.24**, condition (e) for an arbitrary measure: (e) holds if and only if (a)
holds and every `μ((R^ν_ε)⁻¹(𝔹(x, ρ)))` is finite for some `ν`.  For finite `μ` the second
condition is automatic, which gives (a) ⇔ (e) (`almost_everywhere_convergence`); for the counting
measure on `ℕ` it can fail (`almost_everywhere_convergence_counterexample`). -/
theorem tendsto_measure_svExcessMap_iff (μ : Measure T) {S : T → Set F} {Sseq : ℕ → T → Set F}
    (hSc : ∀ t, IsClosed (S t)) (hSseqc : ∀ n t, IsClosed (Sseq n t)) (hS : SvMeasurable S)
    (hSseq : ∀ n, SvMeasurable (Sseq n)) :
    (∀ x : F, ∀ ε ρ : ℝ, 0 < ε → 0 < ρ →
        Tendsto (fun ν ↦ μ (svPreimage (svExcessMap Sseq S ε ν) (closedBall x ρ))) atTop
          (𝓝 0)) ↔
      (∀ᵐ t ∂μ, PKConverges (fun n ↦ Sseq n t) (S t)) ∧
        ∀ x : F, ∀ ε ρ : ℝ, 0 < ε → 0 < ρ →
          ∃ ν, μ (svPreimage (svExcessMap Sseq S ε ν) (closedBall x ρ)) ≠ ⊤ := by
  constructor
  · intro he
    refine ⟨ae_pkConverges_of_tendsto_measure_svExcessMap μ hSc he, fun x ε ρ hε hρ ↦ ?_⟩
    obtain ⟨ν, hν⟩ := ((he x ε ρ hε hρ).eventually (Iio_mem_nhds ENNReal.zero_lt_top)).exists
    exact ⟨ν, (Set.mem_Iio.1 hν).ne⟩
  · rintro ⟨hae, hfin⟩ x ε ρ hε hρ
    exact tendsto_measure_svExcessMap_of_ae_of_exists_ne_top μ hSseq hSseqc hS hSc hae x hε ρ
      (hfin x ε ρ hε hρ)

/-- **Proposition 14.24 (almost everywhere convergence)**, adapted.  For closed-valued
measurable `S, Sν : T ⇉ F`: (a) `Sν →p S` a.e., (b) the hit-and-miss inclusions, (c) their
ball versions and (d) a.e. convergence of the distance functions are equivalent; (e) implies
(a), and (a) implies (e) when `μ` is finite (`almost_everywhere_convergence_counterexample`
shows that finiteness cannot be dropped; `tendsto_measure_svExcessMap_iff` characterizes (e) for
an arbitrary measure). -/
theorem almost_everywhere_convergence (μ : Measure T) {S : T → Set F} {Sseq : ℕ → T → Set F}
    (hSc : ∀ t, IsClosed (S t)) (hSseqc : ∀ n t, IsClosed (Sseq n t)) (hS : SvMeasurable S)
    (hSseq : ∀ n, SvMeasurable (Sseq n)) :
    List.TFAE [
      ∀ᵐ t ∂μ, PKConverges (fun n ↦ Sseq n t) (S t),
      ∀ B O : Set F, IsCompact B → IsOpen O →
        {t | ∃ᶠ n in atTop, t ∈ svPreimage (Sseq n) B} ≤ᵐ[μ] svPreimage S B ∧
          svPreimage S O ≤ᵐ[μ] {t | ∀ᶠ n in atTop, t ∈ svPreimage (Sseq n) O},
      ∀ x : F, ∀ ρ : ℝ, 0 < ρ →
        svPreimage S (ball x ρ) ≤ᵐ[μ] {t | ∀ᶠ n in atTop, t ∈ svPreimage (Sseq n) (ball x ρ)} ∧
          {t | ∀ᶠ n in atTop, t ∈ svPreimage (Sseq n) (ball x ρ)} ⊆
            {t | ∃ᶠ n in atTop, t ∈ svPreimage (Sseq n) (closedBall x ρ)} ∧
          {t | ∃ᶠ n in atTop, t ∈ svPreimage (Sseq n) (closedBall x ρ)} ≤ᵐ[μ]
            svPreimage S (closedBall x ρ),
      ∀ᵐ t ∂μ, ∀ x : F,
        Tendsto (fun n ↦ infEDist x (Sseq n t)) atTop (𝓝 (infEDist x (S t)))] ∧
    ((∀ x : F, ∀ ε ρ : ℝ, 0 < ε → 0 < ρ →
        Tendsto (fun ν ↦ μ (svPreimage (svExcessMap Sseq S ε ν) (closedBall x ρ))) atTop
          (𝓝 0)) →
      ∀ᵐ t ∂μ, PKConverges (fun n ↦ Sseq n t) (S t)) ∧
    (IsFiniteMeasure μ → (∀ᵐ t ∂μ, PKConverges (fun n ↦ Sseq n t) (S t)) →
      ∀ x : F, ∀ ε ρ : ℝ, 0 < ε → 0 < ρ →
        Tendsto (fun ν ↦ μ (svPreimage (svExcessMap Sseq S ε ν) (closedBall x ρ))) atTop
          (𝓝 0)) := by
  refine ⟨?_, ae_pkConverges_of_tendsto_measure_svExcessMap μ hSc,
    fun _ hae x ε ρ hε _ ↦
      tendsto_measure_svExcessMap_of_ae μ hSseq hSseqc hS hSc hae x hε ρ⟩
  tfae_have 1 → 2 := by
    intro hae B O hB hO
    refine ⟨hae.mono fun t ht hfreq ↦ ?_, hae.mono fun t ht hhit ↦ ?_⟩
    · by_contra hmiss
      have hdisj : Disjoint (S t) B := by
        rw [Set.disjoint_iff_inter_eq_empty]
        exact not_nonempty_iff_eq_empty.1 hmiss
      have hev := (outerSetLimit_subset_iff_eventually_misses_compact (hSc t)).1 ht.outer_eq.le
        B hB hdisj
      obtain ⟨n, hn1, hn2⟩ := (Frequently.and_eventually hfreq hev).exists
      obtain ⟨y, hy⟩ := hn1
      exact Set.disjoint_left.1 hn2 hy.1 hy.2
    · exact (subset_innerSetLimit_iff_eventually_hits_open.1 ht.inner_eq.ge) O hO hhit
  tfae_have 2 → 3 := by
    intro hb x ρ _
    obtain ⟨h1, h2⟩ := hb (closedBall x ρ) (ball x ρ) (isCompact_closedBall x ρ) isOpen_ball
    refine ⟨h2, fun t ht ↦ ?_, h1⟩
    exact (Eventually.frequently ht).mono fun n hn ↦
      hn.mono (inter_subset_inter_right _ ball_subset_closedBall)
  tfae_have 3 → 1 := by
    intro hc
    set D := TopologicalSpace.denseSeq F
    have hD := TopologicalSpace.denseRange_denseSeq F
    have hall : ∀ᵐ t ∂μ, ∀ (i : ℕ) (q : ℚ), 0 < q →
        ((S t ∩ ball (D i) q).Nonempty →
          ∀ᶠ n in atTop, (Sseq n t ∩ ball (D i) q).Nonempty) ∧
        ((∃ᶠ n in atTop, (Sseq n t ∩ closedBall (D i) q).Nonempty) →
          (S t ∩ closedBall (D i) q).Nonempty) := by
      refine ae_all_iff.2 fun i ↦ ae_all_iff.2 fun q ↦ ?_
      by_cases hq : 0 < q
      · obtain ⟨h1, _, h3⟩ := hc (D i) q (by exact_mod_cast hq)
        filter_upwards [h1, h3] with t ht1 ht3
        exact fun _ ↦ ⟨ht1, ht3⟩
      · exact Eventually.of_forall fun t hq' ↦ absurd hq' hq
    filter_upwards [hall] with t ht
    refine pkConverges_of_subset_of_subset ?_ ?_
    · refine subset_innerSetLimit_iff_eventually_hits_ball.2 fun x ρ hρ ⟨y, hyS, hyB⟩ ↦ ?_
      have hr : 0 < ρ - dist y x := by rw [mem_ball] at hyB; linarith
      obtain ⟨i, hi⟩ := hD.exists_dist_lt y (by linarith : 0 < (ρ - dist y x) / 4)
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn
        (show (ρ - dist y x) / 4 < (ρ - dist y x) / 2 by linarith)
      have hq0 : (0 : ℝ) < q := by linarith [dist_nonneg (x := y) (y := D i)]
      have hsub : ball (D i) q ⊆ ball x ρ := by
        intro z hz
        rw [mem_ball] at hz ⊢
        calc dist z x ≤ dist z (D i) + dist (D i) y + dist y x := dist_triangle4 _ _ _ _
          _ < ρ := by rw [dist_comm (D i) y]; linarith
      have hev := (ht i q (by exact_mod_cast hq0)).1 ⟨y, hyS, by
        rw [mem_ball]; linarith⟩
      exact hev.mono fun n hn ↦ hn.mono (inter_subset_inter_right _ hsub)
    · intro y hy
      by_contra hyS
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (hSc t).isOpen_compl y hyS
      obtain ⟨i, hi⟩ := hD.exists_dist_lt y (by linarith : 0 < r / 4)
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show r / 4 < r / 2 by linarith)
      have hq0 : (0 : ℝ) < q := by linarith
      have hsub : closedBall (D i) q ⊆ ball y r := by
        intro z hz
        rw [mem_closedBall] at hz
        rw [mem_ball]
        calc dist z y ≤ dist z (D i) + dist (D i) y := dist_triangle _ _ _
          _ < r := by rw [dist_comm (D i) y]; linarith
      have hfreq : ∃ᶠ n in atTop, (Sseq n t ∩ closedBall (D i) q).Nonempty :=
        (hy (ball (D i) q) (isOpen_ball.mem_nhds (by rw [mem_ball]; linarith))).mono
          fun n hn ↦ hn.mono (inter_subset_inter_right _ ball_subset_closedBall)
      obtain ⟨z, hzS, hzB⟩ := (ht i q (by exact_mod_cast hq0)).2 hfreq
      exact hball (hsub hzB) hzS
  tfae_have 1 ↔ 4 := by
    constructor
    · intro hae
      exact hae.mono fun t ht ↦ (pkConverges_iff_tendsto_infEDist (hSc t)).1 ht
    · intro hd
      exact hd.mono fun t ht ↦ (pkConverges_iff_tendsto_infEDist (hSc t)).2 ht
  tfae_finish

/-- The finiteness of `μ` in (a) ⇒ (e) of 14.24 cannot be dropped: on `ℕ` with the counting
measure, `Sν(t) = {1}` for `t ≥ ν`, `{0}` otherwise, converge everywhere to `S ≡ {0}`, but
`μ((R^ν_{1/2})⁻¹(2𝔹)) = ∞` for every `ν`. -/
theorem almost_everywhere_convergence_counterexample :
    (∀ t : ℕ, PKConverges (fun n ↦ if n ≤ t then ({1} : Set ℝ) else {0}) {0}) ∧
      ∀ ν : ℕ, Measure.count (svPreimage (svExcessMap
        (fun n t ↦ if n ≤ t then ({1} : Set ℝ) else {0}) (fun _ ↦ {0}) (1 / 2) ν)
          (closedBall 0 2)) = ∞ := by
  constructor
  · intro t
    have hev : ∀ᶠ n in atTop, (if n ≤ t then ({1} : Set ℝ) else {0}) = {0} :=
      eventually_atTop.2 ⟨t + 1, fun n hn ↦ if_neg (by omega)⟩
    refine pkConverges_of_subset_of_subset (fun x hx V hV ↦ ?_) (fun x hx ↦ ?_)
    · rw [mem_singleton_iff] at hx
      subst hx
      exact hev.mono fun n hn ↦ by rw [hn]; exact ⟨0, rfl, mem_of_mem_nhds hV⟩
    · by_contra hx0
      have hV : ({0} : Set ℝ)ᶜ ∈ 𝓝 x := isOpen_compl_singleton.mem_nhds hx0
      obtain ⟨n, hn1, hn2⟩ := (Frequently.and_eventually (hx _ hV) hev).exists
      have hn1' : ((if n ≤ t then ({1} : Set ℝ) else {0}) ∩ ({0} : Set ℝ)ᶜ).Nonempty := hn1
      rw [hn2] at hn1'
      obtain ⟨y, hy0, hyV⟩ := hn1'
      exact hyV hy0
  · intro ν
    refine measure_mono_top (s₁ := Ici ν) (fun t ht ↦ ?_)
      (Measure.count_apply_infinite (Set.Ici_infinite ν))
    rw [svPreimage_svExcessMap]
    simp only [mem_iUnion, mem_union, mem_setOf_eq, exists_prop]
    refine ⟨t, ht, Or.inl ⟨1, ⟨by simp, ?_⟩, ?_⟩⟩
    · rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs]
      norm_num
    · rw [infEDist_singleton, edist_dist, Real.dist_eq]
      norm_num

/-- The counterexample of `almost_everywhere_convergence_counterexample` in the form of 14.24:
for the counting measure on `ℕ`, (a) holds while (e) fails at `x = 0`, `ε = 1/2`, `ρ = 2`. -/
theorem almost_everywhere_convergence_counterexample_not_tendsto :
    (∀ᵐ t ∂(Measure.count : Measure ℕ),
        PKConverges (fun n ↦ if n ≤ t then ({1} : Set ℝ) else {0}) {0}) ∧
      ¬ Tendsto (fun ν ↦ Measure.count (svPreimage (svExcessMap
        (fun n t ↦ if n ≤ t then ({1} : Set ℝ) else {0}) (fun _ ↦ {0}) (1 / 2) ν)
          (closedBall 0 2))) atTop (𝓝 0) := by
  obtain ⟨hpk, htop⟩ := almost_everywhere_convergence_counterexample
  refine ⟨Eventually.of_forall hpk, fun h ↦ ?_⟩
  obtain ⟨ν, hν⟩ := (h.eventually (Iio_mem_nhds ENNReal.zero_lt_top)).exists
  exact (Set.mem_Iio.1 hν).ne (htop ν)

end Proposition1424

section Proposition1425

/-- **Proposition 14.25 (almost uniform convergence).** For closed-valued measurable mappings
and a finite measure, a.e. pointwise convergence is equivalent to almost uniform convergence:
for every `δ > 0` there is a measurable `Tδ` with `μ(Tδ) < δ` such that `Sν → S` uniformly
(Definition 5.41) on `T \ Tδ`. -/
theorem almost_uniform_convergence (μ : Measure T) [IsFiniteMeasure μ] {S : T → Set F}
    {Sseq : ℕ → T → Set F} (hSc : ∀ t, IsClosed (S t)) (hSseqc : ∀ n t, IsClosed (Sseq n t))
    (hS : SvMeasurable S) (hSseq : ∀ n, SvMeasurable (Sseq n)) :
    (∀ᵐ t ∂μ, PKConverges (fun n ↦ Sseq n t) (S t)) ↔
      ∀ δ : ℝ≥0∞, 0 < δ → ∃ Tδ : Set T, MeasurableSet Tδ ∧ μ Tδ < δ ∧
        SvConvergesUniformlyOn Sseq S Tδᶜ := by
  constructor
  · intro hae δ hδ
    set W : ℕ → ℕ → Set T := fun k ν ↦
      svPreimage (svExcessMap Sseq S (1 / ((k : ℝ) + 1)) ν) (closedBall 0 ((k : ℝ) + 1))
    have hWm : ∀ k ν, MeasurableSet (W k ν) := fun k ν ↦
      measurableSet_svPreimage_svExcessMap hSseq hSseqc hS hSc _ ν isClosed_closedBall
    have hWt : ∀ k, Tendsto (fun ν ↦ μ (W k ν)) atTop (𝓝 0) := fun k ↦
      tendsto_measure_svExcessMap_of_ae μ hSseq hSseqc hS hSc hae 0 (by positivity) _
    obtain ⟨ε', hε'pos, hε'sum⟩ := ENNReal.exists_pos_sum_of_countable hδ.ne' ℕ
    have hm : ∀ k, ∃ m, μ (W k m) < ε' k := fun k ↦
      ((hWt k).eventually (gt_mem_nhds (by exact_mod_cast hε'pos k))).exists
    choose m hm using hm
    refine ⟨⋃ k, W k (m k), MeasurableSet.iUnion fun k ↦ hWm k (m k), ?_, ?_⟩
    · calc μ (⋃ k, W k (m k)) ≤ ∑' k, μ (W k (m k)) := measure_iUnion_le _
        _ ≤ ∑' k, (ε' k : ℝ≥0∞) := ENNReal.tsum_le_tsum fun k ↦ (hm k).le
        _ < δ := hε'sum
    · intro ε hε ρ _
      obtain ⟨k, hk⟩ := exists_nat_gt (max ρ (1 / ε))
      have hk1 : ρ ≤ (k : ℝ) + 1 := by linarith [le_max_left ρ (1 / ε)]
      have hk2 : 1 / ((k : ℝ) + 1) < ε := by
        have h1 : 1 / ε < (k : ℝ) + 1 := by linarith [le_max_right ρ (1 / ε)]
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ hε] at h1
        linarith
      refine eventually_atTop.2 ⟨m k, fun n hn t ht ↦ ?_⟩
      have htW : t ∉ W k (m k) := fun h ↦ ht (mem_iUnion.2 ⟨k, h⟩)
      have h := subset_cthickening_of_not_mem_svPreimage_svExcessMap htW hn
      refine ⟨fun y hy ↦ ?_, fun y hy ↦ ?_⟩
      · exact cthickening_subset_thickening' hε hk2 _
          (h.1 ⟨hy.1, closedBall_subset_closedBall hk1 hy.2⟩)
      · exact cthickening_subset_thickening' hε hk2 _
          (h.2 ⟨hy.1, closedBall_subset_closedBall hk1 hy.2⟩)
  · intro hau
    have hT : ∀ k : ℕ, ∃ Tk : Set T, MeasurableSet Tk ∧ μ Tk < (k : ℝ≥0∞)⁻¹ ∧
        SvConvergesUniformlyOn Sseq S Tkᶜ := fun k ↦
      hau _ (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top k))
    choose Tk _ hTμ hTu using hT
    have hN : μ (⋂ k, Tk k) = 0 := by
      by_contra hne
      obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hne
      exact absurd ((measure_mono (iInter_subset Tk n)).trans_lt (hTμ n)) (not_lt.2 hn.le)
    refine ae_iff.2 (measure_mono_null (fun t ht ↦ ?_) hN)
    simp only [mem_setOf_eq] at ht
    by_contra htN
    simp only [mem_iInter, not_forall] at htN
    obtain ⟨k, hk⟩ := htN
    apply ht
    rw [pkConverges_iff_eventuallyInnerApproximates_and_eventuallyOuterApproximates (hSc t)]
    exact ⟨fun ρ hρ ε hε ↦ (hTu k ε hε ρ hρ).mono fun n hn ↦ (hn t hk).2,
      fun ρ hρ ε hε ↦ (hTu k ε hε ρ hρ).mono fun n hn ↦ (hn t hk).1⟩

end Proposition1425

end RW
