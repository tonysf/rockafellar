/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 14: Graph measurability

Theorem 14.8 of Rockafellar–Wets: Borel inverse images give measurability, a closed-valued
measurable mapping has an `A ⊗ B(F)`-measurable graph, and, when the σ-field is complete for an
s-finite (e.g. σ-finite) measure, graph measurability gives measurable inverse images of all Borel
sets (via the measurable projection theorem 14(2)).

Correction (Adapted): the book asks completeness "for some measure μ", which is vacuous, since
every σ-field is complete for the counting measure (its only null set is `∅`).  Read literally,
both remaining claims fail on the Baire space `ℕ → ℕ` with its Borel field (formal versions in
`CompletenessCounterexamples`): the equivalence for closed-valued `S` fails at (a) ⇒ (c)
(`graph_measurability_closedValued_counterexample`), and "(b) ⇒ (c) ⇒ (a) even if S is not
closed-valued" fails for a mapping whose Borel graph projects onto a non-Borel set
(`graph_measurability_counterexample`).  We assume instead that `A` is complete for an s-finite
(e.g. σ-finite) measure, which suffices.  For closed-valued `S` on a standard Borel space,
(a) ⇔ (b) also holds without any measure (`graph_measurability_standardBorel` in
`StandardBorelMeasurability`), by Novikov's theorem on Borel sets with compact sections
(`NovikovProjection`), while (a) ⇒ (c) still fails there.
-/

import RockafellarWets.Chapter14.MeasurableMappings
import RockafellarWets.Chapter14.AnalyticMeasurability

open Set Filter Topology Metric TopologicalSpace MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace RW

section Theorem148

variable {T F : Type*} [MeasurableSpace T] [MetricSpace F] [ProperSpace F]
  [MeasurableSpace F] [BorelSpace F]

omit [ProperSpace F] in
/-- **Theorem 14.8**, (c) ⇒ (a): measurable inverse images of all Borel sets give measurability
(closedness is not needed). -/
theorem svMeasurable_of_measurableSet_svPreimage_borel {S : T → Set F}
    (h : ∀ D : Set F, MeasurableSet D → MeasurableSet (svPreimage S D)) : SvMeasurable S :=
  fun _ hO ↦ h _ hO.measurableSet

omit [MeasurableSpace T] [ProperSpace F] [MeasurableSpace F] [BorelSpace F] in
/-- The rational-ball representation of the graph of a closed-valued mapping used in the proof
of Theorem 14.8. -/
theorem svGraph_eq_iInter_iUnion {ι : Type*} {D : ι → F} (hD : DenseRange D) {S : T → Set F}
    (hSc : ∀ t, IsClosed (S t)) :
    svGraph S = ⋂ q : ℚ, ⋂ (_ : 0 < q), ⋃ i : ι,
      svPreimage S (closedBall (D i) q) ×ˢ closedBall (D i) q := by
  ext ⟨t, x⟩
  simp only [mem_svGraph, mem_iInter, mem_iUnion, mem_prod]
  constructor
  · intro hx q hq
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    obtain ⟨i, hi⟩ := hD.exists_dist_lt x hq'
    exact ⟨i, ⟨x, hx, hi.le⟩, hi.le⟩
  · intro h
    rw [← (hSc t).closure_eq, Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨q, hq0, hq⟩ := exists_rat_btwn (half_pos hε)
    have hq0' : (0 : ℝ) < q := hq0
    obtain ⟨i, ⟨y, hyS, hyB⟩, hxB⟩ := h q (by exact_mod_cast hq0')
    refine ⟨y, hyS, ?_⟩
    have h1 : dist x (D i) ≤ q := hxB
    have h2 : dist y (D i) ≤ q := hyB
    calc dist x y ≤ dist x (D i) + dist y (D i) := dist_triangle_right _ _ _
      _ ≤ q + q := by linarith
      _ < ε := by linarith

/-- **Theorem 14.8**, (a) ⇒ (b): the graph of a closed-valued measurable mapping is
`A ⊗ B(F)`-measurable. -/
theorem SvMeasurable.measurableSet_svGraph {S : T → Set F} (hS : SvMeasurable S)
    (hSc : ∀ t, IsClosed (S t)) : MeasurableSet (svGraph S) := by
  rcases isEmpty_or_nonempty F with hF | hF
  · have : svGraph S = ∅ := by
      ext ⟨t, x⟩
      exact hF.elim x
    rw [this]
    exact MeasurableSet.empty
  rw [svGraph_eq_iInter_iUnion (denseRange_denseSeq F) hSc]
  refine MeasurableSet.iInter fun q ↦ MeasurableSet.iInter fun hq ↦
    MeasurableSet.iUnion fun i ↦ ?_
  exact (hS.measurableSet_svPreimage_of_isCompact hSc (isCompact_closedBall _ _)).prod
    measurableSet_closedBall

omit [ProperSpace F] in
/-- **Theorem 14.8**, (b) ⇒ (c) under completeness: if the σ-field `A` is complete for an
s-finite measure, then the inverse image of every Borel set under a mapping with
`A ⊗ B(F)`-measurable graph is measurable. Closed-valuedness is not needed. -/
theorem measurableSet_svPreimage_of_measurableSet_svGraph [PolishSpace F] (μ : Measure T)
    [SFinite μ] [μ.IsComplete] {S : T → Set F} (hS : MeasurableSet (svGraph S)) {D : Set F}
    (hD : MeasurableSet D) : MeasurableSet (svPreimage S D) := by
  have : svPreimage S D = Prod.fst '' (svGraph S ∩ (univ ×ˢ D)) := by
    ext t
    simp only [svPreimage, mem_setOf_eq, mem_image, mem_inter_iff, mem_svGraph, mem_prod,
      mem_univ, true_and, Prod.exists, exists_and_right, exists_eq_right]
    rfl
  rw [this]
  exact measurableSet_image_fst_of_isComplete μ (hS.inter (MeasurableSet.univ.prod hD))

omit [ProperSpace F] in
/-- **Theorem 14.8**, (b) ⇒ (a) under completeness for an s-finite measure, without
closed-valuedness. -/
theorem svMeasurable_of_measurableSet_svGraph [PolishSpace F] (μ : Measure T) [SFinite μ]
    [μ.IsComplete] {S : T → Set F} (hS : MeasurableSet (svGraph S)) : SvMeasurable S :=
  svMeasurable_of_measurableSet_svPreimage_borel fun _ hD ↦
    measurableSet_svPreimage_of_measurableSet_svGraph μ hS hD

/-- **Theorem 14.8 (graph measurability)**, adapted. For closed-valued `S`, (c) ⇒ (a) ⇒ (b); when
the σ-field is complete for an s-finite (e.g. σ-finite) measure, (a), (b), (c) are equivalent. -/
theorem graph_measurability {S : T → Set F} (hSc : ∀ t, IsClosed (S t)) :
    ((∀ D : Set F, MeasurableSet D → MeasurableSet (svPreimage S D)) → SvMeasurable S) ∧
    (SvMeasurable S → MeasurableSet (svGraph S)) ∧
    ∀ (μ : Measure T) [SFinite μ] [μ.IsComplete],
      List.TFAE [SvMeasurable S, MeasurableSet (svGraph S),
        ∀ D : Set F, MeasurableSet D → MeasurableSet (svPreimage S D)] := by
  refine ⟨svMeasurable_of_measurableSet_svPreimage_borel, fun h ↦ h.measurableSet_svGraph hSc,
    fun μ _ _ ↦ ?_⟩
  tfae_have 1 → 2 := fun h ↦ h.measurableSet_svGraph hSc
  tfae_have 2 → 3 := fun h _ hD ↦ measurableSet_svPreimage_of_measurableSet_svGraph μ h hD
  tfae_have 3 → 1 := svMeasurable_of_measurableSet_svPreimage_borel
  tfae_finish

end Theorem148

end RW
