/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 14: Counterexamples to "complete for some measure"

Theorem 14.8, Exercise 14.35 and Proposition 14.53(b) of Rockafellar–Wets assume that `(T, A)` is
"complete for some measure μ".  This is vacuous: every σ-field is complete for the counting
measure, whose only null set is `∅` (`count_isComplete`).  The adapted statements assume
completeness for an s-finite measure instead.  Here the literal statements are refuted on the
Baire space `ℕ → ℕ` with its Borel σ-field, by the non-Borel Suslin diagonal of
`RW.SuslinDiagonal`, which is the projection of the Borel set of pairs `(t, b)` with `b` a branch
of the tree coded by `t` in the witness space (`SuslinDiagonal.measurableSet_svGraph_branches`):

* 14.8, last sentence: a mapping into `ℝ` with Borel graph need not be measurable
  (`graph_measurability_counterexample`; also `graph_measurability_counterexample_of_horizon`,
  from the counterexample to 14.56);
* 14.8, closed-valued equivalence: a closed-valued measurable `S` into `ℝ²`, whose graph is
  therefore measurable, can have a non-measurable `S⁻¹(D)` for a Borel `D`, so (a) ⇒ (c) fails
  (`graph_measurability_closedValued_counterexample`);
* 14.35: `cl f₀(t, ·)` is not normal for the indicator `f₀` of that Borel graph
  (`closure_integrand_counterexample`);
* 14.53(b), lim inf clause: indicators of compact sets depending measurably on `t` whose
  `cl [p-lim inf]` has the Suslin diagonal as its domain set (`liminf_integrand_counterexample`).
-/

import RockafellarWets.Chapter14.HorizonGraphCounterexample
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal

open Set Filter Topology MeasureTheory

noncomputable section

namespace RW

/-- Every σ-field is complete for the counting measure, whose only null set is `∅`; so the
hypothesis "complete for some measure" of 14.8, 14.34, 14.35 and 14.53(b) is vacuous. -/
theorem count_isComplete {T : Type*} [MeasurableSpace T] :
    (Measure.count : Measure T).IsComplete := by
  refine ⟨fun s hs ↦ ?_⟩
  have : s = ∅ := Measure.count_eq_zero_iff.1 hs
  subst this
  exact MeasurableSet.empty

/-! ### A Borel set with the Suslin diagonal as projection -/

namespace SuslinDiagonal

theorem measurableSet_witnessSet : MeasurableSet witnessSet := by
  have : witnessSet = ⋂ i, ⋃ n, (fun b : ℕ → Bool ↦ b (Nat.pair i n)) ⁻¹' {true} := by
    ext b
    simp [witnessSet]
  rw [this]
  exact MeasurableSet.iInter fun i ↦ MeasurableSet.iUnion fun n ↦
    (measurable_pi_apply (Nat.pair i n)) (measurableSet_singleton true)

/-- The branches in the witness space of the tree coded by `t`. -/
def branches (t : ℕ → ℕ) : Set (ℕ → Bool) :=
  {b | b ∈ witnessSet ∧ ∀ n, t (code (pre t n, pre b n)) = 0}

theorem svDom_branches : svDom branches = SuslinDiagonal.diagonal := by
  ext t
  simp only [mem_svDom, Set.Nonempty, branches, mem_setOf_eq, SuslinDiagonal.diagonal]

/-- The graph of `t ↦ branches t` is Borel. -/
theorem measurableSet_svGraph_branches : MeasurableSet (svGraph branches) := by
  have : svGraph branches = (Prod.snd ⁻¹' witnessSet) ∩
      ⋂ n, {p : (ℕ → ℕ) × (ℕ → Bool) | p.1 (code (pre p.1 n, pre p.2 n)) = 0} := by
    ext ⟨t, b⟩
    simp only [mem_svGraph, branches, mem_setOf_eq, mem_inter_iff, mem_preimage, mem_iInter]
  rw [this]
  refine (measurable_snd measurableSet_witnessSet).inter (MeasurableSet.iInter fun n ↦ ?_)
  have h : {p : (ℕ → ℕ) × (ℕ → Bool) | p.1 (code (pre p.1 n, pre p.2 n)) = 0} =
      ⋃ u : Fin n → Bool, ((⋂ i : Fin n, (fun p : (ℕ → ℕ) × (ℕ → Bool) ↦ p.2 i) ⁻¹' {u i}) ∩
        Prod.fst ⁻¹' {t : ℕ → ℕ | t (code (pre t n, List.ofFn u)) = 0}) := by
    ext ⟨t, b⟩
    simp only [mem_setOf_eq, mem_iUnion, mem_inter_iff, mem_preimage, mem_iInter,
      mem_singleton_iff]
    constructor
    · intro h
      exact ⟨fun i ↦ b i, fun i ↦ rfl, h⟩
    · rintro ⟨u, hu, h⟩
      have hpre : pre b n = List.ofFn u := by
        unfold pre
        congr 1
        funext i
        exact hu i
      rw [hpre]
      exact h
  rw [h]
  refine MeasurableSet.iUnion fun u ↦ MeasurableSet.inter ?_
    (measurable_fst (measurableSet_code_eq_zero n _))
  exact MeasurableSet.iInter fun i ↦
    ((measurable_pi_apply (i : ℕ)).comp measurable_snd) (measurableSet_singleton (u i))

end SuslinDiagonal

namespace CantorGaps

open SuslinDiagonal

/-- The branches of `branches t`, as points of the Cantor set in `ℝ`. -/
def branchPoints (t : ℕ → ℕ) : Set ℝ := point '' branches t

theorem svDom_branchPoints : svDom branchPoints = SuslinDiagonal.diagonal := by
  rw [← svDom_branches]
  ext t
  simp only [mem_svDom, branchPoints, image_nonempty]

/-- The graph of `t ↦ branchPoints t` is Borel in `(ℕ → ℕ) × ℝ`. -/
theorem measurableSet_svGraph_branchPoints : MeasurableSet (svGraph branchPoints) := by
  have hpt : IsClosedEmbedding point := continuous_point.isClosedEmbedding point_injective
  have hemb : IsEmbedding (Prod.map (id : (ℕ → ℕ) → (ℕ → ℕ)) point) :=
    IsEmbedding.id.prodMap hpt.isEmbedding
  have hrange : MeasurableSet (range (Prod.map (id : (ℕ → ℕ) → (ℕ → ℕ)) point)) := by
    rw [Set.range_prodMap, range_id]
    exact MeasurableSet.univ.prod hpt.isClosed_range.measurableSet
  have : svGraph branchPoints =
      Prod.map (id : (ℕ → ℕ) → (ℕ → ℕ)) point '' svGraph branches := by
    ext ⟨t, y⟩
    simp only [mem_svGraph, branchPoints, mem_image, Prod.exists, Prod.map_apply, id_eq,
      Prod.mk.injEq]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨t, b, hb, rfl, rfl⟩
    · rintro ⟨t', b, hb, rfl, rfl⟩
      exact ⟨b, hb, rfl⟩
  rw [this]
  exact (hemb.measurableEmbedding hrange).measurableSet_image' measurableSet_svGraph_branches

end CantorGaps

open SuslinDiagonal CantorGaps

/-! ### Theorem 14.8 and Exercise 14.35 -/

/-- **Theorem 14.8**, last sentence, fails as printed: the Borel field of the Baire space is
complete for the counting measure, yet a mapping into `ℝ` with `A ⊗ B(ℝ)`-measurable graph need
not be measurable, since its domain can be the Suslin diagonal. -/
theorem graph_measurability_counterexample :
    (Measure.count : Measure (ℕ → ℕ)).IsComplete ∧
      ∃ S : (ℕ → ℕ) → Set ℝ, MeasurableSet (svGraph S) ∧ ¬ SvMeasurable S := by
  refine ⟨count_isComplete, branchPoints, measurableSet_svGraph_branchPoints, fun h ↦ ?_⟩
  have := h.measurableSet_svDom
  rw [svDom_branchPoints] at this
  exact not_measurableSet_diagonal this

/-- **Theorem 14.8**, the closed-valued equivalence fails as printed: on the Baire space with its
Borel field (complete for the counting measure), `S(t) = {e(t)} × ℝ` for a measurable embedding
`e : (ℕ → ℕ) → ℝ` is closed-valued and measurable, so (a) and (b) hold, while `S⁻¹(D)` is the
Suslin diagonal for a Borel set `D ⊆ ℝ²`, so (c) fails. -/
theorem graph_measurability_closedValued_counterexample :
    (Measure.count : Measure (ℕ → ℕ)).IsComplete ∧
      ∃ S : (ℕ → ℕ) → Set (ℝ × ℝ), (∀ t, IsClosed (S t)) ∧ SvMeasurable S ∧
        MeasurableSet (svGraph S) ∧ ∃ D : Set (ℝ × ℝ), MeasurableSet D ∧
          ¬ MeasurableSet (svPreimage S D) := by
  refine ⟨count_isComplete, ?_⟩
  obtain ⟨e, he⟩ := MeasureTheory.exists_measurableEmbedding_real (ℕ → ℕ)
  set S : (ℕ → ℕ) → Set (ℝ × ℝ) := fun t ↦ {e t} ×ˢ univ with hS
  have hSc : ∀ t, IsClosed (S t) := fun t ↦ isClosed_singleton.prod isClosed_univ
  have hSm : SvMeasurable S := by
    intro O hO
    have : svPreimage S O = e ⁻¹' (Prod.fst '' O) := by
      ext t
      simp only [mem_svPreimage, hS, mem_preimage, mem_image, Prod.exists, exists_and_right,
        exists_eq_right]
      constructor
      · rintro ⟨⟨a, y⟩, ⟨ha, -⟩, hO'⟩
        rw [mem_singleton_iff] at ha
        subst ha
        exact ⟨y, hO'⟩
      · rintro ⟨y, hy⟩
        exact ⟨(e t, y), ⟨rfl, mem_univ _⟩, hy⟩
    rw [this]
    exact he.measurable (isOpenMap_fst O hO).measurableSet
  refine ⟨S, hSc, hSm, hSm.measurableSet_svGraph hSc,
    Prod.map e id '' svGraph branchPoints, ?_, fun h ↦ ?_⟩
  · refine measurableSet_svGraph_branchPoints.image_of_measurable_injOn
      (he.measurable.prodMap measurable_id) ?_
    rintro ⟨t, y⟩ - ⟨t', y'⟩ - h
    simp only [Prod.map_apply, id_eq, Prod.mk.injEq] at h
    rw [he.injective h.1, h.2]
  · have : svPreimage S (Prod.map e id '' svGraph branchPoints) = SuslinDiagonal.diagonal := by
      rw [← svDom_branchPoints]
      ext t
      simp only [mem_svPreimage, hS, mem_svDom]
      constructor
      · rintro ⟨⟨a, y⟩, ⟨ha, -⟩, ⟨⟨t', y'⟩, hg, heq⟩⟩
        rw [mem_singleton_iff] at ha
        simp only [Prod.map_apply, id_eq, Prod.mk.injEq] at heq
        have ht : t' = t := he.injective (heq.1.trans ha)
        subst ht
        exact ⟨y', hg⟩
      · rintro ⟨y, hy⟩
        exact ⟨(e t, y), ⟨rfl, mem_univ _⟩, ⟨(t, y), hy, rfl⟩⟩
    rw [this] at h
    exact not_measurableSet_diagonal h

/-- **Theorem 14.8**, last sentence, refuted a second time by the counterexample to 14.56: the
graph of `t ↦ gph ∂^∞f(t, ·)` is `A ⊗ B`-measurable for every normal integrand
(`measurableSet_svGraph_svGraph_horizonSubdifferential`), but the mapping of
`RW.HorizonGraph.horizon_graph_counterexample` is not measurable. -/
theorem graph_measurability_counterexample_of_horizon :
    (Measure.count : Measure (ℕ → ℕ)).IsComplete ∧
      ∃ S : (ℕ → ℕ) → Set (HorizonGraph.E2 × HorizonGraph.E2),
        MeasurableSet (svGraph S) ∧ ¬ SvMeasurable S := by
  obtain ⟨f, hf, -, -, hnot⟩ := HorizonGraph.horizon_graph_counterexample
  exact ⟨count_isComplete, _, measurableSet_svGraph_svGraph_horizonSubdifferential hf, hnot⟩

/-- **Exercise 14.35** fails as printed: on the Baire space with its Borel field (complete for the
counting measure), the indicator `f₀` of the Borel graph of `branchPoints` is
`A ⊗ B(ℝ)`-measurable, but `cl f₀(t, ·)` is not a normal integrand, since its domain set is the
Suslin diagonal. -/
theorem closure_integrand_counterexample :
    (Measure.count : Measure (ℕ → ℕ)).IsComplete ∧
      ∃ f₀ : (ℕ → ℕ) → ℝ → EReal, Measurable (Function.uncurry f₀) ∧
        ¬ IsNormalIntegrand (fun t ↦ epiClosure (f₀ t)) := by
  classical
  refine ⟨count_isComplete, fun t ↦ indicatorVA (branchPoints t), ?_, fun h ↦ ?_⟩
  · have : Function.uncurry (fun t ↦ indicatorVA (branchPoints t)) =
        fun p : (ℕ → ℕ) × ℝ ↦ if p ∈ svGraph branchPoints then (0 : EReal) else ⊤ := by
      funext ⟨t, y⟩
      simp only [Function.uncurry, indicatorVA, mem_svGraph]
    rw [this]
    exact Measurable.ite measurableSet_svGraph_branchPoints measurable_const measurable_const
  · have hm := h.2.measurableSet_svDom
    have : svDom (epiMapping fun t ↦ epiClosure (indicatorVA (branchPoints t))) =
        SuslinDiagonal.diagonal := by
      rw [← svDom_branchPoints]
      ext t
      simp only [mem_svDom, epiMapping, epigraph_epiClosure, closure_nonempty_iff,
        epigraph_indicatorVA, prod_nonempty_iff, nonempty_Ici, and_true]
    rw [this] at hm
    exact not_measurableSet_diagonal hm

/-! ### Proposition 14.53(b), lim inf clause -/

namespace LiminfCounterexample

/-- Columns `0, …, i` of `b` all have a `true` strictly before position `m`. -/
def HitsColumns (i m : ℕ) (b : ℕ → Bool) : Prop :=
  ∀ j ≤ i, ∃ n, Nat.pair j n < m ∧ b (Nat.pair j n) = true

/-- `m` is the least position bound with `HitsColumns i m b`. -/
def IsLeastHitBound (i m : ℕ) (b : ℕ → Bool) : Prop :=
  HitsColumns i m b ∧ ∀ m' < m, ¬ HitsColumns i m' b

theorem hitsColumns_congr {i m : ℕ} {b b' : ℕ → Bool} (h : ∀ k < m, b' k = b k)
    (hw : HitsColumns i m b') : HitsColumns i m b := fun j hj ↦ by
  obtain ⟨n, hn, hb⟩ := hw j hj
  exact ⟨n, hn, by rw [← h _ hn]; exact hb⟩

theorem isLeastHitBound_congr {i m : ℕ} {b b' : ℕ → Bool} (h : ∀ k < m, b' k = b k)
    (hq : IsLeastHitBound i m b') : IsLeastHitBound i m b :=
  ⟨hitsColumns_congr h hq.1, fun m' hm' hw ↦ hq.2 m' hm'
    (hitsColumns_congr (fun k hk ↦ (h k (hk.trans hm')).symm) hw)⟩

theorem isLeastHitBound_unique {i m m' : ℕ} {b : ℕ → Bool} (h : IsLeastHitBound i m b)
    (h' : IsLeastHitBound i m' b) : m = m' := by
  rcases lt_trichotomy m m' with hlt | heq | hgt
  · exact absurd h.1 (h'.2 m hlt)
  · exact heq
  · exact absurd h'.1 (h.2 m' hgt)

theorem lt_of_hitsColumns {i m : ℕ} {b : ℕ → Bool} (h : HitsColumns i m b) : i < m := by
  obtain ⟨n, hn, -⟩ := h i le_rfl
  exact lt_of_le_of_lt (Nat.left_le_pair i n) hn

theorem exists_isLeastHitBound {b : ℕ → Bool} (hb : b ∈ witnessSet) (i : ℕ) :
    ∃ m, IsLeastHitBound i m b := by
  classical
  have hex : ∃ m, HitsColumns i m b := by
    choose n hn using hb
    refine ⟨(Finset.range (i + 1)).sup (fun j ↦ Nat.pair j (n j)) + 1,
      fun j hj ↦ ⟨n j, ?_, hn j⟩⟩
    exact Nat.lt_succ_of_le (Finset.le_sup (f := fun j ↦ Nat.pair j (n j))
      (Finset.mem_range.2 (Nat.lt_succ_of_le hj)))
  exact ⟨Nat.find hex, Nat.find_spec hex, fun m' hm' ↦ Nat.find_min hex hm'⟩

/-- The compact pieces of the Cantor space: sequences whose prefix of length `m` lies in the tree
coded by `t`, with `m` the least position bound for the columns `0, …, i`. -/
def piece (i m : ℕ) (t : ℕ → ℕ) : Set (ℕ → Bool) :=
  {b | pre b m ∈ onSet t ∧ IsLeastHitBound i m b}

theorem piece_congr {i m : ℕ} {t : ℕ → ℕ} {b b' : ℕ → Bool} (h : ∀ k < m, b' k = b k)
    (hb' : b' ∈ piece i m t) : b ∈ piece i m t := by
  refine ⟨?_, isLeastHitBound_congr h hb'.2⟩
  have : pre b m = pre b' m := pre_eq_pre_iff.2 fun k hk ↦ (h k hk).symm
  rw [this]
  exact hb'.1

theorem isClosed_piece (i m : ℕ) (t : ℕ → ℕ) : IsClosed (piece i m t) := by
  set r : (ℕ → Bool) → (Fin m → Bool) := fun b k ↦ b k with hr
  have hrc : Continuous r := continuous_pi fun k ↦ continuous_apply (k : ℕ)
  have : piece i m t = r ⁻¹' (r '' piece i m t) := by
    refine Subset.antisymm (subset_preimage_image r _) ?_
    rintro b ⟨b', hb', hbb'⟩
    refine piece_congr (fun k hk ↦ ?_) hb'
    exact congrFun hbb' ⟨k, hk⟩
  rw [this]
  exact (isClosed_discrete _).preimage hrc

/-- The pieces as compact subsets of the Cantor set in `ℝ`. -/
def realPiece (i m : ℕ) (t : ℕ → ℕ) : Set ℝ := point '' piece i m t

theorem isClosed_realPiece (i m : ℕ) (t : ℕ → ℕ) : IsClosed (realPiece i m t) :=
  ((isClosed_piece i m t).isCompact.image continuous_point).isClosed

theorem svMeasurable_realPiece (i m : ℕ) : SvMeasurable (fun t ↦ realPiece i m t) := by
  classical
  have heq : (fun t ↦ realPiece i m t) = fun t ↦ ⋃ σ : List Bool,
      (if t ∈ {t : ℕ → ℕ | σ ∈ onSet t} then point '' {b | pre b m = σ ∧ IsLeastHitBound i m b}
        else (∅ : Set ℝ)) := by
    funext t
    ext y
    simp only [realPiece, piece, mem_image, mem_setOf_eq, mem_iUnion]
    constructor
    · rintro ⟨b, ⟨hb1, hb2⟩, rfl⟩
      exact ⟨pre b m, by rw [if_pos hb1]; exact ⟨b, ⟨rfl, hb2⟩, rfl⟩⟩
    · rintro ⟨σ, hσ⟩
      by_cases h : σ ∈ onSet t
      · rw [if_pos h] at hσ
        obtain ⟨b, ⟨rfl, hb2⟩, rfl⟩ := hσ
        exact ⟨b, ⟨h, hb2⟩, rfl⟩
      · rw [if_neg h] at hσ
        exact absurd hσ (notMem_empty _)
  rw [heq]
  exact SvMeasurable.iUnion fun σ ↦ SvMeasurable.ite (measurableSet_mem_onSet σ)
    (svMeasurable_const _) (svMeasurable_const _)

/-- The sequence of normal integrands `δ_{C^n}`, `C^{⟨i, m⟩}(t) = realPiece i m t`. -/
def pieceIndicator (n : ℕ) (t : ℕ → ℕ) : ℝ → EReal :=
  indicatorVA (realPiece (Nat.unpair n).1 (Nat.unpair n).2 t)

theorem isNormalIntegrand_pieceIndicator (n : ℕ) : IsNormalIntegrand (pieceIndicator n) :=
  isNormalIntegrand_indicatorVA_iff.2 ⟨fun t ↦ isClosed_realPiece _ _ t, svMeasurable_realPiece _ _⟩

/-- Some point lies in infinitely many `C^n(t)` exactly when `t` is in the Suslin diagonal: for
fixed `i` at most one `m` qualifies, and `point` is injective. -/
theorem exists_frequently_mem_iff (t : ℕ → ℕ) :
    (∃ x : ℝ, ∃ᶠ n in atTop, x ∈ realPiece (Nat.unpair n).1 (Nat.unpair n).2 t) ↔
      t ∈ SuslinDiagonal.diagonal := by
  rw [diagonal_eq]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨n₀, hn₀⟩ := hx.exists
    obtain ⟨b, -, rfl⟩ := hn₀
    have hall : ∀ n, point b ∈ realPiece (Nat.unpair n).1 (Nat.unpair n).2 t →
        b ∈ piece (Nat.unpair n).1 (Nat.unpair n).2 t := by
      rintro n ⟨b', hb', hpt⟩
      rwa [point_injective hpt] at hb'
    have hinf : {n | point b ∈ realPiece (Nat.unpair n).1 (Nat.unpair n).2 t}.Infinite :=
      Nat.frequently_atTop_iff_infinite.1 hx
    have hunb : ∀ i, ∃ n, point b ∈ realPiece (Nat.unpair n).1 (Nat.unpair n).2 t ∧
        i ≤ (Nat.unpair n).1 := by
      intro i
      by_contra hcon
      push_neg at hcon
      have hinj : Set.InjOn (fun n ↦ (Nat.unpair n).1)
          {n | point b ∈ realPiece (Nat.unpair n).1 (Nat.unpair n).2 t} := by
        intro n hn n' hn' heq
        have h1 := (hall n hn).2
        have h2 := (hall n' hn').2
        simp only at heq
        rw [heq] at h1
        have hm : (Nat.unpair n).2 = (Nat.unpair n').2 := isLeastHitBound_unique h1 h2
        rw [← Nat.pair_unpair n, ← Nat.pair_unpair n', heq, hm]
      refine hinf (Set.Finite.of_finite_image ?_ hinj)
      refine (Finset.range i).finite_toSet.subset ?_
      rintro _ ⟨n, hn, rfl⟩
      simpa using hcon n hn
    refine ⟨b, fun i ↦ ?_, fun m ↦ ?_⟩
    · obtain ⟨n, hn, hi⟩ := hunb i
      obtain ⟨n', -, hb⟩ := (hall n hn).2.1 i hi
      exact ⟨n', hb⟩
    · obtain ⟨n, hn, hi⟩ := hunb m
      have hK := hall n hn
      have hlt : m < (Nat.unpair n).2 := lt_of_le_of_lt hi (lt_of_hitsColumns hK.2.1)
      have := take_mem_onSet hK.1 m
      rwa [take_pre b hlt.le] at this
  · rintro ⟨b, hbW, hpre⟩
    refine ⟨point b, Nat.frequently_atTop_iff_infinite.2 ?_⟩
    choose m hm using exists_isLeastHitBound hbW
    refine Set.infinite_of_injective_forall_mem (f := fun i ↦ Nat.pair i (m i)) ?_ ?_
    · intro i i' h
      have := congrArg (fun n ↦ (Nat.unpair n).1) h
      simpa using this
    · intro i
      simp only [mem_setOf_eq, Nat.unpair_pair]
      exact ⟨b, ⟨hpre (m i), hm i⟩, rfl⟩

end LiminfCounterexample

open LiminfCounterexample in
/-- **Proposition 14.53(b)**, lim inf clause, fails as printed: on the Baire space with its Borel
field (complete for the counting measure), the indicators `fν` of the compact sets
`C^ν(t) = realPiece i m t`, `ν = ⟨i, m⟩`, are normal integrands, but `cl [p-lim inf fν(t, ·)]` is
not, since its domain set is the Suslin diagonal (`exists_frequently_mem_iff`). -/
theorem liminf_integrand_counterexample :
    (Measure.count : Measure (ℕ → ℕ)).IsComplete ∧
      ∃ f : ℕ → (ℕ → ℕ) → ℝ → EReal, (∀ n, IsNormalIntegrand (f n)) ∧
        ¬ IsNormalIntegrand
          (fun t ↦ epiClosure (fun x ↦ Filter.liminf (fun n ↦ f n t x) atTop)) := by
  refine ⟨count_isComplete, pieceIndicator, isNormalIntegrand_pieceIndicator, fun h ↦ ?_⟩
  have hm := h.2.measurableSet_svDom
  have : svDom (epiMapping fun t ↦
      epiClosure (fun x ↦ Filter.liminf (fun n ↦ pieceIndicator n t x) atTop)) =
      SuslinDiagonal.diagonal := by
    ext t
    rw [← exists_frequently_mem_iff t]
    simp only [mem_svDom, epiMapping, epigraph_epiClosure, closure_nonempty_iff]
    constructor
    · rintro ⟨⟨x, α⟩, hxα⟩
      have hle : Filter.liminf (fun n ↦ pieceIndicator n t x) atTop ≤ α := hxα
      refine ⟨x, ?_⟩
      by_contra hnf
      rw [Filter.not_frequently] at hnf
      have htop : Filter.liminf (fun n ↦ pieceIndicator n t x) atTop = ⊤ := by
        have : (fun n ↦ pieceIndicator n t x) =ᶠ[atTop] fun _ ↦ (⊤ : EReal) := by
          filter_upwards [hnf] with n hn
          simp [pieceIndicator, indicatorVA, hn]
        rw [Filter.liminf_congr this, Filter.liminf_const]
      rw [htop] at hle
      exact absurd hle (by simp)
    · rintro ⟨x, hx⟩
      refine ⟨(x, 0), ?_⟩
      change Filter.liminf (fun n ↦ pieceIndicator n t x) atTop ≤ ((0 : ℝ) : EReal)
      refine Filter.liminf_le_of_frequently_le (hx.mono fun n hn ↦ ?_)
      simp [pieceIndicator, indicatorVA, hn]
  rw [this] at hm
  exact not_measurableSet_diagonal hm

end RW
