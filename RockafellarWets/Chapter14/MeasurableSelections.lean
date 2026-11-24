/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 14: Measurable selections and Castaing representations

Theorem 14.5, Corollary 14.6 and Example 14.7 of Rockafellar–Wets.

The selection theorem is proved by the successive approximation scheme of Kuratowski and
Ryll-Nardzewski, which works for closed-valued measurable mappings into any complete separable
metric space; the Castaing representation is then assembled from selections of the truncated
mappings `S(t) ∩ IB(a, ρ)` over rational balls (the book instead iterates nearest-point maps,
which needs the Euclidean structure).

The book's functions `xν : dom S → ℝⁿ` are measurable functions on the measurable set `dom S`;
here they are measurable functions on all of `T` (a measurable function on `dom S` extends by a
constant, and the restriction of a measurable function is measurable), and only their values on
`dom S` matter.
-/

import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import RockafellarWets.Chapter14.MeasurableMappings

open Set Filter Topology Metric
open scoped ENNReal NNReal Classical

noncomputable section

namespace RW

section Basic

variable {T F : Type*} [MeasurableSpace T] [TopologicalSpace F]

/-- Mappings defined piecewise on a measurable set from measurable pieces are measurable. -/
theorem SvMeasurable.ite {S₁ S₂ : T → Set F} {A : Set T} (hA : MeasurableSet A)
    (h₁ : SvMeasurable S₁) (h₂ : SvMeasurable S₂) :
    SvMeasurable (fun t ↦ if t ∈ A then S₁ t else S₂ t) := by
  intro O hO
  have : svPreimage (fun t ↦ if t ∈ A then S₁ t else S₂ t) O =
      (A ∩ svPreimage S₁ O) ∪ (Aᶜ ∩ svPreimage S₂ O) := by
    ext t
    by_cases ht : t ∈ A <;> simp [svPreimage, ht]
  rw [this]
  exact (hA.inter (h₁ O hO)).union (hA.compl.inter (h₂ O hO))

end Basic

section Intersections

variable {T F : Type*} [MeasurableSpace T] [MetricSpace F] [ProperSpace F]

/-- Intersecting a closed-valued measurable mapping with a fixed closed set preserves
measurability. -/
theorem SvMeasurable.inter_isClosed {S : T → Set F} (hS : SvMeasurable S)
    (hSc : ∀ t, IsClosed (S t)) {C : Set F} (hC : IsClosed C) :
    SvMeasurable (fun t ↦ S t ∩ C) := by
  refine svMeasurable_of_measurableSet_svPreimage_isCompact fun K hK ↦ ?_
  have : svPreimage (fun t ↦ S t ∩ C) K = svPreimage S (C ∩ K) := by
    ext t
    simp only [mem_svPreimage, inter_assoc]
  rw [this]
  exact hS.measurableSet_svPreimage_of_isCompact hSc (hK.inter_left hC)

end Intersections

section FindIndex

variable {T : Type*} [MeasurableSpace T]

/-- The least index satisfying `P`, or `0` when there is none. -/
def natFindOrZero (P : ℕ → Prop) : ℕ :=
  if h : ∃ i, P i then Nat.find h else 0

theorem natFindOrZero_spec {P : ℕ → Prop} (h : ∃ i, P i) : P (natFindOrZero P) := by
  rw [natFindOrZero, dif_pos h]
  exact Nat.find_spec h

theorem natFindOrZero_eq_iff {P : ℕ → Prop} {n : ℕ} :
    natFindOrZero P = n ↔ (P n ∧ ∀ m < n, ¬ P m) ∨ ((∀ i, ¬ P i) ∧ n = 0) := by
  unfold natFindOrZero
  by_cases h : ∃ i, P i
  · rw [dif_pos h, Nat.find_eq_iff]
    constructor
    · intro h'
      exact Or.inl h'
    · rintro (h' | ⟨h', -⟩)
      · exact h'
      · obtain ⟨i, hi⟩ := h
        exact absurd hi (h' i)
  · rw [dif_neg h]
    push_neg at h
    constructor
    · rintro rfl
      exact Or.inr ⟨h, rfl⟩
    · rintro (⟨h', -⟩ | ⟨-, rfl⟩)
      · exact absurd h' (h n)
      · rfl

theorem measurable_natFindOrZero {P : ℕ → T → Prop} (hP : ∀ i, MeasurableSet {t | P i t}) :
    Measurable fun t ↦ natFindOrZero (P · t) := by
  refine measurable_to_countable' fun n ↦ ?_
  have : (fun t ↦ natFindOrZero (P · t)) ⁻¹' {n} =
      ({t | P n t} ∩ ⋂ m ∈ Finset.range n, {t | P m t}ᶜ) ∪
        ((⋂ i, {t | P i t}ᶜ) ∩ {_t | n = 0}) := by
    ext t
    simp only [mem_preimage, mem_singleton_iff, natFindOrZero_eq_iff, mem_union, mem_inter_iff,
      mem_setOf_eq, mem_iInter, Finset.mem_range, mem_compl_iff]
  rw [this]
  refine ((hP n).inter ?_).union ((MeasurableSet.iInter fun i ↦ (hP i).compl).inter
    (MeasurableSet.const _))
  exact Finset.measurableSet_biInter _ fun m _ ↦ (hP m).compl

end FindIndex

section SelectionScheme

variable {T F : Type*} [MetricSpace F]

/-- The radii `(1/2)^k` of the successive approximation scheme. -/
def selRadius (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ k

theorem selRadius_pos (k : ℕ) : 0 < selRadius k := by
  unfold selRadius
  positivity

theorem selRadius_succ (k : ℕ) : selRadius (k + 1) = selRadius k / 2 := by
  unfold selRadius
  rw [pow_succ]
  ring

/-- The index sequence of the Kuratowski–Ryll-Nardzewski scheme: at stage `k + 1` take the
least `i` with `S(t)` meeting `IB°(d i, (1/2)^(k+1))` and `d i` within `2 (1/2)^k` of the
previous approximation. -/
def selIndex (S : T → Set F) (d : ℕ → F) : ℕ → T → ℕ
  | 0 => fun t ↦ natFindOrZero fun i ↦ (S t ∩ ball (d i) (selRadius 0)).Nonempty
  | k + 1 => fun t ↦ natFindOrZero fun i ↦
      (S t ∩ ball (d i) (selRadius (k + 1))).Nonempty ∧
        dist (d i) (d (selIndex S d k t)) < 2 * selRadius k

theorem measurable_selIndex [MeasurableSpace T] {S : T → Set F} (hS : SvMeasurable S)
    (d : ℕ → F) (k : ℕ) :
    Measurable (selIndex S d k) := by
  induction k with
  | zero =>
    exact measurable_natFindOrZero fun i ↦ hS _ isOpen_ball
  | succ k ih =>
    refine measurable_natFindOrZero fun i ↦ ?_
    have : {t | (S t ∩ ball (d i) (selRadius (k + 1))).Nonempty ∧
        dist (d i) (d (selIndex S d k t)) < 2 * selRadius k} =
        svPreimage S (ball (d i) (selRadius (k + 1))) ∩
          selIndex S d k ⁻¹' {j | dist (d i) (d j) < 2 * selRadius k} := rfl
    rw [this]
    exact (hS _ isOpen_ball).inter (ih (Set.to_countable _).measurableSet)

/-- On `dom S`, each stage of the scheme succeeds. -/
theorem selIndex_spec {S : T → Set F} {d : ℕ → F} (hd : DenseRange d) {t : T}
    (ht : (S t).Nonempty) (k : ℕ) :
    (S t ∩ ball (d (selIndex S d k t)) (selRadius k)).Nonempty ∧
      (∀ j, k = j + 1 →
        dist (d (selIndex S d k t)) (d (selIndex S d j t)) < 2 * selRadius j) := by
  induction k with
  | zero =>
    refine ⟨?_, fun j hj ↦ absurd hj (Nat.succ_ne_zero j).symm⟩
    obtain ⟨s, hs⟩ := ht
    have hex : ∃ i, (S t ∩ ball (d i) (selRadius 0)).Nonempty := by
      obtain ⟨i, hi⟩ := hd.exists_dist_lt s (selRadius_pos 0)
      exact ⟨i, s, hs, hi⟩
    exact natFindOrZero_spec hex
  | succ k ih =>
    have hex : ∃ i, (S t ∩ ball (d i) (selRadius (k + 1))).Nonempty ∧
        dist (d i) (d (selIndex S d k t)) < 2 * selRadius k := by
      obtain ⟨s, hsS, hsb⟩ := ih.1
      obtain ⟨i, hi⟩ := hd.exists_dist_lt s (selRadius_pos (k + 1))
      refine ⟨i, ⟨s, hsS, hi⟩, ?_⟩
      have h1 : dist (d i) s < selRadius (k + 1) := by rwa [dist_comm]
      have h2 : dist s (d (selIndex S d k t)) < selRadius k := hsb
      have h3 : selRadius (k + 1) ≤ selRadius k := by
        rw [selRadius_succ]; linarith [selRadius_pos k]
      calc dist (d i) (d (selIndex S d k t))
          ≤ dist (d i) s + dist s (d (selIndex S d k t)) := dist_triangle _ _ _
        _ < 2 * selRadius k := by linarith
    have hspec := natFindOrZero_spec hex
    refine ⟨hspec.1, fun j hj ↦ ?_⟩
    obtain rfl : k = j := by omega
    exact hspec.2

end SelectionScheme

section Selection

variable {T F : Type*} [MeasurableSpace T] [MetricSpace F] [CompleteSpace F]
  [TopologicalSpace.SeparableSpace F] [MeasurableSpace F] [BorelSpace F]

/-- **Corollary 14.6 (measurable selections)**, in the Kuratowski–Ryll-Nardzewski form: a
closed-valued measurable mapping into a complete separable metric space admits a measurable
function `x` with `x(t) ∈ S(t)` for every `t ∈ dom S`. -/
theorem SvMeasurable.exists_measurable_selection [Nonempty F] {S : T → Set F}
    (hS : SvMeasurable S) (hSc : ∀ t, IsClosed (S t)) :
    ∃ x : T → F, Measurable x ∧ ∀ t ∈ svDom S, x t ∈ S t := by
  set d := TopologicalSpace.denseSeq F
  have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq F
  set u : ℕ → T → F := fun k t ↦ d (selIndex S d k t) with hu
  have hcauchy : ∀ t ∈ svDom S, CauchySeq fun k ↦ u k t := by
    intro t ht
    refine cauchySeq_of_le_geometric_two (C := 4) fun k ↦ ?_
    have h := (selIndex_spec hd ht (k + 1)).2 k rfl
    rw [dist_comm]
    have : 2 * selRadius k = 4 / 2 / 2 ^ k := by
      unfold selRadius
      rw [one_div_pow]
      ring
    linarith
  set x : T → F := fun t ↦ if t ∈ svDom S then limUnder atTop (fun k ↦ u k t) else d 0 with hx
  have htend : ∀ t ∈ svDom S, Tendsto (fun k ↦ u k t) atTop (𝓝 (x t)) := by
    intro t ht
    have hx' : x t = limUnder atTop (fun k ↦ u k t) := if_pos ht
    rw [hx']
    exact tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (hcauchy t ht))
  refine ⟨x, ?_, ?_⟩
  · have hdom := hS.measurableSet_svDom
    have hmeas : ∀ k, Measurable fun t ↦ if t ∈ svDom S then u k t else d 0 := fun k ↦
      Measurable.ite hdom ((measurable_from_top).comp (measurable_selIndex hS d k))
        measurable_const
    refine measurable_of_tendsto_metrizable hmeas (tendsto_pi_nhds.2 fun t ↦ ?_)
    by_cases ht : t ∈ svDom S
    · simp only [ht, if_true]
      exact htend t ht
    · simp only [ht, if_false, hx]
      exact tendsto_const_nhds
  · intro t ht
    choose s hs using fun k ↦ (selIndex_spec hd ht k).1
    refine (hSc t).mem_of_tendsto (f := s) (b := atTop) ?_ (Eventually.of_forall fun k ↦ (hs k).1)
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ ↦ dist_nonneg) (fun k ↦ ?_) (g := fun k ↦
      selRadius k + dist (u k t) (x t)) ?_
    · have h1 : dist (s k) (u k t) < selRadius k := (hs k).2
      exact (dist_triangle _ _ _).trans (by linarith)
    · have h1 : Tendsto selRadius atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      have h2 := (tendsto_iff_dist_tendsto_zero.1 (htend t ht))
      simpa using h1.add h2

end Selection


section Castaing

variable {T F : Type*} [MeasurableSpace T] [MetricSpace F]

/-- A **Castaing representation** of `S`: countably many measurable functions `xν` with
`S(t) = cl {xν(t) | ν ∈ ℕ}` for every `t ∈ dom S` (Theorem 14.5(a)). -/
def IsCastaingRepresentation [MeasurableSpace F] (S : T → Set F) (x : ℕ → T → F) : Prop :=
  (∀ n, Measurable (x n)) ∧ ∀ t ∈ svDom S, S t = closure (range fun n ↦ x n t)

/-- Theorem 14.5, (a) ⇒ measurability: a mapping with measurable domain and a Castaing
representation is measurable (closedness is not needed). -/
theorem IsCastaingRepresentation.svMeasurable [MeasurableSpace F] [OpensMeasurableSpace F]
    {S : T → Set F} {x : ℕ → T → F} (hx : IsCastaingRepresentation S x)
    (hdom : MeasurableSet (svDom S)) : SvMeasurable S := by
  intro O hO
  have : svPreimage S O = svDom S ∩ ⋃ n, x n ⁻¹' O := by
    ext t
    simp only [mem_svPreimage, mem_inter_iff, mem_iUnion, mem_preimage]
    constructor
    · rintro ⟨s, hsS, hsO⟩
      have ht : t ∈ svDom S := ⟨s, hsS⟩
      refine ⟨ht, ?_⟩
      rw [hx.2 t ht] at hsS
      obtain ⟨_, hyO, ⟨n, rfl⟩⟩ := _root_.mem_closure_iff.1 hsS O hO hsO
      exact ⟨n, hyO⟩
    · rintro ⟨ht, n, hn⟩
      refine ⟨x n t, ?_, hn⟩
      rw [hx.2 t ht]
      exact subset_closure ⟨n, rfl⟩
  rw [this]
  exact hdom.inter (MeasurableSet.iUnion fun n ↦ (hx.1 n) hO.measurableSet)

/-- Theorem 14.5(b): the domain is automatically measurable for a family as in (b). -/
theorem measurableSet_svDom_of_dense_family {S : T → Set F} {y : ℕ → T → F}
    (hT : ∀ n, MeasurableSet {t | y n t ∈ S t})
    (hdense : ∀ t, S t ⊆ closure (S t ∩ range fun n ↦ y n t)) :
    MeasurableSet (svDom S) := by
  have : svDom S = ⋃ n, {t | y n t ∈ S t} := by
    ext t
    simp only [mem_svDom, mem_iUnion, mem_setOf_eq]
    constructor
    · rintro ⟨s, hs⟩
      obtain ⟨_, -, hzS, ⟨n, rfl⟩⟩ :=
        _root_.mem_closure_iff.1 (hdense t hs) univ isOpen_univ trivial
      exact ⟨n, hzS⟩
    · rintro ⟨n, hn⟩
      exact ⟨_, hn⟩
  rw [this]
  exact MeasurableSet.iUnion hT

/-- Theorem 14.5, (b) ⇒ measurability (closedness is not needed). -/
theorem svMeasurable_of_dense_family [MeasurableSpace F] [OpensMeasurableSpace F]
    {S : T → Set F} {y : ℕ → T → F} (hy : ∀ n, Measurable (y n))
    (hT : ∀ n, MeasurableSet {t | y n t ∈ S t})
    (hdense : ∀ t, S t ⊆ closure (S t ∩ range fun n ↦ y n t)) : SvMeasurable S := by
  intro O hO
  have : svPreimage S O = ⋃ n, {t | y n t ∈ S t} ∩ y n ⁻¹' O := by
    ext t
    simp only [mem_svPreimage, mem_iUnion, mem_inter_iff, mem_setOf_eq, mem_preimage]
    constructor
    · rintro ⟨s, hsS, hsO⟩
      obtain ⟨_, hzO, hzS, ⟨n, rfl⟩⟩ := _root_.mem_closure_iff.1 (hdense t hsS) O hO hsO
      exact ⟨n, hzS, hzO⟩
    · rintro ⟨n, hn, hnO⟩
      exact ⟨y n t, hn, hnO⟩
  rw [this]
  exact MeasurableSet.iUnion fun n ↦ (hT n).inter ((hy n) hO.measurableSet)

variable [ProperSpace F] [MeasurableSpace F] [BorelSpace F]

/-- Theorem 14.5, measurability ⇒ (a): every closed-valued measurable mapping into a proper
space has a Castaing representation. -/
theorem SvMeasurable.exists_castaingRepresentation [Nonempty F] {S : T → Set F}
    (hS : SvMeasurable S) (hSc : ∀ t, IsClosed (S t)) :
    ∃ x : ℕ → T → F, IsCastaingRepresentation S x := by
  set d := TopologicalSpace.denseSeq F
  have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq F
  set B : ℕ × ℚ → Set F := fun p ↦ closedBall (d p.1) p.2 with hB
  set Sp : ℕ × ℚ → T → Set F :=
    fun p t ↦ if t ∈ svPreimage S (B p) then S t ∩ B p else S t with hSpdef
  have hSp : ∀ p, SvMeasurable (Sp p) := fun p ↦
    SvMeasurable.ite (hS.measurableSet_svPreimage_of_isClosed hSc isClosed_closedBall)
      (hS.inter_isClosed hSc isClosed_closedBall) hS
  have hSpc : ∀ p t, IsClosed (Sp p t) := by
    intro p t
    simp only [hSpdef]
    split_ifs
    · exact (hSc t).inter isClosed_closedBall
    · exact hSc t
  have hSpdom : ∀ p t, t ∈ svDom S → t ∈ svDom (Sp p) := by
    intro p t ht
    simp only [mem_svDom, hSpdef]
    split_ifs with h
    · exact h
    · exact ht
  choose xs hxs hxsS using fun p ↦ (hSp p).exists_measurable_selection (hSpc p)
  have hmemS : ∀ p t, t ∈ svDom S → xs p t ∈ S t := by
    intro p t ht
    have h := hxsS p t (hSpdom p t ht)
    simp only [hSpdef] at h
    split_ifs at h
    · exact h.1
    · exact h
  have hmemB : ∀ p t, t ∈ svDom S → t ∈ svPreimage S (B p) → xs p t ∈ B p := by
    intro p t ht hp
    have h := hxsS p t (hSpdom p t ht)
    simp only [hSpdef, if_pos hp] at h
    exact h.2
  obtain ⟨e, he⟩ : ∃ e : ℕ → ℕ × ℚ, Function.Surjective e := exists_surjective_nat _
  refine ⟨fun n ↦ xs (e n), fun n ↦ hxs (e n), fun t ht ↦ ?_⟩
  apply Subset.antisymm
  · intro s hs
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨q, hq0, hq⟩ := exists_rat_btwn (half_pos hε)
    have hq0' : (0 : ℝ) < q := hq0
    obtain ⟨i, hi⟩ := hd.exists_dist_lt s hq0'
    obtain ⟨n, hn⟩ := he (i, q)
    have hsB : s ∈ B (i, q) := by
      simp only [hB, mem_closedBall]
      exact hi.le
    have hxB := hmemB (i, q) t ht ⟨s, hs, hsB⟩
    simp only [hB, mem_closedBall] at hxB
    refine ⟨xs (e n) t, ⟨n, rfl⟩, ?_⟩
    rw [hn]
    calc dist s (xs (i, q) t) ≤ dist s (d i) + dist (d i) (xs (i, q) t) := dist_triangle _ _ _
      _ < q + q := by rw [dist_comm (d i)]; linarith
      _ < ε := by linarith
  · exact closure_minimal (range_subset_iff.2 fun n ↦ hmemS (e n) t ht) (hSc t)

/-- **Theorem 14.5 (Castaing representations).**  For a closed-valued mapping `S : T ⇉ F` into a
proper metric space, measurability of `S` is equivalent to each of
(a) `dom S` is measurable and `S` admits a Castaing representation;
(b) `dom S` is measurable and there are measurable `yν` such that each
`Tν = {t | yν(t) ∈ S(t)}` is measurable and `S(t) ∩ {yν(t) | ν}` is dense in `S(t)` for every `t`.
(In (b) the measurability of `dom S` is automatic: `measurableSet_svDom_of_dense_family`.) -/
theorem castaing_representations [Nonempty F] {S : T → Set F} (hSc : ∀ t, IsClosed (S t)) :
    (SvMeasurable S ↔
        MeasurableSet (svDom S) ∧ ∃ x : ℕ → T → F, IsCastaingRepresentation S x) ∧
      (SvMeasurable S ↔ MeasurableSet (svDom S) ∧ ∃ y : ℕ → T → F, (∀ n, Measurable (y n)) ∧
        (∀ n, MeasurableSet {t | y n t ∈ S t}) ∧
          ∀ t, S t ⊆ closure (S t ∩ range fun n ↦ y n t)) := by
  constructor
  · constructor
    · intro hS
      exact ⟨hS.measurableSet_svDom, hS.exists_castaingRepresentation hSc⟩
    · rintro ⟨hdom, x, hx⟩
      exact hx.svMeasurable hdom
  · constructor
    · intro hS
      obtain ⟨x, hx⟩ := hS.exists_castaingRepresentation hSc
      refine ⟨hS.measurableSet_svDom, x, hx.1, fun n ↦ ?_, fun t s hs ↦ ?_⟩
      · have : {t | x n t ∈ S t} = svDom S := by
          ext t
          constructor
          · intro h
            exact ⟨_, h⟩
          · intro ht
            change x n t ∈ S t
            rw [hx.2 t ht]
            exact subset_closure ⟨n, rfl⟩
        rw [this]
        exact hS.measurableSet_svDom
      · have ht : t ∈ svDom S := ⟨s, hs⟩
        have hsub : range (fun n ↦ x n t) ⊆ S t ∩ range fun n ↦ x n t := fun z hz ↦
          ⟨by rw [hx.2 t ht]; exact subset_closure hz, hz⟩
        rw [hx.2 t ht] at hs
        exact closure_mono hsub hs
    · rintro ⟨-, y, hy, hT, hdense⟩
      exact svMeasurable_of_dense_family hy hT hdense

/-- **Corollary 14.6 (measurable selections)** for mappings into a proper space (a special
case of `SvMeasurable.exists_measurable_selection`, which allows any complete separable
metric space). -/
theorem measurable_selections [Nonempty F] {S : T → Set F} (hS : SvMeasurable S)
    (hSc : ∀ t, IsClosed (S t)) : ∃ x : T → F, Measurable x ∧ ∀ t ∈ svDom S, x t ∈ S t :=
  hS.exists_measurable_selection hSc

/-- **Example 14.7 (convex-valued and solid-valued mappings).**  A solid-valued mapping,
`S(t) = cl (int S(t))` for all `t`, is measurable if and only if `S⁻¹(x) = {t | x ∈ S(t)}` is
measurable for every `x`. -/
theorem svMeasurable_iff_of_solidValued {S : T → Set F}
    (hsolid : ∀ t, S t = closure (interior (S t))) :
    SvMeasurable S ↔ ∀ x : F, MeasurableSet {t | x ∈ S t} := by
  have hSc : ∀ t, IsClosed (S t) := fun t ↦ by rw [hsolid t]; exact isClosed_closure
  constructor
  · intro hS x
    have := hS.measurableSet_svPreimage_of_isCompact hSc (isCompact_singleton (x := x))
    rwa [svPreimage_singleton] at this
  · intro h
    rcases isEmpty_or_nonempty F with hF | hF
    · intro O _
      have : svPreimage S O = ∅ := by
        ext t
        simp only [mem_svPreimage, mem_empty_iff_false, iff_false]
        rintro ⟨s, -⟩
        exact hF.elim s
      rw [this]
      exact MeasurableSet.empty
    set d := TopologicalSpace.denseSeq F
    have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq F
    refine svMeasurable_of_dense_family (y := fun n _ ↦ d n) (fun _ ↦ measurable_const)
      (fun n ↦ h (d n)) fun t s hs ↦ ?_
    rw [hsolid t] at hs
    rw [_root_.mem_closure_iff] at hs ⊢
    intro O hO hsO
    obtain ⟨z, hzO, hzint⟩ := hs O hO hsO
    obtain ⟨_, ⟨hwO, hwint⟩, ⟨n, rfl⟩⟩ :=
      hd.inter_open_nonempty _ (hO.inter isOpen_interior) ⟨z, hzO, hzint⟩
    exact ⟨d n, hwO, interior_subset hwint, ⟨n, rfl⟩⟩

end Castaing

section ConvexSolid

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Example 14.7: a closed convex set with nonempty interior is the closure of its interior,
so closed-convex-valued mappings with nonempty interiors are solid-valued. -/
theorem eq_closure_interior_of_convex {C : Set F} (hC : Convex ℝ C) (hCc : IsClosed C)
    (hint : (interior C).Nonempty) : C = closure (interior C) := by
  rw [hC.closure_interior_eq_closure_of_nonempty_interior hint, hCc.closure_eq]

end ConvexSolid

end RW
