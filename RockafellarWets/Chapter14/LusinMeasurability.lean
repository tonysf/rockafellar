/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 14: Measurability versus continuity

Theorem 14.10 of Rockafellar–Wets.  The setting `T ∈ B(ℝᵈ)`, `A = L(T)`, `μ` = Lebesgue measure is
modelled by a Borel set `T₀` in a finite-dimensional space `E` and a measure `μ` on `E` that is finite
on compact sets and inner regular by compact sets on sets of finite measure (as Lebesgue measure is);
`S⁻¹(O) ∈ L(T)` becomes null-measurability of `T₀ ∩ S⁻¹(O)` (`SvNullMeasurableOn`), the Lebesgue sets
being the null-measurable sets of Lebesgue measure.

Proof as in the book: a Borel modification on a full-measure Borel subset, a Lusin-type construction
(compact inner approximations of `S⁻¹(O)` and of its complement for the countably many rational open and
closed balls, giving relatively open, resp. closed, inverse images: Theorem 5.7) on pieces of finite
measure, glued along the annuli `{j ≤ ‖t‖ < j + 1}`, and for (c) the measurable projection theorem
(projections of Borel sets are analytic, hence Lebesgue measurable).
-/

import RockafellarWets.Chapter14.AnalyticMeasurability
import RockafellarWets.Chapter14.GraphMeasurability
import RockafellarWets.Chapter5.SemicontinuityCriteria
import Mathlib.MeasureTheory.Measure.Regular

open Set Filter Topology Metric MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace RW

section Locality

variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]

/-- Relative continuity at `x` only depends on the set near `x`. -/
theorem SvContinuousWithinAt.congr_set {S : E → Set F} {X Y V : Set E} {x : E} (hV : V ∈ 𝓝 x)
    (hXY : X ∩ V = Y ∩ V) (h : SvContinuousWithinAt S X x) : SvContinuousWithinAt S Y x := by
  have hn := nhdsWithin_eq_nhdsWithin' hV hXY
  unfold SvContinuousWithinAt SvOscWithinAt SvIscWithinAt svOuterLimitWithin
    svInnerLimitWithin at *
  rwa [← hn]

/-- Outer semicontinuity relative to a closed set `K` makes the graph over `K` closed. -/
theorem SvOscOn.isClosed_svGraph_inter {S : E → Set F} {K : Set E} (hK : IsClosed K)
    (h : SvOscOn S K) : IsClosed (svGraph S ∩ (K ×ˢ univ)) := by
  rw [← closure_subset_iff_isClosed]
  rintro ⟨x, u⟩ hp
  have hxK : (x, u) ∈ K ×ˢ (univ : Set F) :=
    (closure_mono inter_subset_right).trans (hK.prod isClosed_univ).closure_subset hp
  refine ⟨?_, hxK⟩
  by_contra hu
  obtain ⟨W, hW, V, hV, hempty⟩ := svOscWithinAt_iff.1 (h x hxK.1) u hu
  obtain ⟨⟨y, v⟩, hyv, hgraph, hyK⟩ :=
    mem_closure_iff_nhds.1 hp (V ×ˢ W) (prod_mem_nhds hV hW)
  have : y ∈ K ∩ V ∩ svPreimage S W := ⟨⟨hyK.1, hyv.1⟩, v, hgraph, hyv.2⟩
  rw [hempty] at this
  exact this

end Locality

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

section LusinFinite

/-- Rational balls: around every point of an open set there is a rational ball (center from the
dense sequence, rational radius) containing the point whose closure lies in the set. -/
theorem exists_denseSeq_ball_subset {O : Set F} (hO : IsOpen O) {u : F} (hu : u ∈ O) :
    ∃ p : ℕ × ℚ, u ∈ ball (TopologicalSpace.denseSeq F p.1) p.2 ∧
      closedBall (TopologicalSpace.denseSeq F p.1) p.2 ⊆ O := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hO u hu
  obtain ⟨i, hi⟩ := (TopologicalSpace.denseRange_denseSeq F).exists_dist_lt u
    (by linarith : 0 < r / 4)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show r / 4 < r / 2 by linarith)
  refine ⟨(i, q), ?_, fun z hz ↦ hball ?_⟩
  · show dist u _ < (q : ℝ)
    linarith
  · rw [mem_closedBall] at hz
    rw [mem_ball]
    calc dist z u ≤ dist z (TopologicalSpace.denseSeq F i) +
          dist u (TopologicalSpace.denseSeq F i) := dist_triangle_right _ _ _
      _ < r := by linarith

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Lusin-type construction** (proof of Theorem 14.10): a closed-valued mapping whose inverse
images of open sets meet a Borel set `A` of finite measure in measurable sets is continuous relative
to a compact `K ⊆ A` with `μ(A \ K) < ε`. -/
theorem exists_isCompact_svContinuousOn (μ : Measure E) [μ.InnerRegularCompactLTTop]
    {S : E → Set F} (hSc : ∀ t, IsClosed (S t)) {A : Set E} (hA : MeasurableSet A)
    (hAμ : μ A ≠ ∞) (hS : ∀ O : Set F, IsOpen O → MeasurableSet (A ∩ svPreimage S O))
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K ⊆ A, IsCompact K ∧ μ (A \ K) < ε ∧ SvContinuousOn S K := by
  classical
  set D := TopologicalSpace.denseSeq F
  set SA : E → Set F := fun t ↦ if t ∈ A then S t else ∅
  have hSA : SvMeasurable SA := fun O hO ↦ by
    have : svPreimage SA O = A ∩ svPreimage S O := by
      ext t
      by_cases ht : t ∈ A <;> simp [SA, svPreimage, ht]
    rw [this]
    exact hS O hO
  have hSAc : ∀ t, IsClosed (SA t) := fun t ↦ by
    by_cases ht : t ∈ A
    · simp only [SA, ht, if_true]
      exact hSc t
    · simp only [SA, ht, if_false]
      exact isClosed_empty
  set P : ℕ × ℚ → Set E := fun p ↦ A ∩ svPreimage S (ball (D p.1) p.2)
  set Q : ℕ × ℚ → Set E := fun p ↦ A ∩ svPreimage S (closedBall (D p.1) p.2)
  have hP : ∀ p, MeasurableSet (P p) := fun p ↦ hS _ isOpen_ball
  have hQ : ∀ p, MeasurableSet (Q p) := fun p ↦ by
    have : Q p = svPreimage SA (closedBall (D p.1) p.2) := by
      ext t
      by_cases ht : t ∈ A <;> simp [Q, SA, svPreimage, ht]
    rw [this]
    exact hSA.measurableSet_svPreimage_of_isCompact hSAc (isCompact_closedBall _ _)
  have hε4 : ε / 4 ≠ 0 := by simp [hε]
  obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable hε4 (ℕ × ℚ)
  have happrox : ∀ M : Set E, MeasurableSet M → M ⊆ A → ∀ p : ℕ × ℚ,
      ∃ K ⊆ M, IsCompact K ∧ μ (M \ K) < δ p := fun M hM hMA p ↦
    hM.exists_isCompact_diff_lt (ne_top_of_le_ne_top hAμ (measure_mono hMA))
      (by exact_mod_cast (hδpos p).ne')
  have h1 := fun p ↦ happrox (P p) (hP p) inter_subset_left p
  have h2 := fun p ↦ happrox (A \ P p) (hA.diff (hP p)) diff_subset p
  have h3 := fun p ↦ happrox (Q p) (hQ p) inter_subset_left p
  have h4 := fun p ↦ happrox (A \ Q p) (hA.diff (hQ p)) diff_subset p
  choose K1 hK1s hK1c hK1μ using h1
  choose K2 hK2s hK2c hK2μ using h2
  choose L1 hL1s hL1c hL1μ using h3
  choose L2 hL2s hL2c hL2μ using h4
  set K : Set E := (⋂ p, (K1 p ∪ K2 p)) ∩ ⋂ p, (L1 p ∪ L2 p) with hKdef
  have hK12 : ∀ p, K ⊆ K1 p ∪ K2 p := fun p ↦ inter_subset_left.trans (iInter_subset _ p)
  have hL12 : ∀ p, K ⊆ L1 p ∪ L2 p := fun p ↦ inter_subset_right.trans (iInter_subset _ p)
  have hKA : K ⊆ A := (hK12 (0, 0)).trans (union_subset ((hK1s _).trans inter_subset_left)
    ((hK2s _).trans diff_subset))
  have hKclosed : IsClosed K :=
    (isClosed_iInter fun p ↦ (hK1c p).isClosed.union (hK2c p).isClosed).inter
      (isClosed_iInter fun p ↦ (hL1c p).isClosed.union (hL2c p).isClosed)
  have hKc : IsCompact K :=
    ((hK1c (0, 0)).union (hK2c (0, 0))).of_isClosed_subset hKclosed (hK12 (0, 0))
  refine ⟨K, hKA, hKc, ?_, ?_⟩
  · -- the measure estimate
    have hsub : A \ K ⊆ (⋃ p, ((P p \ K1 p) ∪ ((A \ P p) \ K2 p))) ∪
        ⋃ p, ((Q p \ L1 p) ∪ ((A \ Q p) \ L2 p)) := by
      rintro t ⟨htA, htK⟩
      rw [hKdef, mem_inter_iff, not_and_or, mem_iInter, mem_iInter, not_forall,
        not_forall] at htK
      rcases htK with ⟨p, hp⟩ | ⟨p, hp⟩
      · refine Or.inl (mem_iUnion.2 ⟨p, ?_⟩)
        by_cases htP : t ∈ P p
        · exact Or.inl ⟨htP, fun h ↦ hp (Or.inl h)⟩
        · exact Or.inr ⟨⟨htA, htP⟩, fun h ↦ hp (Or.inr h)⟩
      · refine Or.inr (mem_iUnion.2 ⟨p, ?_⟩)
        by_cases htQ : t ∈ Q p
        · exact Or.inl ⟨htQ, fun h ↦ hp (Or.inl h)⟩
        · exact Or.inr ⟨⟨htA, htQ⟩, fun h ↦ hp (Or.inr h)⟩
    have hsum : ∀ (X Y : ℕ × ℚ → Set E), (∀ p, μ (X p) < δ p) → (∀ p, μ (Y p) < δ p) →
        μ (⋃ p, (X p ∪ Y p)) ≤ 2 * ∑' p, (δ p : ℝ≥0∞) := by
      intro X Y hX hY
      calc μ (⋃ p, (X p ∪ Y p)) ≤ ∑' p, μ (X p ∪ Y p) := measure_iUnion_le _
        _ ≤ ∑' p, 2 * (δ p : ℝ≥0∞) := ENNReal.tsum_le_tsum fun p ↦
            (measure_union_le _ _).trans (by rw [two_mul]; exact add_le_add (hX p).le (hY p).le)
        _ = 2 * ∑' p, (δ p : ℝ≥0∞) := ENNReal.tsum_mul_left
    calc μ (A \ K) ≤ μ (⋃ p, ((P p \ K1 p) ∪ ((A \ P p) \ K2 p))) +
          μ (⋃ p, ((Q p \ L1 p) ∪ ((A \ Q p) \ L2 p))) :=
          (measure_mono hsub).trans (measure_union_le _ _)
      _ ≤ 2 * ∑' p, (δ p : ℝ≥0∞) + 2 * ∑' p, (δ p : ℝ≥0∞) :=
          add_le_add (hsum _ _ hK1μ hK2μ) (hsum _ _ hL1μ hL2μ)
      _ = 4 * ∑' p, (δ p : ℝ≥0∞) := by ring
      _ < ε := by
          rw [mul_comm]
          exact ENNReal.mul_lt_of_lt_div hδsum
  · intro x hxK
    refine ⟨?_, ?_⟩
    · -- outer semicontinuity relative to `K`
      have hval : ∀ y ∈ K, IsClosed (S y) := fun y _ ↦ hSc y
      have hosc : SvOscOn S K := by
        rw [svOscOn_iff_closure_svPreimage hval]
        intro B hB y ⟨hyK, hycl⟩
        by_contra hyB
        have hdisj : ∀ b ∈ B, ∃ p : ℕ × ℚ, b ∈ ball (D p.1) p.2 ∧
            closedBall (D p.1) p.2 ⊆ (S y)ᶜ := fun b hb ↦
          exists_denseSeq_ball_subset (hSc y).isOpen_compl fun hbS ↦ hyB ⟨b, hbS, hb⟩
        choose! pb hpb hpbS using hdisj
        obtain ⟨s, hsB, hcover⟩ := hB.elim_nhds_subcover (fun b ↦ ball (D (pb b).1) (pb b).2)
          fun b hb ↦ isOpen_ball.mem_nhds (hpb b hb)
        have hyL : ∀ b ∈ s, y ∉ L1 (pb b) := fun b hb hyL ↦ by
          obtain ⟨v, hvS, hvB⟩ := ((hL1s (pb b)) hyL).2
          exact hpbS b (hsB b hb) hvB hvS
        have hW : (⋂ b ∈ s, (L1 (pb b))ᶜ) ∈ 𝓝 y :=
          (Finset.iInter_mem_sets s).2 fun b hb ↦ (hL1c (pb b)).isClosed.isOpen_compl.mem_nhds
            (hyL b hb)
        obtain ⟨z, hzW, hzK, w, hwS, hwB⟩ := mem_closure_iff_nhds.1 hycl _ hW
        obtain ⟨b, hb, hwb⟩ := mem_iUnion₂.1 (hcover hwB)
        have hzQ : z ∈ Q (pb b) := ⟨hKA hzK, w, hwS, ball_subset_closedBall hwb⟩
        rcases hL12 (pb b) hzK with hz1 | hz2
        · exact mem_iInter₂.1 hzW b hb hz1
        · exact ((hL2s (pb b)) hz2).2 hzQ
      exact hosc x hxK
    · -- inner semicontinuity relative to `K`
      have hisc : SvIscOn S K := by
        rw [svIscOn_iff_eventually_svPreimage]
        intro O hO y hyK ⟨u, huS, huO⟩
        obtain ⟨p, hup, hpO⟩ := exists_denseSeq_ball_subset hO huO
        have hyP : y ∈ P p := ⟨hKA hyK, u, huS, hup⟩
        have hyK2 : y ∉ K2 p := fun h ↦ ((hK2s p) h).2 hyP
        have hev : ∀ᶠ z in 𝓝[K] y, z ∈ K ∧ z ∈ (K2 p)ᶜ :=
          (eventually_mem_nhdsWithin).and
            (nhdsWithin_le_nhds ((hK2c p).isClosed.isOpen_compl.mem_nhds hyK2))
        refine hev.mono fun z ⟨hzK, hz2⟩ ↦ ?_
        rcases hK12 p hzK with hz1 | hz2'
        · obtain ⟨v, hvS, hvB⟩ := ((hK1s p) hz1).2
          exact ⟨v, hvS, hpO (ball_subset_closedBall hvB)⟩
        · exact absurd hz2' hz2
      exact hisc x hxK

end LusinFinite

section Theorem1410

variable [MeasurableSpace F] [BorelSpace F]

/-- Measurability of `S : T ⇉ F` with respect to `L(T)`, `T = T₀`: every `T₀ ∩ S⁻¹(O)`, `O` open, is
null-measurable (Lebesgue measurable when `μ` is Lebesgue measure). -/
def SvNullMeasurableOn (μ : Measure E) (T₀ : Set E) (S : E → Set F) : Prop :=
  ∀ O : Set F, IsOpen O → NullMeasurableSet (T₀ ∩ svPreimage S O) μ

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F] in
/-- Borel modification: an `L(T)`-measurable mapping is Borel measurable on `T₀ \ N` for a Borel
null set `N`. -/
theorem SvNullMeasurableOn.exists_null {μ : Measure E} {T₀ : Set E} {S : E → Set F}
    (h : SvNullMeasurableOn μ T₀ S) (hT₀ : MeasurableSet T₀) :
    ∃ N, MeasurableSet N ∧ μ N = 0 ∧
      ∀ O : Set F, IsOpen O → MeasurableSet ((T₀ \ N) ∩ svPreimage S O) := by
  set D := TopologicalSpace.denseSeq F
  set s : ℕ × ℚ → Set E := fun p ↦ T₀ ∩ svPreimage S (ball (D p.1) p.2)
  set t : ℕ × ℚ → Set E := fun p ↦ toMeasurable μ (s p)
  have hst : ∀ p, s p =ᵐ[μ] t p := fun p ↦ (h _ isOpen_ball).toMeasurable_ae_eq.symm
  set N : Set E := ⋃ p, toMeasurable μ ((s p \ t p) ∪ (t p \ s p))
  have hN0 : μ N = 0 := measure_iUnion_null fun p ↦ by
    rw [measure_toMeasurable]
    obtain ⟨h1, h2⟩ := ae_eq_set.1 (hst p)
    exact measure_union_null h1 h2
  refine ⟨N, MeasurableSet.iUnion fun p ↦ measurableSet_toMeasurable _ _, hN0, fun O hO ↦ ?_⟩
  have heq : (T₀ \ N) ∩ svPreimage S O = ⋃ p : ℕ × ℚ, ⋃ (_ : ball (D p.1) p.2 ⊆ O),
      (T₀ \ N) ∩ t p := by
    ext x
    simp only [mem_inter_iff, mem_diff, mem_iUnion, exists_prop]
    have hiff : ∀ p, x ∈ T₀ → x ∉ N → (x ∈ svPreimage S (ball (D p.1) p.2) ↔ x ∈ t p) := by
      intro p hxT hxN
      have hxN' : x ∉ (s p \ t p) ∪ (t p \ s p) := fun hx ↦
        hxN (mem_iUnion.2 ⟨p, subset_toMeasurable _ _ hx⟩)
      constructor
      · intro hx
        by_contra hxt
        exact hxN' (Or.inl ⟨⟨hxT, hx⟩, hxt⟩)
      · intro hxt
        by_contra hx
        exact hxN' (Or.inr ⟨hxt, fun hs ↦ hx hs.2⟩)
    constructor
    · rintro ⟨⟨hxT, hxN⟩, u, huS, huO⟩
      obtain ⟨p, hup, hpO⟩ := exists_denseSeq_ball_subset hO huO
      exact ⟨p, ball_subset_closedBall.trans hpO, ⟨hxT, hxN⟩,
        (hiff p hxT hxN).1 ⟨u, huS, hup⟩⟩
    · rintro ⟨p, hpO, ⟨hxT, hxN⟩, hxt⟩
      obtain ⟨u, huS, hup⟩ := (hiff p hxT hxN).2 hxt
      exact ⟨⟨hxT, hxN⟩, u, huS, hpO hup⟩
  rw [heq]
  exact MeasurableSet.iUnion fun p ↦ MeasurableSet.iUnion fun _ ↦
    (hT₀.diff (MeasurableSet.iUnion fun p ↦ measurableSet_toMeasurable _ _)).inter
      (measurableSet_toMeasurable _ _)

/-- (c) ⇒ measurability: the inverse images of a mapping with Borel graph over `T₀` are analytic,
hence null-measurable for every s-finite measure (measurable projection theorem). -/
theorem nullMeasurableSet_inter_svPreimage_of_measurableSet_svGraph (μ : Measure E) [SFinite μ]
    {T₀ : Set E} {R : E → Set F} (hR : MeasurableSet (svGraph R ∩ (T₀ ×ˢ univ))) {O : Set F}
    (hO : IsOpen O) : NullMeasurableSet (T₀ ∩ svPreimage R O) μ := by
  have heq : T₀ ∩ svPreimage R O = Prod.fst '' (svGraph R ∩ (T₀ ×ˢ univ) ∩ (univ ×ˢ O)) := by
    ext t
    simp only [mem_inter_iff, svPreimage, mem_setOf_eq, mem_image, mem_svGraph, mem_prod,
      mem_univ, and_true, true_and, Prod.exists, exists_and_right, exists_eq_right]
    constructor
    · rintro ⟨htT, u, huR, huO⟩
      exact ⟨u, ⟨huR, htT⟩, huO⟩
    · rintro ⟨u, ⟨huR, htT⟩, huO⟩
      exact ⟨htT, u, huR, huO⟩
  rw [heq]
  have hA : AnalyticSet (Prod.fst '' (svGraph R ∩ (T₀ ×ˢ univ) ∩ (univ ×ˢ O))) :=
    (hR.inter (MeasurableSet.univ.prod hO.measurableSet)).analyticSet_image measurable_fst
  exact (RW.AnalyticSet.nullMeasurableSet hA μ.toFinite).mono_ac (absolutelyContinuous_toFinite μ)

/-- The annuli `{j ≤ ‖t‖ < j + 1}`. -/
def normAnnulus (j : ℕ) : Set E := {t | (j : ℝ) ≤ ‖t‖ ∧ ‖t‖ < (j : ℝ) + 1}

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
theorem locallyFinite_of_subset_normAnnulus {K : ℕ → Set E} (hK : ∀ j, K j ⊆ normAnnulus j) :
    LocallyFinite K := by
  intro x
  refine ⟨ball x 1, ball_mem_nhds x one_pos, ?_⟩
  refine (Set.finite_Iic (⌈‖x‖⌉₊ + 1)).subset fun j ⟨y, hyK, hyB⟩ ↦ ?_
  have hy := (hK j hyK).1
  rw [mem_ball, dist_eq_norm] at hyB
  have h1 : ‖y‖ ≤ ‖x‖ + 1 := by
    have := norm_sub_norm_le y x
    linarith
  have h2 : (j : ℝ) ≤ (⌈‖x‖⌉₊ : ℝ) + 1 := by
    have := Nat.le_ceil ‖x‖
    linarith
  show j ≤ ⌈‖x‖⌉₊ + 1
  exact_mod_cast h2

omit [MeasurableSpace F] [BorelSpace F] in
/-- Measurable ⇒ (a) of Theorem 14.10 on a set where the mapping is Borel measurable: glue the
finite-measure construction over the annuli. -/
theorem exists_isClosed_svContinuousOn (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    [μ.InnerRegularCompactLTTop] {S : E → Set F} (hSc : ∀ t, IsClosed (S t)) {T₁ : Set E}
    (hT₁ : MeasurableSet T₁) (hS : ∀ O : Set F, IsOpen O → MeasurableSet (T₁ ∩ svPreimage S O))
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K ⊆ T₁, IsClosed K ∧ μ (T₁ \ K) < ε ∧ SvContinuousOn S K := by
  obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable hε ℕ
  have hAn : ∀ j : ℕ, MeasurableSet (T₁ ∩ normAnnulus j) := fun j ↦
    hT₁.inter ((measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_lt measurable_norm measurable_const))
  have hAμ : ∀ j : ℕ, μ (T₁ ∩ normAnnulus j) ≠ ∞ := fun j ↦
    ne_top_of_le_ne_top (measure_closedBall_lt_top (x := (0 : E)) (r := (j : ℝ) + 1)).ne
      (measure_mono fun t ht ↦ by
        rw [mem_closedBall, dist_zero_right]
        exact ht.2.2.le)
  have hpiece := fun j ↦ exists_isCompact_svContinuousOn μ hSc (hAn j) (hAμ j)
    (fun O hO ↦ by
      have : (T₁ ∩ normAnnulus j) ∩ svPreimage S O = (T₁ ∩ svPreimage S O) ∩ normAnnulus j := by
        ext t
        simp only [mem_inter_iff]
        tauto
      rw [this]
      exact (hS O hO).inter ((measurableSet_le measurable_const measurable_norm).inter
        (measurableSet_lt measurable_norm measurable_const)))
    (by exact_mod_cast (hδpos j).ne' : (δ j : ℝ≥0∞) ≠ 0)
  choose K hKs hKc hKμ hKcont using hpiece
  have hKA : ∀ j, K j ⊆ normAnnulus j := fun j ↦ (hKs j).trans inter_subset_right
  have hlf := locallyFinite_of_subset_normAnnulus hKA
  refine ⟨⋃ j, K j, iUnion_subset fun j ↦ (hKs j).trans inter_subset_left,
    hlf.isClosed_iUnion fun j ↦ (hKc j).isClosed, ?_, ?_⟩
  · have hsub : T₁ \ ⋃ j, K j ⊆ ⋃ j, ((T₁ ∩ normAnnulus j) \ K j) := by
      rintro t ⟨htT, htK⟩
      refine mem_iUnion.2 ⟨⌊‖t‖⌋₊, ⟨htT, Nat.floor_le (norm_nonneg t), Nat.lt_floor_add_one _⟩,
        fun h ↦ htK (mem_iUnion.2 ⟨_, h⟩)⟩
    calc μ (T₁ \ ⋃ j, K j) ≤ ∑' j, μ ((T₁ ∩ normAnnulus j) \ K j) :=
          (measure_mono hsub).trans (measure_iUnion_le _)
      _ ≤ ∑' j, (δ j : ℝ≥0∞) := ENNReal.tsum_le_tsum fun j ↦ (hKμ j).le
      _ < ε := hδsum
  · intro x hx
    obtain ⟨j, hxj⟩ := mem_iUnion.1 hx
    have hdisj : ∀ i, i ≠ j → x ∉ K i := fun i hij hxi ↦ by
      have h1 := hKA i hxi
      have h2 := hKA j hxj
      simp only [normAnnulus, mem_setOf_eq] at h1 h2
      have : (i : ℝ) < (j : ℝ) + 1 := by linarith
      have : (j : ℝ) < (i : ℝ) + 1 := by linarith
      have : i = j := by
        have h3 : i < j + 1 := by exact_mod_cast (by linarith : (i : ℝ) < (j : ℝ) + 1)
        have h4 : j < i + 1 := by exact_mod_cast (by linarith : (j : ℝ) < (i : ℝ) + 1)
        omega
      exact hij this
    set V : Set E := (⋃ i, if i = j then ∅ else K i)ᶜ
    have hlf' : LocallyFinite fun i ↦ if i = j then (∅ : Set E) else K i :=
      hlf.subset fun i ↦ by split_ifs <;> simp
    have hV : V ∈ 𝓝 x := by
      refine (hlf'.isClosed_iUnion fun i ↦ ?_).isOpen_compl.mem_nhds ?_
      · split_ifs
        · exact isClosed_empty
        · exact (hKc i).isClosed
      · simp only [mem_compl_iff, mem_iUnion, not_exists]
        intro i
        split_ifs with hij
        · exact notMem_empty x
        · exact hdisj i hij
    have hVeq : K j ∩ V = (⋃ i, K i) ∩ V := by
      ext y
      simp only [mem_inter_iff, mem_iUnion, V, mem_compl_iff, not_exists]
      constructor
      · rintro ⟨hy, hyV⟩
        exact ⟨⟨j, hy⟩, hyV⟩
      · rintro ⟨⟨i, hy⟩, hyV⟩
        refine ⟨?_, hyV⟩
        by_cases hij : i = j
        · exact hij ▸ hy
        · have := hyV i
          rw [if_neg hij] at this
          exact absurd hy this
    exact (hKcont j x hxj).congr_set hV hVeq

/-- **Theorem 14.10 (measurability versus continuity).** For a Borel set `T₀` in a
finite-dimensional space, a measure `μ` finite on compact sets and inner regular by compact sets on
sets of finite measure (Lebesgue measure), and a closed-valued `S : T₀ ⇉ F`, the following are
equivalent to the `L(T)`-measurability of `S`: (a) for every `ε > 0` there is a closed `T_ε ⊆ T₀`
with `μ(T₀ \ T_ε) < ε` relative to which `S` is continuous; (b) the same with outer
semicontinuity; (c) `S` agrees, on a measurable `T' ⊆ T₀` of full measure, with a closed-valued `R`
whose graph over `T₀` is Borel.  When `μ(T₀) < ∞`, the sets `T_ε` can be taken compact. -/
theorem measurability_versus_continuity (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    [μ.InnerRegularCompactLTTop] {T₀ : Set E} (hT₀ : MeasurableSet T₀) {S : E → Set F}
    (hSc : ∀ t, IsClosed (S t)) :
    List.TFAE [SvNullMeasurableOn μ T₀ S,
      ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ K ⊆ T₀, IsClosed K ∧ μ (T₀ \ K) < ε ∧ SvContinuousOn S K,
      ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ K ⊆ T₀, IsClosed K ∧ μ (T₀ \ K) < ε ∧ SvOscOn S K,
      ∃ R : E → Set F, (∀ t, IsClosed (R t)) ∧ MeasurableSet (svGraph R ∩ (T₀ ×ˢ univ)) ∧
        ∃ T' ⊆ T₀, NullMeasurableSet T' μ ∧ μ (T₀ \ T') = 0 ∧ ∀ t ∈ T', R t = S t] ∧
    (μ T₀ ≠ ∞ → SvNullMeasurableOn μ T₀ S → ∀ ε : ℝ≥0∞, ε ≠ 0 →
      ∃ K ⊆ T₀, IsCompact K ∧ μ (T₀ \ K) < ε ∧ SvContinuousOn S K ∧ SvOscOn S K) := by
  have hmeas_to_cont : SvNullMeasurableOn μ T₀ S → ∀ ε : ℝ≥0∞, ε ≠ 0 →
      ∃ K ⊆ T₀, IsClosed K ∧ μ (T₀ \ K) < ε ∧ SvContinuousOn S K := by
    intro h ε hε
    obtain ⟨N, hN, hN0, hNS⟩ := h.exists_null hT₀
    obtain ⟨K, hKT, hKc, hKμ, hK⟩ := exists_isClosed_svContinuousOn μ hSc (hT₀.diff hN) hNS hε
    refine ⟨K, hKT.trans diff_subset, hKc, ?_, hK⟩
    calc μ (T₀ \ K) ≤ μ (N ∪ ((T₀ \ N) \ K)) := measure_mono fun t ⟨htT, htK⟩ ↦ by
          by_cases htN : t ∈ N
          · exact Or.inl htN
          · exact Or.inr ⟨⟨htT, htN⟩, htK⟩
      _ ≤ μ N + μ ((T₀ \ N) \ K) := measure_union_le _ _
      _ < ε := by rw [hN0, zero_add]; exact hKμ
  refine ⟨?_, ?_⟩
  · tfae_have 1 → 2 := hmeas_to_cont
    tfae_have 2 → 3 := fun h ε hε ↦ by
      obtain ⟨K, hKT, hKc, hKμ, hK⟩ := h ε hε
      exact ⟨K, hKT, hKc, hKμ, fun x hx ↦ (hK x hx).1⟩
    tfae_have 3 → 4 := by
      intro h
      choose K hKT hKc hKμ hK using fun n : ℕ ↦ h ((n : ℝ≥0∞) + 1)⁻¹ (by simp)
      classical
      set T' := ⋃ n, K n
      refine ⟨fun t ↦ if t ∈ T' then S t else ∅, fun t ↦ ?_, ?_, T',
        iUnion_subset hKT, (MeasurableSet.iUnion fun n ↦ (hKc n).measurableSet).nullMeasurableSet,
        ?_, fun t ht ↦ if_pos ht⟩
      · show IsClosed (if t ∈ T' then S t else ∅)
        split_ifs
        · exact hSc t
        · exact isClosed_empty
      · have heq : svGraph (fun t ↦ if t ∈ T' then S t else ∅) ∩ (T₀ ×ˢ univ) =
            ⋃ n, svGraph S ∩ (K n ×ˢ univ) := by
          ext ⟨t, u⟩
          simp only [mem_inter_iff, mem_svGraph, mem_prod, mem_univ, and_true, mem_iUnion]
          constructor
          · rintro ⟨hu, -⟩
            by_cases ht : t ∈ T'
            · rw [if_pos ht] at hu
              obtain ⟨n, hn⟩ := mem_iUnion.1 ht
              exact ⟨n, hu, hn⟩
            · rw [if_neg ht] at hu
              exact absurd hu (notMem_empty u)
          · rintro ⟨n, hu, hn⟩
            have ht : t ∈ T' := mem_iUnion.2 ⟨n, hn⟩
            exact ⟨by rw [if_pos ht]; exact hu, hKT n hn⟩
        rw [heq]
        exact MeasurableSet.iUnion fun n ↦ ((hK n).isClosed_svGraph_inter (hKc n)).measurableSet
      · refine le_antisymm (ge_of_tendsto' ENNReal.tendsto_inv_nat_nhds_zero fun n ↦ ?_)
          (zero_le _)
        calc μ (T₀ \ T') ≤ μ (T₀ \ K n) := measure_mono (diff_subset_diff_right
              (subset_iUnion K n))
          _ ≤ ((n : ℝ≥0∞) + 1)⁻¹ := (hKμ n).le
          _ ≤ (n : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 le_self_add
    tfae_have 4 → 1 := by
      rintro ⟨R, -, hR, T', hT'T, hT', hT'μ, hRS⟩ O hO
      have hRO := nullMeasurableSet_inter_svPreimage_of_measurableSet_svGraph μ hR hO
      refine hRO.congr ?_
      have hsub : ∀ᵐ t ∂μ, t ∈ T₀ → t ∈ T' := by
        rw [ae_iff]
        refine measure_mono_null (fun t ht ↦ ?_) hT'μ
        simp only [mem_setOf_eq, Classical.not_imp] at ht
        exact ⟨ht.1, ht.2⟩
      filter_upwards [hsub] with t ht
      simp only [eq_iff_iff]
      constructor
      · rintro ⟨htT, hRt⟩
        refine ⟨htT, ?_⟩
        have h' : (R t ∩ O).Nonempty := hRt
        rw [hRS t (ht htT)] at h'
        exact h'
      · rintro ⟨htT, hSt⟩
        refine ⟨htT, ?_⟩
        have h' : (S t ∩ O).Nonempty := hSt
        rw [← hRS t (ht htT)] at h'
        exact h'
    tfae_finish
  · intro hfin h ε hε
    obtain ⟨N, hN, hN0, hNS⟩ := h.exists_null hT₀
    obtain ⟨K, hKT, hKc, hKμ, hK⟩ := exists_isCompact_svContinuousOn μ hSc (hT₀.diff hN)
      (ne_top_of_le_ne_top hfin (measure_mono diff_subset)) hNS hε
    refine ⟨K, hKT.trans diff_subset, hKc, ?_, hK, fun x hx ↦ (hK x hx).1⟩
    calc μ (T₀ \ K) ≤ μ (N ∪ ((T₀ \ N) \ K)) := measure_mono fun t ⟨htT, htK⟩ ↦ by
          by_cases htN : t ∈ N
          · exact Or.inl htN
          · exact Or.inr ⟨⟨htT, htN⟩, htK⟩
      _ ≤ μ N + μ ((T₀ \ N) \ K) := measure_union_le _ _
      _ < ε := by rw [hN0, zero_add]; exact hKμ

end Theorem1410

end RW
