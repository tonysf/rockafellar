/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 14: Measurable mappings

Definition 14.1, Proposition 14.2 and Theorem 14.3 of Rockafellar–Wets.

Throughout, `(T, A)` is an arbitrary measurable space, written `[MeasurableSpace T]`, and a
set-valued mapping `S : T ⇉ F` is a function `S : T → Set F`.  The inverse image
`S⁻¹(D) = {t | S(t) ∩ D ≠ ∅}` is `svPreimage S D` from Chapter 5.

The book works in `ℝⁿ`.  Theorem 14.3 is proved here for closed-valued mappings into any proper
metric space `F` (closed balls are compact), and the "rational" balls of the book, with centers
in `ℚⁿ` and rational radii, are balls whose centers range over an arbitrary countable dense
family `D : ι → F` and whose radii are positive rationals; `ℚⁿ ⊂ ℝⁿ` is one such family.
The distance function of 14.3(j) is the extended distance `infEDist x (S t) ∈ [0, ∞]`, which is
`∞` when `S t = ∅`, matching the book's convention `d(x, ∅) = ∞`.
-/

import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Order.Archimedean
import RockafellarWets.Chapter5.SemicontinuityCriteria

open Set Filter Topology Metric
open scoped ENNReal NNReal Pointwise

noncomputable section

namespace RW

section Definition141

variable {T F : Type*} [MeasurableSpace T] [TopologicalSpace F]

/-- **Definition 14.1 (measurable mappings).**  A set-valued mapping `S : T ⇉ F` is measurable
if `S⁻¹(O) = {t | S(t) ∩ O ≠ ∅}` is a measurable subset of `T` for every open `O ⊂ F`. -/
def SvMeasurable (S : T → Set F) : Prop :=
  ∀ O : Set F, IsOpen O → MeasurableSet (svPreimage S O)

theorem SvMeasurable.measurableSet_svPreimage {S : T → Set F} (hS : SvMeasurable S)
    {O : Set F} (hO : IsOpen O) : MeasurableSet (svPreimage S O) :=
  hS O hO

/-- **Definition 14.1**: the domain `dom S = S⁻¹(F)` of a measurable mapping is measurable. -/
theorem SvMeasurable.measurableSet_svDom {S : T → Set F} (hS : SvMeasurable S) :
    MeasurableSet (svDom S) := by
  rw [← svPreimage_univ]
  exact hS univ isOpen_univ

omit [MeasurableSpace T] [TopologicalSpace F] in
theorem svPreimage_singleton_map (x : T → F) (O : Set F) :
    svPreimage (fun t ↦ ({x t} : Set F)) O = x ⁻¹' O := by
  ext t
  simp [svPreimage]

/-- **Definition 14.1**: for single-valued mappings the definition reduces to ordinary
measurability (with respect to the Borel field). -/
theorem svMeasurable_singleton_iff [MeasurableSpace F] [BorelSpace F] {x : T → F} :
    SvMeasurable (fun t ↦ ({x t} : Set F)) ↔ Measurable x := by
  constructor
  · intro h
    exact measurable_of_isOpen fun O hO ↦ by
      rw [← svPreimage_singleton_map]
      exact h O hO
  · intro h O hO
    rw [svPreimage_singleton_map]
    exact h hO.measurableSet

/-- Constant mappings `S(t) ≡ D` are measurable. -/
theorem svMeasurable_const (D : Set F) : SvMeasurable (fun _ : T ↦ D) :=
  fun _ _ ↦ MeasurableSet.const _

/-- Step mappings: `S(t) ≡ D_j` on the cells `T_j = idx⁻¹(j)` of a countable measurable
partition of `T`. -/
theorem svMeasurable_step {ι : Type*} [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {idx : T → ι} (hidx : Measurable idx) (D : ι → Set F) :
    SvMeasurable (fun t ↦ D (idx t)) := by
  intro O _
  have : svPreimage (fun t ↦ D (idx t)) O = idx ⁻¹' {j | (D j ∩ O).Nonempty} := rfl
  rw [this]
  exact hidx (Set.to_countable _).measurableSet

/-- Translates `S(t) = D + a(t)` of a fixed set by a measurable vector are measurable. -/
theorem svMeasurable_add_const_image [AddGroup F] [ContinuousAdd F] [MeasurableSpace F]
    [OpensMeasurableSpace F] (D : Set F) {a : T → F} (ha : Measurable a) :
    SvMeasurable (fun t ↦ (fun d ↦ d + a t) '' D) := by
  intro O hO
  have hopen : IsOpen (⋃ d ∈ D, (fun y ↦ d + y) ⁻¹' O) :=
    isOpen_biUnion fun d _ ↦ hO.preimage (continuous_const.add continuous_id)
  have : svPreimage (fun t ↦ (fun d ↦ d + a t) '' D) O = a ⁻¹' ⋃ d ∈ D, (fun y ↦ d + y) ⁻¹' O := by
    ext t
    simp only [mem_svPreimage, mem_preimage, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨_, ⟨d, hd, rfl⟩, hO'⟩
      exact ⟨d, hd, hO'⟩
    · rintro ⟨d, hd, hO'⟩
      exact ⟨_, ⟨d, hd, rfl⟩, hO'⟩
  rw [this]
  exact ha hopen.measurableSet

/-- Scalar multiples `S(t) = λ(t) D` of a fixed set by a measurable scalar are measurable. -/
theorem svMeasurable_smul_const [AddCommMonoid F] [Module ℝ F] [ContinuousSMul ℝ F] (D : Set F)
    {lam : T → ℝ} (hlam : Measurable lam) : SvMeasurable (fun t ↦ lam t • D) := by
  intro O hO
  have hopen : IsOpen (⋃ d ∈ D, (fun τ : ℝ ↦ τ • d) ⁻¹' O) :=
    isOpen_biUnion fun d _ ↦ hO.preimage (continuous_id.smul continuous_const)
  have : svPreimage (fun t ↦ lam t • D) O = lam ⁻¹' ⋃ d ∈ D, (fun τ : ℝ ↦ τ • d) ⁻¹' O := by
    ext t
    simp only [mem_svPreimage, mem_preimage, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨_, ⟨d, hd, rfl⟩, hO'⟩
      exact ⟨d, hd, hO'⟩
    · rintro ⟨d, hd, hO'⟩
      exact ⟨_, ⟨d, hd, rfl⟩, hO'⟩
  rw [this]
  exact hlam hopen.measurableSet

end Definition141

section Proposition142

variable {T F : Type*} [MeasurableSpace T] [TopologicalSpace F]

omit [MeasurableSpace T] in
theorem svPreimage_closure_of_isOpen (S : T → Set F) {O : Set F} (hO : IsOpen O) :
    svPreimage (fun t ↦ closure (S t)) O = svPreimage S O := by
  ext t
  exact closure_inter_open_nonempty_iff hO

/-- **Proposition 14.2 (preservation with closure of images).** -/
theorem SvMeasurable.closure {S : T → Set F} (hS : SvMeasurable S) :
    SvMeasurable (fun t ↦ closure (S t)) := by
  intro O hO
  rw [svPreimage_closure_of_isOpen S hO]
  exact hS O hO

/-- Proposition 14.2, with the (trivial) converse. -/
theorem svMeasurable_closure_iff {S : T → Set F} :
    SvMeasurable (fun t ↦ closure (S t)) ↔ SvMeasurable S := by
  refine ⟨fun h O hO ↦ ?_, SvMeasurable.closure⟩
  rw [← svPreimage_closure_of_isOpen S hO]
  exact h O hO

end Proposition142

section RationalBalls

variable {F : Type*} [PseudoMetricSpace F]

/-- In a metric space with a dense family `D`, every point of an open set lies in a closed ball
with center in `D` and positive rational radius contained in the open set; the same ball's
interior also contains the point. -/
theorem exists_rat_ball_subset {ι : Type*} {D : ι → F} (hD : DenseRange D) {O : Set F}
    (hO : IsOpen O) {x : F} (hx : x ∈ O) :
    ∃ i : ι, ∃ q : ℚ, 0 < q ∧ x ∈ ball (D i) q ∧ closedBall (D i) q ⊆ O := by
  obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.1 hO x hx
  obtain ⟨q, hq0, hq⟩ := exists_rat_btwn (half_pos hε)
  have hq0' : (0 : ℝ) < q := hq0
  obtain ⟨i, hi⟩ := hD.exists_dist_lt x hq0'
  refine ⟨i, q, by exact_mod_cast hq0', ?_, ?_⟩
  · rw [mem_ball]
    exact hi
  · intro y hy
    apply hεO
    rw [Metric.mem_ball]
    have h1 : dist y (D i) ≤ q := hy
    have h2 : dist (D i) x < q := by rwa [dist_comm]
    calc dist y x ≤ dist y (D i) + dist (D i) x := dist_triangle _ _ _
      _ < q + q := by linarith
      _ < ε := by linarith

end RationalBalls

section Theorem143

variable {T F : Type*} [MeasurableSpace T] [MetricSpace F]

omit [MeasurableSpace T] in
/-- `S⁻¹(O)` of an open set is the countable union of the `S⁻¹(B)` over the closed rational balls
`B ⊂ O`. -/
theorem svPreimage_eq_iUnion_rat_closedBall {ι : Type*} {D : ι → F} (hD : DenseRange D)
    (S : T → Set F) {O : Set F} (hO : IsOpen O) :
    svPreimage S O = ⋃ p : ι × ℚ, ⋃ (_ : 0 < p.2 ∧ closedBall (D p.1) p.2 ⊆ O),
      svPreimage S (closedBall (D p.1) p.2) := by
  ext t
  simp only [mem_iUnion, exists_prop, Prod.exists]
  constructor
  · rintro ⟨s, hsS, hsO⟩
    obtain ⟨i, q, hq, hsball, hsub⟩ := exists_rat_ball_subset hD hO hsO
    exact ⟨i, q, ⟨hq, hsub⟩, s, hsS, ball_subset_closedBall hsball⟩
  · rintro ⟨i, q, ⟨_, hsub⟩, s, hsS, hsB⟩
    exact ⟨s, hsS, hsub hsB⟩

omit [MeasurableSpace T] in
/-- `S⁻¹(O)` of an open set is the countable union of the `S⁻¹(B)` over the open rational balls
`B ⊂ O`. -/
theorem svPreimage_eq_iUnion_rat_ball {ι : Type*} {D : ι → F} (hD : DenseRange D)
    (S : T → Set F) {O : Set F} (hO : IsOpen O) :
    svPreimage S O = ⋃ p : ι × ℚ, ⋃ (_ : 0 < p.2 ∧ ball (D p.1) p.2 ⊆ O),
      svPreimage S (ball (D p.1) p.2) := by
  ext t
  simp only [mem_iUnion, exists_prop, Prod.exists]
  constructor
  · rintro ⟨s, hsS, hsO⟩
    obtain ⟨i, q, hq, hsball, hsub⟩ := exists_rat_ball_subset hD hO hsO
    exact ⟨i, q, ⟨hq, ball_subset_closedBall.trans hsub⟩, s, hsS, hsball⟩
  · rintro ⟨i, q, ⟨_, hsub⟩, s, hsS, hsB⟩
    exact ⟨s, hsS, hsub hsB⟩

omit [MeasurableSpace T] [MetricSpace F] in
theorem setOf_subset_eq_compl_svPreimage (S : T → Set F) (D : Set F) :
    {t | S t ⊆ D} = (svPreimage S Dᶜ)ᶜ := by
  ext t
  simp only [mem_setOf_eq, mem_compl_iff, mem_svPreimage, not_nonempty_iff_eq_empty]
  constructor
  · intro h
    ext s
    simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and,
      not_not]
    exact fun hs ↦ h hs
  · intro h s hs
    by_contra hsD
    have : s ∈ S t ∩ Dᶜ := ⟨hs, hsD⟩
    rw [h] at this
    exact this

omit [MeasurableSpace T] in
/-- The extended distance `d(x, S(t))` is below `r` exactly when `S(t)` meets the open
`r`-ball around `x`. -/
theorem setOf_infEDist_lt_eq_svPreimage (S : T → Set F) (x : F) (r : ℝ≥0∞) :
    {t | infEDist x (S t) < r} = svPreimage S (eball x r) := by
  ext t
  simp only [mem_setOf_eq, mem_svPreimage, infEDist_lt_iff]
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact ⟨y, hy, by rw [mem_eball, edist_comm]; exact hxy⟩
  · rintro ⟨y, hy, hxy⟩
    rw [mem_eball, edist_comm] at hxy
    exact ⟨y, hy, hxy⟩

/-- Open-ball inverse images with positive radii suffice for measurability in a separable
space. -/
theorem svMeasurable_of_measurableSet_svPreimage_ball [TopologicalSpace.SeparableSpace F]
    {S : T → Set F} (h : ∀ (x : F) (r : ℝ), 0 < r → MeasurableSet (svPreimage S (ball x r))) :
    SvMeasurable S := by
  intro O hO
  rcases isEmpty_or_nonempty F with hF | hF
  · have : svPreimage S O = ∅ := by
      ext t
      simp only [mem_svPreimage, mem_empty_iff_false, iff_false]
      rintro ⟨s, -⟩
      exact hF.elim s
    rw [this]
    exact MeasurableSet.empty
  rw [svPreimage_eq_iUnion_rat_ball (TopologicalSpace.denseRange_denseSeq F) S hO]
  exact MeasurableSet.iUnion fun p ↦ MeasurableSet.iUnion fun hp ↦
    h _ _ (by exact_mod_cast hp.1)

/-- Closed-ball inverse images with positive radii suffice for measurability in a separable
space. -/
theorem svMeasurable_of_measurableSet_svPreimage_closedBall [TopologicalSpace.SeparableSpace F]
    {S : T → Set F}
    (h : ∀ (x : F) (r : ℝ), 0 < r → MeasurableSet (svPreimage S (closedBall x r))) :
    SvMeasurable S := by
  intro O hO
  rcases isEmpty_or_nonempty F with hF | hF
  · have : svPreimage S O = ∅ := by
      ext t
      simp only [mem_svPreimage, mem_empty_iff_false, iff_false]
      rintro ⟨s, -⟩
      exact hF.elim s
    rw [this]
    exact MeasurableSet.empty
  rw [svPreimage_eq_iUnion_rat_closedBall (TopologicalSpace.denseRange_denseSeq F) S hO]
  exact MeasurableSet.iUnion fun p ↦ MeasurableSet.iUnion fun hp ↦
    h _ _ (by exact_mod_cast hp.1)

/-- **Theorem 14.3**, (c) ⇒ (a) without closedness: compact inverse images suffice in a proper
space. -/
theorem svMeasurable_of_measurableSet_svPreimage_isCompact [ProperSpace F] {S : T → Set F}
    (h : ∀ K : Set F, IsCompact K → MeasurableSet (svPreimage S K)) : SvMeasurable S :=
  svMeasurable_of_measurableSet_svPreimage_closedBall fun x r _ ↦ h _ (isCompact_closedBall x r)

/-- **Theorem 14.3**, (a) ⇒ (c): for closed-valued `S`, inverse images of compact sets are
measurable. -/
theorem SvMeasurable.measurableSet_svPreimage_of_isCompact {S : T → Set F} (hS : SvMeasurable S)
    (hSc : ∀ t, IsClosed (S t)) {K : Set F} (hK : IsCompact K) :
    MeasurableSet (svPreimage S K) := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · have : svPreimage S (∅ : Set F) = ∅ := by ext t; simp [svPreimage]
    rw [this]
    exact MeasurableSet.empty
  have key : svPreimage S K = ⋂ n : ℕ, svPreimage S (thickening (1 / ((n : ℝ) + 1)) K) := by
    ext t
    simp only [mem_iInter]
    constructor
    · intro ht n
      exact svPreimage_mono (self_subset_thickening (by positivity) K) ht
    · intro ht
      obtain ⟨s₀, hs₀, -⟩ := ht 0
      have hSne : (S t).Nonempty := ⟨s₀, hs₀⟩
      obtain ⟨k₀, hk₀K, hk₀min⟩ := hK.exists_isMinOn hKne
        (continuous_infDist_pt (S t)).continuousOn
      have hzero : infDist k₀ (S t) = 0 := by
        refine le_antisymm ?_ infDist_nonneg
        by_contra hpos
        push_neg at hpos
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
        obtain ⟨s, hsS, hsth⟩ := ht n
        obtain ⟨k, hkK, hsk⟩ := mem_thickening_iff.1 hsth
        have h1 : infDist k₀ (S t) ≤ infDist k (S t) := hk₀min hkK
        have h2 : infDist k (S t) ≤ dist k s := infDist_le_dist_of_mem hsS
        rw [dist_comm] at hsk
        linarith
      have hk₀S : k₀ ∈ S t := by
        rw [← (hSc t).closure_eq, mem_closure_iff_infDist_zero hSne]
        exact hzero
      exact ⟨k₀, hk₀S, hk₀K⟩
  rw [key]
  exact MeasurableSet.iInter fun n ↦ hS _ isOpen_thickening

/-- **Theorem 14.3**, (c) ⇒ (b): closed sets are countable unions of compact sets. -/
theorem measurableSet_svPreimage_isClosed_of_isCompact [ProperSpace F] {S : T → Set F}
    (h : ∀ K : Set F, IsCompact K → MeasurableSet (svPreimage S K)) {C : Set F}
    (hC : IsClosed C) : MeasurableSet (svPreimage S C) := by
  rcases isEmpty_or_nonempty F with hF | ⟨⟨x₀⟩⟩
  · have : svPreimage S C = ∅ := by
      ext t
      simp only [mem_svPreimage, mem_empty_iff_false, iff_false]
      rintro ⟨s, -⟩
      exact hF.elim s
    rw [this]
    exact MeasurableSet.empty
  have key : svPreimage S C = ⋃ n : ℕ, svPreimage S (C ∩ closedBall x₀ n) := by
    ext t
    simp only [mem_iUnion]
    constructor
    · rintro ⟨s, hsS, hsC⟩
      obtain ⟨n, hn⟩ := exists_nat_ge (dist s x₀)
      exact ⟨n, s, hsS, hsC, hn⟩
    · rintro ⟨n, hn⟩
      exact svPreimage_mono inter_subset_left hn
  rw [key]
  exact MeasurableSet.iUnion fun n ↦ h _ ((isCompact_closedBall x₀ n).inter_left hC)

/-- **Theorem 14.3**, (a) ⇒ (b) for closed-valued mappings into a proper space. -/
theorem SvMeasurable.measurableSet_svPreimage_of_isClosed [ProperSpace F] {S : T → Set F}
    (hS : SvMeasurable S) (hSc : ∀ t, IsClosed (S t)) {C : Set F} (hC : IsClosed C) :
    MeasurableSet (svPreimage S C) :=
  measurableSet_svPreimage_isClosed_of_isCompact
    (fun _ hK ↦ hS.measurableSet_svPreimage_of_isCompact hSc hK) hC

/-- **Theorem 14.3**, (a) ⇒ (j): `t ↦ d(x, S(t))` is measurable; this needs no closedness. -/
theorem SvMeasurable.measurable_infEDist {S : T → Set F} (hS : SvMeasurable S) (x : F) :
    Measurable fun t ↦ infEDist x (S t) := by
  refine measurable_of_Iio fun r ↦ ?_
  change MeasurableSet {t | infEDist x (S t) < r}
  rw [setOf_infEDist_lt_eq_svPreimage]
  exact hS _ isOpen_eball

/-- **Theorem 14.3**, (j) ⇒ (f): measurability of the distance functions gives measurable
inverse images of open balls, without closedness. -/
theorem measurableSet_svPreimage_ball_of_measurable_infEDist {S : T → Set F}
    (h : ∀ x : F, Measurable fun t ↦ infEDist x (S t)) (x : F) (r : ℝ) :
    MeasurableSet (svPreimage S (ball x r)) := by
  rw [← Metric.eball_ofReal, ← setOf_infEDist_lt_eq_svPreimage]
  exact h x measurableSet_Iio

/-- **Theorem 14.3**, (j) ⇒ (a) in a separable space, without closedness. -/
theorem svMeasurable_of_measurable_infEDist [TopologicalSpace.SeparableSpace F] {S : T → Set F}
    (h : ∀ x : F, Measurable fun t ↦ infEDist x (S t)) : SvMeasurable S :=
  svMeasurable_of_measurableSet_svPreimage_ball fun x r _ ↦
    measurableSet_svPreimage_ball_of_measurable_infEDist h x r

/-- **Theorem 14.3 (measurability equivalences under closed-valuedness).**  For a closed-valued
mapping `S : T ⇉ F` into a proper metric space, and any countable dense family `D : ι → F`
(standing in for `ℚⁿ`), each of the following is equivalent to measurability of `S`:
(a) open inverse images; (b) closed; (c) compact; (d) closed balls; (e) closed rational balls;
(f) open balls; (g) open rational balls; (h) `{t | S t ⊆ O}` for open `O`;
(i) `{t | S t ⊆ C}` for closed `C`; (j) measurability of `t ↦ d(x, S t)` for every `x`. -/
theorem measurability_equivalences [ProperSpace F] {ι : Type*} [Countable ι] {D : ι → F}
    (hD : DenseRange D) {S : T → Set F} (hSc : ∀ t, IsClosed (S t)) :
    List.TFAE
      [SvMeasurable S,
        ∀ C : Set F, IsClosed C → MeasurableSet (svPreimage S C),
        ∀ K : Set F, IsCompact K → MeasurableSet (svPreimage S K),
        ∀ (x : F) (r : ℝ), 0 < r → MeasurableSet (svPreimage S (closedBall x r)),
        ∀ (i : ι) (q : ℚ), 0 < q → MeasurableSet (svPreimage S (closedBall (D i) q)),
        ∀ (x : F) (r : ℝ), 0 < r → MeasurableSet (svPreimage S (ball x r)),
        ∀ (i : ι) (q : ℚ), 0 < q → MeasurableSet (svPreimage S (ball (D i) q)),
        ∀ O : Set F, IsOpen O → MeasurableSet {t | S t ⊆ O},
        ∀ C : Set F, IsClosed C → MeasurableSet {t | S t ⊆ C},
        ∀ x : F, Measurable fun t ↦ infEDist x (S t)] := by
  tfae_have 1 → 3 := fun h K hK ↦ h.measurableSet_svPreimage_of_isCompact hSc hK
  tfae_have 3 → 4 := fun h x r _ ↦ h _ (isCompact_closedBall x r)
  tfae_have 4 → 5 := fun h i q hq ↦ h _ _ (by exact_mod_cast hq)
  tfae_have 5 → 1 := by
    intro h O hO
    rw [svPreimage_eq_iUnion_rat_closedBall hD S hO]
    exact MeasurableSet.iUnion fun p ↦ MeasurableSet.iUnion fun hp ↦ h _ _ hp.1
  tfae_have 3 → 2 := fun h C hC ↦ measurableSet_svPreimage_isClosed_of_isCompact h hC
  tfae_have 2 → 3 := fun h K hK ↦ h K hK.isClosed
  tfae_have 1 → 6 := fun h x r _ ↦ h _ isOpen_ball
  tfae_have 6 → 7 := fun h i q hq ↦ h _ _ (by exact_mod_cast hq)
  tfae_have 7 → 1 := by
    intro h O hO
    rw [svPreimage_eq_iUnion_rat_ball hD S hO]
    exact MeasurableSet.iUnion fun p ↦ MeasurableSet.iUnion fun hp ↦ h _ _ hp.1
  tfae_have 2 → 8 := by
    intro h O hO
    rw [setOf_subset_eq_compl_svPreimage]
    exact (h _ hO.isClosed_compl).compl
  tfae_have 8 → 2 := by
    intro h C hC
    have := (h _ hC.isOpen_compl).compl
    rwa [setOf_subset_eq_compl_svPreimage, compl_compl, compl_compl] at this
  tfae_have 1 → 9 := by
    intro h C hC
    rw [setOf_subset_eq_compl_svPreimage]
    exact (h _ hC.isOpen_compl).compl
  tfae_have 9 → 1 := by
    intro h O hO
    have := (h _ hO.isClosed_compl).compl
    rwa [setOf_subset_eq_compl_svPreimage, compl_compl, compl_compl] at this
  tfae_have 1 → 10 := fun h x ↦ h.measurable_infEDist x
  tfae_have 10 → 6 := fun h x r _ ↦ measurableSet_svPreimage_ball_of_measurable_infEDist h x r
  tfae_finish

/-- The book's rational points `ℚⁿ ⊂ ℝⁿ` form a countable dense family in
`EuclideanSpace ℝ (Fin n)`, so Theorem 14.3 applies with the book's rational balls by taking
`D` to be this family in `measurability_equivalences`. -/
theorem denseRange_ratPoints (n : ℕ) :
    DenseRange (fun q : Fin n → ℚ ↦ WithLp.toLp 2 (fun i ↦ (q i : ℝ))) := by
  have h1 : DenseRange (fun q : Fin n → ℚ ↦ fun i ↦ (q i : ℝ)) :=
    DenseRange.piMap fun _ ↦ Rat.denseRange_cast
  exact (WithLp.toLp_surjective 2).denseRange.comp h1 (PiLp.continuous_toLp 2 _)

end Theorem143

end RW
