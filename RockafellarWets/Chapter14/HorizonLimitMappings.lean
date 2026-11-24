/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 14: Horizon limits of measurable mappings and of normal integrands

Exercise 14.21(b) and Exercise 14.54(b) of Rockafellar–Wets.  With the rational scalings
`E_k(C) = ⋃_{0 < q < 1/(k+1)} q C` (`horizonRatScaling`), the horizon limits of Chapter 4 have the
countable descriptions
* `lim sup^∞ Cν = {0} ∪ ⋂ₖ cl ⋃_{ν ≥ k} E_k(Cν)`,
* `lim inf^∞ Cν = {0} ∪ ⋂ₖ cl ⋃_N ⋂_{ν ≥ N} (E_k(Cν) + (k+1)⁻¹𝔹)`,
from which measurability follows as for the ordinary limits in 14.20 (the guide's "similar
constructions").  For integrands, the horizon epi-limits of Definition 7.49 have the horizon
limits of the epigraphs as epigraphs (Chapter 7), except that the epigraph is empty when the
epigraphs `epi fν(t, ·)` are eventually (resp. frequently) empty.
-/

import RockafellarWets.Chapter14.HorizonMappings
import RockafellarWets.Chapter4.HorizonLimitSubsequences
import RockafellarWets.Chapter7.HorizonScaleSelections
import RockafellarWets.Chapter7.HorizonEpiLimits

open Set Filter Topology Metric
open scoped ENNReal NNReal Pointwise

noncomputable section

namespace RW

section Formulas

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Rational positive scalings `⋃_{0 < q < 1/(k+1)} q C`. -/
def horizonRatScaling (k : ℕ) (C : Set E) : Set E :=
  ⋃ q : ℚ, ⋃ (_ : 0 < q ∧ (q : ℝ) < 1 / ((k : ℝ) + 1)), (q : ℝ) • C

theorem mem_horizonRatScaling {k : ℕ} {C : Set E} {x : E} :
    x ∈ horizonRatScaling k C ↔
      ∃ q : ℚ, 0 < q ∧ (q : ℝ) < 1 / ((k : ℝ) + 1) ∧ ∃ y ∈ C, (q : ℝ) • y = x := by
  simp only [horizonRatScaling, mem_iUnion, exists_prop, Set.mem_smul_set]
  constructor
  · rintro ⟨q, ⟨hq0, hq1⟩, y, hy, rfl⟩
    exact ⟨q, hq0, hq1, y, hy, rfl⟩
  · rintro ⟨q, hq0, hq1, y, hy, rfl⟩
    exact ⟨q, ⟨hq0, hq1⟩, y, hy, rfl⟩

/-- Rational approximation of a positive scaling factor. -/
theorem exists_rat_smul_near {s : ℝ} (hs : 0 < s) (z : E) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℚ, 0 < q ∧ (q : ℝ) < s ∧ dist ((q : ℝ) • z) (s • z) < ε := by
  set δ := min (s / 2) (ε / (‖z‖ + 1)) with hδ
  have hδ0 : 0 < δ := lt_min (half_pos hs) (div_pos hε (by positivity))
  have hδs : δ ≤ s / 2 := min_le_left _ _
  have hδε : δ ≤ ε / (‖z‖ + 1) := min_le_right _ _
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show s - δ < s by linarith)
  refine ⟨q, ?_, hq2, ?_⟩
  · exact_mod_cast (show (0 : ℝ) < q by linarith)
  · rw [dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs, abs_of_neg (by linarith)]
    have h1 : 0 ≤ -((q : ℝ) - s) := by linarith
    calc -((q : ℝ) - s) * ‖z‖ ≤ δ * ‖z‖ := by gcongr; linarith
      _ ≤ ε / (‖z‖ + 1) * ‖z‖ := by gcongr
      _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg z]

/-- The outer horizon limit through rational scalings. -/
theorem horizonOuterSetLimit_eq_insert_iInter (C : ℕ → Set E) :
    horizonOuterSetLimit C =
      insert 0 (⋂ k : ℕ, _root_.closure (⋃ n ≥ k, horizonRatScaling k (C n))) := by
  ext w
  rw [mem_horizonOuterSetLimit_iff_zero_or_scaling, mem_insert_iff]
  refine or_congr_right ⟨?_, ?_⟩
  · rintro ⟨φ, z, s, hφ, hz, hs, hs0, hst⟩
    have hq : ∀ m : ℕ, ∃ q : ℚ, 0 < q ∧ (q : ℝ) < s m ∧
        dist ((q : ℝ) • z m) (s m • z m) < 1 / ((m : ℝ) + 1) :=
      fun m ↦ exists_rat_smul_near (hs m) (z m) (by positivity)
    choose q hq0 hqs hqd using hq
    have hd : Tendsto (fun m ↦ dist (s m • z m) ((q m : ℝ) • z m)) atTop (𝓝 0) :=
      squeeze_zero (fun _ ↦ dist_nonneg) (fun m ↦ by rw [dist_comm]; exact (hqd m).le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    have hqt : Tendsto (fun m ↦ (q m : ℝ) • z m) atTop (𝓝 w) := hst.congr_dist hd
    refine mem_iInter.2 fun k ↦ mem_closure_of_tendsto hqt ?_
    have h1 : ∀ᶠ m in atTop, k ≤ φ m := hφ.tendsto_atTop.eventually_ge_atTop k
    have h2 : ∀ᶠ m in atTop, s m < 1 / ((k : ℝ) + 1) :=
      hs0.eventually (Iio_mem_nhds (by positivity))
    filter_upwards [h1, h2] with m hm1 hm2
    exact mem_iUnion₂.2 ⟨φ m, hm1, mem_horizonRatScaling.2
      ⟨q m, hq0 m, (hqs m).trans hm2, z m, hz m, rfl⟩⟩
  · intro hw
    have hk : ∀ k : ℕ, ∃ n, k ≤ n ∧ ∃ q : ℚ, 0 < q ∧ (q : ℝ) < 1 / ((k : ℝ) + 1) ∧
        ∃ y ∈ C n, dist w ((q : ℝ) • y) < 1 / ((k : ℝ) + 1) := by
      intro k
      obtain ⟨p, hp, hpw⟩ := Metric.mem_closure_iff.1 (mem_iInter.1 hw k) _
        (by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1))
      obtain ⟨n, hn, hpn⟩ := mem_iUnion₂.1 hp
      obtain ⟨q, hq0, hq1, y, hy, rfl⟩ := mem_horizonRatScaling.1 hpn
      exact ⟨n, hn, q, hq0, hq1, y, hy, hpw⟩
    choose n hnk q hq0 hq1 y hy hd using hk
    obtain ⟨ψ, hψs⟩ : ∃ ψ : ℕ → ℕ, ∀ j, ψ (j + 1) = n (ψ j) + ψ j + 1 :=
      ⟨fun j ↦ Nat.rec 0 (fun _ a ↦ n a + a + 1) j, fun _ ↦ rfl⟩
    have hψ : StrictMono ψ := strictMono_nat_of_lt_succ fun j ↦ by rw [hψs]; omega
    have hφ : StrictMono fun j ↦ n (ψ j) := strictMono_nat_of_lt_succ fun j ↦ by
      have := hnk (ψ (j + 1))
      rw [hψs] at this ⊢
      omega
    have hψt := hψ.tendsto_atTop
    have hinv : Tendsto (fun j ↦ 1 / ((ψ j : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hψt
    refine ⟨fun j ↦ n (ψ j), fun j ↦ y (ψ j), fun j ↦ (q (ψ j) : ℝ), hφ, fun j ↦ hy (ψ j),
      fun j ↦ Rat.cast_pos.2 (hq0 (ψ j)), ?_, ?_⟩
    · exact squeeze_zero (fun j ↦ by exact_mod_cast (hq0 (ψ j)).le) (fun j ↦ (hq1 (ψ j)).le)
        hinv
    · rw [tendsto_iff_dist_tendsto_zero]
      exact squeeze_zero (fun _ ↦ dist_nonneg)
        (fun j ↦ by rw [dist_comm]; exact (hd (ψ j)).le) hinv

/-- The inner horizon limit through rational scalings. -/
theorem horizonInnerSetLimit_eq_insert_iInter (C : ℕ → Set E) :
    horizonInnerSetLimit C = insert 0 (⋂ k : ℕ, _root_.closure (⋃ N : ℕ, ⋂ n ≥ N,
      cthickening (1 / ((k : ℝ) + 1)) (horizonRatScaling k (C n)))) := by
  ext w
  rw [mem_insert_iff]
  by_cases hw0 : w = 0
  · subst hw0
    simp only [true_or, iff_true]
    exact (isCone_horizonInnerSetLimit C).1
  simp only [hw0, false_or]
  rw [horizonInnerSetLimit_eq_iInter_subsequence_outer]
  simp only [mem_iInter]
  constructor
  · intro hw k
    refine subset_closure (mem_iUnion.2 ?_)
    by_contra hnot
    push_neg at hnot
    have hfreq : ∃ᶠ n in atTop,
        w ∉ cthickening (1 / ((k : ℝ) + 1)) (horizonRatScaling k (C n)) := by
      rw [frequently_atTop]
      intro N
      obtain ⟨n, hn⟩ : ∃ n, ¬ (N ≤ n → w ∈ cthickening (1 / ((k : ℝ) + 1))
          (horizonRatScaling k (C n))) := by
        have := hnot N
        simpa only [mem_iInter, not_forall] using this
      exact ⟨n, (Classical.not_imp.1 hn).1, (Classical.not_imp.1 hn).2⟩
    obtain ⟨φ, hφ, hφw⟩ := extraction_of_frequently_atTop hfreq
    have hwφ := hw φ hφ
    rw [mem_horizonOuterSetLimit_iff_zero_or_scaling] at hwφ
    rcases hwφ with hw0' | ⟨ψ, z, s, _, hz, hs, hs0, hst⟩
    · exact hw0 hw0'
    have hk0 : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have h1 : ∀ᶠ m in atTop, s m < 1 / ((k : ℝ) + 1) := hs0.eventually (Iio_mem_nhds hk0)
    have h2 : ∀ᶠ m in atTop, dist (s m • z m) w < 1 / ((k : ℝ) + 1) / 2 :=
      (tendsto_iff_dist_tendsto_zero.1 hst).eventually (Iio_mem_nhds (by positivity))
    obtain ⟨m, hm1, hm2⟩ := (h1.and h2).exists
    obtain ⟨q, hq0, hqs, hqd⟩ := exists_rat_smul_near (hs m) (z m)
      (by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1) / 2)
    apply hφw (ψ m)
    refine thickening_subset_cthickening _ _ (mem_thickening_iff.2 ⟨(q : ℝ) • z m,
      mem_horizonRatScaling.2 ⟨q, hq0, hqs.trans hm1, z m, hz m, rfl⟩, ?_⟩)
    calc dist w ((q : ℝ) • z m) ≤ dist w (s m • z m) + dist (s m • z m) ((q : ℝ) • z m) :=
          dist_triangle _ _ _
      _ < 1 / ((k : ℝ) + 1) / 2 + 1 / ((k : ℝ) + 1) / 2 :=
          add_lt_add (by rw [dist_comm]; exact hm2) (by rw [dist_comm]; exact hqd)
      _ = 1 / ((k : ℝ) + 1) := by ring
  · intro hw φ hφ
    have hk : ∀ k : ℕ, ∃ N, ∀ n ≥ N, ∃ q : ℚ, 0 < q ∧ (q : ℝ) < 1 / ((k : ℝ) + 1) ∧
        ∃ y ∈ C n, dist w ((q : ℝ) • y) < 3 / ((k : ℝ) + 1) := by
      intro k
      have hk0 : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      obtain ⟨w', hw', hww'⟩ := Metric.mem_closure_iff.1 (hw k) _ hk0
      obtain ⟨N, hN⟩ := mem_iUnion.1 hw'
      refine ⟨N, fun n hn ↦ ?_⟩
      have hc : w' ∈ cthickening (1 / ((k : ℝ) + 1)) (horizonRatScaling k (C n)) :=
        mem_iInter₂.1 hN n hn
      have ht := cthickening_subset_thickening' (by positivity : (0 : ℝ) < 2 / ((k : ℝ) + 1))
        (by rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num) _ hc
      obtain ⟨p, hp, hpw⟩ := mem_thickening_iff.1 ht
      obtain ⟨q, hq0, hq1, y, hy, rfl⟩ := mem_horizonRatScaling.1 hp
      refine ⟨q, hq0, hq1, y, hy, ?_⟩
      calc dist w ((q : ℝ) • y) ≤ dist w w' + dist w' ((q : ℝ) • y) := dist_triangle _ _ _
        _ < 1 / ((k : ℝ) + 1) + 2 / ((k : ℝ) + 1) := add_lt_add hww' hpw
        _ = 3 / ((k : ℝ) + 1) := by ring
    choose N hN using hk
    obtain ⟨ψ, hψ, hψN⟩ := extraction_forall_of_eventually
      (P := fun k m ↦ N k ≤ φ m) fun k ↦ hφ.tendsto_atTop.eventually_ge_atTop (N k)
    have hsel : ∀ k : ℕ, ∃ q : ℚ, 0 < q ∧ (q : ℝ) < 1 / ((k : ℝ) + 1) ∧
        ∃ y ∈ C (φ (ψ k)), dist w ((q : ℝ) • y) < 3 / ((k : ℝ) + 1) :=
      fun k ↦ hN k (φ (ψ k)) (hψN k)
    choose q hq0 hq1 y hy hd using hsel
    rw [mem_horizonOuterSetLimit_iff_zero_or_scaling]
    refine Or.inr ⟨ψ, y, fun k ↦ (q k : ℝ), hψ, hy, fun k ↦ Rat.cast_pos.2 (hq0 k), ?_, ?_⟩
    · exact squeeze_zero (fun k ↦ by exact_mod_cast (hq0 k).le) (fun k ↦ (hq1 k).le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    · rw [tendsto_iff_dist_tendsto_zero]
      have h3 : Tendsto (fun k : ℕ ↦ 3 / ((k : ℝ) + 1)) atTop (𝓝 0) := by
        have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (3 : ℝ)
        simpa [mul_one_div] using this
      exact squeeze_zero (fun _ ↦ dist_nonneg)
        (fun k ↦ by rw [dist_comm]; exact (hd k).le) h3

end Formulas

section Exercise1421b

variable {T E : Type*} [MeasurableSpace T] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem SvMeasurable.horizonRatScaling {S : T → Set E} (hS : SvMeasurable S) (k : ℕ) :
    SvMeasurable fun t ↦ RW.horizonRatScaling k (S t) := by
  refine SvMeasurable.iUnion fun q ↦ ?_
  by_cases hq : 0 < q ∧ (q : ℝ) < 1 / ((k : ℝ) + 1)
  · have : (fun t ↦ ⋃ (_ : 0 < q ∧ (q : ℝ) < 1 / ((k : ℝ) + 1)), (q : ℝ) • S t) =
        fun t ↦ (q : ℝ) • S t := funext fun t ↦ iSup_pos hq
    rw [this]
    exact hS.image (continuous_const_smul (q : ℝ))
  · have : (fun t ↦ ⋃ (_ : 0 < q ∧ (q : ℝ) < 1 / ((k : ℝ) + 1)), (q : ℝ) • S t) =
        fun _ ↦ ∅ := funext fun t ↦ iSup_neg hq
    rw [this]
    exact svMeasurable_const ∅

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem SvMeasurable.iUnion_of_prop {p : Prop} {S : T → Set E} (h : SvMeasurable S) :
    SvMeasurable fun t ↦ ⋃ (_ : p), S t := by
  by_cases hp : p
  · have : (fun t ↦ ⋃ (_ : p), S t) = S := funext fun t ↦ iSup_pos hp
    rw [this]
    exact h
  · have : (fun t ↦ ⋃ (_ : p), S t) = fun _ ↦ ∅ := funext fun t ↦ iSup_neg hp
    rw [this]
    exact svMeasurable_const ∅

/-- **Exercise 14.21(b)**, outer horizon limit. -/
theorem SvMeasurable.horizonOuterSetLimit {S : ℕ → T → Set E} (h : ∀ n, SvMeasurable (S n)) :
    SvMeasurable fun t ↦ RW.horizonOuterSetLimit fun n ↦ S n t := by
  have hk : ∀ k : ℕ, SvMeasurable fun t ↦ ⋃ n : ℕ, ⋃ (_ : n ≥ k),
      RW.horizonRatScaling k (S n t) := fun k ↦
    SvMeasurable.iUnion fun n ↦ SvMeasurable.iUnion_of_prop ((h n).horizonRatScaling k)
  have hI : SvMeasurable fun t ↦ ⋂ k : ℕ, _root_.closure (⋃ n : ℕ, ⋃ (_ : n ≥ k),
      RW.horizonRatScaling k (S n t)) :=
    SvMeasurable.iInter (fun k ↦ (hk k).closure) (fun _ _ ↦ isClosed_closure)
  have hU : SvMeasurable fun t ↦ {(0 : E)} ∪ ⋂ k : ℕ, _root_.closure (⋃ n : ℕ, ⋃ (_ : n ≥ k),
      RW.horizonRatScaling k (S n t)) := (svMeasurable_const _).union hI
  have heq : (fun t ↦ RW.horizonOuterSetLimit fun n ↦ S n t) = fun t ↦ {(0 : E)} ∪
      ⋂ k : ℕ, _root_.closure (⋃ n : ℕ, ⋃ (_ : n ≥ k), RW.horizonRatScaling k (S n t)) :=
    funext fun t ↦ by rw [horizonOuterSetLimit_eq_insert_iInter, insert_eq]
  rw [heq]
  exact hU

/-- **Exercise 14.21(b)**, inner horizon limit. -/
theorem SvMeasurable.horizonInnerSetLimit {S : ℕ → T → Set E} (h : ∀ n, SvMeasurable (S n)) :
    SvMeasurable fun t ↦ RW.horizonInnerSetLimit fun n ↦ S n t := by
  have hN : ∀ k N : ℕ, SvMeasurable fun t ↦ ⋂ n : ℕ, ⋂ (_ : n ≥ N),
      Metric.cthickening (1 / ((k : ℝ) + 1)) (RW.horizonRatScaling k (S n t)) := by
    intro k N
    refine SvMeasurable.iInter (fun n ↦ ?_) (fun n t ↦ ?_)
    · by_cases hn : n ≥ N
      · have : (fun t ↦ ⋂ (_ : n ≥ N), Metric.cthickening (1 / ((k : ℝ) + 1))
            (RW.horizonRatScaling k (S n t))) = fun t ↦ Metric.cthickening (1 / ((k : ℝ) + 1))
              (RW.horizonRatScaling k (S n t)) := funext fun t ↦ iInf_pos hn
        rw [this]
        exact ((h n).horizonRatScaling k).cthickening _
      · have : (fun t ↦ ⋂ (_ : n ≥ N), Metric.cthickening (1 / ((k : ℝ) + 1))
            (RW.horizonRatScaling k (S n t))) = fun _ ↦ univ := funext fun t ↦ iInf_neg hn
        rw [this]
        exact svMeasurable_const univ
    · exact isClosed_iInter fun _ ↦ Metric.isClosed_cthickening
  have hI : SvMeasurable fun t ↦ ⋂ k : ℕ, _root_.closure (⋃ N : ℕ, ⋂ n : ℕ, ⋂ (_ : n ≥ N),
      Metric.cthickening (1 / ((k : ℝ) + 1)) (RW.horizonRatScaling k (S n t))) :=
    SvMeasurable.iInter (fun k ↦ (SvMeasurable.iUnion fun N ↦ hN k N).closure)
      (fun _ _ ↦ isClosed_closure)
  have hU : SvMeasurable fun t ↦ {(0 : E)} ∪ ⋂ k : ℕ, _root_.closure (⋃ N : ℕ, ⋂ n : ℕ,
      ⋂ (_ : n ≥ N), Metric.cthickening (1 / ((k : ℝ) + 1)) (RW.horizonRatScaling k (S n t))) :=
    (svMeasurable_const _).union hI
  have heq : (fun t ↦ RW.horizonInnerSetLimit fun n ↦ S n t) = fun t ↦ {(0 : E)} ∪
      ⋂ k : ℕ, _root_.closure (⋃ N : ℕ, ⋂ n : ℕ, ⋂ (_ : n ≥ N),
        Metric.cthickening (1 / ((k : ℝ) + 1)) (RW.horizonRatScaling k (S n t))) :=
    funext fun t ↦ by rw [horizonInnerSetLimit_eq_insert_iInter, insert_eq]
  rw [heq]
  exact hU

/-- **Exercise 14.21 (horizon cones and limits)**, part (b): for any sequence of measurable
mappings `Sν : T ⇉ E`, the horizon limit mappings `t ↦ lim inf^∞ Sν(t)`, `t ↦ lim sup^∞ Sν(t)`,
and `t ↦ lim^∞ Sν(t)` when it exists, are closed-valued and measurable. -/
theorem horizon_limit_mappings {S : ℕ → T → Set E} (h : ∀ n, SvMeasurable (S n)) :
    ((∀ t, IsClosed (RW.horizonInnerSetLimit fun n ↦ S n t)) ∧
      SvMeasurable fun t ↦ RW.horizonInnerSetLimit fun n ↦ S n t) ∧
    ((∀ t, IsClosed (RW.horizonOuterSetLimit fun n ↦ S n t)) ∧
      SvMeasurable fun t ↦ RW.horizonOuterSetLimit fun n ↦ S n t) ∧
    ∀ L : T → Set E, (∀ t, HorizonConverges (fun n ↦ S n t) (L t)) →
      (∀ t, IsClosed (L t)) ∧ SvMeasurable L := by
  refine ⟨⟨fun t ↦ isClosed_horizonInnerSetLimit _, SvMeasurable.horizonInnerSetLimit h⟩,
    ⟨fun t ↦ isClosed_horizonOuterSetLimit _, SvMeasurable.horizonOuterSetLimit h⟩,
    fun L hL ↦ ?_⟩
  have heq : L = fun t ↦ RW.horizonInnerSetLimit fun n ↦ S n t :=
    funext fun t ↦ (hL t).1.symm
  rw [heq]
  exact ⟨fun t ↦ isClosed_horizonInnerSetLimit _, SvMeasurable.horizonInnerSetLimit h⟩

end Exercise1421b

section Exercise1454b

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem epigraph_lowerHorizonEpiLimit_eq_ite (f : ℕ → E → EReal) [Decidable
    (∃ᶠ n in atTop, (epigraph (f n)).Nonempty)] :
    epigraph (lowerHorizonEpiLimit f) =
      if ∃ᶠ n in atTop, (epigraph (f n)).Nonempty then
        RW.horizonOuterSetLimit fun n ↦ epigraph (f n)
      else ∅ := by
  split_ifs with hf
  · exact epigraph_lowerHorizonEpiLimit hf
  · refine eq_empty_iff_forall_notMem.2 fun w hw ↦ hf ?_
    change (((0 : ℝ), w.1), w.2) ∈
      epigraph (epiLowerLimit fun n ↦ positiveScalePerspective (f n)) at hw
    rw [epigraph_epiLowerLimit] at hw
    refine (hw univ univ_mem).mono fun n hn ↦ ?_
    obtain ⟨⟨⟨s, x⟩, a⟩, hp, -⟩ := hn
    exact ⟨_, (mem_epigraph_positiveScalePerspective.1 hp).2⟩

theorem epigraph_upperHorizonEpiLimit_eq_ite (f : ℕ → E → EReal) [Decidable
    (∀ᶠ n in atTop, (epigraph (f n)).Nonempty)] :
    epigraph (upperHorizonEpiLimit f) =
      if ∀ᶠ n in atTop, (epigraph (f n)).Nonempty then
        RW.horizonInnerSetLimit fun n ↦ epigraph (f n)
      else ∅ := by
  split_ifs with hf
  · exact epigraph_upperHorizonEpiLimit hf
  · refine eq_empty_iff_forall_notMem.2 fun w hw ↦ hf ?_
    change (((0 : ℝ), w.1), w.2) ∈
      epigraph (epiUpperLimit fun n ↦ positiveScalePerspective (f n)) at hw
    rw [epigraph_epiUpperLimit] at hw
    refine (hw univ univ_mem).mono fun n hn ↦ ?_
    obtain ⟨⟨⟨s, x⟩, a⟩, hp, -⟩ := hn
    exact ⟨_, (mem_epigraph_positiveScalePerspective.1 hp).2⟩

variable {T : Type*} [MeasurableSpace T] [FiniteDimensional ℝ E]

open scoped Classical in
/-- **Exercise 14.54(b)**, lower horizon epi-limit: `h(t, ·) = e-lim inf^∞ fν(t, ·)` is a normal
integrand. -/
theorem IsNormalIntegrand.lowerHorizonEpiLimit {f : ℕ → T → E → EReal}
    (hf : ∀ n, IsNormalIntegrand (f n)) :
    IsNormalIntegrand fun t ↦ RW.lowerHorizonEpiLimit fun n ↦ f n t := by
  set A : Set T := {t | ∃ᶠ n in atTop, (epigraph (f n t)).Nonempty}
  have hA : MeasurableSet A := by
    have : A = ⋂ N : ℕ, ⋃ n : ℕ, ⋃ (_ : N ≤ n), svDom (epiMapping (f n)) := by
      ext t
      simp only [A, mem_setOf_eq, frequently_atTop, mem_iInter, mem_iUnion, exists_prop]
      rfl
    rw [this]
    exact MeasurableSet.iInter fun N ↦ MeasurableSet.iUnion fun n ↦ MeasurableSet.iUnion
      fun _ ↦ (hf n).2.measurableSet_svDom
  have hepi : ∀ t, epigraph (RW.lowerHorizonEpiLimit fun n ↦ f n t) =
      if t ∈ A then RW.horizonOuterSetLimit (fun n ↦ epiMapping (f n) t) else ∅ := by
    intro t
    rw [epigraph_lowerHorizonEpiLimit_eq_ite]
    rfl
  refine ⟨fun t ↦ ?_, ?_⟩
  · rw [hepi t]
    split_ifs
    · exact isClosed_horizonOuterSetLimit _
    · exact isClosed_empty
  · rw [show epiMapping (fun t ↦ RW.lowerHorizonEpiLimit fun n ↦ f n t) = _ from funext hepi]
    exact SvMeasurable.ite hA (SvMeasurable.horizonOuterSetLimit fun n ↦ (hf n).2)
      (svMeasurable_const ∅)

open scoped Classical in
/-- **Exercise 14.54(b)**, upper horizon epi-limit: `h(t, ·) = e-lim sup^∞ fν(t, ·)` is a normal
integrand. -/
theorem IsNormalIntegrand.upperHorizonEpiLimit {f : ℕ → T → E → EReal}
    (hf : ∀ n, IsNormalIntegrand (f n)) :
    IsNormalIntegrand fun t ↦ RW.upperHorizonEpiLimit fun n ↦ f n t := by
  set A : Set T := {t | ∀ᶠ n in atTop, (epigraph (f n t)).Nonempty}
  have hA : MeasurableSet A := by
    have : A = ⋃ N : ℕ, ⋂ n : ℕ, ⋂ (_ : N ≤ n), svDom (epiMapping (f n)) := by
      ext t
      simp only [A, mem_setOf_eq, eventually_atTop, mem_iInter, mem_iUnion]
      rfl
    rw [this]
    exact MeasurableSet.iUnion fun N ↦ MeasurableSet.iInter fun n ↦ MeasurableSet.iInter
      fun _ ↦ (hf n).2.measurableSet_svDom
  have hepi : ∀ t, epigraph (RW.upperHorizonEpiLimit fun n ↦ f n t) =
      if t ∈ A then RW.horizonInnerSetLimit (fun n ↦ epiMapping (f n) t) else ∅ := by
    intro t
    rw [epigraph_upperHorizonEpiLimit_eq_ite]
    rfl
  refine ⟨fun t ↦ ?_, ?_⟩
  · rw [hepi t]
    split_ifs
    · exact isClosed_horizonInnerSetLimit _
    · exact isClosed_empty
  · rw [show epiMapping (fun t ↦ RW.upperHorizonEpiLimit fun n ↦ f n t) = _ from funext hepi]
    exact SvMeasurable.ite hA (SvMeasurable.horizonInnerSetLimit fun n ↦ (hf n).2)
      (svMeasurable_const ∅)

/-- **Exercise 14.54 (horizon integrands and horizon limits)**, part (b): for normal integrands
`fν`, the lower and upper horizon epi-limits are normal integrands, and so is the horizon
epi-limit `e-lim^∞ fν(t, ·)` when it exists for all `t`. -/
theorem horizon_epi_limits_of_normal_integrands {f : ℕ → T → E → EReal}
    (hf : ∀ n, IsNormalIntegrand (f n)) :
    IsNormalIntegrand (fun t ↦ RW.lowerHorizonEpiLimit fun n ↦ f n t) ∧
      IsNormalIntegrand (fun t ↦ RW.upperHorizonEpiLimit fun n ↦ f n t) ∧
      ∀ h : T → E → EReal, (∀ t, HorizonEpiConverges (fun n ↦ f n t) (h t)) →
        IsNormalIntegrand h := by
  refine ⟨IsNormalIntegrand.lowerHorizonEpiLimit hf, IsNormalIntegrand.upperHorizonEpiLimit hf,
    fun h hh ↦ ?_⟩
  have heq : h = fun t ↦ RW.lowerHorizonEpiLimit fun n ↦ f n t :=
    funext fun t ↦ (hh t).1.symm
  rw [heq]
  exact IsNormalIntegrand.lowerHorizonEpiLimit hf

end Exercise1454b

end RW
