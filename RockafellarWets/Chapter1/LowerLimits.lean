/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 1B, 1D, 1E: Lower and upper limits

* **Definition 1.5**: the lower limit `liminf_{x→x̄} f(x) = sup_{δ>0} inf_{IB(x̄,δ)} f`
  (`lowerLimit`), its expressions in 1(1), the inequality 1(3) and both forms 1(2) of lower
  semicontinuity at a point.
* **Theorem 1.6**: lower semicontinuity, closedness of `epi f`, and closedness of all level sets
  `lev≤α f` are equivalent (`lowerSemicontinuous_tfae`), for real and for extended levels.
* **Lemma 1.7**: the lower limit is the least limit of `f(xν)` along sequences `xν → x̄`.
* **Exercise 1.12**: continuity is lower plus upper semicontinuity, and at a point it means that
  the lower and the upper limit agree.
* **Exercise 1.13**: closures and interiors of epigraphs and hypographs through lower and upper
  limits, with the lower closure 1(6)–1(7) as a consequence.
* **Exercise 1.15**: the cluster points of a sequence in `ℝ̄` form a closed set whose least and
  greatest elements are the lower and the upper limit, each attained along a subsequence.

The book works in `ℝⁿ`; here `E` is any (pseudo)metric space, so the closed balls `IB(x̄,δ)` of
1(1) are available.
-/

import RockafellarWets.Chapter1.Semicontinuity
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Sequences
import Mathlib.Topology.Bases
import Mathlib.Analysis.SpecificLimits.Basic

open Set Filter Topology Metric

noncomputable section

namespace RW

variable {E : Type*}

/-! ## Definition 1.5 and formula 1(4) -/

section Limits

variable [PseudoMetricSpace E]

/-- **Definition 1.5**, formula 1(1): the lower limit
`liminf_{x→x̄} f(x) = sup_{δ>0} inf_{x∈IB(x̄,δ)} f(x)`. -/
def lowerLimit (f : E → EReal) (x : E) : EReal :=
  ⨆ δ > (0 : ℝ), ⨅ y ∈ closedBall x δ, f y

/-- Formula 1(4): the upper limit `limsup_{x→x̄} f(x) = inf_{δ>0} sup_{x∈IB(x̄,δ)} f(x)`. -/
def upperLimit (f : E → EReal) (x : E) : EReal :=
  ⨅ δ > (0 : ℝ), ⨆ y ∈ closedBall x δ, f y

/-- The infimum of `f` over the closed ball `IB(x̄,δ)`. -/
def ballInf (f : E → EReal) (x : E) (δ : ℝ) : EReal := ⨅ y ∈ closedBall x δ, f y

/-- The supremum of `f` over the closed ball `IB(x̄,δ)`. -/
def ballSup (f : E → EReal) (x : E) (δ : ℝ) : EReal := ⨆ y ∈ closedBall x δ, f y

theorem lowerLimit_eq_iSup_ballInf (f : E → EReal) (x : E) :
    lowerLimit f x = ⨆ δ > (0 : ℝ), ballInf f x δ := rfl

theorem antitone_ballInf (f : E → EReal) (x : E) : Antitone (ballInf f x) :=
  fun _ _ h ↦ biInf_mono fun _ hy ↦ closedBall_subset_closedBall h hy

theorem monotone_ballSup (f : E → EReal) (x : E) : Monotone (ballSup f x) :=
  fun _ _ h ↦ biSup_mono fun _ hy ↦ closedBall_subset_closedBall h hy

/-- Formula 1(1): the lower limit is the supremum over all neighborhoods `V ∈ N(x̄)` of
`inf_V f`. -/
theorem lowerLimit_eq_iSup_nhds (f : E → EReal) (x : E) :
    lowerLimit f x = ⨆ V ∈ 𝓝 x, ⨅ y ∈ V, f y := by
  apply le_antisymm
  · exact iSup₂_le fun δ hδ ↦ le_iSup₂_of_le (closedBall x δ) (closedBall_mem_nhds x hδ) le_rfl
  · refine iSup₂_le fun V hV ↦ ?_
    obtain ⟨δ, hδ, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hV
    exact le_iSup₂_of_le δ hδ (biInf_mono fun y hy ↦ hsub hy)

/-- The lower limit of 1(1) is Mathlib's `liminf` along the neighborhood filter. -/
theorem lowerLimit_eq_liminf (f : E → EReal) (x : E) :
    lowerLimit f x = liminf f (𝓝 x) := by
  rw [lowerLimit_eq_iSup_nhds, liminf_eq_iSup_iInf]

/-- Formula 1(4): the upper limit is the infimum over all neighborhoods of `sup_V f`. -/
theorem upperLimit_eq_iInf_nhds (f : E → EReal) (x : E) :
    upperLimit f x = ⨅ V ∈ 𝓝 x, ⨆ y ∈ V, f y := by
  apply le_antisymm
  · refine le_iInf₂ fun V hV ↦ ?_
    obtain ⟨δ, hδ, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hV
    exact iInf₂_le_of_le δ hδ (biSup_mono fun y hy ↦ hsub hy)
  · exact le_iInf₂ fun δ hδ ↦ iInf₂_le_of_le (closedBall x δ) (closedBall_mem_nhds x hδ) le_rfl

theorem upperLimit_eq_limsup (f : E → EReal) (x : E) :
    upperLimit f x = limsup f (𝓝 x) := by
  rw [upperLimit_eq_iInf_nhds, limsup_eq_iInf_iSup]

/-- Formula 1(1): `liminf_{x→x̄} f(x) = lim_{δ↘0} inf_{x∈IB(x̄,δ)} f(x)`. -/
theorem tendsto_ballInf_lowerLimit (f : E → EReal) (x : E) :
    Tendsto (ballInf f x) (𝓝[>] 0) (𝓝 (lowerLimit f x)) := by
  have h := (antitone_ballInf f x).tendsto_nhdsGT 0
  convert h using 2
  rw [lowerLimit_eq_iSup_ballInf, sSup_image]
  rfl

/-- Formula 1(4): `limsup_{x→x̄} f(x) = lim_{δ↘0} sup_{x∈IB(x̄,δ)} f(x)`. -/
theorem tendsto_ballSup_upperLimit (f : E → EReal) (x : E) :
    Tendsto (ballSup f x) (𝓝[>] 0) (𝓝 (upperLimit f x)) := by
  have h := (monotone_ballSup f x).tendsto_nhdsGT 0
  convert h using 2
  rw [sInf_image]
  rfl

/-- Formula 1(3): `liminf_{x→x̄} f(x) ≤ f(x̄)`. -/
theorem lowerLimit_le (f : E → EReal) (x : E) : lowerLimit f x ≤ f x :=
  iSup₂_le fun _ hδ ↦ biInf_le f (mem_closedBall_self hδ.le)

/-- The upper counterpart of 1(3). -/
theorem le_upperLimit (f : E → EReal) (x : E) : f x ≤ upperLimit f x :=
  le_iInf₂ fun _ hδ ↦ le_biSup f (mem_closedBall_self hδ.le)

theorem lowerLimit_le_upperLimit (f : E → EReal) (x : E) : lowerLimit f x ≤ upperLimit f x :=
  (lowerLimit_le f x).trans (le_upperLimit f x)

/-- **Definition 1.5**, formula 1(2): lower semicontinuity at `x̄` means
`liminf_{x→x̄} f(x) ≥ f(x̄)`. -/
theorem lowerSemicontinuousAt_iff_le_lowerLimit {f : E → EReal} {x : E} :
    LowerSemicontinuousAt f x ↔ f x ≤ lowerLimit f x := by
  rw [lowerSemicontinuousAt_iff_le_liminf, lowerLimit_eq_liminf]

/-- **Definition 1.5**, the equivalent form in 1(2): `liminf_{x→x̄} f(x) = f(x̄)`. -/
theorem lowerSemicontinuousAt_iff_lowerLimit_eq {f : E → EReal} {x : E} :
    LowerSemicontinuousAt f x ↔ lowerLimit f x = f x := by
  rw [lowerSemicontinuousAt_iff_le_lowerLimit]
  exact ⟨fun h ↦ le_antisymm (lowerLimit_le f x) h, fun h ↦ h.ge⟩

/-- Upper semicontinuity at `x̄` means `limsup_{x→x̄} f(x) = f(x̄)`. -/
theorem upperSemicontinuousAt_iff_upperLimit_le {f : E → EReal} {x : E} :
    UpperSemicontinuousAt f x ↔ upperLimit f x ≤ f x := by
  rw [upperSemicontinuousAt_iff_limsup_le, upperLimit_eq_limsup]

theorem upperSemicontinuousAt_iff_upperLimit_eq {f : E → EReal} {x : E} :
    UpperSemicontinuousAt f x ↔ upperLimit f x = f x := by
  rw [upperSemicontinuousAt_iff_upperLimit_le]
  exact ⟨fun h ↦ le_antisymm h (le_upperLimit f x), fun h ↦ h.le⟩

/-- Lower semicontinuity on the whole space, in the form of Definition 1.5. -/
theorem lowerSemicontinuous_iff_forall_le_lowerLimit {f : E → EReal} :
    LowerSemicontinuous f ↔ ∀ x, f x ≤ lowerLimit f x :=
  forall_congr' fun _ ↦ lowerSemicontinuousAt_iff_le_lowerLimit

/-- The upper limit is the negative of the lower limit of `-f`. -/
theorem upperLimit_eq_neg_lowerLimit_neg (f : E → EReal) (x : E) :
    upperLimit f x = -lowerLimit (fun y ↦ -f y) x := by
  rw [upperLimit_eq_limsup, lowerLimit_eq_liminf]
  change _ = -liminf (-f) (𝓝 x)
  rw [EReal.liminf_neg, neg_neg]

/-! ## Lemma 1.7 -/

/-- If `xν → x̄` then `liminf_{x→x̄} f(x) ≤ liminf_ν f(xν)`. -/
theorem lowerLimit_le_liminf_comp {f : E → EReal} {x : E} {xs : ℕ → E}
    (hxs : Tendsto xs atTop (𝓝 x)) : lowerLimit f x ≤ liminf (fun n ↦ f (xs n)) atTop := by
  rw [lowerLimit_eq_liminf]
  exact liminf_le_liminf_of_le hxs

/-- Along a sequence `δν ↘ 0`, the infima over `IB(x̄,δν)` increase to the lower limit. -/
theorem tendsto_ballInf_inv_succ (f : E → EReal) (x : E) :
    Tendsto (fun n : ℕ ↦ ballInf f x (1 / ((n : ℝ) + 1))) atTop (𝓝 (lowerLimit f x)) := by
  refine (tendsto_ballInf_lowerLimit f x).comp ?_
  refine tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
  exact Eventually.of_forall fun n ↦ show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity

/-- **Lemma 1.7**: `liminf_{x→x̄} f(x) = min {α ∈ ℝ̄ | ∃ xν → x̄ with f(xν) → α}`.  The minimum
is attained. -/
theorem isLeast_lowerLimit (f : E → EReal) (x : E) :
    IsLeast {a : EReal | ∃ xs : ℕ → E, Tendsto xs atTop (𝓝 x) ∧
      Tendsto (fun n ↦ f (xs n)) atTop (𝓝 a)} (lowerLimit f x) := by
  refine ⟨?_, ?_⟩
  · rcases eq_top_or_lt_top (lowerLimit f x) with htop | hlt
    · refine ⟨fun _ ↦ x, tendsto_const_nhds, ?_⟩
      have hfx : f x = ⊤ := top_le_iff.1 (htop ▸ lowerLimit_le f x)
      rw [htop]
      simp only [hfx]
      exact tendsto_const_nhds
    · obtain ⟨b, -, hbI, hb⟩ := exists_seq_strictAnti_tendsto' hlt
      have hex : ∀ n : ℕ, ∃ y ∈ closedBall x (1 / ((n : ℝ) + 1)), f y < b n := by
        intro n
        have hle : ballInf f x (1 / ((n : ℝ) + 1)) ≤ lowerLimit f x :=
          le_iSup₂_of_le (1 / ((n : ℝ) + 1)) (by positivity) le_rfl
        have := lt_of_le_of_lt hle (hbI n).1
        simpa [ballInf, iInf_lt_iff] using this
      choose xs hxsB hxsb using hex
      refine ⟨xs, ?_, ?_⟩
      · refine tendsto_iff_dist_tendsto_zero.2 ?_
        refine squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ mem_closedBall.1 (hxsB n)) ?_
        exact tendsto_one_div_add_atTop_nhds_zero_nat
      · refine tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_ballInf_inv_succ f x) hb
          (fun n ↦ biInf_le f (hxsB n)) (fun n ↦ (hxsb n).le)
  · rintro a ⟨xs, hxs, hfa⟩
    exact (lowerLimit_le_liminf_comp hxs).trans_eq hfa.liminf_eq

/-- The upper limit formula after Lemma 1.7:
`limsup_{x→x̄} f(x) = max {α ∈ ℝ̄ | ∃ xν → x̄ with f(xν) → α}`. -/
theorem isGreatest_upperLimit (f : E → EReal) (x : E) :
    IsGreatest {a : EReal | ∃ xs : ℕ → E, Tendsto xs atTop (𝓝 x) ∧
      Tendsto (fun n ↦ f (xs n)) atTop (𝓝 a)} (upperLimit f x) := by
  have h := isLeast_lowerLimit (fun y ↦ -f y) x
  rw [upperLimit_eq_neg_lowerLimit_neg]
  refine ⟨?_, ?_⟩
  · obtain ⟨xs, hxs, hlim⟩ := h.1
    refine ⟨xs, hxs, ?_⟩
    have := (continuous_neg.tendsto _).comp hlim
    simpa [Function.comp_def] using this
  · rintro a ⟨xs, hxs, hfa⟩
    have hmem : -a ∈ {a : EReal | ∃ xs : ℕ → E, Tendsto xs atTop (𝓝 x) ∧
        Tendsto (fun n ↦ -f (xs n)) atTop (𝓝 a)} :=
      ⟨xs, hxs, (continuous_neg.tendsto _).comp hfa⟩
    exact EReal.le_neg_of_le_neg (h.2 hmem)

end Limits

/-! ## Theorem 1.6 -/

section Characterization

variable [TopologicalSpace E]

/-- Closed real level sets make every extended level set closed: `lev≤∞ f` is the whole space
and `lev≤-∞ f` is the intersection of the real level sets. -/
theorem isClosed_levelSet_ereal_of_real {f : E → EReal}
    (h : ∀ a : ℝ, IsClosed (levelSet f a)) (a : EReal) : IsClosed (levelSet f a) := by
  induction a using EReal.rec with
  | bot =>
    have : levelSet f ⊥ = ⋂ n : ℕ, levelSet f ((-(n : ℝ) : ℝ) : EReal) := by
      ext y
      simp only [levelSet, mem_setOf_eq, mem_iInter, le_bot_iff]
      constructor
      · intro hy n
        rw [hy]
        exact bot_le
      · intro hy
        by_contra hne
        obtain ⟨n, hn⟩ := exists_nat_gt (-(f y).toReal)
        rcases eq_top_or_lt_top (f y) with htop | hlt
        · have := hy 0
          rw [htop] at this
          exact absurd this (by simp)
        · have hfin : f y = ((f y).toReal : EReal) := (EReal.coe_toReal hlt.ne hne).symm
          have := hy n
          rw [hfin, EReal.coe_le_coe_iff] at this
          linarith
    rw [this]
    exact isClosed_iInter fun n ↦ h _
  | top => simp [levelSet_top]
  | coe a => exact h a

/-- **Theorem 1.6**: for `f : ℝⁿ → ℝ̄` the following are equivalent:
(a) `f` is lower semicontinuous; (b) `epi f` is closed in `ℝⁿ × ℝ`; (c) all level sets
`lev≤α f`, `α ∈ ℝ`, are closed.  A fourth equivalent form uses all `α ∈ ℝ̄`. -/
theorem lowerSemicontinuous_tfae (f : E → EReal) :
    List.TFAE [LowerSemicontinuous f, IsClosed (epigraph f),
      ∀ a : ℝ, IsClosed (levelSet f a), ∀ a : EReal, IsClosed (levelSet f a)] := by
  tfae_have 1 ↔ 2 := lsc_iff_epigraph_closed_ereal f
  tfae_have 1 → 4 := fun h a ↦ (lowerSemicontinuous_iff_isClosed_preimage.1 h) a
  tfae_have 4 → 3 := fun h a ↦ h a
  tfae_have 3 → 4 := isClosed_levelSet_ereal_of_real
  tfae_have 4 → 1 := fun h ↦ lowerSemicontinuous_iff_isClosed_preimage.2 h
  tfae_finish

/-- **Theorem 1.6**, (a) ⇔ (c) for real levels. -/
theorem lowerSemicontinuous_iff_isClosed_levelSet {f : E → EReal} :
    LowerSemicontinuous f ↔ ∀ a : ℝ, IsClosed (levelSet f a) :=
  (lowerSemicontinuous_tfae f).out 0 2

/-- The indicator `δ_C` is lsc exactly when `C` is closed (Theorem 1.6 for indicators). -/
theorem lowerSemicontinuous_indicatorVA_iff {C : Set E} :
    LowerSemicontinuous (indicatorVA C) ↔ IsClosed C := by
  rw [lowerSemicontinuous_iff_isClosed_levelSet]
  constructor
  · intro h
    have : levelSet (indicatorVA C) ((0 : ℝ) : EReal) = C := by
      ext y
      by_cases hy : y ∈ C <;> simp [levelSet, hy]
    rw [← this]
    exact h 0
  · intro hC a
    by_cases ha : (0 : ℝ) ≤ a
    · have : levelSet (indicatorVA C) a = C := by
        ext y
        by_cases hy : y ∈ C <;> simp [levelSet, hy, ha]
      rw [this]
      exact hC
    · have : levelSet (indicatorVA C) a = ∅ := by
        ext y
        by_cases hy : y ∈ C <;> simp [levelSet, hy, not_le.1 ha]
      simp [this]

/-- **Exercise 1.12**: `f : ℝⁿ → ℝ̄` is continuous iff it is both lower and upper
semicontinuous. -/
theorem continuous_iff_lowerSemicontinuous_and_upperSemicontinuous {f : E → EReal} :
    Continuous f ↔ LowerSemicontinuous f ∧ UpperSemicontinuous f := by
  rw [continuous_iff_continuousAt]
  simp only [continuousAt_iff_lower_upperSemicontinuousAt]
  exact ⟨fun h ↦ ⟨fun x ↦ (h x).1, fun x ↦ (h x).2⟩, fun h x ↦ ⟨h.1 x, h.2 x⟩⟩

end Characterization

section PointContinuity

variable [PseudoMetricSpace E]

/-- **Exercise 1.12** at a point: `lim_{x→x̄} f(x) = f(x̄)` iff
`liminf_{x→x̄} f(x) = limsup_{x→x̄} f(x)`. -/
theorem continuousAt_iff_lowerLimit_eq_upperLimit {f : E → EReal} {x : E} :
    ContinuousAt f x ↔ lowerLimit f x = upperLimit f x := by
  rw [continuousAt_iff_lower_upperSemicontinuousAt, lowerSemicontinuousAt_iff_le_lowerLimit,
    upperSemicontinuousAt_iff_upperLimit_le]
  constructor
  · rintro ⟨h1, h2⟩
    exact le_antisymm (lowerLimit_le_upperLimit f x) (h2.trans h1)
  · intro h
    exact ⟨h ▸ le_upperLimit f x, h ▸ lowerLimit_le f x⟩

end PointContinuity

/-! ## Exercise 1.13 and the lower closure 1(6)–1(7) -/

section EpigraphClosure

variable [PseudoMetricSpace E]

/-- An extended real below every `a + ε`, `ε > 0`, is below `a`. -/
theorem ereal_le_coe_of_forall_pos {b : EReal} {a : ℝ}
    (h : ∀ ε > (0 : ℝ), b ≤ ((a + ε : ℝ) : EReal)) : b ≤ a := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨c, hac, hcb⟩ := EReal.exists_between_coe_real hlt
  have hac' : a < c := EReal.coe_lt_coe_iff.1 hac
  have := h (c - a) (by linarith)
  rw [show a + (c - a) = c by ring] at this
  exact absurd this (not_le.2 hcb)

theorem lowerLimit_mono {f g : E → EReal} (h : ∀ y, f y ≤ g y) (x : E) :
    lowerLimit f x ≤ lowerLimit g x :=
  iSup₂_mono fun _ _ ↦ iInf₂_mono fun y _ ↦ h y

/-- **Exercise 1.13(a)**: `(x̄, ᾱ) ∈ cl(epi f)` iff `ᾱ ≥ liminf_{x→x̄} f(x)`. -/
theorem mem_closure_epigraph_iff {f : E → EReal} {x : E} {a : ℝ} :
    (x, a) ∈ closure (epigraph f) ↔ lowerLimit f x ≤ a := by
  rw [Metric.mem_closure_iff]
  constructor
  · intro h
    refine iSup₂_le fun δ hδ ↦ ereal_le_coe_of_forall_pos fun ε hε ↦ ?_
    obtain ⟨⟨y, c⟩, hyc, hd⟩ := h (min δ ε) (lt_min hδ hε)
    have hdy : dist x y < min δ ε := lt_of_le_of_lt (le_max_left _ _) hd
    have hdc : dist a c < min δ ε := lt_of_le_of_lt (le_max_right _ _) hd
    have hy : y ∈ closedBall x δ :=
      mem_closedBall'.2 (hdy.le.trans (min_le_left _ _))
    have hc : c ≤ a + ε := by
      have h' : |a - c| < ε := by
        have := lt_of_lt_of_le hdc (min_le_right _ _)
        rwa [Real.dist_eq] at this
      have := (abs_sub_lt_iff.1 h').2
      linarith
    exact (biInf_le f hy).trans ((mem_epigraph_iff f y c).1 hyc |>.trans
      (EReal.coe_le_coe_iff.2 hc))
  · intro h ε hε
    have hball : ballInf f x (ε / 2) < ((a + ε / 2 : ℝ) : EReal) := by
      have hle : ballInf f x (ε / 2) ≤ lowerLimit f x :=
        le_iSup₂_of_le (ε / 2) (by positivity) le_rfl
      exact lt_of_le_of_lt (hle.trans h) (EReal.coe_lt_coe_iff.2 (by linarith))
    obtain ⟨y, hy, hfy⟩ : ∃ y ∈ closedBall x (ε / 2), f y < ((a + ε / 2 : ℝ) : EReal) := by
      simpa [ballInf, iInf_lt_iff] using hball
    refine ⟨(y, a + ε / 2), (mem_epigraph_iff f y _).2 hfy.le, ?_⟩
    have h1 : dist x y ≤ ε / 2 := by rw [dist_comm]; exact mem_closedBall.1 hy
    have h2 : dist a (a + ε / 2) = ε / 2 := by
      rw [Real.dist_eq, show a - (a + ε / 2) = -(ε / 2) by ring, abs_neg,
        abs_of_pos (by positivity)]
    rw [Prod.dist_eq]
    exact lt_of_le_of_lt (max_le h1 h2.le) (by linarith)

/-- **Exercise 1.13(b)**: `(x̄, ᾱ) ∈ int(epi f)` iff `ᾱ > limsup_{x→x̄} f(x)`. -/
theorem mem_interior_epigraph_iff {f : E → EReal} {x : E} {a : ℝ} :
    (x, a) ∈ interior (epigraph f) ↔ upperLimit f x < a := by
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  constructor
  · rintro ⟨ε, hε, hsub⟩
    have hbound : ballSup f x (ε / 2) ≤ ((a - ε / 2 : ℝ) : EReal) := by
      refine iSup₂_le fun y hy ↦ ?_
      have hmem : (y, a - ε / 2) ∈ ball (x, a) ε := by
        rw [← ball_prod_same]
        refine ⟨?_, ?_⟩
        · exact mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hy) (by linarith))
        · rw [mem_ball, Real.dist_eq, show a - ε / 2 - a = -(ε / 2) by ring, abs_neg,
            abs_of_pos (by positivity)]
          linarith
      exact (mem_epigraph_iff f y _).1 (hsub hmem)
    exact lt_of_le_of_lt (iInf₂_le_of_le (ε / 2) (by positivity) hbound)
      (EReal.coe_lt_coe_iff.2 (by linarith))
  · intro h
    obtain ⟨δ, hδ, hlt⟩ : ∃ δ > (0 : ℝ), ballSup f x δ < a := by
      simpa [upperLimit, ballSup, iInf_lt_iff] using h
    obtain ⟨c, hsc, hca⟩ := EReal.exists_between_coe_real hlt
    have hca' : c < a := EReal.coe_lt_coe_iff.1 hca
    refine ⟨min δ (a - c), lt_min hδ (by linarith), ?_⟩
    rintro ⟨y, b⟩ hyb
    rw [← ball_prod_same] at hyb
    obtain ⟨hy, hb⟩ := hyb
    have hy' : y ∈ closedBall x δ :=
      mem_closedBall.2 ((mem_ball.1 hy).le.trans (min_le_left _ _))
    have hb' : c < b := by
      have h' : |b - a| < a - c := by
        have := lt_of_lt_of_le (mem_ball.1 hb) (min_le_right _ _)
        rwa [Real.dist_eq] at this
      have := (abs_sub_lt_iff.1 h').2
      linarith
    exact (mem_epigraph_iff f y b).2 ((le_biSup f hy').trans
      (hsc.le.trans (EReal.coe_le_coe_iff.2 hb'.le)))

/-- Reflection of the second coordinate. -/
def flipHeight (E : Type*) [TopologicalSpace E] : E × ℝ ≃ₜ E × ℝ :=
  (Homeomorph.refl E).prodCongr (Homeomorph.neg ℝ)

theorem hypograph_eq_preimage_epigraph_neg (f : E → EReal) :
    hypograph f = flipHeight E ⁻¹' epigraph (fun y ↦ -f y) := by
  ext ⟨y, b⟩
  change (b : EReal) ≤ f y ↔ -f y ≤ ((-b : ℝ) : EReal)
  rw [EReal.coe_neg, EReal.neg_le_neg_iff]

/-- The hypograph form of 1.13(a): `(x̄, ᾱ) ∈ cl(hypo f)` iff `ᾱ ≤ limsup_{x→x̄} f(x)`. -/
theorem mem_closure_hypograph_iff {f : E → EReal} {x : E} {a : ℝ} :
    (x, a) ∈ closure (hypograph f) ↔ (a : EReal) ≤ upperLimit f x := by
  rw [hypograph_eq_preimage_epigraph_neg, ← (flipHeight E).preimage_closure, mem_preimage]
  change (x, -a) ∈ closure _ ↔ _
  rw [mem_closure_epigraph_iff, upperLimit_eq_neg_lowerLimit_neg, EReal.coe_neg,
    EReal.le_neg]

/-- The hypograph form of 1.13(b): `(x̄, ᾱ) ∈ int(hypo f)` iff `ᾱ < liminf_{x→x̄} f(x)`. -/
theorem mem_interior_hypograph_iff {f : E → EReal} {x : E} {a : ℝ} :
    (x, a) ∈ interior (hypograph f) ↔ (a : EReal) < lowerLimit f x := by
  rw [hypograph_eq_preimage_epigraph_neg, ← (flipHeight E).preimage_interior, mem_preimage]
  change (x, -a) ∈ interior _ ↔ _
  rw [mem_interior_epigraph_iff, EReal.coe_neg]
  have h : upperLimit (fun y ↦ -f y) x = -lowerLimit f x := by
    rw [upperLimit_eq_neg_lowerLimit_neg]
    simp
  rw [h, EReal.neg_lt_neg_iff]

/-- **Exercise 1.13(c)**: `(x̄, ᾱ) ∉ cl(epi f)` iff `(x̄, ᾱ) ∈ int(hypo f)`. -/
theorem not_mem_closure_epigraph_iff {f : E → EReal} {x : E} {a : ℝ} :
    (x, a) ∉ closure (epigraph f) ↔ (x, a) ∈ interior (hypograph f) := by
  rw [mem_closure_epigraph_iff, mem_interior_hypograph_iff, not_le]

/-- **Exercise 1.13(d)**: `(x̄, ᾱ) ∉ int(epi f)` iff `(x̄, ᾱ) ∈ cl(hypo f)`. -/
theorem not_mem_interior_epigraph_iff {f : E → EReal} {x : E} {a : ℝ} :
    (x, a) ∉ interior (epigraph f) ↔ (x, a) ∈ closure (hypograph f) := by
  rw [mem_interior_epigraph_iff, mem_closure_hypograph_iff, not_lt]

/-- Formulas 1(6)–1(7): the lower closure `cl f`, given by `(cl f)(x) = liminf_{x'→x} f(x')`,
has `epi (cl f) = cl (epi f)`. -/
theorem epigraph_lowerLimit (f : E → EReal) : epigraph (lowerLimit f) = closure (epigraph f) := by
  ext ⟨x, a⟩
  rw [mem_epigraph_iff, mem_closure_epigraph_iff]

/-- The lower closure is lower semicontinuous. -/
theorem lowerSemicontinuous_lowerLimit (f : E → EReal) : LowerSemicontinuous (lowerLimit f) :=
  (lsc_iff_epigraph_closed_ereal _).2 (by rw [epigraph_lowerLimit]; exact isClosed_closure)

/-- The lower closure is the greatest lsc function below `f`. -/
theorem le_lowerLimit_of_lowerSemicontinuous {f g : E → EReal} (hg : LowerSemicontinuous g)
    (hgf : ∀ y, g y ≤ f y) (x : E) : g x ≤ lowerLimit f x :=
  (lowerSemicontinuousAt_iff_le_lowerLimit.1 (hg x)).trans (lowerLimit_mono hgf x)

end EpigraphClosure

/-! ## Exercise 1.15 -/

section Sequences

variable {u : ℕ → EReal} {a : EReal}

/-- The lower limit of a sequence in `ℝ̄` is one of its cluster points. -/
theorem mapClusterPt_liminf (u : ℕ → EReal) : MapClusterPt (liminf u atTop) atTop u := by
  rw [mapClusterPt_iff_frequently]
  intro s hs
  induction hL : liminf u atTop using EReal.rec with
  | bot =>
    rw [hL] at hs
    obtain ⟨y, hy⟩ := EReal.mem_nhds_bot_iff.1 hs
    have : liminf u atTop < (y : EReal) := hL ▸ EReal.bot_lt_coe y
    exact (frequently_lt_of_liminf_lt (by isBoundedDefault) this).mono fun n hn ↦ hy hn
  | top =>
    rw [hL] at hs
    obtain ⟨y, hy⟩ := EReal.mem_nhds_top_iff.1 hs
    have : (y : EReal) < liminf u atTop := hL ▸ EReal.coe_lt_top y
    exact (eventually_lt_of_lt_liminf this (by isBoundedDefault)).frequently.mono
      fun n hn ↦ hy hn
  | coe r =>
    rw [hL, EReal.nhds_coe, mem_map] at hs
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hs
    have hlo : ((r - ε : ℝ) : EReal) < liminf u atTop := by
      rw [hL]; exact EReal.coe_lt_coe_iff.2 (by linarith)
    have hhi : liminf u atTop < ((r + ε : ℝ) : EReal) := by
      rw [hL]; exact EReal.coe_lt_coe_iff.2 (by linarith)
    have h1 := eventually_lt_of_lt_liminf hlo (by isBoundedDefault)
    have h2 := frequently_lt_of_liminf_lt (by isBoundedDefault) hhi
    refine (h2.and_eventually h1).mono fun n ⟨hn2, hn1⟩ ↦ ?_
    have hne_top : u n ≠ ⊤ := ne_top_of_lt hn2
    have hne_bot : u n ≠ ⊥ := ne_bot_of_gt hn1
    have hfin : u n = ((u n).toReal : EReal) := (EReal.coe_toReal hne_top hne_bot).symm
    rw [hfin] at hn1 hn2 ⊢
    have hlo' := EReal.coe_lt_coe_iff.1 hn1
    have hhi' := EReal.coe_lt_coe_iff.1 hn2
    exact hball (by rw [mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)

/-- **Exercise 1.15**: some subsequence converges to the lower limit. -/
theorem exists_subseq_tendsto_liminf (u : ℕ → EReal) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 (liminf u atTop)) :=
  TopologicalSpace.FirstCountableTopology.tendsto_subseq (mapClusterPt_liminf u)

/-- **Exercise 1.15**: some subsequence converges to the upper limit. -/
theorem exists_subseq_tendsto_limsup (u : ℕ → EReal) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 (limsup u atTop)) := by
  obtain ⟨φ, hφ, hlim⟩ := exists_subseq_tendsto_liminf (fun n ↦ -u n)
  refine ⟨φ, hφ, ?_⟩
  have h := (continuous_neg.tendsto _).comp hlim
  have hl : liminf (fun n ↦ -u n) atTop = -limsup u atTop := EReal.liminf_neg
  rw [hl, neg_neg] at h
  simpa [Function.comp_def] using h

/-- The upper limit of a sequence in `ℝ̄` is one of its cluster points. -/
theorem mapClusterPt_limsup (u : ℕ → EReal) : MapClusterPt (limsup u atTop) atTop u := by
  obtain ⟨φ, hφ, hlim⟩ := exists_subseq_tendsto_limsup u
  exact MapClusterPt.of_comp hφ.tendsto_atTop hlim.mapClusterPt

theorem liminf_le_of_mapClusterPt (h : MapClusterPt a atTop u) : liminf u atTop ≤ a := by
  obtain ⟨φ, hφ, hlim⟩ := TopologicalSpace.FirstCountableTopology.tendsto_subseq h
  calc liminf u atTop ≤ liminf (u ∘ φ) atTop := liminf_le_liminf_of_le hφ.tendsto_atTop
    _ = a := hlim.liminf_eq

theorem le_limsup_of_mapClusterPt (h : MapClusterPt a atTop u) : a ≤ limsup u atTop := by
  obtain ⟨φ, hφ, hlim⟩ := TopologicalSpace.FirstCountableTopology.tendsto_subseq h
  calc a = limsup (u ∘ φ) atTop := hlim.limsup_eq.symm
    _ ≤ limsup u atTop := limsup_le_limsup_of_le hφ.tendsto_atTop

/-- **Exercise 1.15**: the cluster points of a sequence in `ℝ̄` form a closed set. -/
theorem isClosed_setOf_mapClusterPt (u : ℕ → EReal) :
    IsClosed {a : EReal | MapClusterPt a atTop u} :=
  isClosed_setOf_clusterPt

/-- **Exercise 1.15**: the lowest cluster point is `liminf_ν αν`. -/
theorem isLeast_liminf_mapClusterPt (u : ℕ → EReal) :
    IsLeast {a : EReal | MapClusterPt a atTop u} (liminf u atTop) :=
  ⟨mapClusterPt_liminf u, fun _ h ↦ liminf_le_of_mapClusterPt h⟩

/-- **Exercise 1.15**: the highest cluster point is `limsup_ν αν`. -/
theorem isGreatest_limsup_mapClusterPt (u : ℕ → EReal) :
    IsGreatest {a : EReal | MapClusterPt a atTop u} (limsup u atTop) :=
  ⟨mapClusterPt_limsup u, fun _ h ↦ le_limsup_of_mapClusterPt h⟩

end Sequences

end RW
