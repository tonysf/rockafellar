/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 1C–D and 1I: Attainment of a minimum

* **Definition 1.8**: level boundedness (`IsLevelBounded`) means `f(x) → ∞` as `|x| → ∞`
  (`isLevelBounded_iff_tendsto_cobounded`, `isLevelBounded_iff_tendsto_norm`).
* **Theorem 1.9**: a proper, lsc, level-bounded `f` has finite `inf f` and a nonempty compact
  `argmin f`, together with the weaker-hypothesis remark after Corollary 1.10.
* **Corollary 1.10**: a proper lsc `f` is bounded below on bounded sets and attains its minimum on
  every compact set meeting `dom f`.
* **Example 1.11**: minimizing a continuous `f₀` over a nonempty closed `C` with bounded sets
  `{x ∈ C | f₀(x) ≤ α}`.
* **Exercise 1.14**: growth properties, with the lower and upper limits at infinity of 1(8).
* **Theorem 1.42**: minimizing sequences.

The book's `ℝⁿ` is a finite-dimensional real normed space `E`.
-/

import RockafellarWets.Chapter1.LowerLimits
import RockafellarWets.Chapter3.Coercivity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Normed.Group.Bounded

open Set Filter Topology Metric Bornology

noncomputable section

namespace RW

variable {E : Type*}

/-! ## Definition 1.8 -/

section LevelBounded

variable [PseudoMetricSpace E]

/-- **Definition 1.8**: `f` is level-bounded iff `f(x) → ∞` as `x` escapes every bounded set. -/
theorem isLevelBounded_iff_tendsto_cobounded {f : E → EReal} :
    IsLevelBounded f ↔ Tendsto f (cobounded E) (𝓝 ⊤) := by
  rw [EReal.tendsto_nhds_top_iff_real]
  refine forall_congr' fun a ↦ ?_
  rw [isBounded_def]
  have : (levelSet f a)ᶜ = {x | (a : EReal) < f x} := by ext x; simp [levelSet]
  rw [this]
  rfl

end LevelBounded

/-- **Definition 1.8**: level boundedness corresponds to having `f(x) → ∞` as `|x| → ∞`. -/
theorem isLevelBounded_iff_tendsto_norm [SeminormedAddCommGroup E] {f : E → EReal} :
    IsLevelBounded f ↔ Tendsto f (comap norm atTop) (𝓝 ⊤) := by
  rw [comap_norm_atTop, isLevelBounded_iff_tendsto_cobounded]

/-! ## Theorem 1.9 and Corollary 1.10 -/

/-- The minimum value of a proper function attaining its infimum is finite. -/
theorem exists_coe_eq_iInf_of_eq_iInf {f : E → EReal} (hp : IsProper f) {x : E}
    (hx : f x = ⨅ y, f y) : ∃ a : ℝ, (⨅ y, f y) = a := by
  have htop : f x ≠ ⊤ := by
    obtain ⟨y, hy⟩ := hp.1
    exact ne_top_of_le_ne_top hy.ne (hx ▸ iInf_le f y)
  exact ⟨(f x).toReal, hx ▸ (EReal.coe_toReal htop (hp.2 x).ne').symm⟩

/-- **Corollary 1.10** (lower bounds), second part: a proper lsc `f` attains a (finite) minimum
relative to any compact set that meets `dom f`. -/
theorem lower_bounds_compact [TopologicalSpace E] {f : E → EReal} (hlsc : LowerSemicontinuous f)
    (hp : IsProper f) {K : Set E} (hK : IsCompact K) (hKd : (K ∩ effectiveDomain f).Nonempty) :
    ∃ x ∈ K, IsMinOn f K x ∧ ∃ a : ℝ, f x = a := by
  obtain ⟨y, hyK, hyd⟩ := hKd
  obtain ⟨x, hxK, hmin⟩ := (hlsc.lowerSemicontinuousOn K).exists_isMinOn ⟨y, hyK⟩ hK
  have htop : f x ≠ ⊤ := ne_top_of_le_ne_top (show f y < ⊤ from hyd).ne (hmin hyK)
  exact ⟨x, hxK, hmin, (f x).toReal, (EReal.coe_toReal htop (hp.2 x).ne').symm⟩

section Attainment

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Theorem 1.9** (attainment of a minimum): if `f` is lower semicontinuous, level-bounded and
proper, then `inf f` is finite and `argmin f` is nonempty and compact. -/
theorem attainment_of_minimum {f : E → EReal} (hlsc : LowerSemicontinuous f)
    (hlb : IsLevelBounded f) (hp : IsProper f) :
    (∃ a : ℝ, (⨅ x, f x) = a) ∧ (argmin f).Nonempty ∧ IsCompact (argmin f) := by
  have hic := isInfCompact_of_isLevelBounded_of_lsc hlsc hlb
  obtain ⟨x, hx⟩ := exists_eq_iInf_of_isInfCompact_of_lsc_of_isProper hic hlsc hp
  exact ⟨exists_coe_eq_iInf_of_eq_iInf hp hx,
    argmin_nonempty_of_isInfCompact_of_lsc_of_isProper hic hlsc hp,
    isCompact_argmin_of_isInfCompact_of_lsc_of_isProper hic hlsc hp⟩

/-- The remark after Corollary 1.10: in Theorem 1.9 it suffices that a single level set
`lev≤α f` be bounded and nonempty. -/
theorem attainment_of_minimum_of_levelSet {f : E → EReal} (hlsc : LowerSemicontinuous f)
    (hp : IsProper f) {α : ℝ} (hb : IsBounded (levelSet f α))
    (hne : (levelSet f α).Nonempty) :
    (∃ a : ℝ, (⨅ x, f x) = a) ∧ (argmin f).Nonempty ∧ IsCompact (argmin f) := by
  have hcl : ∀ β : ℝ, IsClosed (levelSet f β) := lowerSemicontinuous_iff_isClosed_levelSet.1 hlsc
  have hK : IsCompact (levelSet f α) := Metric.isCompact_of_isClosed_isBounded (hcl α) hb
  obtain ⟨x₀, hx₀K, hmin⟩ := (hlsc.lowerSemicontinuousOn _).exists_isMinOn hne hK
  have hglob : IsMinOn f univ x₀ := by
    intro y _
    by_cases hy : y ∈ levelSet f α
    · exact hmin hy
    · exact (show f x₀ ≤ α from hx₀K).trans (le_of_lt (not_le.1 hy))
  have hx : f x₀ = ⨅ y, f y := by
    symm
    simpa [iInf_subtype'', iInf_univ] using hglob.iInf_eq (mem_univ x₀)
  have harg := argmin_eq_levelSet_toReal_of_isMinOn_of_isProper hglob hp
  refine ⟨exists_coe_eq_iInf_of_eq_iInf hp hx,
    ⟨x₀, (mem_argmin_iff_eq_iInf_of_isProper hp x₀).2 hx⟩, ?_⟩
  rw [harg]
  refine hK.of_isClosed_subset (hcl _) fun y hy ↦ ?_
  have htop : f x₀ ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top α) hx₀K
  have hfx : ((f x₀).toReal : EReal) = f x₀ := EReal.coe_toReal htop (hp.2 x₀).ne'
  calc f y ≤ ((f x₀).toReal : EReal) := hy
    _ = f x₀ := hfx
    _ ≤ α := hx₀K

/-- A lower semicontinuous function without the value `-∞` is bounded below by a real number
on every bounded set. -/
theorem exists_real_le_on_bounded {f : E → EReal} (hlsc : LowerSemicontinuous f)
    (hbot : ∀ x, ⊥ < f x) {B : Set E} (hB : IsBounded B) :
    ∃ m : ℝ, ∀ x ∈ B, (m : EReal) ≤ f x := by
  rcases B.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, fun x hx ↦ absurd hx (notMem_empty x)⟩
  obtain ⟨x₀, -, hmin⟩ := (hlsc.lowerSemicontinuousOn _).exists_isMinOn hne.closure
    hB.isCompact_closure
  obtain ⟨m, -, hm⟩ := EReal.lt_iff_exists_real_btwn.1 (hbot x₀)
  exact ⟨m, fun x hx ↦ hm.le.trans (hmin (subset_closure hx))⟩

/-- **Corollary 1.10** (lower bounds), first part: a proper lsc `f` is bounded from below
(finitely) on each bounded set. -/
theorem lower_bounds_bounded {f : E → EReal} (hlsc : LowerSemicontinuous f) (hp : IsProper f)
    {B : Set E} (hB : IsBounded B) : ∃ m : ℝ, ∀ x ∈ B, (m : EReal) ≤ f x :=
  exists_real_le_on_bounded hlsc hp.2 hB


end Attainment

/-! ## Example 1.11 -/

section ConstraintFunctions

/-- The extended-real function `f₀ + δ_C` of Example 1.11. -/
def restrictedObjective (f₀ : E → ℝ) (C : Set E) (x : E) : EReal :=
  (f₀ x : EReal) + indicatorVA C x

theorem restrictedObjective_of_mem {f₀ : E → ℝ} {C : Set E} {x : E} (hx : x ∈ C) :
    restrictedObjective f₀ C x = f₀ x := by
  simp [restrictedObjective, hx]

theorem restrictedObjective_of_not_mem {f₀ : E → ℝ} {C : Set E} {x : E} (hx : x ∉ C) :
    restrictedObjective f₀ C x = ⊤ := by
  simp [restrictedObjective, hx]

theorem levelSet_restrictedObjective (f₀ : E → ℝ) (C : Set E) (α : ℝ) :
    levelSet (restrictedObjective f₀ C) α = {x ∈ C | f₀ x ≤ α} := by
  ext x
  by_cases hx : x ∈ C
  · simp [levelSet, restrictedObjective_of_mem hx, hx]
  · simp [levelSet, restrictedObjective_of_not_mem hx, hx]

theorem iInf_restrictedObjective (f₀ : E → ℝ) (C : Set E) :
    (⨅ x, restrictedObjective f₀ C x) = ⨅ x ∈ C, (f₀ x : EReal) := by
  refine le_antisymm (le_iInf₂ fun x hx ↦ ?_) (le_iInf fun x ↦ ?_)
  · exact (iInf_le _ x).trans (restrictedObjective_of_mem hx).le
  · by_cases hx : x ∈ C
    · rw [restrictedObjective_of_mem hx]; exact iInf₂_le x hx
    · rw [restrictedObjective_of_not_mem hx]; exact le_top

end ConstraintFunctions

section Constraints

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Example 1.11** (level boundedness relative to constraints): for continuous `f₀` and a
nonempty closed `C` with all sets `{x ∈ C | f₀(x) ≤ α}` bounded, the minimum of `f₀` over `C` is
finite and attained on a nonempty compact subset of `C`. -/
theorem level_boundedness_relative_to_constraints {f₀ : E → ℝ} (hf₀ : Continuous f₀)
    {C : Set E} (hC : IsClosed C) (hne : C.Nonempty)
    (hb : ∀ α : ℝ, IsBounded {x ∈ C | f₀ x ≤ α}) :
    (∃ a : ℝ, (⨅ x ∈ C, (f₀ x : EReal)) = a) ∧
      {x ∈ C | IsMinOn f₀ C x}.Nonempty ∧ IsCompact {x ∈ C | IsMinOn f₀ C x} := by
  have hlsc : LowerSemicontinuous (restrictedObjective f₀ C) := by
    refine lowerSemicontinuous_iff_isClosed_levelSet.2 fun α ↦ ?_
    rw [levelSet_restrictedObjective]
    exact hC.inter (isClosed_le hf₀ continuous_const)
  have hlb : IsLevelBounded (restrictedObjective f₀ C) := fun α ↦ by
    rw [levelSet_restrictedObjective]; exact hb α
  have hp : IsProper (restrictedObjective f₀ C) := by
    obtain ⟨x, hx⟩ := hne
    refine ⟨⟨x, by simp [restrictedObjective_of_mem hx]⟩, fun y ↦ ?_⟩
    by_cases hy : y ∈ C
    · simp [restrictedObjective_of_mem hy]
    · simp [restrictedObjective_of_not_mem hy]
  obtain ⟨⟨a, ha⟩, harg, hcpt⟩ := attainment_of_minimum hlsc hlb hp
  have hargeq : argmin (restrictedObjective f₀ C) = {x ∈ C | IsMinOn f₀ C x} := by
    rw [argmin_eq_setOf_eq_iInf_of_isProper hp]
    ext x
    simp only [mem_setOf_eq]
    rw [ha]
    constructor
    · intro hx
      have hxC : x ∈ C := by
        by_contra hxC
        rw [restrictedObjective_of_not_mem hxC] at hx
        exact EReal.coe_ne_top a hx.symm
      refine ⟨hxC, fun y hy ↦ ?_⟩
      have h1 : restrictedObjective f₀ C x ≤ restrictedObjective f₀ C y :=
        hx ▸ ha ▸ iInf_le (restrictedObjective f₀ C) y
      rw [restrictedObjective_of_mem hxC, restrictedObjective_of_mem hy] at h1
      exact EReal.coe_le_coe_iff.1 h1
    · rintro ⟨hxC, hmin⟩
      rw [← ha]
      refine le_antisymm ?_ (iInf_le (restrictedObjective f₀ C) x)
      refine le_iInf fun y ↦ ?_
      by_cases hy : y ∈ C
      · rw [restrictedObjective_of_mem hxC, restrictedObjective_of_mem hy]
        exact EReal.coe_le_coe_iff.2 (hmin hy)
      · rw [restrictedObjective_of_not_mem hy]; exact le_top
  refine ⟨⟨a, (iInf_restrictedObjective f₀ C).symm.trans ha⟩, hargeq ▸ harg, hargeq ▸ hcpt⟩

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The criterion of Example 1.11 holds when `C` is bounded. -/
theorem constraint_level_bounded_of_bounded {f₀ : E → ℝ} {C : Set E} (hC : IsBounded C)
    (α : ℝ) : IsBounded {x ∈ C | f₀ x ≤ α} :=
  hC.subset fun _ hx ↦ hx.1

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The criterion of Example 1.11 holds when `f₀` is level-bounded (including `C = ℝⁿ`). -/
theorem constraint_level_bounded_of_isLevelBounded {f₀ : E → ℝ}
    (hf₀ : IsLevelBounded (fun x ↦ (f₀ x : EReal))) (C : Set E) (α : ℝ) :
    IsBounded {x ∈ C | f₀ x ≤ α} :=
  (hf₀ α).subset fun _ hx ↦ (show ((f₀ _ : ℝ) : EReal) ≤ α from EReal.coe_le_coe_iff.2 hx.2)

end Constraints

/-! ## Theorem 1.42 -/

section MinimizingSequences

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Theorem 1.42** (minimizing sequences): for `f` lsc, level-bounded and proper, every
minimizing sequence is bounded and has all its cluster points in `argmin f`; if the minimum is
attained at a unique point `x̄`, then `xν → x̄`. -/
theorem minimizing_sequences {f : E → EReal} (hlsc : LowerSemicontinuous f)
    (hlb : IsLevelBounded f) (hp : IsProper f) {xs : ℕ → E}
    (hmin : Tendsto (fun n ↦ f (xs n)) atTop (𝓝 (⨅ x, f x))) :
    IsBounded (range xs) ∧ (∀ c, MapClusterPt c atTop xs → c ∈ argmin f) ∧
      ∀ x, argmin f = {x} → Tendsto xs atTop (𝓝 x) := by
  obtain ⟨⟨a, ha⟩, -, -⟩ := attainment_of_minimum hlsc hlb hp
  rw [ha] at hmin
  have hcl : ∀ β : ℝ, IsClosed (levelSet f β) := lowerSemicontinuous_iff_isClosed_levelSet.1 hlsc
  have hev : ∀ β : ℝ, a < β → ∀ᶠ n in atTop, xs n ∈ levelSet f β := fun β hβ ↦
    hmin.eventually (gt_mem_nhds (EReal.coe_lt_coe_iff.2 hβ)) |>.mono fun _ hn ↦ hn.le
  have hK : IsCompact (levelSet f (a + 1)) :=
    Metric.isCompact_of_isClosed_isBounded (hcl _) (hlb _)
  have hcluster : ∀ c, MapClusterPt c atTop xs → c ∈ argmin f := by
    intro c hc
    have hle : ∀ β : ℝ, a < β → f c ≤ β := fun β hβ ↦ (hcl β).mem_of_mapClusterPt hc (hev β hβ)
    have hfc : f c ≤ a := by
      refine ereal_le_coe_of_forall_pos fun ε hε ↦ hle _ (by linarith)
    rw [argmin_eq_setOf_eq_iInf_of_isProper hp, mem_setOf_eq, ha]
    exact le_antisymm hfc (ha ▸ iInf_le f c)
  refine ⟨?_, hcluster, fun x hx ↦ ?_⟩
  · obtain ⟨N, hN⟩ := eventually_atTop.1 (hev (a + 1) (by linarith))
    have hsub : range xs ⊆ levelSet f (a + 1) ∪ xs '' Iio N := by
      rintro _ ⟨n, rfl⟩
      by_cases hn : N ≤ n
      · exact Or.inl (hN n hn)
      · exact Or.inr ⟨n, not_le.1 hn, rfl⟩
    exact ((hlb _).union ((finite_Iio N).image xs).isBounded).subset hsub
  · refine hK.tendsto_nhds_of_unique_mapClusterPt (hev (a + 1) (by linarith))
      fun c _ hc ↦ ?_
    have := hcluster c hc
    rwa [hx, mem_singleton_iff] at this

end MinimizingSequences

/-! ## Exercise 1.14 -/

section ERealHelpers

theorem neg_iSup_ereal {ι : Sort*} (g : ι → EReal) : -(⨆ i, g i) = ⨅ i, -g i :=
  EReal.negOrderIso.map_iSup g

theorem neg_iInf_ereal {ι : Sort*} (g : ι → EReal) : -(⨅ i, g i) = ⨆ i, -g i :=
  EReal.negOrderIso.map_iInf g

/-- An extended real `a` lies below `b` once every real number below `a` lies below `b`. -/
theorem ereal_le_of_forall_coe_lt {a b : EReal} (h : ∀ γ : ℝ, (γ : EReal) < a → (γ : EReal) ≤ b) :
    a ≤ b := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨γ, hbγ, hγa⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
  exact absurd (h γ hγa) (not_le.2 hbγ)

/-- A real `γ` lies below `b` once every `γ - ε`, `ε > 0`, does. -/
theorem ereal_coe_le_of_forall_sub {γ : ℝ} {b : EReal}
    (h : ∀ ε > (0 : ℝ), ((γ - ε : ℝ) : EReal) ≤ b) : (γ : EReal) ≤ b := by
  refine ereal_le_of_forall_coe_lt fun c hc ↦ ?_
  have := h (γ - c) (by linarith [EReal.coe_lt_coe_iff.1 hc])
  rwa [show γ - (γ - c) = c by ring] at this

end ERealHelpers

section Growth

variable [NormedAddCommGroup E]

/-- Formula 1(8): `liminf_{|x|→∞} g(x) = lim_{r→∞} inf_{|x|≥r} g(x)`. -/
def liminfAtInfinity (g : E → EReal) : EReal := ⨆ r : ℝ, ⨅ x ∈ {x : E | r ≤ ‖x‖}, g x

/-- Formula 1(8): `limsup_{|x|→∞} g(x) = lim_{r→∞} sup_{|x|≥r} g(x)`. -/
def limsupAtInfinity (g : E → EReal) : EReal := ⨅ r : ℝ, ⨆ x ∈ {x : E | r ≤ ‖x‖}, g x

theorem monotone_iInf_norm_ge (g : E → EReal) :
    Monotone (fun r : ℝ ↦ ⨅ x ∈ {x : E | r ≤ ‖x‖}, g x) :=
  fun _ _ h ↦ biInf_mono fun _ hx ↦ h.trans hx

theorem antitone_iSup_norm_ge (g : E → EReal) :
    Antitone (fun r : ℝ ↦ ⨆ x ∈ {x : E | r ≤ ‖x‖}, g x) :=
  fun _ _ h ↦ biSup_mono fun _ hx ↦ h.trans hx

/-- Formula 1(8) as a limit as `r → ∞`. -/
theorem tendsto_liminfAtInfinity (g : E → EReal) :
    Tendsto (fun r : ℝ ↦ ⨅ x ∈ {x : E | r ≤ ‖x‖}, g x) atTop (𝓝 (liminfAtInfinity g)) :=
  tendsto_atTop_iSup (monotone_iInf_norm_ge g)

theorem tendsto_limsupAtInfinity (g : E → EReal) :
    Tendsto (fun r : ℝ ↦ ⨆ x ∈ {x : E | r ≤ ‖x‖}, g x) atTop (𝓝 (limsupAtInfinity g)) :=
  tendsto_atTop_iInf (antitone_iSup_norm_ge g)

theorem limsupAtInfinity_eq_neg_liminfAtInfinity_neg (g : E → EReal) :
    limsupAtInfinity g = -liminfAtInfinity (fun x ↦ -g x) := by
  rw [liminfAtInfinity, neg_iSup_ereal]
  refine iInf_congr fun r ↦ ?_
  rw [neg_iInf_ereal]
  refine iSup_congr fun x ↦ ?_
  rw [neg_iInf_ereal]
  simp

/-- The quotient `f(x)/|x|^p` of Exercise 1.14; its value at `x = 0` plays no role. -/
def growthQuotient (f : E → EReal) (p : ℝ) (x : E) : EReal :=
  f x * (((‖x‖ ^ p)⁻¹ : ℝ) : EReal)

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Exercise 1.14**, lower growth: for `p ∈ (0,∞)`, `f` lsc with `f > -∞`,
`liminf_{|x|→∞} f(x)/|x|^p = sup {γ ∈ ℝ | ∃ β ∈ ℝ, f(x) ≥ γ|x|^p + β for all x}`. -/
theorem liminfAtInfinity_growthQuotient {f : E → EReal} {p : ℝ} (hp : 0 < p)
    (hlsc : LowerSemicontinuous f) (hbot : ∀ x, ⊥ < f x) :
    liminfAtInfinity (growthQuotient f p) =
      ⨆ (γ : ℝ) (_ : ∃ β : ℝ, ∀ x, ((γ * ‖x‖ ^ p + β : ℝ) : EReal) ≤ f x), (γ : EReal) := by
  apply le_antisymm
  · refine ereal_le_of_forall_coe_lt fun γ hγ ↦ ?_
    obtain ⟨r, hr⟩ := lt_iSup_iff.1 hγ
    set R := max r 1 with hR
    have hfar : ∀ x : E, R ≤ ‖x‖ → ((γ * ‖x‖ ^ p : ℝ) : EReal) ≤ f x := by
      intro x hx
      have hrx : r ≤ ‖x‖ := (le_max_left r 1).trans hx
      have hpos : 0 < ‖x‖ := lt_of_lt_of_le one_pos ((le_max_right r 1).trans hx)
      have ht : 0 < ‖x‖ ^ p := Real.rpow_pos_of_pos hpos p
      have hlt : (γ : EReal) < growthQuotient f p x := lt_of_lt_of_le hr (biInf_le _ hrx)
      have hmul := mul_le_mul_of_nonneg_right hlt.le (EReal.coe_nonneg.2 ht.le)
      have heq : growthQuotient f p x * ((‖x‖ ^ p : ℝ) : EReal) = f x := by
        rw [growthQuotient, mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ ht.ne', EReal.coe_one,
          mul_one]
      rw [heq, ← EReal.coe_mul] at hmul
      exact hmul
    obtain ⟨m, hm⟩ :=
      exists_real_le_on_bounded hlsc hbot (isBounded_closedBall (x := (0 : E)) (r := R))
    refine le_iSup₂_of_le γ ⟨min 0 (m - |γ| * R ^ p), fun x ↦ ?_⟩ le_rfl
    by_cases hx : R ≤ ‖x‖
    · refine le_trans (EReal.coe_le_coe_iff.2 ?_) (hfar x hx)
      linarith [min_le_left 0 (m - |γ| * R ^ p)]
    · have hxR : ‖x‖ ≤ R := (not_le.1 hx).le
      refine le_trans (EReal.coe_le_coe_iff.2 ?_) (hm x (mem_closedBall_zero_iff.2 hxR))
      have h1 : γ * ‖x‖ ^ p ≤ |γ| * R ^ p := by
        calc γ * ‖x‖ ^ p ≤ |γ| * ‖x‖ ^ p :=
              mul_le_mul_of_nonneg_right (le_abs_self γ) (Real.rpow_nonneg (norm_nonneg x) p)
          _ ≤ |γ| * R ^ p :=
              mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg x) hxR hp.le)
                (abs_nonneg γ)
      linarith [min_le_right 0 (m - |γ| * R ^ p)]
  · refine iSup₂_le fun γ ⟨β, hβ⟩ ↦ ereal_coe_le_of_forall_sub fun ε hε ↦ ?_
    obtain ⟨r, hr1, hr2⟩ := ((tendsto_rpow_atTop hp).eventually_ge_atTop (|β| / ε + 1)).and
      (eventually_ge_atTop 1) |>.exists
    refine le_iSup_of_le r (le_iInf₂ fun x hx ↦ ?_)
    have hx' : r ≤ ‖x‖ := hx
    have hpos : 0 < ‖x‖ := lt_of_lt_of_le one_pos (hr2.trans hx')
    have ht : r ^ p ≤ ‖x‖ ^ p := Real.rpow_le_rpow (by linarith) hx' hp.le
    have htpos : 0 < ‖x‖ ^ p := Real.rpow_pos_of_pos hpos p
    set t := ‖x‖ ^ p with htdef
    have hmul := mul_le_mul_of_nonneg_right (hβ x) (EReal.coe_nonneg.2 (inv_nonneg.2 htpos.le))
    refine le_trans (EReal.coe_le_coe_iff.2 ?_) (hmul.trans_eq' (EReal.coe_mul _ _).symm)
    have hkey : (γ * t + β) * t⁻¹ = γ + β / t := by field_simp
    rw [hkey]
    have hεt : |β| ≤ ε * t := by
      have : |β| / ε + 1 ≤ t := hr1.trans ht
      have h2 : |β| / ε * ε = |β| := div_mul_cancel₀ _ hε.ne'
      nlinarith
    have : -ε ≤ β / t := by
      rw [le_div_iff₀ htpos]
      linarith [neg_abs_le β]
    linarith

/-- **Exercise 1.14**, upper growth: for `p ∈ (0,∞)`, `f` usc with `f < ∞`,
`limsup_{|x|→∞} f(x)/|x|^p = inf {γ ∈ ℝ | ∃ β ∈ ℝ, f(x) ≤ γ|x|^p + β for all x}`. -/
theorem limsupAtInfinity_growthQuotient {f : E → EReal} {p : ℝ} (hp : 0 < p)
    (husc : UpperSemicontinuous f) (htop : ∀ x, f x < ⊤) :
    limsupAtInfinity (growthQuotient f p) =
      ⨅ (γ : ℝ) (_ : ∃ β : ℝ, ∀ x, f x ≤ ((γ * ‖x‖ ^ p + β : ℝ) : EReal)), (γ : EReal) := by
  have hlsc : LowerSemicontinuous (fun x ↦ -f x) :=
    continuous_neg.comp_upperSemicontinuous_antitone husc fun _ _ h ↦ EReal.neg_le_neg_iff.2 h
  have hbot : ∀ x, ⊥ < -f x := fun x ↦ EReal.neg_lt_neg_iff.2 (htop x) |>.trans_eq' (by simp)
  have h := liminfAtInfinity_growthQuotient hp hlsc hbot
  have hq : growthQuotient (fun x ↦ -f x) p = fun x ↦ -growthQuotient f p x := by
    funext x; simp [growthQuotient]
  rw [limsupAtInfinity_eq_neg_liminfAtInfinity_neg, ← hq, h, neg_iSup_ereal]
  refine le_antisymm ?_ ?_
  · refine le_iInf₂ fun γ ⟨β, hβ⟩ ↦ iInf_le_of_le (-γ) ?_
    have hmem : ∃ β : ℝ, ∀ x, ((-γ * ‖x‖ ^ p + β : ℝ) : EReal) ≤ -f x := by
      refine ⟨-β, fun x ↦ ?_⟩
      rw [EReal.le_neg, ← EReal.coe_neg]
      convert hβ x using 2
      ring
    rw [neg_iSup_ereal]
    exact iInf_le_of_le hmem (by simp)
  · refine le_iInf fun γ ↦ ?_
    rw [neg_iSup_ereal]
    refine le_iInf fun ⟨β, hβ⟩ ↦ ?_
    have hmem : ∃ β : ℝ, ∀ x, f x ≤ ((-γ * ‖x‖ ^ p + β : ℝ) : EReal) := by
      refine ⟨-β, fun x ↦ ?_⟩
      have := hβ x
      rw [EReal.le_neg, ← EReal.coe_neg] at this
      convert this using 2
      ring
    exact (iInf₂_le (-γ) hmem).trans_eq (by simp)

end Growth

end RW
