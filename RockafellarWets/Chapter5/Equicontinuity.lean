/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Equicontinuity of Sequences

Definition 5.38 and Exercise 5.39.

Following Chapter 4 and 5.12, `S + εIB` is the open thickening; since every
clause quantifies `∀ ε > 0`, this agrees with the book's closed one.  The
book's index set `N ∈ N∞` is the `atTop` filter: "for all `ν` in some
`N ∈ N∞`" is `∀ᶠ ν in atTop`.

The remarks after 5.38 are proved: equicontinuity is asymptotic
equicontinuity, and it forces each term of the sequence to be continuous,
whereas the book's example `Sν(x) = {1/ν}, [-1/ν, 1/ν], {-1/ν}` for
`x > 0, x = 0, x < 0` is asymptotically equicontinuous at `0` with no term
inner semicontinuous there.

Exercise 5.39 turns on one geometric step.  Equi-outer semicontinuity
controls `Fν(y) - Fν(x̄)` only where `|Fν(y)| ≤ ρ`, while equi-inner
semicontinuity asks for that control where `|Fν(x̄)| ≤ ρ`.  Continuity of each
`Fν` bridges the two by the intermediate value theorem: if `Fν` ever left the
ball of radius `ρ + ε` along the segment from `x̄` to `y`, it would first have
to cross that sphere, and at the crossing point equi-outer semicontinuity
already pins it within `ε` of `Fν(x̄)`, so it never got that far.
-/

import Mathlib.Tactic.Module
import RockafellarWets.Chapter5.LocallyBoundedContinuity

open Bornology Filter Metric Set Topology

namespace RW

section Definitions

variable {E F : Type*} [PseudoMetricSpace E] [SeminormedAddCommGroup F]

/-- **Definition 5.38**: the sequence is equi-osc at `x` relative to `X`. -/
def SvEquiOscWithinAt (Sseq : ℕ → E → Set F) (X : Set E) (x : E) : Prop :=
  ∀ ε > 0, ∀ ρ > 0, ∃ V ∈ nhds x, ∀ n, ∀ y ∈ V ∩ X,
    Sseq n y ∩ closedBall 0 ρ ⊆ thickening ε (Sseq n x)

/-- **Definition 5.38**: the sequence is asymptotically equi-osc at `x`
relative to `X`.  The index set, like the neighborhood, may depend on `ε`
and `ρ`. -/
def SvAsymptoticallyEquiOscWithinAt (Sseq : ℕ → E → Set F) (X : Set E) (x : E) :
    Prop :=
  ∀ ε > 0, ∀ ρ > 0, ∃ V ∈ nhds x, ∀ᶠ n in atTop, ∀ y ∈ V ∩ X,
    Sseq n y ∩ closedBall 0 ρ ⊆ thickening ε (Sseq n x)

/-- **Definition 5.38**: the sequence is equi-isc at `x` relative to `X`. -/
def SvEquiIscWithinAt (Sseq : ℕ → E → Set F) (X : Set E) (x : E) : Prop :=
  ∀ ε > 0, ∀ ρ > 0, ∃ V ∈ nhds x, ∀ n, ∀ y ∈ V ∩ X,
    Sseq n x ∩ closedBall 0 ρ ⊆ thickening ε (Sseq n y)

/-- **Definition 5.38**: the sequence is asymptotically equi-isc at `x`
relative to `X`. -/
def SvAsymptoticallyEquiIscWithinAt (Sseq : ℕ → E → Set F) (X : Set E) (x : E) :
    Prop :=
  ∀ ε > 0, ∀ ρ > 0, ∃ V ∈ nhds x, ∀ᶠ n in atTop, ∀ y ∈ V ∩ X,
    Sseq n x ∩ closedBall 0 ρ ⊆ thickening ε (Sseq n y)

/-- **Definition 5.38**: equicontinuity at `x` relative to `X`. -/
def SvEquicontinuousWithinAt (Sseq : ℕ → E → Set F) (X : Set E) (x : E) : Prop :=
  SvEquiIscWithinAt Sseq X x ∧ SvEquiOscWithinAt Sseq X x

/-- **Definition 5.38**: asymptotic equicontinuity at `x` relative to `X`. -/
def SvAsymptoticallyEquicontinuousWithinAt (Sseq : ℕ → E → Set F) (X : Set E)
    (x : E) : Prop :=
  SvAsymptoticallyEquiIscWithinAt Sseq X x ∧
    SvAsymptoticallyEquiOscWithinAt Sseq X x

/-- **Definition 5.38** in the absolute case. -/
def SvEquiOscAt (Sseq : ℕ → E → Set F) (x : E) : Prop :=
  SvEquiOscWithinAt Sseq univ x

/-- **Definition 5.38** in the absolute case. -/
def SvAsymptoticallyEquiOscAt (Sseq : ℕ → E → Set F) (x : E) : Prop :=
  SvAsymptoticallyEquiOscWithinAt Sseq univ x

/-- **Definition 5.38** in the absolute case. -/
def SvEquiIscAt (Sseq : ℕ → E → Set F) (x : E) : Prop :=
  SvEquiIscWithinAt Sseq univ x

/-- **Definition 5.38** in the absolute case. -/
def SvAsymptoticallyEquiIscAt (Sseq : ℕ → E → Set F) (x : E) : Prop :=
  SvAsymptoticallyEquiIscWithinAt Sseq univ x

/-- **Definition 5.38** in the absolute case. -/
def SvEquicontinuousAt (Sseq : ℕ → E → Set F) (x : E) : Prop :=
  SvEquicontinuousWithinAt Sseq univ x

/-- **Definition 5.38** in the absolute case. -/
def SvAsymptoticallyEquicontinuousAt (Sseq : ℕ → E → Set F) (x : E) : Prop :=
  SvAsymptoticallyEquicontinuousWithinAt Sseq univ x

theorem svEquiOscAt_iff {Sseq : ℕ → E → Set F} {x : E} :
    SvEquiOscAt Sseq x ↔
      ∀ ε > 0, ∀ ρ > 0, ∃ V ∈ nhds x, ∀ n, ∀ y ∈ V,
        Sseq n y ∩ closedBall 0 ρ ⊆ thickening ε (Sseq n x) := by
  simp [SvEquiOscAt, SvEquiOscWithinAt]

theorem svAsymptoticallyEquiOscAt_iff {Sseq : ℕ → E → Set F} {x : E} :
    SvAsymptoticallyEquiOscAt Sseq x ↔
      ∀ ε > 0, ∀ ρ > 0, ∃ V ∈ nhds x, ∀ᶠ n in atTop, ∀ y ∈ V,
        Sseq n y ∩ closedBall 0 ρ ⊆ thickening ε (Sseq n x) := by
  simp [SvAsymptoticallyEquiOscAt, SvAsymptoticallyEquiOscWithinAt]

theorem svAsymptoticallyEquiIscAt_iff {Sseq : ℕ → E → Set F} {x : E} :
    SvAsymptoticallyEquiIscAt Sseq x ↔
      ∀ ε > 0, ∀ ρ > 0, ∃ V ∈ nhds x, ∀ᶠ n in atTop, ∀ y ∈ V,
        Sseq n x ∩ closedBall 0 ρ ⊆ thickening ε (Sseq n y) := by
  simp [SvAsymptoticallyEquiIscAt, SvAsymptoticallyEquiIscWithinAt]

theorem svEquiIscAt_iff {Sseq : ℕ → E → Set F} {x : E} :
    SvEquiIscAt Sseq x ↔
      ∀ ε > 0, ∀ ρ > 0, ∃ V ∈ nhds x, ∀ n, ∀ y ∈ V,
        Sseq n x ∩ closedBall 0 ρ ⊆ thickening ε (Sseq n y) := by
  simp [SvEquiIscAt, SvEquiIscWithinAt]

/-- The remark after 5.38: equicontinuity is stronger than asymptotic
equicontinuity, each clause holding for all indices rather than eventually. -/
theorem SvEquiOscWithinAt.asymptotically {Sseq : ℕ → E → Set F} {X : Set E}
    {x : E} (h : SvEquiOscWithinAt Sseq X x) :
    SvAsymptoticallyEquiOscWithinAt Sseq X x := by
  intro ε hε ρ hρ
  obtain ⟨V, hV, hsub⟩ := h ε hε ρ hρ
  exact ⟨V, hV, Eventually.of_forall hsub⟩

theorem SvEquiIscWithinAt.asymptotically {Sseq : ℕ → E → Set F} {X : Set E}
    {x : E} (h : SvEquiIscWithinAt Sseq X x) :
    SvAsymptoticallyEquiIscWithinAt Sseq X x := by
  intro ε hε ρ hρ
  obtain ⟨V, hV, hsub⟩ := h ε hε ρ hρ
  exact ⟨V, hV, Eventually.of_forall hsub⟩

theorem SvEquicontinuousWithinAt.asymptotically {Sseq : ℕ → E → Set F}
    {X : Set E} {x : E} (h : SvEquicontinuousWithinAt Sseq X x) :
    SvAsymptoticallyEquicontinuousWithinAt Sseq X x :=
  ⟨h.1.asymptotically, h.2.asymptotically⟩

/-- The remark after 5.38: equi-outer semicontinuity of a sequence entails
outer semicontinuity of each of its terms, so equicontinuity of a sequence is
much stronger than asymptotic equicontinuity. -/
theorem SvEquiOscAt.svOscAt {Sseq : ℕ → E → Set F} {x : E}
    (h : SvEquiOscAt Sseq x) (n : ℕ) (hclosed : IsClosed (Sseq n x)) :
    SvOscAt (Sseq n) x := by
  intro u hu
  rw [← hclosed.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  have hδpos : 0 < min (ε / 2) 1 := lt_min (by linarith) zero_lt_one
  obtain ⟨V, hV, hsub⟩ :=
    svEquiOscAt_iff.1 h (ε / 2) (by linarith) (‖u‖ + 1) (by positivity)
  obtain ⟨y, ⟨v, hvS, hvball⟩, hyV⟩ :=
    ((hu (ball u (min (ε / 2) 1)) (ball_mem_nhds u hδpos)).and_eventually
      (eventually_mem_set.2 hV)).exists
  have hvu : dist v u < min (ε / 2) 1 := by rwa [mem_ball] at hvball
  have hvnorm : v ∈ closedBall (0 : F) (‖u‖ + 1) := by
    rw [mem_closedBall_zero_iff]
    have h1 : ‖v‖ ≤ ‖v - u‖ + ‖u‖ := by simpa using norm_add_le (v - u) u
    rw [← dist_eq_norm] at h1
    have h2 : dist v u < 1 := lt_of_lt_of_le hvu (min_le_right _ _)
    linarith
  obtain ⟨w, hwS, hwdist⟩ :=
    Metric.mem_thickening_iff.1 (hsub n y hyV ⟨hvS, hvnorm⟩)
  refine ⟨w, hwS, ?_⟩
  have h3 : dist u w ≤ dist u v + dist v w := dist_triangle _ _ _
  have h4 : dist u v < ε / 2 := by
    rw [dist_comm]
    exact lt_of_lt_of_le hvu (min_le_left _ _)
  linarith

/-- The companion remark: equi-inner semicontinuity entails inner
semicontinuity of each term. -/
theorem SvEquiIscAt.svIscAt {Sseq : ℕ → E → Set F} {x : E}
    (h : SvEquiIscAt Sseq x) (n : ℕ) : SvIscAt (Sseq n) x := by
  intro u hu W hW
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hW
  obtain ⟨V, hV, hsub⟩ := svEquiIscAt_iff.1 h ε hε (‖u‖ + 1) (by positivity)
  filter_upwards [hV] with y hy
  obtain ⟨w, hwS, hwdist⟩ := Metric.mem_thickening_iff.1
    (hsub n y hy ⟨hu, by rw [mem_closedBall_zero_iff]; linarith⟩)
  exact ⟨w, hwS, hball (by rwa [mem_ball, dist_comm])⟩

/-- The remark after 5.38: an equicontinuous sequence consists of continuous
mappings. -/
theorem SvEquicontinuousAt.svContinuousAt {Sseq : ℕ → E → Set F} {x : E}
    (h : SvEquicontinuousAt Sseq x) (n : ℕ) (hclosed : IsClosed (Sseq n x)) :
    SvContinuousAt (Sseq n) x :=
  ⟨SvEquiOscAt.svOscAt h.2 n hclosed, SvEquiIscAt.svIscAt h.1 n⟩

end Definitions

section AsymptoticExample

/-- The book's example after 5.38: `Sν(x) = {1/ν}` for `x > 0`,
`[-1/ν, 1/ν]` for `x = 0` and `{-1/ν}` for `x < 0`. -/
noncomputable def stepSeq : ℕ → ℝ → Set ℝ := fun n x ↦
  if 0 < x then {((n : ℝ) + 1)⁻¹}
  else if x < 0 then {-((n : ℝ) + 1)⁻¹}
  else Icc (-((n : ℝ) + 1)⁻¹) (((n : ℝ) + 1)⁻¹)

theorem stepSeq_zero (n : ℕ) :
    stepSeq n 0 = Icc (-((n : ℝ) + 1)⁻¹) (((n : ℝ) + 1)⁻¹) := by
  simp [stepSeq]

theorem stepSeq_subset (n : ℕ) (y : ℝ) :
    stepSeq n y ⊆ Icc (-((n : ℝ) + 1)⁻¹) (((n : ℝ) + 1)⁻¹) := by
  have hc : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
  unfold stepSeq
  split
  · simp only [singleton_subset_iff, mem_Icc]
    constructor <;> linarith
  · split
    · simp only [singleton_subset_iff, mem_Icc]
      constructor <;> linarith
    · exact Subset.rfl

theorem stepSeq_nonempty (n : ℕ) (y : ℝ) : (stepSeq n y).Nonempty := by
  have hc : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
  unfold stepSeq
  split
  · exact ⟨_, rfl⟩
  · split
    · exact ⟨_, rfl⟩
    · exact ⟨0, by constructor <;> linarith⟩

theorem stepSeq_of_ne (n : ℕ) {y : ℝ} (hy : y ≠ 0) :
    stepSeq n y = {((n : ℝ) + 1)⁻¹} ∨ stepSeq n y = {-((n : ℝ) + 1)⁻¹} := by
  unfold stepSeq
  rcases lt_trichotomy y 0 with h | h | h
  · right
    rw [if_neg (by linarith), if_pos h]
  · exact absurd h hy
  · left
    rw [if_pos h]

/-- The example is equi-osc at `0`: every value is contained in the value at
`0`, so no neighborhood is needed at all. -/
theorem svEquiOscAt_stepSeq : SvEquiOscAt stepSeq 0 := by
  rw [svEquiOscAt_iff]
  intro ε hε ρ _
  refine ⟨univ, univ_mem, fun n y _ ↦ ?_⟩
  refine (inter_subset_left.trans (stepSeq_subset n y)).trans ?_
  rw [← stepSeq_zero n]
  exact self_subset_thickening hε _

/-- But it is only *asymptotically* equi-isc: the two-sided value at `0` has
width `2/ν`, which is below `ε` only for late indices. -/
theorem svAsymptoticallyEquiIscAt_stepSeq :
    SvAsymptoticallyEquiIscAt stepSeq 0 := by
  rw [svAsymptoticallyEquiIscAt_iff]
  intro ε hε ρ _
  refine ⟨univ, univ_mem,
    eventually_atTop.2 ⟨⌈2 / ε⌉₊, fun n hn y _ u hu ↦ ?_⟩⟩
  obtain ⟨w, hw⟩ := stepSeq_nonempty n y
  refine Metric.mem_thickening_iff.2 ⟨w, hw, ?_⟩
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hnR : (2 : ℝ) / ε ≤ (n : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
  rw [div_le_iff₀ hε] at hnR
  have hsmall : 2 * ((n : ℝ) + 1)⁻¹ < ε := by
    have hkey : (2 : ℝ) < ε * ((n : ℝ) + 1) := by nlinarith
    calc 2 * ((n : ℝ) + 1)⁻¹ = 2 / ((n : ℝ) + 1) := by ring
      _ < ε := by rw [div_lt_iff₀ hn1]; linarith
  obtain ⟨h1, h2⟩ := stepSeq_subset n 0 hu.1
  obtain ⟨h3, h4⟩ := stepSeq_subset n y hw
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- The example is asymptotically equicontinuous at `0`. -/
theorem svAsymptoticallyEquicontinuousAt_stepSeq :
    SvAsymptoticallyEquicontinuousAt stepSeq 0 :=
  ⟨svAsymptoticallyEquiIscAt_stepSeq, svEquiOscAt_stepSeq.asymptotically⟩

/-- **The remark after 5.38.**  None of the mappings in the example is inner
semicontinuous at `0`, hence none is continuous there, yet the sequence is
asymptotically equicontinuous at `0`.  So asymptotic equicontinuity is
strictly weaker than equicontinuity. -/
theorem not_svIscAt_stepSeq (n : ℕ) : ¬ SvIscAt (stepSeq n) 0 := by
  intro hisc
  have hc : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
  have hmem : (0 : ℝ) ∈ stepSeq n 0 := by
    rw [stepSeq_zero]
    constructor <;> linarith
  have hev := hisc hmem (ball (0 : ℝ) (((n : ℝ) + 1)⁻¹)) (ball_mem_nhds 0 hc)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hev
  have hy : (δ / 2 : ℝ) ∈ ball (0 : ℝ) δ := by
    rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by linarith)]
    linarith
  obtain ⟨w, hwS, hwball⟩ := hball hy
  have hδne : (δ / 2 : ℝ) ≠ 0 := by positivity
  have habs : |w| = ((n : ℝ) + 1)⁻¹ := by
    rcases stepSeq_of_ne n hδne with heq | heq
    · rw [heq, mem_singleton_iff] at hwS
      rw [hwS, abs_of_pos hc]
    · rw [heq, mem_singleton_iff] at hwS
      rw [hwS, abs_neg, abs_of_pos hc]
  rw [mem_ball, Real.dist_eq, sub_zero, habs] at hwball
  exact absurd hwball (lt_irrefl _)

/-- Consequently no term of the example is continuous at `0`. -/
theorem not_svContinuousAt_stepSeq (n : ℕ) : ¬ SvContinuousAt (stepSeq n) 0 :=
  fun h ↦ not_svIscAt_stepSeq n h.2

end AsymptoticExample

section SingleValued

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [SeminormedAddCommGroup F]

omit [NormedSpace ℝ E] in
theorem mem_thickening_singleton_iff {u v : F} {ε : ℝ} :
    u ∈ thickening ε ({v} : Set F) ↔ dist u v < ε := by
  simp

omit [NormedSpace ℝ E] in
/-- **Exercise 5.39**, the explicit form of equi-outer semicontinuity for
single-valued mappings. -/
theorem svEquiOscAt_svSingleton_iff {Fs : ℕ → E → F} {x : E} :
    SvEquiOscAt (fun n ↦ svSingleton (Fs n)) x ↔
      ∀ ε > 0, ∀ ρ > 0, ∃ V ∈ nhds x, ∀ n, ∀ y ∈ V,
        ‖Fs n y‖ ≤ ρ → dist (Fs n y) (Fs n x) < ε := by
  rw [svEquiOscAt_iff]
  refine forall₂_congr fun ε _ ↦ forall₂_congr fun ρ _ ↦ ?_
  constructor
  · rintro ⟨V, hV, hsub⟩
    refine ⟨V, hV, fun n y hy hnorm ↦ mem_thickening_singleton_iff.1 ?_⟩
    exact hsub n y hy ⟨rfl, by rwa [mem_closedBall_zero_iff]⟩
  · rintro ⟨V, hV, hsub⟩
    refine ⟨V, hV, fun n y hy u hu ↦ ?_⟩
    have hueq : u = Fs n y := hu.1
    subst hueq
    exact mem_thickening_singleton_iff.2
      (hsub n y hy (by simpa [mem_closedBall_zero_iff] using hu.2))

omit [NormedSpace ℝ E] in
/-- The same unpacking for equi-inner semicontinuity. -/
theorem svEquiIscAt_svSingleton_iff {Fs : ℕ → E → F} {x : E} :
    SvEquiIscAt (fun n ↦ svSingleton (Fs n)) x ↔
      ∀ ε > 0, ∀ ρ > 0, ∃ V ∈ nhds x, ∀ n, ∀ y ∈ V,
        ‖Fs n x‖ ≤ ρ → dist (Fs n x) (Fs n y) < ε := by
  rw [svEquiIscAt_iff]
  refine forall₂_congr fun ε _ ↦ forall₂_congr fun ρ _ ↦ ?_
  constructor
  · rintro ⟨V, hV, hsub⟩
    refine ⟨V, hV, fun n y hy hnorm ↦ mem_thickening_singleton_iff.1 ?_⟩
    exact hsub n y hy ⟨rfl, by rwa [mem_closedBall_zero_iff]⟩
  · rintro ⟨V, hV, hsub⟩
    refine ⟨V, hV, fun n y hy u hu ↦ ?_⟩
    have hueq : u = Fs n x := hu.1
    subst hueq
    exact mem_thickening_singleton_iff.2
      (hsub n y hy (by simpa [mem_closedBall_zero_iff] using hu.2))

/-- The segment step behind 5.39.  If a continuous `f` moves by `ε` or more
between `x` and a nearby `y`, and every point of the segment at which `f` is
no larger than `ρ + ε` moves by less than `ε`, then `f(x)` is larger than
`ρ`: the intermediate value theorem catches the first crossing. -/
private theorem norm_le_of_segment {f : E → F} (hf : Continuous f) {x y : E}
    {ρ ε : ℝ} (hε : 0 < ε) (hx : ‖f x‖ ≤ ρ)
    (hstep : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖f (x + t • (y - x))‖ ≤ ρ + ε → dist (f (x + t • (y - x))) (f x) < ε) :
    dist (f y) (f x) < ε := by
  by_contra hcon
  push_neg at hcon
  set g : ℝ → ℝ := fun t ↦ ‖f (x + t • (y - x))‖ with hg
  have hgcont : ContinuousOn g (Icc (0 : ℝ) 1) := by
    apply Continuous.continuousOn
    exact (hf.comp (continuous_const.add (continuous_id.smul continuous_const))).norm
  have hg0 : g 0 ≤ ρ := by simpa [hg] using hx
  have hg1 : ρ + ε < g 1 := by
    have h1 : x + (1 : ℝ) • (y - x) = y := by module
    have : ¬ ‖f y‖ ≤ ρ + ε := fun hle ↦
      absurd (hstep 1 (by norm_num) (by rwa [h1])) (by rwa [h1, not_lt])
    simp only [hg, h1]
    linarith [not_le.1 this]
  obtain ⟨t, ht, hgt⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hgcont
    (show ρ + ε ∈ Icc (g 0) (g 1) from ⟨by linarith, by linarith⟩)
  have hmove := hstep t ht (le_of_eq hgt)
  have : ‖f (x + t • (y - x))‖ < ρ + ε := by
    have h2 : ‖f (x + t • (y - x))‖ ≤ ‖f (x + t • (y - x)) - f x‖ + ‖f x‖ := by
      simpa using norm_add_le (f (x + t • (y - x)) - f x) (f x)
    rw [← dist_eq_norm] at h2
    linarith
  have hgtv : ‖f (x + t • (y - x))‖ = ρ + ε := hgt
  rw [hgtv] at this
  exact absurd this (lt_irrefl _)

/-- **Exercise 5.39**: for continuous single-valued mappings, equi-outer
semicontinuity already implies equi-inner semicontinuity. -/
theorem svEquiIscAt_svSingleton_of_svEquiOscAt {Fs : ℕ → E → F}
    (hcont : ∀ n, Continuous (Fs n)) {x : E}
    (h : SvEquiOscAt (fun n ↦ svSingleton (Fs n)) x) :
    SvEquiIscAt (fun n ↦ svSingleton (Fs n)) x := by
  rw [svEquiIscAt_svSingleton_iff]
  intro ε hε ρ hρ
  obtain ⟨V, hV, hsub⟩ :=
    svEquiOscAt_svSingleton_iff.1 h ε hε (ρ + ε) (by linarith)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hV
  refine ⟨ball x δ, ball_mem_nhds x hδ, fun n y hy hnorm ↦ ?_⟩
  rw [dist_comm]
  refine norm_le_of_segment (hcont n) hε hnorm fun t ht hle ↦ ?_
  refine hsub n _ (hball ?_) hle
  rw [mem_ball, dist_eq_norm]
  have hnorm' : ‖x + t • (y - x) - x‖ = |t| * ‖y - x‖ := by
    have : x + t • (y - x) - x = t • (y - x) := by module
    rw [this, norm_smul, Real.norm_eq_abs]
  rw [hnorm', abs_of_nonneg ht.1]
  have hyx : ‖y - x‖ < δ := by simpa [dist_eq_norm] using mem_ball.1 hy
  nlinarith [norm_nonneg (y - x), ht.2]

/-- **Exercise 5.39**: for continuous single-valued mappings, equicontinuity
at `x̄` is the same as equi-outer semicontinuity at `x̄`. -/
theorem svEquicontinuousAt_svSingleton_iff {Fs : ℕ → E → F}
    (hcont : ∀ n, Continuous (Fs n)) {x : E} :
    SvEquicontinuousAt (fun n ↦ svSingleton (Fs n)) x ↔
      SvEquiOscAt (fun n ↦ svSingleton (Fs n)) x :=
  ⟨fun h ↦ h.2, fun h ↦ ⟨svEquiIscAt_svSingleton_of_svEquiOscAt hcont h, h⟩⟩

omit [NormedSpace ℝ E] in
/-- **Exercise 5.39**, asymptotic form of the explicit statement. -/
theorem svAsymptoticallyEquiOscAt_svSingleton_iff {Fs : ℕ → E → F} {x : E} :
    SvAsymptoticallyEquiOscAt (fun n ↦ svSingleton (Fs n)) x ↔
      ∀ ε > 0, ∀ ρ > 0, ∃ V ∈ nhds x, ∀ᶠ n in atTop, ∀ y ∈ V,
        ‖Fs n y‖ ≤ ρ → dist (Fs n y) (Fs n x) < ε := by
  rw [svAsymptoticallyEquiOscAt_iff]
  refine forall₂_congr fun ε _ ↦ forall₂_congr fun ρ _ ↦ ?_
  constructor
  · rintro ⟨V, hV, hsub⟩
    refine ⟨V, hV, hsub.mono fun n hn y hy hnorm ↦ mem_thickening_singleton_iff.1 ?_⟩
    exact hn y hy ⟨rfl, by rwa [mem_closedBall_zero_iff]⟩
  · rintro ⟨V, hV, hsub⟩
    refine ⟨V, hV, hsub.mono fun n hn y hy u hu ↦ ?_⟩
    have hueq : u = Fs n y := hu.1
    subst hueq
    exact mem_thickening_singleton_iff.2
      (hn y hy (by simpa [mem_closedBall_zero_iff] using hu.2))

omit [NormedSpace ℝ E] in
/-- The same unpacking for asymptotic equi-inner semicontinuity. -/
theorem svAsymptoticallyEquiIscAt_svSingleton_iff {Fs : ℕ → E → F} {x : E} :
    SvAsymptoticallyEquiIscAt (fun n ↦ svSingleton (Fs n)) x ↔
      ∀ ε > 0, ∀ ρ > 0, ∃ V ∈ nhds x, ∀ᶠ n in atTop, ∀ y ∈ V,
        ‖Fs n x‖ ≤ ρ → dist (Fs n x) (Fs n y) < ε := by
  rw [svAsymptoticallyEquiIscAt_iff]
  refine forall₂_congr fun ε _ ↦ forall₂_congr fun ρ _ ↦ ?_
  constructor
  · rintro ⟨V, hV, hsub⟩
    refine ⟨V, hV, hsub.mono fun n hn y hy hnorm ↦ mem_thickening_singleton_iff.1 ?_⟩
    exact hn y hy ⟨rfl, by rwa [mem_closedBall_zero_iff]⟩
  · rintro ⟨V, hV, hsub⟩
    refine ⟨V, hV, hsub.mono fun n hn y hy u hu ↦ ?_⟩
    have hueq : u = Fs n x := hu.1
    subst hueq
    exact mem_thickening_singleton_iff.2
      (hn y hy (by simpa [mem_closedBall_zero_iff] using hu.2))

/-- **Exercise 5.39**, final sentence: the asymptotic notions match too. -/
theorem svAsymptoticallyEquicontinuousAt_svSingleton_iff {Fs : ℕ → E → F}
    (hcont : ∀ n, Continuous (Fs n)) {x : E} :
    SvAsymptoticallyEquicontinuousAt (fun n ↦ svSingleton (Fs n)) x ↔
      SvAsymptoticallyEquiOscAt (fun n ↦ svSingleton (Fs n)) x := by
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨svAsymptoticallyEquiIscAt_svSingleton_iff.2 ?_, h⟩⟩
  intro ε hε ρ hρ
  obtain ⟨V, hV, hsub⟩ :=
    svAsymptoticallyEquiOscAt_svSingleton_iff.1 h ε hε (ρ + ε) (by linarith)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hV
  refine ⟨ball x δ, ball_mem_nhds x hδ, hsub.mono fun n hn y hy hnorm ↦ ?_⟩
  rw [dist_comm]
  refine norm_le_of_segment (hcont n) hε hnorm fun t ht hle ↦ ?_
  refine hn _ (hball ?_) hle
  rw [mem_ball, dist_eq_norm]
  have hnorm' : ‖x + t • (y - x) - x‖ = |t| * ‖y - x‖ := by
    have hsub' : x + t • (y - x) - x = t • (y - x) := by module
    rw [hsub', norm_smul, Real.norm_eq_abs]
  rw [hnorm', abs_of_nonneg ht.1]
  have hyx : ‖y - x‖ < δ := by simpa [dist_eq_norm] using mem_ball.1 hy
  nlinarith [norm_nonneg (y - x), ht.2]

/-- The book's "eventually locally bounded" condition, under which the
mention of `ρ` in 5.39 can be dropped. -/
def SvEventuallyLocallyBoundedAt (Fs : ℕ → E → F) (x : E) : Prop :=
  ∃ V ∈ nhds x, ∃ ρ : ℝ, ∀ᶠ n in atTop, ∀ y ∈ V, ‖Fs n y‖ ≤ ρ

omit [NormedSpace ℝ E] in
/-- **Exercise 5.39**, final remark: for an eventually locally bounded
sequence, asymptotic equi-outer semicontinuity is the traditional
`ε`-statement, with no `ρ`. -/
theorem svAsymptoticallyEquiOscAt_svSingleton_iff_of_eventuallyLocallyBounded
    {Fs : ℕ → E → F} {x : E} (hb : SvEventuallyLocallyBoundedAt Fs x) :
    SvAsymptoticallyEquiOscAt (fun n ↦ svSingleton (Fs n)) x ↔
      ∀ ε > 0, ∃ V ∈ nhds x, ∀ᶠ n in atTop, ∀ y ∈ V,
        dist (Fs n y) (Fs n x) < ε := by
  obtain ⟨W, hW, ρ, hρ⟩ := hb
  rw [svAsymptoticallyEquiOscAt_svSingleton_iff]
  constructor
  · intro h ε hε
    obtain ⟨V, hV, hsub⟩ := h ε hε (max ρ 1) (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
    refine ⟨V ∩ W, Filter.inter_mem hV hW, ?_⟩
    filter_upwards [hsub, hρ] with n hn hnb y hy
    exact hn y hy.1 ((hnb y hy.2).trans (le_max_left _ _))
  · intro h ε hε _ _
    obtain ⟨V, hV, hsub⟩ := h ε hε
    exact ⟨V, hV, hsub.mono fun n hn y hy _ ↦ hn y hy⟩

end SingleValued

end RW
