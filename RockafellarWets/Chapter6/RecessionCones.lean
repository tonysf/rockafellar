/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Recession Vectors and Recession Cones

Definition 6.33 and Exercise 6.34 of Rockafellar & Wets, "Variational
Analysis" (book page 222).

A vector `w` is a *local recession vector* for `C` at `x̄ ∈ C`, written
`w ∈ R_C(x̄)`, when the whole short forward ray in the direction `w` stays in
`C` uniformly over base points near `x̄`: for some neighborhood `V` of `x̄` and
some `ε > 0` one has `x + τ • w ∈ C` for every `x ∈ C ∩ V` and every
`τ ∈ [0, ε]`.  It is a *global recession vector* when `x + τ • w ∈ C` for
every `x ∈ C` and every `τ ≥ 0`.

Conventions used here.

* `localRecessionCone C x̄` carries the feasibility requirement `x̄ ∈ C` in its
  definition, so it is *empty* at points off `C`
  (`localRecessionCone_eq_empty_of_not_mem`).  This keeps Definition 6.33
  attached to feasible base points, as printed.
* `globalRecessionCone C` is defined by the invariance of all forward rays.
  Its conditions are vacuous on the empty set, so
  `globalRecessionCone ∅ = univ`, matching the convention
  `⋂ x ∈ (∅ : Set E), localRecessionCone ∅ x = univ` for the empty
  intersection in Exercise 6.34(b).
* This repository uses `horizonCone ∅ = {0}` (Definition 3.3).  Hence the
  comparison of Exercise 6.34(c) genuinely needs `C.Nonempty`: for `C = ∅` the
  global recession set is `univ` while the horizon cone is `{0}`.  The
  nonemptiness hypothesis is recorded explicitly rather than dropped.
* Exercise 6.34(c) is stated for the ray-defined `globalRecessionCone`.  The
  identification of that set with `⋂ x ∈ C, localRecessionCone C x` is
  Exercise 6.34(b) and really does need closedness: for an *open* convex set
  every vector is locally recessive at every point, so the intersection is
  `univ` while the horizon cone can be `{0}`.

The main results are the local structure of Exercise 6.34(a) — including the
uniform statement for a finite family and its convex hull, valid for an
arbitrary set `C` — the local-to-global identity of Exercise 6.34(b) for
closed `C`, and the horizon cone comparison of Exercise 6.34(c).
-/

import RockafellarWets.Chapter6.RegularTangents
import RockafellarWets.Chapter3.Cones

open Filter Metric Set Topology
open scoped Pointwise

namespace RW

section Recession

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Definition 6.33 -/

/-- **Definition 6.33** (local recession vectors): `w ∈ R_C(x̄)` when `x̄ ∈ C`
and, for some neighborhood `V` of `x̄` and some `ε > 0`, one has
`x + τ • w ∈ C` for all `x ∈ C ∩ V` and all `τ ∈ [0, ε]`. -/
def localRecessionCone (C : Set E) (xbar : E) : Set E :=
  {w | xbar ∈ C ∧
    ∃ V ∈ nhds xbar, ∃ ε > 0,
      ∀ x ∈ C ∩ V, ∀ τ ∈ Set.Icc (0 : ℝ) ε,
        x + τ • w ∈ C}

/-- **Definition 6.33** (global recession vectors): `w` translates every
forward ray of `C` into `C`. -/
def globalRecessionCone (C : Set E) : Set E :=
  {w | ∀ x ∈ C, ∀ τ : ℝ, 0 ≤ τ → x + τ • w ∈ C}

theorem mem_localRecessionCone_iff {C : Set E} {xbar w : E} :
    w ∈ localRecessionCone C xbar ↔
      xbar ∈ C ∧ ∃ V ∈ nhds xbar, ∃ ε > 0,
        ∀ x ∈ C ∩ V, ∀ τ ∈ Set.Icc (0 : ℝ) ε, x + τ • w ∈ C :=
  Iff.rfl

/-- Introduction rule for Definition 6.33. -/
theorem mem_localRecessionCone {C : Set E} {xbar w : E} (hxbar : xbar ∈ C)
    {V : Set E} (hV : V ∈ nhds xbar) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ x ∈ C ∩ V, ∀ τ ∈ Set.Icc (0 : ℝ) ε, x + τ • w ∈ C) :
    w ∈ localRecessionCone C xbar :=
  ⟨hxbar, V, hV, ε, hε, h⟩

/-- Local recession vectors are only defined at feasible points. -/
theorem mem_of_mem_localRecessionCone {C : Set E} {xbar w : E}
    (hw : w ∈ localRecessionCone C xbar) : xbar ∈ C :=
  hw.1

/-- The off-set formula: away from `C` the local recession cone is empty. -/
theorem localRecessionCone_eq_empty_of_not_mem {C : Set E} {xbar : E}
    (hxbar : xbar ∉ C) : localRecessionCone C xbar = ∅ := by
  ext w
  simp only [Set.mem_empty_iff_false, iff_false]
  exact fun hw ↦ hxbar hw.1

@[simp] theorem localRecessionCone_empty (xbar : E) :
    localRecessionCone (∅ : Set E) xbar = ∅ :=
  localRecessionCone_eq_empty_of_not_mem (by simp)

/-- The metric reading of Definition 6.33. -/
theorem mem_localRecessionCone_iff_exists_ball {C : Set E} {xbar w : E} :
    w ∈ localRecessionCone C xbar ↔
      xbar ∈ C ∧ ∃ δ > 0, ∃ ε > 0, ∀ x ∈ C, dist x xbar < δ →
        ∀ τ ∈ Set.Icc (0 : ℝ) ε, x + τ • w ∈ C := by
  constructor
  · rintro ⟨hxbar, V, hV, ε, hε, h⟩
    obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp hV
    exact ⟨hxbar, δ, hδ, ε, hε, fun x hx hxd ↦
      h x ⟨hx, hsub (Metric.mem_ball.mpr hxd)⟩⟩
  · rintro ⟨hxbar, δ, hδ, ε, hε, h⟩
    exact ⟨hxbar, Metric.ball xbar δ, Metric.ball_mem_nhds _ hδ, ε, hε,
      fun x hx ↦ h x hx.1 (Metric.mem_ball.mp hx.2)⟩

/-- The filter reading of Definition 6.33: one step size `ε` works for all
base points in `C` near `x̄`. -/
theorem mem_localRecessionCone_iff_eventually {C : Set E} {xbar w : E} :
    w ∈ localRecessionCone C xbar ↔
      xbar ∈ C ∧ ∃ ε > 0, ∀ᶠ x in nhds xbar,
        x ∈ C → ∀ τ ∈ Set.Icc (0 : ℝ) ε, x + τ • w ∈ C := by
  constructor
  · rintro ⟨hxbar, V, hV, ε, hε, h⟩
    refine ⟨hxbar, ε, hε, ?_⟩
    filter_upwards [hV] with x hxV hxC
    exact h x ⟨hxC, hxV⟩
  · rintro ⟨hxbar, ε, hε, hev⟩
    obtain ⟨V, hV, hVsub⟩ := eventually_iff_exists_mem.mp hev
    exact ⟨hxbar, V, hV, ε, hε, fun x hx ↦ hVsub x hx.2 hx.1⟩

theorem mem_globalRecessionCone_iff {C : Set E} {w : E} :
    w ∈ globalRecessionCone C ↔ ∀ x ∈ C, ∀ τ : ℝ, 0 ≤ τ → x + τ • w ∈ C :=
  Iff.rfl

/-- The translation reading of a global recession vector: `C + τw ⊆ C` for
every `τ ≥ 0`. -/
theorem mem_globalRecessionCone_iff_add_smul_singleton_subset {C : Set E} {w : E} :
    w ∈ globalRecessionCone C ↔ ∀ τ : ℝ, 0 ≤ τ → C + τ • ({w} : Set E) ⊆ C := by
  constructor
  · intro hw τ hτ y hy
    rw [smul_set_singleton, Set.add_singleton, Set.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact hw x hx τ hτ
  · intro h x hx τ hτ
    refine h τ hτ ?_
    rw [smul_set_singleton, Set.add_singleton]
    exact ⟨x, hx, rfl⟩

@[simp] theorem globalRecessionCone_empty :
    globalRecessionCone (∅ : Set E) = Set.univ := by
  ext w
  simp [globalRecessionCone]

/-! ### Exercise 6.34(a): local structure -/

theorem zero_mem_localRecessionCone {C : Set E} {xbar : E} (hxbar : xbar ∈ C) :
    (0 : E) ∈ localRecessionCone C xbar :=
  mem_localRecessionCone hxbar Filter.univ_mem one_pos
    (by intro x hx τ _; simpa using hx.1)

theorem smul_mem_localRecessionCone {C : Set E} {xbar w : E}
    (hw : w ∈ localRecessionCone C xbar) {c : ℝ} (hc : 0 < c) :
    c • w ∈ localRecessionCone C xbar := by
  obtain ⟨hxbar, V, hV, ε, hε, h⟩ := hw
  refine mem_localRecessionCone hxbar hV (div_pos hε hc) ?_
  intro x hx τ hτ
  have hτc : τ * c ∈ Set.Icc (0 : ℝ) ε :=
    ⟨mul_nonneg hτ.1 hc.le, (le_div_iff₀ hc).mp hτ.2⟩
  simpa [smul_smul] using h x hx (τ * c) hτc

/-- **Exercise 6.34(a)**: the local recession vectors form a cone. -/
theorem isCone_localRecessionCone {C : Set E} {xbar : E} (hxbar : xbar ∈ C) :
    IsCone (localRecessionCone C xbar) :=
  ⟨zero_mem_localRecessionCone hxbar, fun _ hw _ hc ↦ smul_mem_localRecessionCone hw hc⟩

/-- The engine behind the uniform finite-family clause of Exercise 6.34(a).

For finitely many local recession vectors `w i`, `i ∈ s`, and any target
radius `r > 0`, there is one threshold `δ > 0` such that applying the
directions successively with nonnegative step sizes of total size less than
`δ`, starting from any point of `C` within `δ` of `x̄`, both stays in `C` and
stays within `r` of `x̄`.  The extra distance conclusion is what allows the
next direction to be applied: it keeps the intermediate points inside the
witnessing neighborhood of the direction that comes next. -/
theorem exists_pos_forall_add_sum_smul_mem {C : Set E} {xbar : E} {ι : Type*}
    (w : ι → E) (s : Finset ι) :
    (∀ i ∈ s, w i ∈ localRecessionCone C xbar) → ∀ r : ℝ, 0 < r →
      ∃ δ > 0, ∀ x ∈ C, dist x xbar < δ → ∀ t : ι → ℝ, (∀ i ∈ s, 0 ≤ t i) →
        ∑ i ∈ s, t i < δ →
          x + ∑ i ∈ s, t i • w i ∈ C ∧
            dist (x + ∑ i ∈ s, t i • w i) xbar < r := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro _ r hr
      refine ⟨min r 1, lt_min hr one_pos, ?_⟩
      intro x hx hxd t _ _
      simp only [Finset.sum_empty, add_zero]
      exact ⟨hx, lt_of_lt_of_le hxd (min_le_left _ _)⟩
  | @insert a s ha ih =>
      intro hw r hr
      obtain ⟨hxbar, V, hV, ε, hε, hVε⟩ := hw a (Finset.mem_insert_self a s)
      obtain ⟨ρ, hρ, hballV⟩ := Metric.mem_nhds_iff.mp hV
      obtain ⟨δ', hδ', H⟩ :=
        ih (fun i hi ↦ hw i (Finset.mem_insert_of_mem hi)) (min (r / 2) (ρ / 2))
          (lt_min (by linarith) (by linarith))
      have hNpos : (0 : ℝ) < 2 * (1 + ‖w a‖) := by positivity
      have hlast : (0 : ℝ) < r / (2 * (1 + ‖w a‖)) := div_pos hr hNpos
      refine ⟨min δ' (min ε (r / (2 * (1 + ‖w a‖)))), lt_min hδ' (lt_min hε hlast), ?_⟩
      intro x hx hxd t ht hts
      have hδδ' : min δ' (min ε (r / (2 * (1 + ‖w a‖)))) ≤ δ' := min_le_left _ _
      have hδε : min δ' (min ε (r / (2 * (1 + ‖w a‖)))) ≤ ε :=
        le_trans (min_le_right _ _) (min_le_left _ _)
      have hδr : min δ' (min ε (r / (2 * (1 + ‖w a‖)))) ≤ r / (2 * (1 + ‖w a‖)) :=
        le_trans (min_le_right _ _) (min_le_right _ _)
      have hta0 : 0 ≤ t a := ht a (Finset.mem_insert_self a s)
      have hsnn : 0 ≤ ∑ i ∈ s, t i :=
        Finset.sum_nonneg fun i hi ↦ ht i (Finset.mem_insert_of_mem hi)
      have hsplit : ∑ i ∈ insert a s, t i = t a + ∑ i ∈ s, t i := Finset.sum_insert ha
      have hsums : ∑ i ∈ s, t i < δ' := by
        have : ∑ i ∈ s, t i ≤ ∑ i ∈ insert a s, t i := by rw [hsplit]; linarith
        exact lt_of_le_of_lt this (lt_of_lt_of_le hts hδδ')
      obtain ⟨hyC, hyd⟩ :=
        H x hx (lt_of_lt_of_le hxd hδδ') t
          (fun i hi ↦ ht i (Finset.mem_insert_of_mem hi)) hsums
      have htas : t a ≤ ∑ i ∈ insert a s, t i := by rw [hsplit]; linarith
      have hyρ : dist (x + ∑ i ∈ s, t i • w i) xbar < ρ :=
        lt_of_lt_of_le (lt_of_lt_of_le hyd (min_le_right _ _)) (by linarith)
      have hyV : x + ∑ i ∈ s, t i • w i ∈ V := hballV (Metric.mem_ball.mpr hyρ)
      have htaε : t a ≤ ε := le_trans htas (le_trans hts.le hδε)
      have hstep : (x + ∑ i ∈ s, t i • w i) + t a • w a ∈ C :=
        hVε _ ⟨hyC, hyV⟩ (t a) ⟨hta0, htaε⟩
      have hrewrite : x + ∑ i ∈ insert a s, t i • w i
          = (x + ∑ i ∈ s, t i • w i) + t a • w a := by
        rw [Finset.sum_insert ha]; abel
      refine ⟨by rw [hrewrite]; exact hstep, ?_⟩
      rw [hrewrite]
      have htar : t a ≤ r / (2 * (1 + ‖w a‖)) :=
        le_trans htas (le_trans hts.le hδr)
      have hkey : r / (2 * (1 + ‖w a‖)) * (1 + ‖w a‖) = r / 2 := by
        have hne : (1 : ℝ) + ‖w a‖ ≠ 0 := by positivity
        field_simp
      have hnorm : ‖t a • w a‖ ≤ r / 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hta0]
        calc t a * ‖w a‖ ≤ t a * (1 + ‖w a‖) :=
              mul_le_mul_of_nonneg_left (by linarith) hta0
          _ ≤ r / (2 * (1 + ‖w a‖)) * (1 + ‖w a‖) :=
              mul_le_mul_of_nonneg_right htar (by positivity)
          _ = r / 2 := hkey
      have htri : dist ((x + ∑ i ∈ s, t i • w i) + t a • w a) xbar
          ≤ ‖t a • w a‖ + dist (x + ∑ i ∈ s, t i • w i) xbar := by
        calc dist ((x + ∑ i ∈ s, t i • w i) + t a • w a) xbar
            ≤ dist ((x + ∑ i ∈ s, t i • w i) + t a • w a) (x + ∑ i ∈ s, t i • w i)
              + dist (x + ∑ i ∈ s, t i • w i) xbar := dist_triangle _ _ _
          _ = ‖t a • w a‖ + dist (x + ∑ i ∈ s, t i • w i) xbar := by
              simp [dist_eq_norm]
      have hhalf : dist (x + ∑ i ∈ s, t i • w i) xbar < r / 2 :=
        lt_of_lt_of_le hyd (min_le_left _ _)
      linarith

/-- Convex combinations of a finite family described through the standard
simplex.  Only the forward inclusion is used below, but the equivalence is the
convenient reusable form. -/
theorem mem_convexHull_range_iff {ι : Type*} [Fintype ι] {w : ι → E} {z : E} :
    z ∈ convexHull ℝ (Set.range w) ↔
      ∃ lam : ι → ℝ, (∀ i, 0 ≤ lam i) ∧ ∑ i, lam i = 1 ∧ ∑ i, lam i • w i = z := by
  classical
  constructor
  · intro hz
    have hsub : convexHull ℝ (Set.range w) ⊆
        {z : E | ∃ lam : ι → ℝ,
          (∀ i, 0 ≤ lam i) ∧ ∑ i, lam i = 1 ∧ ∑ i, lam i • w i = z} := by
      refine convexHull_min ?_ ?_
      · rintro _ ⟨i, rfl⟩
        refine ⟨fun j ↦ if j = i then 1 else 0, fun j ↦ by positivity, by simp, ?_⟩
        simp
      · rintro z₀ ⟨lam₀, hlam₀, hsum₀, rfl⟩ z₁ ⟨lam₁, hlam₁, hsum₁, rfl⟩ p q hp hq hpq
        refine ⟨fun i ↦ p * lam₀ i + q * lam₁ i,
          fun i ↦ add_nonneg (mul_nonneg hp (hlam₀ i)) (mul_nonneg hq (hlam₁ i)), ?_, ?_⟩
        · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum₀, hsum₁]
          simpa using hpq
        · rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [add_smul, smul_smul, smul_smul]
    exact hsub hz
  · rintro ⟨lam, hlam, hsum, rfl⟩
    exact (convex_convexHull ℝ (Set.range w)).sum_mem (fun i _ ↦ hlam i) hsum
      (fun i _ ↦ subset_convexHull ℝ _ ⟨i, rfl⟩)

/-- **Exercise 6.34(a)**, uniform finite-family clause: if `w i ∈ R_C(x̄)` for
every member of a finite family, then one neighborhood `V` of `x̄` and one step
bound `ε > 0` serve *all* directions in the convex hull `con{w i}`
simultaneously, i.e. `x + τ • z ∈ C` for `x ∈ C ∩ V`, `τ ∈ [0, ε]` and
`z ∈ con{w i}`.

The set `C` is arbitrary here; convexity of `C` is not used.  Note that the
convex hull cannot be replaced by the conic hull: a uniform positive step
bound would then be false. -/
theorem exists_nhds_forall_smul_mem_of_mem_convexHull_range {C : Set E} {xbar : E}
    {ι : Type*} [Finite ι] {w : ι → E}
    (hw : ∀ i, w i ∈ localRecessionCone C xbar) :
    ∃ V ∈ nhds xbar, ∃ ε > 0, ∀ x ∈ C ∩ V, ∀ τ ∈ Set.Icc (0 : ℝ) ε,
      ∀ z ∈ convexHull ℝ (Set.range w), x + τ • z ∈ C := by
  classical
  haveI := Fintype.ofFinite ι
  obtain ⟨δ, hδ, H⟩ :=
    exists_pos_forall_add_sum_smul_mem w Finset.univ (fun i _ ↦ hw i) 1 one_pos
  refine ⟨Metric.ball xbar δ, Metric.ball_mem_nhds _ hδ, δ / 2, half_pos hδ, ?_⟩
  intro x hx τ hτ z hz
  obtain ⟨lam, hlam, hsum, rfl⟩ := mem_convexHull_range_iff.mp hz
  have hcoef : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ τ * lam i :=
    fun i _ ↦ mul_nonneg hτ.1 (hlam i)
  have hsmall : ∑ i, τ * lam i < δ := by
    rw [← Finset.mul_sum, hsum, mul_one]
    exact lt_of_le_of_lt hτ.2 (by linarith)
  have hmem := (H x hx.1 (Metric.mem_ball.mp hx.2) (fun i ↦ τ * lam i) hcoef hsmall).1
  have hrw : ∑ i, (τ * lam i) • w i = τ • ∑ i, lam i • w i := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [smul_smul]
  rwa [hrw] at hmem

/-- The printed form of the uniform clause in Exercise 6.34(a):
`x + τW ⊆ C` for all `x ∈ C ∩ V` and `τ ∈ [0, ε]`, where `W` is the convex
hull of the finite family. -/
theorem exists_nhds_forall_singleton_add_smul_convexHull_subset {C : Set E} {xbar : E}
    {ι : Type*} [Finite ι] {w : ι → E}
    (hw : ∀ i, w i ∈ localRecessionCone C xbar) :
    ∃ V ∈ nhds xbar, ∃ ε > 0, ∀ x ∈ C ∩ V, ∀ τ ∈ Set.Icc (0 : ℝ) ε,
      {x} + τ • convexHull ℝ (Set.range w) ⊆ C := by
  obtain ⟨V, hV, ε, hε, H⟩ := exists_nhds_forall_smul_mem_of_mem_convexHull_range hw
  refine ⟨V, hV, ε, hε, ?_⟩
  intro x hx τ hτ y hy
  rw [Set.singleton_add, Set.mem_image] at hy
  obtain ⟨u, hu, rfl⟩ := hy
  obtain ⟨z, hz, rfl⟩ := Set.mem_smul_set.mp hu
  exact H x hx τ hτ z hz

/-- The finite-set version of the uniform clause of Exercise 6.34(a). -/
theorem exists_nhds_forall_smul_mem_of_mem_convexHull {C : Set E} {xbar : E}
    {W : Set E} (hWfin : W.Finite) (hW : W ⊆ localRecessionCone C xbar) :
    ∃ V ∈ nhds xbar, ∃ ε > 0, ∀ x ∈ C ∩ V, ∀ τ ∈ Set.Icc (0 : ℝ) ε,
      ∀ z ∈ convexHull ℝ W, x + τ • z ∈ C := by
  haveI : Finite (W : Type _) := hWfin.to_subtype
  obtain ⟨V, hV, ε, hε, H⟩ :=
    exists_nhds_forall_smul_mem_of_mem_convexHull_range
      (C := C) (xbar := xbar) (w := (Subtype.val : W → E)) (fun i ↦ hW i.2)
  refine ⟨V, hV, ε, hε, fun x hx τ hτ z hz ↦ H x hx τ hτ z ?_⟩
  rwa [Subtype.range_coe]

/-- **Exercise 6.34(a)**: the local recession cone is convex.  This is the
two-direction case of the uniform finite-family clause; note that `C` itself
need not be convex. -/
theorem convex_localRecessionCone {C : Set E} {xbar : E} :
    Convex ℝ (localRecessionCone C xbar) := by
  by_cases hxbar : xbar ∈ C
  · intro w₀ h₀ w₁ h₁ p q hp hq hpq
    have hw2 : ∀ i : Fin 2, ![w₀, w₁] i ∈ localRecessionCone C xbar := by
      intro i
      fin_cases i
      · simpa using h₀
      · simpa using h₁
    obtain ⟨V, hV, ε, hε, H⟩ :=
      exists_nhds_forall_smul_mem_of_mem_convexHull_range hw2
    refine mem_localRecessionCone hxbar hV hε ?_
    intro x hx τ hτ
    refine H x hx τ hτ _ ?_
    refine mem_convexHull_range_iff.mpr ⟨![p, q], ?_, ?_, ?_⟩
    · intro i
      fin_cases i
      · simpa using hp
      · simpa using hq
    · simpa using hpq
    · simp
  · rw [localRecessionCone_eq_empty_of_not_mem hxbar]
    exact convex_empty

theorem add_mem_localRecessionCone {C : Set E} {xbar w₀ w₁ : E}
    (h₀ : w₀ ∈ localRecessionCone C xbar) (h₁ : w₁ ∈ localRecessionCone C xbar) :
    w₀ + w₁ ∈ localRecessionCone C xbar :=
  add_mem_of_convex_isCone convex_localRecessionCone
    (isCone_localRecessionCone h₀.1) h₀ h₁

/-- **Exercise 6.34(a)**: every local recession vector is a *regular* tangent
vector.  Given base points `x̄ₙ → x̄` in `C` and scales `τₙ ↓ 0`, the points
`x̄ₙ + τₙ w` eventually lie in `C` and realize the difference quotient `w`
exactly. -/
theorem localRecessionCone_subset_regularTangentCone {C : Set E} {xbar : E} :
    localRecessionCone C xbar ⊆ regularTangentCone C xbar := by
  classical
  rintro w ⟨hxbar, V, hV, ε, hε, hVε⟩
  rw [mem_regularTangentCone_iff_forall_sequences hxbar]
  intro τs xbars hτpos hτ0 hxbarC hxbarto
  refine ⟨fun n ↦ xbars n + (if xbars n ∈ V ∧ τs n ≤ ε then τs n • w else 0), ?_, ?_, ?_⟩
  · intro n
    by_cases h : xbars n ∈ V ∧ τs n ≤ ε
    · simp only [if_pos h]
      exact hVε (xbars n) ⟨hxbarC n, h.1⟩ (τs n) ⟨(hτpos n).le, h.2⟩
    · simpa only [if_neg h, add_zero] using hxbarC n
  · have hd : Tendsto
        (fun n ↦ if xbars n ∈ V ∧ τs n ≤ ε then τs n • w else (0 : E)) atTop (nhds 0) := by
      refine squeeze_zero_norm (fun n ↦ ?_) (by simpa using hτ0.mul_const ‖w‖)
      by_cases h : xbars n ∈ V ∧ τs n ≤ ε
      · simp only [if_pos h, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hτpos n).le]
        exact le_rfl
      · simp only [if_neg h, norm_zero]
        exact mul_nonneg (hτpos n).le (norm_nonneg w)
    simpa using hxbarto.add hd
  · have hVev : ∀ᶠ n in atTop, xbars n ∈ V := hxbarto.eventually_mem hV
    have hτev : ∀ᶠ n in atTop, τs n < ε := hτ0.eventually_mem (Iio_mem_nhds hε)
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hVev, hτev] with n hn hn'
    have hcond : xbars n ∈ V ∧ τs n ≤ ε := ⟨hn, hn'.le⟩
    simp only [add_sub_cancel_left, if_pos hcond]
    rw [smul_smul, inv_mul_cancel₀ (hτpos n).ne', one_smul]

theorem localRecessionCone_subset_derivableCone {C : Set E} {xbar : E} :
    localRecessionCone C xbar ⊆ derivableCone C xbar := fun _ hw ↦
  regularTangentCone_subset_derivableCone hw.1
    (localRecessionCone_subset_regularTangentCone hw)

theorem localRecessionCone_subset_tangentCone {C : Set E} {xbar : E} :
    localRecessionCone C xbar ⊆ tangentCone C xbar := fun _ hw ↦
  regularTangentCone_subset_tangentCone hw.1
    (localRecessionCone_subset_regularTangentCone hw)

/-! ### Exercise 6.34(b): global structure -/

theorem zero_mem_globalRecessionCone (C : Set E) : (0 : E) ∈ globalRecessionCone C := by
  intro x hx τ _
  simpa using hx

theorem smul_mem_globalRecessionCone {C : Set E} {w : E}
    (hw : w ∈ globalRecessionCone C) {c : ℝ} (hc : 0 ≤ c) :
    c • w ∈ globalRecessionCone C := by
  intro x hx τ hτ
  simpa [smul_smul] using hw x hx (τ * c) (mul_nonneg hτ hc)

theorem add_mem_globalRecessionCone {C : Set E} {w₀ w₁ : E}
    (h₀ : w₀ ∈ globalRecessionCone C) (h₁ : w₁ ∈ globalRecessionCone C) :
    w₀ + w₁ ∈ globalRecessionCone C := by
  intro x hx τ hτ
  rw [smul_add, ← add_assoc]
  exact h₁ _ (h₀ x hx τ hτ) τ hτ

/-- **Exercise 6.34(b)**: the global recession vectors form a cone, for an
arbitrary set `C`. -/
theorem isCone_globalRecessionCone (C : Set E) : IsCone (globalRecessionCone C) :=
  ⟨zero_mem_globalRecessionCone C, fun _ hw _ hc ↦ smul_mem_globalRecessionCone hw hc.le⟩

/-- **Exercise 6.34(b)**: the global recession vectors form a convex set, for
an arbitrary set `C`. -/
theorem convex_globalRecessionCone (C : Set E) : Convex ℝ (globalRecessionCone C) :=
  ((isCone_globalRecessionCone C).convex_iff_add_mem).2
    fun _ _ hw₀ hw₁ ↦ add_mem_globalRecessionCone hw₀ hw₁

/-- **Exercise 6.34(b)**: the global recession cone of a closed set is
closed. -/
theorem isClosed_globalRecessionCone {C : Set E} (hC : IsClosed C) :
    IsClosed (globalRecessionCone C) := by
  have heq : globalRecessionCone C =
      ⋂ x ∈ C, ⋂ τ ∈ Set.Ici (0 : ℝ), (fun v : E ↦ x + τ • v) ⁻¹' C := by
    ext v
    simp only [globalRecessionCone, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage,
      Set.mem_Ici]
  rw [heq]
  refine isClosed_biInter fun x _ ↦ isClosed_biInter fun τ _ ↦ hC.preimage ?_
  exact continuous_const.add (continuous_const_smul τ)

theorem globalRecessionCone_subset_localRecessionCone {C : Set E} {x : E} (hx : x ∈ C) :
    globalRecessionCone C ⊆ localRecessionCone C x := fun _ hw ↦
  mem_localRecessionCone hx Filter.univ_mem one_pos
    fun y hy τ hτ ↦ hw y hy.1 τ hτ.1

theorem globalRecessionCone_subset_iInter_localRecessionCone (C : Set E) :
    globalRecessionCone C ⊆ ⋂ x ∈ C, localRecessionCone C x :=
  Set.subset_iInter₂ fun _ hx ↦ globalRecessionCone_subset_localRecessionCone hx

/-- **Exercise 6.34(b)**: for a closed set the global recession vectors are
exactly the vectors that are locally recessive at every point of `C`.

The nontrivial inclusion is the printed last-contact argument: if the forward
ray from `x ∈ C` leaves `C` before the parameter `τ`, then the ray has a last
contact point `x̃ = x + σ • w` with `C`, and local recessiveness of `w` at `x̃`
produces contact points beyond `σ`. -/
theorem globalRecessionCone_eq_iInter_localRecessionCone {C : Set E} (hC : IsClosed C) :
    globalRecessionCone C = ⋂ x ∈ C, localRecessionCone C x := by
  refine Set.Subset.antisymm (globalRecessionCone_subset_iInter_localRecessionCone C) ?_
  intro w hw
  have hw' : ∀ x ∈ C, w ∈ localRecessionCone C x := by
    intro x hx
    exact Set.mem_iInter₂.mp hw x hx
  intro x hx τ hτ
  by_contra hcon
  set K : Set ℝ := Set.Icc 0 τ ∩ (fun σ : ℝ ↦ x + σ • w) ⁻¹' C with hK
  have hcont : Continuous fun σ : ℝ ↦ x + σ • w :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hKcompact : IsCompact K := isCompact_Icc.inter_right (hC.preimage hcont)
  have hKne : K.Nonempty := ⟨0, ⟨le_refl 0, hτ⟩, by simpa using hx⟩
  have hmem : sSup K ∈ K := hKcompact.sSup_mem hKne
  obtain ⟨⟨hσ0, hστ⟩, hσC⟩ := hmem
  have hσlt : sSup K < τ := by
    rcases lt_or_eq_of_le hστ with h | h
    · exact h
    · exact absurd (by rw [← h]; exact hσC) hcon
  obtain ⟨-, V, hV, ε, hε, hVε⟩ := hw' _ hσC
  set η : ℝ := min ε (τ - sSup K) with hη
  have hηpos : 0 < η := lt_min hε (by linarith)
  have hstep : (x + sSup K • w) + η • w ∈ C :=
    hVε _ ⟨hσC, mem_of_mem_nhds hV⟩ η ⟨hηpos.le, min_le_left _ _⟩
  have hsum : x + (sSup K + η) • w ∈ C := by
    rw [add_smul, ← add_assoc]; exact hstep
  have hmemK : sSup K + η ∈ K := by
    refine ⟨⟨by linarith, ?_⟩, hsum⟩
    have : η ≤ τ - sSup K := min_le_right _ _
    linarith
  have hle : sSup K + η ≤ sSup K := le_csSup hKcompact.bddAbove hmemK
  linarith

/-- **Exercise 6.34(b)**: for closed `C` the intersection of the local
recession cones is convex. -/
theorem convex_iInter_localRecessionCone {C : Set E} (hC : IsClosed C) :
    Convex ℝ (⋂ x ∈ C, localRecessionCone C x) := by
  rw [← globalRecessionCone_eq_iInter_localRecessionCone hC]
  exact convex_globalRecessionCone C

/-- **Exercise 6.34(b)**: for closed `C` the intersection of the local
recession cones is a cone. -/
theorem isCone_iInter_localRecessionCone {C : Set E} (hC : IsClosed C) :
    IsCone (⋂ x ∈ C, localRecessionCone C x) := by
  rw [← globalRecessionCone_eq_iInter_localRecessionCone hC]
  exact isCone_globalRecessionCone C

/-- **Exercise 6.34(b)**: for closed `C` the intersection of the local
recession cones is closed. -/
theorem isClosed_iInter_localRecessionCone {C : Set E} (hC : IsClosed C) :
    IsClosed (⋂ x ∈ C, localRecessionCone C x) := by
  rw [← globalRecessionCone_eq_iInter_localRecessionCone hC]
  exact isClosed_globalRecessionCone hC

/-- The empty-set convention of Exercise 6.34(b): the empty intersection is
`univ`, which is exactly the vacuously defined global recession set of `∅`. -/
@[simp] theorem iInter_localRecessionCone_empty :
    (⋂ x ∈ (∅ : Set E), localRecessionCone (∅ : Set E) x) = Set.univ := by
  simp

/-! ### Exercise 6.34(c): comparison with the horizon cone -/

/-- **Exercise 6.34(c)**, first half: global recession vectors are horizon
vectors.  Nonemptiness of `C` is needed because `horizonCone ∅ = {0}` whereas
the global recession conditions are vacuous on `∅`.  Convexity is not needed
for this inclusion. -/
theorem globalRecessionCone_subset_horizonCone {C : Set E} (hne : C.Nonempty) :
    globalRecessionCone C ⊆ horizonCone C := by
  intro w hw
  obtain ⟨x, hx⟩ := hne
  refine mem_horizonCone_of_forall_smul_add_mem (x := x) ?_
  intro τ hτ
  rw [add_comm]
  exact hw x hx τ hτ

/-- **Exercise 6.34(c)** as printed, for a nonempty convex set.  The convexity
hypothesis is carried only to match the book; it is not used, as
`globalRecessionCone_subset_horizonCone` shows. -/
theorem globalRecessionCone_subset_horizonCone_of_convex {C : Set E}
    (_hconv : Convex ℝ C) (hne : C.Nonempty) :
    globalRecessionCone C ⊆ horizonCone C :=
  globalRecessionCone_subset_horizonCone hne

/-- **Exercise 6.34(c)**, second half: for a closed convex set every horizon
vector is a global recession vector (Theorem 3.6). -/
theorem horizonCone_subset_globalRecessionCone {C : Set E} (hconv : Convex ℝ C)
    (hC : IsClosed C) : horizonCone C ⊆ globalRecessionCone C := by
  intro w hw x hx τ hτ
  rw [add_comm]
  exact smul_add_mem_of_mem_horizonCone hconv hC hx hw hτ

/-- **Exercise 6.34(c)**: for a nonempty closed convex set the global
recession cone *is* the horizon cone. -/
theorem globalRecessionCone_eq_horizonCone {C : Set E} (hne : C.Nonempty)
    (hconv : Convex ℝ C) (hC : IsClosed C) :
    globalRecessionCone C = horizonCone C :=
  Set.Subset.antisymm (globalRecessionCone_subset_horizonCone hne)
    (horizonCone_subset_globalRecessionCone hconv hC)

/-- **Exercise 6.34(b)(c)** combined: for a nonempty closed convex set the
intersection of the local recession cones is the horizon cone. -/
theorem iInter_localRecessionCone_eq_horizonCone {C : Set E} (hne : C.Nonempty)
    (hconv : Convex ℝ C) (hC : IsClosed C) :
    (⋂ x ∈ C, localRecessionCone C x) = horizonCone C := by
  rw [← globalRecessionCone_eq_iInter_localRecessionCone hC]
  exact globalRecessionCone_eq_horizonCone hne hconv hC

end Recession

end RW
