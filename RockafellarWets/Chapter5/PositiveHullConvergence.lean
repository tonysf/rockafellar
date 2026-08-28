/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Convergence of Positive Hulls

Exercise 5.54.

The Guide routes the exercise through the mapping `S(x) = pos{x}` and 5.53,
but that mapping is continuous only *relative to* the complement of a
neighborhood of the origin -- it has no continuous extension across `0`, since
`cl(gph S)` contains the whole fibre `{0} × IRⁿ` -- and the images of 5.30 and
5.53 are taken under mappings that are continuous everywhere.  The exercise is
therefore proved directly, which is also shorter: away from the origin a point
of `pos C` is a scalar multiple `a y` with `a` and `y` each confined to a
compact range, so both directions are one extraction each.

Both hypotheses on `C` are used exactly once.  Compactness gives the upper
bound on `‖y‖`, through eventual boundedness of the `Cν` by 4.25; `0 ∉ C`
gives the lower bound, through the eventual separation of the `Cν` from the
origin.  Between them they keep the coefficient `a = ‖u‖ / ‖y‖` in a compact
range, which is what the extraction needs.

The passage from ordinary to total convergence is the Guide's: positive hulls
are cones, so 4.25(b) applies.
-/

import RockafellarWets.Chapter3.PositiveHulls
import RockafellarWets.Chapter4.EventuallyBounded
import RockafellarWets.Chapter4.SetLimitCharacterizations
import RockafellarWets.Chapter4.TotalConvergenceAutomatic

open Bornology Filter Metric Set Topology

namespace RW

section Congr

variable {E : Type*} [TopologicalSpace E] {A B : ℕ → Set E}

/-- Set limits are tail-determined, so eventually equal families have equal
limits. -/
theorem outerSetLimit_congr (h : ∀ᶠ n in atTop, A n = B n) :
    outerSetLimit A = outerSetLimit B := by
  ext u
  simp only [mem_outerSetLimit]
  constructor
  · intro hu V hV
    refine (hu V hV).mp ?_
    filter_upwards [h] with n hn hmem
    rwa [hn] at hmem
  · intro hu V hV
    refine (hu V hV).mp ?_
    filter_upwards [h] with n hn hmem
    rwa [← hn] at hmem

theorem innerSetLimit_congr (h : ∀ᶠ n in atTop, A n = B n) :
    innerSetLimit A = innerSetLimit B := by
  ext u
  simp only [mem_innerSetLimit]
  constructor
  · intro hu V hV
    filter_upwards [hu V hV, h] with n hn hne
    rwa [hne] at hn
  · intro hu V hV
    filter_upwards [hu V hV, h] with n hn hne
    rwa [← hne] at hn

theorem PKConverges.congr {D : Set E} (h : ∀ᶠ n in atTop, A n = B n)
    (hA : PKConverges A D) : PKConverges B D :=
  ⟨(innerSetLimit_congr h).symm.trans hA.inner_eq,
    (outerSetLimit_congr h).symm.trans hA.outer_eq⟩

end Congr

section Separation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {Cseq : ℕ → Set E} {C : Set E}

/-- A convergent family stays eventually clear of any ball the limit misses.
Otherwise a point of the ball would be a cluster point, hence a point of the
limit. -/
theorem eventually_forall_norm_lt_of_outerSetLimit_subset
    (hC : outerSetLimit Cseq ⊆ C) {r : ℝ}
    (hr : ∀ z ∈ C, r < ‖z‖) :
    ∀ᶠ n in atTop, ∀ x ∈ Cseq n, r < ‖x‖ := by
  by_contra hcon
  rw [not_eventually] at hcon
  simp only [not_forall, not_lt, exists_prop] at hcon
  obtain ⟨φ, hφ, hpick⟩ := Filter.extraction_of_frequently_atTop hcon
  choose x hxC hxr using hpick
  have hbdd : IsBounded (Set.range x) :=
    (isBounded_closedBall (x := (0 : E)) (r := r)).subset (by
      rintro _ ⟨k, rfl⟩
      simpa only [mem_closedBall, dist_zero_right] using hxr k)
  obtain ⟨z, -, ψ, hψ, hz⟩ :=
    tendsto_subseq_of_bounded hbdd fun k ↦ Set.mem_range_self k
  have hzC : z ∈ C := hC (mem_outerSetLimit_iff_exists_subsequence.2
    ⟨φ ∘ ψ, x ∘ ψ, hφ.comp hψ, fun k ↦ hxC (ψ k), hz⟩)
  have hznorm : ‖z‖ ≤ r :=
    le_of_tendsto' (hz.norm) fun k ↦ hxr (ψ k)
  exact absurd (hr z hzC) (not_lt.2 hznorm)

/-- Total convergence to an empty limit forces the family to be eventually
empty: it is eventually bounded, and a nonempty tail would cluster. -/
theorem eventually_eq_empty_of_totalConverges_empty
    (hC : TotalConverges Cseq (∅ : Set E)) :
    ∀ᶠ n in atTop, Cseq n = (∅ : Set E) := by
  have hbdd : EventuallyBounded Cseq := by
    refine (horizonOuterSetLimit_eq_singleton_zero_iff_eventuallyBounded Cseq).1 ?_
    refine Subset.antisymm ?_ ?_
    · simpa using hC.horizonOuter_subset
    · rw [singleton_subset_iff]
      exact (isCone_horizonOuterSetLimit Cseq).1
  obtain ⟨r, N, hN⟩ := hbdd
  by_contra hcon
  rw [not_eventually] at hcon
  simp only [← Ne.eq_def, ← nonempty_iff_ne_empty] at hcon
  obtain ⟨φ, hφ, hpick⟩ :=
    Filter.extraction_of_frequently_atTop (hcon.and_eventually (eventually_ge_atTop N))
  choose x hxC using fun k ↦ (hpick k).1
  have hbd : IsBounded (Set.range x) :=
    (isBounded_closedBall (x := (0 : E)) (r := r)).subset (by
      rintro _ ⟨k, rfl⟩
      exact hN (φ k) (hpick k).2 (hxC k))
  obtain ⟨z, -, ψ, hψ, hz⟩ :=
    tendsto_subseq_of_bounded hbd fun k ↦ Set.mem_range_self k
  have : z ∈ outerSetLimit Cseq := mem_outerSetLimit_iff_exists_subsequence.2
    ⟨φ ∘ ψ, x ∘ ψ, hφ.comp hψ, fun k ↦ hxC (ψ k), hz⟩
  rw [hC.pkConverges.outer_eq] at this
  exact absurd this (notMem_empty z)

end Separation

section Exercise554

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {Cseq : ℕ → Set E} {C : Set E}

omit [FiniteDimensional ℝ E] in
/-- The inner half of 5.54: a point `a y` of `pos C` is approached by the
points `a z` for `z ∈ Cν` near `y`, the coefficient `a` staying fixed. -/
theorem positiveHull_subset_innerSetLimit_positiveHull
    (hC : C ⊆ innerSetLimit Cseq) :
    positiveHull C ⊆ innerSetLimit (fun n ↦ positiveHull (Cseq n)) := by
  intro u hu
  rcases mem_positiveHull.1 hu with rfl | ⟨a, ha, y, hyC, rfl⟩
  · intro V hV
    filter_upwards with n
    exact ⟨0, zero_mem_positiveHull _, mem_of_mem_nhds hV⟩
  · intro V hV
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hV
    filter_upwards [hC hyC (ball y (ε / a)) (ball_mem_nhds y (by positivity))]
      with n hn
    obtain ⟨z, hzC, hzball⟩ := hn
    refine ⟨a • z, mem_positiveHull.2 (Or.inr ⟨a, ha, z, hzC, rfl⟩), hball ?_⟩
    have hzy : ‖z - y‖ < ε / a := by rwa [mem_ball, dist_eq_norm] at hzball
    rw [mem_ball, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_pos ha]
    calc a * ‖z - y‖ < a * (ε / a) := by nlinarith [hzy, ha]
      _ = ε := by field_simp

/-- The outer half of 5.54.  Away from the origin a point of the limit is
`a y` with `y` a cluster point of the `Cν` and `a = ‖u‖ / ‖y‖`; the two-sided
bound on `‖y‖` is what keeps that quotient from degenerating. -/
theorem outerSetLimit_positiveHull_subset
    (hlim : outerSetLimit Cseq ⊆ C) {r M : ℝ} (hr : 0 < r)
    (hlow : ∀ᶠ n in atTop, ∀ x ∈ Cseq n, r < ‖x‖)
    (hup : ∀ᶠ n in atTop, ∀ x ∈ Cseq n, ‖x‖ ≤ M) :
    outerSetLimit (fun n ↦ positiveHull (Cseq n)) ⊆ positiveHull C := by
  intro u hu
  by_cases hu0 : u = 0
  · rw [hu0]
    exact zero_mem_positiveHull C
  obtain ⟨φ, w, hφ, hwmem, hwu⟩ := mem_outerSetLimit_iff_exists_subsequence.1 hu
  -- Past a common index the values are nonzero and both bounds apply.
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 hlow
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 (hwu.eventually_ne hu0)
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.1 hup
  set N := max (max N₁ N₂) N₃ with hNdef
  set φ' : ℕ → ℕ := fun k ↦ φ (k + N) with hφ'
  have hφ'mono : StrictMono φ' := fun i j hij ↦ hφ (by omega)
  have hφ'ge : ∀ k, N ≤ φ' k := fun k ↦ le_trans (by omega) (hφ.le_apply)
  have hwu' : Tendsto (fun k ↦ w (k + N)) atTop (nhds u) :=
    hwu.comp (tendsto_add_atTop_nat N)
  have hwne : ∀ k, w (k + N) ≠ 0 := fun k ↦ hN₂ _ (by omega)
  -- Split each value into a positive coefficient and a point of `Cν`.
  have hsplit : ∀ k, ∃ a : ℝ, 0 < a ∧ ∃ y ∈ Cseq (φ' k), w (k + N) = a • y := by
    intro k
    rcases mem_positiveHull.1 (hwmem (k + N)) with h0 | h
    · exact absurd h0 (hwne k)
    · exact h
  choose a hapos y hyC hwy using hsplit
  have hylow : ∀ k, r < ‖y k‖ := fun k ↦
    hN₁ _ (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (hφ'ge k)) _ (hyC k)
  have hyup : ∀ k, ‖y k‖ ≤ M := fun k ↦
    hN₃ _ (le_trans (le_max_right _ _) (hφ'ge k)) _ (hyC k)
  have hybdd : IsBounded (Set.range y) :=
    (isBounded_closedBall (x := (0 : E)) (r := M)).subset (by
      rintro _ ⟨k, rfl⟩
      simpa only [mem_closedBall, dist_zero_right] using hyup k)
  obtain ⟨z, -, ψ, hψ, hz⟩ :=
    tendsto_subseq_of_bounded hybdd fun k ↦ Set.mem_range_self k
  have hzC : z ∈ C := hlim (mem_outerSetLimit_iff_exists_subsequence.2
    ⟨φ' ∘ ψ, y ∘ ψ, hφ'mono.comp hψ, fun k ↦ hyC (ψ k), hz⟩)
  have hznorm : r ≤ ‖z‖ := ge_of_tendsto' hz.norm fun k ↦ (hylow (ψ k)).le
  have hzpos : (0 : ℝ) < ‖z‖ := lt_of_lt_of_le hr hznorm
  have hzne : ‖z‖ ≠ 0 := ne_of_gt hzpos
  -- The coefficients are the quotients of the norms, so they converge too.
  have hacoe : ∀ k, a k = ‖w (k + N)‖ / ‖y k‖ := by
    intro k
    have hy0 : ‖y k‖ ≠ 0 := ne_of_gt (hr.trans (hylow k))
    rw [hwy k, norm_smul, Real.norm_eq_abs, abs_of_pos (hapos k)]
    field_simp
  have haconv : Tendsto (fun k ↦ a (ψ k)) atTop (nhds (‖u‖ / ‖z‖)) := by
    simp only [hacoe]
    exact ((hwu'.comp hψ.tendsto_atTop).norm).div hz.norm hzne
  have hlimit : Tendsto (fun k ↦ w (ψ k + N)) atTop (nhds ((‖u‖ / ‖z‖) • z)) := by
    have : ∀ k, w (ψ k + N) = a (ψ k) • y (ψ k) := fun k ↦ hwy (ψ k)
    simp only [this]
    exact haconv.smul hz
  have hueq : u = (‖u‖ / ‖z‖) • z :=
    tendsto_nhds_unique (hwu'.comp hψ.tendsto_atTop) hlimit
  refine mem_positiveHull.2 (Or.inr ⟨‖u‖ / ‖z‖, ?_, z, hzC, hueq⟩)
  exact div_pos (norm_pos_iff.2 hu0) hzpos

/-- **Exercise 5.54**: positive hulls of totally convergent sets converge
totally, provided the limit is compact and misses the origin. -/
theorem totalConverges_positiveHull
    (hC : TotalConverges Cseq C) (hcomp : IsCompact C) (hzero : (0 : E) ∉ C) :
    TotalConverges (fun n ↦ positiveHull (Cseq n)) (positiveHull C) := by
  refine totalConverges_of_isCone ?_ (positiveHull_nonempty C)
    fun n ↦ isCone_positiveHull
  rcases eq_empty_or_nonempty C with rfl | hne
  · refine PKConverges.congr ?_ (pkConverges_const_of_isClosed
      (D := positiveHull (∅ : Set E)) (by rw [positiveHull_empty]; exact isClosed_singleton))
    filter_upwards [eventually_eq_empty_of_totalConverges_empty hC] with n hn
    rw [hn]
  · -- The limit is compact and misses the origin, so it is bounded away from it.
    have hd : 0 < infDist (0 : E) C := by
      rcases (hcomp.isClosed.mem_iff_infDist_zero hne (x := (0 : E))).not.1 hzero with h
      exact lt_of_le_of_ne infDist_nonneg (Ne.symm h)
    set r := infDist (0 : E) C / 2 with hrdef
    have hr : 0 < r := by positivity
    have hrC : ∀ z ∈ C, r < ‖z‖ := by
      intro z hz
      have : infDist (0 : E) C ≤ dist 0 z := infDist_le_dist_of_mem hz
      rw [dist_zero_left] at this
      simp only [hrdef]
      linarith
    have hlow := eventually_forall_norm_lt_of_outerSetLimit_subset
      hC.pkConverges.outer_eq.subset hrC
    -- Compactness of the limit makes the family eventually bounded, by 4.25.
    have hbdd : EventuallyBounded Cseq := by
      refine (horizonOuterSetLimit_eq_singleton_zero_iff_eventuallyBounded Cseq).1 ?_
      refine Subset.antisymm ?_ ?_
      · refine hC.horizonOuter_subset.trans ?_
        rw [isBounded_iff_horizonCone_eq_singleton_zero.mp hcomp.isBounded]
      · rw [singleton_subset_iff]
        exact (isCone_horizonOuterSetLimit Cseq).1
    obtain ⟨M, N, hMN⟩ := hbdd
    have hup : ∀ᶠ n in atTop, ∀ x ∈ Cseq n, ‖x‖ ≤ M := by
      filter_upwards [eventually_ge_atTop N] with n hn x hx
      simpa only [mem_closedBall, dist_zero_right] using hMN n hn hx
    have hinner := positiveHull_subset_innerSetLimit_positiveHull
      (Cseq := Cseq) hC.pkConverges.inner_eq.ge
    have houter := outerSetLimit_positiveHull_subset
      hC.pkConverges.outer_eq.subset hr hlow hup
    exact ⟨Subset.antisymm
        ((innerSetLimit_subset_outerSetLimit _).trans houter) hinner,
      Subset.antisymm houter
        (hinner.trans (innerSetLimit_subset_outerSetLimit _))⟩

end Exercise554

end RW
