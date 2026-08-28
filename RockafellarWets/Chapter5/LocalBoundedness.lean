/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Local Boundedness

Definition 5.14 asks that `S` carry some neighborhood of the base point into
a single bounded set; Proposition 5.15 upgrades this from neighborhoods to
arbitrary bounded sets, and Exercise 5.16 reads the resulting condition off
the inverse.

The image `S(V) = ⋃ {S(x) | x ∈ V}` of a set under a set-valued mapping is
introduced here, since Chapter 5 has not needed it before.  Note that local
boundedness is not a nonemptiness condition: at a point outside `cl(dom S)`
it holds vacuously, because a whole neighborhood there has empty image.
-/

import Mathlib.Analysis.Normed.Module.Basic
import RockafellarWets.Chapter5.SemicontinuityCriteria

open Bornology Filter Metric Set Topology

namespace RW

section Images

variable {E F : Type*}

/-- The image `S(V) = ⋃ {S(x) | x ∈ V}` of a set under a set-valued
mapping. -/
def svImage (S : E → Set F) (V : Set E) : Set F := ⋃ x ∈ V, S x

@[simp]
theorem mem_svImage {S : E → Set F} {V : Set E} {u : F} :
    u ∈ svImage S V ↔ ∃ x ∈ V, u ∈ S x := by
  simp [svImage]

theorem svImage_mono {S : E → Set F} {V W : Set E} (h : V ⊆ W) :
    svImage S V ⊆ svImage S W := by
  intro u hu
  obtain ⟨x, hx, hux⟩ := mem_svImage.1 hu
  exact mem_svImage.2 ⟨x, h hx, hux⟩

theorem subset_svImage {S : E → Set F} {V : Set E} {x : E} (hx : x ∈ V) :
    S x ⊆ svImage S V :=
  fun _ hu ↦ mem_svImage.2 ⟨x, hx, hu⟩

theorem svImage_univ (S : E → Set F) : svImage S univ = svRange S := by
  ext u
  simp [svRange]

theorem svImage_iUnion {ι : Sort*} (S : E → Set F) (W : ι → Set E) :
    svImage S (⋃ i, W i) = ⋃ i, svImage S (W i) := by
  ext u
  simp only [mem_svImage, mem_iUnion]
  constructor
  · rintro ⟨x, ⟨i, hi⟩, hux⟩
    exact ⟨i, x, hi, hux⟩
  · rintro ⟨i, x, hi, hux⟩
    exact ⟨x, ⟨i, hi⟩, hux⟩

theorem svImage_eq_empty_iff {S : E → Set F} {V : Set E} :
    svImage S V = ∅ ↔ V ∩ svDom S = ∅ := by
  constructor
  · intro h
    rw [eq_empty_iff_forall_notMem]
    rintro x ⟨hxV, u, hu⟩
    have hmem : u ∈ svImage S V := mem_svImage.2 ⟨x, hxV, hu⟩
    rw [h] at hmem
    exact hmem
  · intro h
    rw [eq_empty_iff_forall_notMem]
    intro u hu
    obtain ⟨x, hxV, hux⟩ := mem_svImage.1 hu
    have hmem : x ∈ V ∩ svDom S := ⟨hxV, u, hux⟩
    rw [h] at hmem
    exact hmem

end Images

section Definition514

variable {E F : Type*} [TopologicalSpace E] [PseudoMetricSpace F]

/-- **Definition 5.14**: `S` is locally bounded at `x` when it carries some
neighborhood of `x` into a bounded set. -/
def SvLocallyBoundedAt (S : E → Set F) (x : E) : Prop :=
  ∃ V ∈ nhds x, IsBounded (svImage S V)

/-- **Definition 5.14**: `S` is locally bounded when it is so at every
point. -/
def SvLocallyBounded (S : E → Set F) : Prop := ∀ x, SvLocallyBoundedAt S x

/-- **Definition 5.14**: `S` is bounded when its range is. -/
def SvBounded (S : E → Set F) : Prop := IsBounded (svRange S)

/-- Local boundedness at `x` requires `S(x)` itself to be bounded. -/
theorem SvLocallyBoundedAt.isBounded_apply {S : E → Set F} {x : E}
    (h : SvLocallyBoundedAt S x) : IsBounded (S x) := by
  obtain ⟨V, hV, hbdd⟩ := h
  exact hbdd.subset (subset_svImage (mem_of_mem_nhds hV))

/-- A bounded mapping is locally bounded. -/
theorem SvBounded.svLocallyBounded {S : E → Set F} (h : SvBounded S) :
    SvLocallyBounded S := fun x ↦
  ⟨univ, univ_mem, by rwa [svImage_univ]⟩

/-- The remark after 5.14: local boundedness holds vacuously off the closure
of the domain, since a neighborhood there has empty image. -/
theorem svLocallyBoundedAt_of_notMem_closure_svDom {S : E → Set F} {x : E}
    (hx : x ∉ closure (svDom S)) : SvLocallyBoundedAt S x := by
  refine ⟨(closure (svDom S))ᶜ, isClosed_closure.isOpen_compl.mem_nhds hx, ?_⟩
  rw [svImage_eq_empty_iff.2 ?_]
  · exact isBounded_empty
  · rw [eq_empty_iff_forall_notMem]
    rintro z ⟨hz₁, hz₂⟩
    exact hz₁ (subset_closure hz₂)

end Definition514

section BallForm

variable {E F : Type*} [PseudoMetricSpace E] [NormedAddCommGroup F]

/-- **Definition 5.14** in the book's explicit form: local boundedness at `x`
says that `S(IB(x, δ)) ⊂ IB(0, ρ)` for some `δ > 0` and `ρ > 0`. -/
theorem svLocallyBoundedAt_iff_exists_closedBall {S : E → Set F} {x : E} :
    SvLocallyBoundedAt S x ↔
      ∃ δ > 0, ∃ ρ > 0, svImage S (closedBall x δ) ⊆ closedBall 0 ρ := by
  constructor
  · rintro ⟨V, hV, hbdd⟩
    obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.1 hV
    obtain ⟨ρ, hρ⟩ := (isBounded_iff_subset_closedBall (0 : F)).1 hbdd
    refine ⟨δ / 2, by positivity, max ρ 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
    refine subset_trans ?_ (subset_trans hρ (closedBall_subset_closedBall (le_max_left _ _)))
    exact svImage_mono fun z hz ↦
      hδV (mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hz) (by linarith)))
  · rintro ⟨δ, hδ, ρ, _, hsub⟩
    exact ⟨closedBall x δ, closedBall_mem_nhds x hδ,
      (isBounded_closedBall).subset hsub⟩

end BallForm

section BoundedImages

variable {E F : Type*} [PseudoMetricSpace E] [ProperSpace E]
variable [PseudoMetricSpace F]

/-- **Proposition 5.15.**  Local boundedness is exactly the property of
carrying bounded sets to bounded sets.

Sufficiency is immediate from a bounded neighborhood.  Necessity covers the
compact set `cl B` by finitely many neighborhoods with bounded images and
takes the union. -/
theorem svLocallyBounded_iff_isBounded_svImage {S : E → Set F} :
    SvLocallyBounded S ↔ ∀ B : Set E, IsBounded B → IsBounded (svImage S B) := by
  constructor
  · intro h B hB
    have hcl : IsCompact (closure B) := hB.isCompact_closure
    choose! V hVnhds hVbdd using h
    obtain ⟨t, htcl, hcover⟩ := hcl.elim_nhds_subcover V fun x _ ↦ hVnhds x
    have hsub : svImage S B ⊆ svImage S (⋃ x ∈ t, V x) :=
      svImage_mono (subset_closure.trans hcover)
    refine IsBounded.subset ?_ hsub
    simp only [svImage_iUnion]
    exact (isBounded_biUnion_finset t).2 fun a _ ↦ hVbdd a
  · intro h x
    exact ⟨ball x 1, ball_mem_nhds x one_pos, h _ isBounded_ball⟩

end BoundedImages

section SequentialBoundedness

variable {E F : Type*} [PseudoMetricSpace E] [ProperSpace E]
variable [NormedAddCommGroup F]

/-- **Proposition 5.15**, sequential form: local boundedness says that
bounded sequences of arguments have bounded sequences of values. -/
theorem svLocallyBounded_iff_seq {S : E → Set F} :
    SvLocallyBounded S ↔
      ∀ (xs : ℕ → E) (us : ℕ → F), (∀ n, us n ∈ S (xs n)) →
        IsBounded (range xs) → IsBounded (range us) := by
  rw [svLocallyBounded_iff_isBounded_svImage]
  constructor
  · intro h xs us hmem hbdd
    refine (h _ hbdd).subset ?_
    rintro u ⟨n, rfl⟩
    exact mem_svImage.2 ⟨xs n, mem_range_self n, hmem n⟩
  · intro h B hB
    by_contra hnot
    rw [isBounded_iff_subset_closedBall (0 : F)] at hnot
    push_neg at hnot
    have hpick : ∀ n : ℕ, ∃ u ∈ svImage S B, (n : ℝ) < ‖u‖ := by
      intro n
      obtain ⟨u, huS, hu⟩ := Set.not_subset.1 (hnot n)
      exact ⟨u, huS, by simpa [mem_closedBall, dist_zero_right] using hu⟩
    choose us husImage husnorm using hpick
    choose xs hxsB hxsmem using fun n ↦ mem_svImage.1 (husImage n)
    have hxbdd : IsBounded (range xs) := hB.subset (range_subset_iff.2 hxsB)
    obtain ⟨r, hr⟩ :=
      (isBounded_iff_subset_closedBall (0 : F)).1 (h xs us hxsmem hxbdd)
    obtain ⟨n, hn⟩ := exists_nat_gt r
    have : ‖us n‖ ≤ r := by
      simpa [mem_closedBall, dist_zero_right] using hr (mem_range_self n)
    linarith [husnorm n]

end SequentialBoundedness

section InverseBoundedness

variable {E F : Type*} [NormedAddCommGroup E]
variable [NormedAddCommGroup F] [ProperSpace F]

/-- An unbounded set carries a sequence whose norms diverge. -/
private theorem exists_seq_norm_atTop {A : Set E} (h : ¬ IsBounded A) :
    ∃ a : ℕ → E, (∀ n, a n ∈ A) ∧ Tendsto (fun n ↦ ‖a n‖) atTop atTop := by
  rw [isBounded_iff_subset_closedBall (0 : E)] at h
  push_neg at h
  have hpick : ∀ n : ℕ, ∃ y ∈ A, (n : ℝ) < ‖y‖ := by
    intro n
    obtain ⟨y, hyA, hy⟩ := Set.not_subset.1 (h n)
    exact ⟨y, hyA, by simpa [mem_closedBall, dist_zero_right] using hy⟩
  choose a haA hanorm using hpick
  refine ⟨a, haA, tendsto_atTop_mono (fun n ↦ (hanorm n).le) ?_⟩
  exact tendsto_natCast_atTop_atTop

/-- **Exercise 5.16.**  The inverse of `S` is locally bounded exactly when
arguments escaping to infinity force their values to escape too. -/
theorem svLocallyBounded_svInv_iff {S : E → Set F} :
    SvLocallyBounded (svInv S) ↔
      ∀ (xs : ℕ → E) (us : ℕ → F), (∀ n, us n ∈ S (xs n)) →
        Tendsto (fun n ↦ ‖xs n‖) atTop atTop →
        Tendsto (fun n ↦ ‖us n‖) atTop atTop := by
  rw [svLocallyBounded_iff_isBounded_svImage]
  constructor
  · intro h xs us hmem hxs
    by_contra hnot
    rw [tendsto_atTop_atTop] at hnot
    push_neg at hnot
    obtain ⟨b, hb⟩ := hnot
    have hfreq : ∃ᶠ n in atTop, ‖us n‖ < b := by
      rw [Filter.frequently_atTop]
      intro N
      obtain ⟨n, hn, hlt⟩ := hb N
      exact ⟨n, hn, hlt⟩
    obtain ⟨φ, hφ, hφlt⟩ := extraction_of_frequently_atTop hfreq
    have hball : IsBounded (closedBall (0 : F) b) := isBounded_closedBall
    have hbdd := h _ hball
    obtain ⟨r, hr⟩ := (isBounded_iff_subset_closedBall (0 : E)).1 hbdd
    have hxin : ∀ n, xs (φ n) ∈ svImage (svInv S) (closedBall (0 : F) b) :=
      fun n ↦ mem_svImage.2
        ⟨us (φ n), by
          simpa [mem_closedBall, dist_zero_right] using (hφlt n).le,
          hmem (φ n)⟩
    have hnorm : ∀ n, ‖xs (φ n)‖ ≤ r := fun n ↦ by
      simpa [mem_closedBall, dist_zero_right] using hr (hxin n)
    have hdiv : Tendsto (fun n ↦ ‖xs (φ n)‖) atTop atTop :=
      hxs.comp hφ.tendsto_atTop
    obtain ⟨n, hn⟩ := (hdiv.eventually_ge_atTop (r + 1)).exists
    linarith [hnorm n]
  · intro h B hB
    by_contra hnot
    obtain ⟨xs, hxsA, hxsdiv⟩ := exists_seq_norm_atTop hnot
    choose us husB husmem using fun n ↦ mem_svImage.1 (hxsA n)
    have hdiv := h xs us husmem hxsdiv
    obtain ⟨r, hr⟩ := (isBounded_iff_subset_closedBall (0 : F)).1 hB
    obtain ⟨n, hn⟩ := (hdiv.eventually_ge_atTop (r + 1)).exists
    have : ‖us n‖ ≤ r := by
      simpa [mem_closedBall, dist_zero_right] using hr (husB n)
    linarith

end InverseBoundedness

end RW
