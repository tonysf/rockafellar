/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Uniformity of Approximation

Proposition 5.12 restates semicontinuity as a uniform approximation property
on bounded balls: outer semicontinuity says the part of `S(x)` inside `ρIB`
is eventually within `ε` of `S(x̄)`, and inner semicontinuity says the part
of `S(x̄)` inside `ρIB` is eventually within `ε` of `S(x)`.  Exercise 5.13
upgrades this to a uniform statement over a compact parameter set.

The book derives 5.12 from 4.10.  That derivation does not transfer directly
here: the Chapter 4 proofs of 4.10 extract convergent subsequences, and the
limits of 5(1) run along a neighborhood filter where no subsequence is
available.  Both halves are proved instead by the filter-native compactness
arguments that Chapter 5 already has -- the compact extraction of
`SetLimitsAlong.lean` for the outer clause, and a finite subcover of the
compact set `S(x̄) ∩ ρIB` for the inner one.

Following Chapter 4, `S(x̄) + εIB` is rendered as the open thickening
`Metric.thickening ε (S x̄)`; since both clauses quantify over all `ε > 0`,
nothing turns on the choice between the open and closed thickening.
-/

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import RockafellarWets.Chapter5.SemicontinuityCriteria

open Filter Metric Set Topology

namespace RW

section Uniformity

variable {E F : Type*} [TopologicalSpace E]
variable [NormedAddCommGroup F] [ProperSpace F]
variable {S : E → Set F} {X : Set E} {x : E}

/-- **Proposition 5.12(a).**  Outer semicontinuity relative to `X` is uniform
approximation of `S(x̄)` from outside on every bounded ball.

Failure of the uniform condition makes the images frequently meet the compact
set `ρIB \ thickening ε (S x̄)`, and the compact extraction lemma then puts a
point of the outer limit there -- a point that outer semicontinuity places in
`S(x̄)`, which is absurd. -/
theorem svOscWithinAt_iff_eventually_inter_closedBall_subset
    (hclosed : IsClosed (S x)) :
    SvOscWithinAt S X x ↔
      ∀ ρ > 0, ∀ ε > 0, ∀ᶠ z in nhdsWithin x X,
        S z ∩ closedBall 0 ρ ⊆ thickening ε (S x) := by
  constructor
  · intro h ρ hρ ε hε
    by_contra hnot
    rw [Filter.not_eventually] at hnot
    have hK : IsCompact (closedBall (0 : F) ρ \ thickening ε (S x)) :=
      (isCompact_closedBall (0 : F) ρ).diff isOpen_thickening
    have hfreq : ∃ᶠ z in nhdsWithin x X,
        (S z ∩ (closedBall (0 : F) ρ \ thickening ε (S x))).Nonempty := by
      refine hnot.mono fun z hz ↦ ?_
      obtain ⟨w, hw, hwnot⟩ := Set.not_subset.1 hz
      exact ⟨w, hw.1, hw.2, hwnot⟩
    obtain ⟨w, hwlim, hwball, hwnot⟩ :=
      outerSetLimitAlong_inter_nonempty_of_frequently hK hfreq
    exact hwnot (self_subset_thickening hε (S x) (h hwlim))
  · intro h u hu
    rw [← hclosed.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    set ρ : ℝ := ‖u‖ + 1 with hρdef
    have hρ : 0 < ρ := by positivity
    set δ : ℝ := min (ε / 2) 1 with hδdef
    have hδ : 0 < δ := lt_min (by positivity) one_pos
    have hfreq := hu (ball u δ) (ball_mem_nhds u hδ)
    obtain ⟨z, ⟨w, hwS, hwball⟩, hzsub⟩ :=
      (hfreq.and_eventually (h ρ hρ (ε / 2) (by positivity))).exists
    have hwρ : w ∈ closedBall (0 : F) ρ := by
      rw [mem_closedBall, dist_zero_right]
      have h₁ : dist w u < δ := by simpa [dist_comm] using hwball
      have h₂ : ‖w‖ ≤ ‖u‖ + dist w u := by
        simpa [dist_eq_norm] using norm_le_norm_add_norm_sub' w u
      have h₃ : δ ≤ 1 := min_le_right _ _
      linarith
    obtain ⟨v, hvS, hvdist⟩ := mem_thickening_iff.1 (hzsub ⟨hwS, hwρ⟩)
    refine ⟨v, hvS, ?_⟩
    have h₁ : dist u w < δ := by simpa [dist_comm] using hwball
    have h₂ : δ ≤ ε / 2 := min_le_left _ _
    have h₃ : dist u v ≤ dist u w + dist w v := dist_triangle _ _ _
    linarith

/-- **Proposition 5.12(b).**  Inner semicontinuity relative to `X` is uniform
approximation of `S(x̄)` from inside on every bounded ball.

Here the compact set is `S(x̄) ∩ ρIB` itself: cover it by finitely many balls
of radius `ε/2` centred at points of it, and inner semicontinuity makes the
nearby images meet all of them at once. -/
theorem svIscWithinAt_iff_eventually_inter_closedBall_subset
    (hclosed : IsClosed (S x)) :
    SvIscWithinAt S X x ↔
      ∀ ρ > 0, ∀ ε > 0, ∀ᶠ z in nhdsWithin x X,
        S x ∩ closedBall 0 ρ ⊆ thickening ε (S z) := by
  constructor
  · intro h ρ hρ ε hε
    have hK : IsCompact (S x ∩ closedBall (0 : F) ρ) :=
      (isCompact_closedBall (0 : F) ρ).inter_left hclosed
    obtain ⟨t, htK, hcover⟩ :=
      hK.elim_nhds_subcover (fun v ↦ ball v (ε / 2))
        fun v _ ↦ ball_mem_nhds v (by positivity)
    have hev : ∀ᶠ z in nhdsWithin x X,
        ∀ v ∈ t, (S z ∩ ball v (ε / 2)).Nonempty :=
      Filter.eventually_all_finset t |>.2 fun v hv ↦
        h (htK v hv).1 (ball v (ε / 2)) (ball_mem_nhds v (by positivity))
    filter_upwards [hev] with z hz v hv
    obtain ⟨v₀, hv₀t, hvball⟩ := mem_iUnion₂.1 (hcover hv)
    obtain ⟨w, hwS, hwball⟩ := hz v₀ hv₀t
    refine mem_thickening_iff.2 ⟨w, hwS, ?_⟩
    have h₁ : dist v v₀ < ε / 2 := mem_ball.1 hvball
    have h₂ : dist v₀ w < ε / 2 := by simpa [dist_comm] using mem_ball.1 hwball
    have h₃ : dist v w ≤ dist v v₀ + dist v₀ w := dist_triangle _ _ _
    linarith
  · intro h v hv W hW
    obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.1 hW
    set ρ : ℝ := ‖v‖ + 1 with hρdef
    have hρ : 0 < ρ := by positivity
    have hvρ : v ∈ closedBall (0 : F) ρ := by
      rw [mem_closedBall, dist_zero_right, hρdef]
      linarith
    filter_upwards [h ρ hρ ε hε] with z hz
    obtain ⟨w, hwS, hwdist⟩ := mem_thickening_iff.1 (hz ⟨hv, hvρ⟩)
    exact ⟨w, hwS, hεW (mem_ball.2 (by simpa [dist_comm] using hwdist))⟩

/-- **Proposition 5.12(a)** in the book's explicit neighborhood form. -/
theorem svOscWithinAt_iff_exists_nhds_inter_closedBall_subset
    (hclosed : IsClosed (S x)) :
    SvOscWithinAt S X x ↔
      ∀ ρ > 0, ∀ ε > 0, ∃ V ∈ nhds x, ∀ z ∈ X ∩ V,
        S z ∩ closedBall 0 ρ ⊆ thickening ε (S x) := by
  rw [svOscWithinAt_iff_eventually_inter_closedBall_subset hclosed]
  exact forall₂_congr fun _ _ ↦ forall₂_congr fun _ _ ↦
    eventually_nhdsWithin_iff_exists_nhds

/-- **Proposition 5.12(b)** in the book's explicit neighborhood form. -/
theorem svIscWithinAt_iff_exists_nhds_inter_closedBall_subset
    (hclosed : IsClosed (S x)) :
    SvIscWithinAt S X x ↔
      ∀ ρ > 0, ∀ ε > 0, ∃ V ∈ nhds x, ∀ z ∈ X ∩ V,
        S x ∩ closedBall 0 ρ ⊆ thickening ε (S z) := by
  rw [svIscWithinAt_iff_eventually_inter_closedBall_subset hclosed]
  exact forall₂_congr fun _ _ ↦ forall₂_congr fun _ _ ↦
    eventually_nhdsWithin_iff_exists_nhds

end Uniformity

section UniformContinuity

variable {E F : Type*} [PseudoMetricSpace E]
variable [NormedAddCommGroup F] [ProperSpace F]

/-- **Exercise 5.13 (uniform continuity).**  A mapping continuous relative to
a compact set `X` approximates uniformly over `X`.

Applying both clauses of 5.12 at each point of `X` -- the outer one at radius
`ρ` and the inner one at the enlarged radius `ρ + ε`, since a point within
`ε/2` of `ρIB` need not lie in `ρIB` -- produces an open cover of `X`, and a
Lebesgue number for that cover is the required `δ`.

The book's hypothesis `X ⊂ dom S` is not needed: where `S(x̄)` is empty, outer
semicontinuity already forces the nearby images to leave every bounded ball.
Closed-valuedness is likewise automatic, since outer semicontinuity relative
to `X` makes `S` closed-valued on `X`. -/
theorem exists_delta_uniform_of_svContinuousOn {S : E → Set F} {X : Set E}
    (hX : IsCompact X) (h : SvContinuousOn S X) {ρ : ℝ} (hρ : 0 < ρ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ X, ∀ x' ∈ X, dist x' x ≤ δ →
      S x' ∩ closedBall 0 ρ ⊆ thickening ε (S x) := by
  have hclosed : ∀ z ∈ X, IsClosed (S z) := fun z hz ↦ (h z hz).1.isClosed hz
  have hkey : ∀ p : ↥X, ∃ U : Set E, IsOpen U ∧ (p : E) ∈ U ∧
      ∀ z ∈ X ∩ U,
        (S z ∩ closedBall 0 ρ ⊆ thickening (ε / 2) (S (p : E))) ∧
          S (p : E) ∩ closedBall 0 (ρ + ε) ⊆ thickening (ε / 2) (S z) := by
    rintro ⟨p, hp⟩
    have hosc := (svOscWithinAt_iff_eventually_inter_closedBall_subset
      (hclosed p hp)).1 (h p hp).1 ρ hρ (ε / 2) (by positivity)
    have hisc := (svIscWithinAt_iff_eventually_inter_closedBall_subset
      (hclosed p hp)).1 (h p hp).2 (ρ + ε) (by positivity) (ε / 2)
      (by positivity)
    obtain ⟨V, hV, hVsub⟩ :=
      eventually_nhdsWithin_iff_exists_nhds.1 (hosc.and hisc)
    obtain ⟨U, hUV, hUopen, hpU⟩ := _root_.mem_nhds_iff.1 hV
    exact ⟨U, hUopen, hpU, fun z hz ↦ hVsub z ⟨hz.1, hUV hz.2⟩⟩
  choose U hUopen hUmem hUprop using hkey
  obtain ⟨δ, hδ, hball⟩ :=
    lebesgue_number_lemma_of_metric hX hUopen fun z hz ↦
      mem_iUnion.2 ⟨⟨z, hz⟩, hUmem ⟨z, hz⟩⟩
  refine ⟨δ / 2, by positivity, fun x hx x' hx' hdist u hu ↦ ?_⟩
  obtain ⟨p, hpsub⟩ := hball x hx
  have hxU : x ∈ U p := hpsub (mem_ball_self hδ)
  have hx'U : x' ∈ U p := hpsub (mem_ball.2 (by linarith))
  obtain ⟨v, hvS, hvdist⟩ :=
    mem_thickening_iff.1 ((hUprop p x' ⟨hx', hx'U⟩).1 hu)
  have hvball : v ∈ closedBall (0 : F) (ρ + ε) := by
    rw [mem_closedBall, dist_zero_right]
    have h₁ : ‖v‖ ≤ ‖u‖ + dist u v := by
      simpa [dist_eq_norm, norm_sub_rev] using norm_le_norm_add_norm_sub' v u
    have h₂ : ‖u‖ ≤ ρ := by
      simpa [dist_zero_right] using mem_closedBall.1 hu.2
    linarith
  obtain ⟨w, hwS, hwdist⟩ :=
    mem_thickening_iff.1 ((hUprop p x ⟨hx, hxU⟩).2 ⟨hvS, hvball⟩)
  refine mem_thickening_iff.2 ⟨w, hwS, ?_⟩
  have h₃ : dist u w ≤ dist u v + dist v w := dist_triangle _ _ _
  linarith

end UniformContinuity

end RW
