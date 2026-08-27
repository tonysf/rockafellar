/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Semicontinuity Through Distance Functions

Proposition 5.11 converts semicontinuity of a closed-valued mapping `S` into
ordinary semicontinuity of the real-valued distance functions
`x ↦ d(u, S(x))`, one for each `u`.  Outer semicontinuity of `S` corresponds
to lower semicontinuity of every such distance function, inner
semicontinuity to upper semicontinuity, and continuity to continuity.

Distances are taken as `Metric.infEDist`, valued in `[0, ∞]`, which is the
convention Chapter 4 uses and the one the book's `d(u, ∅) = ∞` requires; the
ordinary real `infDist` sets the distance to the empty set to `0` and would
break every clause below.

The book calls the proof immediate from 4.7.  Two things are not immediate
once the limits are taken along a neighborhood filter rather than a sequence.
Closed-valuedness is what turns `d(u, S(x̄)) = 0` back into `u ∈ S(x̄)` in
(a), and the forward half of (a) needs a compact set to be extracted from
frequent hits -- `outerSetLimitAlong_inter_nonempty_of_frequently` -- since
there is no subsequence to pass to.  Properness of the target supplies the
compact set as a closed ball.

Note on the printed statement: clause (b) of 5.11 reads "the function
`u → d(u, S(x))` is usc", which is a misprint.  The variable being moved is
`x`, as in (a) and (c), and as clause (c) -- the conjunction of (a) and (b)
-- requires.  The corrected reading is what is formalized here.
-/

import RockafellarWets.Chapter5.SemicontinuityCriteria

open Filter Metric Set Topology

namespace RW

section DistanceCriteria

variable {E F : Type*} [TopologicalSpace E] [PseudoMetricSpace F]
variable {S : E → Set F} {X : Set E} {x : E}

/-- **Proposition 5.11(b).**  Inner semicontinuity relative to `X` is upper
semicontinuity, relative to `X`, of every distance function `x ↦ d(u, S(x))`.

Neither closed-valuedness nor properness is needed for this clause: a point
of `S(x̄)` within `d(u, S(x̄))`-distance of `u` already lies in the open ball
`{w | d(u, w) < y}`, and inner semicontinuity carries that ball into the
nearby images. -/
theorem svIscWithinAt_iff_upperSemicontinuousWithinAt :
    SvIscWithinAt S X x ↔
      ∀ u : F, UpperSemicontinuousWithinAt
        (fun z ↦ Metric.infEDist u (S z)) X x := by
  constructor
  · intro h u y hy
    obtain ⟨v, hvS, hvlt⟩ := Metric.infEDist_lt_iff.1 hy
    have hball : Metric.eball u y ∈ nhds v :=
      Metric.isOpen_eball.mem_nhds (Metric.mem_eball'.2 hvlt)
    filter_upwards [h hvS (Metric.eball u y) hball] with z hz
    obtain ⟨w, hwS, hwball⟩ := hz
    exact lt_of_le_of_lt (Metric.infEDist_le_edist_of_mem hwS)
      (Metric.mem_eball'.1 hwball)
  · intro h v hv W hW
    obtain ⟨r, hr, hrW⟩ := EMetric.mem_nhds_iff.1 hW
    have hlt : Metric.infEDist v (S x) < r := by
      rw [Metric.infEDist_zero_of_mem hv]
      exact hr
    filter_upwards [h v r hlt] with z hz
    obtain ⟨w, hwS, hwlt⟩ := Metric.infEDist_lt_iff.1 hz
    exact ⟨w, hwS, hrW (Metric.mem_eball'.2 hwlt)⟩

/-- The easy half of **Proposition 5.11(a)**: lower semicontinuity of all the
distance functions forces outer semicontinuity, for a closed-valued
mapping. -/
theorem svOscWithinAt_of_lowerSemicontinuousWithinAt
    (hclosed : IsClosed (S x))
    (h : ∀ u : F, LowerSemicontinuousWithinAt
      (fun z ↦ Metric.infEDist u (S z)) X x) :
    SvOscWithinAt S X x := by
  intro u hu
  rw [Metric.mem_iff_infEDist_zero_of_closed hclosed]
  by_contra hne
  obtain ⟨y, hy0, hyx⟩ := exists_between (pos_iff_ne_zero.2 hne)
  have hfreq : ∃ᶠ z in nhdsWithin x X,
      Metric.infEDist u (S z) < y := by
    refine (hu (Metric.eball u y) (Metric.eball_mem_nhds u hy0)).mono ?_
    rintro z ⟨w, hwS, hwball⟩
    exact lt_of_le_of_lt (Metric.infEDist_le_edist_of_mem hwS)
      (Metric.mem_eball'.1 hwball)
  obtain ⟨z, hz₁, hz₂⟩ := (hfreq.and_eventually (h u y hyx)).exists
  exact absurd hz₁ (not_lt.2 hz₂.le)

/-- The other half of **Proposition 5.11(a)**, where properness of the target
enters.  Frequent near-hits of `u` put the images frequently inside a compact
ball, and the compact extraction lemma then produces a point of the outer
limit inside that ball. -/
theorem lowerSemicontinuousWithinAt_of_svOscWithinAt [ProperSpace F]
    (h : SvOscWithinAt S X x) (u : F) :
    LowerSemicontinuousWithinAt (fun z ↦ Metric.infEDist u (S z)) X x := by
  intro y hy
  by_contra hnot
  rw [Filter.not_eventually] at hnot
  obtain ⟨c, hyc, hcx⟩ := exists_between hy
  have hctop : c ≠ ⊤ := (lt_of_lt_of_le hcx le_top).ne
  have hfreq : ∃ᶠ z in nhdsWithin x X,
      (S z ∩ Metric.closedBall u c.toReal).Nonempty := by
    refine hnot.mono fun z hz ↦ ?_
    obtain ⟨w, hwS, hwlt⟩ :=
      Metric.infEDist_lt_iff.1 (lt_of_le_of_lt (not_lt.1 hz) hyc)
    refine ⟨w, hwS, Metric.mem_closedBall'.2 ?_⟩
    rw [dist_edist]
    exact ENNReal.toReal_mono hctop hwlt.le
  obtain ⟨w, hwlim, hwball⟩ :=
    outerSetLimitAlong_inter_nonempty_of_frequently
      (isCompact_closedBall u c.toReal) hfreq
  have hwS : w ∈ S x := h hwlim
  have hle : Metric.infEDist u (S x) ≤ c := by
    refine le_trans (Metric.infEDist_le_edist_of_mem hwS) ?_
    rw [edist_dist, ← ENNReal.ofReal_toReal hctop]
    exact ENNReal.ofReal_le_ofReal (Metric.mem_closedBall'.1 hwball)
  exact absurd hcx (not_lt.2 hle)

/-- **Proposition 5.11(a).**  For a closed-valued mapping, outer
semicontinuity relative to `X` is lower semicontinuity, relative to `X`, of
every distance function `x ↦ d(u, S(x))`. -/
theorem svOscWithinAt_iff_lowerSemicontinuousWithinAt [ProperSpace F]
    (hclosed : IsClosed (S x)) :
    SvOscWithinAt S X x ↔
      ∀ u : F, LowerSemicontinuousWithinAt
        (fun z ↦ Metric.infEDist u (S z)) X x :=
  ⟨lowerSemicontinuousWithinAt_of_svOscWithinAt,
    svOscWithinAt_of_lowerSemicontinuousWithinAt hclosed⟩

/-- **Proposition 5.11(c).**  For a closed-valued mapping, continuity
relative to `X` is continuity, relative to `X`, of every distance function
`x ↦ d(u, S(x))`. -/
theorem svContinuousWithinAt_iff_continuousWithinAt [ProperSpace F]
    (hclosed : IsClosed (S x)) :
    SvContinuousWithinAt S X x ↔
      ∀ u : F, ContinuousWithinAt (fun z ↦ Metric.infEDist u (S z)) X x := by
  simp only [SvContinuousWithinAt,
    svOscWithinAt_iff_lowerSemicontinuousWithinAt hclosed,
    svIscWithinAt_iff_upperSemicontinuousWithinAt,
    continuousWithinAt_iff_lower_upperSemicontinuousWithinAt, forall_and]

end DistanceCriteria

section Absolute

variable {E F : Type*} [TopologicalSpace E] [PseudoMetricSpace F]
variable {S : E → Set F} {x : E}

/-- The absolute case `X = IRⁿ` of 5.11(a). -/
theorem svOscAt_iff_lowerSemicontinuousAt [ProperSpace F]
    (hclosed : IsClosed (S x)) :
    SvOscAt S x ↔
      ∀ u : F, LowerSemicontinuousAt (fun z ↦ Metric.infEDist u (S z)) x := by
  rw [← svOscWithinAt_univ, svOscWithinAt_iff_lowerSemicontinuousWithinAt hclosed]
  exact forall_congr' fun u ↦ lowerSemicontinuousWithinAt_univ_iff

/-- The absolute case `X = IRⁿ` of 5.11(b). -/
theorem svIscAt_iff_upperSemicontinuousAt :
    SvIscAt S x ↔
      ∀ u : F, UpperSemicontinuousAt (fun z ↦ Metric.infEDist u (S z)) x := by
  rw [← svIscWithinAt_univ, svIscWithinAt_iff_upperSemicontinuousWithinAt]
  exact forall_congr' fun u ↦ upperSemicontinuousWithinAt_univ_iff

/-- The absolute case `X = IRⁿ` of 5.11(c). -/
theorem svContinuousAt_iff_continuousAt [ProperSpace F]
    (hclosed : IsClosed (S x)) :
    SvContinuousAt S x ↔
      ∀ u : F, ContinuousAt (fun z ↦ Metric.infEDist u (S z)) x := by
  rw [← svContinuousWithinAt_univ,
    svContinuousWithinAt_iff_continuousWithinAt hclosed]
  exact forall_congr' fun u ↦ continuousWithinAt_univ _ _

end Absolute

end RW
