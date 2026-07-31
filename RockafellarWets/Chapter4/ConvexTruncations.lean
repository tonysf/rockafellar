/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Convex Truncations and Hausdorff Convergence

This file proves Theorem 4.16 of Rockafellar--Wets.  It first records the
compactness principle that Painleve--Kuratowski convergence inside a common
compact set, with nonempty compact limit, implies convergence in extended
Hausdorff distance.
-/

import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Sequences
import RockafellarWets.Chapter4.ConvexLimits
import RockafellarWets.Chapter4.HausdorffConvergence
import RockafellarWets.Chapter4.HitAndMiss

open Bornology Filter Function Metric Set Topology

namespace RW

section CompactHausdorffConvergence

variable {E : Type*} [MetricSpace E] [ProperSpace E]

/-- On a common compact set, Painleve--Kuratowski convergence to a compact set
implies convergence in extended Hausdorff distance, including the empty-limit
case. -/
theorem PKConverges.tendsto_hausdorffEDist_of_compactly_bounded
    {Aseq : ℕ → Set E} {A B : Set E}
    (hlim : PKConverges Aseq A) (hAcompact : IsCompact A)
    (hBcompact : IsCompact B) (hsub : ∀ n, Aseq n ⊆ B) :
    Tendsto (fun n ↦ hausdorffEDist (Aseq n) A) atTop (nhds 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hhalf : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  let F : Set E := B ∩ {x | ε ≤ infEDist x A}
  have hFcompact : IsCompact F := by
    apply hBcompact.inter_right
    exact isClosed_le continuous_const continuous_infEDist
  have hAF : Disjoint A F := by
    rw [Set.disjoint_left]
    intro x hxA hxF
    have hεzero : ε ≤ 0 := calc
      ε ≤ infEDist x A := hxF.2
      _ = 0 := infEDist_zero_of_mem hxA
    exact hε.not_ge hεzero
  have houter : outerSetLimit Aseq ⊆ A := by
    rw [hlim.outer_eq]
  have hmiss : ∀ᶠ n in atTop, Disjoint (Aseq n) F :=
    (outerSetLimit_subset_iff_eventually_misses_compact hAcompact.isClosed).1
      houter F hFcompact hAF
  have hcover : A ⊆ ⋃ p : A, eball (p : E) (ε / 2) := by
    intro x hxA
    exact mem_iUnion_of_mem (⟨x, hxA⟩ : A) (mem_eball_self hhalf)
  rcases hAcompact.elim_finite_subcover
      (fun p : A ↦ eball (p : E) (ε / 2))
      (fun _ ↦ isOpen_eball) hcover with ⟨t, ht⟩
  have hhits : ∀ᶠ n in atTop,
      ∀ p ∈ t, (Aseq n ∩ eball (p : E) (ε / 2)).Nonempty := by
    apply t.eventually_all.2
    intro p hp
    have hpInner : (p : E) ∈ innerSetLimit Aseq := by
      rw [hlim.inner_eq]
      exact p.property
    exact hpInner _ (eball_mem_nhds _ hhalf)
  filter_upwards [hmiss, hhits] with n hnmiss hnhits
  apply hausdorffEDist_le_of_mem_edist
  · intro x hxSeq
    have hxB : x ∈ B := hsub n hxSeq
    have hxNotF : x ∉ F := fun hxF ↦ hnmiss.le_bot ⟨hxSeq, hxF⟩
    have hxDist : infEDist x A < ε := by
      exact lt_of_not_ge fun hge ↦ hxNotF ⟨hxB, hge⟩
    rcases infEDist_lt_iff.1 hxDist with ⟨y, hyA, hxy⟩
    exact ⟨y, hyA, hxy.le⟩
  · intro x hxA
    rcases mem_iUnion₂.1 (ht hxA) with ⟨p, hpt, hxp⟩
    rcases hnhits p hpt with ⟨y, hySeq, hyp⟩
    refine ⟨y, hySeq, ?_⟩
    calc
      edist x y ≤ edist x (p : E) + edist (p : E) y := edist_triangle _ _ _
      _ ≤ ε := by
        rw [← ENNReal.add_halves ε]
        exact (ENNReal.add_lt_add (mem_eball.1 hxp) (mem_eball'.1 hyp)).le

/-- **Example 4.13 (common-bounded equivalence).** On sequences contained
in one bounded set, Painleve--Kuratowski convergence to a closed target is
equivalent to Pompeiu--Hausdorff convergence.  The extended distance also
handles the empty-target boundary case. -/
theorem pkConverges_iff_tendsto_pompeiuHausdorffEDist_of_common_bounded
    {Aseq : ℕ → Set E} {A B : Set E} (hAclosed : IsClosed A)
    (hBbounded : IsBounded B) (hAseqB : ∀ n, Aseq n ⊆ B)
    (hAB : A ⊆ B) :
    PKConverges Aseq A ↔
      Tendsto (fun n ↦ pompeiuHausdorffEDist (Aseq n) A)
        atTop (nhds 0) := by
  constructor
  · intro hlim
    apply hlim.tendsto_hausdorffEDist_of_compactly_bounded
    · exact isCompact_iff_isClosed_bounded.2
        ⟨hAclosed, hBbounded.subset hAB⟩
    · exact hBbounded.isCompact_closure
    · intro n
      exact (hAseqB n).trans subset_closure
  · exact pkConverges_of_tendsto_pompeiuHausdorffEDist_zero hAclosed

end CompactHausdorffConvergence

section ConvexTruncationLimits

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Intersecting a convergent convex sequence with a closed ball preserves
Painleve--Kuratowski convergence whenever the limit contains a point strictly
inside that ball.  This is the geometric core of Theorem 4.16. -/
theorem PKConverges.inter_closedBall_of_convex
    {C : ℕ → Set E} {D : Set E} (hlim : PKConverges C D)
    (hCconv : ∀ n, Convex ℝ (C n)) {c : E} (hcD : c ∈ D)
    {r : ℝ} (hcr : ‖c‖ < r) :
    PKConverges (fun n ↦ C n ∩ closedBall (0 : E) r)
      (D ∩ closedBall (0 : E) r) := by
  have hDconv : Convex ℝ D := hlim.convex hCconv
  have hcBall : c ∈ ball (0 : E) r := by
    simpa only [mem_ball, dist_zero_right] using hcr
  have hcInterior : c ∈ interior (closedBall (0 : E) r) :=
    ball_subset_interior_closedBall hcBall
  have houter :
      outerSetLimit (fun n ↦ C n ∩ closedBall (0 : E) r) ⊆
        D ∩ closedBall (0 : E) r := by
    intro x hx
    have hxC : x ∈ outerSetLimit C :=
      outerSetLimit_mono (fun n ↦ inter_subset_left) hx
    have hxBall : x ∈ outerSetLimit (fun _ : ℕ ↦ closedBall (0 : E) r) :=
      outerSetLimit_mono (fun n ↦ inter_subset_right) hx
    rw [hlim.outer_eq] at hxC
    rw [outerSetLimit_const, isClosed_closedBall.closure_eq] at hxBall
    exact ⟨hxC, hxBall⟩
  have hinner :
      D ∩ closedBall (0 : E) r ⊆
        innerSetLimit (fun n ↦ C n ∩ closedBall (0 : E) r) := by
    intro x hx V hV
    rcases _root_.mem_nhds_iff.1 hV with ⟨U, hUV, hUopen, hxU⟩
    have hxClosure : x ∈ closure (openSegment ℝ c x) :=
      segment_subset_closure_openSegment (right_mem_segment ℝ c x)
    rcases mem_closure_iff.1 hxClosure U hUopen hxU with ⟨z, hzU, hzOpen⟩
    have hzD : z ∈ D := hDconv.openSegment_subset hcD hx.1 hzOpen
    have hzBallInterior : z ∈ interior (closedBall (0 : E) r) :=
      (convex_closedBall (0 : E) r).openSegment_interior_self_subset_interior
        hcInterior hx.2 hzOpen
    have hzInner : z ∈ innerSetLimit C := by
      rw [hlim.inner_eq]
      exact hzD
    have hlocal : U ∩ closedBall (0 : E) r ∈ nhds z :=
      inter_mem (hUopen.mem_nhds hzU) (mem_interior_iff_mem_nhds.1 hzBallInterior)
    exact (hzInner _ hlocal).mono fun n ⟨y, hyC, hyU, hyBall⟩ ↦
      ⟨y, ⟨hyC, hyBall⟩, hUV hyU⟩
  constructor
  · exact Set.Subset.antisymm
      ((innerSetLimit_subset_outerSetLimit _).trans houter) hinner
  · exact Set.Subset.antisymm houter
      (hinner.trans (innerSetLimit_subset_outerSetLimit _))

/-- Forward implication of **Theorem 4.16**: a convergent convex sequence has
Hausdorff-convergent truncations at every sufficiently large radius.  The
empty-limit case is included; then every radius is admissible. -/
theorem PKConverges.exists_tendsto_hausdorffEDist_inter_closedBall
    [FiniteDimensional ℝ E] {C : ℕ → Set E} {D : Set E}
    (hlim : PKConverges C D) (hCconv : ∀ n, Convex ℝ (C n)) :
    ∃ r₀ : ℝ, 0 ≤ r₀ ∧ ∀ r : ℝ, r₀ ≤ r →
      Tendsto
        (fun n ↦ hausdorffEDist
          (C n ∩ closedBall (0 : E) r)
          (D ∩ closedBall (0 : E) r))
        atTop (nhds 0) := by
  by_cases hDempty : D = ∅
  · refine ⟨0, le_rfl, fun r _hr ↦ ?_⟩
    have houter : outerSetLimit (fun n ↦ C n ∩ closedBall (0 : E) r) = ∅ := by
      apply eq_empty_iff_forall_notMem.2
      intro x hx
      have hxC : x ∈ outerSetLimit C :=
        outerSetLimit_mono (fun n ↦ inter_subset_left) hx
      rw [hlim.outer_eq, hDempty] at hxC
      exact hxC
    have htrunc :
        PKConverges (fun n ↦ C n ∩ closedBall (0 : E) r) ∅ := by
      constructor
      · apply eq_empty_iff_forall_notMem.2
        intro x hx
        exact houter.subset (innerSetLimit_subset_outerSetLimit _ hx)
      · exact houter
    simpa only [hDempty, empty_inter] using
      htrunc.tendsto_hausdorffEDist_of_compactly_bounded isCompact_empty
        (isCompact_closedBall (0 : E) r) (fun n ↦ inter_subset_right)
  · have hDne : D.Nonempty := Set.nonempty_iff_ne_empty.2 hDempty
    rcases hDne with ⟨c, hcD⟩
    refine ⟨‖c‖ + 1, by positivity, fun r hr ↦ ?_⟩
    have hcr : ‖c‖ < r := lt_of_lt_of_le (lt_add_one ‖c‖) hr
    have htrunc := hlim.inter_closedBall_of_convex hCconv hcD hcr
    exact htrunc.tendsto_hausdorffEDist_of_compactly_bounded
      ((isCompact_closedBall (0 : E) r).inter_left hlim.isClosed)
      (isCompact_closedBall (0 : E) r) (fun n ↦ inter_subset_right)

/-- Reverse implication of **Theorem 4.16**.  Convexity is not needed in this
direction: Hausdorff convergence of every sufficiently large truncation to a
closed target already implies Painleve--Kuratowski convergence. -/
theorem pkConverges_of_tendsto_hausdorffEDist_inter_closedBall
    [FiniteDimensional ℝ E] {C : ℕ → Set E} {D : Set E} (hDclosed : IsClosed D)
    {r₀ : ℝ}
    (hhaus : ∀ r : ℝ, r₀ ≤ r →
      Tendsto
        (fun n ↦ hausdorffEDist
          (C n ∩ closedBall (0 : E) r)
          (D ∩ closedBall (0 : E) r))
        atTop (nhds 0)) :
    PKConverges C D := by
  have hinner : D ⊆ innerSetLimit C := by
    intro x hxD V hV
    rcases Metric.mem_nhds_iff.1 hV with ⟨δ, hδ, hballV⟩
    let r : ℝ := max r₀ (‖x‖ + 1)
    have hr₀ : r₀ ≤ r := le_max_left _ _
    have hxr : ‖x‖ ≤ r :=
      (le_add_of_nonneg_right zero_le_one).trans (le_max_right _ _)
    have hxTrunc : x ∈ D ∩ closedBall (0 : E) r := by
      exact ⟨hxD, by simpa only [mem_closedBall, dist_zero_right] using hxr⟩
    have hδE : 0 < ENNReal.ofReal δ := ENNReal.ofReal_pos.2 hδ
    have hevent := (hhaus r hr₀).eventually (Iio_mem_nhds hδE)
    exact hevent.mono fun n hn ↦ by
      have hn' :
          hausdorffEDist (D ∩ closedBall (0 : E) r)
            (C n ∩ closedBall (0 : E) r) < ENNReal.ofReal δ := by
        simpa only [hausdorffEDist_comm] using hn
      rcases exists_edist_lt_of_hausdorffEDist_lt hxTrunc hn' with
        ⟨y, hyTrunc, hxy⟩
      have hxyDist : dist x y < δ := by
        rwa [edist_dist, ENNReal.ofReal_lt_ofReal_iff hδ] at hxy
      exact ⟨y, hyTrunc.1, hballV (by simpa only [mem_ball, dist_comm] using hxyDist)⟩
  have houter : outerSetLimit C ⊆ D := by
    apply (outerSetLimit_subset_iff_eventually_misses_compact hDclosed).2
    intro K hK hDK
    rcases hK.isBounded.subset_closedBall (0 : E) with ⟨R, hKR⟩
    let r : ℝ := max r₀ R
    have hr₀ : r₀ ≤ r := le_max_left _ _
    have hKr : K ⊆ closedBall (0 : E) r :=
      hKR.trans (closedBall_subset_closedBall (le_max_right _ _))
    let T : Set E := D ∩ closedBall (0 : E) r
    have hTclosed : IsClosed T := hDclosed.inter isClosed_closedBall
    have hKT : Disjoint K T := by
      rw [Set.disjoint_left]
      intro x hxK hxT
      exact hDK.le_bot ⟨hxT.1, hxK⟩
    rcases exists_pos_forall_lt_edist hK hTclosed hKT with
      ⟨η, hη, hsep⟩
    have hηE : 0 < (η : ENNReal) := ENNReal.coe_pos.2 hη
    have hevent := (hhaus r hr₀).eventually (Iio_mem_nhds hηE)
    exact hevent.mono fun n hn ↦ by
      rw [Set.disjoint_left]
      intro x hxC hxK
      have hxTrunc : x ∈ C n ∩ closedBall (0 : E) r := ⟨hxC, hKr hxK⟩
      rcases exists_edist_lt_of_hausdorffEDist_lt hxTrunc hn with
        ⟨y, hyT, hxy⟩
      exact (lt_asymm (hsep x hxK y hyT) hxy).elim
  constructor
  · exact Set.Subset.antisymm
      ((innerSetLimit_subset_outerSetLimit C).trans houter) hinner
  · exact Set.Subset.antisymm houter
      (hinner.trans (innerSetLimit_subset_outerSetLimit C))

/-- **Theorem 4.16 (convex truncation criterion).** For a sequence of convex
sets and a closed candidate limit in a finite-dimensional real normed space,
Painleve--Kuratowski convergence is equivalent to convergence in extended
Hausdorff distance of every sufficiently large closed-ball truncation.

The Lean statement is slightly stronger than the printed one: the individual
sets need not be closed or nonempty, because both PK limits and extended
Hausdorff distance are invariant under termwise closure and handle empty sets
exactly. -/
theorem pkConverges_iff_exists_tendsto_hausdorffEDist_inter_closedBall
    [FiniteDimensional ℝ E] {C : ℕ → Set E} {D : Set E}
    (hCconv : ∀ n, Convex ℝ (C n)) (hDclosed : IsClosed D) :
    PKConverges C D ↔
      ∃ r₀ : ℝ, 0 ≤ r₀ ∧ ∀ r : ℝ, r₀ ≤ r →
        Tendsto
          (fun n ↦ hausdorffEDist
            (C n ∩ closedBall (0 : E) r)
            (D ∩ closedBall (0 : E) r))
          atTop (nhds 0) := by
  constructor
  · intro hlim
    exact hlim.exists_tendsto_hausdorffEDist_inter_closedBall hCconv
  · rintro ⟨r₀, _hr₀, hhaus⟩
    exact pkConverges_of_tendsto_hausdorffEDist_inter_closedBall hDclosed hhaus

end ConvexTruncationLimits

section ConvexTruncationRegressions

/-- Regression: a constant unbounded closed ray satisfies the forward
truncation criterion. -/
example : ∃ r₀ : ℝ, 0 ≤ r₀ ∧ ∀ r : ℝ, r₀ ≤ r →
    Tendsto
      (fun _n : ℕ ↦ hausdorffEDist
        (Set.Ici (0 : ℝ) ∩ closedBall (0 : ℝ) r)
        (Set.Ici (0 : ℝ) ∩ closedBall (0 : ℝ) r))
      atTop (nhds 0) := by
  exact PKConverges.exists_tendsto_hausdorffEDist_inter_closedBall
    (pkConverges_const_of_isClosed isClosed_Ici) (fun _ ↦ convex_Ici 0)

/-- Regression: the reverse criterion handles points on truncation
boundaries; here every truncated set agrees identically with its target. -/
example : PKConverges (fun _ : ℕ ↦ Set.Icc (-1 : ℝ) 1) (Set.Icc (-1 : ℝ) 1) := by
  apply pkConverges_of_tendsto_hausdorffEDist_inter_closedBall (r₀ := 0) isClosed_Icc
  intro r hr
  simpa only [hausdorffEDist_self] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ENNReal)) atTop (nhds 0))

end ConvexTruncationRegressions

end RW
