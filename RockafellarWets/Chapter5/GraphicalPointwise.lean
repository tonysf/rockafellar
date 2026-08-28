/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Graphical versus Pointwise Convergence

Theorem 5.40.  Asymptotic equi-outer semicontinuity at a point is exactly
what collapses the graphical limits there onto the pointwise ones.

By 5(11) the pointwise limits are always contained in the graphical ones, so
only the reverse inclusions are at issue, and both come from the same
computation: a value `uν ∈ Sν(xν)` with `xν → x̄` is trapped in a fixed ball,
so equi-outer semicontinuity moves it to within `ε` of `Sν(x̄)`, and `uν → ū`
carries `ū` there too.  The outer statement differs from the inner one only
in reading `∃ᶠ` for `∀ᶠ`.

The three-way statement follows: with (a) in hand, (b) and (c) are the same
condition, and the remaining implication (b) + (c) ⇒ (a) is the book's
contradiction argument, the only place where compactness of bounded sets in
the target is used.  Closed-valuedness, which the printed statement assumes,
is nowhere needed.
-/

import RockafellarWets.Chapter5.Equicontinuity
import RockafellarWets.Chapter5.GraphicalLimitFormulas

open Bornology Filter Metric Set Topology

namespace RW

section Collapse

variable {E F : Type*} [PseudoMetricSpace E] [NormedAddCommGroup F]
variable {Sseq : ℕ → E → Set F} {S : E → Set F} {x : E}

/-- **Theorem 5.40**, inner half: under asymptotic equi-outer semicontinuity
the graphical inner limit at `x̄` is the pointwise one. -/
theorem graphicalInnerLimit_eq_pointwiseInnerLimit
    (h : SvAsymptoticallyEquiOscAt Sseq x) :
    graphicalInnerLimit Sseq x = pointwiseInnerLimit Sseq x := by
  refine Subset.antisymm (fun u hu ↦ ?_)
    (pointwiseInnerLimit_subset_graphicalInnerLimit Sseq x)
  obtain ⟨y, v, hv, hy, hvu⟩ := mem_graphicalInnerLimit_iff.1 hu
  refine mem_innerSetLimit_iff_eventually_ball.2 fun ε hε ↦ ?_
  obtain ⟨V, hV, hsub⟩ := svAsymptoticallyEquiOscAt_iff.1 h (ε / 2) (by linarith)
    (‖u‖ + 1) (by positivity)
  filter_upwards [hv, hsub, hy.eventually_mem hV,
    hvu.eventually_mem (ball_mem_nhds u one_pos),
    hvu.eventually_mem (ball_mem_nhds u (half_pos hε))]
    with n hvn hsubn hyn hclose1 hclose
  have hnorm : v n ∈ closedBall (0 : F) (‖u‖ + 1) := by
    rw [mem_closedBall_zero_iff]
    have h1 : ‖v n‖ ≤ ‖v n - u‖ + ‖u‖ := by simpa using norm_add_le (v n - u) u
    rw [← dist_eq_norm] at h1
    have h2 : dist (v n) u < 1 := mem_ball.1 hclose1
    linarith
  obtain ⟨w, hwS, hwdist⟩ :=
    Metric.mem_thickening_iff.1 (hsubn (y n) hyn ⟨hvn, hnorm⟩)
  refine ⟨w, hwS, ?_⟩
  rw [mem_ball, dist_comm]
  have h3 : dist u w ≤ dist u (v n) + dist (v n) w := dist_triangle _ _ _
  have h4 : dist u (v n) < ε / 2 := by
    rw [dist_comm]
    exact mem_ball.1 hclose
  linarith

/-- **Theorem 5.40**, outer half. -/
theorem graphicalOuterLimit_eq_pointwiseOuterLimit
    (h : SvAsymptoticallyEquiOscAt Sseq x) :
    graphicalOuterLimit Sseq x = pointwiseOuterLimit Sseq x := by
  refine Subset.antisymm (fun u hu ↦ ?_)
    (pointwiseOuterLimit_subset_graphicalOuterLimit Sseq x)
  obtain ⟨φ, y, v, hφ, hv, hy, hvu⟩ := mem_graphicalOuterLimit_iff.1 hu
  refine mem_outerSetLimit_iff_frequently_ball.2 fun ε hε ↦ ?_
  obtain ⟨V, hV, hsub⟩ := svAsymptoticallyEquiOscAt_iff.1 h (ε / 2) (by linarith)
    (‖u‖ + 1) (by positivity)
  have hgoal : ∀ᶠ k in atTop, (Sseq (φ k) x ∩ ball u ε).Nonempty := by
    filter_upwards [hφ.tendsto_atTop.eventually hsub, hy.eventually_mem hV,
      hvu.eventually_mem (ball_mem_nhds u one_pos),
      hvu.eventually_mem (ball_mem_nhds u (half_pos hε))]
      with k hsubk hyk hclose1 hclose
    have hnorm : v k ∈ closedBall (0 : F) (‖u‖ + 1) := by
      rw [mem_closedBall_zero_iff]
      have h1 : ‖v k‖ ≤ ‖v k - u‖ + ‖u‖ := by simpa using norm_add_le (v k - u) u
      rw [← dist_eq_norm] at h1
      have h2 : dist (v k) u < 1 := mem_ball.1 hclose1
      linarith
    obtain ⟨w, hwS, hwdist⟩ :=
      Metric.mem_thickening_iff.1 (hsubk (y k) hyk ⟨hv k, hnorm⟩)
    refine ⟨w, hwS, ?_⟩
    rw [mem_ball, dist_comm]
    have h3 : dist u w ≤ dist u (v k) + dist (v k) w := dist_triangle _ _ _
    have h4 : dist u (v k) < ε / 2 := by
      rw [dist_comm]
      exact mem_ball.1 hclose
    linarith
  exact Frequently.filter_mono
    ((frequently_map (m := φ)).2 hgoal.frequently) hφ.tendsto_atTop

/-- Pointwise convergence at a single point, the notion the book uses in the
last paragraph of 5.31. -/
def PointwiseConvergesAt (Sseq : ℕ → E → Set F) (S : E → Set F) (x : E) : Prop :=
  PKConverges (fun n ↦ Sseq n x) (S x)

omit [PseudoMetricSpace E] in
theorem pointwiseConvergesAt_iff :
    PointwiseConvergesAt Sseq S x ↔
      pointwiseOuterLimit Sseq x ⊆ S x ∧ S x ⊆ pointwiseInnerLimit Sseq x := by
  constructor
  · intro h
    exact ⟨h.outer_eq.subset, h.inner_eq.ge⟩
  · rintro ⟨ho, hi⟩
    exact ⟨Subset.antisymm ((innerSetLimit_subset_outerSetLimit _).trans ho) hi,
      Subset.antisymm ho (hi.trans (innerSetLimit_subset_outerSetLimit _))⟩

/-- **Theorem 5.40**, (a) and (b) give (c). -/
theorem PointwiseConvergesAt.of_graphicalConvergesAt
    (ha : SvAsymptoticallyEquiOscAt Sseq x) (hb : GraphicalConvergesAt Sseq S x) :
    PointwiseConvergesAt Sseq S x := by
  refine pointwiseConvergesAt_iff.2
    ⟨?_, hb.2.trans (graphicalInnerLimit_eq_pointwiseInnerLimit ha).subset⟩
  rw [← graphicalOuterLimit_eq_pointwiseOuterLimit ha]
  exact hb.1

/-- **Theorem 5.40**, (a) and (c) give (b). -/
theorem GraphicalConvergesAt.of_pointwiseConvergesAt
    (ha : SvAsymptoticallyEquiOscAt Sseq x) (hc : PointwiseConvergesAt Sseq S x) :
    GraphicalConvergesAt Sseq S x := by
  obtain ⟨ho, hi⟩ := pointwiseConvergesAt_iff.1 hc
  exact ⟨(graphicalOuterLimit_eq_pointwiseOuterLimit ha).subset.trans ho,
    hi.trans (graphicalInnerLimit_eq_pointwiseInnerLimit ha).symm.subset⟩

/-- **Theorem 5.40**, the global form: an everywhere asymptotically equi-osc
sequence converges graphically exactly when it converges pointwise. -/
theorem graphicalConverges_iff_pointwiseConverges
    (ha : ∀ x, SvAsymptoticallyEquiOscAt Sseq x) :
    GraphicalConverges Sseq S ↔ PointwiseConverges Sseq S := by
  rw [graphicalConverges_iff_forall_graphicalConvergesAt]
  constructor
  · exact fun h x ↦ PointwiseConvergesAt.of_graphicalConvergesAt (ha x) (h x)
  · exact fun h x ↦ GraphicalConvergesAt.of_pointwiseConvergesAt (ha x) (h x)

end Collapse

section Converse

variable {E F : Type*} [PseudoMetricSpace E] [NormedAddCommGroup F] [ProperSpace F]
variable {Sseq : ℕ → E → Set F} {S : E → Set F} {x : E}

/-- **Theorem 5.40**, (b) and (c) give (a).

If the sequence were not asymptotically equi-osc, one could pick values
`uν ∈ Sν(yν) ∩ ρIB` with `yν → x̄` staying `ε` away from `Sν(x̄)`.  Those
values are bounded, so a cluster point `ū` of them exists; it lies in the
graphical outer limit, hence in `S(x̄)` by (b), hence in the pointwise inner
limit by (c) -- which puts points of `Sν(x̄)` arbitrarily close to it, and so
to the `uν`. -/
theorem svAsymptoticallyEquiOscAt_of_graphicalConvergesAt_of_pointwiseConvergesAt
    (hb : GraphicalConvergesAt Sseq S x) (hc : PointwiseConvergesAt Sseq S x) :
    SvAsymptoticallyEquiOscAt Sseq x := by
  by_contra hcon
  rw [svAsymptoticallyEquiOscAt_iff] at hcon
  push_neg at hcon
  obtain ⟨ε, hε, ρ, hρ, hbad⟩ := hcon
  -- Choose escaping data along shrinking neighborhoods and late indices.
  have hpick : ∀ k : ℕ, ∃ (n : ℕ) (y : E) (u : F), k ≤ n ∧
      dist y x < ((k : ℝ) + 1)⁻¹ ∧ u ∈ Sseq n y ∧ ‖u‖ ≤ ρ ∧
        u ∉ thickening ε (Sseq n x) := by
    intro k
    have hδ : (0 : ℝ) < ((k : ℝ) + 1)⁻¹ := by positivity
    obtain ⟨n, hn, y, hyV, hysub⟩ :=
      frequently_atTop.1 (hbad (ball x ((k : ℝ) + 1)⁻¹) (ball_mem_nhds x hδ)) k
    obtain ⟨u, huS, hunot⟩ := not_subset.1 hysub
    exact ⟨n, y, u, hn, mem_ball.1 hyV, huS.1,
      by simpa [mem_closedBall_zero_iff] using huS.2, hunot⟩
  choose ns ys us hns hys huS huρ hunot using hpick
  have hnsTop : Tendsto ns atTop atTop := tendsto_atTop_mono hns tendsto_id
  have hysTo : Tendsto ys atTop (nhds x) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun k ↦ dist_nonneg) (fun k ↦ (hys k).le) ?_
    simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  -- A cluster point of the escaping values.
  obtain ⟨ubar, -, ψ, hψ, huto⟩ :=
    (isCompact_closedBall (0 : F) ρ).tendsto_subseq
      (fun k ↦ by rw [mem_closedBall_zero_iff]; exact huρ k)
  have hnψ : Tendsto (fun k ↦ ns (ψ k)) atTop atTop := hnsTop.comp hψ.tendsto_atTop
  -- It is in the graphical outer limit, hence in `S(x̄)`.
  have hbarOuter : ubar ∈ graphicalOuterLimit Sseq x := by
    intro W hW
    obtain ⟨V₁, hV₁, V₂, hV₂, hsub⟩ := mem_nhds_prod_iff.1 hW
    have hev : ∀ᶠ k in atTop,
        (svGraph (Sseq (ns (ψ k))) ∩ W).Nonempty := by
      filter_upwards [(hysTo.comp hψ.tendsto_atTop).eventually_mem hV₁,
        huto.eventually_mem hV₂] with k hk1 hk2
      exact ⟨(ys (ψ k), us (ψ k)), huS (ψ k), hsub ⟨hk1, hk2⟩⟩
    exact Frequently.filter_mono
      ((frequently_map (m := fun k ↦ ns (ψ k))).2 hev.frequently) hnψ
  have hbarS : ubar ∈ S x := hb.1 hbarOuter
  -- By (c) the values at `x̄` come arbitrarily close to it.
  have hbarInner : ubar ∈ innerSetLimit (fun n ↦ Sseq n x) :=
    (pointwiseConvergesAt_iff.1 hc).2 hbarS
  have hnear : ∀ᶠ n in atTop, (Sseq n x ∩ ball ubar (ε / 2)).Nonempty :=
    (mem_innerSetLimit_iff_eventually_ball.1 hbarInner) (ε / 2) (by linarith)
  obtain ⟨k, ⟨w, hwS, hwball⟩, hclose⟩ :=
    ((hnψ.eventually hnear).and
      (huto.eventually_mem (ball_mem_nhds ubar (by linarith : (0 : ℝ) < ε / 2)))).exists
  refine hunot (ψ k) (Metric.mem_thickening_iff.2 ⟨w, hwS, ?_⟩)
  have h1 : dist (us (ψ k)) ubar < ε / 2 := mem_ball.1 hclose
  have h2 : dist ubar w < ε / 2 := by rwa [mem_ball, dist_comm] at hwball
  calc dist (us (ψ k)) w ≤ dist (us (ψ k)) ubar + dist ubar w := dist_triangle _ _ _
    _ < ε := by linarith

end Converse

end RW
