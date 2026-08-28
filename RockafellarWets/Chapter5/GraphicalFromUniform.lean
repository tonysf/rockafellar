/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Graphical Convergence from Uniform Convergence

Proposition 5.46.

Clause (a) is proved directly, in the `ε`-`ρ` inclusions rather than through
distances.  Outer semicontinuity passes to the limit by the same three-fold
composition as the last sentence of 5.43: `S(z)` reaches `Sν(z)` by uniform
convergence, `Sν(z)` reaches `Sν(x̄)` because `Sν` is osc, and `Sν(x̄)` reaches
`S(x̄)` by uniform convergence again -- one index chosen once serving all
three.  The two halves of relative graphical convergence then come cheaply:
the outer half composes uniform convergence with the outer semicontinuity just
proved, and the inner half is uniform convergence at the single point `x̄`,
where the second inclusion of Definition 5.41 already places `S(x̄)` inside the
pointwise inner limit.

Clause (b) is 5.43 followed by 5.44, exactly as the book says.

Both clauses need the limit to be closed-valued on `X`, which the printed
statement does not assume; see the ledger and
`svOscOn_not_automatic_without_closedValued` in
[`ContinuousVersusUniform.lean`](ContinuousVersusUniform.lean).  The book's own
proof of (a) uses it at the last step, concluding `ū ∈ S(x̄)` from
`d(ū, S(x̄)) ≤ 2ε` for every `ε > 0`.
-/

import RockafellarWets.Chapter5.ContinuousVersusUniform

open Filter Metric Set Topology

namespace RW

section OuterSemicontinuity

variable {E F : Type*} [PseudoMetricSpace E] [NormedAddCommGroup F] [ProperSpace F]
variable {Sseq : ℕ → E → Set F} {S : E → Set F} {X : Set E} {x : E}

/-- **Proposition 5.46(a)**, first conclusion, at a point: uniform convergence
carries outer semicontinuity to the limit. -/
theorem svOscWithinAt_of_svConvergesUniformlyOn (hx : x ∈ X)
    (hSn : ∀ n, SvOscWithinAt (Sseq n) X x)
    (hu : SvConvergesUniformlyOn Sseq S X) (hclx : IsClosed (S x)) :
    SvOscWithinAt S X x := by
  refine (svOscWithinAt_iff_exists_nhds_inter_closedBall_subset hclx).2
    fun ρ hρ ε hε ↦ ?_
  obtain ⟨n, hn⟩ := (hu (ε / 3) (by linarith) (ρ + ε) (by linarith)).exists
  obtain ⟨V, hV, hoscn⟩ :=
    (svOscWithinAt_iff_exists_nhds_inter_closedBall_subset ((hSn n).isClosed hx)).1
      (hSn n) (ρ + ε / 3) (by linarith) (ε / 3) (by linarith)
  refine ⟨V, hV, fun z hz ↦ ?_⟩
  have hstep := inter_closedBall_subset_thickening_trans (le_refl (ρ + ε / 3))
    (inter_closedBall_subset_of_le (by linarith) (hn z hz.1).2) (hoscn z hz)
  have hstep' := inter_closedBall_subset_thickening_trans
    (by linarith : ρ + (ε / 3 + ε / 3) ≤ ρ + ε / 3 + ε / 3) hstep
    (inter_closedBall_subset_of_le (by linarith) (hn x hx).1)
  have hsum : ε / 3 + ε / 3 + ε / 3 = ε := by ring
  rwa [hsum] at hstep'

/-- **Proposition 5.46(a)**, first conclusion. -/
theorem svOscOn_of_svConvergesUniformlyOn (hSn : ∀ n, SvOscOn (Sseq n) X)
    (hu : SvConvergesUniformlyOn Sseq S X) (hclosed : ∀ z ∈ X, IsClosed (S z)) :
    SvOscOn S X := fun x hx ↦
  svOscWithinAt_of_svConvergesUniformlyOn hx (fun n ↦ hSn n x hx) hu (hclosed x hx)

omit [PseudoMetricSpace E] [ProperSpace F] in
/-- Uniform convergence on `X` already places `S(x̄)` inside the pointwise
inner limit at each `x̄ ∈ X`: that is the second inclusion of Definition 5.41,
read at the single point `x̄`. -/
theorem subset_pointwiseInnerLimit_of_svConvergesUniformlyOn (hx : x ∈ X)
    (hu : SvConvergesUniformlyOn Sseq S X) : S x ⊆ pointwiseInnerLimit Sseq x := by
  intro ubar hubar
  refine mem_innerSetLimit_iff_eventually_ball.2 fun ε hε ↦ ?_
  filter_upwards [hu ε hε (‖ubar‖ + 1) (by positivity)] with n hn
  obtain ⟨w, hw, hdw⟩ := mem_thickening_iff.1
    ((hn x hx).2 ⟨hubar, mem_closedBall_zero_iff.2 (by linarith)⟩)
  exact ⟨w, hw, by rw [mem_ball, dist_comm]; exact hdw⟩

/-- **Proposition 5.46(a)**, second conclusion.

For the outer half, a value approached along `xν → x̄` in `X` is moved to
within `ε/3` of `S(xν)` by the uniform convergence and from there to within
`ε/3` of `S(x̄)` by the outer semicontinuity of `S` just established; the
remaining `ε/3` is the distance from the limit to the approaching values. -/
theorem graphicalConvergesOn_of_svConvergesUniformlyOn
    (hSn : ∀ n, SvOscOn (Sseq n) X) (hu : SvConvergesUniformlyOn Sseq S X)
    (hclosed : ∀ z ∈ X, IsClosed (S z)) : GraphicalConvergesOn Sseq S X := by
  have hosc := svOscOn_of_svConvergesUniformlyOn hSn hu hclosed
  intro x hx
  refine ⟨fun u hmem ↦ ?_,
    (subset_pointwiseInnerLimit_of_svConvergesUniformlyOn hx hu).trans
      (pointwiseInnerLimit_subset_graphicalInnerLimitWithin Sseq hx)⟩
  obtain ⟨φ, y, v, hφ, hyX, hv, hy, hvu⟩ :=
    (mem_graphicalOuterLimitWithin_iff_exists_subsequence hx).1 hmem
  rw [← (hclosed x hx).closure_eq, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨V, hV, hoscx⟩ :=
    (svOscWithinAt_iff_exists_nhds_inter_closedBall_subset (hclosed x hx)).1
      (hosc x hx) (‖u‖ + 1 + ε / 3) (by positivity) (ε / 3) (by linarith)
  have hev : ∀ᶠ _k : ℕ in atTop, ∃ s ∈ S x, dist u s < ε := by
    filter_upwards [hφ.tendsto_atTop.eventually
        (hu (ε / 3) (by linarith) (‖u‖ + 1 + ε / 3) (by positivity)),
      hvu.eventually_mem (ball_mem_nhds u one_pos),
      hvu.eventually_mem (ball_mem_nhds u (show (0 : ℝ) < ε / 3 by linarith)),
      hy.eventually_mem hV] with k hk hb1 hb2 hkV
    have hnorm : v k ∈ closedBall (0 : F) (‖u‖ + 1) := by
      rw [mem_closedBall_zero_iff]
      have h1 : ‖v k‖ - ‖u‖ ≤ dist (v k) u := by
        simpa only [dist_eq_norm] using norm_sub_norm_le (v k) u
      have h2 : dist (v k) u < 1 := mem_ball.1 hb1
      linarith
    have hcomp := inter_closedBall_subset_thickening_trans
      (le_refl (‖u‖ + 1 + ε / 3))
      (inter_closedBall_subset_of_le (by linarith) (hk (y k) (hyX k)).1)
      (hoscx (y k) ⟨hyX k, hkV⟩)
    obtain ⟨s, hs, hds⟩ := mem_thickening_iff.1 (hcomp ⟨hv k, hnorm⟩)
    refine ⟨s, hs, ?_⟩
    have h3 : dist u (v k) < ε / 3 := by
      rw [dist_comm]
      exact mem_ball.1 hb2
    calc dist u s ≤ dist u (v k) + dist (v k) s := dist_triangle _ _ _
      _ < ε := by linarith
  obtain ⟨-, hs⟩ := hev.exists
  exact hs

end OuterSemicontinuity

section ContinuousCase

variable {E F : Type*} [PseudoMetricSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {Sseq : ℕ → E → Set F} {S : E → Set F} {X : Set E}

/-- **Proposition 5.46(b)**: 5.43 turns uniform convergence on the compact
subsets of a locally compact `X` into continuous convergence relative to `X`,
and 5.44 turns that into relative graphical convergence. -/
theorem graphicalConvergesOn_of_svConvergesUniformlyOn_of_svContinuousOn
    (hSn : ∀ n, SvContinuousOn (Sseq n) X)
    (hu : ∀ B ⊆ X, IsCompact B → SvConvergesUniformlyOn Sseq S B)
    (hloc : ∀ z ∈ X, ∃ B ⊆ X, IsCompact B ∧ B ∈ nhdsWithin z X)
    (hclosed : ∀ z ∈ X, IsClosed (S z)) : GraphicalConvergesOn Sseq S X :=
  fun x hx ↦
    (svConvergesContinuouslyOn_of_svConvergesUniformlyOn hu
      (svContinuousOn_of_svConvergesUniformlyOn hSn hu hloc hclosed) x
      hx).graphicalConvergesWithinAt hx

end ContinuousCase

end RW
