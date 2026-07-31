/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Internal Approximation of Convex Set Limits

This file proves the compact internal-approximation clause of Theorem 4.15
of Rockafellar--Wets.  The proof uses normalized separating functionals and
compactness of the dual unit sphere in finite dimensions.
-/

import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.MetricSpace.Sequences
import RockafellarWets.Chapter4.ConvexLimits

open Bornology Filter Function Metric Set Topology

namespace RW

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem interior_closure_eq_interior_of_convex {S : Set E}
    [FiniteDimensional ℝ E] (hS : Convex ℝ S) :
    interior (closure S) = interior S := by
  by_cases hSne : (interior S).Nonempty
  · exact hS.interior_closure_eq_interior_of_nonempty_interior hSne
  · have hSempty : interior S = ∅ := not_nonempty_iff_eq_empty.1 hSne
    rw [hSempty]
    apply eq_empty_iff_forall_notMem.2
    intro x hx
    apply hSne
    rw [Convex.interior_nonempty_iff_affineSpan_eq_top hS]
    apply top_unique
    have hclosureSub : closure S ⊆ affineSpan ℝ S :=
      closure_minimal (subset_affineSpan ℝ S)
        (affineSpan ℝ S).closed_of_finiteDimensional
    have hspanClosure : affineSpan ℝ (closure S) = ⊤ :=
      (Convex.interior_nonempty_iff_affineSpan_eq_top hS.closure).1 ⟨x, hx⟩
    rw [← hspanClosure]
    exact affineSpan_le.2 hclosureSub

private theorem tendsto_dual_apply
    {f : ℕ → StrongDual ℝ E} {f₀ : StrongDual ℝ E}
    {x : ℕ → E} {x₀ : E}
    (hf : Tendsto f atTop (nhds f₀)) (hx : Tendsto x atTop (nhds x₀)) :
    Tendsto (fun n ↦ f n (x n)) atTop (nhds (f₀ x₀)) := by
  have hp : Tendsto (fun n ↦ (x n, f n)) atTop (nhds (x₀, f₀)) := by
    rw [nhds_prod_eq]
    exact hx.prodMk hf
  simpa only [ContinuousLinearMap.apply_apply] using
    ((ContinuousLinearMap.apply ℝ ℝ).continuous₂.tendsto (x₀, f₀)).comp hp

end Helpers

section InternalApproximation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **Theorem 4.15 (compact internal approximation).** If `B` is compact and
contained in the interior of the inner limit of convex sets, then `B` is
eventually contained in the interiors of the terms. -/
theorem eventually_compact_subset_interior_innerSetLimit
    (C : ℕ → Set E) (hCconv : ∀ n, Convex ℝ (C n))
    {B : Set E} (hBcompact : IsCompact B)
    (hBsub : B ⊆ interior (innerSetLimit C)) :
    ∀ᶠ n in atTop, B ⊆ interior (C n) := by
  by_contra hnot
  rw [not_eventually] at hnot
  have hfail : ∃ᶠ n in atTop, ∃ x ∈ B, x ∉ interior (C n) := by
    simpa only [Set.not_subset] using hnot
  rcases extraction_of_frequently_atTop hfail with ⟨φ, hφ, hφfail⟩
  choose q hqB hqNot using hφfail
  rcases hBcompact.tendsto_subseq hqB with ⟨x, hxB, ψ, hψ, hqx⟩
  let i : ℕ → ℕ := φ ∘ ψ
  let p : ℕ → E := q ∘ ψ
  have hi : StrictMono i := hφ.comp hψ
  have hpB : ∀ n, p n ∈ B := fun n ↦ hqB (ψ n)
  have hpNot : ∀ n, p n ∉ interior (C (i n)) := fun n ↦ hqNot (ψ n)
  have hpx : Tendsto p atTop (nhds x) := hqx
  have hxInner : x ∈ innerSetLimit C := interior_subset (hBsub hxB)
  have hCne : ∀ᶠ n in atTop, (C n).Nonempty := by
    exact (hxInner Set.univ univ_mem).mono fun n ⟨y, hyC, _hyUniv⟩ ↦ ⟨y, hyC⟩
  have hCneI : ∀ᶠ n in atTop, (C (i n)).Nonempty :=
    hi.tendsto_atTop.eventually hCne
  rcases extraction_of_eventually_atTop hCneI with ⟨θ, hθ, hθne⟩
  let j : ℕ → ℕ := i ∘ θ
  let a : ℕ → E := p ∘ θ
  have hj : StrictMono j := hi.comp hθ
  have haNot : ∀ n, a n ∉ interior (C (j n)) := fun n ↦ hpNot (θ n)
  have hax : Tendsto a atTop (nhds x) := hpx.comp hθ.tendsto_atTop
  have hCneJ : ∀ n, (C (j n)).Nonempty := hθne
  let e : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hepos : ∀ n, 0 < e n := fun n ↦ by dsimp [e]; positivity
  have he0 : Tendsto e atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hzExists : ∀ n, ∃ z : E,
      z ∈ ball (a n) (e n) ∧ z ∉ closure (C (j n)) := by
    intro n
    have haNotClosure : a n ∉ interior (closure (C (j n))) := by
      rw [interior_closure_eq_interior_of_convex (hCconv (j n))]
      exact haNot n
    have hnotNhds : closure (C (j n)) ∉ nhds (a n) := by
      rwa [← mem_interior_iff_mem_nhds]
    have hnotSub : ¬ ball (a n) (e n) ⊆ closure (C (j n)) := by
      intro hsub
      exact hnotNhds (mem_of_superset (ball_mem_nhds _ (hepos n)) hsub)
    simpa only [Set.not_subset] using hnotSub
  choose z hzBall hzOutside using hzExists
  have hsepExists : ∀ n, ∃ (f : StrongDual ℝ E) (u : ℝ),
      f (z n) < u ∧ ∀ y ∈ closure (C (j n)), u < f y := by
    intro n
    exact geometric_hahn_banach_point_closed
      (hCconv (j n)).closure isClosed_closure (hzOutside n)
  choose f u hfz hfC using hsepExists
  have hfne : ∀ n, f n ≠ 0 := by
    intro n hzero
    rcases hCneJ n with ⟨y, hyC⟩
    have hlow := hfz n
    have hhigh := hfC n y (subset_closure hyC)
    simp only [hzero, ContinuousLinearMap.zero_apply] at hlow hhigh
    linarith
  let g : ℕ → StrongDual ℝ E := fun n ↦ NormedSpace.normalize (f n)
  have hgnorm : ∀ n, ‖g n‖ = 1 := fun n ↦ NormedSpace.norm_normalize (hfne n)
  have hgSphere : ∀ n, g n ∈ sphere (0 : StrongDual ℝ E) 1 := by
    intro n
    simpa only [mem_sphere, dist_zero_right] using hgnorm n
  rcases (isCompact_sphere (0 : StrongDual ℝ E) 1).tendsto_subseq hgSphere with
    ⟨g₀, hg₀Sphere, ξ, hξ, hgg₀⟩
  have hg₀ne : g₀ ≠ 0 := by
    intro hzero
    subst g₀
    have hzero_one : (0 : ℝ) = 1 := by
      simpa only [mem_sphere, dist_self] using hg₀Sphere
    exact zero_ne_one hzero_one
  have hvExists : ∃ v : E, g₀ v ≠ 0 := by
    by_contra h
    push_neg at h
    apply hg₀ne
    ext v
    exact h v
  rcases hvExists with ⟨v, hv⟩
  let w : E := if 0 < g₀ v then -v else v
  have hgw : g₀ w < 0 := by
    dsimp only [w]
    split_ifs with hvpos
    · simpa only [map_neg, neg_lt_zero] using hvpos
    · exact lt_of_le_of_ne (le_of_not_gt hvpos) (fun h ↦ hv h)
  rcases Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 (hBsub hxB)) with
    ⟨δ, hδ, hballInner⟩
  let τ : ℝ := δ / (2 * (‖w‖ + 1))
  have hdenom : 0 < 2 * (‖w‖ + 1) := by positivity
  have hτ : 0 < τ := div_pos hδ hdenom
  let y₀ : E := x + τ • w
  have hy₀Ball : y₀ ∈ ball x δ := by
    simp only [mem_ball, y₀, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos hτ, τ]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hdenom]
    nlinarith [norm_nonneg w]
  have hy₀Inner : y₀ ∈ innerSetLimit C := hballInner hy₀Ball
  have hgy₀ : g₀ y₀ < g₀ x := by
    simp only [y₀, map_add, map_smul, smul_eq_mul]
    linarith [mul_neg_of_pos_of_neg hτ hgw]
  have hhits : ∀ k : ℕ,
      ∀ᶠ n in atTop, (C (j (ξ n)) ∩ ball y₀ (e k)).Nonempty := by
    intro k
    exact (hj.comp hξ).tendsto_atTop.eventually
      (mem_innerSetLimit_iff_eventually_ball.1 hy₀Inner _ (hepos k))
  rcases extraction_forall_of_eventually hhits with ⟨μ, hμ, hhit⟩
  choose y hyC hyBall using hhit
  have hyy₀ : Tendsto y atTop (nhds y₀) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n ↦ dist_nonneg)
      (fun n ↦ (mem_ball.1 (hyBall n)).le) he0
  have hgSub : Tendsto (fun n ↦ g (ξ (μ n))) atTop (nhds g₀) :=
    hgg₀.comp hμ.tendsto_atTop
  have haSub : Tendsto (fun n ↦ a (ξ (μ n))) atTop (nhds x) :=
    hax.comp (hξ.comp hμ).tendsto_atTop
  have heSub : Tendsto (fun n ↦ e (ξ (μ n))) atTop (nhds 0) :=
    he0.comp (hξ.comp hμ).tendsto_atTop
  have hsepNorm : ∀ n, g n (a n) - e n < g n (z n) := by
    intro n
    have hdistApply : dist (g n (a n)) (g n (z n)) < e n :=
      (g n).dist_le_opNorm (a n) (z n) |>.trans_lt <| by
        rw [hgnorm n, one_mul, dist_comm]
        exact mem_ball.1 (hzBall n)
    rw [Real.dist_eq] at hdistApply
    linarith [le_abs_self (g n (a n) - g n (z n))]
  have hsepC : ∀ n, ∀ y' ∈ C (j n), g n (z n) < g n y' := by
    intro n y' hy'
    have hraw : f n (z n) < f n y' :=
      (hfz n).trans (hfC n y' (subset_closure hy'))
    have hscale : 0 < ‖f n‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr (hfne n))
    simpa only [g, NormedSpace.normalize, ContinuousLinearMap.smul_apply, smul_eq_mul] using
      (mul_lt_mul_of_pos_left hraw hscale)
  have hineq : ∀ n,
      g (ξ (μ n)) (a (ξ (μ n))) - e (ξ (μ n)) <
        g (ξ (μ n)) (y n) := by
    intro n
    exact (hsepNorm (ξ (μ n))).trans
      (hsepC (ξ (μ n)) (y n) (hyC n))
  have hEvalA : Tendsto
      (fun n ↦ g (ξ (μ n)) (a (ξ (μ n)))) atTop (nhds (g₀ x)) :=
    tendsto_dual_apply hgSub haSub
  have hEvalY : Tendsto
      (fun n ↦ g (ξ (μ n)) (y n)) atTop (nhds (g₀ y₀)) :=
    tendsto_dual_apply hgSub hyy₀
  have hleft : Tendsto
      (fun n ↦ g (ξ (μ n)) (a (ξ (μ n))) - e (ξ (μ n))) atTop
        (nhds (g₀ x)) := by
    simpa only [sub_zero] using hEvalA.sub heSub
  have hle : g₀ x ≤ g₀ y₀ :=
    le_of_tendsto_of_tendsto' hleft hEvalY fun n ↦ (hineq n).le
  exact (not_le_of_gt hgy₀) hle

/-- The same compact-approximation conclusion for a named inner limit `D`. -/
theorem eventually_compact_subset_interior_of_inner_eq
    (C : ℕ → Set E) (hCconv : ∀ n, Convex ℝ (C n))
    {D B : Set E} (hinner : innerSetLimit C = D)
    (hBcompact : IsCompact B) (hBsub : B ⊆ interior D) :
    ∀ᶠ n in atTop, B ⊆ interior (C n) := by
  apply eventually_compact_subset_interior_innerSetLimit C hCconv hBcompact
  simpa only [hinner] using hBsub

end InternalApproximation

section InternalApproximationRegressions

/-- Regression: every compact subset of the open unit interval is eventually
inside the interiors of a constant sequence of closed unit intervals. -/
example {B : Set ℝ} (hBcompact : IsCompact B)
    (hBsub : B ⊆ Set.Ioo (-1 : ℝ) 1) :
    ∀ᶠ _n : ℕ in atTop, B ⊆ interior (Set.Icc (-1 : ℝ) 1) := by
  apply eventually_compact_subset_interior_innerSetLimit
    (fun _ : ℕ ↦ Set.Icc (-1 : ℝ) 1) (fun _ ↦ convex_Icc _ _) hBcompact
  simpa only [innerSetLimit_const, isClosed_Icc.closure_eq, interior_Icc] using hBsub

end InternalApproximationRegressions

end RW
