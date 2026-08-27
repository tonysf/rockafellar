/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Convergence of solutions to convex systems

This file proves Theorem 4.32.  A simplex contained in the residual set
survives perturbation by Proposition 4.30(b), providing the exact correction
used in the book's proof.
-/

import Mathlib.Analysis.Normed.Affine.Convex
import RockafellarWets.Chapter4.ConvexHullConvergence
import RockafellarWets.Chapter4.ConvexInternalApproximation
import RockafellarWets.Chapter4.ConvexSystems
import RockafellarWets.Chapter4.FiniteUnions
import RockafellarWets.Chapter4.SetLimitExamples

open Bornology Filter Function Metric Set Topology
open scoped BigOperators Pointwise

namespace RW

section ConvexSystemConvergence

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The finite-dimensional characterization of the book's condition that
two convex sets cannot be separated, even improperly (Theorem 2.39). -/
def CannotBeSeparated (A B : Set F) : Prop :=
  0 ∈ interior (A - B)

private theorem inner_point_gives_subsequence_selection
    {G : Type*} [PseudoMetricSpace G] {A : ℕ → Set G} {x : G}
    (hx : x ∈ innerSetLimit A) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    ∃ (ψ : ℕ → ℕ) (y : ℕ → G), StrictMono ψ ∧
      (∀ n, y n ∈ A (φ (ψ n))) ∧ Tendsto y atTop (nhds x) := by
  have hxOuter : x ∈ outerSetLimit (A ∘ φ) :=
    innerSetLimit_subset_outerSetLimit _
      (innerSetLimit_subset_subsequence hφ hx)
  simpa only [Function.comp_apply] using
    (mem_outerSetLimit_iff_exists_subsequence.1 hxOuter)

omit [FiniteDimensional ℝ E] in
/-- **Theorem 4.32 (inner-limit assertion).** -/
theorem linearConstraintSet_subset_innerSetLimit
    {Xseq : ℕ → Set E} {X : Set E}
    {Dseq : ℕ → Set F} {D : Set F}
    {Lseq : ℕ → E →L[ℝ] F} {L : E →L[ℝ] F}
    (hXseqConv : ∀ n, Convex ℝ (Xseq n))
    (hDseqConv : ∀ n, Convex ℝ (Dseq n))
    (hXinner : X ⊆ innerSetLimit Xseq)
    (hDinner : D ⊆ innerSetLimit Dseq)
    (hL : Tendsto Lseq atTop (nhds L))
    (hnosep : CannotBeSeparated (L '' X) D) :
    linearConstraintSet X L D ⊆
      innerSetLimit
        (fun n ↦ linearConstraintSet (Xseq n) (Lseq n) (Dseq n)) := by
  intro xbar hxbar
  let R : Set F := L '' X - D
  have hRnhds : R ∈ nhds (0 : F) := by
    exact mem_interior_iff_mem_nhds.1 hnosep
  rcases exists_mem_interior_convexHull_affineBasis hRnhds with
    ⟨b, hzeroInterior, hbR⟩
  let I := Fin (Module.finrank ℝ F + 1)
  have hbMem : ∀ i : I, b i ∈ R := fun i ↦
    hbR (subset_convexHull ℝ _ (mem_range_self i))
  choose a haImage up hupD hres using fun i ↦ (Set.mem_sub.1 (hbMem i))
  choose xp hxpX hLxp using fun i ↦ haImage i
  have hres' : ∀ i, L (xp i) - up i = b i := by
    intro i
    rw [hLxp i]
    exact hres i
  let J := Option I
  let xPts : J → E := fun j ↦ match j with
    | none => xbar
    | some i => xp i
  let uPts : J → F := fun j ↦ match j with
    | none => L xbar
    | some i => up i
  have hxPtsInner : xPts ∈
      innerSetLimit (fun n ↦ dependentSetProduct (fun _ : J ↦ Xseq n)) := by
    apply dependentSetProduct_innerSetLimit_subset
    rw [mem_dependentSetProduct]
    intro j
    cases j with
    | none => exact hXinner hxbar.1
    | some i => exact hXinner (hxpX i)
  have huPtsInner : uPts ∈
      innerSetLimit (fun n ↦ dependentSetProduct (fun _ : J ↦ Dseq n)) := by
    apply dependentSetProduct_innerSetLimit_subset
    rw [mem_dependentSetProduct]
    intro j
    cases j with
    | none => exact hDinner hxbar.2
    | some i => exact hDinner (hupD i)
  by_contra hxNotInner
  simp only [mem_innerSetLimit] at hxNotInner
  push_neg at hxNotInner
  rcases hxNotInner with ⟨V, hV, hfrequentMiss⟩
  rcases extraction_of_frequently_atTop hfrequentMiss with
    ⟨φ, hφ, hφMiss⟩
  rcases inner_point_gives_subsequence_selection hxPtsInner hφ with
    ⟨ψ, xa, hψ, hxaMem, hxa⟩
  rcases inner_point_gives_subsequence_selection huPtsInner (hφ.comp hψ) with
    ⟨χ, ua, hχ, huaMem, hua⟩
  let ν : ℕ → ℕ := φ ∘ ψ ∘ χ
  let xa' : ℕ → J → E := xa ∘ χ
  have hν : StrictMono ν := (hφ.comp hψ).comp hχ
  have hxa' : Tendsto xa' atTop (nhds xPts) :=
    hxa.comp hχ.tendsto_atTop
  have hLν : Tendsto (Lseq ∘ ν) atTop (nhds L) :=
    hL.comp hν.tendsto_atTop
  let q : ℕ → F := fun n ↦ Lseq (ν n) (xa' n none) - ua n none
  let z : ℕ → I → F := fun n i ↦
    Lseq (ν n) (xa' n (some i)) - ua n (some i)
  have hq0 : Tendsto q atTop (nhds 0) := by
    have hEval : Tendsto (fun n ↦ Lseq (ν n) (xa' n none)) atTop
        (nhds (L xbar)) := by
      have hpair : Tendsto (fun n ↦ (xa' n none, Lseq (ν n))) atTop
          (nhds (xbar, L)) := by
        rw [nhds_prod_eq]
        exact (tendsto_pi_nhds.1 hxa' none).prodMk hLν
      simpa only [ContinuousLinearMap.apply_apply] using
        ((ContinuousLinearMap.apply ℝ F).continuous₂.tendsto (xbar, L)).comp hpair
    simpa [q, uPts] using hEval.sub (tendsto_pi_nhds.1 hua none)
  have hzB : Tendsto z atTop (nhds fun i ↦ b i) := by
    apply tendsto_pi_nhds.2
    intro i
    have hEval : Tendsto (fun n ↦ Lseq (ν n) (xa' n (some i))) atTop
        (nhds (L (xp i))) := by
      have hpair : Tendsto
          (fun n ↦ (xa' n (some i), Lseq (ν n))) atTop
          (nhds (xp i, L)) := by
        rw [nhds_prod_eq]
        exact (tendsto_pi_nhds.1 hxa' (some i)).prodMk hLν
      simpa only [ContinuousLinearMap.apply_apply] using
        ((ContinuousLinearMap.apply ℝ F).continuous₂.tendsto (xp i, L)).comp hpair
    simpa [z, uPts, hres' i] using
      hEval.sub (tendsto_pi_nhds.1 hua (some i))
  let Zseq : ℕ → Set F := fun n ↦ range (z n)
  let Z : Set F := range b
  have hZlim : PKConverges Zseq Z := by
    have hsingle : ∀ i : I,
        PKConverges (fun n ↦ ({z n i} : Set F)) ({b i} : Set F) := by
      intro i
      exact pkConverges_singleton_iff.2 (tendsto_pi_nhds.1 hzB i)
    simpa only [Zseq, Z, iUnion_singleton_eq_range] using
      (pkConverges_iUnion hsingle)
  have hzRangeBounded : IsBounded (range z) :=
    Metric.isBounded_range_of_tendsto z hzB
  rcases hzRangeBounded.subset_closedBall (0 : I → F) with ⟨M, hM⟩
  have hZbounded : ∀ n, Zseq n ⊆ closedBall (0 : F) M := by
    intro n y hy
    rcases hy with ⟨i, rfl⟩
    rw [mem_closedBall, dist_zero_right]
    exact (norm_le_pi_norm (z n) i).trans <| by
      simpa only [mem_closedBall, dist_zero_right] using hM (mem_range_self n)
  have hHullLim : PKConverges (fun n ↦ convexHull ℝ (Zseq n))
      (convexHull ℝ Z) :=
    hZlim.convexHull_of_uniformly_bounded isBounded_closedBall hZbounded
  rcases Metric.mem_nhds_iff.1
      (isOpen_interior.mem_nhds hzeroInterior) with
    ⟨r, hr, hrHull⟩
  have hhalf : 0 < r / 2 := half_pos hr
  have hclosedBallSub : closedBall (0 : F) (r / 2) ⊆
      interior (convexHull ℝ Z) :=
    (closedBall_subset_ball (half_lt_self hr)).trans hrHull
  have hsurvive : ∀ᶠ n in atTop,
      closedBall (0 : F) (r / 2) ⊆ interior (convexHull ℝ (Zseq n)) := by
    apply eventually_compact_subset_interior_of_inner_eq
      (fun n ↦ convexHull ℝ (Zseq n))
      (fun _ ↦ convex_convexHull ℝ _) hHullLim.inner_eq
      (isCompact_closedBall (0 : F) (r / 2)) hclosedBallSub
  have hxaBounded : IsBounded (range xa') :=
    Metric.isBounded_range_of_tendsto xa' hxa'
  rcases hxaBounded.subset_closedBall (0 : J → E) with ⟨A, hA⟩
  have hAnonneg : 0 ≤ A := by
    have hmem := hA (mem_range_self 0)
    rw [mem_closedBall] at hmem
    exact dist_nonneg.trans hmem
  rcases Metric.mem_nhds_iff.1 hV with ⟨δ, hδ, hballV⟩
  have hbaseClose : ∀ᶠ n in atTop, dist (xa' n none) xbar < δ / 2 :=
    (tendsto_pi_nhds.1 hxa' none).eventually
      (ball_mem_nhds xbar (half_pos hδ))
  let t : ℕ → ℝ := fun n ↦ Real.sqrt ‖q n‖
  have ht0 : Tendsto t atTop (nhds 0) := by
    simpa only [t, norm_zero, Real.sqrt_zero] using hq0.norm.sqrt
  have htSmall : ∀ᶠ n in atTop,
      t n < min 1 (min (r / 2) (δ / (2 * (A + ‖xbar‖ + 1)))) :=
    ht0.eventually <| Iio_mem_nhds <| by
      have hden : 0 < 2 * (A + ‖xbar‖ + 1) := by
        positivity
      exact lt_min zero_lt_one (lt_min hhalf (div_pos hδ hden))
  suffices hfalse : ∀ᶠ _n : ℕ in atTop, False by
    rcases (eventually_atTop.1 hfalse) with ⟨N, hN⟩
    exact hN N le_rfl
  filter_upwards [hsurvive, hbaseClose, htSmall] with n hnSurvive hnBase hnT
  have hxaMem' : xa' n ∈
      dependentSetProduct (fun _ : J ↦ Xseq (ν n)) := by
    exact hxaMem (χ n)
  have hqZeroOr : q n = 0 ∨ q n ≠ 0 := eq_or_ne _ _
  rcases hqZeroOr with hqZero | hqNe
  · have hfeas : xa' n none ∈
        linearConstraintSet (Xseq (ν n)) (Lseq (ν n)) (Dseq (ν n)) := by
      refine ⟨mem_dependentSetProduct.1 hxaMem' none, ?_⟩
      have huD := mem_dependentSetProduct.1 (huaMem n) none
      have heq : Lseq (ν n) (xa' n none) = ua n none := by
        exact sub_eq_zero.mp hqZero
      change Lseq (ν n) (xa' n none) ∈ Dseq (ν n)
      rw [heq]
      exact huD
    have hnonempty :
        (linearConstraintSet (Xseq (ν n)) (Lseq (ν n)) (Dseq (ν n)) ∩ V).Nonempty :=
      ⟨xa' n none, hfeas, hballV (by
        rw [mem_ball]
        exact hnBase.trans (half_lt_self hδ))⟩
    have hempty :
        linearConstraintSet (Xseq (ν n)) (Lseq (ν n)) (Dseq (ν n)) ∩ V = ∅ := by
      simpa only [ν, Function.comp_apply] using hφMiss (ψ (χ n))
    rw [hempty] at hnonempty
    exact Set.not_nonempty_empty hnonempty
  · have htPos : 0 < t n := by
      dsimp only [t]
      exact Real.sqrt_pos.2 (norm_pos_iff.2 hqNe)
    have htOne : t n < 1 := hnT.trans_le (min_le_left _ _)
    let wres : F := -(((1 - t n) / t n) • q n)
    have hwNorm : ‖wres‖ ≤ t n := by
      have htSq : (t n) ^ 2 = ‖q n‖ := by
        dsimp only [t]
        exact Real.sq_sqrt (norm_nonneg _)
      simp only [wres, norm_neg, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (sub_nonneg.mpr htOne.le) htPos.le)]
      rw [div_mul_eq_mul_div, ← htSq]
      field_simp [htPos.ne']
      nlinarith
    have hwBall : wres ∈ closedBall (0 : F) (r / 2) := by
      rw [mem_closedBall, dist_zero_right]
      exact hwNorm.trans (hnT.trans_le (min_le_right _ _ |>.trans
        (min_le_left _ _))).le
    have hwHull : wres ∈ convexHull ℝ (Zseq n) :=
      interior_subset (hnSurvive hwBall)
    rcases mem_convexHull_iff_exists_fintype.1 hwHull with
      ⟨κ, hκ, α, vtx, hα0, hα1, hvtx, hcombo⟩
    letI : Fintype κ := hκ
    choose idx hidx using fun k ↦ hvtx k
    let xmix : E := ∑ k, α k • xa' n (some (idx k))
    let umix : F := ∑ k, α k • ua n (some (idx k))
    have hxmix : xmix ∈ Xseq (ν n) := by
      rw [← (hXseqConv (ν n)).convexHull_eq]
      apply mem_convexHull_of_exists_fintype (w := α)
        (z := fun k ↦ xa' n (some (idx k))) hα0 hα1
      · exact fun k ↦ mem_dependentSetProduct.1 hxaMem' (some (idx k))
      · rfl
    have humix : umix ∈ Dseq (ν n) := by
      rw [← (hDseqConv (ν n)).convexHull_eq]
      apply mem_convexHull_of_exists_fintype (w := α)
        (z := fun k ↦ ua n (some (idx k))) hα0 hα1
      · exact fun k ↦ mem_dependentSetProduct.1 (huaMem n) (some (idx k))
      · rfl
    let xnew : E := (1 - t n) • xa' n none + t n • xmix
    have hxnewX : xnew ∈ Xseq (ν n) :=
      hXseqConv (ν n)
        (mem_dependentSetProduct.1 hxaMem' none) hxmix
        (sub_nonneg.mpr htOne.le) htPos.le (sub_add_cancel 1 (t n))
    have hLxnew : Lseq (ν n) xnew =
        (1 - t n) • ua n none + t n • umix := by
      have hresMix : Lseq (ν n) xmix - umix = wres := by
        calc
          Lseq (ν n) xmix - umix =
              ∑ k, α k •
                (Lseq (ν n) (xa' n (some (idx k))) -
                  ua n (some (idx k))) := by
            simp only [xmix, umix, map_sum, map_smul]
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro k _hk
            module
          _ = ∑ k, α k • z n (idx k) := by
            apply Finset.sum_congr rfl
            intro k _hk
            rfl
          _ = ∑ k, α k • vtx k := by
            apply Finset.sum_congr rfl
            intro k _hk
            rw [hidx k]
          _ = wres := hcombo
      have hbase : Lseq (ν n) (xa' n none) - ua n none = q n := rfl
      have hwEq : (1 - t n) • q n + t n • wres = 0 := by
        simp only [wres, smul_neg, smul_smul]
        have hcoef : t n * ((1 - t n) / t n) = 1 - t n := by
          field_simp [htPos.ne']
        rw [hcoef]
        simp
      apply sub_eq_zero.mp
      calc
        Lseq (ν n) xnew - ((1 - t n) • ua n none + t n • umix) =
            (1 - t n) • (Lseq (ν n) (xa' n none) - ua n none) +
              t n • (Lseq (ν n) xmix - umix) := by
          simp only [xnew, map_add, map_smul]
          module
        _ = (1 - t n) • q n + t n • wres := by rw [hbase, hresMix]
        _ = 0 := hwEq
    have hxnewFeas : xnew ∈
        linearConstraintSet (Xseq (ν n)) (Lseq (ν n)) (Dseq (ν n)) := by
      refine ⟨hxnewX, ?_⟩
      change Lseq (ν n) xnew ∈ Dseq (ν n)
      rw [hLxnew]
      exact hDseqConv (ν n)
        (mem_dependentSetProduct.1 (huaMem n) none) humix
        (sub_nonneg.mpr htOne.le) htPos.le (sub_add_cancel 1 (t n))
    have hxmixNorm : ‖xmix‖ ≤ A := by
      calc
        ‖xmix‖ ≤ ∑ k, ‖α k • xa' n (some (idx k))‖ := by
          exact norm_sum_le _ _
        _ = ∑ k, α k * ‖xa' n (some (idx k))‖ := by
          apply Finset.sum_congr rfl
          intro k _hk
          rw [norm_smul, Real.norm_of_nonneg (hα0 k)]
        _ ≤ ∑ k, α k * A := by
          apply Finset.sum_le_sum
          intro k _hk
          apply mul_le_mul_of_nonneg_left _ (hα0 k)
          exact (norm_le_pi_norm (xa' n) (some (idx k))).trans <| by
            simpa only [mem_closedBall, dist_zero_right] using hA (mem_range_self n)
        _ = A := by rw [← Finset.sum_mul, hα1, one_mul]
    have hxnewClose : dist xnew xbar < δ := by
      have hdistBase : ‖xa' n none - xbar‖ < δ / 2 := by
        simpa only [dist_eq_norm] using hnBase
      have htδ : t n * (A + ‖xbar‖ + 1) < δ / 2 := by
        have hden : 0 < 2 * (A + ‖xbar‖ + 1) := by positivity
        have hsmall := hnT.trans_le
          (min_le_right _ _ |>.trans (min_le_right _ _))
        have := (lt_div_iff₀ hden).1 hsmall
        nlinarith
      rw [dist_eq_norm]
      calc
        ‖xnew - xbar‖ =
            ‖(1 - t n) • (xa' n none - xbar) +
              t n • (xmix - xbar)‖ := by
          congr 1
          module
        _ ≤ ‖(1 - t n) • (xa' n none - xbar)‖ +
            ‖t n • (xmix - xbar)‖ := norm_add_le _ _
        _ ≤ ‖xa' n none - xbar‖ + t n * (‖xmix‖ + ‖xbar‖) := by
          rw [norm_smul, norm_smul,
            Real.norm_of_nonneg (sub_nonneg.mpr htOne.le),
            Real.norm_of_nonneg htPos.le]
          apply add_le_add
          · exact mul_le_of_le_one_left (norm_nonneg _)
              (sub_le_self 1 htPos.le)
          · exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) htPos.le
        _ < δ := by nlinarith
    have hnonempty :
        (linearConstraintSet (Xseq (ν n)) (Lseq (ν n)) (Dseq (ν n)) ∩ V).Nonempty :=
      ⟨xnew, hxnewFeas, hballV (by simpa only [mem_ball] using hxnewClose)⟩
    have hempty :
        linearConstraintSet (Xseq (ν n)) (Lseq (ν n)) (Dseq (ν n)) ∩ V = ∅ := by
      simpa only [ν, Function.comp_apply] using hφMiss (ψ (χ n))
    rw [hempty] at hnonempty
    exact Set.not_nonempty_empty hnonempty

omit [FiniteDimensional ℝ E] in
/-- **Theorem 4.32 (convergence assertion).** -/
theorem PKConverges.linearConstraintSet
    {Xseq : ℕ → Set E} {X : Set E}
    {Dseq : ℕ → Set F} {D : Set F}
    {Lseq : ℕ → E →L[ℝ] F} {L : E →L[ℝ] F}
    (hXlim : PKConverges Xseq X) (hDlim : PKConverges Dseq D)
    (hXseqConv : ∀ n, Convex ℝ (Xseq n))
    (hDseqConv : ∀ n, Convex ℝ (Dseq n))
    (hL : Tendsto Lseq atTop (nhds L))
    (hnosep : CannotBeSeparated (L '' X) D) :
    PKConverges
      (fun n ↦ linearConstraintSet (Xseq n) (Lseq n) (Dseq n))
      (linearConstraintSet X L D) := by
  have hinner := linearConstraintSet_subset_innerSetLimit
    hXseqConv hDseqConv hXlim.inner_eq.symm.subset
      hDlim.inner_eq.symm.subset hL hnosep
  have houter := outerSetLimit_linearConstraintSet_subset
    hXlim.outer_eq.subset hDlim.outer_eq.subset hL
  exact ⟨Set.Subset.antisymm
    ((innerSetLimit_subset_outerSetLimit _).trans houter) hinner,
    Set.Subset.antisymm houter
      (hinner.trans (innerSetLimit_subset_outerSetLimit _))⟩

omit [FiniteDimensional ℝ E] in
/-- **Theorem 4.32(a).** Preimages of converging convex sets converge when
the limiting set cannot be separated from the range of the limiting map. -/
theorem PKConverges.linearPreimage_of_cannotBeSeparated_range
    {Dseq : ℕ → Set F} {D : Set F}
    {Lseq : ℕ → E →L[ℝ] F} {L : E →L[ℝ] F}
    (hDlim : PKConverges Dseq D)
    (hDseqConv : ∀ n, Convex ℝ (Dseq n))
    (hL : Tendsto Lseq atTop (nhds L))
    (hnosep : CannotBeSeparated (range L) D) :
    PKConverges (fun n ↦ Lseq n ⁻¹' Dseq n) (L ⁻¹' D) := by
  have hnosep' : CannotBeSeparated (L '' (univ : Set E)) D := by
    simpa only [image_univ] using hnosep
  convert (PKConverges.linearConstraintSet
      (pkConverges_const_of_isClosed (D := (univ : Set E)) isClosed_univ)
      hDlim (fun _ ↦ convex_univ) hDseqConv hL hnosep') using 1 <;>
    ext x <;> simp [RW.linearConstraintSet]

omit [FiniteDimensional ℝ E] in
/-- **Theorem 4.32(b).** A converging sequence of surjective linear systems
with converging right-hand sides has converging solution sets.  This is the
coordinate-free form of the book's full-row-rank matrix assertion. -/
theorem PKConverges.linearFiber_of_surjective
    {bseq : ℕ → F} {b : F}
    {Lseq : ℕ → E →L[ℝ] F} {L : E →L[ℝ] F}
    (hb : Tendsto bseq atTop (nhds b))
    (hL : Tendsto Lseq atTop (nhds L))
    (hLsurj : Function.Surjective L) :
    PKConverges (fun n ↦ {x | Lseq n x = bseq n}) {x | L x = b} := by
  have hnosep : CannotBeSeparated (range L) ({b} : Set F) := by
    have hrange : range L = (univ : Set F) := Set.range_eq_univ.mpr hLsurj
    rw [hrange]
    have hsub : (univ : Set F) - {b} = univ := by
      have hleft : (univ : Set F) - {b} ⊆ univ := fun y _hy ↦ mem_univ y
      apply Set.Subset.antisymm hleft
      intro y _hy
      exact Set.mem_sub.2 ⟨y + b, mem_univ _, b, mem_singleton b, by module⟩
    rw [CannotBeSeparated, hsub, interior_univ]
    exact mem_univ 0
  have h := PKConverges.linearPreimage_of_cannotBeSeparated_range
    (Lseq := Lseq) (L := L) (Dseq := fun n ↦ {bseq n}) (D := {b})
    (pkConverges_singleton_iff.2 hb) (fun n ↦ convex_singleton (bseq n))
    hL hnosep
  exact h

/-- **Theorem 4.32(c), inner-limit form.** -/
theorem inter_innerSetLimit_subset_of_cannotBeSeparated
    {C₁ C₂ : ℕ → Set E}
    (hC₁conv : ∀ n, Convex ℝ (C₁ n))
    (hC₂conv : ∀ n, Convex ℝ (C₂ n))
    (hnosep : CannotBeSeparated (innerSetLimit C₁) (innerSetLimit C₂)) :
    innerSetLimit C₁ ∩ innerSetLimit C₂ ⊆
      innerSetLimit (fun n ↦ C₁ n ∩ C₂ n) := by
  let I : E →L[ℝ] E := ContinuousLinearMap.id ℝ E
  have h := linearConstraintSet_subset_innerSetLimit
    (Xseq := C₁) (X := innerSetLimit C₁)
    (Dseq := C₂) (D := innerSetLimit C₂)
    (Lseq := fun _ ↦ I) (L := I)
    hC₁conv hC₂conv Subset.rfl Subset.rfl tendsto_const_nhds
    (by simpa only [I, ContinuousLinearMap.id_apply, image_id'] using hnosep)
  simpa only [linearConstraintSet, I, ContinuousLinearMap.id_apply,
    preimage_id'] using h

/-- **Theorem 4.32(c), convergence form.** -/
theorem PKConverges.inter_of_cannotBeSeparated
    {C₁ C₂ : ℕ → Set E} {D₁ D₂ : Set E}
    (hC₁lim : PKConverges C₁ D₁) (hC₂lim : PKConverges C₂ D₂)
    (hC₁conv : ∀ n, Convex ℝ (C₁ n))
    (hC₂conv : ∀ n, Convex ℝ (C₂ n))
    (hnosep : CannotBeSeparated D₁ D₂) :
    PKConverges (fun n ↦ C₁ n ∩ C₂ n) (D₁ ∩ D₂) := by
  let I : E →L[ℝ] E := ContinuousLinearMap.id ℝ E
  have h := PKConverges.linearConstraintSet
    (Lseq := fun _ ↦ I) (L := I) hC₁lim hC₂lim
    hC₁conv hC₂conv tendsto_const_nhds
    (by simpa only [I, ContinuousLinearMap.id_apply, image_id'] using hnosep)
  simpa only [linearConstraintSet, I, ContinuousLinearMap.id_apply,
    preimage_id'] using h

end ConvexSystemConvergence

end RW
