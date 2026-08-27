/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Approximation by Finite Sets

This file proves the approximation statement in Proposition 4.45.
-/

import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Instances.RealVectorSpace
import RockafellarWets.Chapter4.FiniteUnions
import RockafellarWets.Chapter4.LocalSetDistances
import RockafellarWets.Chapter4.SetLimitExamples
import RockafellarWets.Chapter4.SetLimitCharacterizations

open Filter Metric Set Topology

namespace RW

section InternalFiniteApproximations

variable {E : Type*} [PseudoMetricSpace E] [ProperSpace E] [Nonempty E]

/-- **Proposition 4.45, finite-set approximation.** Every closed subset of a
proper metric space is the Painleve--Kuratowski limit of finite subsets.  The
approximants may be chosen inside the set itself. -/
theorem IsClosed.exists_finite_pkConverges
    {C : Set E} (hC : IsClosed C) :
    ∃ F : ℕ → Set E, (∀ n, (F n).Finite) ∧
      (∀ n, F n ⊆ C) ∧ PKConverges F C := by
  let o : E := Classical.choice ‹Nonempty E›
  have hcompact : ∀ n : ℕ,
      IsCompact (C ∩ closedBall o n) := by
    intro n
    apply Metric.isCompact_of_isClosed_isBounded
    · exact hC.inter isClosed_closedBall
    · exact isBounded_closedBall.subset inter_subset_right
  have hradius : ∀ n : ℕ, 0 < (1 / ((n : ℝ) + 1) : ℝ) := by
    intro n
    positivity
  choose F hFsub hFfinite hFcover using fun n ↦
    (hcompact n).finite_cover_balls (hradius n)
  have hFC : ∀ n, F n ⊆ C := fun n ↦
    (hFsub n).trans inter_subset_left
  have hinner : C ⊆ innerSetLimit F := by
    intro x hxC V hV
    rcases Metric.mem_nhds_iff.1 hV with ⟨e, he, heV⟩
    obtain ⟨N, hN⟩ := exists_nat_ge (dist x o)
    have hlarge : ∀ᶠ n : ℕ in atTop, dist x o ≤ (n : ℝ) := by
      filter_upwards [eventually_ge_atTop N] with n hn
      exact hN.trans (by exact_mod_cast hn)
    have hsmall : ∀ᶠ n : ℕ in atTop,
        1 / ((n : ℝ) + 1) < e :=
      tendsto_one_div_add_atTop_nhds_zero_nat.eventually
        (Iio_mem_nhds he)
    filter_upwards [hlarge, hsmall] with n hxn hne
    have hxtrunc : x ∈ C ∩ closedBall o n := by
      refine ⟨hxC, ?_⟩
      simpa only [mem_closedBall] using hxn
    rcases mem_iUnion₂.1 (hFcover n hxtrunc) with ⟨y, hyF, hxy⟩
    refine ⟨y, hyF, heV ?_⟩
    rw [mem_ball, dist_comm]
    exact (mem_ball.1 hxy).trans hne
  have houter : outerSetLimit F ⊆ C := by
    have hmono : outerSetLimit F ⊆
        outerSetLimit (fun _ : ℕ ↦ C) :=
      outerSetLimit_mono hFC
    simpa only [outerSetLimit_const, hC.closure_eq] using hmono
  refine ⟨F, hFfinite, hFC, ?_⟩
  constructor
  · exact Set.Subset.antisymm
      ((innerSetLimit_subset_outerSetLimit F).trans houter) hinner
  · exact Set.Subset.antisymm houter
      (hinner.trans (innerSetLimit_subset_outerSetLimit F))

end InternalFiniteApproximations

section DenseFiniteApproximations

variable {E : Type*} [PseudoMetricSpace E] [ProperSpace E] [Nonempty E]

/-- The finite approximants in Proposition 4.45 may be selected from any
dense subset of the ambient space. -/
theorem IsClosed.exists_finite_subset_dense_pkConverges
    {Q C : Set E} (hQ : Dense Q) (hC : IsClosed C) :
    ∃ F : ℕ → Set E, (∀ n, (F n).Finite) ∧
      (∀ n, F n ⊆ Q) ∧ PKConverges F C := by
  rcases RW.IsClosed.exists_finite_pkConverges hC with
    ⟨A, hAfin, hAC, hAlim⟩
  have hradius : ∀ n : ℕ, 0 < (1 / ((n : ℝ) + 1) : ℝ) := by
    intro n
    positivity
  have hnear : ∀ n : ℕ, ∀ a : E,
      ∃ q ∈ Q, q ∈ ball a (1 / ((n : ℝ) + 1)) := by
    intro n a
    exact hQ.exists_mem_open isOpen_ball
      ⟨a, mem_ball_self (hradius n)⟩
  choose q hqQ hqnear using hnear
  let F : ℕ → Set E := fun n ↦ q n '' A n
  have hFfinite : ∀ n, (F n).Finite := fun n ↦
    (hAfin n).image (q n)
  have hFQ : ∀ n, F n ⊆ Q := by
    intro n y
    rintro ⟨a, -, rfl⟩
    exact hqQ n a
  have hinner : C ⊆ innerSetLimit F := by
    intro x hxC V hV
    rcases Metric.mem_nhds_iff.1 hV with ⟨e, he, heV⟩
    have hxInner : x ∈ innerSetLimit A := by
      rw [hAlim.inner_eq]
      exact hxC
    have hhit : ∀ᶠ n in atTop,
        (A n ∩ ball x (e / 2)).Nonempty :=
      hxInner _ (ball_mem_nhds x (half_pos he))
    have hsmall : ∀ᶠ n : ℕ in atTop,
        1 / ((n : ℝ) + 1) < e / 2 :=
      tendsto_one_div_add_atTop_nhds_zero_nat.eventually
        (Iio_mem_nhds (half_pos he))
    filter_upwards [hhit, hsmall] with n hn hne
    rcases hn with ⟨a, haA, hax⟩
    refine ⟨q n a, ⟨a, haA, rfl⟩, heV ?_⟩
    rw [mem_ball]
    calc
      dist (q n a) x ≤ dist (q n a) a + dist a x := dist_triangle _ _ _
      _ < e / 2 + e / 2 := add_lt_add
        ((mem_ball.1 (hqnear n a)).trans hne) (mem_ball.1 hax)
      _ = e := by ring
  have houter : outerSetLimit F ⊆ C := by
    intro x hx
    rcases mem_outerSetLimit_iff_exists_subsequence.1 hx with
      ⟨φ, y, hφ, hyF, hyx⟩
    have hyImage : ∀ n, y n ∈ q (φ n) '' A (φ n) := by
      simpa only [F] using hyF
    choose a haA hay using hyImage
    have hε : Tendsto (fun n ↦ 1 / (((φ n : ℕ) : ℝ) + 1))
        atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    have hdistAY : Tendsto (fun n ↦ dist (a n) (y n))
        atTop (nhds 0) := by
      apply squeeze_zero (fun n ↦ dist_nonneg)
        (fun n ↦ (by
          rw [← hay n, dist_comm]
          exact (mem_ball.1 (hqnear (φ n) (a n))).le))
        hε
    have hdistYX : Tendsto (fun n ↦ dist (y n) x)
        atTop (nhds 0) :=
      tendsto_iff_dist_tendsto_zero.1 hyx
    have hax : Tendsto a atTop (nhds x) := by
      rw [tendsto_iff_dist_tendsto_zero]
      exact squeeze_zero (fun n ↦ dist_nonneg)
        (fun n ↦ dist_triangle (a n) (y n) x)
        (by simpa only [zero_add] using hdistAY.add hdistYX)
    have hxOuter : x ∈ outerSetLimit A :=
      mem_outerSetLimit_iff_exists_subsequence.2
        ⟨φ, a, hφ, haA, hax⟩
    rw [hAlim.outer_eq] at hxOuter
    exact hxOuter
  refine ⟨F, hFfinite, hFQ, ?_⟩
  constructor
  · exact Set.Subset.antisymm
      ((innerSetLimit_subset_outerSetLimit F).trans houter) hinner
  · exact Set.Subset.antisymm houter
      (hinner.trans (innerSetLimit_subset_outerSetLimit F))

/-- For a nonempty limit set, the approximants selected from a dense set can
themselves all be chosen nonempty.  This is the form needed to regard the
finite approximants as points of `cl-sets≠∅(E)` in Proposition 4.45. -/
theorem IsClosed.exists_nonempty_finite_subset_dense_pkConverges
    [T0Space E] {Q C : Set E} (hQ : Dense Q) (hC : IsClosed C)
    (hCne : C.Nonempty) :
    ∃ F : ℕ → Set E, (∀ n, (F n).Finite) ∧
      (∀ n, (F n).Nonempty) ∧ (∀ n, F n ⊆ Q) ∧
        PKConverges F C := by
  letI : MetricSpace E := MetricSpace.ofT0PseudoMetricSpace E
  rcases RW.IsClosed.exists_finite_subset_dense_pkConverges hQ hC with
    ⟨A, hAfin, hAQ, hAlim⟩
  rcases hCne with ⟨c, hcC⟩
  have hradius : ∀ n : ℕ, 0 < (1 / ((n : ℝ) + 1) : ℝ) := by
    intro n
    positivity
  have hnear : ∀ n : ℕ,
      ∃ q ∈ Q, q ∈ ball c (1 / ((n : ℝ) + 1)) := by
    intro n
    exact hQ.exists_mem_open isOpen_ball
      ⟨c, mem_ball_self (hradius n)⟩
  choose q hqQ hqnear using hnear
  have hqc : Tendsto q atTop (nhds c) := by
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero (fun n ↦ dist_nonneg)
      (fun n ↦ (mem_ball.1 (hqnear n)).le)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  let F : ℕ → Set E := fun n ↦ A n ∪ {q n}
  have hFfinite : ∀ n, (F n).Finite := fun n ↦
    (hAfin n).union (finite_singleton (q n))
  have hFne : ∀ n, (F n).Nonempty := fun n ↦
    ⟨q n, Or.inr (mem_singleton (q n))⟩
  have hFQ : ∀ n, F n ⊆ Q := by
    intro n x hx
    rcases hx with hx | hx
    · exact hAQ n hx
    · simpa only [mem_singleton_iff] using hx ▸ hqQ n
  have hsingleton : PKConverges (fun n ↦ ({q n} : Set E)) {c} :=
    pkConverges_singleton_iff.2 hqc
  have hunion : PKConverges F (C ∪ {c}) := by
    have h := pkConverges_iUnion (E := E) (C := fun b : Bool ↦
      cond b A (fun n ↦ ({q n} : Set E)))
      (D := fun b : Bool ↦ cond b C ({c} : Set E)) <| by
        intro b
        cases b <;> simp only [cond_false, cond_true]
        · exact hsingleton
        · exact hAlim
    have hseq : (fun n ↦ ⋃ b : Bool,
        (cond b A (fun k ↦ ({q k} : Set E))) n) = F := by
      funext n
      apply Set.Subset.antisymm
      · intro x hx
        rcases mem_iUnion.1 hx with ⟨b, hxb⟩
        cases b
        · exact Or.inr hxb
        · exact Or.inl hxb
      · intro x hx
        rcases hx with hx | hx
        · exact mem_iUnion_of_mem true hx
        · exact mem_iUnion_of_mem false hx
    have hlimit : (⋃ b : Bool, cond b C ({c} : Set E)) = C ∪ {c} := by
      rw [union_eq_iUnion]
    rw [hseq, hlimit] at h
    exact h
  refine ⟨F, hFfinite, hFne, hFQ, ?_⟩
  simpa only [union_singleton, insert_eq_of_mem hcC] using hunion

end DenseFiniteApproximations

section RationalCoordinates

/-- Points of R^n all of whose coordinates are rational. -/
def rationalCoordinatePoints (n : ℕ) : Set (Fin n → ℝ) :=
  Set.range (Pi.map fun _ : Fin n ↦ fun q : ℚ ↦ (q : ℝ))

/-- Rational-coordinate points are dense in finite-dimensional coordinate
space. -/
theorem dense_rationalCoordinatePoints (n : ℕ) :
    Dense (rationalCoordinatePoints n) := by
  exact DenseRange.piMap
    (fun _ : Fin n ↦ (Rat.denseRange_cast : DenseRange fun q : ℚ ↦ (q : ℝ)))

/-- **Proposition 4.45, rational-coordinate strengthening.** Every closed
subset of R^n is the set limit of finite sets of rational-coordinate
points. -/
theorem IsClosed.exists_finite_rational_pkConverges
    {n : ℕ} {C : Set (Fin n → ℝ)} (hC : IsClosed C) :
    ∃ F : ℕ → Set (Fin n → ℝ), (∀ k, (F k).Finite) ∧
      (∀ k, F k ⊆ rationalCoordinatePoints n) ∧
      PKConverges F C :=
  RW.IsClosed.exists_finite_subset_dense_pkConverges
    (dense_rationalCoordinatePoints n) hC

/-- Nonempty version of the rational-coordinate approximation in
Proposition 4.45, suitable for the nonempty closed-set hyperspace. -/
theorem IsClosed.exists_nonempty_finite_rational_pkConverges
    {n : ℕ} {C : Set (Fin n → ℝ)} (hC : IsClosed C) (hCne : C.Nonempty) :
    ∃ F : ℕ → Set (Fin n → ℝ), (∀ k, (F k).Finite) ∧
      (∀ k, (F k).Nonempty) ∧
      (∀ k, F k ⊆ rationalCoordinatePoints n) ∧
        PKConverges F C :=
  RW.IsClosed.exists_nonempty_finite_subset_dense_pkConverges
    (dense_rationalCoordinatePoints n) hC hCne

/-- The collection of all finite rational-coordinate subsets of R^n is
countable, the countability input in the separability clause of 4.45. -/
theorem countable_finite_rationalCoordinateSets (n : ℕ) :
    {F : Set (Fin n → ℝ) |
      F.Finite ∧ F ⊆ rationalCoordinatePoints n}.Countable := by
  apply Set.countable_setOf_finite_subset
  exact Set.countable_range _

/-- The nonempty finite rational-coordinate sets also form a countable
family, as required by the hyperspace separability conclusion of 4.45. -/
theorem countable_nonempty_finite_rationalCoordinateSets (n : ℕ) :
    {F : Set (Fin n → ℝ) |
      F.Finite ∧ F.Nonempty ∧ F ⊆ rationalCoordinatePoints n}.Countable := by
  apply (countable_finite_rationalCoordinateSets n).mono
  intro F hF
  exact ⟨hF.1, hF.2.2⟩

/-- The countable family used in Proposition 4.45, packaged as points of
the nonempty closed-set hyperspace. -/
def finiteRationalHyperspacePoints (n : ℕ) :
    Set (ClosedNonemptySet (Fin n → ℝ)) :=
  {F | (F : Set (Fin n → ℝ)).Finite ∧
    (F : Set (Fin n → ℝ)) ⊆ rationalCoordinatePoints n}

theorem countable_finiteRationalHyperspacePoints (n : ℕ) :
    (finiteRationalHyperspacePoints n).Countable := by
  change ((fun F : ClosedNonemptySet (Fin n → ℝ) ↦
    (F : Set (Fin n → ℝ))) ⁻¹' {F : Set (Fin n → ℝ) |
      F.Finite ∧ F ⊆ rationalCoordinatePoints n}).Countable
  exact (countable_finite_rationalCoordinateSets n).preimage
    SetLike.coe_injective

/-- Every point of the nonempty closed-set hyperspace is the
Painleve--Kuratowski limit of a sequence drawn from the countable rational
family. -/
theorem exists_finiteRationalHyperspacePoints_pkConverges
    {n : ℕ} (C : ClosedNonemptySet (Fin n → ℝ)) :
    ∃ F : ℕ → ClosedNonemptySet (Fin n → ℝ),
      (∀ k, F k ∈ finiteRationalHyperspacePoints n) ∧
        PKConverges (fun k ↦ (F k : Set (Fin n → ℝ)))
          (C : Set (Fin n → ℝ)) := by
  rcases RW.IsClosed.exists_nonempty_finite_rational_pkConverges
      C.isClosed C.nonempty with
    ⟨A, hAfin, hAne, hArat, hAlim⟩
  let F : ℕ → ClosedNonemptySet (Fin n → ℝ) := fun k ↦
    ⟨A k, (hAfin k).isClosed, hAne k⟩
  refine ⟨F, ?_, ?_⟩
  · intro k
    exact ⟨hAfin k, hArat k⟩
  · simpa only [F] using hAlim

end RationalCoordinates

end RW
