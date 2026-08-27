/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Properties of Pompeiu--Hausdorff Distance

This file proves the three clauses of Exercise 4.40: equivalence with set
convergence for a uniformly bounded sequence, the horizon-cone obstruction
at finite distance, and the Hausdorff metric on closed nonempty subsets of a
bounded set.
-/

import Mathlib.Topology.MetricSpace.Closeds
import RockafellarWets.Chapter3.SetOperations
import RockafellarWets.Chapter4.ConvexTruncations

open Bornology Filter Function Metric Set TopologicalSpace Topology
open scoped ENNReal Pointwise

namespace RW

section BoundedSequences

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Exercise 4.40(a).  Uniform boundedness upgrades
Painleve--Kuratowski convergence to Pompeiu--Hausdorff convergence. -/
theorem pkConverges_iff_tendsto_pompeiuHausdorffEDist_of_bounded_sequence
    {Cseq : ℕ → Set E} {C B : Set E} (hCclosed : IsClosed C)
    (hBbounded : IsBounded B) (hCseqB : ∀ n, Cseq n ⊆ B) :
    PKConverges Cseq C ↔
      Tendsto (fun n ↦ pompeiuHausdorffEDist (Cseq n) C) atTop (nhds 0) := by
  constructor
  · intro hlim
    have hCB : C ⊆ closure B := by
      rw [← hlim.outer_eq, ← outerSetLimit_const B]
      exact outerSetLimit_mono hCseqB
    exact (pkConverges_iff_tendsto_pompeiuHausdorffEDist_of_common_bounded
      hCclosed hBbounded.closure (fun n ↦ (hCseqB n).trans subset_closure) hCB).1 hlim
  · exact pkConverges_of_tendsto_pompeiuHausdorffEDist_zero hCclosed

end BoundedSequences

section HorizonObstruction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem subset_add_closedBall_of_hausdorffEDist_ne_top
    {C D : Set E} (hDclosed : IsClosed D) (hDne : D.Nonempty)
    (hfinite : hausdorffEDist C D ≠ ⊤) :
    C ⊆ D + closedBall (0 : E) (hausdorffDist C D) := by
  intro x hxC
  rcases hDclosed.exists_infDist_eq_dist hDne x with ⟨y, hyD, hy⟩
  have hdist : dist x y ≤ hausdorffDist C D := by
    rw [← hy]
    exact infDist_le_hausdorffDist_of_mem hxC hfinite
  rw [Set.mem_add]
  refine ⟨y, hyD, x - y, ?_, by abel⟩
  rw [mem_closedBall, dist_zero_right, ← dist_eq_norm]
  exact hdist

/-- Exercise 4.40(b), pointwise form: unequal horizon cones force infinite
Pompeiu--Hausdorff distance. -/
theorem hausdorffEDist_eq_top_of_horizonCone_ne
    {C D : Set E} (hCclosed : IsClosed C) (hDclosed : IsClosed D)
    (hCne : C.Nonempty) (hDne : D.Nonempty)
    (hhorizon : horizonCone C ≠ horizonCone D) :
    hausdorffEDist C D = ⊤ := by
  by_contra hfinite
  apply hhorizon
  apply Subset.antisymm
  · have hsub := subset_add_closedBall_of_hausdorffEDist_ne_top
      hDclosed hDne hfinite
    calc
      horizonCone C ⊆
          horizonCone (D + closedBall (0 : E) (hausdorffDist C D)) :=
        horizonCone_mono hsub
      _ = horizonCone D := horizonCone_add_eq_of_bounded_right
        (by
          refine ⟨0, ?_⟩
          exact mem_closedBall_self (hausdorffDist_nonneg (s := C) (t := D)))
        isBounded_closedBall
  · have hfinite' : hausdorffEDist D C ≠ ⊤ := by
      rwa [hausdorffEDist_comm]
    have hsub := subset_add_closedBall_of_hausdorffEDist_ne_top
      hCclosed hCne hfinite'
    calc
      horizonCone D ⊆
          horizonCone (C + closedBall (0 : E) (hausdorffDist D C)) :=
        horizonCone_mono hsub
      _ = horizonCone C := horizonCone_add_eq_of_bounded_right
        (by
          refine ⟨0, ?_⟩
          exact mem_closedBall_self (hausdorffDist_nonneg (s := D) (t := C)))
        isBounded_closedBall

/-- Exercise 4.40(b), sequential consequence: convergence in
Pompeiu--Hausdorff distance forces eventual equality of horizon cones. -/
theorem eventually_horizonCone_eq_of_tendsto_pompeiuHausdorffEDist
    {Cseq : ℕ → Set E} {C : Set E} (hCclosed : IsClosed C)
    (hCne : C.Nonempty) (hCseqclosed : ∀ n, IsClosed (Cseq n))
    (hCseqne : ∀ n, (Cseq n).Nonempty)
    (hlim : Tendsto (fun n ↦ pompeiuHausdorffEDist (Cseq n) C)
      atTop (nhds 0)) :
    ∀ᶠ n in atTop, horizonCone (Cseq n) = horizonCone C := by
  have hfinite : ∀ᶠ n in atTop,
      pompeiuHausdorffEDist (Cseq n) C ≤ 1 :=
    (ENNReal.tendsto_nhds_zero.1 hlim) 1 (by norm_num)
  exact hfinite.mono fun n hn ↦ by
    by_contra hne
    have htop := hausdorffEDist_eq_top_of_horizonCone_ne
      (hCseqclosed n) hCclosed (hCseqne n) hCne hne
    change hausdorffEDist (Cseq n) C ≤ 1 at hn
    rw [htop] at hn
    exact ENNReal.not_top_le_coe hn

end HorizonObstruction

section BoundedHyperspace

/-- The space denoted `cl-sets≠∅(X)` in Exercise 4.40(c). -/
def ClosedNonemptySubsetsOf (E : Type*) [TopologicalSpace E] (X : Set E) :=
  {C : Set E // IsClosed C ∧ C.Nonempty ∧ C ⊆ X}

namespace ClosedNonemptySubsetsOf

variable {E : Type*} [TopologicalSpace E] {X : Set E}

instance : SetLike (ClosedNonemptySubsetsOf E X) E where
  coe C := C.1
  coe_injective' _ _ h := Subtype.ext h

theorem isClosed (C : ClosedNonemptySubsetsOf E X) : IsClosed (C : Set E) :=
  C.property.1

theorem nonempty (C : ClosedNonemptySubsetsOf E X) : (C : Set E).Nonempty :=
  C.property.2.1

theorem subset (C : ClosedNonemptySubsetsOf E X) : (C : Set E) ⊆ X :=
  C.property.2.2

end ClosedNonemptySubsetsOf

namespace ClosedNonemptySubsetsOf

variable {E : Type*} {X : Set E}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A closed nonempty subset of a bounded finite-dimensional set is a
nonempty compact set. -/
noncomputable def toNonemptyCompacts (hX : IsBounded X)
    (C : ClosedNonemptySubsetsOf E X) : NonemptyCompacts E :=
  ⟨⟨(C : Set E), isCompact_iff_isClosed_bounded.2
    ⟨C.isClosed, hX.subset C.subset⟩⟩, C.nonempty⟩

theorem toNonemptyCompacts_injective (hX : IsBounded X) :
    Function.Injective (toNonemptyCompacts hX) := by
  intro C D h
  apply SetLike.coe_injective
  exact congrArg (fun K : NonemptyCompacts E ↦ (K : Set E)) h

/-- Exercise 4.40(c): the metric structure on closed nonempty subsets of a
bounded set, pulled back from the Hausdorff metric on nonempty compact sets. -/
noncomputable def metricSpace (hX : IsBounded X) :
    MetricSpace (ClosedNonemptySubsetsOf E X) :=
  MetricSpace.induced (toNonemptyCompacts hX)
    (toNonemptyCompacts_injective hX) inferInstance

/-- Under the metric from Exercise 4.40(c), distance is exactly the
Pompeiu--Hausdorff distance. -/
theorem dist_eq_hausdorffDist (hX : IsBounded X)
    (C D : ClosedNonemptySubsetsOf E X) :
    @dist (ClosedNonemptySubsetsOf E X) (metricSpace hX).toDist C D =
      hausdorffDist (C : Set E) (D : Set E) :=
  NonemptyCompacts.dist_eq

end ClosedNonemptySubsetsOf

end BoundedHyperspace

end RW
