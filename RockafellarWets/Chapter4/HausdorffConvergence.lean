/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Pompeiu--Hausdorff Convergence

The extended Hausdorff distance in Mathlib is the book's
Pompeiu--Hausdorff distance, including its value `⊤` for sets at infinite
distance.  This file records the defining formula and the implication from
Hausdorff convergence to Painleve--Kuratowski convergence in Example 4.13.
-/

import Mathlib.Topology.MetricSpace.HausdorffDistance
import RockafellarWets.Chapter4.SetLimitDistances

open Filter Function Metric Set Topology

namespace RW

variable {E : Type*} [PseudoMetricSpace E]

/-- **Example 4.13.** The book's Pompeiu--Hausdorff distance, with extended
values so that unbounded or empty-set cases are represented without an extra
finiteness convention. -/
noncomputable abbrev pompeiuHausdorffEDist (C D : Set E) : ENNReal :=
  Metric.hausdorffEDist C D

/-- Formula 4(5), in its equivalent point-to-set-distance form. -/
theorem pompeiuHausdorffEDist_eq_sup_infEDist (C D : Set E) :
    pompeiuHausdorffEDist C D =
      (⨆ x ∈ C, Metric.infEDist x D) ⊔
        ⨆ y ∈ D, Metric.infEDist y C := by
  exact Metric.hausdorffEDist_def C D

/-- Pompeiu--Hausdorff convergence to a closed set entails ordinary
Painleve--Kuratowski convergence.  This is the unrestricted implication in
Example 4.13. -/
theorem pkConverges_of_tendsto_pompeiuHausdorffEDist_zero
    {Cseq : ℕ → Set E} {C : Set E} (hC : IsClosed C)
    (hH : Tendsto (fun n ↦ pompeiuHausdorffEDist (Cseq n) C)
      atTop (nhds 0)) :
    PKConverges Cseq C := by
  have hCInner : C ⊆ innerSetLimit Cseq := by
    intro x hxC
    rw [mem_innerSetLimit_iff_tendsto_infEDist, ENNReal.tendsto_nhds_zero]
    intro ε hε
    have hsmall : ∀ᶠ n in atTop,
        pompeiuHausdorffEDist (Cseq n) C ≤ ε :=
      (ENNReal.tendsto_nhds_zero.1 hH) ε hε
    exact hsmall.mono fun n hn ↦
      (Metric.infEDist_le_hausdorffEDist_of_mem hxC).trans <| by
        simpa only [pompeiuHausdorffEDist, Metric.hausdorffEDist_comm] using hn
  have hOuterC : outerSetLimit Cseq ⊆ C := by
    intro x hxOuter
    rcases mem_outerSetLimit_iff_exists_subsequence.1 hxOuter with
      ⟨φ, y, hφ, hyCseq, hyx⟩
    have hHsub : Tendsto
        (fun n ↦ pompeiuHausdorffEDist (Cseq (φ n)) C)
        atTop (nhds 0) := hH.comp hφ.tendsto_atTop
    have hdistZero : Tendsto (fun n ↦ Metric.infEDist (y n) C)
        atTop (nhds 0) := by
      rw [ENNReal.tendsto_nhds_zero]
      intro ε hε
      have hsmall := (ENNReal.tendsto_nhds_zero.1 hHsub) ε hε
      exact hsmall.mono fun n hn ↦
        (Metric.infEDist_le_hausdorffEDist_of_mem (hyCseq n)).trans hn
    have hdistAtX : Tendsto (fun n ↦ Metric.infEDist (y n) C)
        atTop (nhds (Metric.infEDist x C)) :=
      Metric.continuous_infEDist.continuousAt.tendsto.comp hyx
    have hzero : Metric.infEDist x C = 0 :=
      tendsto_nhds_unique hdistAtX hdistZero
    exact (Metric.mem_iff_infEDist_zero_of_closed hC).2 hzero
  constructor
  · exact Set.Subset.antisymm
      ((innerSetLimit_subset_outerSetLimit Cseq).trans hOuterC) hCInner
  · exact Set.Subset.antisymm hOuterC
      (hCInner.trans (innerSetLimit_subset_outerSetLimit Cseq))

end RW
