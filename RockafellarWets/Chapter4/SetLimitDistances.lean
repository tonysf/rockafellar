/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Distance Characterizations of Set Limits

Extended distances are used throughout, so the formulas remain exact for
empty sets.  In particular, the inner-limit criterion is genuine convergence
of `Metric.infEDist` to zero and the outer-limit criterion is its liminf being
zero.
-/

import Mathlib.Topology.Order.LiminfLimsup
import RockafellarWets.Chapter4.SetLimitCharacterizations

open Filter Metric Set Topology

namespace RW

section ExtendedDistance

variable {E : Type*} [PseudoEMetricSpace E]

/-- Outer-limit membership in terms of frequent small extended distance. -/
theorem mem_outerSetLimit_iff_frequently_infEDist_lt
    {C : ℕ → Set E} {x : E} :
    x ∈ outerSetLimit C ↔
      ∀ ε : ENNReal, 0 < ε →
        ∃ᶠ n in atTop, Metric.infEDist x (C n) < ε := by
  constructor
  · intro hx ε hε
    have hhit := hx (Metric.eball x ε) (Metric.eball_mem_nhds x hε)
    exact hhit.mono fun n ⟨y, hyC, hyBall⟩ ↦
      Metric.infEDist_lt_iff.2 ⟨y, hyC, Metric.mem_eball'.1 hyBall⟩
  · intro hx V hV
    rcases Metric.nhds_basis_eball.mem_iff.1 hV with ⟨ε, hε, hball⟩
    exact (hx ε hε).mono fun n hn ↦ by
      rcases Metric.infEDist_lt_iff.1 hn with ⟨y, hyC, hyDist⟩
      exact ⟨y, hyC, hball (Metric.mem_eball'.2 hyDist)⟩

/-- Inner-limit membership in terms of eventual small extended distance. -/
theorem mem_innerSetLimit_iff_eventually_infEDist_lt
    {C : ℕ → Set E} {x : E} :
    x ∈ innerSetLimit C ↔
      ∀ ε : ENNReal, 0 < ε →
        ∀ᶠ n in atTop, Metric.infEDist x (C n) < ε := by
  constructor
  · intro hx ε hε
    have hhit := hx (Metric.eball x ε) (Metric.eball_mem_nhds x hε)
    exact hhit.mono fun n ⟨y, hyC, hyBall⟩ ↦
      Metric.infEDist_lt_iff.2 ⟨y, hyC, Metric.mem_eball'.1 hyBall⟩
  · intro hx V hV
    rcases Metric.nhds_basis_eball.mem_iff.1 hV with ⟨ε, hε, hball⟩
    exact (hx ε hε).mono fun n hn ↦ by
      rcases Metric.infEDist_lt_iff.1 hn with ⟨y, hyC, hyDist⟩
      exact ⟨y, hyC, hball (Metric.mem_eball'.2 hyDist)⟩

/-- **Theorem 4.2 (inner distance formula).** -/
theorem mem_innerSetLimit_iff_tendsto_infEDist
    {C : ℕ → Set E} {x : E} :
    x ∈ innerSetLimit C ↔
      Tendsto (fun n ↦ Metric.infEDist x (C n)) atTop (nhds 0) := by
  rw [mem_innerSetLimit_iff_eventually_infEDist_lt]
  constructor
  · intro h
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    exact (h ε hε).mono fun _ hn ↦ hn.le
  · intro h ε hε
    exact h.eventually (Iio_mem_nhds hε)

/-- The `limsup` form of the inner distance formula in Exercise 4.2(a). -/
theorem mem_innerSetLimit_iff_limsup_infEDist
    {C : ℕ → Set E} {x : E} :
    x ∈ innerSetLimit C ↔
      limsup (fun n ↦ Metric.infEDist x (C n)) atTop = 0 := by
  rw [mem_innerSetLimit_iff_tendsto_infEDist]
  constructor
  · exact fun h ↦ h.limsup_eq
  · intro hsup
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    have hlt : limsup (fun n ↦ Metric.infEDist x (C n)) atTop < ε := by
      rw [hsup]
      exact hε
    exact (eventually_lt_of_limsup_lt hlt).mono fun _ hn ↦ hn.le

/-- **Theorem 4.2 (outer distance formula).** -/
theorem mem_outerSetLimit_iff_liminf_infEDist
    {C : ℕ → Set E} {x : E} :
    x ∈ outerSetLimit C ↔
      liminf (fun n ↦ Metric.infEDist x (C n)) atTop = 0 := by
  rw [mem_outerSetLimit_iff_frequently_infEDist_lt]
  constructor
  · intro h
    apply le_antisymm
    · rw [liminf_le_iff]
      exact h
    · exact bot_le
  · intro h
    have hzero : liminf (fun n ↦ Metric.infEDist x (C n)) atTop ≤ 0 := by
      rw [h]
    rw [liminf_le_iff] at hzero
    exact hzero

/-- **Corollary 4.7(a).** The lower set-limit inclusion is equivalent to the
corresponding pointwise upper bound on distance limsups. -/
theorem subset_innerSetLimit_iff_limsup_infEDist_le
    {C : Set E} {Cseq : ℕ → Set E} :
    C ⊆ innerSetLimit Cseq ↔
      ∀ x : E,
        limsup (fun n ↦ Metric.infEDist x (Cseq n)) atTop ≤
          Metric.infEDist x C := by
  constructor
  · intro h x
    rw [limsup_le_iff]
    intro ε hε
    rcases Metric.infEDist_lt_iff.1 hε with ⟨y, hyC, hyDist⟩
    have hhit : ∀ᶠ n in atTop, (Cseq n ∩ Metric.eball x ε).Nonempty :=
      h hyC (Metric.eball x ε)
        (Metric.isOpen_eball.mem_nhds (Metric.mem_eball'.2 hyDist))
    exact hhit.mono fun n ⟨z, hzC, hzBall⟩ ↦
      Metric.infEDist_lt_iff.2 ⟨z, hzC, Metric.mem_eball'.1 hzBall⟩
  · intro h x hxC
    rw [mem_innerSetLimit_iff_limsup_infEDist]
    apply le_antisymm
    · exact (h x).trans_eq (Metric.infEDist_zero_of_mem hxC)
    · exact bot_le

end ExtendedDistance

end RW
