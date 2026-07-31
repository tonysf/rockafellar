/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Pointwise Convergence of Distance Functions
-/

import RockafellarWets.Chapter4.HitAndMiss
import RockafellarWets.Chapter4.SetLimitDistances

open Filter Metric Set Topology

namespace RW

section ProperMetricSpace

variable {E : Type*} [PseudoMetricSpace E] [ProperSpace E]

/-- **Corollary 4.7(b).** The upper set-limit inclusion is equivalent to the
pointwise lower bound on distance liminfs. -/
theorem outerSetLimit_subset_iff_infEDist_le_liminf
    {C : Set E} {Cseq : ℕ → Set E} (hC : IsClosed C) :
    outerSetLimit Cseq ⊆ C ↔
      ∀ x : E, Metric.infEDist x C ≤
        liminf (fun n ↦ Metric.infEDist x (Cseq n)) atTop := by
  constructor
  · intro h x
    rw [le_liminf_iff]
    intro y hy
    rcases exists_between hy with ⟨z, hyz, hzC⟩
    have hzTop : z ≠ ⊤ :=
      ne_of_lt (hzC.trans_le le_top)
    have hzZero : z ≠ 0 :=
      ne_of_gt (bot_lt_of_lt hyz)
    have hzReal : 0 < z.toReal := ENNReal.toReal_pos hzZero hzTop
    have hdisj : Disjoint C (closedBall x z.toReal) := by
      rw [Set.disjoint_left]
      intro w hwC hwBall
      have hedLe : edist x w ≤ z := by
        rw [edist_dist, ← ENNReal.ofReal_toReal hzTop]
        exact ENNReal.ofReal_le_ofReal (by
          simpa only [dist_comm] using (Metric.mem_closedBall.1 hwBall))
      exact (not_le_of_gt hzC)
        ((Metric.infEDist_le_edist_of_mem hwC).trans hedLe)
    have hmiss : ∀ᶠ n in atTop, Disjoint (Cseq n) (closedBall x z.toReal) :=
      (outerSetLimit_subset_iff_eventually_misses_compact hC).1 h
        (closedBall x z.toReal) (isCompact_closedBall x z.toReal) hdisj
    exact hmiss.mono fun n hn ↦ hyz.trans_le <| Metric.le_infEDist.2 fun w hwC ↦ by
      by_contra hnot
      have hedLt : edist x w < z := lt_of_not_ge hnot
      have hdistLt : dist w x < z.toReal := by
        rw [dist_comm, ← ENNReal.ofReal_lt_ofReal_iff hzReal,
          ← edist_dist, ENNReal.ofReal_toReal hzTop]
        exact hedLt
      exact hn.le_bot ⟨hwC, Metric.mem_closedBall.2 hdistLt.le⟩
  · intro h x hxOuter
    have hzero : Metric.infEDist x C = 0 := by
      apply le_antisymm
      · exact (h x).trans_eq
          (mem_outerSetLimit_iff_liminf_infEDist.1 hxOuter)
      · exact bot_le
    exact (Metric.mem_iff_infEDist_zero_of_closed hC).2 hzero

/-- **Corollary 4.7 (pointwise distance convergence).** In a proper metric
space, Painleve--Kuratowski convergence to a closed set is equivalent to
pointwise convergence of the extended distance functions. -/
theorem pkConverges_iff_tendsto_infEDist
    {C : Set E} {Cseq : ℕ → Set E} (hC : IsClosed C) :
    PKConverges Cseq C ↔
      ∀ x : E, Tendsto (fun n ↦ Metric.infEDist x (Cseq n)) atTop
        (nhds (Metric.infEDist x C)) := by
  constructor
  · intro h x
    have hinf := (outerSetLimit_subset_iff_infEDist_le_liminf hC).1
      (h.outer_eq.subset) x
    have hsup := (subset_innerSetLimit_iff_limsup_infEDist_le).1
      (h.inner_eq.symm.subset) x
    exact tendsto_of_le_liminf_of_limsup_le hinf hsup
      (h := by isBoundedDefault) (h' := by isBoundedDefault)
  · intro h
    have hCInner : C ⊆ innerSetLimit Cseq :=
      (subset_innerSetLimit_iff_limsup_infEDist_le).2 fun x ↦
        (h x).limsup_eq.le
    have hOuterC : outerSetLimit Cseq ⊆ C :=
      (outerSetLimit_subset_iff_infEDist_le_liminf hC).2 fun x ↦
        (h x).liminf_eq.ge
    constructor
    · exact Set.Subset.antisymm
        ((innerSetLimit_subset_outerSetLimit Cseq).trans hOuterC) hCInner
    · exact Set.Subset.antisymm hOuterC
        (hCInner.trans (innerSetLimit_subset_outerSetLimit Cseq))

/-- **Exercise 4.8 (distance to the outer limit).** -/
theorem liminf_infEDist_eq_infEDist_outerSetLimit
    (Cseq : ℕ → Set E) (x : E) :
    liminf (fun n ↦ Metric.infEDist x (Cseq n)) atTop =
      Metric.infEDist x (outerSetLimit Cseq) := by
  apply le_antisymm
  · rw [Metric.le_infEDist]
    intro y hyOuter
    rcases mem_outerSetLimit_iff_exists_subsequence.1 hyOuter with
      ⟨φ, z, hφ, hzC, hzy⟩
    have hsubseq :
        liminf (fun n ↦ Metric.infEDist x (Cseq n)) atTop ≤
          liminf ((fun n ↦ Metric.infEDist x (Cseq n)) ∘ φ) atTop := by
      have hmap := liminf_le_liminf_of_le hφ.tendsto_atTop
        (f := atTop) (g := Filter.map φ atTop)
        (u := fun n ↦ Metric.infEDist x (Cseq n))
      simpa only [liminf_comp] using hmap
    have hpointwise : ∀ n,
        Metric.infEDist x (Cseq (φ n)) ≤ edist x (z n) := fun n ↦
      Metric.infEDist_le_edist_of_mem (hzC n)
    have hcompare :
        liminf ((fun n ↦ Metric.infEDist x (Cseq n)) ∘ φ) atTop ≤
          liminf (fun n ↦ edist x (z n)) atTop :=
      liminf_le_liminf (Eventually.of_forall hpointwise)
        (hu := by isBoundedDefault) (hv := by isBoundedDefault)
    exact hsubseq.trans <| hcompare.trans_eq
      (tendsto_const_nhds.edist hzy).liminf_eq
  · exact (outerSetLimit_subset_iff_infEDist_le_liminf
      (isClosed_outerSetLimit Cseq)).1 Set.Subset.rfl x

omit [ProperSpace E] in
/-- **Exercise 4.8 (distance to the inner limit).** Equality need not hold in
general, but the sharp universal inequality does. -/
theorem limsup_infEDist_le_infEDist_innerSetLimit
    (Cseq : ℕ → Set E) (x : E) :
    limsup (fun n ↦ Metric.infEDist x (Cseq n)) atTop ≤
      Metric.infEDist x (innerSetLimit Cseq) :=
  (subset_innerSetLimit_iff_limsup_infEDist_le).1 Set.Subset.rfl x

/-- **Corollary 4.11 (escape to the horizon).** A sequence has empty outer
limit exactly when its distance from one fixed base point tends to infinity. -/
theorem outerSetLimit_eq_empty_iff_tendsto_infEDist_top
    (Cseq : ℕ → Set E) (x₀ : E) :
    outerSetLimit Cseq = ∅ ↔
      Tendsto (fun n ↦ Metric.infEDist x₀ (Cseq n)) atTop (nhds ⊤) := by
  rw [← Metric.infEDist_eq_top_iff,
    ← liminf_infEDist_eq_infEDist_outerSetLimit]
  constructor
  · intro hinf
    exact tendsto_of_le_liminf_of_limsup_le
      hinf.ge le_top
      (h := by isBoundedDefault) (h' := by isBoundedDefault)
  · exact fun h ↦ h.liminf_eq

end ProperMetricSpace

end RW
