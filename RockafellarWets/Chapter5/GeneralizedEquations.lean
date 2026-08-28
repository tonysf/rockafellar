/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Approximation of Generalized Equations

Theorem 5.37.  Reading the generalized equation `Sν(x) ∋ ūν` as an
approximation to `S(x) ∋ ū`, the two graphical inclusions say exactly that
cluster points of approximate solutions are true solutions, and that true
solutions are limits of approximate solutions.

Both clauses are direct: (a) unfolds the definition of the graphical outer
limit, and (b) is the sequential description of the graphical inner limit
from 5.32, read through the inverse.  The printed hypothesis that `S` and the
`Sν` be closed-valued is not used by either clause and is dropped.
-/

import RockafellarWets.Chapter5.GraphicalLimitFormulas
import RockafellarWets.Chapter5.SemicontinuityCriteria

open Filter Metric Set Topology

namespace RW

section GeneralizedEquations

variable {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
variable {Sseq : ℕ → E → Set F} {S : E → Set F}

/-- **Theorem 5.37(a)**: every cluster point of approximate solutions is a
true solution. -/
theorem outerSetLimit_svInv_subset (h : ∀ x, graphicalOuterLimit Sseq x ⊆ S x)
    {us : ℕ → F} {u : F} (hus : Tendsto us atTop (nhds u)) :
    outerSetLimit (fun n ↦ svInv (Sseq n) (us n)) ⊆ svInv S u := by
  intro x hx
  obtain ⟨φ, y, hφ, hy, hyx⟩ := mem_outerSetLimit_iff_exists_subsequence.1 hx
  refine h x (mem_graphicalOuterLimit_iff.2
    ⟨φ, y, fun k ↦ us (φ k), hφ, hy, hyx, hus.comp hφ.tendsto_atTop⟩)

/-- **Theorem 5.37(b)**: every true solution is a limit of approximate
solutions, for some choice of right-hand sides converging to `ū`. -/
theorem exists_approximate_solutions (h : ∀ x, S x ⊆ graphicalInnerLimit Sseq x)
    {u : F} {x : E} (hx : x ∈ svInv S u) :
    ∃ (y : ℕ → E) (v : ℕ → F), (∀ᶠ n in atTop, y n ∈ svInv (Sseq n) (v n)) ∧
      Tendsto y atTop (nhds x) ∧ Tendsto v atTop (nhds u) :=
  mem_graphicalInnerLimit_iff.1 (h x hx)

/-- **Theorem 5.37(b)** in the printed form: true solutions lie in every inner
limit of the sets of `ε`-approximate solutions. -/
theorem svInv_subset_iInter_innerSetLimit_svPreimage
    (h : ∀ x, S x ⊆ graphicalInnerLimit Sseq x) (u : F) :
    svInv S u ⊆
      ⋂ ε ∈ Ioi (0 : ℝ),
        innerSetLimit (fun n ↦ svPreimage (Sseq n) (closedBall u ε)) := by
  intro x hx
  obtain ⟨y, v, hv, hy, hvu⟩ := exists_approximate_solutions h hx
  simp only [mem_iInter₂, mem_Ioi]
  intro ε hε
  refine mem_innerSetLimit_iff_exists_seq.2 ⟨y, ?_, hy⟩
  filter_upwards [hv, hvu.eventually_mem (closedBall_mem_nhds u hε)] with n hn hnball
  exact ⟨v n, hn, hnball⟩

/-- **Theorem 5.37(c)**: under graphical convergence both conclusions hold. -/
theorem GraphicalConverges.outerSetLimit_svInv_subset
    (hg : GraphicalConverges Sseq S) {us : ℕ → F} {u : F}
    (hus : Tendsto us atTop (nhds u)) :
    outerSetLimit (fun n ↦ svInv (Sseq n) (us n)) ⊆ svInv S u :=
  _root_.RW.outerSetLimit_svInv_subset (graphicalConverges_iff.1 hg).1 hus

/-- **Theorem 5.37(c)**, the inner conclusion. -/
theorem GraphicalConverges.svInv_subset_iInter
    (hg : GraphicalConverges Sseq S) (u : F) :
    svInv S u ⊆
      ⋂ ε ∈ Ioi (0 : ℝ),
        innerSetLimit (fun n ↦ svPreimage (Sseq n) (closedBall u ε)) :=
  svInv_subset_iInter_innerSetLimit_svPreimage (graphicalConverges_iff.1 hg).2 u

end GeneralizedEquations

end RW
