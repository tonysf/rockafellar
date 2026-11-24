/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: Graphs and images under maximal monotonicity

Exercise 12.8: a mapping is maximal monotone exactly when its inverse is; a
maximal monotone mapping has closed graph, hence is outer semicontinuous; and
both the mapping and its inverse have closed convex values.

The graph of a maximal monotone mapping is the intersection, over its own
points, of the closed sets cut out by the monotonicity inequality.  The values
are convex by the argument of the book's guide: a convex combination of two
values satisfies the monotonicity inequality against the whole graph.
-/

import RockafellarWets.Chapter12.MonotoneOperations
import RockafellarWets.Chapter5.SemicontinuityCriteria

open Set Topology
open scoped InnerProductSpace

namespace RW

section MaximalGraphs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Exercise 12.8(a)**, one direction. -/
theorem SvMaximalMonotone.inv {T : E → Set E} (hT : SvMaximalMonotone T) :
    SvMaximalMonotone (svInv T) := by
  refine ⟨hT.1.inv, fun v x hx ↦ ?_⟩
  obtain ⟨x', v', hv', hlt⟩ := hT.2 x v hx
  exact ⟨v', x', hv', by rwa [real_inner_comm]⟩

/-- **Exercise 12.8(a).** `T` is maximal monotone if and only if `T⁻¹` is. -/
theorem svMaximalMonotone_svInv_iff {T : E → Set E} :
    SvMaximalMonotone (svInv T) ↔ SvMaximalMonotone T :=
  ⟨fun h ↦ by simpa only [svInv_svInv] using h.inv, SvMaximalMonotone.inv⟩

/-- The graph of a maximal monotone mapping is cut out by the monotonicity
inequality against its own points. -/
theorem SvMaximalMonotone.svGraph_eq_biInter {T : E → Set E} (hT : SvMaximalMonotone T) :
    svGraph T = ⋂ p ∈ svGraph T, {q : E × E | 0 ≤ ⟪q.2 - p.2, q.1 - p.1⟫_ℝ} := by
  ext q
  simp only [mem_iInter, mem_setOf_eq]
  constructor
  · intro hq p hp
    exact hT.1 hp hq
  · intro h
    exact hT.mem_of_forall_inner_nonneg fun x' v' hv' ↦ h (x', v') hv'

/-- **Exercise 12.8(b).** The graph of a maximal monotone mapping is closed. -/
theorem SvMaximalMonotone.isClosed_svGraph {T : E → Set E} (hT : SvMaximalMonotone T) :
    IsClosed (svGraph T) := by
  rw [hT.svGraph_eq_biInter]
  exact isClosed_biInter fun p _ ↦ isClosed_le continuous_const (by fun_prop)

/-- **Exercise 12.8(b).** A maximal monotone mapping is outer semicontinuous. -/
theorem SvMaximalMonotone.svOsc {T : E → Set E} (hT : SvMaximalMonotone T) : SvOsc T :=
  isClosed_svGraph_iff_svOsc.1 hT.isClosed_svGraph

/-- **Exercise 12.8(c).** A maximal monotone mapping has closed values. -/
theorem SvMaximalMonotone.isClosed_apply {T : E → Set E} (hT : SvMaximalMonotone T) (x : E) :
    IsClosed (T x) := by
  have h := hT.isClosed_svGraph.preimage (Continuous.prodMk continuous_const continuous_id :
    Continuous fun v : E ↦ (x, v))
  exact h

/-- **Exercise 12.8(c).** A maximal monotone mapping has convex values. -/
theorem SvMaximalMonotone.convex_apply {T : E → Set E} (hT : SvMaximalMonotone T) (x : E) :
    Convex ℝ (T x) := by
  intro v₀ h₀ v₁ h₁ a b ha hb hab
  refine hT.mem_of_forall_inner_nonneg fun x' v' hv' ↦ ?_
  have e : a • v₀ + b • v₁ - v' = a • (v₀ - v') + b • (v₁ - v') := by
    calc a • v₀ + b • v₁ - v' = a • v₀ + b • v₁ - (a + b) • v' := by rw [hab, one_smul]
    _ = a • (v₀ - v') + b • (v₁ - v') := by rw [add_smul, smul_sub, smul_sub]; abel
  rw [e, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  exact add_nonneg (mul_nonneg ha (hT.1 hv' h₀)) (mul_nonneg hb (hT.1 hv' h₁))

/-- **Exercise 12.8(c)** for the inverse mapping. -/
theorem SvMaximalMonotone.isClosed_svInv_apply {T : E → Set E} (hT : SvMaximalMonotone T)
    (v : E) : IsClosed (svInv T v) :=
  hT.inv.isClosed_apply v

/-- **Exercise 12.8(c)** for the inverse mapping. -/
theorem SvMaximalMonotone.convex_svInv_apply {T : E → Set E} (hT : SvMaximalMonotone T)
    (v : E) : Convex ℝ (svInv T v) :=
  hT.inv.convex_apply v

end MaximalGraphs

end RW
