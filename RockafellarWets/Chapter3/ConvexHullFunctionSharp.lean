/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3F: Sharp finite representations of convex hull functions

This file sharpens the finite representation in `ConvexHullFunctions` from
the ambient Carathéodory bound `finrank E + 2` to the boundary-point bound
`finrank E + 1`.
-/

import RockafellarWets.Chapter3.ConvexHullFunctions
import Mathlib.Analysis.Normed.Affine.AddTorsorBases

open Set EReal Filter Topology
open scoped BigOperators Pointwise

namespace RW

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- A point on the finite graph of an extended-real-valued function is not an
interior point of its epigraph. -/
lemma graphPoint_not_mem_interior_epigraph
    {f : E → EReal} {x : E} {r : ℝ} (hr : (r : EReal) = f x) :
    (x, r) ∉ interior (epigraph f) := by
  intro h
  rw [mem_interior_iff_mem_nhds] at h
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp h
  have hε2 : 0 < ε / 2 := half_pos hε
  have hmem : (x, r - ε / 2) ∈ epigraph f := by
    apply hball
    simp only [Metric.mem_ball, Prod.dist_eq, dist_self, max_lt_iff,
      Real.dist_eq]
    constructor
    · exact hε
    · rw [show r - ε / 2 - r = -(ε / 2) by ring, abs_neg,
        abs_of_pos hε2]
      linarith
  have hle : f x ≤ ((r - ε / 2 : ℝ) : EReal) :=
    (mem_epigraph_iff f x (r - ε / 2)).mp hmem
  rw [← hr] at hle
  exact (not_le_of_gt
    (EReal.coe_lt_coe_iff.mpr (sub_lt_self r hε2))) hle

/-- Boundary-point Carathéodory theorem, in positive-span form.  A boundary
point of a convex hull in a `d`-dimensional space uses at most `d` points,
rather than the ambient `d + 1` bound. -/
theorem eq_pos_convex_span_of_mem_boundary_convexHull
    [FiniteDimensional ℝ E] {s : Set E} {x : E}
    (hx : x ∈ convexHull ℝ s) (hxi : x ∉ interior (convexHull ℝ s)) :
    ∃ (ι : Sort (u + 1)) (_ : Fintype ι),
      ∃ (z : ι → E) (w : ι → ℝ),
        Fintype.card ι ≤ Module.finrank ℝ E ∧
        Set.range z ⊆ s ∧ AffineIndependent ℝ z ∧
        (∀ i, 0 < w i) ∧
        ∑ i, w i = 1 ∧ ∑ i, w i • z i = x := by
  obtain ⟨ι, hι, z, w, hzs, hzai, hwpos, hwone, hwsum⟩ :=
    eq_pos_convex_span_of_mem_convexHull (𝕜 := ℝ) hx
  refine ⟨ι, hι, z, w, ?_, hzs, hzai, hwpos, hwone, hwsum⟩
  have hcard :
      Fintype.card ι ≤ Module.finrank ℝ E + 1 := by
    exact hzai.card_le_finrank_succ.trans
      (Nat.add_le_add_right (Submodule.finrank_le _) 1)
  by_contra hnot
  have hcard_eq :
      Fintype.card ι = Module.finrank ℝ E + 1 := by
    omega
  let b : AffineBasis ι ℝ E :=
    ⟨z, hzai,
      hzai.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr hcard_eq⟩
  have hxcomb :
      Finset.univ.affineCombination ℝ b w = x := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hwone]
    exact hwsum
  have hxint :
      x ∈ interior (convexHull ℝ (Set.range z)) := by
    rw [show Set.range z = Set.range b by rfl, b.interior_convexHull]
    intro i
    rw [← hxcomb, b.coord_apply_combination_of_mem
      (Finset.mem_univ i) hwone]
    exact hwpos i
  exact hxi (interior_mono (convexHull_mono hzs) hxint)

/-- Finset form of boundary-point Carathéodory. -/
theorem exists_finite_convexCombination_of_mem_boundary_convexHull
    [FiniteDimensional ℝ E] {s : Set E} {x : E}
    (hx : x ∈ convexHull ℝ s) (hxi : x ∉ interior (convexHull ℝ s)) :
    ∃ (T : Finset E) (w : E → ℝ),
      T.card ≤ Module.finrank ℝ E ∧
      (↑T : Set E) ⊆ s ∧
      (∀ p ∈ T, 0 ≤ w p) ∧
      ∑ p ∈ T, w p = 1 ∧
      ∑ p ∈ T, w p • p = x := by
  classical
  obtain ⟨ι, hι, z, v, hcard, hzs, hzai, hvpos, hvone, hvsum⟩ :=
    eq_pos_convex_span_of_mem_boundary_convexHull hx hxi
  let w : E → ℝ := fun p =>
    if hp : ∃ i, z i = p then v (Classical.choose hp) else 0
  have hzinj : Function.Injective z := hzai.injective
  have hwz : ∀ i, w (z i) = v i := by
    intro i
    unfold w
    split
    next hp =>
      rw [hzinj (Classical.choose_spec hp)]
    next hp =>
      exact (hp ⟨i, rfl⟩).elim
  refine ⟨Finset.univ.image z, w, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hzinj, Finset.card_univ]
    exact hcard
  · intro p hp
    rw [Finset.mem_coe, Finset.mem_image] at hp
    obtain ⟨i, -, rfl⟩ := hp
    exact hzs ⟨i, rfl⟩
  · intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨i, -, rfl⟩ := hp
    exact (hvpos i).le.trans_eq (hwz i).symm
  · rw [Finset.sum_image hzinj.injOn]
    simpa only [hwz] using hvone
  · rw [Finset.sum_image hzinj.injOn]
    simpa only [hwz] using hvsum

/-- Corollary 3.47, sharp attainment part.  Every finite value of the convex
hull function is attained by a convex combination of at most
`finrank E + 1` values of the original function. -/
theorem exists_finite_convexCombination_eq_convexHullFunction_sharp
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f)
    (hf : IsCoercive f) {x : E}
    (hx : x ∈ effectiveDomain (convexHullFunction f)) :
    ∃ (T : Finset (E × ℝ)) (w : E × ℝ → ℝ),
      T.card ≤ Module.finrank ℝ E + 1 ∧
      (∀ p ∈ T, 0 ≤ w p) ∧
      ∑ p ∈ T, w p = 1 ∧
      (∀ p ∈ T, p.1 ∈ effectiveDomain f) ∧
      ∑ p ∈ T, w p • p.1 = x ∧
      ∑ p ∈ T, w p * (f p.1).toReal =
        (convexHullFunction f x).toReal := by
  let g : E → EReal := convexHullFunction f
  have hgproper : IsProper g := by
    simpa [g] using isProper_convexHullFunction hproper hf
  have hxtop : g x ≠ ⊤ := ne_of_lt hx
  have hxbot : g x ≠ ⊥ := ne_of_gt (hgproper.2 x)
  have hcoe : ((g x).toReal : EReal) = g x :=
    EReal.coe_toReal hxtop hxbot
  have hboundary_epi :
      (x, (g x).toReal) ∈ epigraph g := by
    rw [mem_epigraph_iff, hcoe]
  have hboundary_hull :
      (x, (g x).toReal) ∈ convexHull ℝ (epigraph f) := by
    rw [← epigraph_convexHullFunction_eq_of_isCoercive
      hlsc hproper hf]
    simpa [g] using hboundary_epi
  have hboundary_notint :
      (x, (g x).toReal) ∉ interior (convexHull ℝ (epigraph f)) := by
    rw [← epigraph_convexHullFunction_eq_of_isCoercive
      hlsc hproper hf]
    simpa [g] using
      (graphPoint_not_mem_interior_epigraph (f := g)
        (x := x) (r := (g x).toReal) hcoe)
  obtain ⟨T, w, hTcard, hTepi, hw0, hw1, hwsum⟩ :=
    exists_finite_convexCombination_of_mem_boundary_convexHull
      hboundary_hull hboundary_notint
  have hp_top : ∀ p ∈ T, f p.1 ≠ ⊤ := by
    intro p hp
    have hle : f p.1 ≤ (p.2 : EReal) :=
      (mem_epigraph_iff f p.1 p.2).mp (hTepi hp)
    exact ne_of_lt (hle.trans_lt (EReal.coe_lt_top p.2))
  have hp_dom : ∀ p ∈ T, p.1 ∈ effectiveDomain f := by
    intro p hp
    exact lt_top_iff_ne_top.mpr (hp_top p hp)
  have hp_value_le : ∀ p ∈ T, (f p.1).toReal ≤ p.2 := by
    intro p hp
    have hle : f p.1 ≤ (p.2 : EReal) :=
      (mem_epigraph_iff f p.1 p.2).mp (hTepi hp)
    have hcoe_p : ((f p.1).toReal : EReal) = f p.1 :=
      EReal.coe_toReal (hp_top p hp) (ne_of_gt (hproper.2 p.1))
    rw [← hcoe_p] at hle
    exact_mod_cast hle
  have hxsum : ∑ p ∈ T, w p • p.1 = x := by
    have h := congrArg (LinearMap.fst ℝ E ℝ) hwsum
    simpa using h
  have hasum :
      ∑ p ∈ T, w p * p.2 = (g x).toReal := by
    have h := congrArg (LinearMap.snd ℝ E ℝ) hwsum
    simpa [smul_eq_mul] using h
  let β : ℝ := ∑ p ∈ T, w p * (f p.1).toReal
  have hβ_le : β ≤ (g x).toReal := by
    calc
      β ≤ ∑ p ∈ T, w p * p.2 := by
        apply Finset.sum_le_sum
        intro p hp
        exact mul_le_mul_of_nonneg_left (hp_value_le p hp) (hw0 p hp)
      _ = (g x).toReal := hasum
  have hgraph : ∀ p ∈ T, (p.1, (f p.1).toReal) ∈ epigraph f := by
    intro p hp
    rw [mem_epigraph_iff,
      EReal.coe_toReal (hp_top p hp) (ne_of_gt (hproper.2 p.1))]
  have hgraph_sum :
      ∑ p ∈ T, w p • (p.1, (f p.1).toReal) = (x, β) := by
    apply Prod.ext
    · change
        (LinearMap.fst ℝ E ℝ)
            (∑ p ∈ T, w p • (p.1, (f p.1).toReal)) = x
      rw [map_sum]
      simpa using hxsum
    · change
        (LinearMap.snd ℝ E ℝ)
            (∑ p ∈ T, w p • (p.1, (f p.1).toReal)) = β
      rw [map_sum]
      simp [β, smul_eq_mul]
  have hgraph_hull : (x, β) ∈ convexHull ℝ (epigraph f) := by
    have hmem :=
      T.centerMass_mem_convexHull
        (s := epigraph f) hw0 (by rw [hw1]; exact zero_lt_one) hgraph
    rw [T.centerMass_eq_of_sum_1 _ hw1] at hmem
    rw [hgraph_sum] at hmem
    exact hmem
  have hg_le_beta : g x ≤ (β : EReal) := by
    simpa [g] using
      (convexHullFunction_le_of_mem_convexHull_epigraph hgraph_hull)
  have hα_le : (g x).toReal ≤ β := by
    exact_mod_cast (hcoe.trans_le hg_le_beta)
  have hβ_eq : β = (g x).toReal :=
    le_antisymm hβ_le hα_le
  refine ⟨T, w, ?_, hw0, hw1, hp_dom, hxsum, ?_⟩
  · simpa [Module.finrank_prod] using hTcard
  · simpa [β, g] using hβ_eq

end RW
