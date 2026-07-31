/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Total Convergence of Finite Products

This file completes the total-convergence clause of Exercise 4.29(a).
-/

import RockafellarWets.Chapter4.Products
import RockafellarWets.Chapter4.TotalLinearImages

open Filter Function Set Topology

namespace RW

variable {ι : Type*} {E : ι → Type*} [Fintype ι]
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]

omit [∀ i, FiniteDimensional ℝ (E i)] in
/-- Every horizon outer-limit direction of a finite product is componentwise
a horizon outer-limit direction. -/
theorem horizonOuterSetLimit_dependentSetProduct_subset
    (C : ∀ i, ℕ → Set (E i)) :
    horizonOuterSetLimit
        (fun n ↦ dependentSetProduct (fun i ↦ C i n)) ⊆
      dependentSetProduct (fun i ↦ horizonOuterSetLimit (C i)) := by
  intro w hw
  rw [mem_dependentSetProduct]
  intro i
  rcases hw with rfl | ⟨u, huOuter, r, hr, rfl⟩
  · exact (isCone_horizonOuterSetLimit (C i)).1
  · have huProduct : (u : ∀ i, E i) ∈ horizonOuterSetLimit
        (fun n ↦ dependentSetProduct (fun i ↦ C i n)) :=
      cosmicDirection_mem_outer_ordinaryCosmicSequence_iff.1 huOuter
    rcases
        mem_horizonOuterSetLimit_iff_exists_cosmicDirection_subsequence.1
          huProduct with
      ⟨φ, x, hφ, hxProduct, hxu⟩
    by_cases hui : (u : ∀ i, E i) i = 0
    · simpa only [Pi.smul_apply, hui, smul_zero] using
        (isCone_horizonOuterSetLimit (C i)).1
    · rcases exists_scaling_of_tendsto_cosmicDirection hxu with
        ⟨a, haPos, haZero, haxu⟩
      let ui : CosmicBoundary (E i) :=
        cosmicDirectionOf ((u : ∀ i, E i) i) hui
      have hscalePos : ∀ n, 0 < ‖(u : ∀ i, E i) i‖⁻¹ * a n := fun n ↦
        mul_pos (inv_pos.mpr (norm_pos_iff.mpr hui)) (haPos n)
      have hscaleZero :
          Tendsto (fun n ↦ ‖(u : ∀ i, E i) i‖⁻¹ * a n)
            atTop (nhds 0) := by
        simpa only [mul_zero] using tendsto_const_nhds.mul haZero
      have hscaledCoordinate : Tendsto
          (fun n ↦ (‖(u : ∀ i, E i) i‖⁻¹ * a n) • x n i)
            atTop (nhds (ui : E i)) := by
        have hcoordinate : Tendsto (fun n ↦ a n • x n i) atTop
            (nhds ((u : ∀ i, E i) i)) :=
          tendsto_pi_nhds.1 haxu i
        have hconst : Tendsto
            (fun _ : ℕ ↦ ‖(u : ∀ i, E i) i‖⁻¹) atTop
            (nhds ‖(u : ∀ i, E i) i‖⁻¹) :=
          tendsto_const_nhds
        have hnormalized := hconst.smul hcoordinate
        simpa only [mul_smul, ui, coe_cosmicDirectionOf,
          NormedSpace.normalize] using hnormalized
      have hxDirection : Tendsto (fun n ↦ cosmicEmbed (x n i)) atTop
          (nhds (cosmicDirection ui)) :=
        tendsto_cosmicDirection_of_scaling hscalePos hscaleZero
          hscaledCoordinate
      have huiOuter : (ui : E i) ∈ horizonOuterSetLimit (C i) :=
        mem_horizonOuterSetLimit_iff_exists_cosmicDirection_subsequence.2
          ⟨φ, fun n ↦ x n i, hφ,
            fun n ↦ mem_dependentSetProduct.1 (hxProduct n) i,
            hxDirection⟩
      have hcoordinateOuter : (u : ∀ i, E i) i ∈
          horizonOuterSetLimit (C i) := by
        have hscaled := (isCone_horizonOuterSetLimit (C i)).smul_mem
          huiOuter (norm_nonneg ((u : ∀ i, E i) i))
        simpa only [ui, coe_cosmicDirectionOf,
          NormedSpace.norm_smul_normalize ((u : ∀ i, E i) i)] using hscaled
      simpa only [Pi.smul_apply] using
        (isCone_horizonOuterSetLimit (C i)).smul_mem hcoordinateOuter hr.le

/-- **Exercise 4.29(a), total convergence.** Finite dependent products of
totally convergent sequences converge totally when the horizon cone of the
limit product is the product of the component horizon cones. -/
theorem totalConverges_dependentSetProduct
    {C : ∀ i, ℕ → Set (E i)} {D : ∀ i, Set (E i)}
    (h : ∀ i, TotalConverges (C i) (D i))
    (hhorizon : horizonCone (dependentSetProduct D) =
      dependentSetProduct (fun i ↦ horizonCone (D i))) :
    TotalConverges (fun n ↦ dependentSetProduct (fun i ↦ C i n))
      (dependentSetProduct D) := by
  apply totalConverges_iff_pkConverges_and_horizonOuter_subset.2
  refine ⟨pkConverges_dependentSetProduct (fun i ↦ (h i).pkConverges), ?_⟩
  refine (horizonOuterSetLimit_dependentSetProduct_subset C).trans ?_
  intro w hw
  rw [mem_dependentSetProduct] at hw
  rw [hhorizon, mem_dependentSetProduct]
  intro i
  exact (h i).horizonOuter_subset (hw i)

end RW
