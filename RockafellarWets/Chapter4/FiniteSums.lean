/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Inner Limits of Finite Set Sums
-/

import RockafellarWets.Chapter3.FiniteConeSetOperations
import RockafellarWets.Chapter4.Products

open Filter Set Topology

namespace RW

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Exercise 4.29(b).** The inner limit of finite Minkowski sums contains
the sum of the componentwise inner limits. -/
theorem finiteSetSum_innerSetLimit_subset
    (C : ι → ℕ → Set E) :
    finiteSetSum (fun i ↦ innerSetLimit (C i)) ⊆
      innerSetLimit (fun n ↦ finiteSetSum (fun i ↦ C i n)) := by
  rintro x ⟨z, hzInner, hsum⟩
  subst x
  have hzProduct : z ∈
      innerSetLimit (fun n ↦ dependentSetProduct (fun i ↦ C i n)) := by
    apply dependentSetProduct_innerSetLimit_subset C
    exact mem_dependentSetProduct.2 hzInner
  intro V hV
  have hsumContinuous : Continuous (fun y : ι → E ↦ ∑ i, y i) := by
    fun_prop
  have hpre : (fun y : ι → E ↦ ∑ i, y i) ⁻¹' V ∈ nhds z :=
    hsumContinuous.continuousAt hV
  exact (hzProduct _ hpre).mono fun n ⟨y, hyProduct, hyV⟩ ↦ by
    refine ⟨∑ i, y i, ?_, hyV⟩
    exact ⟨y, mem_dependentSetProduct.1 hyProduct, rfl⟩

end RW
