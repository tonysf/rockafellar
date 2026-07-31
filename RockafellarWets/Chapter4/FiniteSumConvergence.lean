/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Convergence of Finite Minkowski Sums

This file proves the ordinary and total sum clauses of Exercise 4.29.
-/

import RockafellarWets.Chapter4.FiniteSums
import RockafellarWets.Chapter4.TotalProducts

open scoped BigOperators Pointwise Matrix
open Set

namespace RW

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The continuous finite-summation map used in Exercise 4.29. -/
def finiteSummationLinearMap : (ι → E) →ₗ[ℝ] E where
  toFun z := ∑ i, z i
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c z := by simp [Finset.smul_sum]

omit [FiniteDimensional ℝ E] in
@[simp]
theorem finiteSummationLinearMap_apply (z : ι → E) :
    finiteSummationLinearMap z = ∑ i, z i := rfl

omit [FiniteDimensional ℝ E] in
/-- A finite Minkowski sum is the image of its finite Cartesian product under
the summation map. -/
theorem finiteSetSum_eq_finiteSummationLinearMap_image (C : ι → Set E) :
    finiteSetSum C =
      finiteSummationLinearMap '' dependentSetProduct C := by
  ext x
  simp [finiteSetSum, dependentSetProduct, Set.mem_pi]

/-- Finite Minkowski sums converge ordinarily under componentwise total
convergence and the absence of cancellation among limiting horizon
directions.  This is the common engine for 4.29(c) and the ordinary part of
4.29(d). -/
theorem pkConverges_finiteSetSum_of_total_of_horizon_noCancel
    {Cseq : ι → ℕ → Set E} {C : ι → Set E}
    (hC : ∀ i, TotalConverges (Cseq i) (C i))
    (hker : ∀ u : ι → E, (∀ i, u i ∈ horizonCone (C i)) →
      (∑ i, u i) = 0 → u = 0) :
    PKConverges (fun n ↦ finiteSetSum (fun i ↦ Cseq i n))
      (finiteSetSum C) := by
  have hproduct : PKConverges
      (fun n ↦ dependentSetProduct (fun i ↦ Cseq i n))
      (dependentSetProduct C) :=
    pkConverges_dependentSetProduct (fun i ↦ (hC i).pkConverges)
  have hnoescape : NoConvergentImageEscapeAlong
      (finiteSummationLinearMap (ι := ι) (E := E))
      (fun n ↦ dependentSetProduct (fun i ↦ Cseq i n)) := by
    apply noConvergentImageEscapeAlong_linear_of_horizonOuter
      (Cseq := fun n ↦ dependentSetProduct (fun i ↦ Cseq i n))
      (finiteSummationLinearMap (ι := ι) (E := E))
    intro u huOuter hsum
    have huProduct :=
      horizonOuterSetLimit_dependentSetProduct_subset Cseq huOuter
    apply hker u
    · intro i
      exact (hC i).horizonOuter_subset
        (mem_dependentSetProduct.1 huProduct i)
    · simpa only [finiteSummationLinearMap_apply] using hsum
  have himage := hproduct.image_of_noConvergentImageEscapeAlong
    (finiteSummationLinearMap (ι := ι) (E := E)).continuous_of_finiteDimensional
    hnoescape
  simpa only [← finiteSetSum_eq_finiteSummationLinearMap_image] using himage

/-- **Exercise 4.29(d).** Finite Minkowski sums converge totally under the
book's product-horizon identity and noncancellation hypothesis. -/
theorem totalConverges_finiteSetSum
    {Cseq : ι → ℕ → Set E} {C : ι → Set E}
    (hC : ∀ i, TotalConverges (Cseq i) (C i))
    (hhorizon : horizonCone (dependentSetProduct C) =
      dependentSetProduct (fun i ↦ horizonCone (C i)))
    (hker : ∀ u : ι → E, (∀ i, u i ∈ horizonCone (C i)) →
      (∑ i, u i) = 0 → u = 0) :
    TotalConverges (fun n ↦ finiteSetSum (fun i ↦ Cseq i n))
      (finiteSetSum C) := by
  have hproduct : TotalConverges
      (fun n ↦ dependentSetProduct (fun i ↦ Cseq i n))
      (dependentSetProduct C) :=
    totalConverges_dependentSetProduct hC hhorizon
  have hkernel : ∀ ⦃u : ι → E⦄,
      u ∈ horizonCone (dependentSetProduct C) →
      finiteSummationLinearMap u = 0 → u = 0 := by
    intro u hu hsum
    apply hker u
    · have hu' : u ∈ dependentSetProduct
          (fun i ↦ horizonCone (C i)) := by
        rw [← hhorizon]
        exact hu
      exact mem_dependentSetProduct.1 hu'
    · simpa only [finiteSummationLinearMap_apply] using hsum
  have himage := hproduct.linear_image
    (finiteSummationLinearMap (ι := ι) (E := E)) hkernel
  simpa only [← finiteSetSum_eq_finiteSummationLinearMap_image] using himage

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A two-term finite set sum is the usual Minkowski sum. -/
theorem finiteSetSum_fin_two (A B : Set E) :
    finiteSetSum (![A, B] : Fin 2 → Set E) = A + B := by
  ext x
  constructor
  · rintro ⟨z, hz, hsum⟩
    apply Set.mem_add.2
    refine ⟨z 0, hz 0, z 1, hz 1, ?_⟩
    simpa only [Fin.sum_univ_two] using hsum
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨![a, b], ?_, ?_⟩
    · intro i
      fin_cases i <;> simp [ha, hb]
    · simp [Fin.sum_univ_two]

/-- **Exercise 4.29(c).** The sums of two totally convergent sequences
converge ordinarily when the two limiting horizon cones cannot cancel. -/
theorem PKConverges.add_of_total_of_horizon_inter_neg_eq_zero
    {C1seq C2seq : ℕ → Set E} {C1 C2 : Set E}
    (hC1 : TotalConverges C1seq C1)
    (hC2 : TotalConverges C2seq C2)
    (hopposite : horizonCone C1 ∩ -(horizonCone C2) = ({0} : Set E)) :
    PKConverges (fun n ↦ C1seq n + C2seq n) (C1 + C2) := by
  let Cseq : Fin 2 → ℕ → Set E :=
    fun i n ↦ (![C1seq n, C2seq n] : Fin 2 → Set E) i
  let C : Fin 2 → Set E := (![C1, C2] : Fin 2 → Set E)
  have hcomponents : ∀ i, TotalConverges (Cseq i) (C i) := by
    intro i
    fin_cases i
    · exact hC1
    · exact hC2
  have hnocancel : ∀ u : Fin 2 → E,
      (∀ i, u i ∈ horizonCone (C i)) →
      (∑ i, u i) = 0 → u = 0 := by
    intro u hu hsum
    have hu0 : u 0 ∈ horizonCone C1 := hu 0
    have hu1 : u 1 ∈ horizonCone C2 := hu 1
    have hsum' : u 0 + u 1 = 0 := by
      simpa only [Fin.sum_univ_two] using hsum
    have hu0neg : u 0 ∈ -(horizonCone C2) := by
      rw [Set.mem_neg, neg_eq_of_add_eq_zero_right hsum']
      exact hu1
    have hu0zero : u 0 = 0 := by
      have : u 0 ∈ ({0} : Set E) := by
        rw [← hopposite]
        exact ⟨hu0, hu0neg⟩
      simpa only [Set.mem_singleton_iff] using this
    have hu1zero : u 1 = 0 := by
      simpa only [hu0zero, zero_add] using hsum'
    funext i
    fin_cases i
    · exact hu0zero
    · exact hu1zero
  have hsum := pkConverges_finiteSetSum_of_total_of_horizon_noCancel
    hcomponents hnocancel
  simpa only [Cseq, C, finiteSetSum_fin_two] using hsum

end RW
