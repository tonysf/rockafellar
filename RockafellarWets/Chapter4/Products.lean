/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Convergence of Finite Products

The dependent finite-product form of Exercise 4.29(a).  Each factor may live
in a different topological space.
-/

import Mathlib.Order.Filter.Finite
import RockafellarWets.Chapter4.SetLimits

open Filter Set Topology

namespace RW

variable {ι : Type*} {E : ι → Type*} [∀ i, TopologicalSpace (E i)]

/-- The dependent Cartesian product of a family of sets. -/
def dependentSetProduct (C : ∀ i, Set (E i)) : Set (∀ i, E i) :=
  Set.univ.pi C

omit [∀ i, TopologicalSpace (E i)] in
@[simp]
theorem mem_dependentSetProduct {C : ∀ i, Set (E i)} {x : ∀ i, E i} :
    x ∈ dependentSetProduct C ↔ ∀ i, x i ∈ C i := by
  simp [dependentSetProduct]

/-- A product of componentwise inner-limit points belongs to the inner limit
of the finite products. -/
theorem dependentSetProduct_innerSetLimit_subset
    [Finite ι] (C : ∀ i, ℕ → Set (E i)) :
    dependentSetProduct (fun i ↦ innerSetLimit (C i)) ⊆
      innerSetLimit (fun n ↦ dependentSetProduct (fun i ↦ C i n)) := by
  classical
  letI := Fintype.ofFinite ι
  intro x hx V hV
  rw [nhds_pi, Filter.mem_pi] at hV
  rcases hV with ⟨I, hIfin, U, hU, hUV⟩
  have hhit : ∀ᶠ n in atTop,
      ∀ i, (C i n ∩ U i).Nonempty := by
    simpa only [Finset.mem_univ, forall_const] using
      (Finset.univ.eventually_all.2 fun i _ ↦
        (mem_dependentSetProduct.1 hx i) (U i) (hU i))
  exact hhit.mono fun n hn ↦ by
    choose y hyC hyU using hn
    refine ⟨y, mem_dependentSetProduct.2 hyC, hUV ?_⟩
    intro i hi
    exact hyU i

/-- The outer limit of finite products is contained in the product of the
componentwise outer limits. -/
theorem outerSetLimit_dependentSetProduct_subset
    (C : ∀ i, ℕ → Set (E i)) :
    outerSetLimit (fun n ↦ dependentSetProduct (fun i ↦ C i n)) ⊆
      dependentSetProduct (fun i ↦ outerSetLimit (C i)) := by
  intro x hx
  rw [mem_dependentSetProduct]
  intro i V hV
  have hpre : (fun y : ∀ i, E i ↦ y i) ⁻¹' V ∈ nhds x :=
    (continuous_apply i).continuousAt hV
  exact (hx _ hpre).mono fun n ⟨y, hyProduct, hyV⟩ ↦
    ⟨y i, mem_dependentSetProduct.1 hyProduct i, hyV⟩

/-- **Exercise 4.29(a), ordinary convergence.** A finite dependent product
of convergent set sequences converges to the product of their limits. -/
theorem pkConverges_dependentSetProduct [Finite ι]
    {C : ∀ i, ℕ → Set (E i)} {D : ∀ i, Set (E i)}
    (h : ∀ i, PKConverges (C i) (D i)) :
    PKConverges (fun n ↦ dependentSetProduct (fun i ↦ C i n))
      (dependentSetProduct D) := by
  have hDInner : dependentSetProduct D ⊆
      innerSetLimit (fun n ↦ dependentSetProduct (fun i ↦ C i n)) := by
    intro x hx
    apply dependentSetProduct_innerSetLimit_subset C
    rw [mem_dependentSetProduct]
    intro i
    rw [(h i).inner_eq]
    exact mem_dependentSetProduct.1 hx i
  have hOuterD :
      outerSetLimit (fun n ↦ dependentSetProduct (fun i ↦ C i n)) ⊆
        dependentSetProduct D := by
    refine (outerSetLimit_dependentSetProduct_subset C).trans ?_
    intro x hx
    rw [mem_dependentSetProduct] at hx ⊢
    intro i
    rw [← (h i).outer_eq]
    exact hx i
  constructor
  · exact Set.Subset.antisymm
      ((innerSetLimit_subset_outerSetLimit _).trans hOuterD) hDInner
  · exact Set.Subset.antisymm hOuterD
      (hDInner.trans (innerSetLimit_subset_outerSetLimit _))

end RW
