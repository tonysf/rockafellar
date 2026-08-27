/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Convergence of finite convex intersections

This file proves Exercise 4.33 by induction from Theorem 4.32(c).
-/

import RockafellarWets.Chapter4.ConvexSystemConvergence

open Filter Set Topology
open scoped BigOperators Pointwise

namespace RW

section ConvexIntersections

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Enlarging the second set preserves nonseparability. -/
theorem CannotBeSeparated.mono_right {A B C : Set E} (hBC : B ⊆ C)
    (h : CannotBeSeparated A B) : CannotBeSeparated A C := by
  rw [CannotBeSeparated] at h ⊢
  apply interior_mono _ h
  intro y hy
  rcases Set.mem_sub.1 hy with ⟨a, ha, b, hb, rfl⟩
  exact Set.mem_sub.2 ⟨a, ha, b, hBC hb, rfl⟩

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Nonseparability is symmetric. -/
theorem CannotBeSeparated.symm {A B : Set E}
    (h : CannotBeSeparated A B) : CannotBeSeparated B A := by
  rw [CannotBeSeparated] at h ⊢
  rcases Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds h) with
    ⟨r, hr, hrAB⟩
  apply mem_interior_iff_mem_nhds.2
  apply Metric.mem_nhds_iff.2
  refine ⟨r, hr, ?_⟩
  intro y hy
  have hneg : -y ∈ Metric.ball (0 : E) r := by
    rw [Metric.mem_ball, dist_zero_right, norm_neg]
    simpa only [Metric.mem_ball, dist_zero_right] using hy
  rcases Set.mem_sub.1 (interior_subset (hrAB hneg)) with
    ⟨a, ha, b, hb, hab⟩
  exact Set.mem_sub.2 ⟨b, hb, a, ha, by
    calc
      b - a = -(a - b) := by module
      _ = -(-y) := congrArg Neg.neg hab
      _ = y := neg_neg y⟩

/-- **Exercise 4.33**, finite-index form.  A finite family of converging
convex sets has a converging intersection when no limiting factor can be
separated from the intersection of all the other factors. -/
theorem pkConverges_iInter_finset_of_cannotBeSeparated
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) {C : ι → ℕ → Set E} {D : ι → Set E}
    (hlim : ∀ i ∈ s, PKConverges (C i) (D i))
    (hconv : ∀ i ∈ s, ∀ n, Convex ℝ (C i n))
    (hnosep : ∀ i ∈ s,
      CannotBeSeparated (D i) (⋂ j ∈ s.erase i, D j)) :
    PKConverges (fun n ↦ ⋂ i ∈ s, C i n) (⋂ i ∈ s, D i) := by
  induction s using Finset.induction_on with
  | empty =>
      simpa using
        (pkConverges_const_of_isClosed (D := (univ : Set E)) isClosed_univ)
  | @insert a s ha ih =>
      have hlimS : ∀ i ∈ s, PKConverges (C i) (D i) :=
        fun i hi ↦ hlim i (Finset.mem_insert_of_mem hi)
      have hconvS : ∀ i ∈ s, ∀ n, Convex ℝ (C i n) :=
        fun i hi ↦ hconv i (Finset.mem_insert_of_mem hi)
      have hnosepS : ∀ i ∈ s,
          CannotBeSeparated (D i) (⋂ j ∈ s.erase i, D j) := by
        intro i hi
        apply CannotBeSeparated.mono_right _
          (hnosep i (Finset.mem_insert_of_mem hi))
        intro x hx
        simp only [mem_iInter] at hx ⊢
        intro j hj
        exact hx j (by
          simp only [Finset.mem_erase, Finset.mem_insert] at hj ⊢
          exact ⟨hj.1, Or.inr hj.2⟩)
      have hlimInter :
          PKConverges (fun n ↦ ⋂ i ∈ s, C i n) (⋂ i ∈ s, D i) :=
        ih hlimS hconvS hnosepS
      have hconvInter : ∀ n, Convex ℝ (⋂ i ∈ s, C i n) := by
        intro n
        exact convex_iInter fun i ↦ convex_iInter fun hi ↦ hconvS i hi n
      have hnosepPair : CannotBeSeparated (⋂ i ∈ s, D i) (D a) := by
        have haNosep := hnosep a (Finset.mem_insert_self a s)
        have herase : (insert a s).erase a = s := Finset.erase_insert ha
        rw [herase] at haNosep
        exact haNosep.symm
      have hpair := PKConverges.inter_of_cannotBeSeparated
        hlimInter (hlim a (Finset.mem_insert_self a s)) hconvInter
        (hconv a (Finset.mem_insert_self a s)) hnosepPair
      simpa only [Finset.set_biInter_insert, ha, inter_comm] using hpair

/-- **Exercise 4.33**, the book's `q`-set formulation. -/
theorem pkConverges_iInter_fin_of_cannotBeSeparated
    {q : ℕ} {C : Fin q → ℕ → Set E} {D : Fin q → Set E}
    (hlim : ∀ i, PKConverges (C i) (D i))
    (hconv : ∀ i n, Convex ℝ (C i n))
    (hnosep : ∀ i,
      CannotBeSeparated (D i) (⋂ j, ⋂ (_h : j ≠ i), D j)) :
    PKConverges (fun n ↦ ⋂ i, C i n) (⋂ i, D i) := by
  have h := pkConverges_iInter_finset_of_cannotBeSeparated
      (s := Finset.univ) (C := C) (D := D)
      (fun i _ ↦ hlim i) (fun i _ ↦ hconv i) (by
        intro i _hi
        simpa only [Finset.mem_erase, Finset.mem_univ, and_true] using hnosep i)
  convert h using 1 <;> ext x <;> simp

end ConvexIntersections

end RW
