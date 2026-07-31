/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3: Dependent Finite Products

This file gives the mixed-dimensional finite-product form of Exercise 3.11.
Each coordinate may live in a different finite-dimensional real normed space.
-/

import RockafellarWets.Chapter3.FiniteConeSetOperations

open Set Bornology Filter Topology

namespace RW

section DependentFiniteProducts

variable {ι : Type*} [Fintype ι]
  {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]

/-- **Exercise 3.11 (dependent finite-product inclusion).** -/
theorem horizonCone_dependentPi_subset_pi_horizonCone
    (C : ∀ i, Set (E i)) :
    horizonCone (Set.pi Set.univ C) ⊆
      Set.pi Set.univ (fun i ↦ horizonCone (C i)) := by
  intro w hw
  have hw' : w = 0 ∨ w ∈ asymptoticCone ℝ (Set.pi Set.univ C) := by
    simpa [horizonCone] using hw
  rcases hw' with rfl | hw
  · simp [Set.mem_pi, zero_mem_horizonCone]
  · rcases exists_seq_pos_smul_of_mem_asymptoticCone
      (C := Set.pi Set.univ C) hw with ⟨c, u, hc, hu, hcpos, hmem⟩
    rw [Set.mem_pi]
    intro i hi
    apply Set.mem_insert_of_mem 0
    refine mem_asymptoticCone_of_seq_smul
      (u := fun n ↦ u n i) hc ?_ ?_
    · exact tendsto_pi_nhds.1 hu i
    · intro n
      have hn := hmem n
      rw [Set.mem_pi] at hn
      simpa using hn i (Set.mem_univ i)

/-- **Exercise 3.11 (dependent finite-product equality, convex case).** -/
theorem horizonCone_dependentPi_eq_pi_horizonCone_of_convex_nonempty
    (C : ∀ i, Set (E i)) (hconv : ∀ i, Convex ℝ (C i))
    (hne : ∀ i, (C i).Nonempty) :
    horizonCone (Set.pi Set.univ C) =
      Set.pi Set.univ (fun i ↦ horizonCone (C i)) := by
  apply le_antisymm (horizonCone_dependentPi_subset_pi_horizonCone C)
  intro w hw
  rw [Set.mem_pi] at hw
  choose x hx using hne
  have hxpi : x ∈ Set.pi Set.univ C := by
    simp [Set.mem_pi, hx]
  have hray :
      ∀ {τ : ℝ}, 0 ≤ τ →
        τ • w + x ∈ closure (Set.pi Set.univ C) := by
    intro τ hτ
    rw [closure_pi_set, Set.mem_pi]
    intro i hi
    exact smul_add_mem_closure_of_mem_horizonCone
      (hconv i) (subset_closure (hx i)) (hw i (Set.mem_univ i)) hτ
  have hclosure :
      w ∈ horizonCone (closure (Set.pi Set.univ C)) :=
    mem_horizonCone_of_forall_smul_add_mem
      (C := closure (Set.pi Set.univ C)) (x := x) (w := w)
        (fun {τ} hτ ↦ hray (τ := τ) hτ)
  simpa [horizonCone_closure] using hclosure

/-- **Exercise 3.11 (dependent finite-product equality, bounded factors).**
Equality also holds when all factors except one designated coordinate are
bounded. -/
theorem horizonCone_dependentPi_eq_pi_horizonCone_of_bounded_off
    (C : ∀ i, Set (E i)) (j : ι) (hne : ∀ i, (C i).Nonempty)
    (hbdd : ∀ i, i ≠ j → IsBounded (C i)) :
    horizonCone (Set.pi Set.univ C) =
      Set.pi Set.univ (fun i ↦ horizonCone (C i)) := by
  classical
  apply le_antisymm (horizonCone_dependentPi_subset_pi_horizonCone C)
  intro w hw
  rw [Set.mem_pi] at hw
  have hwoff : ∀ i, i ≠ j → w i = 0 := by
    intro i hij
    have hzero : horizonCone (C i) = ({0} : Set (E i)) :=
      (isBounded_iff_horizonCone_eq_singleton_zero (C := C i)).mp
        (hbdd i hij)
    simpa [hzero] using hw i (Set.mem_univ i)
  by_cases hwj : w j = 0
  · have hw0 : w = 0 := by
      funext i
      by_cases hij : i = j
      · subst i
        exact hwj
      · exact hwoff i hij
    subst w
    exact zero_mem_horizonCone _
  have hwjasym : w j ∈ asymptoticCone ℝ (C j) := by
    rcases (show w j = 0 ∨ w j ∈ asymptoticCone ℝ (C j) by
      simpa [horizonCone] using hw j (Set.mem_univ j)) with h | h
    · exact (hwj h).elim
    · exact h
  rcases exists_seq_pos_smul_of_mem_asymptoticCone hwjasym with
    ⟨c, u, hc, hu, hcpos, hmem⟩
  choose x hx using hne
  let v : ℕ → ∀ i, E i :=
    fun n i ↦ if hij : i = j then hij ▸ u n else (c n)⁻¹ • x i
  have hv : Tendsto v atTop (nhds w) := by
    apply tendsto_pi_nhds.2
    intro i
    by_cases hij : i = j
    · subst i
      simpa [v] using hu
    · have hi0 :
          Tendsto (fun n ↦ (c n)⁻¹ • x i) atTop (nhds (0 : E i)) := by
        simpa using hc.inv_tendsto_atTop.smul_const (x i)
      simpa [v, hij, hwoff i hij] using hi0
  have hcvmem : ∀ n, c n • v n ∈ Set.pi Set.univ C := by
    intro n
    rw [Set.mem_pi]
    intro i hi
    by_cases hij : i = j
    · subst i
      simpa [v] using hmem n
    · simpa [v, hij, smul_smul, mul_inv_cancel₀ (hcpos n).ne', one_smul]
        using hx i
  exact Set.mem_insert_of_mem 0 <|
    mem_asymptoticCone_of_seq_smul hc hv hcvmem

/-- A dependent finite product of bounded sets is bounded, hence has trivial
horizon cone. -/
theorem horizonCone_dependentPi_eq_singleton_zero_of_bounded
    (C : ∀ i, Set (E i)) (hbdd : ∀ i, IsBounded (C i)) :
    horizonCone (Set.pi Set.univ C) = ({0} : Set (∀ i, E i)) := by
  apply (isBounded_iff_horizonCone_eq_singleton_zero
    (C := Set.pi Set.univ C)).mp
  exact IsBounded.pi hbdd

end DependentFiniteProducts

end RW
