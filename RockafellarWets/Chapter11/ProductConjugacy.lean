/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Conjugation of finite separable sums
-/

import RockafellarWets.Chapter11.FenchelConjugate
import RockafellarWets.Chapter3.ERealInfimum
import RockafellarWets.Chapter10.DependentSeparableSubgradients

open Set
open scoped InnerProductSpace

namespace RW

/-- Extended-real addition distributes over arbitrary suprema, including
when the constant is infinite and when the index type is empty. -/
theorem ereal_iSup_add {α : Sort*} (f : α → EReal) (a : EReal) :
    (⨆ x, f x) + a = ⨆ x, f x + a := by
  induction a using EReal.rec with
  | coe r => exact (erealAddRightOrderIso r).map_iSup f
  | bot => simp
  | top =>
    by_cases h : ∀ x, f x = ⊥
    · simp [h]
    · obtain ⟨x,hx⟩ := not_forall.mp h
      apply le_antisymm
      · apply le_trans le_top
        calc (⊤ : EReal) = f x + ⊤ := (EReal.add_top_of_ne_bot hx).symm
             _ ≤ _ := le_iSup (fun y ↦ f y + ⊤) x
      · exact iSup_le fun x ↦ add_le_add (le_iSup f x) le_rfl

theorem ereal_add_iSup {α : Sort*} (a : EReal) (f : α → EReal) :
    a + (⨆ x, f x) = ⨆ x, a + f x := by
  simpa only [add_comm] using ereal_iSup_add f a

/-- Supremizing over independent coordinates commutes with finite sums
even if some summands are infinite. -/
theorem ereal_iSup_sum_independent {ι : Type*} {X : ι → Type*} [∀ i, Nonempty (X i)]
    (g : ∀ i, X i → EReal) (s : Finset ι) :
    (⨆ x : ∀ i, X i, ∑ i ∈ s, g i (x i)) = ∑ i ∈ s, ⨆ t, g i t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [← ih,ereal_iSup_add]
    simp_rw [ereal_add_iSup]
    apply le_antisymm
    · refine iSup_le fun x ↦ le_iSup_of_le (x i) (le_iSup_of_le x le_rfl)
    · refine iSup_le fun t ↦ iSup_le fun x ↦ le_iSup_of_le (Function.update x i t) ?_
      apply le_of_eq
      rw [Function.update_self]
      congr 1
      exact Finset.sum_congr rfl fun j hj ↦ by rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)]

/-- Subtraction distributes over finite sums of proper-function values
when the first term of each difference is a real scalar. -/
theorem coe_sum_sub_sum_of_ne_bot {ι : Type*} (s : Finset ι) (a : ι → ℝ) (b : ι → EReal)
    (h : ∀ i ∈ s, b i ≠ ⊥) :
    ((∑ i ∈ s, a i : ℝ) : EReal) - ∑ i ∈ s, b i = ∑ i ∈ s, ((a i : EReal) - b i) := by
  classical
  suffices H : (∑ i ∈ s, b i) ≠ ⊥ ∧
      ((∑ i ∈ s, a i : ℝ) : EReal) - ∑ i ∈ s, b i = ∑ i ∈ s, ((a i : EReal) - b i) from H.2
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    obtain ⟨hb,he⟩ := ih (fun j hj ↦ h j (Finset.mem_insert_of_mem hj))
    have hbi := h i (Finset.mem_insert_self _ _)
    simp only [Finset.sum_insert hi]
    refine ⟨EReal.add_ne_bot_iff.mpr ⟨hbi,hb⟩,?_⟩
    rw [← he,EReal.coe_add]
    simp only [sub_eq_add_neg,EReal.neg_add (Or.inl hbi) (Or.inr hb)]
    exact add_add_add_comm _ _ _ _

/-- **Proposition 11.22**. The conjugate of a sum on a finite product is
the sum of the conjugates, allowing different dimensions for each factor. -/
theorem fenchelConjugate_dependentSeparablePi {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
    (f : ∀ i, E i → EReal) (hf : ∀ i, IsProper (f i)) :
    fenchelConjugate (dependentSeparablePi f) = dependentSeparablePi (fun i ↦ fenchelConjugate (f i)) := by
  classical
  funext v
  change (⨆ x : PiLp 2 E, (⟪v,x⟫_ℝ : EReal) - ∑ i, f i (x i)) = _
  simp_rw [PiLp.inner_apply]
  calc
    _ = ⨆ x : ∀ i, E i, ∑ i, ((⟪v i,x i⟫_ℝ : EReal) - f i (x i)) := by
      apply Equiv.iSup_congr (WithLp.equiv 2 _)
      intro x
      exact (coe_sum_sub_sum_of_ne_bot Finset.univ (fun i ↦ ⟪v i,x i⟫_ℝ)
        (fun i ↦ f i (x i)) (fun i _ ↦ ((hf i).2 (x i)).ne')).symm
    _ = _ := ereal_iSup_sum_independent (fun i x ↦ (⟪v i,x⟫_ℝ : EReal) - f i x) Finset.univ

end RW
