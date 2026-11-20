/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Finite inf-addition without negative infinite summands
-/

import RockafellarWets.Chapter7.FiniteEpiSums
import RockafellarWets.Chapter10.SeparableSubgradients

open Set

namespace RW

variable {ι : Type*} [Fintype ι]

theorem finiteInfAddition_eq_sum_of_ne_bot (a : ι → EReal) (ha : ∀ i, a i ≠ ⊥) :
    finiteInfAddition a = ∑ i, a i := by
  classical
  have hsum (r : ι → ℝ) : (∑ i, (r i : EReal)) = ((∑ i, r i : ℝ):EReal) := by
    induction (Finset.univ : Finset ι) using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => rw [Finset.sum_insert hi,Finset.sum_insert hi,ih,EReal.coe_add]
  have hbot : (⊥:EReal) < ∑ i, a i := by
    induction (Finset.univ : Finset ι) using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => rw [Finset.sum_insert hi]; exact EReal.bot_lt_add_iff.mpr ⟨bot_lt_iff_ne_bot.mpr (ha i),ih⟩
  apply le_antisymm
  · by_cases ht : ∑ i, a i = ⊤
    · rw [ht]; exact le_top
    have hc : ∑ i, a i = (((∑ i, a i).toReal : ℝ):EReal) := (EReal.coe_toReal ht hbot.ne').symm
    have hh (i : ι) : ∃ r : ℝ, a i = r := by
      have he : a i+(∑ j ∈ Finset.univ.erase i, a j) = (((∑ j, a j).toReal : ℝ):EReal) := by
        rw [Finset.add_sum_erase Finset.univ a (Finset.mem_univ i)]
        exact hc
      obtain ⟨r,s,hr,_⟩ := exists_coe_components_of_add_eq_coe he
      exact ⟨r,hr⟩
    choose r hr using hh
    have he : ∑ i, a i = ((∑ i, r i : ℝ):EReal) := by simp only [hr,hsum]
    rw [he]
    exact finiteInfAddition_le_sum (fun i ↦ (hr i).le)
  · apply le_iInf
    intro r
    rw [← hsum]
    exact Finset.sum_le_sum (fun i _ ↦ r.2 i)

end RW
