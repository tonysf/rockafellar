/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Weight estimate for the Ky Fan variational formula
-/
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

namespace RW

/-- A weight vector with entries in `[0,1]` and total mass `k` cannot give a
larger weighted sum than placing unit mass on the first `k` entries of a
decreasing real sequence. No sign assumption on the entries is needed. -/
theorem sum_mul_weights_le_sum_initial {n k : ℕ} (hk : k ≤ n)
    {d w : Fin n → ℝ} (hd : Antitone d) (hw₀ : ∀ i, 0 ≤ w i)
    (hw₁ : ∀ i, w i ≤ 1) (hmass : ∑ i, w i = (k : ℝ)) :
    ∑ i, d i * w i ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n ↦ i.val < k), d i := by
  classical
  rcases lt_or_eq_of_le hk with hkn | rfl
  · let j : Fin n := ⟨k,hkn⟩
    let s := Finset.univ.filter (fun i : Fin n ↦ i.val < k)
    have hs : s = Finset.Iio j := by ext i; simp [s,j,Fin.lt_def]
    have hcard : s.card = k := by rw [hs,Fin.card_Iio]
    have hpoint (i : Fin n) : (d i - d j) * w i ≤ if i ∈ s then d i - d j else 0 := by
      by_cases hi : i ∈ s
      · rw [if_pos hi]
        have hij : i < j := Finset.mem_Iio.mp (hs ▸ hi)
        exact mul_le_of_le_one_right (sub_nonneg.mpr (hd hij.le)) (hw₁ i)
      · rw [if_neg hi]
        have hji : j ≤ i := le_of_not_gt (fun hij ↦ hi (hs ▸ Finset.mem_Iio.mpr hij))
        exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hd hji)) (hw₀ i)
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hpoint i)
    simp only [sub_mul,Finset.sum_sub_distrib,← Finset.mul_sum,hmass] at h
    have hr : (∑ i : Fin n, if i ∈ s then d i - d j else 0) = (∑ i ∈ s, d i) - (k:ℝ)*d j := by
      rw [← Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.sum_sub_distrib]
      simp [hcard,nsmul_eq_mul]
    rw [hr] at h
    change _ ≤ ∑ i ∈ s, d i
    linarith [mul_comm (k:ℝ) (d j)]
  · have hsum : (∑ i, (1-w i)) = 0 := by simp [Finset.sum_sub_distrib,hmass]
    have hw (i : Fin k) : w i = 1 := by
      have h := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ sub_nonneg.mpr (hw₁ i))).mp hsum i (Finset.mem_univ i)
      linarith
    simp [hw]

end RW
