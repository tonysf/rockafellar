/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Log-sum-exp and entropy
-/

import RockafellarWets.Chapter3.Entropy
import RockafellarWets.Chapter11.FenchelMoreau
import Mathlib.Analysis.InnerProductSpace.PiL2

open Set
open scoped InnerProductSpace

namespace RW

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The log-exponential function in Example 11.12. -/
noncomputable def logSumExp (x : EuclideanSpace ℝ ι) : ℝ :=
  Real.log (∑ i, Real.exp (x i))

private theorem sum_exp_pos (x : EuclideanSpace ℝ ι) : 0 < ∑ i, Real.exp (x i) :=
  Finset.sum_pos (fun i _ ↦ Real.exp_pos (x i)) Finset.univ_nonempty

private theorem normalized_exp_mem_simplex (x : EuclideanSpace ℝ ι) :
    (fun i ↦ Real.exp (x i - logSumExp x)) ∈ simplexSet := by
  refine ⟨fun i ↦ (Real.exp_pos _).le,?_⟩
  simp_rw [Real.exp_sub,← Finset.sum_div,logSumExp,Real.exp_log (sum_exp_pos x),div_self (sum_exp_pos x).ne']

/-- The variational entropy inequality includes zero coordinates of a
probability vector. -/
theorem inner_sub_entropy_le_logSumExp (x y : EuclideanSpace ℝ ι)
    (hy : WithLp.ofLp y ∈ simplexSet) :
    ⟪x,y⟫_ℝ - entropyCore (WithLp.ofLp y) ≤ logSumExp x := by
  let q (i : ι) := Real.exp (x i - logSumExp x)
  have hq := normalized_exp_mem_simplex x
  have hi (i : ι) : y i * x i - y i * Real.log (y i) - y i * logSumExp x ≤ q i - y i := by
    rcases lt_or_eq_of_le (hy.1 i) with hpos | hzero
    · have h := mul_le_mul_of_nonneg_right
        (Real.log_le_sub_one_of_pos (div_pos (Real.exp_pos (x i - logSumExp x)) hpos)) hpos.le
      rw [Real.log_div (Real.exp_pos _).ne' hpos.ne',Real.log_exp] at h
      simp only [sub_mul,div_mul_cancel₀ _ hpos.ne',one_mul] at h
      dsimp [q]
      linarith only [h]
    · change 0 = y i at hzero
      simpa [← hzero] using (le_of_lt (Real.exp_pos (x i - logSumExp x)))
  have H := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hi i)
  have hm : ∑ i, y i = 1 := hy.2
  have hqm : ∑ i, q i = 1 := hq.2
  simp only [Finset.sum_sub_distrib,← Finset.sum_mul,hm,hqm,one_mul,sub_self] at H
  have he : ⟪x,y⟫_ℝ = ∑ i, y i * x i := by simp [PiLp.inner_apply]
  rw [he]
  change ∑ i, y i * x i - ∑ i, y i * Real.log (y i) ≤ logSumExp x
  linarith

/-- The entropy conjugate attains its supremum at the normalized exponential
weights, giving the log-exponential function. -/
theorem fenchelConjugate_simplexEntropy :
    fenchelConjugate (fun y : EuclideanSpace ℝ ι ↦ simplexEntropy (WithLp.ofLp y)) =
      fun x ↦ (logSumExp x : EReal) := by
  funext x
  refine le_antisymm ((fenchelConjugate_le_iff _ _ _).mpr fun y ↦ ?_) ?_
  · by_cases hy : WithLp.ofLp y ∈ simplexSet
    · rw [simplexEntropy_apply_of_mem hy,← EReal.coe_sub,EReal.coe_le_coe_iff]
      exact inner_sub_entropy_le_logSumExp x y hy
    · rw [simplexEntropy_apply_of_not_mem hy,EReal.sub_top]
      exact bot_le
  · let p := fun i ↦ Real.exp (x i - logSumExp x)
    let y := WithLp.toLp 2 p
    have hp : p ∈ simplexSet := normalized_exp_mem_simplex x
    have hl := le_fenchelConjugate (fun z : EuclideanSpace ℝ ι ↦ simplexEntropy (WithLp.ofLp z)) y x
    change (⟪x,y⟫_ℝ : EReal) - simplexEntropy p ≤ _ at hl
    rw [simplexEntropy_apply_of_mem hp,← EReal.coe_sub] at hl
    have he : ⟪x,y⟫_ℝ - entropyCore p = logSumExp x := by
      have hi : ⟪x,y⟫_ℝ = ∑ i, p i * x i := by simp [PiLp.inner_apply,y]
      rw [hi,entropyCore,← Finset.sum_sub_distrib]
      calc
        _ = ∑ i, p i * logSumExp x := Finset.sum_congr rfl fun i _ ↦ by
          rw [show Real.log (p i) = x i - logSumExp x from Real.log_exp _]
          ring
        _ = _ := by rw [← Finset.sum_mul,hp.2,one_mul]
    rwa [he] at hl

/-- **Example 11.12**, conjugacy on the entire space, including probability
vectors on the boundary and the infinite value outside the simplex. -/
theorem fenchelConjugate_logSumExp :
    fenchelConjugate (fun x : EuclideanSpace ℝ ι ↦ (logSumExp x : EReal)) =
      fun y ↦ simplexEntropy (WithLp.ofLp y) := by
  rw [← fenchelConjugate_simplexEntropy]
  apply fenchelConjugate_fenchelConjugate_eq
  · obtain ⟨⟨y,hy⟩,hb⟩ := simplexEntropy_isProper (ι := ι)
    exact ⟨⟨WithLp.toLp 2 y,hy⟩,fun y ↦ hb (WithLp.ofLp y)⟩
  · exact lowerSemicontinuous_simplexEntropy.comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℝ)).continuous
  · let A := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℝ)).toLinearEquiv.toLinearMap
    exact convex_epigraph_simplexEntropy.linear_preimage (A.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ))

end RW
