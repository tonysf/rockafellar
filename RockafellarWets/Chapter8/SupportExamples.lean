/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: The canonical simplex and the Euclidean ball
-/

import RockafellarWets.Chapter8.SupportFunctions
import RockafellarWets.Chapter3.Entropy
import RockafellarWets.Chapter7.MaxFunctionRegularity
import Mathlib.Analysis.InnerProductSpace.PiL2

open Metric Set
open scoped InnerProductSpace

namespace RW

section Simplex

variable {ι : Type*} [Fintype ι]

/-- The Chapter 3 probability simplex in Euclidean coordinates. -/
def canonicalSimplex : Set (EuclideanSpace ℝ ι) := WithLp.ofLp ⁻¹' simplexSet

theorem convex_canonicalSimplex : Convex ℝ (canonicalSimplex (ι := ι)) :=
  convex_simplexSet.linear_preimage (WithLp.linearEquiv 2 ℝ (ι → ℝ)).toLinearMap

theorem isClosed_canonicalSimplex : IsClosed (canonicalSimplex (ι := ι)) :=
  isClosed_simplexSet.preimage (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℝ)).continuous

variable [Nonempty ι]

/-- The largest coordinate of a Euclidean vector in positive dimension. -/
noncomputable def vecMax : EuclideanSpace ℝ ι → ℝ := finiteMax (fun i x ↦ x i)

theorem canonicalSimplex_nonempty : (canonicalSimplex (ι := ι)).Nonempty := by
  obtain ⟨v,hv⟩ := simplexSet_nonempty (ι := ι)
  exact ⟨WithLp.toLp 2 v,hv⟩

omit [Nonempty ι] in
private theorem simplex_inner (x w : EuclideanSpace ℝ ι) : ⟪x,w⟫_ℝ = ∑ i, x i*w i := by
  simp [PiLp.inner_apply, mul_comm]

/-- **Example 8.26.** The support function of the canonical simplex is the
maximum coordinate, with the maximum attained at a coordinate vector. -/
theorem supportFunction_canonicalSimplex (w : EuclideanSpace ℝ ι) :
    supportFunction canonicalSimplex w = (vecMax w : EReal) ∧
      ∃ v ∈ canonicalSimplex, ⟪v,w⟫_ℝ = vecMax w := by
  classical
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ) Finset.univ_nonempty (fun i ↦ w i)
  let v := EuclideanSpace.single i (1 : ℝ)
  have hv : v ∈ canonicalSimplex := by
    change (∀ j, 0 ≤ v j) ∧ ∑ j, v j = 1
    simp [v, EuclideanSpace.single_apply, ite_nonneg]
  have hinner : ⟪v,w⟫_ℝ = vecMax w := by
    simpa [v, EuclideanSpace.inner_single_left, vecMax, finiteMax] using hi.symm
  refine ⟨le_antisymm ((supportFunction_le_iff _ _ _).2 (fun z hz ↦ ?_))
    (hinner ▸ inner_le_supportFunction hv w), ⟨v,hv,hinner⟩⟩
  rw [EReal.coe_le_coe_iff, simplex_inner]
  calc
    ∑ i, z i*w i ≤ ∑ i, z i*vecMax w := Finset.sum_le_sum fun i _ ↦
      mul_le_mul_of_nonneg_left (le_finiteMax (fun j (u : EuclideanSpace ℝ ι) ↦ u j) w i) (hz.1 i)
    _ = vecMax w := by rw [← Finset.sum_mul, hz.2, one_mul]

/-- A probability vector attains the vector maximum precisely when its
positive coordinates only occur at maximizing indices. -/
theorem simplex_inner_eq_vecMax_iff {v w : EuclideanSpace ℝ ι} (hv : v ∈ canonicalSimplex) :
    ⟪v,w⟫_ℝ = vecMax w ↔ ∀ i, w i ≠ vecMax w → v i = 0 := by
  classical
  have hsum : ∑ i, v i*(vecMax w-w i) = vecMax w - ⟪v,w⟫_ℝ := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hv.2, one_mul, simplex_inner]
  have hn (i : ι) : 0 ≤ v i*(vecMax w-w i) :=
    mul_nonneg (hv.1 i) (sub_nonneg.2 (le_finiteMax (fun j (u : EuclideanSpace ℝ ι) ↦ u j) w i))
  constructor
  · intro he i hi
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ hn i)).1 (hsum.trans (by rw [he, sub_self])) i (Finset.mem_univ i)
    exact (mul_eq_zero.1 h0).resolve_right (sub_ne_zero.2 hi.symm)
  · intro h
    have hzero : ∑ i, v i*(vecMax w-w i) = 0 := Finset.sum_eq_zero fun i _ ↦ by
      by_cases hi : w i = vecMax w
      · rw [hi, sub_self, mul_zero]
      · rw [h i hi, zero_mul]
    linarith

end Simplex

section Ball

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Exercise 8.27.** The support value on the unit ball equals the norm and
is attained in every direction, including the zero direction. -/
theorem supportFunction_unitBall (w : E) :
    supportFunction (closedBall (0:E) 1) w = (‖w‖ : EReal) ∧
      ∃ v ∈ closedBall (0:E) 1, ⟪v,w⟫_ℝ = ‖w‖ := by
  have hupper := (supportFunction_le_iff (closedBall (0:E) 1) w (‖w‖ : EReal)).2 fun v hv ↦
    EReal.coe_le_coe_iff.2 (((le_abs_self _).trans (abs_real_inner_le_norm v w)).trans
      (by simpa using mul_le_mul_of_nonneg_right (mem_closedBall_zero_iff.1 hv) (norm_nonneg w)))
  by_cases hw : w = 0
  · subst w
    exact ⟨by simp [supportFunction_zero (nonempty_closedBall.2 zero_le_one)], ⟨0, by simp, by simp⟩⟩
  let v := ‖w‖⁻¹ • w
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw
  have hv : v ∈ closedBall (0:E) 1 := by
    rw [mem_closedBall_zero_iff, show ‖v‖=1 by simp [v, norm_smul, hn]]
  have he : ⟪v,w⟫_ℝ = ‖w‖ := by rw [real_inner_smul_left, real_inner_self_eq_norm_sq]; field_simp
  exact ⟨hupper.antisymm (he ▸ inner_le_supportFunction hv w),⟨v,hv,he⟩⟩

theorem unitBall_inner_eq_norm_iff {v w : E} (hw : w ≠ 0) (hv : v ∈ closedBall (0:E) 1) :
    ⟪v,w⟫_ℝ = ‖w‖ ↔ v = ‖w‖⁻¹ • w := by
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
  constructor
  · intro he
    have hprod := (le_abs_self _).trans (abs_real_inner_le_norm v w)
    rw [he] at hprod
    have hnv : ‖v‖ = 1 := (mem_closedBall_zero_iff.1 hv).antisymm (by nlinarith)
    have hmul := (inner_eq_norm_mul_iff_real (x := v) (y := w)).1 (by simpa [hnv] using he)
    rw [hnv,one_smul] at hmul
    simpa [inv_smul_smul₀ hn.ne'] using congrArg (fun z : E ↦ ‖w‖⁻¹ • z) hmul
  · rintro rfl
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]; field_simp

end Ball

end RW
