/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Finite ball intersection for Lipschitz extensions
-/

import RockafellarWets.Chapter8.FiniteMaxSubgradients
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Group.Bounded

open Filter Metric Set Topology
open scoped BigOperators InnerProductSpace Gradient

namespace RW

variable {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [Fintype ι]

/-- The weighted pairwise squared-distance identity. -/
theorem weighted_pairwise_norm_sq (w : ι → ℝ) (u : ι → E) (hw : ∑ i, w i = 1) :
    ∑ i, ∑ j, w i * w j * ‖u i - u j‖ ^ 2 =
      2 * (∑ i, w i * ‖u i‖ ^ 2) - 2 * ‖∑ i, w i • u i‖ ^ 2 := by
  have hi : ‖∑ i, w i • u i‖ ^ 2 = ∑ i, ∑ j, w i * w j * ⟪u i,u j⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [real_inner_comm (u j) (u i)]
    ring
  rw [hi]
  simp_rw [norm_sub_sq_real]
  have expand (i j : ι) : w i * w j * (‖u i‖ ^ 2 - 2 * ⟪u i,u j⟫_ℝ + ‖u j‖ ^ 2) =
      (w i * ‖u i‖ ^ 2) * w j - 2 * (w i * w j * ⟪u i,u j⟫_ℝ) + w i * (w j * ‖u j‖ ^ 2) := by ring
  simp_rw [expand,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.sum_mul,hw]
  ring

private theorem gradient_sq_dist_sub_const (b x : F) (c : ℝ) :
    ∇ (fun y : F ↦ ‖y-b‖ ^ 2 - c) x = (2:ℝ) • (x-b) := by
  letI := FiniteDimensional.complete ℝ F
  have h : HasGradientAt (fun y : F ↦ ‖y-b‖ ^ 2 - c) ((2:ℝ) • (x-b)) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert ((hasFDerivAt_id x).sub_const b).norm_sq.sub_const c using 1 <;>
      ext v <;> simp
  exact h.gradient

/-- The finite intersection step in **Theorem 9.58**: pairwise contractions
of the centers preserve the intersection property of balls centered there. -/
theorem exists_mem_closedBalls_of_pairwise_dist_le [Nonempty ι]
    (a : ι → E) (b : ι → F) (hab : ∀ i j, ‖b i - b j‖ ≤ ‖a i - a j‖) :
    ∃ y : F, ∀ i, ‖y-b i‖ ≤ ‖a i‖ := by
  classical
  letI := FiniteDimensional.complete ℝ F
  let fs (i : ι) (y : F) := ‖y-b i‖ ^ 2 - ‖a i‖ ^ 2
  have hs (i : ι) : ContDiff ℝ 1 (fs i) := by
    dsimp only [fs]
    exact ((contDiff_id.sub contDiff_const).norm_sq ℝ).sub contDiff_const
  have hc : Continuous (finiteMax fs) := by
    unfold finiteMax
    exact Continuous.finset_sup'_apply _ fun i _ ↦ (hs i).continuous
  let i₀ : ι := Classical.arbitrary _
  have hcoerce : Tendsto (finiteMax fs) (cocompact F) atTop := by
    apply Filter.tendsto_atTop.mpr
    intro R
    have hn := (tendsto_norm_cocompact_atTop (E := F)).eventually
      (eventually_ge_atTop (Real.sqrt (max (R + ‖a i₀‖ ^ 2) 0) + ‖b i₀‖))
    filter_upwards [hn] with y hy
    have htri : ‖y‖ ≤ ‖y-b i₀‖ + ‖b i₀‖ := by
      simpa only [sub_add_cancel] using norm_add_le (y-b i₀) (b i₀)
    have hsqrt := Real.sq_sqrt (le_max_right (R + ‖a i₀‖ ^ 2) 0)
    have hmax := le_max_left (R + ‖a i₀‖ ^ 2) 0
    have hsq : R ≤ fs i₀ y := by
      dsimp only [fs]
      nlinarith [Real.sqrt_nonneg (max (R + ‖a i₀‖ ^ 2) 0),norm_nonneg (y-b i₀)]
    exact hsq.trans (le_finiteMax fs y i₀)
  obtain ⟨y,hy⟩ := hc.exists_forall_le hcoerce
  have hzero : (0:F) ∈ subdifferential (fun z ↦ (finiteMax fs z : EReal)) y := by
    apply regularSubdifferential_subset_subdifferential
    refine ⟨finiteMax fs y,rfl,fun ε hε ↦ .of_forall fun z ↦ ?_⟩
    simp only [inner_zero_left,add_zero,EReal.coe_le_coe_iff]
    exact (sub_le_self _ (mul_nonneg hε.le (norm_nonneg _))).trans (hy z)
  rw [subdifferential_finiteMax hs] at hzero
  obtain ⟨κ,_,w,z,hw,hws,hz,hzero⟩ := mem_convexHull_iff_exists_fintype.mp hzero
  have hactive (j : κ) : ∃ i : ι, fs i y = finiteMax fs y ∧ z j = (2:ℝ) • (y-b i) := by
    obtain ⟨i,hi,hzi⟩ := hz j
    exact ⟨i,mem_maxActiveIndices.mp hi, hzi.symm.trans (gradient_sq_dist_sub_const _ _ _)⟩
  choose idx hidx hzi using hactive
  have hmean : ∑ j, w j • (y-b (idx j)) = 0 := by
    have he : (2:ℝ) • (∑ j, w j • (y-b (idx j))) = 0 := by
      calc
        _ = ∑ j, w j • ((2:ℝ) • (y-b (idx j))) := by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun j _ ↦ smul_comm _ _ _
        _ = ∑ j, w j • z j := by simp only [hzi]
        _ = 0 := hzero
    exact (smul_eq_zero.mp he).resolve_left (by norm_num)
  have hdist (i j : κ) : ‖(y-b (idx i)) - (y-b (idx j))‖ ^ 2 ≤ ‖a (idx i) - a (idx j)‖ ^ 2 := by
    have he : (y-b (idx i)) - (y-b (idx j)) = -(b (idx i)-b (idx j)) := by abel
    rw [he,norm_neg]
    exact sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr (hab _ _)
  have hsum : (∑ i, ∑ j, w i * w j * ‖(y-b (idx i)) - (y-b (idx j))‖ ^ 2) ≤
      ∑ i, ∑ j, w i * w j * ‖a (idx i) - a (idx j)‖ ^ 2 :=
    Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset κ)) ↦
    Finset.sum_le_sum (fun j _ ↦ mul_le_mul_of_nonneg_left (hdist i j) (mul_nonneg (hw i) (hw j))))
  rw [weighted_pairwise_norm_sq w _ hws,weighted_pairwise_norm_sq w _ hws,hmean,norm_zero] at hsum
  have heach : ∑ j, w j * ‖y-b (idx j)‖ ^ 2 = finiteMax fs y + ∑ j, w j * ‖a (idx j)‖ ^ 2 := by
    have hi (j : κ) : w j * ‖y-b (idx j)‖ ^ 2 = w j * finiteMax fs y + w j * ‖a (idx j)‖ ^ 2 := by
      have hj := hidx j
      dsimp only [fs] at hj
      rw [← mul_add]
      congr 1
      linarith
    simp_rw [hi,Finset.sum_add_distrib,← Finset.sum_mul,hws,one_mul]
  rw [heach] at hsum
  have hmin : finiteMax fs y ≤ 0 := by nlinarith [sq_nonneg ‖∑ j, w j • a (idx j)‖]
  refine ⟨y,fun i ↦ ?_⟩
  have hi := (le_finiteMax fs y i).trans hmin
  dsimp only [fs] at hi
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (sub_nonpos.mp hi)

end RW
