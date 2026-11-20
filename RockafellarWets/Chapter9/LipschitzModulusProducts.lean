/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Euclidean bound for the modulus of a product mapping
-/

import RockafellarWets.Chapter9.Scalarization

open Filter Metric Set Topology
open scoped ENNReal NNReal InnerProductSpace

namespace RW

variable {E ι : Type*} [MetricSpace E] [Fintype ι]
  {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)]
  [∀ i, FiniteDimensional ℝ (F i)]

/-- Bounds on the component moduli give the Euclidean norm of those
bounds as a bound for the product modulus. Components may themselves be vectors. -/
theorem lipschitzModulusWithin_piLp_le_of_bounds (f : (i : ι) → E → F i) (X : Set E) (x : E)
    (k : ι → ℝ≥0) (h : ∀ i, lipschitzModulusWithin (f i) X x ≤ (k i : ℝ≥0∞)) :
    lipschitzModulusWithin (fun y ↦ WithLp.toLp 2 (fun i ↦ f i y)) X x ≤
      (‖WithLp.toLp 2 (fun i ↦ (k i : ℝ))‖₊ : ℝ≥0∞) := by
  rw [lipschitzModulusWithin_eq_iSup_unit_inner]
  apply iSup_le
  intro v
  have he : (fun y ↦ ⟪v.1,WithLp.toLp 2 (fun i ↦ f i y)⟫_ℝ) =
      fun y ↦ ∑ i, ⟪v.1 i,f i y⟫_ℝ := by
    funext y
    exact PiLp.inner_apply _ _
  rw [he]
  calc
    _ ≤ ∑ i, lipschitzModulusWithin (fun y ↦ ⟪v.1 i,f i y⟫_ℝ) X x :=
      lipschitzModulusWithin_sum_le Finset.univ _ X x
    _ ≤ ∑ i, (‖v.1 i‖₊ : ℝ≥0∞) * k i := Finset.sum_le_sum fun i _ ↦
      (lipschitzModulusWithin_inner_le (f i) X x (v.1 i)).trans (mul_le_mul' le_rfl (h i))
    _ = ((∑ i, ‖v.1 i‖₊ * k i : ℝ≥0) : ℝ≥0∞) := by simp only [ENNReal.coe_finset_sum,ENNReal.coe_mul]
    _ ≤ _ := by
      apply ENNReal.coe_le_coe.mpr
      apply NNReal.coe_le_coe.mp
      push_cast
      let u : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i ↦ ‖v.1 i‖)
      have hunorm : ‖u‖ = ‖v.1‖ := by simp only [u,PiLp.norm_eq_of_L2,Real.norm_eq_abs,abs_norm]
      have hc := real_inner_le_norm u (WithLp.toLp 2 (fun i ↦ (k i : ℝ)))
      rw [hunorm,v.2,one_mul] at hc
      simpa only [u,PiLp.inner_apply,RCLike.inner_apply',conj_trivial] using hc

/-- **Exercise 9.8(d)**, the Euclidean product bound, with the extended
Euclidean norm on the right so that infinite component moduli are included. -/
theorem lipschitzModulusWithin_piLp_le (f : (i : ι) → E → F i) (X : Set E) (x : E) :
    lipschitzModulusWithin (fun y ↦ WithLp.toLp 2 (fun i ↦ f i y)) X x ≤
      (∑ i, lipschitzModulusWithin (f i) X x ^ 2) ^ (1 / 2 : ℝ) := by
  classical
  by_cases hfin : ∀ i, lipschitzModulusWithin (f i) X x ≠ ⊤
  · let k := fun i ↦ (lipschitzModulusWithin (f i) X x).toNNReal
    have hk (i : ι) : (k i : ℝ≥0∞) = lipschitzModulusWithin (f i) X x := ENNReal.coe_toNNReal (hfin i)
    have hb := lipschitzModulusWithin_piLp_le_of_bounds f X x k (fun i ↦ (hk i).ge)
    apply hb.trans_eq
    rw [PiLp.nnnorm_eq_of_L2]
    simp only [NNReal.nnnorm_eq,NNReal.sqrt_eq_rpow,ENNReal.coe_rpow_of_nonneg _ (by norm_num : (0:ℝ) ≤ 1/2),ENNReal.coe_finset_sum,
      ENNReal.coe_pow,hk]
  · push_neg at hfin
    obtain ⟨i,hi⟩ := hfin
    have hsum : (∑ j, lipschitzModulusWithin (f j) X x ^ 2) = ⊤ := by
      apply top_unique
      simpa only [hi,ENNReal.top_pow,OfNat.ofNat_ne_zero,not_false_eq_true] using
        (Finset.single_le_sum (f := fun j ↦ lipschitzModulusWithin (f j) X x ^ 2)
          (fun j _ ↦ bot_le) (Finset.mem_univ i))
    rw [hsum,ENNReal.top_rpow_of_pos (by norm_num)]
    exact le_top

end RW
