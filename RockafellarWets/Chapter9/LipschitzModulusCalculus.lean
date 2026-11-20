/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: Calculus of the Lipschitz modulus
-/

import RockafellarWets.Chapter9.LipschitzModulus
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.Normed.Module.Basic

open Filter Metric Set Topology
open scoped ENNReal NNReal

namespace RW

variable {E F G : Type*} [MetricSpace E]

theorem lipschitzModulusWithin_const [MetricSpace F] (c : F) (X : Set E) (x : E) :
    lipschitzModulusWithin (fun _ : E ↦ c) X x = 0 := by
  apply bot_unique
  exact lipschitzModulusWithin_le (k := 0) univ_mem (fun _ _ _ _ ↦ by simp)

/-- Composing with a globally Lipschitz outer function multiplies the
relative modulus by at most its Lipschitz constant, also at infinite moduli. -/
theorem lipschitzModulusWithin_comp_lipschitzWith [MetricSpace F] [MetricSpace G]
    {g : F → G} {k : ℝ≥0} (hg : LipschitzWith k g) (f : E → F) (X : Set E) (x : E) :
    lipschitzModulusWithin (g ∘ f) X x ≤ (k : ℝ≥0∞) * lipschitzModulusWithin f X x := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp only [ENNReal.coe_zero, zero_mul]
    exact lipschitzModulusWithin_le (k := 0) univ_mem (fun y _ z _ ↦ by simpa using hg (f y) (f z))
  · unfold lipschitzModulusWithin
    rw [ENNReal.mul_iInf_of_ne (ENNReal.coe_ne_zero.mpr hk) ENNReal.coe_ne_top]
    refine le_iInf fun a ↦ ?_
    obtain ⟨U, hU, hf⟩ := a.property
    rw [← ENNReal.coe_mul]
    exact lipschitzModulusWithin_le hU (hg.comp_lipschitzOnWith hf)

/-- **Exercise 9.8(a)**, including a zero multiplier at an infinite modulus. -/
theorem lipschitzModulusWithin_smul [NormedAddCommGroup F] [NormedSpace ℝ F] (r : ℝ)
    (f : E → F) (X : Set E) (x : E) :
    lipschitzModulusWithin (fun y ↦ r • f y) X x = (‖r‖₊ : ℝ≥0∞) * lipschitzModulusWithin f X x := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp only [zero_smul, nnnorm_zero, ENNReal.coe_zero, zero_mul, lipschitzModulusWithin_const]
  refine le_antisymm (lipschitzModulusWithin_comp_lipschitzWith (lipschitzWith_smul r) f X x) ?_
  have h := lipschitzModulusWithin_comp_lipschitzWith (lipschitzWith_smul r⁻¹) (fun y ↦ r • f y) X x
  simp only [Function.comp_def, smul_smul, inv_mul_cancel₀ hr, one_smul] at h
  calc
    _ ≤ (‖r‖₊ : ℝ≥0∞) * ((‖r⁻¹‖₊ : ℝ≥0∞) * lipschitzModulusWithin (fun y ↦ r • f y) X x) :=
      mul_le_mul_right h _
    _ = _ := by rw [← mul_assoc, ← ENNReal.coe_mul, ← nnnorm_mul, mul_inv_cancel₀ hr]; simp

theorem lipschitzModulusWithin_neg [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (X : Set E) (x : E) :
    lipschitzModulusWithin (fun y ↦ -f y) X x = lipschitzModulusWithin f X x := by
  simpa using lipschitzModulusWithin_smul (-1) f X x

/-- **Exercise 9.8(b)**, the sum bound. -/
theorem lipschitzModulusWithin_add_le [NormedAddCommGroup F] (f g : E → F) (X : Set E) (x : E) :
    lipschitzModulusWithin (fun y ↦ f y + g y) X x ≤ lipschitzModulusWithin f X x + lipschitzModulusWithin g X x := by
  apply ENNReal.le_iInf_add_iInf
  intro k l
  obtain ⟨U, hU, hf⟩ := k.property
  obtain ⟨V, hV, hg⟩ := l.property
  rw [← ENNReal.coe_add]
  apply lipschitzModulusWithin_le (inter_mem hU hV)
  apply LipschitzOnWith.of_dist_le_mul
  intro y hy z hz
  calc
    _ ≤ dist (f y + g y) (f z + g y) + dist (f z + g y) (f z + g z) := dist_triangle ..
    _ = dist (f y) (f z) + dist (g y) (g z) := by simp only [dist_add_right, dist_add_left]
    _ ≤ _ := (add_le_add (hf.dist_le_mul _ hy.1 _ hz.1) (hg.dist_le_mul _ hy.2 _ hz.2)).trans_eq
      (by simp only [NNReal.coe_add, add_mul])

/-- **Exercise 9.8(c)**, the composition bound for strictly continuous
mappings. The two finite moduli avoid the indeterminate zero/infinity product. -/
theorem lipschitzModulus_comp_le [MetricSpace F] [MetricSpace G] {f : E → F} {g : F → G} {x : E}
    (hf : StrictlyContinuousAt f x) (hg : StrictlyContinuousAt g (f x)) :
    lipschitzModulus (g ∘ f) x ≤ lipschitzModulus g (f x) * lipschitzModulus f x := by
  obtain ⟨k, U, hU, hfk⟩ := strictlyContinuousAt_iff.mp hf
  obtain ⟨l, V, hV, hgl⟩ := strictlyContinuousAt_iff.mp hg
  apply ENNReal.le_iInf_mul_iInf
  · exact ⟨⟨l, V, nhdsWithin_univ (f x) ▸ hV, hgl⟩, ENNReal.coe_ne_top⟩
  · exact ⟨⟨k, U, nhdsWithin_univ x ▸ hU, hfk⟩, ENNReal.coe_ne_top⟩
  · intro a b
    obtain ⟨A, hA, hga⟩ := a.property
    obtain ⟨B, hB, hfb⟩ := b.property
    rw [nhdsWithin_univ] at hA hB
    rw [← ENNReal.coe_mul]
    exact lipschitzModulus_le (inter_mem hB (hf.continuousAt hA))
      (hga.comp (hfb.mono inter_subset_left) (fun _ h ↦ h.2))

/-- **Exercise 9.8(c)** also permits infinite moduli whenever neither factor
is zero while the other is infinite. The excluded cases genuinely fail under
the extended-nonnegative-real convention `0 * ∞ = 0`. -/
theorem lipschitzModulus_comp_le_of_no_zero_infinity [MetricSpace F] [MetricSpace G]
    {f : E → F} {g : F → G} {x : E}
    (hgzero : lipschitzModulus g (f x) = 0 → lipschitzModulus f x ≠ ⊤)
    (hfzero : lipschitzModulus f x = 0 → lipschitzModulus g (f x) ≠ ⊤) :
    lipschitzModulus (g ∘ f) x ≤ lipschitzModulus g (f x) * lipschitzModulus f x := by
  by_cases hf : lipschitzModulus f x = ⊤
  · rw [hf,ENNReal.mul_top (fun h ↦ hgzero h hf)]
    exact le_top
  by_cases hg : lipschitzModulus g (f x) = ⊤
  · rw [hg,ENNReal.top_mul (fun h ↦ hfzero h hg)]
    exact le_top
  exact lipschitzModulus_comp_le (lt_top_iff_ne_top.mpr hf) (lt_top_iff_ne_top.mpr hg)

end RW
