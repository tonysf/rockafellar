/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 2C: Vector-max, log-exponential and norm examples

This file formalizes Examples 2.16 and 2.17 of Rockafellar–Wets.

* Example 2.16: the vector-max function `vecMax` (Chapter 8) and the
  log-exponential function `logSumExp` (Chapter 11) on `EuclideanSpace ℝ ι`
  are convex but not strictly convex.
* Example 2.17: every norm, i.e. every function with the three norm axioms
  (`IsNormFunction`), is convex but not strictly convex, its balls are convex,
  and the `ℓᵖ` norms for `1 ≤ p < ∞` and the `ℓ^∞` norm of 2(9) are norms.

The convexity of `logSumExp` is obtained from the convexity of `exp` after
normalizing each exponential sum to `1`, which is the Hölder inequality in
disguise; the book's Hessian computation is not needed.
-/

import RockafellarWets.Chapter2.ConvexFunctions
import RockafellarWets.Chapter8.SupportExamples
import RockafellarWets.Chapter11.EntropyConjugacy
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

open Set
open scoped InnerProductSpace

noncomputable section

namespace RW

/-! ## Example 2.16 -/

section VecMaxLogExp

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The vector of ones in `EuclideanSpace ℝ ι`. -/
def onesVector : EuclideanSpace ℝ ι := WithLp.toLp 2 fun _ ↦ 1

omit [Fintype ι] [Nonempty ι] in
@[simp] theorem onesVector_apply (i : ι) : (onesVector : EuclideanSpace ℝ ι) i = 1 := rfl

omit [Fintype ι] in
theorem onesVector_ne_zero : (onesVector : EuclideanSpace ℝ ι) ≠ 0 := by
  intro h
  have := congrArg (fun v : EuclideanSpace ℝ ι ↦ v (Classical.arbitrary ι)) h
  simp at this

theorem vecMax_smul_onesVector (c : ℝ) : vecMax (c • (onesVector : EuclideanSpace ℝ ι)) = c := by
  apply le_antisymm
  · exact finiteMax_le_iff.mpr fun i ↦ by simp
  · have := le_finiteMax (fun i (x : EuclideanSpace ℝ ι) ↦ x i)
      (c • (onesVector : EuclideanSpace ℝ ι)) (Classical.arbitrary ι)
    simpa [vecMax] using this

theorem logSumExp_smul_onesVector (c : ℝ) :
    logSumExp (c • (onesVector : EuclideanSpace ℝ ι)) = Real.log (Fintype.card ι) + c := by
  simp only [logSumExp, PiLp.smul_apply, onesVector_apply, smul_eq_mul, mul_one,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Real.log_mul (by exact_mod_cast Fintype.card_ne_zero) (Real.exp_pos c).ne', Real.log_exp]

/-- **Example 2.16**: the vector-max function is convex. -/
theorem convexOn_vecMax : ConvexOn ℝ univ (vecMax : EuclideanSpace ℝ ι → ℝ) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
  refine finiteMax_le_iff.mpr fun i ↦ ?_
  have hx := le_finiteMax (fun i (x : EuclideanSpace ℝ ι) ↦ x i) x i
  have hy := le_finiteMax (fun i (x : EuclideanSpace ℝ ι) ↦ x i) y i
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)

/-- **Example 2.16**: the vector-max function is not strictly convex. -/
theorem not_strictConvexOn_vecMax : ¬StrictConvexOn ℝ univ (vecMax : EuclideanSpace ℝ ι → ℝ) := by
  intro h
  have := h.2 (mem_univ 0) (mem_univ onesVector) onesVector_ne_zero.symm
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  rw [smul_zero, zero_add, vecMax_smul_onesVector] at this
  have h0 : vecMax (0 : EuclideanSpace ℝ ι) = 0 := by
    simpa using vecMax_smul_onesVector (ι := ι) 0
  have h1 : vecMax (onesVector : EuclideanSpace ℝ ι) = 1 := by
    simpa using vecMax_smul_onesVector (ι := ι) 1
  rw [h0, h1] at this
  norm_num at this

/-- **Example 2.16**: the log-exponential function is convex. -/
theorem convexOn_logSumExp : ConvexOn ℝ univ (logSumExp : EuclideanSpace ℝ ι → ℝ) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
  simp only [logSumExp, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  set U := ∑ i, Real.exp (x i) with hUdef
  set V := ∑ i, Real.exp (y i) with hVdef
  have hU : 0 < U := Finset.sum_pos (fun i _ ↦ Real.exp_pos _) Finset.univ_nonempty
  have hV : 0 < V := Finset.sum_pos (fun i _ ↦ Real.exp_pos _) Finset.univ_nonempty
  set L := a * Real.log U + b * Real.log V
  have hnormU : ∑ i, Real.exp (x i - Real.log U) = 1 := by
    simp_rw [Real.exp_sub, Real.exp_log hU, ← Finset.sum_div, ← hUdef, div_self hU.ne']
  have hnormV : ∑ i, Real.exp (y i - Real.log V) = 1 := by
    simp_rw [Real.exp_sub, Real.exp_log hV, ← Finset.sum_div, ← hVdef, div_self hV.ne']
  have hsplit : ∀ i, Real.exp (a * x i + b * y i) =
      Real.exp L * Real.exp (a * (x i - Real.log U) + b * (y i - Real.log V)) := by
    intro i
    rw [← Real.exp_add]
    congr 1
    ring
  have hsum : ∑ i, Real.exp (a * (x i - Real.log U) + b * (y i - Real.log V)) ≤ 1 := by
    calc ∑ i, Real.exp (a * (x i - Real.log U) + b * (y i - Real.log V))
        ≤ ∑ i, (a * Real.exp (x i - Real.log U) + b * Real.exp (y i - Real.log V)) := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          simpa [smul_eq_mul] using
            convexOn_exp.2 (mem_univ (x i - Real.log U)) (mem_univ (y i - Real.log V)) ha hb hab
      _ = a * 1 + b * 1 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hnormU, hnormV]
      _ = 1 := by rw [mul_one, mul_one, hab]
  have key : ∑ i, Real.exp (a * x i + b * y i) ≤ Real.exp L := by
    simp_rw [hsplit, ← Finset.mul_sum]
    calc Real.exp L * ∑ i, Real.exp (a * (x i - Real.log U) + b * (y i - Real.log V))
        ≤ Real.exp L * 1 := mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le
      _ = Real.exp L := mul_one _
  have hpos : 0 < ∑ i, Real.exp (a * x i + b * y i) :=
    Finset.sum_pos (fun i _ ↦ Real.exp_pos _) Finset.univ_nonempty
  calc Real.log (∑ i, Real.exp (a * x i + b * y i)) ≤ Real.log (Real.exp L) :=
        Real.log_le_log hpos key
    _ = a * Real.log U + b * Real.log V := Real.log_exp _

/-- **Example 2.16**: the log-exponential function is not strictly convex,
since `logexp(x + t·1) = logexp(x) + t`. -/
theorem not_strictConvexOn_logSumExp :
    ¬StrictConvexOn ℝ univ (logSumExp : EuclideanSpace ℝ ι → ℝ) := by
  intro h
  have := h.2 (mem_univ 0) (mem_univ onesVector) onesVector_ne_zero.symm
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  rw [smul_zero, zero_add, logSumExp_smul_onesVector] at this
  have h0 : logSumExp (0 : EuclideanSpace ℝ ι) = Real.log (Fintype.card ι) + 0 := by
    simpa using logSumExp_smul_onesVector (ι := ι) 0
  have h1 : logSumExp (onesVector : EuclideanSpace ℝ ι) = Real.log (Fintype.card ι) + 1 := by
    simpa using logSumExp_smul_onesVector (ι := ι) 1
  rw [h0, h1, smul_eq_mul, smul_eq_mul] at this
  linarith

end VecMaxLogExp

/-! ## Example 2.17 -/

section Norms

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A norm on a real vector space in the sense of Example 2.17:
`h(λx) = |λ| h(x)`, `h(x + y) ≤ h(x) + h(y)`, and `h(x) > 0` for `x ≠ 0`. -/
structure IsNormFunction (h : E → ℝ) : Prop where
  smul_eq : ∀ (c : ℝ) (x : E), h (c • x) = |c| * h x
  add_le : ∀ x y : E, h (x + y) ≤ h x + h y
  pos : ∀ x : E, x ≠ 0 → 0 < h x

theorem IsNormFunction.map_zero {h : E → ℝ} (hh : IsNormFunction h) : h 0 = 0 := by
  simpa using hh.smul_eq 0 0

/-- **Example 2.17**: every norm is convex. -/
theorem IsNormFunction.convexOn {h : E → ℝ} (hh : IsNormFunction h) : ConvexOn ℝ univ h := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
  calc h (a • x + b • y) ≤ h (a • x) + h (b • y) := hh.add_le _ _
    _ = a • h x + b • h y := by
        rw [hh.smul_eq, hh.smul_eq, abs_of_nonneg ha, abs_of_nonneg hb, smul_eq_mul, smul_eq_mul]

/-- **Example 2.17**: a norm on a nonzero space is not strictly convex; the
strict inequality fails for `x₀ = 0`, `x₁ ≠ 0`. -/
theorem IsNormFunction.not_strictConvexOn [Nontrivial E] {h : E → ℝ} (hh : IsNormFunction h) :
    ¬StrictConvexOn ℝ univ h := by
  intro hs
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have := hs.2 (mem_univ 0) (mem_univ v) hv.symm (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  rw [smul_zero, zero_add, hh.smul_eq, hh.map_zero, smul_eq_mul, smul_eq_mul] at this
  norm_num at this

/-- **Example 2.17**: closed balls `{x | ‖x - x₀‖ ≤ ρ}` of a norm are convex. -/
theorem IsNormFunction.convex_closedBall {h : E → ℝ} (hh : IsNormFunction h) (x₀ : E) (ρ : ℝ) :
    Convex ℝ {x | h (x - x₀) ≤ ρ} := by
  intro x hx y hy a b ha hb hab
  have he : a • x + b • y - x₀ = a • (x - x₀) + b • (y - x₀) := by
    calc a • x + b • y - x₀ = a • x + b • y - (a + b) • x₀ := by rw [hab, one_smul]
      _ = a • (x - x₀) + b • (y - x₀) := by module
  change h (a • x + b • y - x₀) ≤ ρ
  rw [he]
  have hc := hh.convexOn.2 (mem_univ (x - x₀)) (mem_univ (y - x₀)) ha hb hab
  simp only [smul_eq_mul] at hc
  have hx' : h (x - x₀) ≤ ρ := hx
  have hy' : h (y - x₀) ≤ ρ := hy
  calc h (a • (x - x₀) + b • (y - x₀)) ≤ a * h (x - x₀) + b * h (y - x₀) := hc
    _ ≤ a * ρ + b * ρ :=
        add_le_add (mul_le_mul_of_nonneg_left hx' ha) (mul_le_mul_of_nonneg_left hy' hb)
    _ = ρ := by rw [← add_mul, hab, one_mul]

/-- **Example 2.17**: open balls `{x | ‖x - x₀‖ < ρ}` of a norm are convex. -/
theorem IsNormFunction.convex_ball {h : E → ℝ} (hh : IsNormFunction h) (x₀ : E) (ρ : ℝ) :
    Convex ℝ {x | h (x - x₀) < ρ} := by
  intro x hx y hy a b ha hb hab
  have he : a • x + b • y - x₀ = a • (x - x₀) + b • (y - x₀) := by
    calc a • x + b • y - x₀ = a • x + b • y - (a + b) • x₀ := by rw [hab, one_smul]
      _ = a • (x - x₀) + b • (y - x₀) := by module
  change h (a • x + b • y - x₀) < ρ
  rw [he]
  have hc := hh.convexOn.2 (mem_univ (x - x₀)) (mem_univ (y - x₀)) ha hb hab
  simp only [smul_eq_mul] at hc
  have hx' : h (x - x₀) < ρ := hx
  have hy' : h (y - x₀) < ρ := hy
  rcases ha.eq_or_lt with rfl | ha'
  · simp only [zero_add] at hab
    subst hab
    linarith
  · calc h (a • (x - x₀) + b • (y - x₀)) ≤ a * h (x - x₀) + b * h (y - x₀) := hc
      _ < a * ρ + b * ρ := add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hx' ha')
          (mul_le_mul_of_nonneg_left hy'.le hb)
      _ = ρ := by rw [← add_mul, hab, one_mul]

/-- The norm of a real normed space, in particular the Euclidean norm, is a norm
in the sense of Example 2.17. -/
theorem isNormFunction_norm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    IsNormFunction (fun x : F ↦ ‖x‖) where
  smul_eq c x := by rw [norm_smul, Real.norm_eq_abs]
  add_le x y := norm_add_le x y
  pos x hx := norm_pos_iff.mpr hx

end Norms

section LpNorms

variable {ι : Type*} [Fintype ι]

/-- The `ℓᵖ` norm `(∑ |xⱼ|ᵖ)^(1/p)` of 2(9). -/
def lpNormFunction (p : ℝ) (x : ι → ℝ) : ℝ :=
  (∑ j, |x j| ^ p) ^ (1 / p)

/-- The `ℓ^∞` norm `max |xⱼ|` of 2(9). -/
def linftyNormFunction [Nonempty ι] (x : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun j ↦ |x j|

/-- **Example 2.17**: for `1 ≤ p < ∞`, the `ℓᵖ` norm is a norm. -/
theorem isNormFunction_lpNormFunction {p : ℝ} (hp : 1 ≤ p) :
    IsNormFunction (lpNormFunction (ι := ι) p) where
  smul_eq c x := by
    have hp0 : p ≠ 0 := by linarith
    simp only [lpNormFunction, Pi.smul_apply, smul_eq_mul, abs_mul]
    simp_rw [Real.mul_rpow (abs_nonneg c) (abs_nonneg _)]
    rw [← Finset.mul_sum, Real.mul_rpow (Real.rpow_nonneg (abs_nonneg c) _)
      (Finset.sum_nonneg fun j _ ↦ Real.rpow_nonneg (abs_nonneg _) _), one_div,
      Real.rpow_rpow_inv (abs_nonneg c) hp0]
  add_le x y := Real.Lp_add_le Finset.univ x y hp
  pos x hx := by
    obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx (funext h)
    apply Real.rpow_pos_of_pos
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun i _ ↦ Real.rpow_nonneg (abs_nonneg (x i)) p)
      (Finset.mem_univ j))
    exact Real.rpow_pos_of_pos (abs_pos.mpr hj) p

/-- **Example 2.17**: the `ℓ^∞` norm is a norm. -/
theorem isNormFunction_linftyNormFunction [Nonempty ι] :
    IsNormFunction (linftyNormFunction (ι := ι)) where
  smul_eq c x := by
    simp only [linftyNormFunction, Pi.smul_apply, smul_eq_mul, abs_mul]
    rw [Finset.comp_sup'_eq_sup'_comp Finset.univ_nonempty (fun t ↦ |c| * t)
      fun s t ↦ mul_max_of_nonneg s t (abs_nonneg c)]
    rfl
  add_le x y := by
    simp only [linftyNormFunction, Pi.add_apply]
    refine Finset.sup'_le _ _ fun j _ ↦ (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · exact Finset.le_sup' (fun j ↦ |x j|) (Finset.mem_univ j)
    · exact Finset.le_sup' (fun j ↦ |y j|) (Finset.mem_univ j)
  pos x hx := by
    obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx (funext h)
    exact (abs_pos.mpr hj).trans_le (Finset.le_sup' (fun j ↦ |x j|) (Finset.mem_univ j))

end LpNorms

end RW
