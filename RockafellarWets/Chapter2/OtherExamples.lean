/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 2J: Other examples of convexity

This file formalizes Exercises and Examples 2.51–2.54 of Rockafellar–Wets.

* Exercise 2.51: functions with convex level sets (quasiconvex functions) are
  characterized by `⟨∇f(x₀), x₀ - x₁⟩ ≥ 0` whenever `f(x₁) ≤ f(x₀)`, and have
  positive-semidefinite Hessians at critical points.
* Example 2.52: posynomials become convex after the logarithmic change of
  variables; products of powers of posynomials as well.
* Example 2.53: negative weighted geometric means are proper, lsc and convex.
* Exercise 2.54: sums of the `k` largest eigenvalues are convex on symmetric
  operators (the Ky Fan functions of Chapter 10).
-/

import RockafellarWets.Chapter2.ConvexExamples
import RockafellarWets.Chapter10.KyFanSpectralTrace
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.MeanInequalities

open Set Filter Topology Asymptotics
open scoped InnerProductSpace

noncomputable section

namespace RW

/-! ## Exercise 2.51 -/

section Quasiconvex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasDerivAt_segment {f : E → ℝ} (hf : Differentiable ℝ f) (x₀ v : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ f (x₀ + s • v)) (fderiv ℝ f (x₀ + t • v) v) t := by
  have hpath : HasDerivAt (fun s : ℝ ↦ x₀ + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x₀
  exact (hf (x₀ + t • v)).hasFDerivAt.comp_hasDerivAt t hpath

/-- **Exercise 2.51**: a differentiable `f` has convex level sets `lev≤α f` if
and only if `⟨∇f(x₀), x₀ - x₁⟩ ≥ 0` whenever `f(x₁) ≤ f(x₀)`. -/
theorem convex_levelSets_iff_fderiv {f : E → ℝ} (hf : Differentiable ℝ f) :
    (∀ α : ℝ, Convex ℝ {x | f x ≤ α}) ↔
      ∀ x₀ x₁ : E, f x₁ ≤ f x₀ → 0 ≤ fderiv ℝ f x₀ (x₀ - x₁) := by
  constructor
  · intro hq x₀ x₁ h
    have hseg : ∀ t ∈ Ioc (0 : ℝ) 1, f (x₀ + t • (x₁ - x₀)) ≤ f x₀ := by
      intro t ht
      have hmem := hq (f x₀) (show f x₀ ≤ f x₀ from le_rfl) (show f x₁ ≤ f x₀ from h)
        (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t) ht.1.le (by ring)
      have he : (1 - t) • x₀ + t • x₁ = x₀ + t • (x₁ - x₀) := by module
      rw [he] at hmem
      exact hmem
    have hd := (hasDerivAt_segment hf x₀ (x₁ - x₀) 0).tendsto_slope_zero_right
    simp only [zero_smul, add_zero, zero_add, smul_eq_mul] at hd
    have hle : fderiv ℝ f x₀ (x₁ - x₀) ≤ 0 := by
      refine le_of_tendsto hd ?_
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with t ht
      have := hseg t ⟨ht.1, ht.2.le⟩
      exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht.1.le) (by linarith)
    have hneg : fderiv ℝ f x₀ (x₀ - x₁) = -fderiv ℝ f x₀ (x₁ - x₀) := by
      rw [← map_neg, neg_sub]
    linarith
  · intro h α x₀ hx₀ x₁ hx₁ a b ha hb hab
    change f x₀ ≤ α at hx₀
    change f x₁ ≤ α at hx₁
    change f (a • x₀ + b • x₁) ≤ α
    by_contra hlt
    push_neg at hlt
    set v := x₁ - x₀ with hv
    set g : ℝ → ℝ := fun s ↦ f (x₀ + s • v) with hg
    have hgd : ∀ t, HasDerivAt g (fderiv ℝ f (x₀ + t • v) v) t := hasDerivAt_segment hf x₀ v
    have hgc : Continuous g := continuous_iff_continuousAt.mpr fun t ↦ (hgd t).continuousAt
    have hb' : a • x₀ + b • x₁ = x₀ + b • v := by
      rw [hv]
      have : a = 1 - b := by linarith
      subst this
      module
    have hgτ : α < g b := by simp only [hg]; rw [← hb']; exact hlt
    have hg0 : g 0 ≤ α := by simpa [hg] using hx₀
    have hg1 : g 1 ≤ α := by simpa [hg, hv] using hx₁
    have hderiv0 : ∀ t ∈ Ioo (0 : ℝ) 1, α < g t → fderiv ℝ f (x₀ + t • v) v = 0 := by
      intro t ht hgt
      have hgx0 : g 0 = f x₀ := by simp [hg]
      have hgx1 : g 1 = f x₁ := by simp [hg, hv]
      have e1 := h (x₀ + t • v) x₀ (by rw [← hgx0]; exact hg0.trans hgt.le)
      have e2 := h (x₀ + t • v) x₁ (by rw [← hgx1]; exact hg1.trans hgt.le)
      have d1 : x₀ + t • v - x₀ = t • v := by abel
      have d2 : x₀ + t • v - x₁ = (t - 1) • v := by rw [hv]; module
      rw [d1, map_smul, smul_eq_mul] at e1
      rw [d2, map_smul, smul_eq_mul] at e2
      have p1 : 0 ≤ fderiv ℝ f (x₀ + t • v) v := nonneg_of_mul_nonneg_right
        (by linarith) ht.1
      have p2 : fderiv ℝ f (x₀ + t • v) v ≤ 0 := by
        by_contra hpos
        push_neg at hpos
        have : (t - 1) * fderiv ℝ f (x₀ + t • v) v < 0 :=
          mul_neg_of_neg_of_pos (by linarith [ht.2]) hpos
        linarith
      linarith
    set S := {s : ℝ | s ∈ Icc 0 b ∧ g s ≤ α} with hS
    have hSc : IsClosed S := (isClosed_Icc).inter (isClosed_le hgc continuous_const)
    have hSne : S.Nonempty := ⟨0, ⟨le_rfl, hb⟩, hg0⟩
    have hSb : BddAbove S := ⟨b, fun s hs ↦ hs.1.2⟩
    set s₀ := sSup S with hs₀
    have hs₀S : s₀ ∈ S := hSc.csSup_mem hSne hSb
    have hs₀b : s₀ < b := by
      refine lt_of_le_of_ne hs₀S.1.2 fun he ↦ ?_
      have := hs₀S.2
      rw [he] at this
      linarith
    obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope g (fun t ↦ fderiv ℝ f (x₀ + t • v) v)
      hs₀b hgc.continuousOn (fun t _ ↦ hgd t)
    have hb1 : b ≤ 1 := by linarith
    have hgc' : α < g c := by
      by_contra hle
      push_neg at hle
      have hcS : c ∈ S := ⟨⟨hs₀S.1.1.trans hc.1.le, hc.2.le⟩, hle⟩
      have := le_csSup hSb hcS
      linarith [hc.1]
    have h0 := hderiv0 c ⟨lt_of_le_of_lt hs₀S.1.1 hc.1, lt_of_lt_of_le hc.2 hb1⟩ hgc'
    rw [h0, eq_comm, div_eq_zero_iff] at hcd
    rcases hcd with hcd | hcd
    · have := hs₀S.2
      linarith [sub_eq_zero.mp hcd]
    · linarith

/-- **Exercise 2.51**: if `f` has convex level sets and is twice differentiable
at `x̄` with `∇f(x̄) = 0`, then `∇²f(x̄)` is positive-semidefinite. -/
theorem hessian_nonneg_of_convex_levelSets {f : E → ℝ} (hf : Differentiable ℝ f)
    (hq : ∀ α : ℝ, Convex ℝ {x | f x ≤ α}) {x : E} {f'' : E →L[ℝ] E →L[ℝ] ℝ}
    (h2 : HasFDerivAt (fderiv ℝ f) f'' x) (hgrad : fderiv ℝ f x = 0) (z : E) :
    0 ≤ f'' z z := by
  by_contra hneg
  push_neg at hneg
  set q := f'' z z with hq'
  have hderiv : ∀ y ∈ interior (univ : Set E), HasFDerivAt f (fderiv ℝ f y) y :=
    fun y _ ↦ (hf y).hasFDerivAt
  have h2' : HasFDerivWithinAt (fderiv ℝ f) f'' (interior univ) x := h2.hasFDerivWithinAt
  have key : ∀ w : E, f'' w w = q → ∀ᶠ h in 𝓝[>] (0 : ℝ), f (x + h • w) < f x := by
    intro w hw
    have ht := convex_univ.taylor_approx_two_segment hderiv (mem_univ x) h2' (v := 0) (w := w)
      (by simp) (by simp)
    have hb := ht.def (show (0 : ℝ) < -q / 4 by linarith)
    filter_upwards [hb, self_mem_nhdsWithin] with h hh hpos
    have hpos' : (0 : ℝ) < h := hpos
    simp only [smul_zero, add_zero, hgrad, ContinuousLinearMap.zero_apply, map_zero,
      ContinuousLinearMap.zero_apply, smul_eq_mul, mul_zero, sub_zero, hw, Real.norm_eq_abs,
      abs_pow, abs_of_pos hpos'] at hh
    have := (abs_le.mp hh).2
    nlinarith [sq_nonneg h, mul_pos hpos' hpos']
  have hz := key z rfl
  have hnz := key (-z) (by simp [hq'])
  obtain ⟨h, ⟨h1, h2⟩, hpos⟩ := ((hz.and hnz).and self_mem_nhdsWithin).exists
  set α := max (f (x + h • z)) (f (x + h • -z))
  have hmid := hq α (show f (x + h • z) ≤ α from le_max_left _ _)
    (show f (x + h • -z) ≤ α from le_max_right _ _) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have he : (1 / 2 : ℝ) • (x + h • z) + (1 / 2 : ℝ) • (x + h • -z) = x := by module
  change f ((1 / 2 : ℝ) • (x + h • z) + (1 / 2 : ℝ) • (x + h • -z)) ≤ α at hmid
  rw [he] at hmid
  exact absurd hmid (not_le.mpr (max_lt h1 h2))

end Quasiconvex

/-! ## Example 2.52 -/

section Posynomials

/-- `x ↦ log ∑ᵢ exp(φᵢ(x))` is convex for affine `φᵢ`. -/
theorem convexOn_log_sum_exp_affine {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*}
    [Fintype ι] [Nonempty ι] {φ : ι → E → ℝ}
    (hφ : ∀ i (x y : E) (a b : ℝ), a + b = 1 → φ i (a • x + b • y) = a * φ i x + b * φ i y) :
    ConvexOn ℝ univ (fun x ↦ Real.log (∑ i, Real.exp (φ i x))) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
  simp only [smul_eq_mul]
  set U := ∑ i, Real.exp (φ i x) with hUdef
  set V := ∑ i, Real.exp (φ i y) with hVdef
  have hU : 0 < U := Finset.sum_pos (fun i _ ↦ Real.exp_pos _) Finset.univ_nonempty
  have hV : 0 < V := Finset.sum_pos (fun i _ ↦ Real.exp_pos _) Finset.univ_nonempty
  set L := a * Real.log U + b * Real.log V
  have hnormU : ∑ i, Real.exp (φ i x - Real.log U) = 1 := by
    simp_rw [Real.exp_sub, Real.exp_log hU, ← Finset.sum_div, ← hUdef, div_self hU.ne']
  have hnormV : ∑ i, Real.exp (φ i y - Real.log V) = 1 := by
    simp_rw [Real.exp_sub, Real.exp_log hV, ← Finset.sum_div, ← hVdef, div_self hV.ne']
  have hsplit : ∀ i, Real.exp (φ i (a • x + b • y)) =
      Real.exp L * Real.exp (a * (φ i x - Real.log U) + b * (φ i y - Real.log V)) := by
    intro i
    rw [hφ i x y a b hab, ← Real.exp_add]
    congr 1
    ring
  have hsum : ∑ i, Real.exp (a * (φ i x - Real.log U) + b * (φ i y - Real.log V)) ≤ 1 := by
    calc ∑ i, Real.exp (a * (φ i x - Real.log U) + b * (φ i y - Real.log V))
        ≤ ∑ i, (a * Real.exp (φ i x - Real.log U) + b * Real.exp (φ i y - Real.log V)) := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          simpa [smul_eq_mul] using
            convexOn_exp.2 (mem_univ (φ i x - Real.log U)) (mem_univ (φ i y - Real.log V)) ha hb
              hab
      _ = a * 1 + b * 1 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hnormU, hnormV]
      _ = 1 := by rw [mul_one, mul_one, hab]
  have key : ∑ i, Real.exp (φ i (a • x + b • y)) ≤ Real.exp L := by
    simp_rw [hsplit, ← Finset.mul_sum]
    calc Real.exp L * ∑ i, Real.exp (a * (φ i x - Real.log U) + b * (φ i y - Real.log V))
        ≤ Real.exp L * 1 := mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le
      _ = Real.exp L := mul_one _
  have hpos : 0 < ∑ i, Real.exp (φ i (a • x + b • y)) :=
    Finset.sum_pos (fun i _ ↦ Real.exp_pos _) Finset.univ_nonempty
  calc Real.log (∑ i, Real.exp (φ i (a • x + b • y))) ≤ Real.log (Real.exp L) :=
        Real.log_le_log hpos key
    _ = a * Real.log U + b * Real.log V := Real.log_exp _

variable {n r : ℕ}

/-- A posynomial `g(y) = ∑ᵢ cᵢ y₁^{aᵢ₁} ⋯ yₙ^{aᵢₙ}` (Example 2.52). -/
def posynomial (c : Fin r → ℝ) (a : Fin r → Fin n → ℝ) (y : Fin n → ℝ) : ℝ :=
  ∑ i, c i * ∏ j, y j ^ a i j

/-- After the change of variables `yⱼ = exp xⱼ`, `log g = logexp(Ax + b)` with
`bᵢ = log cᵢ`. -/
theorem log_posynomial_exp {c : Fin r → ℝ} (hc : ∀ i, 0 < c i) (a : Fin r → Fin n → ℝ)
    (x : Fin n → ℝ) :
    Real.log (posynomial c a (fun j ↦ Real.exp (x j))) =
      Real.log (∑ i, Real.exp (∑ j, a i j * x j + Real.log (c i))) := by
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Real.exp_add, Real.exp_log (hc i), Real.exp_sum, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  rw [← Real.exp_mul, mul_comm]

/-- **Example 2.52**: for a posynomial `g` with positive coefficients, the
function `x ↦ log g(exp x₁, …, exp xₙ)` is convex on `ℝⁿ`. -/
theorem convexOn_log_posynomial_exp [NeZero r] {c : Fin r → ℝ} (hc : ∀ i, 0 < c i)
    (a : Fin r → Fin n → ℝ) :
    ConvexOn ℝ univ (fun x : Fin n → ℝ ↦ Real.log (posynomial c a (fun j ↦ Real.exp (x j)))) := by
  have h := convexOn_log_sum_exp_affine (ι := Fin r) (E := Fin n → ℝ)
    (φ := fun i x ↦ ∑ j, a i j * x j + Real.log (c i)) (fun i x y s t hst ↦ by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hsplit : ∑ j, a i j * (s * x j + t * y j) =
          s * ∑ j, a i j * x j + t * ∑ j, a i j * y j := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ ↦ by ring
      rw [hsplit]
      linear_combination (-Real.log (c i)) * hst)
  refine h.congr fun x _ ↦ ?_
  exact (log_posynomial_exp hc a x).symm

/-- **Example 2.52**: for a posynomial of rank `r = 1`, `x ↦ log g(exp x)` is
affine. -/
theorem log_posynomial_exp_rank_one {c : Fin 1 → ℝ} (hc : ∀ i, 0 < c i)
    (a : Fin 1 → Fin n → ℝ) (x : Fin n → ℝ) :
    Real.log (posynomial c a (fun j ↦ Real.exp (x j))) = ∑ j, a 0 j * x j + Real.log (c 0) := by
  rw [log_posynomial_exp hc a x, Fin.sum_univ_one, Real.log_exp]

/-- **Example 2.52**: for `g = g₁^{λ₁} ⋯ g_p^{λ_p}` with posynomials `g_k` and
`λ_k > 0`, the function `x ↦ log g(exp x)` is convex. -/
theorem convexOn_log_prod_posynomial_exp {p : ℕ} {r : Fin p → ℕ} [∀ k, NeZero (r k)]
    {c : ∀ k, Fin (r k) → ℝ} (hc : ∀ k i, 0 < c k i) (a : ∀ k, Fin (r k) → Fin n → ℝ)
    {lam : Fin p → ℝ} (hlam : ∀ k, 0 < lam k) :
    ConvexOn ℝ univ (fun x : Fin n → ℝ ↦
      Real.log (∏ k, posynomial (c k) (a k) (fun j ↦ Real.exp (x j)) ^ lam k)) := by
  have hpos : ∀ k (x : Fin n → ℝ), 0 < posynomial (c k) (a k) (fun j ↦ Real.exp (x j)) := by
    intro k x
    refine Finset.sum_pos (fun i _ ↦ mul_pos (hc k i)
      (Finset.prod_pos fun j _ ↦ Real.rpow_pos_of_pos (Real.exp_pos _) _))
      Finset.univ_nonempty
  have heq : (fun x : Fin n → ℝ ↦
      Real.log (∏ k, posynomial (c k) (a k) (fun j ↦ Real.exp (x j)) ^ lam k)) =
      fun x ↦ ∑ k, lam k * Real.log (posynomial (c k) (a k) (fun j ↦ Real.exp (x j))) := by
    funext x
    rw [Real.log_prod (fun k _ ↦ (Real.rpow_pos_of_pos (hpos k x) _).ne')]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Real.log_rpow (hpos k x)]
  rw [heq]
  induction (Finset.univ : Finset (Fin p)) using Finset.induction_on with
  | empty => exact convexOn_const 0 convex_univ
  | insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    exact ((convexOn_log_posynomial_exp (hc k) (a k)).smul (hlam k).le).add ih

end Posynomials

/-! ## Example 2.53 -/

section GeometricMeans

variable {ι : Type*} [Fintype ι]

/-- Superadditivity of a weighted geometric mean with weights summing to `1`. -/
theorem prod_rpow_add_le {lam : ι → ℝ} (hlam : ∀ j, 0 < lam j) (hsum : ∑ j, lam j = 1)
    {x y : ι → ℝ} (hx : ∀ j, 0 ≤ x j) (hy : ∀ j, 0 ≤ y j) :
    ∏ j, x j ^ lam j + ∏ j, y j ^ lam j ≤ ∏ j, (x j + y j) ^ lam j := by
  by_cases hzero : ∃ j, x j + y j = 0
  · obtain ⟨j, hj⟩ := hzero
    have hxj : x j = 0 := by linarith [hx j, hy j]
    have hyj : y j = 0 := by linarith [hx j, hy j]
    have h0 : ∀ z : ι → ℝ, z j = 0 → ∏ i, z i ^ lam i = 0 := fun z hz ↦
      Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hz, Real.zero_rpow (hlam j).ne'])
    rw [h0 x hxj, h0 y hyj, h0 (fun i ↦ x i + y i) hj, add_zero]
  push_neg at hzero
  have hs : ∀ j, 0 < x j + y j := fun j ↦ lt_of_le_of_ne (add_nonneg (hx j) (hy j)) (hzero j).symm
  set S := ∏ j, (x j + y j) ^ lam j
  have hS : 0 < S := Finset.prod_pos fun j _ ↦ Real.rpow_pos_of_pos (hs j) _
  have hamgm : ∀ z : ι → ℝ, (∀ j, 0 ≤ z j) →
      (∏ j, z j ^ lam j) / S ≤ ∑ j, lam j * (z j / (x j + y j)) := by
    intro z hz
    have h := Real.geom_mean_le_arith_mean_weighted Finset.univ lam (fun j ↦ z j / (x j + y j))
      (fun j _ ↦ (hlam j).le) hsum (fun j _ ↦ div_nonneg (hz j) (hs j).le)
    calc (∏ j, z j ^ lam j) / S = ∏ j, (z j / (x j + y j)) ^ lam j := by
          rw [← Finset.prod_div_distrib]
          exact Finset.prod_congr rfl fun j _ ↦ (Real.div_rpow (hz j) (hs j).le _).symm
      _ ≤ _ := h
  have h1 := hamgm x hx
  have h2 := hamgm y hy
  have hsum' : ∑ j, lam j * (x j / (x j + y j)) + ∑ j, lam j * (y j / (x j + y j)) = 1 := by
    rw [← Finset.sum_add_distrib, ← hsum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    field_simp [(hs j).ne']
  have := add_le_add h1 h2
  rw [hsum', ← add_div, div_le_one hS] at this
  exact this

/-- A weighted geometric mean with positive weights summing to at most `1` is
concave on the nonnegative orthant. -/
theorem concaveOn_prod_rpow {lam : ι → ℝ} (hlam : ∀ j, 0 < lam j) (hsum : ∑ j, lam j ≤ 1) :
    ConcaveOn ℝ {x : ι → ℝ | ∀ j, 0 ≤ x j} (fun x ↦ ∏ j, x j ^ lam j) := by
  classical
  have hconv : Convex ℝ {x : ι → ℝ | ∀ j, 0 ≤ x j} := by
    intro x hx y hy a b ha hb _ j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx j)) (mul_nonneg hb (hy j))
  refine ⟨hconv, fun x hx y hy a b ha hb hab ↦ ?_⟩
  -- weights summing to one after normalizing the extra coordinate
  set μ : Option ι → ℝ := fun o ↦ Option.elim o (1 - ∑ j, lam j) lam
  by_cases heq : ∑ j, lam j = 1
  · have hhom : ∀ (c : ℝ) (z : ι → ℝ), 0 ≤ c → (∀ j, 0 ≤ z j) →
        ∏ j, (c * z j) ^ lam j = c * ∏ j, z j ^ lam j := by
      intro c z hc hz
      simp_rw [Real.mul_rpow hc (hz _)]
      rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_nonneg hc (fun j _ ↦ (hlam j).le), heq,
        Real.rpow_one]
    have hsup := prod_rpow_add_le hlam heq (x := fun j ↦ a * x j) (y := fun j ↦ b * y j)
      (fun j ↦ mul_nonneg ha (hx j)) (fun j ↦ mul_nonneg hb (hy j))
    simp only [smul_eq_mul, Pi.add_apply, Pi.smul_apply]
    rw [hhom a x ha hx, hhom b y hb hy] at hsup
    exact hsup
  · have hlt : ∑ j, lam j < 1 := lt_of_le_of_ne hsum heq
    have hμpos : ∀ o, 0 < μ o := by
      intro o
      cases o with
      | none => simp only [μ, Option.elim_none]; linarith
      | some j => exact hlam j
    have hμsum : ∑ o, μ o = 1 := by
      rw [Fintype.sum_option]
      simp only [μ, Option.elim_none, Option.elim_some]
      ring
    have hext : ∀ z : ι → ℝ, ∏ o, (Option.elim o 1 z : ℝ) ^ μ o = ∏ j, z j ^ lam j := by
      intro z
      rw [Fintype.prod_option]
      simp [μ]
    have hhom : ∀ (c : ℝ) (z : Option ι → ℝ), 0 ≤ c → (∀ o, 0 ≤ z o) →
        ∏ o, (c * z o) ^ μ o = c * ∏ o, z o ^ μ o := by
      intro c z hc hz
      simp_rw [Real.mul_rpow hc (hz _)]
      rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_nonneg hc (fun o _ ↦ (hμpos o).le),
        hμsum, Real.rpow_one]
    have hxo : ∀ o, 0 ≤ (Option.elim o 1 x : ℝ) := fun o ↦ by cases o <;> simp [hx _]
    have hyo : ∀ o, 0 ≤ (Option.elim o 1 y : ℝ) := fun o ↦ by cases o <;> simp [hy _]
    have hsup := prod_rpow_add_le hμpos hμsum (x := fun o ↦ a * Option.elim o 1 x)
      (y := fun o ↦ b * Option.elim o 1 y) (fun o ↦ mul_nonneg ha (hxo o))
      (fun o ↦ mul_nonneg hb (hyo o))
    rw [hhom a _ ha hxo, hhom b _ hb hyo, hext, hext] at hsup
    have key : ∏ o, (a * Option.elim o 1 x + b * Option.elim o 1 y) ^ μ o =
        ∏ j, (a * x j + b * y j) ^ lam j := by
      rw [Fintype.prod_option]
      simp only [Option.elim_none, Option.elim_some, mul_one, hab, Real.one_rpow, one_mul, μ]
    have hsup' : a * ∏ j, x j ^ lam j + b * ∏ j, y j ^ lam j ≤
        ∏ o, (a * Option.elim o 1 x + b * Option.elim o 1 y) ^ μ o := hsup
    rw [key] at hsup'
    simpa [smul_eq_mul] using hsup'

/-- The negative weighted geometric mean of Example 2.53, `∞` off `ℝⁿ₊`. -/
def negWeightedGeomMean (lam : ι → ℝ) (x : ι → ℝ) : EReal :=
  open Classical in if ∀ j, 0 ≤ x j then ((-∏ j, x j ^ lam j : ℝ) : EReal) else ⊤

/-- **Example 2.53**: for weights `λⱼ > 0` with `∑ λⱼ ≤ 1`, the function
`-x₁^{λ₁} ⋯ xₙ^{λₙ}` on `x ≥ 0`, `∞` elsewhere, is proper, lsc and convex. -/
theorem negWeightedGeomMean_proper_lsc_convex {lam : ι → ℝ} (hlam : ∀ j, 0 < lam j)
    (hsum : ∑ j, lam j ≤ 1) :
    IsProper (negWeightedGeomMean lam) ∧ LowerSemicontinuous (negWeightedGeomMean lam) ∧
      IsConvexRelative univ (negWeightedGeomMean lam) := by
  classical
  set K := {x : ι → ℝ | ∀ j, 0 ≤ x j} with hK
  have hKc : Convex ℝ K := (concaveOn_prod_rpow hlam hsum).1
  have h0 : ∀ j, 0 ≤ (0 : ι → ℝ) j := fun j ↦ le_refl 0
  refine ⟨⟨⟨0, by rw [negWeightedGeomMean, if_pos h0]; exact EReal.coe_lt_top _⟩,
    fun x ↦ ?_⟩, ?_, ?_⟩
  · by_cases hx : ∀ j, 0 ≤ x j
    · rw [negWeightedGeomMean, if_pos hx]; exact EReal.bot_lt_coe _
    · rw [negWeightedGeomMean, if_neg hx]; exact bot_lt_top
  · apply lowerSemicontinuous_of_isClosed_epigraph_ereal
    have hepi : epigraph (negWeightedGeomMean lam) =
        {p : (ι → ℝ) × ℝ | ∀ j, 0 ≤ p.1 j} ∩ {p | -∏ j, p.1 j ^ lam j ≤ p.2} := by
      ext ⟨x, α⟩
      rw [mem_epigraph_iff]
      simp only [mem_inter_iff, mem_setOf_eq]
      unfold negWeightedGeomMean
      by_cases hx : ∀ j, 0 ≤ x j
      · rw [if_pos hx, EReal.coe_le_coe_iff]
        exact ⟨fun h ↦ ⟨hx, h⟩, fun h ↦ h.2⟩
      · rw [if_neg hx]
        exact ⟨fun h ↦ absurd h (not_le.mpr (EReal.coe_lt_top α)), fun h ↦ absurd h.1 hx⟩
    rw [hepi]
    have hcont : Continuous fun p : (ι → ℝ) × ℝ ↦ ∏ j, p.1 j ^ lam j :=
      continuous_finset_prod _ fun j _ ↦
        (Real.continuous_rpow_const (hlam j).le).comp ((continuous_apply j).comp continuous_fst)
    refine IsClosed.inter ?_ (isClosed_le hcont.neg continuous_snd)
    have : {p : (ι → ℝ) × ℝ | ∀ j, 0 ≤ p.1 j} = ⋂ j, {p | 0 ≤ p.1 j} := by
      ext p
      simp
    rw [this]
    exact isClosed_iInter fun j ↦ isClosed_le continuous_const
      ((continuous_apply j).comp continuous_fst)
  · have hneg : ConvexOn ℝ K (fun x ↦ -∏ j, x j ^ lam j) := (concaveOn_prod_rpow hlam hsum).neg
    have h := (isConvexRelative_iff_extension hKc _).mp ((isConvexRelative_coe_iff hKc _).mpr hneg)
    refine h.congr convex_univ fun x _ ↦ ?_
    by_cases hx : ∀ j, 0 ≤ x j <;> simp [negWeightedGeomMean, hK, hx]

end GeometricMeans

/-! ## Exercise 2.54 -/

section Eigenvalues

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Exercise 2.54**: for `k ≤ n`, the sum `Λ_k(A)` of the `k` largest
eigenvalues (in decreasing order, with multiplicity) is a convex function of the
symmetric operator `A`; it is the Ky Fan function of Chapter 10. -/
theorem convexOn_sum_largest_eigenvalues {k : ℕ} (hk : k ≤ Module.finrank ℝ E) :
    Convex ℝ {A : E →L[ℝ] E | A.toLinearMap.IsSymmetric} ∧
      ConvexOn ℝ {A : E →L[ℝ] E | A.toLinearMap.IsSymmetric} (kyFanValue k) ∧
      ∀ (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric),
        Antitone (hA.eigenvalues rfl) ∧
          kyFanValue k A =
            ∑ j ∈ spectralInitialIndices (Module.finrank ℝ E) k, hA.eigenvalues rfl j := by
  have hS : Convex ℝ {A : E →L[ℝ] E | A.toLinearMap.IsSymmetric} := by
    intro A hA B hB a b _ _ _
    simp only [mem_setOf_eq, ContinuousLinearMap.coe_add, ContinuousLinearMap.coe_smul] at hA hB ⊢
    exact (LinearMap.IsSymmetric.smul (c := a) (by simp) hA).add
      (LinearMap.IsSymmetric.smul (c := b) (by simp) hB)
  exact ⟨hS, (convexOn_kyFanValue k).subset (subset_univ _) hS, fun A hA ↦
    ⟨hA.eigenvalues_antitone rfl, kyFanValue_eq_eigenvalue_sum hk A hA⟩⟩

end Eigenvalues

end RW
