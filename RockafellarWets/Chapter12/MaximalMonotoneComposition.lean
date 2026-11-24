/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: Preservation of maximal monotonicity

Theorem 12.43, Corollary 12.44, Example 12.45, Exercise 12.46 and Example 12.47.

For `T(x) = A* S(Ax + a)` the proof follows the book's Yosida argument.  For
`λ > 0` the mapping `x ↦ A* Sλ(Ax + a)`, with `Sλ` the Yosida regularization
(12.13), is single-valued, continuous and monotone, hence maximal monotone by
12.7, so `z = xλ + A* yλ` is solvable with `yλ = Sλ(Axλ + a)`, that is
`yλ ∈ S(uλ)` for `uλ = Axλ + a - λyλ`.  Testing monotonicity of `S` against a
graph point over `s₀ = Ax₀ + a ∈ rint(dom S)` bounds `A* yλ`.  If the `yλ` stay
bounded along a sequence `λν ↘ 0`, a cluster point solves `z ∈ (I + T)(x)`, and
`T` is maximal by 12.12.  Otherwise a normalized cluster point `ỹ` of `yν`
satisfies `A* ỹ = 0` and `⟪ỹ, s - s₀⟫ ≤ 0` on `dom S`, so `⟪ỹ, ·⟫` is constant on
`dom S` by the relative interior condition.

The book then reaches a contradiction after reducing, without loss of
generality, to the case where `dom S` and `rge A` span the whole space.  That
reduction is avoided here: since every `uν` lies in `dom S`, the identity
`λν yν = (Axν + a - s₀) + (s₀ - uν)` shows `⟪ỹ, yν⟫ = 0` for every `ν`, which is
incompatible with `yν/|yν| → ỹ ≠ 0`.

The relative interior enters only through the property that a linear
functional maximized over `dom S` at `s₀` is constant on `dom S`
(`NoNontrivialSupport`), which every relative-interior point has.  The general
theorems are stated with this property, which makes products easy to handle:
12.44 is 12.43 for the diagonal map into the Euclidean product
`WithLp 2 (E × E)`, 12.46 composes with `x₁ ↦ (x₁, x̄₂)` and 12.47 with
`τ ↦ x + τw`.
-/

import RockafellarWets.Chapter12.MonotoneDomains
import RockafellarWets.Chapter12.OneDimensionalMonotonicity
import RockafellarWets.Chapter12.YosidaRegularization
import RockafellarWets.Chapter6.ProductCones

open Bornology Filter Metric Set Topology Function
open scoped InnerProductSpace Pointwise

namespace RW

section Support

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- `C` has no non-trivial supporting hyperplane at `s₀ ∈ C`: a linear
functional maximized over `C` at `s₀` is constant on `C`.  Relative-interior
points have this property (Rockafellar, *Convex Analysis*, Theorem 11.6). -/
def NoNontrivialSupport (C : Set F) (s₀ : F) : Prop :=
  s₀ ∈ C ∧ ∀ y : F, (∀ s ∈ C, ⟪y, s - s₀⟫_ℝ ≤ 0) → ∀ s ∈ C, ⟪y, s - s₀⟫_ℝ = 0

/-- Relative-interior points admit no non-trivial supporting hyperplane. -/
theorem noNontrivialSupport_of_mem_intrinsicInterior {C : Set F} {s₀ : F}
    (h : s₀ ∈ intrinsicInterior ℝ C) : NoNontrivialSupport C s₀ := by
  refine ⟨intrinsicInterior_subset h, fun y hy s hs ↦ le_antisymm (hy s hs) ?_⟩
  obtain ⟨ε, hε, hmem⟩ := exists_pos_add_smul_sub_mem_of_mem_intrinsicInterior h hs
  have h1 := hy _ hmem
  rw [add_sub_cancel_left, real_inner_smul_right, ← neg_sub s s₀, inner_neg_right] at h1
  nlinarith

end Support

section Bound

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The a priori bound of 12.43: from `0 ≤ ⟪p - q, c - p⟫ - λ⟪y - w₀, y⟫` with
`0 ≤ λ ≤ 1` one gets `|p| ≤ |c| + |q| + |q||c| + |w₀|² + 1`. -/
theorem norm_le_of_inner_sub_nonneg {p q c : E} {y w₀ : F} {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlam1 : lam ≤ 1) (hm : 0 ≤ ⟪p - q, c - p⟫_ℝ - lam * ⟪y - w₀, y⟫_ℝ) :
    ‖p‖ ≤ ‖c‖ + ‖q‖ + ‖q‖ * ‖c‖ + ‖w₀‖ ^ 2 + 1 := by
  have e3 : ⟪p - q, c - p⟫_ℝ = ⟪p, c⟫_ℝ - ‖p‖ ^ 2 - ⟪q, c⟫_ℝ + ⟪q, p⟫_ℝ := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_self_eq_norm_sq]
    ring
  have e4 : ⟪y - w₀, y⟫_ℝ = ‖y‖ ^ 2 - ⟪w₀, y⟫_ℝ := by
    rw [inner_sub_left, real_inner_self_eq_norm_sq]
  rw [e3, e4] at hm
  have b1 := real_inner_le_norm p c
  have b2 : -⟪q, c⟫_ℝ ≤ ‖q‖ * ‖c‖ := by
    have := abs_real_inner_le_norm q c
    linarith [neg_abs_le ⟪q, c⟫_ℝ]
  have b3 := real_inner_le_norm q p
  have b4 := mul_le_mul_of_nonneg_left (real_inner_le_norm w₀ y) hlam0
  have b5 : 0 ≤ lam * (‖y‖ - ‖w₀‖ / 2) ^ 2 := mul_nonneg hlam0 (sq_nonneg _)
  have b6 : lam * ‖w₀‖ ^ 2 ≤ ‖w₀‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_right hlam1 (sq_nonneg ‖w₀‖)
    linarith
  have key : ‖p‖ ^ 2 ≤ (‖c‖ + ‖q‖) * ‖p‖ + ‖q‖ * ‖c‖ + ‖w₀‖ ^ 2 / 4 := by
    nlinarith
  by_contra hcon
  push_neg at hcon
  have hqc := mul_nonneg (norm_nonneg q) (norm_nonneg c)
  have hK1 : 1 ≤ ‖c‖ + ‖q‖ + ‖q‖ * ‖c‖ + ‖w₀‖ ^ 2 + 1 := by
    nlinarith [norm_nonneg c, norm_nonneg q, sq_nonneg ‖w₀‖]
  have hp1 : 1 ≤ ‖p‖ := hK1.trans hcon.le
  have h1 : (‖c‖ + ‖q‖ + ‖q‖ * ‖c‖ + ‖w₀‖ ^ 2 + 1) * ‖p‖ < ‖p‖ * ‖p‖ :=
    mul_lt_mul_of_pos_right hcon (by linarith)
  have h2 : (‖q‖ * ‖c‖ + ‖w₀‖ ^ 2 + 1) * 1 ≤ (‖q‖ * ‖c‖ + ‖w₀‖ ^ 2 + 1) * ‖p‖ :=
    mul_le_mul_of_nonneg_left hp1 (by positivity)
  nlinarith [sq_nonneg ‖w₀‖]

end Bound

section Composition

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The regularized equation of 12.43: for `λ > 0` there are `x` and `y` with
`y ∈ S(Ax + a - λy)` and `x + A*y = z`, namely `y = Sλ(Ax + a)` for the Yosida
regularization `Sλ` and `x` the resolvent of the maximal monotone mapping
`x ↦ A* Sλ(Ax + a)` at `z`. -/
theorem SvMaximalMonotone.exists_regularized_adjointComp {S : F → Set F}
    (hS : SvMaximalMonotone S) (A : E →L[ℝ] F) (a : F) {lam : ℝ} (hlam : 0 < lam) (z : E) :
    ∃ (x : E) (y : F), y ∈ S (A x + a - lam • y) ∧ x + A.adjoint y = z := by
  set G : E → E := fun x ↦ A.adjoint (yosidaMap S lam (A x + a)) with hG
  have hYmono : SvMonotone (fun s ↦ ({yosidaMap S lam s} : Set F)) := by
    rw [← hS.svYosida_eq_fun hlam]
    exact hS.1.svMonotone_svYosida hlam.le
  have hGmono : SvMonotone (fun x ↦ ({G x} : Set E)) := by
    have h := hYmono.adjointComp A a
    have e : svAdjointComp A (fun s ↦ ({yosidaMap S lam s} : Set F)) a =
        fun x ↦ ({G x} : Set E) := by
      funext x
      simp only [svAdjointComp, image_singleton, hG]
    rwa [e] at h
  have hGcont : Continuous G :=
    A.adjoint.continuous.comp ((hS.lipschitzWith_yosidaMap hlam).continuous.comp
      (A.continuous.add continuous_const))
  have hGmax := svMaximalMonotone_singleton_of_continuous hGcont hGmono
  set x := resolventMap (fun x ↦ ({G x} : Set E)) 1 z with hx
  obtain ⟨v, hv, hxv⟩ := (hGmax.resolventMap_eq_iff one_pos).1 hx.symm
  rw [mem_singleton_iff] at hv
  obtain ⟨hs, hy⟩ := (hS.resolventMap_yosidaMap_eq_iff hlam (z := A x + a)).1 ⟨rfl, rfl⟩
  refine ⟨x, yosidaMap S lam (A x + a), ?_, ?_⟩
  · have e : A x + a - lam • yosidaMap S lam (A x + a) = resolventMap S lam (A x + a) :=
      sub_eq_iff_eq_add.2 hs
    rw [e]
    exact hy
  · rw [hv, one_smul] at hxv
    exact hxv

/-- **Theorem 12.43**, general form: `T(x) = A* S(Ax + a)` is maximal monotone
when `Ax₀ + a` is a point of `dom S` at which `dom S` has no non-trivial
supporting hyperplane. -/
theorem SvMaximalMonotone.svMaximalMonotone_svAdjointComp_of_noNontrivialSupport
    {S : F → Set F} (hS : SvMaximalMonotone S) (A : E →L[ℝ] F) (a : F) {x₀ : E}
    (h₀ : NoNontrivialSupport (svDom S) (A x₀ + a)) :
    SvMaximalMonotone (svAdjointComp A S a) := by
  have hmono : SvMonotone (svAdjointComp A S a) := hS.1.adjointComp A a
  refine svMaximalMonotone_of_svDom_svResolvent hmono one_pos (eq_univ_of_forall fun z ↦ ?_)
  obtain ⟨⟨w₀, hw₀⟩, hsupp⟩ := h₀
  set lam : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1) with hlamdef
  have hlampos : ∀ n, 0 < lam n := fun n ↦ by positivity
  have hlam1 : ∀ n, lam n ≤ 1 := fun n ↦ by
    rw [hlamdef, div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hlim : Tendsto lam atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose x y hy hxy using fun n ↦ hS.exists_regularized_adjointComp A a (hlampos n) z
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = ‖z - x₀‖ + ‖A.adjoint w₀‖ + ‖A.adjoint w₀‖ * ‖z - x₀‖ +
      ‖w₀‖ ^ 2 + 1 := ⟨_, rfl⟩
  -- the bound on `A* yν`
  have hp : ∀ n, ‖A.adjoint (y n)‖ ≤ K := by
    intro n
    have hm := hS.1 hw₀ (hy n)
    have e1 : A (x n) + a - lam n • y n - (A x₀ + a) = A (x n - x₀) - lam n • y n := by
      rw [map_sub]
      abel
    have e2 : x n - x₀ = (z - x₀) - A.adjoint (y n) := by
      rw [← hxy n]
      abel
    rw [e1, inner_sub_right, ← ContinuousLinearMap.adjoint_inner_left, map_sub, e2,
      real_inner_smul_right] at hm
    rw [hK]
    exact norm_le_of_inner_sub_nonneg (hlampos n).le (hlam1 n) hm
  -- bounds on `xν` and `uν = Axν + a - λν yν`
  have hxb : ∀ n, ‖x n‖ ≤ ‖z‖ + K := by
    intro n
    have e : x n = z - A.adjoint (y n) := eq_sub_of_add_eq (hxy n)
    rw [e]
    calc ‖z - A.adjoint (y n)‖ ≤ ‖z‖ + ‖A.adjoint (y n)‖ := norm_sub_le _ _
      _ ≤ ‖z‖ + K := by linarith [hp n]
  have hu_res : ∀ n, resolventMap S (lam n) (A (x n) + a) = A (x n) + a - lam n • y n :=
    fun n ↦ (hS.resolventMap_eq_iff (hlampos n)).2 ⟨y n, hy n, by rw [sub_add_cancel]⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ‖A‖ * (‖z‖ + K + ‖x₀‖) + ‖w₀‖ := ⟨_, rfl⟩
  have hub : ∀ n, A (x n) + a - lam n • y n ∈ closedBall (A x₀ + a) M := by
    intro n
    rw [mem_closedBall, dist_eq_norm]
    have h := hS.norm_resolventMap_sub_le (hlampos n) (A (x n) + a) hw₀
    rw [hu_res] at h
    have e : A (x n) + a - (A x₀ + a) = A (x n - x₀) := by
      rw [map_sub]
      abel
    have hA : ‖A (x n - x₀)‖ ≤ ‖A‖ * (‖z‖ + K + ‖x₀‖) := by
      refine (A.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg A))
      calc ‖x n - x₀‖ ≤ ‖x n‖ + ‖x₀‖ := norm_sub_le _ _
        _ ≤ ‖z‖ + K + ‖x₀‖ := by linarith [hxb n]
    have hw : lam n * ‖w₀‖ ≤ ‖w₀‖ := by
      have := mul_le_mul_of_nonneg_right (hlam1 n) (norm_nonneg w₀)
      linarith
    rw [e] at h
    rw [hM]
    linarith
  by_cases hbdd : ∃ R, ∃ᶠ n in atTop, ‖y n‖ ≤ R
  · -- bounded case: a cluster point solves the equation
    obtain ⟨R, hR⟩ := hbdd
    obtain ⟨ybar, -, φ, hφ, hyφ⟩ := tendsto_subseq_of_frequently_bounded
      (isBounded_closedBall (x := (0 : F)) (r := R))
      (hR.mono fun n hn ↦ mem_closedBall_zero_iff.2 hn)
    set xbar := z - A.adjoint ybar with hxbar
    have hxφ : Tendsto (fun n ↦ x (φ n)) atTop (𝓝 xbar) := by
      have e : (fun n ↦ x (φ n)) = fun n ↦ z - A.adjoint (y (φ n)) :=
        funext fun n ↦ eq_sub_of_add_eq (hxy (φ n))
      rw [e]
      exact tendsto_const_nhds.sub ((A.adjoint.continuous.tendsto ybar).comp hyφ)
    have huφ : Tendsto (fun n ↦ A (x (φ n)) + a - lam (φ n) • y (φ n)) atTop
        (𝓝 (A xbar + a)) := by
      have h1 : Tendsto (fun n ↦ A (x (φ n)) + a - lam (φ n) • y (φ n)) atTop
          (𝓝 (A xbar + a - (0 : ℝ) • ybar)) :=
        (((A.continuous.tendsto xbar).comp hxφ).add tendsto_const_nhds).sub
          ((hlim.comp hφ.tendsto_atTop).smul hyφ)
      rwa [zero_smul, sub_zero] at h1
    have hmem : ybar ∈ S (A xbar + a) :=
      hS.isClosed_svGraph.mem_of_tendsto (huφ.prodMk_nhds hyφ)
        (Eventually.of_forall fun n ↦ hy (φ n))
    exact ⟨xbar, mem_svResolvent.2 ⟨A.adjoint ybar, ⟨ybar, hmem, rfl⟩,
      by rw [one_smul, hxbar, sub_add_cancel]⟩⟩
  · -- unbounded case: contradiction with the relative interior condition
    exfalso
    push_neg at hbdd
    have hnorm : Tendsto (fun n ↦ ‖y n‖) atTop atTop :=
      tendsto_atTop.2 fun R ↦ (hbdd R).mono fun n hn ↦ hn.le
    obtain ⟨φ, yt, hφ, hyt1, hyt⟩ := exists_subseq_tendsto_normalize hnorm
    obtain ⟨ubar, -, ψ, hψ, huψ⟩ := tendsto_subseq_of_bounded
      (isBounded_closedBall (x := A x₀ + a) (r := M)) (fun n ↦ hub (φ n))
    set ν := φ ∘ ψ with hνdef
    have hν : StrictMono ν := hφ.comp hψ
    have hytν : Tendsto (fun n ↦ ‖y (ν n)‖⁻¹ • y (ν n)) atTop (𝓝 yt) :=
      hyt.comp hψ.tendsto_atTop
    have hnormν : Tendsto (fun n ↦ ‖y (ν n)‖) atTop atTop := hnorm.comp hν.tendsto_atTop
    have huν : Tendsto (fun n ↦ A (x (ν n)) + a - lam (ν n) • y (ν n)) atTop (𝓝 ubar) := huψ
    -- `A* ỹ = 0`
    have hAyt : A.adjoint yt = 0 := by
      have h1 : Tendsto (fun n ↦ A.adjoint (‖y (ν n)‖⁻¹ • y (ν n))) atTop (𝓝 (A.adjoint yt)) :=
        (A.adjoint.continuous.tendsto yt).comp hytν
      have h2 : Tendsto (fun n ↦ A.adjoint (‖y (ν n)‖⁻¹ • y (ν n))) atTop (𝓝 0) := by
        have hc0 : Tendsto (fun n ↦ ‖y (ν n)‖⁻¹) atTop (𝓝 0) :=
          tendsto_inv_atTop_zero.comp hnormν
        refine squeeze_zero_norm (fun n ↦ ?_) (by simpa using hc0.mul_const K)
        rw [map_smul, norm_smul, norm_inv, norm_norm]
        exact mul_le_mul_of_nonneg_left (hp (ν n)) (inv_nonneg.2 (norm_nonneg _))
      exact tendsto_nhds_unique h1 h2
    -- `⟪ỹ, uν - s₀⟫ = -λν⟪ỹ, yν⟫`
    have he : ∀ n, ⟪yt, A (x n) + a - lam n • y n - (A x₀ + a)⟫_ℝ = -(lam n * ⟪yt, y n⟫_ℝ) := by
      intro n
      have e1 : A (x n) + a - lam n • y n - (A x₀ + a) = A (x n - x₀) - lam n • y n := by
        rw [map_sub]
        abel
      rw [e1, inner_sub_right, ← ContinuousLinearMap.adjoint_inner_left, hAyt, inner_zero_left,
        real_inner_smul_right, zero_sub]
    have hpos : ∀ᶠ n in atTop, 0 < ⟪yt, ‖y (ν n)‖⁻¹ • y (ν n)⟫_ℝ := by
      have h1 : Tendsto (fun n ↦ ⟪yt, ‖y (ν n)‖⁻¹ • y (ν n)⟫_ℝ) atTop (𝓝 ⟪yt, yt⟫_ℝ) :=
        tendsto_const_nhds.inner hytν
      rw [real_inner_self_eq_norm_sq, hyt1, one_pow] at h1
      exact h1.eventually (lt_mem_nhds one_pos)
    -- every `s ∈ dom S` satisfies `⟪ỹ, s - s₀⟫ ≤ 0`
    have hdom : ∀ s ∈ svDom S, ⟪yt, s - (A x₀ + a)⟫_ℝ ≤ 0 := by
      have hb : ∀ s ∈ svDom S, ⟪yt, s - ubar⟫_ℝ ≤ 0 := by
        rintro s ⟨w, hw⟩
        exact inner_nonpos_of_inner_sub_nonneg
          (x := fun n ↦ A (x (ν n)) + a - lam (ν n) • y (ν n)) (v := fun n ↦ y (ν n))
          (a := fun _ ↦ s) (b := fun _ ↦ w) (Eventually.of_forall fun n ↦ hS.1 hw (hy (ν n)))
          huν tendsto_const_nhds tendsto_const_nhds hnormν hytν
      have hc' : ⟪yt, ubar - (A x₀ + a)⟫_ℝ ≤ 0 := by
        refine le_of_tendsto (tendsto_const_nhds.inner (huν.sub tendsto_const_nhds)) ?_
        filter_upwards [hpos] with n hn
        rw [he, neg_nonpos]
        rw [real_inner_smul_right] at hn
        exact (mul_pos (hlampos (ν n))
          (pos_of_mul_pos_right hn (inv_nonneg.2 (norm_nonneg _)))).le
      intro s hs
      have e : s - (A x₀ + a) = (s - ubar) + (ubar - (A x₀ + a)) := by abel
      rw [e, inner_add_right]
      linarith [hb s hs]
    have hzero := hsupp yt hdom
    -- hence `⟪ỹ, yν⟫ = 0` for every `ν`, contradicting `yν/|yν| → ỹ`
    obtain ⟨n, hn⟩ := hpos.exists
    have h1 := he (ν n)
    rw [hzero _ ⟨y (ν n), hy (ν n)⟩] at h1
    have h2 : ⟪yt, y (ν n)⟫_ℝ = 0 := by
      have := mul_eq_zero.1 (neg_eq_zero.1 h1.symm)
      exact this.resolve_left (hlampos (ν n)).ne'
    rw [real_inner_smul_right, h2, mul_zero] at hn
    exact lt_irrefl 0 hn

/-- **Theorem 12.43 (maximal monotonicity under composition).**  If `S` is
maximal monotone and `(rge A + a) ∩ rint(dom S) ≠ ∅`, then `T(x) = A* S(Ax + a)`
is maximal monotone. -/
theorem SvMaximalMonotone.svMaximalMonotone_svAdjointComp {S : F → Set F}
    (hS : SvMaximalMonotone S) (A : E →L[ℝ] F) (a : F)
    (h : (range (fun x ↦ A x + a) ∩ intrinsicInterior ℝ (svDom S)).Nonempty) :
    SvMaximalMonotone (svAdjointComp A S a) := by
  obtain ⟨_, ⟨x₀, rfl⟩, hx₀⟩ := h
  exact hS.svMaximalMonotone_svAdjointComp_of_noNontrivialSupport A a
    (noNontrivialSupport_of_mem_intrinsicInterior hx₀)

end Composition

/-- Extensionality for the Euclidean product. -/
theorem withLp_prod_ext {E F : Type*} {p q : WithLp 2 (E × F)} (h₁ : p.fst = q.fst)
    (h₂ : p.snd = q.snd) : p = q :=
  WithLp.ofLp_injective 2 (Prod.ext h₁ h₂)

section Products

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The product of maximal monotone mappings, `(x₁, x₂) ↦ T₁(x₁) × T₂(x₂)` on the
Euclidean product, is maximal monotone. -/
theorem SvMaximalMonotone.l2Prod {T₁ : E → Set E} {T₂ : F → Set F}
    (h₁ : SvMaximalMonotone T₁) (h₂ : SvMaximalMonotone T₂) :
    SvMaximalMonotone (fun p : WithLp 2 (E × F) ↦ l2ProdSet (T₁ p.fst) (T₂ p.snd)) := by
  have hmono : SvMonotone (fun p : WithLp 2 (E × F) ↦ l2ProdSet (T₁ p.fst) (T₂ p.snd)) := by
    intro p₀ q₀ h₀ p₁ q₁ h₁'
    rw [WithLp.prod_inner_apply]
    simp only [WithLp.ofLp_fst, WithLp.ofLp_snd, WithLp.sub_fst, WithLp.sub_snd]
    exact add_nonneg (h₁.1 h₀.1 h₁'.1) (h₂.1 h₀.2 h₁'.2)
  refine svMaximalMonotone_of_svDom_svResolvent hmono one_pos (eq_univ_of_forall fun z ↦ ?_)
  refine ⟨WithLp.toLp 2 (resolventMap T₁ 1 z.fst, resolventMap T₂ 1 z.snd), ?_⟩
  rw [mem_svResolvent]
  refine ⟨WithLp.toLp 2 (z.fst - resolventMap T₁ 1 z.fst, z.snd - resolventMap T₂ 1 z.snd),
    ⟨?_, ?_⟩, ?_⟩
  · simpa using h₁.inv_smul_sub_resolventMap_mem one_pos z.fst
  · simpa using h₂.inv_smul_sub_resolventMap_mem one_pos z.snd
  · refine withLp_prod_ext ?_ ?_ <;> simp

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] in
/-- The domain of the product mapping is the product of the domains. -/
theorem svDom_l2Prod (T₁ : E → Set E) (T₂ : F → Set F) :
    svDom (fun p : WithLp 2 (E × F) ↦ l2ProdSet (T₁ p.fst) (T₂ p.snd)) =
      l2ProdSet (svDom T₁) (svDom T₂) := by
  ext p
  constructor
  · rintro ⟨q, hq₁, hq₂⟩
    exact ⟨⟨_, hq₁⟩, ⟨_, hq₂⟩⟩
  · rintro ⟨⟨v₁, hv₁⟩, ⟨v₂, hv₂⟩⟩
    exact ⟨WithLp.toLp 2 (v₁, v₂), hv₁, hv₂⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The relative interior condition passes to products. -/
theorem noNontrivialSupport_l2ProdSet {C : Set E} {D : Set F} {c : E} {d : F}
    (hC : NoNontrivialSupport C c) (hD : NoNontrivialSupport D d) :
    NoNontrivialSupport (l2ProdSet C D) (WithLp.toLp 2 (c, d)) := by
  refine ⟨⟨hC.1, hD.1⟩, fun y hy s hs ↦ ?_⟩
  have hfst : ∀ s₁ ∈ C, ⟪y.fst, s₁ - c⟫_ℝ ≤ 0 := by
    intro s₁ hs₁
    have h := hy (WithLp.toLp 2 (s₁, d)) ⟨hs₁, hD.1⟩
    rw [WithLp.prod_inner_apply] at h
    simpa using h
  have hsnd : ∀ s₂ ∈ D, ⟪y.snd, s₂ - d⟫_ℝ ≤ 0 := by
    intro s₂ hs₂
    have h := hy (WithLp.toLp 2 (c, s₂)) ⟨hC.1, hs₂⟩
    rw [WithLp.prod_inner_apply] at h
    simpa using h
  rw [WithLp.prod_inner_apply]
  have h₁ := hC.2 _ hfst _ hs.1
  have h₂ := hD.2 _ hsnd _ hs.2
  simp only [WithLp.ofLp_fst, WithLp.ofLp_snd, WithLp.sub_fst, WithLp.sub_snd,
    WithLp.toLp_fst, WithLp.toLp_snd]
  rw [h₁, h₂, add_zero]

/-- The diagonal map `x ↦ (x, x)` into the Euclidean product. -/
noncomputable def diagL2 : E →L[ℝ] WithLp 2 (E × E) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.id ℝ E).prod (ContinuousLinearMap.id ℝ E))

omit [FiniteDimensional ℝ E] in
@[simp]
theorem diagL2_apply (x : E) : diagL2 x = WithLp.toLp 2 (x, x) := rfl

/-- The adjoint of the diagonal map adds the components. -/
theorem diagL2_adjoint_apply (q : WithLp 2 (E × E)) :
    (diagL2 (E := E)).adjoint q = q.fst + q.snd := by
  refine ext_inner_right ℝ fun x ↦ ?_
  rw [ContinuousLinearMap.adjoint_inner_left, diagL2_apply, WithLp.prod_inner_apply,
    inner_add_left]
  simp

/-- The sum of two mappings is the composition of their product with the
diagonal map, in the sense of 12.43. -/
theorem svAdjointComp_diagL2 (T₁ T₂ : E → Set E) :
    svAdjointComp diagL2 (fun p : WithLp 2 (E × E) ↦ l2ProdSet (T₁ p.fst) (T₂ p.snd)) 0 =
      svAdd T₁ T₂ := by
  funext x
  ext v
  rw [mem_svAdjointComp, mem_svAdd]
  constructor
  · rintro ⟨q, ⟨hq₁, hq₂⟩, rfl⟩
    refine ⟨q.fst, ?_, q.snd, ?_, (diagL2_adjoint_apply q).symm⟩
    · simpa using hq₁
    · simpa using hq₂
  · rintro ⟨v₁, hv₁, v₂, hv₂, rfl⟩
    refine ⟨WithLp.toLp 2 (v₁, v₂), ⟨?_, ?_⟩, ?_⟩
    · simpa using hv₁
    · simpa using hv₂
    · rw [diagL2_adjoint_apply]
      rfl

/-- **Corollary 12.44**, general form: the sum of maximal monotone mappings is
maximal monotone when some point of both domains admits no non-trivial
supporting hyperplane to either domain. -/
theorem SvMaximalMonotone.svMaximalMonotone_svAdd_of_noNontrivialSupport
    {T₁ T₂ : E → Set E} (h₁ : SvMaximalMonotone T₁) (h₂ : SvMaximalMonotone T₂) {x₀ : E}
    (hx₁ : NoNontrivialSupport (svDom T₁) x₀) (hx₂ : NoNontrivialSupport (svDom T₂) x₀) :
    SvMaximalMonotone (svAdd T₁ T₂) := by
  rw [← svAdjointComp_diagL2]
  refine (h₁.l2Prod h₂).svMaximalMonotone_svAdjointComp_of_noNontrivialSupport diagL2 0
    (x₀ := x₀) ?_
  rw [svDom_l2Prod, diagL2_apply, add_zero]
  exact noNontrivialSupport_l2ProdSet hx₁ hx₂

/-- **Corollary 12.44 (maximal monotonicity under addition).**  If `T₁` and `T₂`
are maximal monotone and `rint(dom T₁) ∩ rint(dom T₂) ≠ ∅`, then `T₁ + T₂` is
maximal monotone. -/
theorem SvMaximalMonotone.svMaximalMonotone_svAdd {T₁ T₂ : E → Set E}
    (h₁ : SvMaximalMonotone T₁) (h₂ : SvMaximalMonotone T₂)
    (h : (intrinsicInterior ℝ (svDom T₁) ∩ intrinsicInterior ℝ (svDom T₂)).Nonempty) :
    SvMaximalMonotone (svAdd T₁ T₂) := by
  obtain ⟨x₀, hx₁, hx₂⟩ := h
  exact h₁.svMaximalMonotone_svAdd_of_noNontrivialSupport h₂
    (noNontrivialSupport_of_mem_intrinsicInterior hx₁)
    (noNontrivialSupport_of_mem_intrinsicInterior hx₂)

end Products

section Truncation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Example 12.45(a) (truncation).**  If `B` is compact and convex and
`int B` meets `dom T`, then `S = T + N_B` is maximal monotone, agrees with `T`
on `int B`, and has `rge S = IRⁿ`. -/
theorem SvMaximalMonotone.truncation_svDom {T : E → Set E} (hT : SvMaximalMonotone T)
    {B : Set E} (hBc : IsCompact B) (hBconv : Convex ℝ B)
    (hB : (interior B ∩ svDom T).Nonempty) :
    SvMaximalMonotone (svAdd T (normalCone B)) ∧
      (∀ x ∈ interior B, svAdd T (normalCone B) x = T x) ∧
      svRange (svAdd T (normalCone B)) = univ := by
  obtain ⟨x, hxB, hxT⟩ := hB
  have hBne : B.Nonempty := ⟨x, interior_subset hxB⟩
  have hN : SvMaximalMonotone (normalCone B) :=
    svMaximalMonotone_normalCone hBc.isClosed hBconv hBne
  have hxcl : x ∈ closure (intrinsicInterior ℝ (closure (svDom T))) :=
    Convex.subset_closure_intrinsicInterior hT.convex_closure_svDom (subset_closure hxT)
  obtain ⟨z, hzB, hzD⟩ := mem_closure_iff_nhds.1 hxcl _ (isOpen_interior.mem_nhds hxB)
  have hzT : z ∈ intrinsicInterior ℝ (svDom T) := by
    rw [hT.intrinsicInterior_svDom]
    exact hzD
  have hzN : NoNontrivialSupport (svDom (normalCone B)) z := by
    rw [svDom_normalCone B]
    exact noNontrivialSupport_of_mem_intrinsicInterior (interior_subset_intrinsicInterior hzB)
  have hS : SvMaximalMonotone (svAdd T (normalCone B)) :=
    hT.svMaximalMonotone_svAdd_of_noNontrivialSupport hN
      (noNontrivialSupport_of_mem_intrinsicInterior hzT) hzN
  refine ⟨hS, fun y hy ↦ ?_, hS.svRange_eq_univ_of_isBounded_svDom ?_⟩
  · simp only [svAdd]
    rw [normalCone_eq_singleton_of_mem_interior hy, Set.singleton_zero, add_zero]
  · refine hBc.isBounded.subset fun y hy ↦ ?_
    obtain ⟨v, hv⟩ := hy
    obtain ⟨_, -, w, hw, -⟩ := mem_svAdd.1 hv
    exact hw.1

/-- **Example 12.45(b) (truncation).**  If `B` is compact and convex and
`int B` meets `rge T`, then `S = (T⁻¹ + N_B)⁻¹` is maximal monotone, `S⁻¹` agrees
with `T⁻¹` on `int B`, and `dom S = IRⁿ`. -/
theorem SvMaximalMonotone.truncation_svRange {T : E → Set E} (hT : SvMaximalMonotone T)
    {B : Set E} (hBc : IsCompact B) (hBconv : Convex ℝ B)
    (hB : (interior B ∩ svRange T).Nonempty) :
    SvMaximalMonotone (svInv (svAdd (svInv T) (normalCone B))) ∧
      (∀ v ∈ interior B, svInv (svInv (svAdd (svInv T) (normalCone B))) v = svInv T v) ∧
      svDom (svInv (svAdd (svInv T) (normalCone B))) = univ := by
  obtain ⟨h₁, h₂, h₃⟩ := hT.inv.truncation_svDom hBc hBconv (by rwa [svDom_svInv])
  exact ⟨h₁.inv, fun v hv ↦ by rw [svInv_svInv]; exact h₂ v hv, by rwa [svDom_svInv]⟩

/-- **Example 12.45 (truncation)**, collected. -/
theorem truncation {T : E → Set E} (hT : SvMaximalMonotone T) {B : Set E} (hBc : IsCompact B)
    (hBconv : Convex ℝ B) :
    ((interior B ∩ svDom T).Nonempty →
      SvMaximalMonotone (svAdd T (normalCone B)) ∧
        (∀ x ∈ interior B, svAdd T (normalCone B) x = T x) ∧
        svRange (svAdd T (normalCone B)) = univ) ∧
    ((interior B ∩ svRange T).Nonempty →
      SvMaximalMonotone (svInv (svAdd (svInv T) (normalCone B))) ∧
        (∀ v ∈ interior B, svInv (svInv (svAdd (svInv T) (normalCone B))) v = svInv T v) ∧
        svDom (svInv (svAdd (svInv T) (normalCone B))) = univ) :=
  ⟨hT.truncation_svDom hBc hBconv, hT.truncation_svRange hBc hBconv⟩

end Truncation

section Restriction

variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]

/-- The embedding `x₁ ↦ (x₁, 0)` into the Euclidean product. -/
noncomputable def inlL2 : E₁ →L[ℝ] WithLp 2 (E₁ × E₂) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ E₁ E₂)

omit [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂] in
@[simp]
theorem inlL2_apply (x : E₁) : (inlL2 x : WithLp 2 (E₁ × E₂)) = WithLp.toLp 2 (x, 0) := rfl

/-- The adjoint of `x₁ ↦ (x₁, 0)` is the first projection. -/
theorem inlL2_adjoint_apply (q : WithLp 2 (E₁ × E₂)) :
    (inlL2 (E₂ := E₂)).adjoint q = q.fst := by
  refine ext_inner_right ℝ fun x ↦ ?_
  rw [ContinuousLinearMap.adjoint_inner_left, inlL2_apply, WithLp.prod_inner_apply]
  simp

/-- **Exercise 12.46 (restriction of arguments).**  If `T` is maximal monotone
on `IRⁿ¹ × IRⁿ²` and `(x̄₁, x̄₂) ∈ rint(dom T)` for some `x̄₁`, then
`T₁(x₁) = {v₁ | ∃ v₂, (v₁, v₂) ∈ T(x₁, x̄₂)}` is maximal monotone. -/
theorem SvMaximalMonotone.restriction {T : WithLp 2 (E₁ × E₂) → Set (WithLp 2 (E₁ × E₂))}
    (hT : SvMaximalMonotone T) (xbar₂ : E₂)
    (h : ∃ xbar₁ : E₁, WithLp.toLp 2 (xbar₁, xbar₂) ∈ intrinsicInterior ℝ (svDom T)) :
    SvMaximalMonotone
      (fun x₁ : E₁ ↦ {v₁ | ∃ v₂, WithLp.toLp 2 (v₁, v₂) ∈ T (WithLp.toLp 2 (x₁, xbar₂))}) := by
  obtain ⟨xbar₁, hx⟩ := h
  have e : (fun x₁ : E₁ ↦ {v₁ | ∃ v₂, WithLp.toLp 2 (v₁, v₂) ∈ T (WithLp.toLp 2 (x₁, xbar₂))}) =
      svAdjointComp inlL2 T (WithLp.toLp 2 (0, xbar₂)) := by
    funext x₁
    ext v₁
    have ex : (inlL2 x₁ : WithLp 2 (E₁ × E₂)) + WithLp.toLp 2 (0, xbar₂) =
        WithLp.toLp 2 (x₁, xbar₂) := by
      refine withLp_prod_ext ?_ ?_ <;> simp
    rw [mem_svAdjointComp, ex]
    constructor
    · rintro ⟨v₂, hv⟩
      exact ⟨_, hv, by rw [inlL2_adjoint_apply]; rfl⟩
    · rintro ⟨q, hq, rfl⟩
      refine ⟨q.snd, ?_⟩
      rw [inlL2_adjoint_apply]
      exact hq
  rw [e]
  refine hT.svMaximalMonotone_svAdjointComp inlL2 _ ⟨_, ⟨xbar₁, rfl⟩, ?_⟩
  have ex : (inlL2 xbar₁ : WithLp 2 (E₁ × E₂)) + WithLp.toLp 2 (0, xbar₂) =
      WithLp.toLp 2 (xbar₁, xbar₂) := by
    refine withLp_prod_ext ?_ ?_ <;> simp
  change (inlL2 xbar₁ : WithLp 2 (E₁ × E₂)) + WithLp.toLp 2 (0, xbar₂) ∈
    intrinsicInterior ℝ (svDom T)
  rw [ex]
  exact hx

end Restriction

section Lines

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The adjoint of `τ ↦ τw` is `v ↦ ⟪w, v⟫`. -/
theorem toSpanSingleton_adjoint_apply (w v : E) :
    (ContinuousLinearMap.toSpanSingleton ℝ w).adjoint v = ⟪v, w⟫_ℝ := by
  refine ext_inner_right ℝ fun τ ↦ ?_
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.toSpanSingleton_apply,
    real_inner_smul_right]
  simp only [RCLike.inner_apply, conj_trivial]

/-- **Example 12.47 (monotonicity along lines).**  For maximal monotone `T`,
`x ∈ rint(dom T)` and any `w`, the mapping `T_{x,w}(τ) = {⟪v, w⟫ | v ∈ T(x + τw)}`
on `IR` is maximal monotone. -/
theorem SvMaximalMonotone.svMaximalMonotone_alongLine {T : E → Set E}
    (hT : SvMaximalMonotone T) {x : E} (hx : x ∈ intrinsicInterior ℝ (svDom T)) (w : E) :
    SvMaximalMonotone (fun τ : ℝ ↦ (fun v ↦ ⟪v, w⟫_ℝ) '' T (x + τ • w)) := by
  have e : (fun τ : ℝ ↦ (fun v ↦ ⟪v, w⟫_ℝ) '' T (x + τ • w)) =
      svAdjointComp (ContinuousLinearMap.toSpanSingleton ℝ w) T x := by
    funext τ
    ext r
    rw [mem_svAdjointComp, ContinuousLinearMap.toSpanSingleton_apply, add_comm (τ • w) x]
    simp only [mem_image, toSpanSingleton_adjoint_apply]
  rw [e]
  refine hT.svMaximalMonotone_svAdjointComp _ x ⟨x, ⟨0, ?_⟩, hx⟩
  simp

/-- **Example 12.47**, with the representation of 12.9(b): `T_{x,w}` is given by a
nondecreasing `φ : IR → IR̄` with `φ ≢ ∞`, `φ ≢ -∞` and
`T_{x,w}(τ) = {r | φ(τ-) ≤ r ≤ φ(τ+)}`. -/
theorem SvMaximalMonotone.exists_monotone_alongLine {T : E → Set E}
    (hT : SvMaximalMonotone T) {x : E} (hx : x ∈ intrinsicInterior ℝ (svDom T)) (w : E) :
    ∃ φ : ℝ → EReal, Monotone φ ∧ (∃ τ, φ τ ≠ ⊤) ∧ (∃ τ, φ τ ≠ ⊥) ∧
      ∀ τ, (fun v ↦ ⟪v, w⟫_ℝ) '' T (x + τ • w) =
        {r : ℝ | leftLim φ τ ≤ (r : EReal) ∧ (r : EReal) ≤ rightLim φ τ} :=
  svMaximalMonotone_real_iff.1 (hT.svMaximalMonotone_alongLine hx w)

/-- **Example 12.47 (monotonicity along lines)**, collected. -/
theorem monotonicity_along_lines {T : E → Set E} (hT : SvMaximalMonotone T) {x : E}
    (hx : x ∈ intrinsicInterior ℝ (svDom T)) (w : E) :
    SvMaximalMonotone (fun τ : ℝ ↦ (fun v ↦ ⟪v, w⟫_ℝ) '' T (x + τ • w)) ∧
      ∃ φ : ℝ → EReal, Monotone φ ∧ (∃ τ, φ τ ≠ ⊤) ∧ (∃ τ, φ τ ≠ ⊥) ∧
        ∀ τ, (fun v ↦ ⟪v, w⟫_ℝ) '' T (x + τ • w) =
          {r : ℝ | leftLim φ τ ≤ (r : EReal) ∧ (r : EReal) ≤ rightLim φ τ} :=
  ⟨hT.svMaximalMonotone_alongLine hx w, hT.exists_monotone_alongLine hx w⟩

end Lines

end RW
