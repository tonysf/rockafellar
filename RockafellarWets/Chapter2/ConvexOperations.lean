/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 2D: Convexity in operations

This file formalizes Section D of Chapter 2 of Rockafellar–Wets for
extended-real-valued functions, with sums formed by the book's inf-addition
(`finiteInfAddition`, Chapter 7) and the convention `0 · ∞ = 0`.

* Exercise 2.18: nonnegative combinations `∑ λᵢ fᵢ`, and their strict convexity.
* Exercise 2.19: products of convex sets, boxes, and separable functions.
* Exercise 2.20: composition with affine maps, with nondecreasing convex
  functions, and with vectors of convex and affine functions.
* Proposition 2.21: linear images and preimages.
* Proposition 2.22: inf-projection (`valueFunction`, Chapter 3) and
  epi-composition.
* Proposition 2.23: convexity in set algebra.
* Exercise 2.24: epi-sums `infEpiSum` and epi-multiples `epiMultiplication`
  (Chapter 14).
-/

import RockafellarWets.Chapter2.ConvexFunctions
import RockafellarWets.Chapter3.Parametric
import RockafellarWets.Chapter14.EpiOperations

open Set Filter Topology
open scoped Pointwise

noncomputable section

namespace RW

/-! ## Finite inf-addition -/

section FiniteInfAddition

variable {ι : Type*} [Fintype ι]

/-- Finite inf-addition of real values is their ordinary sum. -/
theorem finiteInfAddition_coe (b : ι → ℝ) :
    finiteInfAddition (fun i ↦ (b i : EReal)) = ((∑ i, b i : ℝ) : EReal) := by
  apply le_antisymm
  · exact finiteInfAddition_le_sum fun i ↦ le_rfl
  · refine le_iInf fun r ↦ ?_
    exact EReal.coe_le_coe_iff.mpr (Finset.sum_le_sum fun i _ ↦ EReal.coe_le_coe_iff.mp (r.2 i))

/-- A real number above a finite inf-sum splits into real upper bounds. -/
theorem exists_of_finiteInfAddition_lt {a : ι → EReal} {α : ℝ}
    (h : finiteInfAddition a < (α : EReal)) :
    ∃ r : ι → ℝ, (∀ i, a i ≤ (r i : EReal)) ∧ ∑ i, r i < α := by
  obtain ⟨⟨r, hr⟩, hlt⟩ := iInf_lt_iff.mp h
  exact ⟨r, hr, by exact_mod_cast hlt⟩

/-- A summand `∞` makes a finite inf-sum `∞`. -/
theorem finiteInfAddition_eq_top_of_eq_top {a : ι → EReal} {i₀ : ι} (h : a i₀ = ⊤) :
    finiteInfAddition a = ⊤ := by
  unfold finiteInfAddition
  refine iInf_eq_top.mpr fun r ↦ absurd (r.2 i₀) ?_
  rw [h]
  exact not_le.mpr (EReal.coe_lt_top _)

/-- A summand `-∞` and no summand `∞` make a finite inf-sum `-∞`. -/
theorem finiteInfAddition_eq_bot_of_eq_bot {a : ι → EReal} (ha : ∀ i, a i < ⊤) {i₀ : ι}
    (h : a i₀ = ⊥) : finiteInfAddition a = ⊥ := by
  classical
  refine (EReal.eq_bot_iff_forall_lt _).mpr fun z ↦ ?_
  have hreal : ∀ i, ∃ r : ℝ, a i ≤ (r : EReal) := fun i ↦ by
    obtain ⟨r, hr, -⟩ := EReal.lt_iff_exists_real_btwn.mp (ha i)
    exact ⟨r, hr.le⟩
  choose r hr using hreal
  set S := ∑ i, r i
  let r' : ι → ℝ := Function.update r i₀ (r i₀ - (S - z) - 1)
  have hr' : ∀ i, a i ≤ (r' i : EReal) := by
    intro i
    by_cases hi : i = i₀
    · subst hi
      rw [h]
      exact bot_le
    · simp only [r', Function.update_of_ne hi]
      exact hr i
  have hsum : ∑ i, r' i = S - (S - z) - 1 := by
    simp only [r']
    rw [Finset.sum_update_of_mem (Finset.mem_univ i₀)]
    have := Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ i₀) r
    simp only [S] at this ⊢
    linarith
  calc finiteInfAddition a ≤ ((∑ i, r' i : ℝ) : EReal) := finiteInfAddition_le_sum hr'
    _ < (z : EReal) := by rw [hsum]; exact_mod_cast (by linarith)

/-- A strictly smaller summand gives a strictly smaller finite inf-sum. -/
theorem finiteInfAddition_lt_of_le_of_lt {a : ι → EReal} {c : ι → ℝ}
    (h : ∀ i, a i ≤ (c i : EReal)) {i₀ : ι} (h₀ : a i₀ < (c i₀ : EReal)) :
    finiteInfAddition a < ((∑ i, c i : ℝ) : EReal) := by
  classical
  obtain ⟨r₀, hr₀, hr₀c⟩ := EReal.lt_iff_exists_real_btwn.mp h₀
  let r : ι → ℝ := Function.update c i₀ r₀
  have hr : ∀ i, a i ≤ (r i : EReal) := by
    intro i
    by_cases hi : i = i₀
    · subst hi
      simpa [r] using hr₀.le
    · simpa [r, Function.update_of_ne hi] using h i
  have hlt : ∑ i, r i < ∑ i, c i := by
    refine Finset.sum_lt_sum (fun i _ ↦ ?_) ⟨i₀, Finset.mem_univ _, ?_⟩
    · by_cases hi : i = i₀
      · subst hi
        simpa [r] using (EReal.coe_lt_coe_iff.mp hr₀c).le
      · simp [r, Function.update_of_ne hi]
    · simpa [r] using EReal.coe_lt_coe_iff.mp hr₀c
  exact (finiteInfAddition_le_sum hr).trans_lt (by exact_mod_cast hlt)

/-- A finite inf-sum is finite exactly when all summands are finite. -/
theorem finiteInfAddition_finite_iff {a : ι → EReal} :
    (finiteInfAddition a ≠ ⊤ ∧ finiteInfAddition a ≠ ⊥) → ∀ i, a i ≠ ⊤ ∧ a i ≠ ⊥ := by
  rintro ⟨ht, hb⟩ i
  have htop : ∀ j, a j < ⊤ := fun j ↦ lt_top_iff_ne_top.mpr fun hj ↦
    ht (finiteInfAddition_eq_top_of_eq_top hj)
  exact ⟨(htop i).ne, fun hi ↦ hb (finiteInfAddition_eq_bot_of_eq_bot htop hi)⟩

end FiniteInfAddition

/-! ## Convexity of finite inf-sums -/

section Sums

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*} [Fintype ι]

/-- A finite inf-sum of convex functions is convex. -/
theorem isConvexRelative_finiteInfAddition {g : ι → E → EReal}
    (hg : ∀ i, IsConvexRelative univ (g i)) :
    IsConvexRelative univ (fun x ↦ finiteInfAddition fun i ↦ g i x) := by
  rw [isConvexRelative_iff_lt convex_univ]
  intro x₀ _ x₁ _ α₀ α₁ h₀ h₁ τ hτ0 hτ1
  obtain ⟨r, hr, hrα⟩ := exists_of_finiteInfAddition_lt h₀
  obtain ⟨s, hs, hsα⟩ := exists_of_finiteInfAddition_lt h₁
  have hi : ∀ i, g i ((1 - τ) • x₀ + τ • x₁) ≤ (((1 - τ) * r i + τ * s i : ℝ) : EReal) :=
    fun i ↦ (hg i).le_of_le (hr i) (hs i) hτ0.le hτ1.le
  refine (finiteInfAddition_le_sum hi).trans (EReal.coe_le_coe_iff.mpr ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  nlinarith

/-- A finite inf-sum of convex functions is strictly convex when, for every pair
of distinct points, one summand satisfies the strict inequality 2(3) there. -/
theorem isStrictlyConvexRelative_finiteInfAddition {g : ι → E → EReal}
    (hg : ∀ i, IsConvexRelative univ (g i))
    (hstrict : ∀ x₀ x₁ : E, x₀ ≠ x₁ → ∃ i, g i x₀ ≠ ⊤ → g i x₀ ≠ ⊥ → g i x₁ ≠ ⊤ →
      g i x₁ ≠ ⊥ → ∀ τ : ℝ, 0 < τ → τ < 1 →
        g i ((1 - τ) • x₀ + τ • x₁) <
          infAddition (((1 - τ : ℝ) : EReal) * g i x₀) ((τ : EReal) * g i x₁)) :
    IsStrictlyConvexRelative univ (fun x ↦ finiteInfAddition fun i ↦ g i x) := by
  refine ⟨isConvexRelative_finiteInfAddition hg, ?_⟩
  intro x₀ _ x₁ _ hne h₀t h₀b h₁t h₁b τ hτ0 hτ1
  have hfin₀ := finiteInfAddition_finite_iff ⟨h₀t, h₀b⟩
  have hfin₁ := finiteInfAddition_finite_iff ⟨h₁t, h₁b⟩
  set b : ι → ℝ := fun i ↦ (g i x₀).toReal
  set c : ι → ℝ := fun i ↦ (g i x₁).toReal
  have hb : ∀ i, g i x₀ = (b i : EReal) := fun i ↦ (EReal.coe_toReal (hfin₀ i).1 (hfin₀ i).2).symm
  have hc : ∀ i, g i x₁ = (c i : EReal) := fun i ↦ (EReal.coe_toReal (hfin₁ i).1 (hfin₁ i).2).symm
  have hG₀ : finiteInfAddition (fun i ↦ g i x₀) = ((∑ i, b i : ℝ) : EReal) := by
    rw [← finiteInfAddition_coe]; exact congrArg _ (funext hb)
  have hG₁ : finiteInfAddition (fun i ↦ g i x₁) = ((∑ i, c i : ℝ) : EReal) := by
    rw [← finiteInfAddition_coe]; exact congrArg _ (funext hc)
  have hle : ∀ i, g i ((1 - τ) • x₀ + τ • x₁) ≤ (((1 - τ) * b i + τ * c i : ℝ) : EReal) :=
    fun i ↦ (hg i).le_of_le (hb i).le (hc i).le hτ0.le hτ1.le
  obtain ⟨i₀, hi₀⟩ := hstrict x₀ x₁ hne
  have hlt : g i₀ ((1 - τ) • x₀ + τ • x₁) < (((1 - τ) * b i₀ + τ * c i₀ : ℝ) : EReal) := by
    have := hi₀ (hfin₀ i₀).1 (hfin₀ i₀).2 (hfin₁ i₀).1 (hfin₁ i₀).2 τ hτ0 hτ1
    rwa [hb i₀, hc i₀, ← EReal.coe_mul, ← EReal.coe_mul,
      infAddition_eq_add_of_ne_bot (EReal.coe_ne_bot _) (EReal.coe_ne_bot _),
      ← EReal.coe_add] at this
  beta_reduce
  rw [hG₀, hG₁, ← EReal.coe_mul, ← EReal.coe_mul,
    infAddition_eq_add_of_ne_bot (EReal.coe_ne_bot _) (EReal.coe_ne_bot _), ← EReal.coe_add]
  calc finiteInfAddition (fun i ↦ g i ((1 - τ) • x₀ + τ • x₁))
      < ((∑ i, ((1 - τ) * b i + τ * c i) : ℝ) : EReal) :=
        finiteInfAddition_lt_of_le_of_lt hle hlt
    _ = (((1 - τ) * ∑ i, b i + τ * ∑ i, c i : ℝ) : EReal) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- Multiplying a convex function by a nonnegative scalar preserves convexity
(with `0 · ∞ = 0`). -/
theorem IsConvexRelative.const_mul {f : E → EReal} (hf : IsConvexRelative univ f) {lam : ℝ}
    (hlam : 0 ≤ lam) : IsConvexRelative univ (fun x ↦ (lam : EReal) * f x) := by
  rcases hlam.eq_or_lt with rfl | hpos
  · simpa using (isConvexRelative_coe_iff convex_univ (fun _ : E ↦ (0 : ℝ))).mpr
      (convexOn_const 0 convex_univ)
  rw [isConvexRelative_iff_lt convex_univ]
  intro x₀ _ x₁ _ α₀ α₁ h₀ h₁ τ hτ0 hτ1
  have h₀' : f x₀ ≤ ((α₀ / lam : ℝ) : EReal) := ereal_le_coe_div_of_coe_mul_le hpos h₀.le
  have h₁' : f x₁ ≤ ((α₁ / lam : ℝ) : EReal) := ereal_le_coe_div_of_coe_mul_le hpos h₁.le
  have h := hf.le_of_le h₀' h₁' hτ0.le hτ1.le
  calc (lam : EReal) * f ((1 - τ) • x₀ + τ • x₁)
      ≤ (lam : EReal) * (((1 - τ) * (α₀ / lam) + τ * (α₁ / lam) : ℝ) : EReal) :=
        mul_le_mul_of_nonneg_left h (EReal.coe_nonneg.mpr hpos.le)
    _ = (((1 - τ) * α₀ + τ * α₁ : ℝ) : EReal) := by
        rw [← EReal.coe_mul]
        congr 1
        field_simp

/-- A positive multiple of a strictly convex function is strictly convex. -/
theorem IsStrictlyConvexRelative.const_mul {f : E → EReal} (hf : IsStrictlyConvexRelative univ f)
    {lam : ℝ} (hlam : 0 < lam) : IsStrictlyConvexRelative univ (fun x ↦ (lam : EReal) * f x) := by
  refine ⟨hf.1.const_mul hlam.le, ?_⟩
  intro x₀ _ x₁ _ hne h₀t h₀b h₁t h₁b τ hτ0 hτ1
  have hne₀ : f x₀ ≠ ⊤ ∧ f x₀ ≠ ⊥ := by
    constructor <;> intro h <;> simp [h, EReal.coe_mul_top_of_pos hlam,
      EReal.coe_mul_bot_of_pos hlam] at h₀t h₀b
  have hne₁ : f x₁ ≠ ⊤ ∧ f x₁ ≠ ⊥ := by
    constructor <;> intro h <;> simp [h, EReal.coe_mul_top_of_pos hlam,
      EReal.coe_mul_bot_of_pos hlam] at h₁t h₁b
  have hs := hf.2 (mem_univ x₀) (mem_univ x₁) hne hne₀.1 hne₀.2 hne₁.1 hne₁.2 hτ0 hτ1
  lift f x₀ to ℝ using hne₀ with u
  lift f x₁ to ℝ using hne₁ with v
  rw [← EReal.coe_mul, ← EReal.coe_mul,
    infAddition_eq_add_of_ne_bot (EReal.coe_ne_bot _) (EReal.coe_ne_bot _),
    ← EReal.coe_add] at hs
  rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_mul,
    infAddition_eq_add_of_ne_bot (EReal.coe_ne_bot _) (EReal.coe_ne_bot _), ← EReal.coe_add]
  calc (lam : EReal) * f ((1 - τ) • x₀ + τ • x₁)
      < ((lam * ((1 - τ) * u + τ * v) : ℝ) : EReal) := ereal_coe_mul_lt_coe_mul hlam hs
    _ = (((1 - τ) * (lam * u) + τ * (lam * v) : ℝ) : EReal) := by congr 1; ring

/-- **Exercise 2.18**: for convex `fᵢ` and `λᵢ ≥ 0`, the function `∑ λᵢ fᵢ`
(formed with inf-addition) is convex. -/
theorem IsConvexRelative.finiteInfAddition_smul {f : ι → E → EReal}
    (hf : ∀ i, IsConvexRelative univ (f i)) {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i) :
    IsConvexRelative univ (fun x ↦ finiteInfAddition fun i ↦ (lam i : EReal) * f i x) :=
  isConvexRelative_finiteInfAddition fun i ↦ (hf i).const_mul (hlam i)

/-- **Exercise 2.18**: `∑ λᵢ fᵢ` is strictly convex when some `fᵢ` with
`λᵢ > 0` is strictly convex. -/
theorem IsStrictlyConvexRelative.finiteInfAddition_smul {f : ι → E → EReal}
    (hf : ∀ i, IsConvexRelative univ (f i)) {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i) {i₀ : ι}
    (hi₀ : 0 < lam i₀) (hs : IsStrictlyConvexRelative univ (f i₀)) :
    IsStrictlyConvexRelative univ (fun x ↦ finiteInfAddition fun i ↦ (lam i : EReal) * f i x) := by
  refine isStrictlyConvexRelative_finiteInfAddition (fun i ↦ (hf i).const_mul (hlam i))
    fun x₀ x₁ hne ↦ ⟨i₀, fun h₀t h₀b h₁t h₁b τ hτ0 hτ1 ↦ ?_⟩
  exact (hs.const_mul hi₀).2 (mem_univ x₀) (mem_univ x₁) hne h₀t h₀b h₁t h₁b hτ0 hτ1

end Sums

/-! ## Exercise 2.19 -/

section Products

variable {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, AddCommGroup (E i)]
  [∀ i, Module ℝ (E i)]

omit [Fintype ι] in
/-- **Exercise 2.19(a)**: a product of convex sets is convex. -/
theorem convex_pi_of_convex {C : ∀ i, Set (E i)} (hC : ∀ i, Convex ℝ (C i)) :
    Convex ℝ (Set.pi univ C) :=
  convex_pi fun i _ ↦ hC i

omit [Fintype ι] in
/-- **Exercise 2.19(a)**: a box, a product of closed intervals (possibly
unbounded), is closed and convex. -/
theorem isClosed_convex_box {X : ι → Set ℝ} (hX : ∀ j, IsClosed (X j))
    (hXc : ∀ j, Convex ℝ (X j)) : IsClosed (Set.pi univ X) ∧ Convex ℝ (Set.pi univ X) :=
  ⟨isClosed_set_pi fun j _ ↦ hX j, convex_pi fun j _ ↦ hXc j⟩

omit [Fintype ι] in
/-- A convex function of one block of variables is convex on the product. -/
theorem IsConvexRelative.comp_eval {i : ι} {f : E i → EReal} (hf : IsConvexRelative univ f) :
    IsConvexRelative univ (fun x : (∀ j, E j) ↦ f (x i)) :=
  fun x₀ _ x₁ _ τ hτ0 hτ1 ↦ by simpa using hf (mem_univ (x₀ i)) (mem_univ (x₁ i)) hτ0 hτ1

/-- **Exercise 2.19(b)**: a separable function `∑ fᵢ(xᵢ)` of convex functions
(formed with inf-addition) is convex. -/
theorem IsConvexRelative.separable {f : ∀ i, E i → EReal}
    (hf : ∀ i, IsConvexRelative univ (f i)) :
    IsConvexRelative univ (fun x : (∀ i, E i) ↦ finiteInfAddition fun i ↦ f i (x i)) :=
  isConvexRelative_finiteInfAddition fun i ↦ (hf i).comp_eval

/-- **Exercise 2.19(b)**: a separable function of strictly convex functions is
strictly convex. -/
theorem IsStrictlyConvexRelative.separable {f : ∀ i, E i → EReal}
    (hf : ∀ i, IsStrictlyConvexRelative univ (f i)) :
    IsStrictlyConvexRelative univ
      (fun x : (∀ i, E i) ↦ finiteInfAddition fun i ↦ f i (x i)) := by
  refine isStrictlyConvexRelative_finiteInfAddition (fun i ↦ (hf i).1.comp_eval) ?_
  intro x₀ x₁ hne
  obtain ⟨i, hi⟩ : ∃ i, x₀ i ≠ x₁ i := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  refine ⟨i, fun h₀t h₀b h₁t h₁b τ hτ0 hτ1 ↦ ?_⟩
  simpa using (hf i).2 (mem_univ (x₀ i)) (mem_univ (x₁ i)) hi h₀t h₀b h₁t h₁b hτ0 hτ1

end Products

/-! ## Exercise 2.20 -/

section Composition

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- **Exercise 2.20(a)**: `x ↦ g(Ax + a)` is convex for convex `g` and linear `A`. -/
theorem IsConvexRelative.comp_affine {g : F → EReal} (hg : IsConvexRelative univ g)
    (A : E →ₗ[ℝ] F) (a : F) : IsConvexRelative univ (fun x ↦ g (A x + a)) := by
  intro x₀ _ x₁ _ τ hτ0 hτ1
  have h : A ((1 - τ) • x₀ + τ • x₁) + a = (1 - τ) • (A x₀ + a) + τ • (A x₁ + a) := by
    simp only [map_add, map_smul]
    module
  change g (A ((1 - τ) • x₀ + τ • x₁) + a) ≤ _
  rw [h]
  exact hg (mem_univ _) (mem_univ _) hτ0 hτ1

/-- The extension of `θ : ℝ → ℝ̄` to `ℝ̄` with `θ(∞) = ∞` and `θ(-∞) = inf θ`,
the convention of Exercise 2.20(b). -/
def compositionExtension (θ : ℝ → EReal) (u : EReal) : EReal :=
  if u = ⊤ then ⊤ else if u = ⊥ then ⨅ t, θ t else θ u.toReal

@[simp] theorem compositionExtension_top (θ : ℝ → EReal) : compositionExtension θ ⊤ = ⊤ := by
  simp [compositionExtension]

@[simp] theorem compositionExtension_bot (θ : ℝ → EReal) : compositionExtension θ ⊥ = ⨅ t, θ t := by
  simp [compositionExtension]

@[simp] theorem compositionExtension_coe (θ : ℝ → EReal) (t : ℝ) :
    compositionExtension θ (t : EReal) = θ t := by
  simp [compositionExtension]

theorem monotone_compositionExtension {θ : ℝ → EReal} (hθ : Monotone θ) :
    Monotone (compositionExtension θ) := by
  intro u v huv
  induction u using EReal.rec with
  | bot =>
    induction v using EReal.rec with
    | bot => exact le_rfl
    | coe t => simpa using iInf_le θ t
    | top => simp
  | coe s =>
    induction v using EReal.rec with
    | bot => exact absurd huv (by simp)
    | coe t => simpa using hθ (EReal.coe_le_coe_iff.mp huv)
    | top => simp
  | top =>
    have : v = ⊤ := top_le_iff.mp huv
    subst this
    exact le_rfl

/-- **Exercise 2.20(b)**: `θ ∘ g` is convex for convex `g` and nondecreasing
convex `θ : ℝ → ℝ̄`, with `θ(∞) = ∞` and `θ(-∞) = inf θ`. -/
theorem IsConvexRelative.comp_monotone {g : E → EReal} (hg : IsConvexRelative univ g)
    {θ : ℝ → EReal} (hθ : IsConvexRelative univ θ) (hmono : Monotone θ) :
    IsConvexRelative univ (fun x ↦ compositionExtension θ (g x)) := by
  have key : ∀ x (α : ℝ), compositionExtension θ (g x) < (α : EReal) →
      ∃ t : ℝ, g x ≤ (t : EReal) ∧ θ t < (α : EReal) := by
    intro x α h
    induction hgx : g x using EReal.rec with
    | bot =>
      rw [hgx, compositionExtension_bot] at h
      obtain ⟨t, ht⟩ := iInf_lt_iff.mp h
      exact ⟨t, bot_le, ht⟩
    | coe s =>
      rw [hgx, compositionExtension_coe] at h
      exact ⟨s, le_rfl, h⟩
    | top =>
      rw [hgx, compositionExtension_top] at h
      exact absurd h (not_lt_of_ge le_top)
  rw [isConvexRelative_iff_lt convex_univ]
  intro x₀ _ x₁ _ α₀ α₁ h₀ h₁ τ hτ0 hτ1
  obtain ⟨t₀, hg₀, hθ₀⟩ := key x₀ α₀ h₀
  obtain ⟨t₁, hg₁, hθ₁⟩ := key x₁ α₁ h₁
  have hgτ := hg.le_of_le hg₀ hg₁ hτ0.le hτ1.le
  calc compositionExtension θ (g ((1 - τ) • x₀ + τ • x₁))
      ≤ compositionExtension θ (((1 - τ) * t₀ + τ * t₁ : ℝ) : EReal) :=
        monotone_compositionExtension hmono hgτ
    _ = θ ((1 - τ) * t₀ + τ * t₁) := compositionExtension_coe θ _
    _ ≤ (((1 - τ) * α₀ + τ * α₁ : ℝ) : EReal) := by
        have := (isConvexRelative_iff_lt convex_univ θ).mp hθ (mem_univ t₀) (mem_univ t₁)
          hθ₀ hθ₁ hτ0 hτ1
        simpa [smul_eq_mul] using this

/-- **Exercise 2.20(b)**, strict part, corrected: `θ ∘ g` is strictly convex when
`g` is strictly convex and never `-∞`, and `θ` is increasing and convex.  Without
`g > -∞` the claim fails (`not_isStrictlyConvexRelative_comp_of_bot`). -/
theorem IsStrictlyConvexRelative.comp_strictMono {g : E → EReal}
    (hg : IsStrictlyConvexRelative univ g) (hgb : ∀ x, g x ≠ ⊥) {θ : ℝ → EReal}
    (hθ : IsConvexRelative univ θ) (hmono : StrictMono θ) :
    IsStrictlyConvexRelative univ (fun x ↦ compositionExtension θ (g x)) := by
  refine ⟨hg.1.comp_monotone hθ hmono.monotone, ?_⟩
  intro x₀ _ x₁ _ hne h₀t h₀b h₁t h₁b τ hτ0 hτ1
  have hg₀t : g x₀ ≠ ⊤ := fun h ↦ h₀t (by simp [h])
  have hg₁t : g x₁ ≠ ⊤ := fun h ↦ h₁t (by simp [h])
  have hs := hg.2 (mem_univ x₀) (mem_univ x₁) hne hg₀t (hgb x₀) hg₁t (hgb x₁) hτ0 hτ1
  simp only at h₀t h₀b h₁t h₁b ⊢
  lift g x₀ to ℝ using ⟨hg₀t, hgb x₀⟩ with u hu
  lift g x₁ to ℝ using ⟨hg₁t, hgb x₁⟩ with v hv
  rw [compositionExtension_coe] at h₀t h₀b h₁t h₁b ⊢
  rw [← EReal.coe_mul, ← EReal.coe_mul,
    infAddition_eq_add_of_ne_bot (EReal.coe_ne_bot _) (EReal.coe_ne_bot _),
    ← EReal.coe_add] at hs
  have hτb := hgb ((1 - τ) • x₀ + τ • x₁)
  lift g ((1 - τ) • x₀ + τ • x₁) to ℝ using ⟨(hs.trans (EReal.coe_lt_top _)).ne, hτb⟩ with w hw
  rw [compositionExtension_coe]
  calc θ w < θ ((1 - τ) * u + τ * v) := hmono (EReal.coe_lt_coe_iff.mp hs)
    _ ≤ infAddition (((1 - τ : ℝ) : EReal) * θ u) ((τ : EReal) * θ v) := by
        simpa [smul_eq_mul] using hθ (mem_univ u) (mem_univ v) hτ0 hτ1

/-- The strict part of Exercise 2.20(b) needs `g > -∞`: the constant `-∞`
function is (vacuously) strictly convex, `θ = exp` is increasing and convex, yet
`θ ∘ g ≡ inf θ` is a finite constant, which is not strictly convex. -/
theorem not_isStrictlyConvexRelative_comp_of_bot :
    IsStrictlyConvexRelative univ (fun _ : ℝ ↦ (⊥ : EReal)) ∧
      IsConvexRelative univ (fun t : ℝ ↦ (Real.exp t : EReal)) ∧
      StrictMono (fun t : ℝ ↦ (Real.exp t : EReal)) ∧
      ¬IsStrictlyConvexRelative univ
        (fun x : ℝ ↦ compositionExtension (fun t : ℝ ↦ (Real.exp t : EReal)) ((fun _ ↦ ⊥) x)) := by
  refine ⟨⟨fun _ _ _ _ _ _ _ ↦ bot_le, fun _ _ _ _ _ _ h ↦ absurd rfl h⟩,
    (isConvexRelative_coe_iff convex_univ _).mpr convexOn_exp,
    fun s t hst ↦ EReal.coe_lt_coe_iff.mpr (Real.exp_lt_exp.mpr hst), ?_⟩
  rintro ⟨-, hs⟩
  have hct : (⨅ t : ℝ, (Real.exp t : EReal)) ≠ ⊤ :=
    (lt_of_le_of_lt (iInf_le (fun t : ℝ ↦ (Real.exp t : EReal)) 0) (EReal.coe_lt_top _)).ne
  have hcb : (⨅ t : ℝ, (Real.exp t : EReal)) ≠ ⊥ := by
    refine (lt_of_lt_of_le (EReal.bot_lt_coe 0) (le_iInf fun t ↦ ?_)).ne'
    exact EReal.coe_le_coe_iff.mpr (Real.exp_pos t).le
  have h := hs (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ)) zero_ne_one
    (by simp) (by simpa using hcb) (by simp) (by simpa using hcb)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  simp only [compositionExtension_bot] at h
  generalize (⨅ t : ℝ, (Real.exp t : EReal)) = c at h hct hcb
  lift c to ℝ using ⟨hct, hcb⟩ with a
  rw [← EReal.coe_mul, ← EReal.coe_mul,
    infAddition_eq_add_of_ne_bot (EReal.coe_ne_bot _) (EReal.coe_ne_bot _),
    ← EReal.coe_add, EReal.coe_lt_coe_iff] at h
  linarith

/-- Coordinatewise monotonicity in the coordinates of `S` gives monotonicity
for simultaneous increases in those coordinates. -/
theorem monotone_of_forall_update {ι : Type*} [Finite ι] [DecidableEq ι] {S : Set ι}
    {g : (ι → ℝ) → EReal}
    (hmono : ∀ i ∈ S, ∀ (u : ι → ℝ) (s t : ℝ), s ≤ t →
      g (Function.update u i s) ≤ g (Function.update u i t))
    {u v : ι → ℝ} (hle : ∀ i ∈ S, u i ≤ v i) (heq : ∀ i ∉ S, u i = v i) : g u ≤ g v := by
  classical
  have := Fintype.ofFinite ι
  have key : ∀ T : Finset ι, (↑T : Set ι) ⊆ S →
      g u ≤ g (fun i ↦ if i ∈ T then v i else u i) := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _; simp
    | insert j T hj ih =>
      intro hTS
      have hjS : j ∈ S := hTS (by simp)
      refine (ih fun x hx ↦ hTS (by simp [hx])).trans ?_
      have e1 : (fun i ↦ if i ∈ T then v i else u i) =
          Function.update (fun i ↦ if i ∈ T then v i else u i) j (u j) := by
        funext i
        by_cases hij : i = j
        · subst hij; simp [hj]
        · simp [Function.update_of_ne hij]
      have e2 : (fun i ↦ if i ∈ insert j T then v i else u i) =
          Function.update (fun i ↦ if i ∈ T then v i else u i) j (v j) := by
        funext i
        by_cases hij : i = j
        · subst hij; simp
        · simp [hij]
      rw [e1, e2]
      exact hmono j hjS _ _ _ (hle j hjS)
  have := key (Finset.univ.filter (· ∈ S)) (fun x hx ↦ by simpa using hx)
  convert this using 2
  funext i
  by_cases hi : i ∈ S
  · simp [hi]
  · simp [hi, heq i hi]

/-- **Exercise 2.20(c)**: `x ↦ g(F(x))` is convex when `F = (f₁, …, f_m)` has
convex components `fᵢ` for `i ∈ S` and affine components otherwise, and `g` is
convex and nondecreasing in each `uᵢ` with `i ∈ S`. -/
theorem IsConvexRelative.comp_vector {ι : Type*} [Finite ι] [DecidableEq ι] {S : Set ι}
    {g : (ι → ℝ) → EReal} (hg : IsConvexRelative univ g)
    (hmono : ∀ i ∈ S, ∀ (u : ι → ℝ) (s t : ℝ), s ≤ t →
      g (Function.update u i s) ≤ g (Function.update u i t))
    {f : ι → E → ℝ} (hconv : ∀ i ∈ S, ConvexOn ℝ univ (f i))
    (haff : ∀ i ∉ S, ∃ (L : E →ₗ[ℝ] ℝ) (c : ℝ), ∀ x, f i x = L x + c) :
    IsConvexRelative univ (fun x ↦ g (fun i ↦ f i x)) := by
  intro x₀ _ x₁ _ τ hτ0 hτ1
  have hle : g (fun i ↦ f i ((1 - τ) • x₀ + τ • x₁)) ≤
      g ((1 - τ) • (fun i ↦ f i x₀) + τ • (fun i ↦ f i x₁)) := by
    refine monotone_of_forall_update hmono (fun i hi ↦ ?_) (fun i hi ↦ ?_)
    · have := (hconv i hi).2 (mem_univ x₀) (mem_univ x₁) (by linarith : (0 : ℝ) ≤ 1 - τ)
        hτ0.le (by ring)
      simpa [smul_eq_mul] using this
    · obtain ⟨L, c, hL⟩ := haff i hi
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hL, map_add, map_smul]
      ring
  exact hle.trans (hg (mem_univ _) (mem_univ _) hτ0 hτ1)

end Composition

/-! ## Proposition 2.21 -/

/-- **Proposition 2.21**: linear images and preimages of convex sets are convex. -/
theorem convex_linear_image_and_preimage {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (L : E →ₗ[ℝ] F) :
    (∀ C : Set E, Convex ℝ C → Convex ℝ (L '' C)) ∧
      ∀ D : Set F, Convex ℝ D → Convex ℝ (L ⁻¹' D) :=
  ⟨fun _ hC ↦ hC.linear_image L, fun _ hD ↦ hD.linear_preimage L⟩

/-! ## Proposition 2.22 -/

section InfProjection

/-- Equality of strict epigraphs forces equality of functions. -/
theorem eq_of_strictEpigraph_eq {E : Type*} {f g : E → EReal}
    (h : strictEpigraph f = strictEpigraph g) : f = g := by
  funext x
  have key : ∀ (φ ψ : E → EReal), strictEpigraph φ ⊆ strictEpigraph ψ → ψ x ≤ φ x := by
    intro φ ψ hsub
    refine EReal.le_of_forall_lt_iff_le.mp fun z hz ↦ ?_
    exact (hsub (show (x, z) ∈ strictEpigraph φ from hz)).le
  exact le_antisymm (key g f h.ge) (key f g h.le)

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem strictEpigraph_valueFunction (f : E × F → EReal) :
    strictEpigraph (valueFunction f) =
      (LinearMap.prodMap (LinearMap.snd ℝ E F) (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) ''
        strictEpigraph f := by
  ext ⟨u, α⟩
  simp only [mem_strictEpigraph, valueFunction, iInf_lt_iff, mem_image, Prod.exists,
    LinearMap.prodMap_apply, LinearMap.snd_apply, LinearMap.id_coe, id_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, u, α, hx, rfl, rfl⟩
  · rintro ⟨x, u', α', hx, rfl, rfl⟩
    exact ⟨x, hx⟩

/-- **Proposition 2.22(a)**: the inf-projection `p(u) = inf_x f(x,u)` of a convex
function is convex. -/
theorem isConvexRelative_valueFunction {f : E × F → EReal} (hf : IsConvexRelative univ f) :
    IsConvexRelative univ (valueFunction f) := by
  rw [isConvexRelative_univ_iff_convex_strictEpigraph, strictEpigraph_valueFunction]
  exact ((isConvexRelative_univ_iff_convex_strictEpigraph f).mp hf).linear_image _

/-- **Proposition 2.22(a)**: the minimizer sets `P(u) = argmin_x f(x,u)` of a
convex function are convex. -/
theorem convex_paramArgmin {f : E × F → EReal} (hf : IsConvexRelative univ f) (u : F) :
    Convex ℝ (paramArgmin f u) := by
  have h := hf.comp_affine (LinearMap.inl ℝ E F) (0, u)
  have h' : IsConvexRelative univ (fun x : E ↦ f (x, u)) := by
    simpa using h
  exact h'.convex_argmin

/-- **Proposition 2.22(b)**: the epi-composition
`(Af)(u) = inf {f(x) | Ax = u}` of a convex function is convex. -/
theorem isConvexRelative_epiComposition {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] {f : E → EReal} (hf : IsConvexRelative univ f)
    (A : E →ₗ[ℝ] F) :
    IsConvexRelative univ (fun u ↦ ⨅ x : {x : E // A x = u}, f x) := by
  rw [isConvexRelative_univ_iff_convex_strictEpigraph]
  have himg : strictEpigraph (fun u ↦ ⨅ x : {x : E // A x = u}, f x) =
      (LinearMap.prodMap A (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) '' strictEpigraph f := by
    ext ⟨u, α⟩
    simp only [mem_strictEpigraph, iInf_lt_iff, Subtype.exists, exists_prop, mem_image,
      Prod.exists, LinearMap.prodMap_apply, LinearMap.id_coe, id_eq, Prod.mk.injEq]
    constructor
    · rintro ⟨x, hx, hfx⟩
      exact ⟨x, α, hfx, hx, rfl⟩
    · rintro ⟨x, α', hfx, hx, rfl⟩
      exact ⟨x, hx, hfx⟩
  rw [himg]
  exact ((isConvexRelative_univ_iff_convex_strictEpigraph f).mp hf).linear_image _

end InfProjection

/-! ## Proposition 2.23 -/

/-- **Proposition 2.23**: (a) `C₁ + C₂` is convex, (b) `λC` is convex, and
(c) `(λ₁ + λ₂)C = λ₁C + λ₂C` for `λ₁, λ₂ ≥ 0` when `C` is convex. -/
theorem convex_setAlgebra {E : Type*} [AddCommGroup E] [Module ℝ E] :
    (∀ C₁ C₂ : Set E, Convex ℝ C₁ → Convex ℝ C₂ → Convex ℝ (C₁ + C₂)) ∧
      (∀ (C : Set E) (lam : ℝ), Convex ℝ C → Convex ℝ (lam • C)) ∧
      ∀ (C : Set E) (lam₁ lam₂ : ℝ), Convex ℝ C → 0 ≤ lam₁ → 0 ≤ lam₂ →
        (lam₁ + lam₂) • C = lam₁ • C + lam₂ • C :=
  ⟨fun _ _ h₁ h₂ ↦ h₁.add h₂, fun _ lam hC ↦ hC.smul lam,
    fun _ _ _ hC h₁ h₂ ↦ hC.add_smul h₁ h₂⟩

/-! ## Exercise 2.24 -/

section EpiOperations

@[simp] theorem zero_infAddition (a : EReal) : infAddition 0 a = a := by
  induction a using EReal.rec <;> simp [infAddition]

@[simp] theorem top_infAddition (a : EReal) : infAddition ⊤ a = ⊤ := by
  simp [infAddition]

@[simp] theorem infAddition_top (a : EReal) : infAddition a ⊤ = ⊤ := by
  simp [infAddition]

/-- Strict form of `infAddition_le_coe_iff`. -/
theorem infAddition_lt_coe_iff (u v : EReal) (α : ℝ) :
    infAddition u v < (α : EReal) ↔
      ∃ r s : ℝ, u < (r : EReal) ∧ v < (s : EReal) ∧ r + s = α := by
  constructor
  · intro h
    have hu : u ≠ ⊤ := fun hu ↦ by simp [hu] at h
    have hv : v ≠ ⊤ := fun hv ↦ by simp [hv] at h
    rw [infAddition, if_neg (by tauto)] at h
    induction u using EReal.rec with
    | bot =>
      obtain ⟨s, hs, -⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_top_iff_ne_top.mpr hv)
      exact ⟨α - s, s, EReal.bot_lt_coe _, hs, by ring⟩
    | top => exact absurd rfl hu
    | coe y =>
      induction v using EReal.rec with
      | bot =>
        exact ⟨y + 1, α - y - 1, EReal.coe_lt_coe_iff.mpr (by linarith), EReal.bot_lt_coe _,
          by ring⟩
      | top => exact absurd rfl hv
      | coe z =>
        have hyz : y + z < α := by exact_mod_cast h
        refine ⟨y + (α - y - z) / 2, z + (α - y - z) / 2, ?_, ?_, by ring⟩ <;>
          exact EReal.coe_lt_coe_iff.mpr (by linarith)
  · rintro ⟨r, s, hr, hs, rfl⟩
    rw [infAddition, if_neg, EReal.coe_add]
    · exact EReal.add_lt_add hr hs
    · rintro (h | h)
      · rw [h] at hr; exact not_top_lt hr
      · rw [h] at hs; exact not_top_lt hs

/-- Multiplying by a positive real and comparing with a real bound. -/
theorem ereal_coe_mul_lt_coe_iff {t : ℝ} (ht : 0 < t) (u : EReal) (r : ℝ) :
    (t : EReal) * u < (r : EReal) ↔ u < ((t⁻¹ * r : ℝ) : EReal) := by
  induction u using EReal.rec with
  | bot =>
    rw [EReal.coe_mul_bot_of_pos ht]
    exact ⟨fun _ ↦ EReal.bot_lt_coe _, fun _ ↦ EReal.bot_lt_coe _⟩
  | top => simp [EReal.coe_mul_top_of_pos ht]
  | coe y =>
    rw [← EReal.coe_mul, EReal.coe_lt_coe_iff, EReal.coe_lt_coe_iff]
    constructor
    · intro h
      calc y = t⁻¹ * (t * y) := by field_simp
        _ < t⁻¹ * r := mul_lt_mul_of_pos_left h (inv_pos.mpr ht)
    · intro h
      calc t * y < t * (t⁻¹ * r) := mul_lt_mul_of_pos_left h ht
        _ = r := by field_simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- The strict epigraph of an epi-sum is the sum of the strict epigraphs. -/
theorem strictEpigraph_infEpiSum (g h : E → EReal) :
    strictEpigraph (infEpiSum g h) = strictEpigraph g + strictEpigraph h := by
  ext ⟨x, α⟩
  simp only [mem_strictEpigraph, infEpiSum, iInf_lt_iff, infAddition_lt_coe_iff, Set.mem_add]
  constructor
  · rintro ⟨w, r, s, hr, hs, rfl⟩
    exact ⟨(x - w, r), hr, (w, s), hs, by simp⟩
  · rintro ⟨⟨y, r⟩, hr, ⟨w, s⟩, hs, he⟩
    simp only [Prod.mk_add_mk, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨w, r, s, by simpa using hr, hs, rfl⟩

/-- **Exercise 2.24(a)**: the epi-sum `f₁ □ f₂` of convex functions is convex. -/
theorem isConvexRelative_infEpiSum {f₁ f₂ : E → EReal} (h₁ : IsConvexRelative univ f₁)
    (h₂ : IsConvexRelative univ f₂) : IsConvexRelative univ (infEpiSum f₁ f₂) := by
  rw [isConvexRelative_univ_iff_convex_strictEpigraph, strictEpigraph_infEpiSum]
  exact ((isConvexRelative_univ_iff_convex_strictEpigraph _).mp h₁).add
    ((isConvexRelative_univ_iff_convex_strictEpigraph _).mp h₂)

/-- **Exercise 2.24(b)**: the epi-multiple `λ ⋆ f` of a convex function is
convex for `λ > 0`. -/
theorem isConvexRelative_epiMultiplication {f : E → EReal} (hf : IsConvexRelative univ f)
    {lam : ℝ} (hlam : 0 < lam) : IsConvexRelative univ (epiMultiplication lam f) := by
  rw [isConvexRelative_univ_iff, epigraph_epiMultiplication_of_pos hlam]
  exact ((isConvexRelative_univ_iff f).mp hf).smul lam

theorem strictEpigraph_epiMultiplication_of_pos {lam : ℝ} (hlam : 0 < lam) (f : E → EReal) :
    strictEpigraph (epiMultiplication lam f) = lam • strictEpigraph f := by
  ext ⟨x, α⟩
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hlam.ne']
  simp only [mem_strictEpigraph, epiMultiplication, if_pos hlam, Prod.smul_mk, smul_eq_mul]
  exact ereal_coe_mul_lt_coe_iff hlam _ _

omit [NormedSpace ℝ E] in
theorem infEpiSum_indicatorVA_zero_left (g : E → EReal) :
    infEpiSum (indicatorVA {0}) g = g := by
  funext x
  apply le_antisymm
  · refine iInf_le_of_le x ?_
    simp
  · refine le_iInf fun w ↦ ?_
    by_cases hw : x - w = 0
    · rw [sub_eq_zero.mp hw]
      simp
    · simp [indicatorVA, hw]

omit [NormedSpace ℝ E] in
theorem infEpiSum_indicatorVA_zero_right (g : E → EReal) :
    infEpiSum g (indicatorVA {0}) = g := by
  funext x
  apply le_antisymm
  · refine iInf_le_of_le 0 ?_
    simp
  · refine le_iInf fun w ↦ ?_
    by_cases hw : w = 0
    · subst hw
      simp
    · simp [indicatorVA, hw]

omit [NormedSpace ℝ E] in
theorem infEpiSum_top_left (g : E → EReal) : infEpiSum (fun _ ↦ ⊤) g = fun _ ↦ ⊤ := by
  funext x
  simp [infEpiSum]

omit [NormedSpace ℝ E] in
theorem infEpiSum_top_right (g : E → EReal) : infEpiSum g (fun _ ↦ ⊤) = fun _ ↦ ⊤ := by
  funext x
  simp [infEpiSum]

theorem epiMultiplication_zero_of_exists {f : E → EReal} (hdom : ∃ y, f y < ⊤) :
    epiMultiplication 0 f = indicatorVA {0} := by
  simp [epiMultiplication, hdom]

theorem epiMultiplication_zero_of_not_exists {f : E → EReal} (hdom : ¬∃ y, f y < ⊤) :
    epiMultiplication 0 f = fun _ ↦ ⊤ := by
  simp only [epiMultiplication, lt_self_iff_false, if_false, hdom]

theorem epiMultiplication_of_not_exists {f : E → EReal} (hdom : ¬∃ y, f y < ⊤) {lam : ℝ}
    (hlam : 0 < lam) : epiMultiplication lam f = fun _ ↦ ⊤ := by
  push_neg at hdom
  funext x
  simp only [epiMultiplication, if_pos hlam]
  rw [top_le_iff.mp (hdom _), EReal.coe_mul_top_of_pos hlam]

/-- **Exercise 2.24(c)**: for convex `f` and `λ₁, λ₂ ≥ 0`,
`(λ₁ + λ₂) ⋆ f = (λ₁ ⋆ f) □ (λ₂ ⋆ f)`. -/
theorem epiMultiplication_add_eq_infEpiSum {f : E → EReal} (hf : IsConvexRelative univ f)
    {lam₁ lam₂ : ℝ} (h₁ : 0 ≤ lam₁) (h₂ : 0 ≤ lam₂) :
    epiMultiplication (lam₁ + lam₂) f =
      infEpiSum (epiMultiplication lam₁ f) (epiMultiplication lam₂ f) := by
  by_cases hdom : ∃ y, f y < ⊤
  · rcases h₁.eq_or_lt with rfl | h₁'
    · rw [zero_add, epiMultiplication_zero_of_exists hdom, infEpiSum_indicatorVA_zero_left]
    rcases h₂.eq_or_lt with rfl | h₂'
    · rw [add_zero, epiMultiplication_zero_of_exists hdom, infEpiSum_indicatorVA_zero_right]
    apply eq_of_strictEpigraph_eq
    rw [strictEpigraph_infEpiSum, strictEpigraph_epiMultiplication_of_pos (add_pos h₁' h₂'),
      strictEpigraph_epiMultiplication_of_pos h₁', strictEpigraph_epiMultiplication_of_pos h₂']
    exact ((isConvexRelative_univ_iff_convex_strictEpigraph f).mp hf).add_smul h₁ h₂
  · have hall : ∀ lam : ℝ, 0 ≤ lam → epiMultiplication lam f = fun _ ↦ ⊤ := by
      intro lam hlam
      rcases hlam.eq_or_lt with rfl | hpos
      · exact epiMultiplication_zero_of_not_exists hdom
      · exact epiMultiplication_of_not_exists hdom hpos
    rw [hall _ (add_nonneg h₁ h₂), hall _ h₁, infEpiSum_top_left]

end EpiOperations

end RW
