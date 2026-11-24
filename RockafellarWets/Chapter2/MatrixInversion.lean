/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 2J*: Matrix inversion and the log-determinant

This file formalizes Exercise 2.55, Proposition 2.56 and Exercise 2.57 of
Rockafellar and Wets, *Variational Analysis*.

Matrices are `Matrix ι ι ℝ` over a finite index type `ι` (the book's `n` is
`Fintype.card ι`).  The order `A ≤ B` is Mathlib's Loewner order
(`B - A` positive semidefinite, scope `MatrixOrder`), which is the order 2(14)
used in Chapter 3 (`RockafellarWets.Chapter3.MatrixOrderings`).  The book's
inner product 2(12) is `⟨A, B⟩ = tr (A B)`.

* `two_mul_dotProduct_sub_le_inv`: the variational formula
  `⟨x, A⁻¹ x⟩ = max_y (2⟨x, y⟩ - ⟨y, A y⟩)` behind Proposition 2.56.
* `matrix_inversion_convexity` (Proposition 2.56): the positive-definite
  matrices form a convex set, open relative to the symmetric matrices, and
  inversion is convex and order-inverting in the Loewner order.
* `logDetFunction_concave_usc_gradient` (Exercise 2.55): `j = log ∘ det` on
  positive-definite matrices (`-∞` elsewhere) is concave and usc, and where
  finite it is differentiable with gradient `A⁻¹` (Jacobi's formula
  `fderiv_log_det_apply`).  The guide's inequalities are
  `card_le_trace_sub_log_det` and `log_det_add_log_det_le` with their
  equality cases.
* `convex_functions_of_posDef_matrices` (Exercise 2.57, adapted): `f ↦ f ∘ J`
  matches nondecreasing with nonincreasing functions and carries convex
  nondecreasing `f` to convex nonincreasing `g`.  The book's claim that this
  is a one-to-one correspondence between the two convex classes is false:
  `convex_antitone_not_convex_comp_inv` (`g(B) = -tr B`).  The example 2(15)
  is `traceInvSup_convex_antitone`.
-/

import RockafellarWets.Chapter2.ConvexFunctions
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

open Set Filter Topology Matrix
open scoped MatrixOrder

namespace RW

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Quadratic forms of real symmetric matrices -/

omit [DecidableEq ι] in
/-- Over `ℝ`, positive semidefiniteness is symmetry plus nonnegativity of the
quadratic form `x ⬝ᵥ M *ᵥ x`. -/
theorem posSemidef_iff_real {M : Matrix ι ι ℝ} :
    M.PosSemidef ↔ M.IsSymm ∧ ∀ x : ι → ℝ, 0 ≤ x ⬝ᵥ (M *ᵥ x) := by
  rw [posSemidef_iff_dotProduct_mulVec]
  simp only [star_trivial]
  exact Iff.rfl

omit [DecidableEq ι] in
/-- The bilinear form of a symmetric matrix is symmetric. -/
theorem dotProduct_mulVec_comm_of_isSymm {A : Matrix ι ι ℝ} (hA : A.IsSymm) (u v : ι → ℝ) :
    u ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (A *ᵥ u) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hA.eq, dotProduct_comm]

theorem PosDef.isUnit_det_real {A : Matrix ι ι ℝ} (hA : A.PosDef) : IsUnit A.det :=
  (isUnit_iff_isUnit_det A).mp hA.isUnit

/-- The variational formula behind Proposition 2.56: for positive-definite `A`,
`2⟨x, y⟩ - ⟨y, A y⟩ ≤ ⟨x, A⁻¹ x⟩` for every `y`. -/
theorem two_mul_dotProduct_sub_le_inv {A : Matrix ι ι ℝ} (hA : A.PosDef) (x y : ι → ℝ) :
    2 * (x ⬝ᵥ y) - y ⬝ᵥ (A *ᵥ y) ≤ x ⬝ᵥ (A⁻¹ *ᵥ x) := by
  have hu := PosDef.isUnit_det_real hA
  have hS : A.IsSymm := hA.isHermitian
  obtain ⟨w, rfl⟩ : ∃ w, x = A *ᵥ w := ⟨A⁻¹ *ᵥ x, by
    rw [mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]⟩
  rw [mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]
  have h0 : 0 ≤ (w - y) ⬝ᵥ (A *ᵥ (w - y)) := by
    simpa using hA.posSemidef.dotProduct_mulVec_nonneg (w - y)
  have key := dotProduct_mulVec_comm_of_isSymm hS w y
  simp only [mulVec_sub, dotProduct_sub, sub_dotProduct] at h0
  rw [dotProduct_comm (A *ᵥ w) y, dotProduct_comm (A *ᵥ w) w]
  linarith

/-- The maximum in `two_mul_dotProduct_sub_le_inv` is attained at `y = A⁻¹ x`. -/
theorem two_mul_dotProduct_sub_inv {A : Matrix ι ι ℝ} (hA : A.PosDef) (x : ι → ℝ) :
    2 * (x ⬝ᵥ (A⁻¹ *ᵥ x)) - (A⁻¹ *ᵥ x) ⬝ᵥ (A *ᵥ (A⁻¹ *ᵥ x)) = x ⬝ᵥ (A⁻¹ *ᵥ x) := by
  have hu := PosDef.isUnit_det_real hA
  rw [mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec, dotProduct_comm (A⁻¹ *ᵥ x) x]
  ring

/-! ### Proposition 2.56 -/

omit [Fintype ι] [DecidableEq ι] in
/-- The positive-definite matrices form a convex set. -/
theorem convex_posDef : Convex ℝ {A : Matrix ι ι ℝ | A.PosDef} := by
  rw [convex_iff_forall_pos]
  intro A hA B hB a b ha hb _
  exact (PosDef.smul hA ha).add (PosDef.smul hB hb)

omit [Fintype ι] [DecidableEq ι] in
/-- The positive-definite matrices form an open subset of the symmetric
matrices: near a positive-definite matrix every symmetric matrix is positive
definite. -/
theorem eventually_posDef_of_isSymm [Finite ι] {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    ∀ᶠ B in 𝓝 A, B.IsSymm → B.PosDef := by
  haveI := Fintype.ofFinite ι
  have hK : IsCompact (Metric.sphere (0 : ι → ℝ) 1) := isCompact_sphere 0 1
  have hcont : Continuous (fun p : Matrix ι ι ℝ × (ι → ℝ) ↦ p.2 ⬝ᵥ (p.1 *ᵥ p.2)) := by
    fun_prop
  have hev := hK.eventually_forall_of_forall_eventually (x₀ := A)
    (P := fun B x ↦ 0 < x ⬝ᵥ (B *ᵥ x)) fun x hx ↦ by
      have hx0 : x ≠ 0 := by
        rintro rfl
        simp at hx
      have hpos : 0 < x ⬝ᵥ (A *ᵥ x) := by
        simpa using hA.dotProduct_mulVec_pos hx0
      exact hcont.continuousAt.eventually (lt_mem_nhds hpos)
  filter_upwards [hev] with B hB hBs
  refine PosDef.of_dotProduct_mulVec_pos hBs fun x hx ↦ ?_
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hu : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : ι → ℝ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have h := hB _ hu
  rw [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul] at h
  have h' : 0 < x ⬝ᵥ (B *ᵥ x) := by
    have := (mul_pos_iff_of_pos_left (inv_pos.mpr hn)).mp h
    exact (mul_pos_iff_of_pos_left (inv_pos.mpr hn)).mp this
  simpa using h'

omit [Fintype ι] [DecidableEq ι] in
/-- The positive-definite matrices are open relative to the symmetric
matrices. -/
theorem eventually_nhdsWithin_isSymm_posDef [Finite ι] {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    ∀ᶠ B in 𝓝[{B : Matrix ι ι ℝ | B.IsSymm}] A, B.PosDef := by
  filter_upwards [nhdsWithin_le_nhds (eventually_posDef_of_isSymm hA),
    self_mem_nhdsWithin] with B hB hBs using hB hBs

omit [DecidableEq ι] in
/-- Loewner comparison of two symmetric matrices through their quadratic
forms. -/
theorem le_of_dotProduct_mulVec_le {A B : Matrix ι ι ℝ} (hA : A.IsSymm) (hB : B.IsSymm)
    (h : ∀ x : ι → ℝ, x ⬝ᵥ (A *ᵥ x) ≤ x ⬝ᵥ (B *ᵥ x)) : A ≤ B := by
  rw [Matrix.le_iff, posSemidef_iff_real]
  refine ⟨hB.sub hA, fun x ↦ ?_⟩
  rw [sub_mulVec, dotProduct_sub]
  linarith [h x]

omit [DecidableEq ι] in
theorem dotProduct_mulVec_le_of_le {A B : Matrix ι ι ℝ} (h : A ≤ B) (x : ι → ℝ) :
    x ⬝ᵥ (A *ᵥ x) ≤ x ⬝ᵥ (B *ᵥ x) := by
  rw [Matrix.le_iff, posSemidef_iff_real] at h
  have := h.2 x
  rw [sub_mulVec, dotProduct_sub] at this
  linarith

/-- **Proposition 2.56** (order inversion, one direction): `A₀ ⪰ A₁` implies
`A₀⁻¹ ⪯ A₁⁻¹`. -/
theorem inv_le_inv_of_le {A₀ A₁ : Matrix ι ι ℝ} (h₀ : A₀.PosDef) (h₁ : A₁.PosDef)
    (h : A₁ ≤ A₀) : A₀⁻¹ ≤ A₁⁻¹ := by
  refine le_of_dotProduct_mulVec_le h₀.inv.isHermitian h₁.inv.isHermitian fun x ↦ ?_
  have e := two_mul_dotProduct_sub_inv h₀ x
  have hle := dotProduct_mulVec_le_of_le h (A₀⁻¹ *ᵥ x)
  have hmax := two_mul_dotProduct_sub_le_inv h₁ x (A₀⁻¹ *ᵥ x)
  linarith

/-- **Proposition 2.56** (order inversion): for positive-definite matrices,
`A₀ ⪰ A₁ ⟺ A₀⁻¹ ⪯ A₁⁻¹`. -/
theorem le_iff_inv_le_inv {A₀ A₁ : Matrix ι ι ℝ} (h₀ : A₀.PosDef) (h₁ : A₁.PosDef) :
    A₁ ≤ A₀ ↔ A₀⁻¹ ≤ A₁⁻¹ := by
  refine ⟨inv_le_inv_of_le h₀ h₁, fun h ↦ ?_⟩
  have := inv_le_inv_of_le h₁.inv h₀.inv h
  rwa [nonsing_inv_nonsing_inv _ (PosDef.isUnit_det_real h₁),
    nonsing_inv_nonsing_inv _ (PosDef.isUnit_det_real h₀)] at this

/-- **Proposition 2.56** (convexity of inversion in the Loewner order):
`(a A₀ + b A₁)⁻¹ ⪯ a A₀⁻¹ + b A₁⁻¹` for `a, b ≥ 0`, `a + b = 1`. -/
theorem inv_convexCombination_le {A₀ A₁ : Matrix ι ι ℝ} (h₀ : A₀.PosDef) (h₁ : A₁.PosDef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a • A₀ + b • A₁)⁻¹ ≤ a • A₀⁻¹ + b • A₁⁻¹ := by
  have hP : (a • A₀ + b • A₁).PosDef := convex_posDef h₀ h₁ ha hb hab
  refine le_of_dotProduct_mulVec_le hP.inv.isHermitian
    (IsSymm.add (IsSymm.smul h₀.inv.isHermitian a) (IsSymm.smul h₁.inv.isHermitian b))
    fun x ↦ ?_
  set y := (a • A₀ + b • A₁)⁻¹ *ᵥ x
  have e := two_mul_dotProduct_sub_inv hP x
  have m₀ := two_mul_dotProduct_sub_le_inv h₀ x y
  have m₁ := two_mul_dotProduct_sub_le_inv h₁ x y
  simp only [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
    smul_eq_mul] at e ⊢
  have hb' : b = 1 - a := by linarith
  subst hb'
  nlinarith [mul_le_mul_of_nonneg_left m₀ ha, mul_le_mul_of_nonneg_left m₁ hb]

/-- **Proposition 2.56**: the set `P` of positive-definite matrices is convex
and open relative to the symmetric matrices; the inversion `J(A) = A⁻¹` maps
`P` into `P`, is convex with respect to `⪰`, and is order-inverting. -/
theorem matrix_inversion_convexity :
    Convex ℝ {A : Matrix ι ι ℝ | A.PosDef} ∧
    (∀ A : Matrix ι ι ℝ, A.PosDef → ∀ᶠ B in 𝓝[{B : Matrix ι ι ℝ | B.IsSymm}] A, B.PosDef) ∧
    (∀ A : Matrix ι ι ℝ, A.PosDef → A⁻¹.PosDef) ∧
    (∀ A₀ A₁ : Matrix ι ι ℝ, A₀.PosDef → A₁.PosDef → ∀ τ : ℝ, 0 < τ → τ < 1 →
      ((1 - τ) • A₀ + τ • A₁)⁻¹ ≤ (1 - τ) • A₀⁻¹ + τ • A₁⁻¹) ∧
    (∀ A₀ A₁ : Matrix ι ι ℝ, A₀.PosDef → A₁.PosDef → (A₁ ≤ A₀ ↔ A₀⁻¹ ≤ A₁⁻¹)) :=
  ⟨convex_posDef, fun _ hA ↦ eventually_nhdsWithin_isSymm_posDef hA, fun _ hA ↦ hA.inv,
    fun _ _ h₀ h₁ _ hτ0 hτ1 ↦
      inv_convexCombination_le h₀ h₁ (by linarith) hτ0.le (by ring),
    fun _ _ h₀ h₁ ↦ le_iff_inv_le_inv h₀ h₁⟩

/-! ### Exercise 2.55 -/

/-- Guide to Exercise 2.55: `tr C - log (det C) ≥ n` for positive-definite `C`. -/
theorem card_le_trace_sub_log_det {C : Matrix ι ι ℝ} (hC : C.PosDef) :
    (Fintype.card ι : ℝ) ≤ C.trace - Real.log C.det := by
  have htr := hC.isHermitian.trace_eq_sum_eigenvalues
  have hdet := hC.isHermitian.det_eq_prod_eigenvalues
  have hpos := hC.eigenvalues_pos
  simp only [RCLike.ofReal_real_eq_id, id] at htr hdet
  rw [htr, hdet, Real.log_prod fun i _ ↦ (hpos i).ne', ← Finset.sum_sub_distrib]
  calc (Fintype.card ι : ℝ) = ∑ _i : ι, (1 : ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum fun i _ ↦ by linarith [Real.log_le_sub_one_of_pos (hpos i)]

/-- Guide to Exercise 2.55: equality holds in `card_le_trace_sub_log_det` only
for `C = I`. -/
theorem trace_sub_log_det_eq_card_iff {C : Matrix ι ι ℝ} (hC : C.PosDef) :
    C.trace - Real.log C.det = Fintype.card ι ↔ C = 1 := by
  refine ⟨fun h ↦ ?_, by rintro rfl; simp⟩
  have htr := hC.isHermitian.trace_eq_sum_eigenvalues
  have hdet := hC.isHermitian.det_eq_prod_eigenvalues
  have hpos := hC.eigenvalues_pos
  simp only [RCLike.ofReal_real_eq_id, id] at htr hdet
  rw [htr, hdet, Real.log_prod fun i _ ↦ (hpos i).ne', ← Finset.sum_sub_distrib] at h
  have hsum : ∑ i, (hC.isHermitian.eigenvalues i -
      Real.log (hC.isHermitian.eigenvalues i) - 1) = 0 := by
    rw [Finset.sum_sub_distrib, h]
    simp
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ by
    linarith [Real.log_le_sub_one_of_pos (hpos i)]).mp hsum
  have he : ∀ i, hC.isHermitian.eigenvalues i = 1 := fun i ↦ by
    by_contra hne
    linarith [Real.log_lt_sub_one_of_pos (hpos i) hne, hz i (Finset.mem_univ _)]
  have hspec := hC.isHermitian.spectral_theorem
  have hd : (RCLike.ofReal ∘ hC.isHermitian.eigenvalues : ι → ℝ) = fun _ ↦ 1 := by
    funext i
    simp [he i]
  rw [hd, diagonal_one, map_one] at hspec
  exact hspec

/-- The congruence `C = S B S` with `S = A^{1/2}` used in the guide to
Exercise 2.55. -/
theorem exists_sqrt_congruence {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    ∃ S : Matrix ι ι ℝ, S.PosDef ∧ S * S = A ∧ (S * B * S).PosDef ∧
      (S * B * S).trace = (A * B).trace ∧
      Real.log (S * B * S).det = Real.log A.det + Real.log B.det := by
  set S := CFC.sqrt A
  have hS : S.PosDef := hA.isStrictlyPositive.sqrt.posDef
  have hSS : S * S = A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  have hC : (S * B * S).PosDef := by
    have := hB.conjTranspose_mul_mul_same (mulVec_injective_iff_isUnit.mpr hS.isUnit)
    rwa [hS.isHermitian.eq] at this
  refine ⟨S, hS, hSS, hC, by rw [trace_mul_cycle, hSS], ?_⟩
  have hdet : (S * B * S).det = A.det * B.det := by
    rw [← hSS, det_mul, det_mul, det_mul]
    ring
  rw [hdet, Real.log_mul hA.det_pos.ne' hB.det_pos.ne']

/-- Guide to Exercise 2.55: `log (det A) + log (det B) ≤ ⟨A, B⟩ - n` for
positive-definite `A`, `B`, where `⟨A, B⟩ = tr (A B)` is 2(12). -/
theorem log_det_add_log_det_le {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    Real.log A.det + Real.log B.det ≤ (A * B).trace - Fintype.card ι := by
  obtain ⟨S, -, -, hC, htr, hlog⟩ := exists_sqrt_congruence hA hB
  have := card_le_trace_sub_log_det hC
  rw [htr, hlog] at this
  linarith

/-- Guide to Exercise 2.55: equality holds in `log_det_add_log_det_le` if and
only if `B = A⁻¹`. -/
theorem log_det_add_log_det_eq_iff {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    Real.log A.det + Real.log B.det = (A * B).trace - Fintype.card ι ↔ B = A⁻¹ := by
  have hu := PosDef.isUnit_det_real hA
  constructor
  · intro h
    obtain ⟨S, hS, hSS, hC, htr, hlog⟩ := exists_sqrt_congruence hA hB
    have h1 : S * B * S = 1 := by
      rw [← trace_sub_log_det_eq_card_iff hC, htr, hlog]
      linarith
    have hSu := PosDef.isUnit_det_real hS
    have hcalc : S⁻¹ * (S * B * S) * S⁻¹ = B := by
      simp only [Matrix.mul_assoc]
      rw [mul_nonsing_inv _ hSu, Matrix.mul_one, nonsing_inv_mul_cancel_left _ _ hSu]
    rw [← hcalc, h1, Matrix.mul_one, ← hSS, Matrix.mul_inv_rev]
  · rintro rfl
    rw [mul_nonsing_inv _ hu, trace_one, ← Real.log_mul hA.det_pos.ne' hA.inv.det_pos.ne',
      ← det_mul, mul_nonsing_inv _ hu, det_one, Real.log_one]
    ring

/-- Concavity of `log det` on the positive-definite matrices, in the form of
the inequality behind Exercise 2.55. -/
theorem log_det_convexCombination_ge {A₀ A₁ : Matrix ι ι ℝ} (h₀ : A₀.PosDef) (h₁ : A₁.PosDef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * Real.log A₀.det + b * Real.log A₁.det ≤ Real.log (a • A₀ + b • A₁).det := by
  have hP := convex_posDef h₀ h₁ ha hb hab
  have hPu := PosDef.isUnit_det_real hP
  have i₀ := log_det_add_log_det_le h₀ hP.inv
  have i₁ := log_det_add_log_det_le h₁ hP.inv
  have hsum : a • (A₀ * (a • A₀ + b • A₁)⁻¹) + b • (A₁ * (a • A₀ + b • A₁)⁻¹) = 1 := by
    rw [← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.add_mul, mul_nonsing_inv _ hPu]
  have htr : a * (A₀ * (a • A₀ + b • A₁)⁻¹).trace + b * (A₁ * (a • A₀ + b • A₁)⁻¹).trace =
      Fintype.card ι := by
    have := congrArg trace hsum
    rwa [trace_add, trace_smul, trace_smul, trace_one, smul_eq_mul, smul_eq_mul] at this
  have hinv : Real.log (a • A₀ + b • A₁)⁻¹.det = -Real.log (a • A₀ + b • A₁).det := by
    rw [det_nonsing_inv, Ring.inverse_eq_inv', Real.log_inv]
  rw [hinv] at i₀ i₁
  have hb' : b = 1 - a := by linarith
  subst hb'
  nlinarith [mul_le_mul_of_nonneg_left i₀ ha, mul_le_mul_of_nonneg_left i₁ hb]

/-- `log det` is concave on the convex set of positive-definite matrices. -/
theorem concaveOn_log_det :
    ConcaveOn ℝ {A : Matrix ι ι ℝ | A.PosDef} (fun A ↦ Real.log A.det) :=
  ⟨convex_posDef, fun _ h₀ _ h₁ _ _ ha hb hab ↦ by
    simpa only [smul_eq_mul] using log_det_convexCombination_ge h₀ h₁ ha hb hab⟩

open Classical in
/-- The function `j` of Exercise 2.55: `log (det A)` when `A` is positive
definite and `-∞` otherwise. -/
noncomputable def logDetFunction (A : Matrix ι ι ℝ) : EReal :=
  if A.PosDef then ((Real.log A.det : ℝ) : EReal) else ⊥

theorem logDetFunction_of_posDef {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    logDetFunction A = ((Real.log A.det : ℝ) : EReal) := by
  simp [logDetFunction, hA]

theorem logDetFunction_of_not_posDef {A : Matrix ι ι ℝ} (hA : ¬A.PosDef) :
    logDetFunction A = ⊥ := by
  simp [logDetFunction, hA]

theorem logDetFunction_ne_top (A : Matrix ι ι ℝ) : logDetFunction A ≠ ⊤ := by
  by_cases hA : A.PosDef
  · simp [logDetFunction_of_posDef hA]
  · simp [logDetFunction_of_not_posDef hA]

/-- `j` is finite exactly on the positive-definite matrices. -/
theorem logDetFunction_ne_bot_iff {A : Matrix ι ι ℝ} : logDetFunction A ≠ ⊥ ↔ A.PosDef := by
  by_cases hA : A.PosDef
  · simp [logDetFunction_of_posDef hA, hA]
  · simp [logDetFunction_of_not_posDef hA, hA]

/-- **Exercise 2.55** (concavity): `j` is concave on the whole matrix space,
in particular on the symmetric matrices. -/
theorem isConcaveRelative_logDetFunction :
    IsConcaveRelative (univ : Set (Matrix ι ι ℝ)) logDetFunction := by
  unfold IsConcaveRelative
  rw [isConvexRelative_iff_lt convex_univ]
  intro A₀ _ A₁ _ α₀ α₁ h₀ h₁ τ hτ0 hτ1
  have hP₀ : A₀.PosDef := by
    by_contra h
    rw [logDetFunction_of_not_posDef h] at h₀
    simp at h₀
  have hP₁ : A₁.PosDef := by
    by_contra h
    rw [logDetFunction_of_not_posDef h] at h₁
    simp at h₁
  rw [logDetFunction_of_posDef hP₀, ← EReal.coe_neg, EReal.coe_lt_coe_iff] at h₀
  rw [logDetFunction_of_posDef hP₁, ← EReal.coe_neg, EReal.coe_lt_coe_iff] at h₁
  have hc := log_det_convexCombination_ge hP₀ hP₁ (a := 1 - τ) (b := τ) (by linarith)
    hτ0.le (by ring)
  rw [logDetFunction_of_posDef (convex_posDef hP₀ hP₁ (by linarith) hτ0.le (by ring)),
    ← EReal.coe_neg, EReal.coe_le_coe_iff]
  nlinarith

omit [Fintype ι] [DecidableEq ι] in
/-- The positive-semidefinite matrices form a closed set. -/
theorem isClosed_posSemidef [Finite ι] : IsClosed {A : Matrix ι ι ℝ | A.PosSemidef} := by
  haveI := Fintype.ofFinite ι
  have : {A : Matrix ι ι ℝ | A.PosSemidef} =
      {A | Aᵀ = A} ∩ ⋂ x : ι → ℝ, {A | 0 ≤ x ⬝ᵥ (A *ᵥ x)} := by
    ext A
    simp only [mem_setOf_eq, mem_inter_iff, mem_iInter, posSemidef_iff_real]
    rfl
  rw [this]
  exact (isClosed_eq continuous_id.matrix_transpose continuous_id).inter
    (isClosed_iInter fun x ↦ isClosed_le continuous_const (by fun_prop))

/-- **Exercise 2.55** (upper semicontinuity): `j` is usc on the whole matrix
space. -/
theorem upperSemicontinuous_logDetFunction :
    UpperSemicontinuous (logDetFunction : Matrix ι ι ℝ → EReal) := by
  rw [upperSemicontinuous_iff_isClosed_preimage]
  intro y
  induction y using EReal.rec with
  | bot => simp
  | top =>
    convert isClosed_empty
    ext A
    simp [logDetFunction_ne_top]
  | coe r =>
    have : logDetFunction ⁻¹' Ici (r : EReal) =
        {A : Matrix ι ι ℝ | A.PosSemidef} ∩ {A | Real.exp r ≤ A.det} := by
      ext A
      simp only [mem_preimage, mem_Ici, mem_inter_iff, mem_setOf_eq]
      constructor
      · intro h
        have hP : A.PosDef := by
          by_contra hn
          rw [logDetFunction_of_not_posDef hn] at h
          simp at h
        rw [logDetFunction_of_posDef hP, EReal.coe_le_coe_iff] at h
        exact ⟨hP.posSemidef, (Real.le_log_iff_exp_le hP.det_pos).mp h⟩
      · rintro ⟨hS, hle⟩
        have hdet : 0 < A.det := (Real.exp_pos r).trans_le hle
        have hP : A.PosDef := hS.posDef_iff_isUnit.mpr
          ((isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hdet.ne'))
        rw [logDetFunction_of_posDef hP, EReal.coe_le_coe_iff]
        exact (Real.le_log_iff_exp_le hdet).mpr hle
    rw [this]
    exact isClosed_posSemidef.inter (isClosed_le continuous_const continuous_id.matrix_det)

/-- Where `j` is finite it agrees near `A`, relative to the symmetric
matrices, with the real function `log ∘ det`. -/
theorem logDetFunction_eventuallyEq {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    logDetFunction =ᶠ[𝓝[{B : Matrix ι ι ℝ | B.IsSymm}] A]
      fun B ↦ ((Real.log B.det : ℝ) : EReal) := by
  filter_upwards [eventually_nhdsWithin_isSymm_posDef hA] with B hB
  exact logDetFunction_of_posDef hB

section Derivative

open scoped Matrix.Norms.Elementwise

/-- The determinant is differentiable (it is a polynomial in the entries). -/
theorem differentiable_det : Differentiable ℝ (fun M : Matrix ι ι ℝ ↦ M.det) := by
  simp_rw [det_apply]
  fun_prop

/-- `d/dr det (I + r M) = tr M` at `r = 0`. -/
theorem hasDerivAt_det_one_add_smul (M : Matrix ι ι ℝ) :
    HasDerivAt (fun r : ℝ ↦ (1 + r • M).det) M.trace 0 := by
  have h := Polynomial.hasDerivAt (det (1 + (Polynomial.X : Polynomial ℝ) •
    M.map Polynomial.C)) 0
  rw [derivative_det_one_add_X_smul] at h
  convert h using 1
  funext r
  simp [eval_det, ← smul_eq_mul_diagonal]

/-- Jacobi's formula along lines: `d/dt det (A + t H) = det A · tr (A⁻¹ H)` at
`t = 0`. -/
theorem hasDerivAt_det_add_smul {A : Matrix ι ι ℝ} (hA : IsUnit A.det) (H : Matrix ι ι ℝ) :
    HasDerivAt (fun t : ℝ ↦ (A + t • H).det) (A.det * (A⁻¹ * H).trace) 0 := by
  have h1 := (hasDerivAt_det_one_add_smul (A⁻¹ * H)).const_mul A.det
  convert h1 using 1
  funext t
  rw [← det_mul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul,
    mul_nonsing_inv_cancel_left _ _ hA]

/-- Jacobi's formula: the derivative of `det` at an invertible `A` is
`H ↦ det A · tr (A⁻¹ H)`. -/
theorem fderiv_det_apply {A : Matrix ι ι ℝ} (hA : IsUnit A.det) (H : Matrix ι ι ℝ) :
    fderiv ℝ (fun B : Matrix ι ι ℝ ↦ B.det) A H = A.det * (A⁻¹ * H).trace := by
  have hd := (differentiable_det (ι := ι) A).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ ↦ A + t • H) H 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const H).const_add A
  have hcomp := hd.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  exact hcomp.unique (hasDerivAt_det_add_smul hA H)

/-- `log ∘ det` is differentiable wherever `det ≠ 0`. -/
theorem differentiableAt_log_det {A : Matrix ι ι ℝ} (hA : A.det ≠ 0) :
    DifferentiableAt ℝ (fun B : Matrix ι ι ℝ ↦ Real.log B.det) A :=
  (differentiable_det A).log hA

/-- **Exercise 2.55** (gradient): the derivative of `log ∘ det` at `A` is
`H ↦ tr (A⁻¹ H) = ⟨A⁻¹, H⟩`, i.e. `∇ j(A) = A⁻¹` for the inner product 2(12). -/
theorem fderiv_log_det_apply {A : Matrix ι ι ℝ} (hA : A.det ≠ 0) (H : Matrix ι ι ℝ) :
    fderiv ℝ (fun B : Matrix ι ι ℝ ↦ Real.log B.det) A H = (A⁻¹ * H).trace := by
  rw [((differentiable_det A).hasFDerivAt.log hA).fderiv, ContinuousLinearMap.smul_apply,
    fderiv_det_apply (isUnit_iff_ne_zero.mpr hA), smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ hA, one_mul]

/-- **Exercise 2.55**: on the symmetric matrices, `j(A) = log (det A)` for
positive-definite `A` and `-∞` otherwise is concave and usc; where it is
finite it coincides near `A` (relative to the symmetric matrices) with
`log ∘ det`, which is differentiable with gradient `A⁻¹` for the inner
product `⟨A, B⟩ = tr (A B)` of 2(12). -/
theorem logDetFunction_concave_usc_gradient :
    IsConcaveRelative {A : Matrix ι ι ℝ | A.IsSymm} logDetFunction ∧
    UpperSemicontinuousOn logDetFunction {A : Matrix ι ι ℝ | A.IsSymm} ∧
    ∀ A : Matrix ι ι ℝ, A.IsSymm → logDetFunction A ≠ ⊥ →
      A.PosDef ∧
      logDetFunction =ᶠ[𝓝[{B : Matrix ι ι ℝ | B.IsSymm}] A]
        (fun B ↦ ((Real.log B.det : ℝ) : EReal)) ∧
      DifferentiableAt ℝ (fun B : Matrix ι ι ℝ ↦ Real.log B.det) A ∧
      ∀ H, fderiv ℝ (fun B : Matrix ι ι ℝ ↦ Real.log B.det) A H = (A⁻¹ * H).trace := by
  refine ⟨IsConvexRelative.mono isConcaveRelative_logDetFunction (subset_univ _),
    upperSemicontinuous_logDetFunction.upperSemicontinuousOn _, fun A _ hA ↦ ?_⟩
  have hP := logDetFunction_ne_bot_iff.mp hA
  exact ⟨hP, logDetFunction_eventuallyEq hP, differentiableAt_log_det hP.det_pos.ne',
    fderiv_log_det_apply hP.det_pos.ne'⟩

end Derivative

/-! ### Exercise 2.57 -/

omit [DecidableEq ι] in
/-- `A ↦ tr (C A Cᵀ) = ⟨Cᵀ C, A⟩` is nondecreasing in the Loewner order. -/
theorem trace_mul_mul_transpose_mono {κ : Type*} [Fintype κ] (C : Matrix κ ι ℝ)
    {A₀ A₁ : Matrix ι ι ℝ} (h : A₀ ≤ A₁) :
    (C * A₀ * Cᵀ).trace ≤ (C * A₁ * Cᵀ).trace := by
  rw [Matrix.le_iff] at h
  have := (h.mul_mul_conjTranspose_same C).trace_nonneg
  rw [conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub, Matrix.sub_mul, trace_sub] at this
  linarith

/-- **Exercise 2.57** (valid direction): if `f` is convex and nondecreasing on
the positive-definite matrices `P`, then `g(B) = f(B⁻¹)` is convex and
nonincreasing on `P`. -/
theorem convexOn_antitoneOn_comp_inv {f : Matrix ι ι ℝ → ℝ}
    (hf : ConvexOn ℝ {A : Matrix ι ι ℝ | A.PosDef} f)
    (hmono : MonotoneOn f {A : Matrix ι ι ℝ | A.PosDef}) :
    ConvexOn ℝ {B : Matrix ι ι ℝ | B.PosDef} (fun B ↦ f B⁻¹) ∧
      AntitoneOn (fun B ↦ f B⁻¹) {B : Matrix ι ι ℝ | B.PosDef} := by
  refine ⟨⟨convex_posDef, fun B₀ h₀ B₁ h₁ a b ha hb hab ↦ ?_⟩,
    fun B₀ h₀ B₁ h₁ hle ↦ hmono h₁.inv h₀.inv (inv_le_inv_of_le h₁ h₀ hle)⟩
  have hP : (a • B₀ + b • B₁).PosDef := convex_posDef h₀ h₁ ha hb hab
  have hQ : (a • B₀⁻¹ + b • B₁⁻¹).PosDef := convex_posDef h₀.inv h₁.inv ha hb hab
  calc f (a • B₀ + b • B₁)⁻¹ ≤ f (a • B₀⁻¹ + b • B₁⁻¹) :=
        hmono hP.inv hQ (inv_convexCombination_le h₀ h₁ ha hb hab)
    _ ≤ a • f B₀⁻¹ + b • f B₁⁻¹ := hf.2 h₀.inv h₁.inv ha hb hab

/-- Exercise 2.57: the relations `f(A) = g(A⁻¹)` and `g(B) = f(B⁻¹)` on `P`
are equivalent. -/
theorem comp_inv_correspondence {f g : Matrix ι ι ℝ → ℝ} :
    (∀ A : Matrix ι ι ℝ, A.PosDef → f A = g A⁻¹) ↔
      ∀ B : Matrix ι ι ℝ, B.PosDef → g B = f B⁻¹ := by
  constructor
  · intro h B hB
    rw [h _ hB.inv, nonsing_inv_nonsing_inv _ (PosDef.isUnit_det_real hB)]
  · intro h A hA
    rw [h _ hA.inv, nonsing_inv_nonsing_inv _ (PosDef.isUnit_det_real hA)]

/-- Exercise 2.57: `f` is nondecreasing on `P` if and only if
`g(B) = f(B⁻¹)` is nonincreasing on `P`. -/
theorem monotoneOn_iff_antitoneOn_comp_inv {f : Matrix ι ι ℝ → ℝ} :
    MonotoneOn f {A : Matrix ι ι ℝ | A.PosDef} ↔
      AntitoneOn (fun B ↦ f B⁻¹) {B : Matrix ι ι ℝ | B.PosDef} := by
  refine ⟨fun h B₀ h₀ B₁ h₁ hle ↦ h h₁.inv h₀.inv (inv_le_inv_of_le h₁ h₀ hle),
    fun h A₀ h₀ A₁ h₁ hle ↦ ?_⟩
  have := h h₁.inv h₀.inv (inv_le_inv_of_le h₁ h₀ hle)
  simpa only [nonsing_inv_nonsing_inv _ (PosDef.isUnit_det_real h₀),
    nonsing_inv_nonsing_inv _ (PosDef.isUnit_det_real h₁)] using this

theorem inv_smul_one {c : ℝ} (hc : c ≠ 0) : (c • (1 : Matrix ι ι ℝ))⁻¹ = c⁻¹ • 1 :=
  inv_eq_left_inv (by rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, inv_mul_cancel₀ hc, one_smul])

/-- **Exercise 2.57** (correction): the converse direction fails, so the
relations do not give a one-to-one correspondence between the convex
nondecreasing `f` and the convex nonincreasing `g`.  The function
`g(B) = -tr B` is convex and nonincreasing on `P`, but `f(A) = g(A⁻¹) =
-tr A⁻¹` is not convex on `P` (for `n ≥ 1`). -/
theorem convex_antitone_not_convex_comp_inv [Nonempty ι] :
    ConvexOn ℝ {B : Matrix ι ι ℝ | B.PosDef} (fun B ↦ -B.trace) ∧
    AntitoneOn (fun B : Matrix ι ι ℝ ↦ -B.trace) {B : Matrix ι ι ℝ | B.PosDef} ∧
    ¬ConvexOn ℝ {A : Matrix ι ι ℝ | A.PosDef} (fun A ↦ -(A⁻¹).trace) := by
  refine ⟨⟨convex_posDef, fun B₀ _ B₁ _ a b _ _ _ ↦ le_of_eq ?_⟩,
    fun B₀ _ B₁ _ hle ↦ ?_, fun hc ↦ ?_⟩
  · simp only [trace_add, trace_smul, smul_eq_mul]
    ring
  · have := (Matrix.le_iff.mp hle).trace_nonneg
    rw [trace_sub] at this
    simp only [neg_le_neg_iff]
    linarith
  · have h3 : ((3 : ℝ) • (1 : Matrix ι ι ℝ)).PosDef := PosDef.one.smul (by norm_num)
    have key := hc.2 PosDef.one h3 (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    have hmid : (1 / 2 : ℝ) • (1 : Matrix ι ι ℝ) + (1 / 2 : ℝ) • ((3 : ℝ) • 1) =
        (2 : ℝ) • 1 := by
      rw [smul_smul, ← add_smul]
      norm_num
    simp only at key
    rw [hmid, inv_smul_one (by norm_num), inv_smul_one (by norm_num), inv_one] at key
    simp only [trace_smul, trace_one, smul_eq_mul] at key
    have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    linarith

/-- The function 2(15): `g(B) = sup_{C ∈ S} tr (C B⁻¹ Cᵀ)`, with values in
`(-∞, ∞]`. -/
noncomputable def traceInvSup {κ : Type*} [Fintype κ] (S : Set (Matrix κ ι ℝ))
    (B : Matrix ι ι ℝ) : EReal :=
  ⨆ C ∈ S, (((C * B⁻¹ * Cᵀ).trace : ℝ) : EReal)

omit [DecidableEq ι] in
/-- The two expressions in 2(15): `tr (C B⁻¹ Cᵀ) = ⟨Cᵀ C, B⁻¹⟩`. -/
theorem trace_mul_inv_mul_transpose {κ : Type*} [Fintype κ] (C : Matrix κ ι ℝ)
    (M : Matrix ι ι ℝ) : (C * M * Cᵀ).trace = (Cᵀ * C * M).trace :=
  trace_mul_cycle C M Cᵀ

/-- Each `B ↦ tr (C B⁻¹ Cᵀ)` is convex and nonincreasing on `P`. -/
theorem convexOn_antitoneOn_trace_conj_inv {κ : Type*} [Fintype κ] (C : Matrix κ ι ℝ) :
    ConvexOn ℝ {B : Matrix ι ι ℝ | B.PosDef} (fun B ↦ (C * B⁻¹ * Cᵀ).trace) ∧
      AntitoneOn (fun B ↦ (C * B⁻¹ * Cᵀ).trace) {B : Matrix ι ι ℝ | B.PosDef} :=
  convexOn_antitoneOn_comp_inv (f := fun A ↦ (C * A * Cᵀ).trace)
    ⟨convex_posDef, fun _ _ _ _ _ _ _ _ _ ↦ le_of_eq (by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, trace_add,
        trace_smul, smul_eq_mul])⟩
    fun _ _ _ _ h ↦ trace_mul_mul_transpose_mono C h

/-- **Exercise 2.57** (example 2(15)): for any set `S` of matrices,
`g(B) = sup_{C ∈ S} tr (C B⁻¹ Cᵀ)` is convex and nonincreasing on `P`. -/
theorem traceInvSup_convex_antitone {κ : Type*} [Fintype κ] (S : Set (Matrix κ ι ℝ)) :
    IsConvexRelative {B : Matrix ι ι ℝ | B.PosDef} (traceInvSup S) ∧
      AntitoneOn (traceInvSup S) {B : Matrix ι ι ℝ | B.PosDef} := by
  constructor
  · rw [isConvexRelative_iff_lt convex_posDef]
    intro B₀ h₀ B₁ h₁ α₀ α₁ hα₀ hα₁ τ hτ0 hτ1
    refine iSup₂_le fun C hC ↦ ?_
    have hc := (convexOn_antitoneOn_trace_conj_inv C).1.2 h₀ h₁
      (by linarith : (0 : ℝ) ≤ 1 - τ) hτ0.le (by ring)
    have e₀ : (C * B₀⁻¹ * Cᵀ).trace < α₀ := by
      have := (le_iSup₂ (f := fun C (_ : C ∈ S) ↦
        (((C * B₀⁻¹ * Cᵀ).trace : ℝ) : EReal)) C hC).trans_lt hα₀
      exact_mod_cast this
    have e₁ : (C * B₁⁻¹ * Cᵀ).trace < α₁ := by
      have := (le_iSup₂ (f := fun C (_ : C ∈ S) ↦
        (((C * B₁⁻¹ * Cᵀ).trace : ℝ) : EReal)) C hC).trans_lt hα₁
      exact_mod_cast this
    simp only [smul_eq_mul] at hc
    have : (C * ((1 - τ) • B₀ + τ • B₁)⁻¹ * Cᵀ).trace ≤ (1 - τ) * α₀ + τ * α₁ := by
      nlinarith [mul_le_mul_of_nonneg_left e₀.le (by linarith : (0 : ℝ) ≤ 1 - τ),
        mul_le_mul_of_nonneg_left e₁.le hτ0.le]
    exact_mod_cast this
  · intro B₀ h₀ B₁ h₁ hle
    exact iSup₂_mono fun C _ ↦
      EReal.coe_le_coe_iff.mpr ((convexOn_antitoneOn_trace_conj_inv C).2 h₀ h₁ hle)

/-- **Exercise 2.57** (adapted): on the positive-definite matrices `P`, the
relations `f(A) = g(A⁻¹)`, `g(B) = f(B⁻¹)` are equivalent, they match the
nondecreasing `f` exactly with the nonincreasing `g`, and they carry convex
nondecreasing `f` to convex nonincreasing `g`.  (The converse of the last
clause fails: `convex_antitone_not_convex_comp_inv`.) -/
theorem convex_functions_of_posDef_matrices :
    (∀ f g : Matrix ι ι ℝ → ℝ, (∀ A : Matrix ι ι ℝ, A.PosDef → f A = g A⁻¹) ↔
      ∀ B : Matrix ι ι ℝ, B.PosDef → g B = f B⁻¹) ∧
    (∀ f : Matrix ι ι ℝ → ℝ, MonotoneOn f {A : Matrix ι ι ℝ | A.PosDef} ↔
      AntitoneOn (fun B ↦ f B⁻¹) {B : Matrix ι ι ℝ | B.PosDef}) ∧
    (∀ f : Matrix ι ι ℝ → ℝ, ConvexOn ℝ {A : Matrix ι ι ℝ | A.PosDef} f →
      MonotoneOn f {A : Matrix ι ι ℝ | A.PosDef} →
        ConvexOn ℝ {B : Matrix ι ι ℝ | B.PosDef} (fun B ↦ f B⁻¹) ∧
          AntitoneOn (fun B ↦ f B⁻¹) {B : Matrix ι ι ℝ | B.PosDef}) :=
  ⟨fun _ _ ↦ comp_inv_correspondence, fun _ ↦ monotoneOn_iff_antitoneOn_comp_inv,
    fun _ hf hmono ↦ convexOn_antitoneOn_comp_inv hf hmono⟩

end RW
