/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: Monotonicity of differentiable mappings

Proposition 12.3: a differentiable mapping `F : ℝⁿ → ℝⁿ` is monotone if and
only if each Jacobian `∇F(x)`, not necessarily symmetric, is positive
semidefinite.  It is strictly monotone if every `∇F(x)` is positive definite,
but this condition is only sufficient.

The necessity proof passes to the limit in the difference quotients
`τ⁻¹⟪F(x + τw) - F(x), w⟫ ≥ 0` as `τ ↘ 0`.  Sufficiency and the strict case
integrate the derivative of `φ(τ) = ⟪x₁ - x₀, F(xτ)⟫` along the segment
`xτ = x₀ + τ(x₁ - x₀)`.  The cube `x ↦ x³` on `ℝ` is strictly monotone while its
derivative vanishes at `0`, so positive definiteness is not necessary.
-/

import RockafellarWets.Chapter12.MonotoneMappings
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Calculus

open Set Filter Topology
open scoped InnerProductSpace

namespace RW

section Differentiable

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The derivative of `τ ↦ ⟪u, F(x + τw)⟫`. -/
theorem hasDerivAt_inner_comp_line {F : E → E} (hF : Differentiable ℝ F) (x w u : E) (t : ℝ) :
    HasDerivAt (fun t : ℝ ↦ ⟪u, F (x + t • w)⟫_ℝ) ⟪u, fderiv ℝ F (x + t • w) w⟫_ℝ t :=
  (innerSL ℝ u).hasFDerivAt.comp_hasDerivAt t
    ((hF _).hasFDerivAt.comp_hasDerivAt t (by
      simpa only [id_eq, one_smul] using ((hasDerivAt_id t).smul_const w).const_add x))

/-- **Proposition 12.3.** A differentiable mapping is monotone if and only if
its Jacobian is positive semidefinite at every point. -/
theorem svMonotone_singleton_iff_fderiv {F : E → E} (hF : Differentiable ℝ F) :
    SvMonotone (fun x ↦ ({F x} : Set E)) ↔ ∀ x w, 0 ≤ ⟪w, fderiv ℝ F x w⟫_ℝ := by
  rw [svMonotone_singleton_iff]
  constructor
  · intro h x w
    have hd := hasDerivAt_inner_comp_line hF x w w 0
    rw [zero_smul, add_zero] at hd
    refine ge_of_tendsto hd.tendsto_slope_zero_right
      (eventually_nhdsWithin_of_forall fun t (ht : 0 < t) ↦ ?_)
    have hmono := h x (x + t • w)
    rw [show x + t • w - x = t • w by abel, real_inner_smul_right, real_inner_comm,
      inner_sub_right] at hmono
    simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
    have hnn : 0 ≤ ⟪w, F (x + t • w)⟫_ℝ - ⟪w, F x⟫_ℝ := (mul_nonneg_iff_of_pos_left ht).1 hmono
    exact mul_nonneg (inv_nonneg.2 ht.le) hnn
  · intro h x₀ x₁
    have hm : Monotone (fun t : ℝ ↦ ⟪x₁ - x₀, F (x₀ + t • (x₁ - x₀))⟫_ℝ) :=
      monotone_of_hasDerivAt_nonneg (hasDerivAt_inner_comp_line hF x₀ (x₁ - x₀) (x₁ - x₀))
        fun t ↦ h _ _
    have h01 := hm (zero_le_one' ℝ)
    simp only [zero_smul, add_zero, one_smul, add_sub_cancel] at h01
    rw [real_inner_comm, inner_sub_right]
    linarith

/-- **Proposition 12.3**, strict monotonicity: positive definite Jacobians at
every point make a differentiable mapping strictly monotone. -/
theorem svStrictlyMonotone_singleton_of_fderiv {F : E → E} (hF : Differentiable ℝ F)
    (h : ∀ x w, w ≠ 0 → 0 < ⟪w, fderiv ℝ F x w⟫_ℝ) :
    SvStrictlyMonotone (fun x ↦ ({F x} : Set E)) := by
  rw [svStrictlyMonotone_singleton_iff]
  intro x₀ x₁ hne
  have hw : x₁ - x₀ ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  have hm : StrictMono (fun t : ℝ ↦ ⟪x₁ - x₀, F (x₀ + t • (x₁ - x₀))⟫_ℝ) :=
    strictMono_of_hasDerivAt_pos (hasDerivAt_inner_comp_line hF x₀ (x₁ - x₀) (x₁ - x₀))
      fun t ↦ h _ _ hw
  have h01 := hm (zero_lt_one' ℝ)
  simp only [zero_smul, add_zero, one_smul, add_sub_cancel] at h01
  rw [real_inner_comm, inner_sub_right]
  linarith

/-- **Proposition 12.3**, the converse fails for strict monotonicity: the cube
on `ℝ` is strictly monotone, while its derivative at `0` is not positive
definite. -/
theorem cube_strictlyMonotone_not_posDef :
    SvStrictlyMonotone (fun x : ℝ ↦ ({x ^ 3} : Set ℝ)) ∧ Differentiable ℝ (fun x : ℝ ↦ x ^ 3) ∧
      ¬ ∀ x w : ℝ, w ≠ 0 → 0 < ⟪w, fderiv ℝ (fun x : ℝ ↦ x ^ 3) x w⟫_ℝ := by
  refine ⟨svStrictlyMonotone_singleton_iff.2 fun x₀ x₁ hne ↦ ?_, by fun_prop, fun h ↦ ?_⟩
  · simp only [RCLike.inner_apply, conj_trivial]
    have hd : x₁ - x₀ ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
    have hq : 0 < x₁ ^ 2 + x₁ * x₀ + x₀ ^ 2 := by
      rcases eq_or_ne x₀ 0 with h0 | h0
      · subst h0
        have : x₁ ≠ 0 := by simpa using hd
        nlinarith [sq_pos_of_ne_zero this]
      · nlinarith [sq_nonneg (x₁ + x₀ / 2), sq_pos_of_ne_zero h0]
    have e : (x₁ - x₀) * (x₁ ^ 3 - x₀ ^ 3) = (x₁ - x₀) ^ 2 * (x₁ ^ 2 + x₁ * x₀ + x₀ ^ 2) := by
      ring
    rw [e]
    exact mul_pos (sq_pos_of_ne_zero hd) hq
  · have h0 := h 0 1 one_ne_zero
    have hderiv : fderiv ℝ (fun x : ℝ ↦ x ^ 3) 0 1 = 0 := by
      rw [fderiv_eq_smul_deriv]
      simp
    rw [hderiv, inner_zero_right] at h0
    exact lt_irrefl _ h0

end Differentiable

end RW
