/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: the coderivative of a strictly continuous single-valued mapping

The remaining statements of **Proposition 9.24(b)**: for `G : E → F` strictly
continuous at `x̄` (finite-dimensional spaces), the coderivative mapping
`D*G(x̄) = coderivative (svSingleton G) x̄ (G x̄)` has nonempty compact values
(`coderivative_svSingleton_nonempty_compact`), is osc and locally bounded
(`coderivative_svSingleton_svOsc_svLocallyBounded`), and has outer norm
`|D*G(x̄)|⁺ = lip G(x̄)` (`svOuterNorm_coderivative_svSingleton`).

The proof combines the scalarization `D*G(x̄)(y) = ∂(yG)(x̄)`
(`coderivative_svSingleton_eq_subdifferential`) with Theorem 9.13 for `yG`
(nonempty compact `∂(yG)(x̄)` and `lip(yG)(x̄) = max |∂(yG)(x̄)|`) and the
scalarization of the modulus in Exercise 9.9.
-/

import RockafellarWets.Chapter9.CoderivativeScalarization
import RockafellarWets.Chapter9.Scalarization
import RockafellarWets.Chapter9.SubgradientModulus
import RockafellarWets.Chapter9.HomogeneousMappingNorms
import RockafellarWets.Chapter8.GraphicalRegularity

open Filter Set Topology Metric
open scoped ENNReal NNReal InnerProductSpace

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
private theorem toReal_inner_coe (y : F) (G : E → F) :
    (fun z ↦ (((⟪y, G z⟫_ℝ : ℝ) : EReal)).toReal) = fun z ↦ ⟪y, G z⟫_ℝ :=
  funext fun _ ↦ EReal.toReal_coe _

omit [InnerProductSpace ℝ E] in
/-- The scalarization `⟪y, G ·⟫` of a strictly continuous mapping is strictly continuous. -/
theorem StrictlyContinuousAt.eRealStrictlyContinuousAt_inner {G : E → F} {x : E}
    (hG : StrictlyContinuousAt G x) (y : F) :
    ERealStrictlyContinuousAt (fun z ↦ ((⟪y, G z⟫_ℝ : ℝ) : EReal)) x := by
  refine ⟨Eventually.of_forall fun _ ↦ by rw [EReal.toReal_coe], ?_⟩
  show lipschitzModulus (fun z ↦ (((⟪y, G z⟫_ℝ : ℝ) : EReal)).toReal) x < ⊤
  rw [toReal_inner_coe]
  exact (lipschitzModulusWithin_inner_le G univ x y).trans_lt
    (ENNReal.mul_lt_top ENNReal.coe_lt_top hG)

variable [FiniteDimensional ℝ E]

/-- **Proposition 9.24(b)**: `D*G(x̄)(y)` is nonempty and compact for every `y`. -/
theorem coderivative_svSingleton_nonempty_compact {G : E → F} {x : E}
    (hG : StrictlyContinuousAt G x) (y : F) :
    (coderivative (svSingleton G) x (G x) y).Nonempty ∧
      IsCompact (coderivative (svSingleton G) x (G x) y) := by
  rw [coderivative_svSingleton_eq_subdifferential hG y]
  exact (hG.eRealStrictlyContinuousAt_inner y).subdifferential_nonempty_compact

variable [FiniteDimensional ℝ F]

/-- **Proposition 9.24(b)**: `|D*G(x̄)|⁺ = lip G(x̄)`. -/
theorem svOuterNorm_coderivative_svSingleton {G : E → F} {x : E}
    (hG : StrictlyContinuousAt G x) :
    svOuterNorm (coderivative (svSingleton G) x (G x)) = lipschitzModulus G x := by
  show svOuterNorm (coderivative (svSingleton G) x (G x)) = lipschitzModulusWithin G univ x
  rw [lipschitzModulusWithin_eq_iSup_ball_inner G univ x]
  unfold svOuterNorm
  refine le_antisymm (iSup₂_le fun y hy ↦ iSup₂_le fun v hv ↦ ?_) (iSup_le fun y ↦ ?_)
  · have hy' : ‖y‖ ≤ 1 := mem_closedBall_zero_iff.1 hy
    rw [coderivative_svSingleton_eq_subdifferential hG y] at hv
    have h1 := (hG.eRealStrictlyContinuousAt_inner y).nnnorm_le_modulus_of_mem_subdifferential hv
    rw [toReal_inner_coe] at h1
    exact h1.trans (le_iSup (fun y : {y : F // ‖y‖ ≤ 1} ↦
      lipschitzModulusWithin (fun z ↦ ⟪y.1, G z⟫_ℝ) univ x) ⟨y, hy'⟩)
  · obtain ⟨v, hv, hmod, -⟩ := (hG.eRealStrictlyContinuousAt_inner y.1).exists_subgradient_norm_eq_modulus
    rw [toReal_inner_coe] at hmod
    rw [← coderivative_svSingleton_eq_subdifferential hG y.1] at hv
    show lipschitzModulus (fun z ↦ ⟪y.1, G z⟫_ℝ) x ≤ _
    rw [hmod]
    exact le_iSup₂_of_le y.1 (mem_closedBall_zero_iff.2 y.2) (le_iSup₂_of_le v hv le_rfl)

/-- **Proposition 9.24(b)**: `D*G(x̄)` is osc and locally bounded. -/
theorem coderivative_svSingleton_svOsc_svLocallyBounded {G : E → F} {x : E}
    (hG : StrictlyContinuousAt G x) :
    SvOsc (coderivative (svSingleton G) x (G x)) ∧
      SvLocallyBounded (coderivative (svSingleton G) x (G x)) := by
  obtain ⟨-, -, ⟨hosc, hph⟩, -⟩ :=
    graphicalDerivative_properties (S := svSingleton G) (x := x) (u := G x) (mem_singleton _)
  refine ⟨hosc, hph.svLocallyBounded_of_svOuterNorm_lt_top ?_⟩
  rw [svOuterNorm_coderivative_svSingleton hG]
  exact hG

end RW
