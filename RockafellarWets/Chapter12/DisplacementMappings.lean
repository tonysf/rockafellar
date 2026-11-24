/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: Displacement mappings

Exercise 12.16: for a nonexpansive `F : ℝⁿ → ℝⁿ`, the displacement mapping
`I - F` is maximal monotone.

Monotonicity is the Cauchy–Schwarz estimate
`⟪(x₁ - F x₁) - (x₀ - F x₀), x₁ - x₀⟫ ≥ |x₁ - x₀|² - |F x₁ - F x₀| |x₁ - x₀| ≥ 0`,
and maximality then follows from continuity by Example 12.7.  The book's guide
routes the argument through 12.11 and 12.15; the direct argument proves the
same statement.  The book's suggested auxiliary mapping
`T₀ = (I - F)⁻¹ ∘ 2I - I` is the mapping that 12.11 attaches to `F`.  The
second theorem below shows it is maximal monotone, through the
correspondence of 12.11 and Theorem 12.12.
-/

import RockafellarWets.Chapter12.ContinuousMaximality
import RockafellarWets.Chapter12.ResolventMaximality

open Set
open scoped InnerProductSpace Pointwise

namespace RW

section Displacement

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The displacement mapping `I - F` of a nonexpansive mapping is monotone. -/
theorem svMonotone_displacement {F : E → E} (hF : LipschitzWith 1 F) :
    SvMonotone (fun x ↦ ({x - F x} : Set E)) := by
  refine svMonotone_singleton_iff.2 fun x₀ x₁ ↦ ?_
  have e : (x₁ - F x₁) - (x₀ - F x₀) = (x₁ - x₀) - (F x₁ - F x₀) := by abel
  rw [e, inner_sub_left, real_inner_self_eq_norm_sq]
  have hcs := real_inner_le_norm (F x₁ - F x₀) (x₁ - x₀)
  have hlip : ‖F x₁ - F x₀‖ ≤ ‖x₁ - x₀‖ := by
    simpa [dist_eq_norm] using hF.dist_le_mul x₁ x₀
  nlinarith [norm_nonneg (x₁ - x₀), norm_nonneg (F x₁ - F x₀)]

/-- **Exercise 12.16 (displacement mappings).** For a nonexpansive mapping
`F`, the displacement mapping `I - F` is maximal monotone. -/
theorem svMaximalMonotone_displacement {F : E → E} (hF : LipschitzWith 1 F) :
    SvMaximalMonotone (fun x ↦ ({x - F x} : Set E)) :=
  svMaximalMonotone_singleton_of_continuous (continuous_id.sub hF.continuous)
    (svMonotone_displacement hF)

/-- The auxiliary mapping `T₀ = (I - F)⁻¹ ∘ 2I - I` of the guide to 12.16 is
the mapping attached to `F` by Proposition 12.11, and it is maximal monotone. -/
theorem svMaximalMonotone_svCayleyInv_of_lipschitz [FiniteDimensional ℝ E] {F : E → E}
    (hF : LipschitzWith 1 F) :
    SvMaximalMonotone (svCayleyInv (fun z ↦ ({F z} : Set E))) ∧
      svCayleyInv (fun z ↦ ({F z} : Set E)) =
        fun x ↦ svInv (fun z ↦ ({z} : Set E) - {F z}) ((2 : ℝ) • x) - {x} := by
  set T₀ := svCayleyInv (fun z ↦ ({F z} : Set E)) with hT₀
  have hmono : SvMonotone T₀ := svMonotone_svCayleyInv_iff.2 (svNonexpansive_singleton_iff.2 hF)
  refine ⟨svMaximalMonotone_of_svDom_svResolvent hmono one_pos ?_, svCayleyInv_eq _⟩
  rw [← svDom_svCayley, hT₀, svCayley_svCayleyInv]
  exact eq_univ_of_forall fun z ↦ ⟨F z, mem_singleton _⟩

end Displacement

end RW
