/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Equivalent nonsingularity criteria for strict inverse mappings
-/

import RockafellarWets.Chapter9.ClassicalImplicitCriteria
import RockafellarWets.Chapter9.InverseLocalizationModuli

open Set
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → E} {x : E} {A : E →L[ℝ] E}

/-- **Corollary 9.55**, the equivalence of coderivative nonsingularity with
classical nonsingularity when the mapping is strictly differentiable. -/
theorem coderivative_nonsingular_iff_bijective_of_hasStrictFDerivAt
    (hf : HasStrictFDerivAt f A x) :
    (∀ y, 0 ∈ coderivative (svSingleton f) x (f x) y → y = 0) ↔ Function.Bijective A := by
  rw [coderivative_singleton_of_hasStrictFDerivAt hf]
  have he : (∀ y, 0 ∈ svSingleton A.adjoint y → y = 0) ↔
      (∀ y, A.adjoint y = 0 → y = 0) := by simp only [svSingleton,mem_singleton_iff,eq_comm]
  rw [he,adjoint_kernel_zero_iff_bijective]

/-- In the classical strict case, coderivative nonsingularity is both
necessary and sufficient for a single-valued Lipschitz inverse localization. -/
theorem hasLipschitzInverseLocalization_iff_coderivative_nonsingular_of_hasStrictFDerivAt
    (hf : HasStrictFDerivAt f A x) :
    HasLipschitzSingleValuedLocalization (svInv (svSingleton f)) (f x) x ↔
      ∀ y, 0 ∈ coderivative (svSingleton f) x (f x) y → y = 0 := by
  rw [coderivative_nonsingular_iff_bijective_of_hasStrictFDerivAt hf]
  exact hasLipschitzInverseLocalization_iff_bijective_of_hasStrictFDerivAt hf

/-- The scalarization form of the necessary nonsingularity condition in9.55. -/
theorem IsLipschitzSingleValuedLocalization.scalarized_inverse_nonsingular
    {g : E → E} (h : IsLipschitzSingleValuedLocalization (svInv (svSingleton f)) (f x) x g)
    (hf : StrictlyContinuousAt f x) :
    ∀ y, 0 ∈ subdifferential (fun a ↦ ((⟪y,f a⟫_ℝ : ℝ) : EReal)) x → y = 0 := by
  intro y hy
  apply h.inverse_coderivative_nonsingular y
  rwa [coderivative_svSingleton_eq_subdifferential hf y]

end RW
