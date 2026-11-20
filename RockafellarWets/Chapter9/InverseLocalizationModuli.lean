/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Sharp moduli of inverse localizations
-/

import RockafellarWets.Chapter9.LocalizationDerivatives
import RockafellarWets.Chapter9.InverseCoderivatives

open Filter Metric Set Topology
open scoped NNReal ENNReal

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {S : E → Set F} {x : E} {u : F} {g : F → E}

/-- **Theorems 9.54(b) and 9.55**: both inverse norms equal the sharp branch modulus. -/
theorem IsLipschitzSingleValuedLocalization.inverse_norms
    (h : IsLipschitzSingleValuedLocalization (svInv S) u x g) :
    lipschitzModulus g u = svOuterNorm (svInv (strictGraphicalDerivative S x u)) ∧
    lipschitzModulus g u = svOuterNorm (svInv (coderivative S x u)) := by
  constructor
  · rw [← h.strictDerivative_norm,strictGraphicalDerivative_svInv]
  · rw [← h.coderivative_norm,svOuterNorm_coderivative_inverse]

/-- Local single-valued Lipschitz inversion forces coderivative nonsingularity. -/
theorem IsLipschitzSingleValuedLocalization.inverse_coderivative_nonsingular
    (h : IsLipschitzSingleValuedLocalization (svInv S) u x g) :
    ∀ y, 0 ∈ coderivative S x u y → y = 0 := by
  intro y hy
  have hm : -y ∈ coderivative (svInv S) u x 0 := by
    rw [mem_coderivative_inverse_iff]
    simpa only [neg_zero,neg_neg] using hy
  rw [h.coderivative_zero,mem_singleton_iff] at hm
  exact neg_eq_zero.mp hm

end RW
