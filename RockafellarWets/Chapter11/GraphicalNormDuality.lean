/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Norm duality for graphical derivatives
-/
import RockafellarWets.Chapter11.SublinearNormDuality
import RockafellarWets.Chapter9.InverseCoderivatives

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The first graphical-regularity specialization in Example 11.29. -/
theorem IsGraphicallyRegularAt.coderivative_norm_eq_innerNorm {S : E → Set F}
    {x : E} {u : F} (hr : IsGraphicallyRegularAt S x u) (hu : u ∈ S x) :
    svOuterNorm (coderivative S x u) = svInnerNorm (graphicalDerivative S x u) := by
  rw [((isGraphicallyRegularAt_iff_adjoints hu hr.1).1.mp hr)]
  exact (sublinear_adjoint_norm_duality (hr.sublinear hu).1 (graphicalDerivative_properties hu).1.1).2.2.1.symm

/-- The inverse graphical-regularity specialization in Example 11.29. -/
theorem IsGraphicallyRegularAt.inverse_coderivative_norm_eq_innerNorm {S : E → Set F}
    {x : E} {u : F} (hr : IsGraphicallyRegularAt S x u) (hu : u ∈ S x) :
    svOuterNorm (svInv (coderivative S x u)) = svInnerNorm (svInv (graphicalDerivative S x u)) := by
  have h := ((isGraphicallyRegularAt_svInv_iff hu).mpr hr).coderivative_norm_eq_innerNorm
    (show x ∈ svInv S u from hu)
  rwa [svOuterNorm_coderivative_inverse,graphicalDerivative_svInv] at h

end RW
