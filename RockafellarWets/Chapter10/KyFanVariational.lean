/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Variational sums of the largest eigenvalues

The supremum of the trace on a k-dimensional orthonormal family is a
finite convex function of the operator, including nonsymmetric operators.
-/

import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import RockafellarWets.Chapter9.ConvexLipschitzBounds

open Set
open scoped InnerProductSpace BigOperators

namespace RW
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- First k coordinates, including all coordinates if k exceeds the dimension. -/
def spectralInitialIndices (n k : ℕ) : Finset (Fin n) := Finset.univ.filter (fun i ↦ i.val < k)

/-- Trace of A on the first k vectors of an orthonormal basis. -/
def orthonormalPartialTrace (k : ℕ) (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E)
    (A : E →L[ℝ] E) : ℝ := ∑ i ∈ spectralInitialIndices (Module.finrank ℝ E) k, ⟪b i,A (b i)⟫_ℝ

/-- Variational Ky Fan sum, defined on the full space of operators. -/
def kyFanValue (k : ℕ) (A : E →L[ℝ] E) : ℝ :=
  ⨆ b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E, orthonormalPartialTrace k b A

theorem abs_orthonormalPartialTrace_le (k : ℕ)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E) (A : E →L[ℝ] E) :
    |orthonormalPartialTrace k b A| ≤ (spectralInitialIndices (Module.finrank ℝ E) k).card * ‖A‖ := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ i ∈ spectralInitialIndices (Module.finrank ℝ E) k, ‖A‖ := by
      apply Finset.sum_le_sum
      intro i _
      calc
        |⟪b i,A (b i)⟫_ℝ| ≤ ‖b i‖ * ‖A (b i)‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖b i‖ * (‖A‖ * ‖b i‖) := mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _)
        _ = ‖A‖ := by rw [b.orthonormal.norm_eq_one i]; ring
    _ = _ := by simp

theorem bddAbove_orthonormalPartialTrace (k : ℕ) (A : E →L[ℝ] E) :
    BddAbove (Set.range fun b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E ↦ orthonormalPartialTrace k b A) := by
  refine ⟨(spectralInitialIndices (Module.finrank ℝ E) k).card * ‖A‖,?_⟩
  rintro _ ⟨b,rfl⟩
  exact (le_abs_self _).trans (abs_orthonormalPartialTrace_le k b A)

theorem orthonormalPartialTrace_le_kyFanValue (k : ℕ)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E) (A : E →L[ℝ] E) :
    orthonormalPartialTrace k b A ≤ kyFanValue k A :=
  le_ciSup (bddAbove_orthonormalPartialTrace k A) b

theorem orthonormalPartialTrace_add (k : ℕ)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E) (A B : E →L[ℝ] E) :
    orthonormalPartialTrace k b (A+B) = orthonormalPartialTrace k b A+orthonormalPartialTrace k b B := by
  simp [orthonormalPartialTrace,inner_add_right,Finset.sum_add_distrib]

theorem orthonormalPartialTrace_smul (k : ℕ)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E) (t : ℝ) (A : E →L[ℝ] E) :
    orthonormalPartialTrace k b (t • A) = t * orthonormalPartialTrace k b A := by
  simp [orthonormalPartialTrace,inner_smul_right,Finset.mul_sum]

/-- The convexity used in Examples 2.54 and 10.28. -/
theorem convexOn_kyFanValue (k : ℕ) : ConvexOn ℝ univ (kyFanValue (E := E) k) := by
  letI : Nonempty (OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E) := ⟨stdOrthonormalBasis ℝ E⟩
  refine ⟨convex_univ,?_⟩
  intro A _ B _ t s ht hs _
  change (⨆ b, orthonormalPartialTrace k b (t • A+s • B)) ≤ _
  apply ciSup_le
  intro b
  rw [orthonormalPartialTrace_add,orthonormalPartialTrace_smul,orthonormalPartialTrace_smul]
  exact add_le_add (mul_le_mul_of_nonneg_left (orthonormalPartialTrace_le_kyFanValue k b A) ht)
    (mul_le_mul_of_nonneg_left (orthonormalPartialTrace_le_kyFanValue k b B) hs)

end
end RW
