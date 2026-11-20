/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Smooth symmetric matrix families
-/
import RockafellarWets.Chapter10.EigenvalueSemidifferentiability
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Spectrum

open Set
open scoped Matrix.Norms.Elementwise
namespace RW
noncomputable section

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Matrix-to-operator map with the entrywise norm on the matrix space. -/
def matrixEuclideanOperator (m : ℕ) : Matrix (Fin m) (Fin m) ℝ →L[ℝ]
    (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) :=
  ((Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv.toLinearMap).toContinuousLinearMap

/-- **Example 10.28**, with smoothness stated separately for every matrix entry.
Eigenvalues are listed in decreasing order, with multiplicity. -/
theorem matrix_orderedEigenvalue_contDiffOn {m : ℕ}
    {A : P → Matrix (Fin m) (Fin m) ℝ} {O : Set P}
    (hO : IsOpen O) (hA : ∀ i j, ContDiffOn ℝ 1 (fun x ↦ A x i j) O)
    (i : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin m))))
    {x : P} (hx : x ∈ O) :
    StrictlyContinuousAt (fun y ↦ orderedEigenvalue i (matrixEuclideanOperator m (A y))) x ∧
      SemidifferentiableAt (fun y ↦ (orderedEigenvalue i (matrixEuclideanOperator m (A y)):EReal)) x := by
  have hmat : ContDiffOn ℝ 1 A O := contDiffOn_pi.mpr (fun i ↦ contDiffOn_pi.mpr (hA i))
  exact orderedEigenvalue_contDiffOn hO ((matrixEuclideanOperator m).contDiff.comp_contDiffOn hmat) i hx

theorem matrix_orderedEigenvalue_eq {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    (hA : A.IsHermitian) (i : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin m)))) :
    orderedEigenvalue i (matrixEuclideanOperator m A) =
      (Matrix.isHermitian_iff_isSymmetric.mp hA).eigenvalues rfl i :=
  orderedEigenvalue_eq i (matrixEuclideanOperator m A) (Matrix.isHermitian_iff_isSymmetric.mp hA)

/-- **Example 10.28** for a matrix family defined smoothly and symmetrically
only on the specified open set. The chosen eigenvalue functions agree there
with the decreasing spectral list, including repetitions. -/
theorem symmetric_matrix_eigenvalues_semidifferentiable {m : ℕ}
    {A : P → Matrix (Fin m) (Fin m) ℝ} {O : Set P}
    (hO : IsOpen O) (hA : ∀ i j, ContDiffOn ℝ 1 (fun x ↦ A x i j) O)
    (hsym : ∀ y ∈ O, (A y).IsHermitian)
    (i : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin m)))) :
    ∃ l : P → ℝ,
      (∀ y (hy : y ∈ O), l y = (Matrix.isHermitian_iff_isSymmetric.mp (hsym y hy)).eigenvalues rfl i) ∧
      ∀ x ∈ O, StrictlyContinuousAt l x ∧ SemidifferentiableAt (fun y ↦ (l y:EReal)) x := by
  refine ⟨fun y ↦ orderedEigenvalue i (matrixEuclideanOperator m (A y)),?_,?_⟩
  · intro y hy
    exact matrix_orderedEigenvalue_eq (A y) (hsym y hy) i
  · intro x hx
    exact matrix_orderedEigenvalue_contDiffOn hO hA i hx

end
end RW
