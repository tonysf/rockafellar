/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Semidifferentiability of ordered eigenvalues

Example 10.28. The Ky Fan difference gives a total scalar function on all
operators; on symmetric operators it is exactly the ordered eigenvalue.
-/

import RockafellarWets.Chapter10.KyFanSpectralTrace
import RockafellarWets.Chapter10.ConvexFiniteSemiderivatives
import RockafellarWets.Chapter9.SmoothLipschitzModulus

open Set
open scoped InnerProductSpace Topology
namespace RW
noncomputable section
variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

def orderedEigenvalue (i : Fin (Module.finrank ℝ E)) (A : E →L[ℝ] E) : ℝ :=
  kyFanValue (i.val+1) A-kyFanValue i.val A

theorem orderedEigenvalue_eq (i : Fin (Module.finrank ℝ E))
    (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric) :
    orderedEigenvalue i A = hA.eigenvalues rfl i := (eigenvalue_eq_kyFan_difference A hA i).symm

theorem semidifferentiableAt_orderedEigenvalue (i : Fin (Module.finrank ℝ E)) (A : E →L[ℝ] E) :
    SemidifferentiableAt (fun B ↦ (orderedEigenvalue i B:EReal)) A := by
  change SemidifferentiableAt (fun B : E →L[ℝ] E ↦ ((kyFanValue (i.val+1) B-kyFanValue i.val B:ℝ):EReal)) A
  exact semidifferentiableAt_convex_difference (E := E →L[ℝ] E)
    (f := kyFanValue (E := E) (i.val+1)) (g := kyFanValue (E := E) i.val)
    (convexOn_kyFanValue (E := E) (i.val+1)) (convexOn_kyFanValue (E := E) i.val) A

theorem strictlyContinuousAt_orderedEigenvalue (i : Fin (Module.finrank ℝ E)) (A : E →L[ℝ] E) :
    StrictlyContinuousAt (orderedEigenvalue i) A := by
  change StrictlyContinuousAt (fun B : E →L[ℝ] E ↦ kyFanValue (i.val+1) B-kyFanValue i.val B) A
  exact strictlyContinuousAt_convex_difference (E := E →L[ℝ] E)
    (f := kyFanValue (E := E) (i.val+1)) (g := kyFanValue (E := E) i.val)
    (convexOn_kyFanValue (E := E) (i.val+1)) (convexOn_kyFanValue (E := E) i.val) A

/-- **Example 10.28**: smooth dependence of the operator implies strict
continuity and semidifferentiability of every ordered eigenvalue. -/
theorem orderedEigenvalue_contDiffOn {A : P → E →L[ℝ] E} {O : Set P}
    (hO : IsOpen O) (hA : ContDiffOn ℝ 1 A O) (i : Fin (Module.finrank ℝ E))
    {x : P} (hx : x ∈ O) :
    StrictlyContinuousAt (fun y ↦ orderedEigenvalue i (A y)) x ∧
      SemidifferentiableAt (fun y ↦ (orderedEigenvalue i (A y):EReal)) x := by
  have h := hA.contDiffAt (hO.mem_nhds hx)
  constructor
  · exact (lipschitzModulus_comp_le (strictlyContinuousAt_of_contDiffAt h)
      (strictlyContinuousAt_orderedEigenvalue i (A x))).trans_lt
      (ENNReal.mul_lt_top (strictlyContinuousAt_orderedEigenvalue i (A x)) (strictlyContinuousAt_of_contDiffAt h))
  · exact (semidifferentiableAt_orderedEigenvalue i (A x)).comp_hasFDerivAt
      (h.differentiableAt (by norm_num)).hasFDerivAt

/-- The same statement using Mathlib's eigenvalues, with their decreasing
order and algebraic multiplicities supplied by the spectral theorem. -/
theorem symmetric_eigenvalues_contDiffOn {A : P → E →L[ℝ] E} {O : Set P}
    (hO : IsOpen O) (hA : ContDiffOn ℝ 1 A O) (hsym : ∀ y, (A y).toLinearMap.IsSymmetric)
    (i : Fin (Module.finrank ℝ E)) {x : P} (hx : x ∈ O) :
    StrictlyContinuousAt (fun y ↦ (hsym y).eigenvalues rfl i) x ∧
      SemidifferentiableAt (fun y ↦ ((hsym y).eigenvalues rfl i:EReal)) x := by
  simpa only [orderedEigenvalue_eq i _ (hsym _)] using orderedEigenvalue_contDiffOn hO hA i hx

end
end RW
