/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3E*: Positive-Semidefinite Matrix Order

This file formalizes Example 3.39 from Rockafellar and Wets,
*Variational Analysis*, using Mathlib's Loewner order on matrices.
-/

import RockafellarWets.Chapter3.Orderings
import Mathlib.Analysis.Matrix.Order

open Filter Topology
open scoped MatrixOrder

namespace RW

variable {n : Type*}

/-- The matrix order in Example 3.39 is exactly the order induced by the
positive-semidefinite cone. -/
theorem matrix_le_iff_sub_posSemidef {A B : Matrix n n ℝ} :
    A ≤ B ↔ (B - A).PosSemidef :=
  Matrix.le_iff

/-- Example 3.39(a): the positive-semidefinite matrix order is reflexive. -/
theorem matrix_le_refl (A : Matrix n n ℝ) : A ≤ A :=
  le_rfl

/-- Example 3.39(b): negation reverses the positive-semidefinite matrix order. -/
theorem matrix_neg_le_neg {A B : Matrix n n ℝ} (hAB : A ≤ B) :
    -B ≤ -A := by
  rw [matrix_le_iff_sub_posSemidef] at hAB ⊢
  simpa only [sub_eq_add_neg, neg_neg, add_comm] using hAB

/-- Example 3.39(c): multiplication by a nonnegative scalar preserves the
positive-semidefinite matrix order. -/
theorem matrix_smul_le_smul {A B : Matrix n n ℝ} {c : ℝ}
    (hAB : A ≤ B) (hc : 0 ≤ c) :
    c • A ≤ c • B := by
  rw [matrix_le_iff_sub_posSemidef] at hAB ⊢
  simpa only [smul_sub] using hAB.smul hc

/-- Example 3.39(d): matrix inequalities add. -/
theorem matrix_add_le_add {A B A' B' : Matrix n n ℝ}
    (hAB : A ≤ B) (hAB' : A' ≤ B') :
    A + A' ≤ B + B' := by
  exact add_le_add hAB hAB'

/-- Example 3.39(f): the positive-semidefinite matrix order is antisymmetric. -/
theorem matrix_le_antisymm {A B : Matrix n n ℝ}
    (hAB : A ≤ B) (hBA : B ≤ A) :
    A = B :=
  le_antisymm hAB hBA

section Limits

variable [Finite n]

/-- Positive semidefiniteness is preserved under limits of finite real
matrices. -/
theorem Matrix.PosSemidef.isClosed_under_tendsto
    {M : ℕ → Matrix n n ℝ} {A : Matrix n n ℝ}
    (hM : Tendsto M atTop (𝓝 A))
    (hpos : ∀ k, (M k).PosSemidef) :
    A.PosSemidef := by
  classical
  letI := Fintype.ofFinite n
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · have hstar :
        Tendsto (fun k => Matrix.conjTranspose (M k)) atTop
          (𝓝 (Matrix.conjTranspose A)) := by
      rw [tendsto_pi_nhds]
      intro i
      rw [tendsto_pi_nhds]
      intro j
      simpa using ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hM j)) i)
    have heq : (fun k => Matrix.conjTranspose (M k)) = M := by
      funext k
      exact (hpos k).isHermitian
    rw [heq] at hstar
    exact tendsto_nhds_unique hstar hM
  · intro x
    have hqContinuous :
        Continuous
          (fun N : Matrix n n ℝ =>
            dotProduct (star x) (Matrix.mulVec N x)) := by
      fun_prop
    have hq :
        Tendsto
          (fun k => dotProduct (star x) (Matrix.mulVec (M k) x))
          atTop
          (𝓝 (dotProduct (star x) (Matrix.mulVec A x))) := by
      exact (hqContinuous.tendsto A).comp hM
    exact isClosed_Ici.mem_of_tendsto hq <|
      Filter.Eventually.of_forall fun k => (hpos k).dotProduct_mulVec_nonneg x

/-- Example 3.39(e): the matrix order is closed under simultaneous limits. -/
theorem matrix_le_of_tendsto
    {A B : ℕ → Matrix n n ℝ} {A₀ B₀ : Matrix n n ℝ}
    (hA : Tendsto A atTop (𝓝 A₀))
    (hB : Tendsto B atTop (𝓝 B₀))
    (hAB : ∀ k, A k ≤ B k) :
    A₀ ≤ B₀ := by
  rw [matrix_le_iff_sub_posSemidef]
  apply Matrix.PosSemidef.isClosed_under_tendsto
      (M := fun k => B k - A k)
  · exact hB.sub hA
  · intro k
    exact (matrix_le_iff_sub_posSemidef.mp (hAB k))

end Limits

end RW
