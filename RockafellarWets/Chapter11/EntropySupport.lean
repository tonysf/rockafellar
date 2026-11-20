/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Support of the log-exponential sublevel set
-/

import RockafellarWets.Chapter11.EntropyConjugacy
import RockafellarWets.Chapter8.SupportCorrespondence

open Set
open scoped InnerProductSpace

namespace RW

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- **Example 11.12**. The support of the zero sublevel set of log-sum-exp
is the homogeneous entropy from Exercise 3.51. This includes the origin,
vectors with vanishing coordinates, and the infinite values outside the
nonnegative orthant. -/
theorem supportFunction_logSumExp_sublevel :
    supportFunction {x : EuclideanSpace ℝ ι | logSumExp x ≤ 0} =
      fun y ↦ homogeneousEntropy (WithLp.ofLp y) := by
  let H := fun y : EuclideanSpace ℝ ι ↦ homogeneousEntropy (WithLp.ofLp y)
  have hset : {x : EuclideanSpace ℝ ι | logSumExp x ≤ 0} = linearMinorantSet H := by
    ext x
    have hdual := fenchelConjugate_le_coe_iff
      (fun y : EuclideanSpace ℝ ι ↦ simplexEntropy (WithLp.ofLp y)) x 0
    rw [fenchelConjugate_simplexEntropy] at hdual
    simp only [sub_zero,EReal.coe_le_coe_iff] at hdual
    change logSumExp x ≤ 0 ↔ ∀ y, (⟪x,y⟫_ℝ : EReal) ≤ H y
    rw [hdual]
    constructor
    · intro h y
      let l (z : ι → ℝ) : EReal := (⟪x,WithLp.toLp 2 z⟫_ℝ : EReal)
      have hhom : PositivelyHomogeneous l := by
        refine ⟨?_,fun z c _ ↦ ?_⟩
        · change (⟪x,0⟫_ℝ : EReal) < ⊤
          exact EReal.coe_lt_top _
        · change (⟪x,c • WithLp.toLp 2 z⟫_ℝ : EReal) = (c : EReal) * (⟪x,WithLp.toLp 2 z⟫_ℝ : EReal)
          rw [real_inner_smul_right,EReal.coe_mul]
      have hle : l ≤ simplexEntropy := fun z ↦ h (WithLp.toLp 2 z)
      change l (WithLp.ofLp y) ≤ homogeneousEntropy (WithLp.ofLp y)
      rw [homogeneousEntropy_eq_positiveHullFunction_simplexEntropy]
      exact le_positiveHullFunction_of_positivelyHomogeneous_of_le hhom hle (WithLp.ofLp y)
    · intro h y
      exact (h y).trans ((homogeneousEntropy_le_positiveHullFunction_simplexEntropy _).trans
        (positiveHullFunction_le_apply _ _))
  rw [hset]
  apply supportFunction_linearMinorantSet (h := H)
  · have h := sublinear_homogeneousEntropy (ι := ι)
    exact ⟨⟨h.1.1,fun _ _ hc ↦ h.1.2 hc⟩,fun x y ↦ h.2 (WithLp.ofLp x) (WithLp.ofLp y)⟩
  · exact lowerSemicontinuous_homogeneousEntropy.comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℝ)).continuous
  · obtain ⟨⟨y,hy⟩,hb⟩ := homogeneousEntropy_isProper (ι := ι)
    exact ⟨⟨WithLp.toLp 2 y,hy⟩,fun x ↦ hb (WithLp.ofLp x)⟩

end RW
