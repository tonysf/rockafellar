/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Normal Constraint Qualification

The common normal-cone constraint qualification in Theorem 6.14 and
Exercise 6.39, stated with an explicit derivative map.
-/

import RockafellarWets.Chapter6.NormalCones
import Mathlib.Analysis.InnerProductSpace.Adjoint

open Set

namespace RW

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The normal constraint qualification of Theorem 6.14: the only target
normal whose negative adjoint image is a source normal is the zero vector.
For constraints `x ∈ X` and `G x ∈ D`, use `A = fderiv ℝ G x` and `u = G x`. -/
def NormalConstraintQualification (X : Set E) (D : Set F) (A : E →L[ℝ] F)
    (x : E) (u : F) : Prop :=
  ∀ y ∈ normalCone D u, -(A.adjoint y) ∈ normalCone X x → y = 0

end RW
