/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Coderivatives of a graphical derivative
-/

import RockafellarWets.Chapter8.GraphicalRegularity
import RockafellarWets.Chapter6.NormalsToTangentCones

open Set

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- **Exercise 8.44(a)** with the local closedness required by Proposition
6.27(a). The first inclusion holds independently of local closedness. -/
theorem coderivative_graphicalDerivative_subset {S : E → Set F} {x : E} {u : F}
    (hx : u ∈ S x) (hlc : IsLocallyClosedAt (euclideanSvGraph S) (WithLp.toLp 2 (x,u)))
    (w : E) (z y : F) :
    let H := graphicalDerivative S x u
    coderivative H w z y ⊆ coderivative H 0 0 y ∧ coderivative H 0 0 y ⊆ coderivative S x u y := by
  let p := WithLp.toLp 2 (x,u)
  let C := euclideanSvGraph S
  have hp : p ∈ C := hx
  exact ⟨fun _ hv ↦ normalCone_subset_normalCone_zero_of_isCone (isClosed_tangentCone C p)
    (isCone_tangentCone hp) (WithLp.toLp 2 (w,z)) hv,
    fun _ hv ↦ normalCone_tangentCone_subset hp hlc 0 hv⟩

end RW
