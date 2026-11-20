/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: Implicit and perturbed solution mappings
-/

import RockafellarWets.Chapter9.AubinProperty

namespace RW

variable {E P F : Type*}

/-- The implicit solution map in Theorem 9.56. The variable pair uses the
Euclidean product so its coderivative has the chapter's Hilbert geometry. -/
def implicitSolutionMapping [Zero F] (S : WithLp 2 (E × P) → Set F) (p : P) : Set E :=
  {x | 0 ∈ S (WithLp.toLp 2 (x,p))}

/-- The perturbed solution map used to reduce implicit mappings to inverse
properties: `T(u,p) = {x | u ∈ S(x,p)}`. -/
def implicitPerturbationMapping (S : WithLp 2 (E × P) → Set F)
    (q : WithLp 2 (F × P)) : Set E :=
  {x | q.fst ∈ S (WithLp.toLp 2 (x,q.snd))}

@[simp] theorem implicitPerturbationMapping_zero [Zero F]
    (S : WithLp 2 (E × P) → Set F) (p : P) :
    implicitPerturbationMapping S (WithLp.toLp 2 (0,p)) = implicitSolutionMapping S p := rfl

end RW
