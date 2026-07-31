/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3D: Coercivity Inherited by Value Functions

This file supplies the final coercivity clauses of Theorem 3.31 in the
project's affine-norm-minorant encoding of Definition 3.25.
-/

import RockafellarWets.Chapter3.Coercivity

open Set EReal

namespace RW

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- A nonnegative-slope affine norm minorant of a parametric integrand passes
to its value function. -/
theorem HasAffineNormLowerBound.valueFunction
    {f : E × F → EReal} {γ β : ℝ}
    (hf : HasAffineNormLowerBound f γ β) (hγ : 0 ≤ γ) :
    HasAffineNormLowerBound (valueFunction f) γ β := by
  intro u
  refine le_iInf fun x => ?_
  have hnorm : ‖u‖ ≤ ‖(x, u)‖ :=
    norm_snd_le (x, u)
  have hreal :
      γ * ‖u‖ + β ≤ γ * ‖(x, u)‖ + β :=
    by
      linarith [mul_le_mul_of_nonneg_left hnorm hγ]
  have hcoe :
      ((γ * ‖u‖ + β : ℝ) : EReal) ≤
        ((γ * ‖(x, u)‖ + β : ℝ) : EReal) := by
    exact_mod_cast hreal
  exact hcoe.trans (hf (x, u))

/-- Theorem 3.31: level coercivity of an integrand is inherited by its
parametric infimum. -/
theorem IsLevelCoercive.valueFunction
    {f : E × F → EReal} (hf : IsLevelCoercive f) :
    IsLevelCoercive (valueFunction f) := by
  rcases hf with ⟨γ, hγ, β, hminor⟩
  exact ⟨γ, hγ, β, hminor.valueFunction hγ.le⟩

/-- Theorem 3.31: coercivity of an integrand is inherited by its parametric
infimum. -/
theorem IsCoercive.valueFunction
    {f : E × F → EReal} (hf : IsCoercive f) :
    IsCoercive (valueFunction f) := by
  intro γ hγ
  rcases hf γ hγ with ⟨β, hminor⟩
  exact ⟨β, hminor.valueFunction hγ.le⟩

end RW
