/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: Exact moduli for smooth and affine mappings
-/

import RockafellarWets.Chapter9.LipschitzModulus
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Normed.Operator.NNNorm

open Filter Metric Set Topology
open scoped ENNReal NNReal InnerProductSpace

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Theorem 9.7.** The modulus of a strictly differentiable mapping is
the operator norm of its strict derivative. -/
theorem lipschitzModulus_eq_of_hasStrictFDerivAt {f : E → F} {A : E →L[ℝ] F} {x : E}
    (hf : HasStrictFDerivAt f A x) : lipschitzModulus f x = (‖A‖₊ : ℝ≥0∞) := by
  apply le_antisymm
  · by_contra! hn
    obtain ⟨k, hk, hk'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hn
    obtain ⟨U, hU, h⟩ := hf.exists_lipschitzOnWith_of_nnnorm_lt k (ENNReal.coe_lt_coe.mp hk)
    exact hk'.not_ge (lipschitzModulus_le hU h)
  · refine le_iInf fun k ↦ ?_
    obtain ⟨U, hU, h⟩ := k.property
    rw [nhdsWithin_univ] at hU
    exact ENNReal.coe_le_coe.mpr (hf.hasFDerivAt.le_of_lipschitzOn hU h)

theorem lipschitzModulus_eq_nnnorm_fderiv {f : E → F} {x : E} (hf : ContDiffAt ℝ 1 f x) :
    lipschitzModulus f x = (‖fderiv ℝ f x‖₊ : ℝ≥0∞) :=
  lipschitzModulus_eq_of_hasStrictFDerivAt (hf.hasStrictFDerivAt one_ne_zero)

theorem strictlyContinuousAt_of_contDiffAt {f : E → F} {x : E} (hf : ContDiffAt ℝ 1 f x) :
    StrictlyContinuousAt f x := (lipschitzModulus_eq_nnnorm_fderiv hf).trans_lt ENNReal.coe_lt_top

/-- **Example 9.3.** An affine mapping has the linear part's norm as
global Lipschitz constant and as its exact modulus at every point. -/
theorem affine_lipschitzModulus (A : E →L[ℝ] F) (b : F) :
    LipschitzWith ‖A‖₊ (fun y ↦ A y + b) ∧ ∀ x, lipschitzModulus (fun y ↦ A y + b) x = (‖A‖₊ : ℝ≥0∞) := by
  constructor
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_add_right] using A.lipschitz.dist_le_mul x y
  · exact fun x ↦ lipschitzModulus_eq_of_hasStrictFDerivAt (A.hasStrictFDerivAt.add_const b)

theorem exists_unit_attaining_opNorm [ProperSpace E] [Nontrivial E] (A : E →L[ℝ] F) :
    ∃ w : E, ‖w‖ = 1 ∧ ‖A w‖ = ‖A‖ := by
  have hne := NormedSpace.sphere_nonempty (E := E) (x := 0) |>.mpr (zero_le_one : (0 : ℝ) ≤ 1)
  obtain ⟨w, hw, hmax⟩ := (isCompact_sphere (0 : E) 1).exists_isMaxOn hne A.continuous.norm.continuousOn
  refine ⟨w, mem_sphere_zero_iff_norm.mp hw, le_antisymm ?_ ?_⟩
  · simpa only [mem_sphere_zero_iff_norm.mp hw, mul_one] using A.le_opNorm w
  · rw [← A.sSup_sphere_eq_norm]
    exact csSup_le (hne.image _) (fun _ ⟨y, hy, he⟩ ↦ he ▸ hmax hy)

section Gradient

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

theorem lipschitzModulus_eq_nnnorm_gradient {f : G → ℝ} {x : G} (hf : ContDiffAt ℝ 1 f x) :
    lipschitzModulus f x = (‖gradient f x‖₊ : ℝ≥0∞) := by
  rw [lipschitzModulus_eq_nnnorm_fderiv hf, gradient, LinearIsometryEquiv.nnnorm_map]

/-- The modulus of the gradient of a twice continuously differentiable
function is the norm of its derivative (the Hessian as a linear operator). -/
theorem lipschitzModulus_gradient_eq_hessian {f : G → ℝ} {x : G} (hf : ContDiffAt ℝ 2 f x) :
    lipschitzModulus (gradient f) x = (‖fderiv ℝ (gradient f) x‖₊ : ℝ≥0∞) := by
  apply lipschitzModulus_eq_nnnorm_fderiv
  let L : StrongDual ℝ G →L[ℝ] G := (InnerProductSpace.toDual ℝ G).symm.toContinuousLinearEquiv.toContinuousLinearMap
  exact L.contDiff.contDiffAt.comp x (hf.fderiv_right (m := 1) (by norm_num))

end Gradient

end RW
