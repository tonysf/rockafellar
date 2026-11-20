/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Conjugate characterizations of minimizers and growth
-/

import RockafellarWets.Chapter11.DualMinimization
import RockafellarWets.Chapter11.SubgradientConjugacy

open Set Filter Topology
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} (hp : IsProper f) (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f))

include hp hl hc

/-- Formula **11(6)**, every tilted solution set is a conjugate subdifferential. -/
theorem argmin_sub_inner_eq_subdifferential_fenchelConjugate (a : E) :
    argmin (fun x ↦ f x-(⟪a,x⟫_ℝ:EReal)) = subdifferential (fenchelConjugate f) a := by
  ext x
  rw [mem_argmin_sub_inner_iff_subgradient hp hc,
    mem_subdifferential_fenchelConjugate_iff hp hl hc]

/-- **11.8(a)**, the unperturbed solution set. -/
theorem argmin_eq_subdifferential_fenchelConjugate_zero :
    argmin f = subdifferential (fenchelConjugate f) 0 := by
  simpa only [inner_zero_left,EReal.coe_zero,sub_zero] using
    argmin_sub_inner_eq_subdifferential_fenchelConjugate hp hl hc (0:E)

/-- **11.8(b)** and **11(6)**, unique primal solutions correspond to strict
gradients of the conjugate, with the solution itself as gradient. -/
theorem argmin_sub_inner_eq_singleton_iff_conjugate_hasStrictGradientAt (a x : E) :
    argmin (fun y ↦ f y-(⟪a,y⟫_ℝ:EReal)) = {x} ↔
      HasStrictGradientAt (fenchelConjugate f) x a := by
  rw [argmin_sub_inner_eq_subdifferential_fenchelConjugate hp hl hc]
  exact subdifferential_eq_singleton_iff_hasStrictGradientAt_of_convex
    (isProper_fenchelConjugate hp hl hc) (lowerSemicontinuous_fenchelConjugate f)
    (convex_epigraph_fenchelConjugate f)

/-- The ordinary differentiability formulation of the same correspondence.
The local finite-value clause makes differentiation of an extended-real
function explicit. -/
theorem argmin_sub_inner_eq_singleton_iff_conjugate_hasGradientAt (a x : E) :
    argmin (fun y ↦ f y-(⟪a,y⟫_ℝ:EReal)) = {x} ↔
      (∀ᶠ v in 𝓝 a, fenchelConjugate f v = ((fenchelConjugate f v).toReal:EReal)) ∧
        HasGradientAt (fun v ↦ (fenchelConjugate f v).toReal) x a := by
  rw [argmin_sub_inner_eq_subdifferential_fenchelConjugate hp hl hc]
  exact subdifferential_eq_singleton_iff_hasGradientAt_of_convex
    (isProper_fenchelConjugate hp hl hc) (lowerSemicontinuous_fenchelConjugate f)
    (convex_epigraph_fenchelConjugate f)

/-- **11.8(b)**, the unperturbed strict-gradient criterion. -/
theorem argmin_eq_singleton_iff_conjugate_hasStrictGradientAt_zero (x : E) :
    argmin f = {x} ↔ HasStrictGradientAt (fenchelConjugate f) x 0 := by
  simpa only [inner_zero_left,EReal.coe_zero,sub_zero] using
    argmin_sub_inner_eq_singleton_iff_conjugate_hasStrictGradientAt hp hl hc (0:E) x

/-- **11.8(b)**, the unperturbed ordinary-gradient criterion. -/
theorem argmin_eq_singleton_iff_conjugate_hasGradientAt_zero (x : E) :
    argmin f = {x} ↔
      (∀ᶠ v in 𝓝 (0:E), fenchelConjugate f v = ((fenchelConjugate f v).toReal:EReal)) ∧
        HasGradientAt (fun v ↦ (fenchelConjugate f v).toReal) x 0 := by
  simpa only [inner_zero_left,EReal.coe_zero,sub_zero] using
    argmin_sub_inner_eq_singleton_iff_conjugate_hasGradientAt hp hl hc (0:E) x

end RW
