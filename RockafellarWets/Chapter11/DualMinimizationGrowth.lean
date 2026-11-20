/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Coercivity and the domain of the conjugate
-/

import RockafellarWets.Chapter11.DualMinimizationEquivalences
import RockafellarWets.Chapter11.HorizonConjugacy

open Set Topology
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} (hp : IsProper f) (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f))

include hp hl hc

/-- **11.8(c)**, level-boundedness is an interior-domain condition on the conjugate. -/
theorem isLevelBounded_iff_zero_mem_interior_conjugate_domain :
    IsLevelBounded f ↔ (0:E) ∈ interior (effectiveDomain (fenchelConjugate f)) :=
  isLevelBounded_iff_zero_mem_interior_of_horizon_support hp hl hc
    (convex_effectiveDomain_of_convex_epigraph (convex_epigraph_fenchelConjugate f))
    (isProper_fenchelConjugate hp hl hc).1 (horizon_conjugate_support_identities hp hl hc).1

/-- **11.8(c)**, equivalently stated using level coercivity. -/
theorem isLevelCoercive_iff_zero_mem_interior_conjugate_domain :
    IsLevelCoercive f ↔ (0:E) ∈ interior (effectiveDomain (fenchelConjugate f)) := by
  rw [← isLevelBounded_iff_isLevelCoercive hc hl hp,
    isLevelBounded_iff_zero_mem_interior_conjugate_domain hp hl hc]

/-- **11.8(d)**, coercivity is equivalent to finiteness of the conjugate everywhere. -/
theorem isCoercive_iff_conjugate_domain_eq_univ :
    IsCoercive f ↔ effectiveDomain (fenchelConjugate f) = univ := by
  refine ⟨effectiveDomain_fenchelConjugate_eq_univ_of_isCoercive,fun hdom ↦ ?_⟩
  apply isCoercive_of_horizon_eq_indicator_zero hp hl
  rw [(horizon_conjugate_support_identities hp hl hc).1,hdom,supportFunction_univ]

/-- Formula **11(6)**, the tilted level-coercivity criterion. -/
theorem isLevelCoercive_sub_inner_iff_mem_interior_conjugate_domain (a : E) :
    IsLevelCoercive (fun x ↦ f x-(⟪a,x⟫_ℝ:EReal)) ↔
      a ∈ interior (effectiveDomain (fenchelConjugate f)) := by
  rw [isLevelCoercive_iff_zero_mem_interior_conjugate_domain
    (isProper_sub_inner hp a) (lowerSemicontinuous_sub_inner hl a) (convex_epigraph_sub_inner hc a)]
  have he : effectiveDomain (fenchelConjugate (fun x ↦ f x-(⟪a,x⟫_ℝ:EReal))) =
      (Homeomorph.addRight a) ⁻¹' effectiveDomain (fenchelConjugate f) := by
    ext v
    change fenchelConjugate (fun x ↦ f x-(⟪a,x⟫_ℝ:EReal)) v < ⊤ ↔ fenchelConjugate f (v+a) < ⊤
    rw [fenchelConjugate_sub_inner]
  rw [he,← (Homeomorph.addRight a).preimage_interior]
  simpa

/-- Formula **11(6)**, the equivalent tilted level-boundedness criterion. -/
theorem isLevelBounded_sub_inner_iff_mem_interior_conjugate_domain (a : E) :
    IsLevelBounded (fun x ↦ f x-(⟪a,x⟫_ℝ:EReal)) ↔
      a ∈ interior (effectiveDomain (fenchelConjugate f)) := by
  rw [isLevelBounded_iff_isLevelCoercive (convex_epigraph_sub_inner hc a)
    (lowerSemicontinuous_sub_inner hl a) (isProper_sub_inner hp a),
    isLevelCoercive_sub_inner_iff_mem_interior_conjugate_domain hp hl hc a]

omit hp hl hc [FiniteDimensional ℝ E] in
/-- Linear tilts preserve coercive growth, even without convexity. -/
theorem IsCoercive.sub_inner {f : E → EReal} (hf : IsCoercive f) (a : E) :
    IsCoercive (fun x ↦ f x-(⟪a,x⟫_ℝ:EReal)) := by
  intro γ hγ
  obtain ⟨β,hβ⟩ := hf (γ+‖a‖) (by positivity)
  refine ⟨β,fun x ↦ ?_⟩
  have hi := (le_abs_self ⟪a,x⟫_ℝ).trans (abs_real_inner_le_norm a x)
  calc
    ((γ*‖x‖+β:ℝ):EReal) ≤ (((γ+‖a‖)*‖x‖+β-⟪a,x⟫_ℝ:ℝ):EReal) := by
      rw [EReal.coe_le_coe_iff]
      nlinarith
    _ = (((γ+‖a‖)*‖x‖+β:ℝ):EReal)-(⟪a,x⟫_ℝ:EReal) := EReal.coe_sub _ _
    _ ≤ f x-(⟪a,x⟫_ℝ:EReal) := EReal.sub_le_sub (hβ x) le_rfl

end RW
