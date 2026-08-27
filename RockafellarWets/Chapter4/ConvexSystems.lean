/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Limit inclusions for constraint systems

This file formalizes the exact general background formulas 4(8) and 4(9)
preceding Theorem 4.32.  The nonseparation-based reverse inclusion is proved
in `ConvexSystemConvergence`.
-/

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import RockafellarWets.Chapter4.SetLimitCharacterizations

open Filter Function Set Topology

namespace RW

section ConvexSystems

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The feasible set `{x ∈ X | L x ∈ D}`. -/
def linearConstraintSet (X : Set E) (L : E →L[ℝ] F) (D : Set F) : Set E :=
  X ∩ L ⁻¹' D

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Formula 4(8), inner-limit half. -/
theorem innerSetLimit_preimage_subset_preimage_innerSetLimit
    (G : E → F) (hG : Continuous G) (D : ℕ → Set F) :
    innerSetLimit (fun n ↦ G ⁻¹' D n) ⊆
      G ⁻¹' innerSetLimit D := by
  intro x hx V hV
  have hpre : G ⁻¹' V ∈ nhds x := hG.continuousAt hV
  exact (hx _ hpre).mono fun n ⟨y, hy, hyV⟩ ↦
    ⟨G y, hy, hyV⟩

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Formula 4(8), outer-limit half. -/
theorem outerSetLimit_preimage_subset_preimage_outerSetLimit
    (G : E → F) (hG : Continuous G) (D : ℕ → Set F) :
    outerSetLimit (fun n ↦ G ⁻¹' D n) ⊆
      G ⁻¹' outerSetLimit D := by
  intro x hx V hV
  have hpre : G ⁻¹' V ∈ nhds x := hG.continuousAt hV
  exact (hx _ hpre).mono fun n ⟨y, hy, hyV⟩ ↦
    ⟨G y, hy, hyV⟩

private theorem tendsto_varying_continuousLinearMap_apply
    {Lseq : ℕ → E →L[ℝ] F} {L : E →L[ℝ] F}
    {x : ℕ → E} {xbar : E}
    (hL : Tendsto Lseq atTop (nhds L))
    (hx : Tendsto x atTop (nhds xbar)) :
    Tendsto (fun n ↦ Lseq n (x n)) atTop (nhds (L xbar)) := by
  have hpair : Tendsto (fun n ↦ (x n, Lseq n)) atTop
      (nhds (xbar, L)) := by
    rw [nhds_prod_eq]
    exact hx.prodMk hL
  simpa only [ContinuousLinearMap.apply_apply] using
    ((ContinuousLinearMap.apply ℝ F).continuous₂.tendsto (xbar, L)).comp hpair

/-- Formula 4(9): the outer limit of feasible sets is contained in the
limiting feasible set under operator-norm convergence of the linear maps. -/
theorem outerSetLimit_linearConstraintSet_subset
    {Xseq : ℕ → Set E} {X : Set E}
    {Dseq : ℕ → Set F} {D : Set F}
    {Lseq : ℕ → E →L[ℝ] F} {L : E →L[ℝ] F}
    (hX : outerSetLimit Xseq ⊆ X)
    (hD : outerSetLimit Dseq ⊆ D)
    (hL : Tendsto Lseq atTop (nhds L)) :
    outerSetLimit
        (fun n ↦ linearConstraintSet (Xseq n) (Lseq n) (Dseq n)) ⊆
      linearConstraintSet X L D := by
  intro x hx
  rcases mem_outerSetLimit_iff_exists_subsequence.1 hx with
    ⟨φ, y, hφ, hyFeas, hyx⟩
  have hxX : x ∈ X := hX <|
    mem_outerSetLimit_iff_exists_subsequence.2
      ⟨φ, y, hφ, fun n ↦ (hyFeas n).1, hyx⟩
  have hLy : Tendsto (fun n ↦ Lseq (φ n) (y n)) atTop
      (nhds (L x)) :=
    tendsto_varying_continuousLinearMap_apply
      (hL.comp hφ.tendsto_atTop) hyx
  have hLxD : L x ∈ D := hD <|
    mem_outerSetLimit_iff_exists_subsequence.2
      ⟨φ, fun n ↦ Lseq (φ n) (y n), hφ,
        fun n ↦ (hyFeas n).2, hLy⟩
  exact ⟨hxX, hLxD⟩

omit [NormedSpace ℝ E] in
/-- The elementary outer-limit rule 4(7) for a pair of intersections. -/
theorem outerSetLimit_inter_subset
    (C₁ C₂ : ℕ → Set E) :
    outerSetLimit (fun n ↦ C₁ n ∩ C₂ n) ⊆
      outerSetLimit C₁ ∩ outerSetLimit C₂ := by
  intro x hx
  constructor
  · exact outerSetLimit_mono (fun n ↦ inter_subset_left) hx
  · exact outerSetLimit_mono (fun n ↦ inter_subset_right) hx

end ConvexSystems

end RW
