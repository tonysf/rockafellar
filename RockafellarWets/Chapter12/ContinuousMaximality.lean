/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: Maximality of continuous monotone mappings

Example 12.7: a continuous monotone single-valued mapping is maximal monotone.
In particular differentiable monotone mappings and affine monotone mappings are
maximal monotone.

The proof is the one in the book.  If `(x̂, v̂)` satisfies the monotonicity
inequality against the whole graph of `F`, then testing it at `x̂ + t d` with
`d = v̂ - F x̂` and letting `t ↘ 0` gives `‖d‖² ≤ 0`.
-/

import RockafellarWets.Chapter12.MonotoneMappings
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Module.FiniteDimension

open Set Filter Topology
open scoped InnerProductSpace

namespace RW

section ContinuousMaximality

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The pairs satisfying the monotonicity inequality against the graph of a
continuous single-valued mapping lie on that graph. -/
theorem eq_of_forall_inner_nonneg_of_continuous {F : E → E} (hF : Continuous F) {x v : E}
    (h : ∀ y, 0 ≤ ⟪v - F y, x - y⟫_ℝ) : v = F x := by
  set d := v - F x with hd
  have hle : ∀ t : ℝ, 0 < t → ⟪v - F (x + t • d), d⟫_ℝ ≤ 0 := by
    intro t ht
    have h' := h (x + t • d)
    rw [show x - (x + t • d) = -(t • d) by abel, inner_neg_right, real_inner_smul_right] at h'
    nlinarith
  have hcont : Continuous fun t : ℝ ↦ ⟪v - F (x + t • d), d⟫_ℝ := by fun_prop
  have hlim : Tendsto (fun t : ℝ ↦ ⟪v - F (x + t • d), d⟫_ℝ) (𝓝[>] 0)
      (𝓝 ⟪v - F (x + (0 : ℝ) • d), d⟫_ℝ) :=
    hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h0 : ⟪v - F (x + (0 : ℝ) • d), d⟫_ℝ ≤ 0 :=
    le_of_tendsto hlim (eventually_nhdsWithin_of_forall fun t ht ↦ hle t ht)
  rw [zero_smul, add_zero, ← hd] at h0
  have hdd : ⟪d, d⟫_ℝ = 0 := le_antisymm h0 real_inner_self_nonneg
  exact sub_eq_zero.1 (inner_self_eq_zero.1 hdd)

/-- **Example 12.7.** A continuous monotone mapping `F : E → E` is maximal
monotone. -/
theorem svMaximalMonotone_singleton_of_continuous {F : E → E} (hF : Continuous F)
    (hmono : SvMonotone (fun x ↦ ({F x} : Set E))) :
    SvMaximalMonotone (fun x ↦ ({F x} : Set E)) := by
  refine svMaximalMonotone_iff_forall_inner_nonneg.2 ⟨hmono, fun x v h ↦ ?_⟩
  exact mem_singleton_iff.2
    (eq_of_forall_inner_nonneg_of_continuous hF fun y ↦ h y (F y) (mem_singleton _))

/-- **Example 12.7**, differentiable mappings: a differentiable monotone
mapping is maximal monotone. -/
theorem svMaximalMonotone_singleton_of_differentiable {F : E → E} (hF : Differentiable ℝ F)
    (hmono : SvMonotone (fun x ↦ ({F x} : Set E))) :
    SvMaximalMonotone (fun x ↦ ({F x} : Set E)) :=
  svMaximalMonotone_singleton_of_continuous hF.continuous hmono

/-- **Example 12.7**, affine mappings: `x ↦ A x + a` with `A` linear is maximal
monotone as soon as it is monotone. -/
theorem svMaximalMonotone_affine {A : E →L[ℝ] E} {a : E}
    (hmono : SvMonotone (fun x ↦ ({A x + a} : Set E))) :
    SvMaximalMonotone (fun x ↦ ({A x + a} : Set E)) :=
  svMaximalMonotone_singleton_of_continuous (by fun_prop) hmono

/-- **Example 12.7**, affine mappings on a finite-dimensional space, where every
affine map is continuous. -/
theorem svMaximalMonotone_affineMap [FiniteDimensional ℝ E] (L : E →ᵃ[ℝ] E)
    (hmono : SvMonotone (fun x ↦ ({L x} : Set E))) :
    SvMaximalMonotone (fun x ↦ ({L x} : Set E)) :=
  svMaximalMonotone_singleton_of_continuous L.continuous_of_finiteDimensional hmono

end ContinuousMaximality

end RW
