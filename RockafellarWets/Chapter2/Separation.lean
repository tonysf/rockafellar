/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 2F-H: Closures, Separation, and Relative Interiors

This file formalizes Sections F, G*, and H* of Chapter 2 of Rockafellar & Wets,
"Variational Analysis":
- Proposition 2.32: Closure of a convex set is convex
- Theorem 2.33: Line segment principle (relative interior characterization)
- Theorem 2.35: Continuity of convex functions on int(dom f)
- Theorem 2.39: Separation of convex sets by hyperplanes
- Proposition 2.40: Properties of relative interiors of convex sets
-/

import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

set_option linter.style.openClassical false

open Set Filter Topology Classical

noncomputable section

namespace RW

/-! ## Section F: Closures and Continuity -/

section ClosuresAndContinuity

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-! ### Proposition 2.32: Closure preserves convexity -/

/-- **Proposition 2.32**: The closure of a convex set is convex.
This is `Convex.closure` in Mathlib. -/
theorem convex_closure [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {S : Set E} (hS : Convex ℝ S) :
    Convex ℝ (closure S) :=
  hS.closure

/-- The interior of a convex set is convex.
This is `Convex.interior` in Mathlib. -/
theorem convex_interior [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {S : Set E} (hS : Convex ℝ S) :
    Convex ℝ (interior S) :=
  hS.interior

/-! ### Theorem 2.33: Line segment principle -/

/-- **Theorem 2.33 (Line segment principle)**: If `x` is in the interior of
a convex set `S` and `y ∈ closure S`, then every point strictly between
`x` and `y` belongs to the interior of `S`. -/
theorem line_segment_interior
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {S : Set E} (hS : Convex ℝ S) {x : E} (hx : x ∈ interior S)
    {y : E} (hy : y ∈ closure S) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (1 - t) • x + t • y ∈ interior S := by
  have h1t : 0 < 1 - t := sub_pos.mpr ht1
  exact hS.combo_interior_closure_mem_interior hx hy h1t ht0.le (sub_add_cancel 1 t)

end ClosuresAndContinuity

/-! ### Theorem 2.35: Continuity of convex functions -/

/-- **Theorem 2.35**: A convex function on an open convex set in a
finite-dimensional space is continuous. -/
theorem continuous_of_convexOn_open
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S : Set E} (hSo : IsOpen S) (_hSc : Convex ℝ S)
    {f : E → ℝ} (hf : ConvexOn ℝ S f) :
    ContinuousOn f S :=
  hf.continuousOn hSo

/-! ## Section G*: Separation of Convex Sets -/

section Separation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A **supporting hyperplane** for a convex set `S` at a boundary point `x₀`
is defined by a nonzero functional `φ` such that `φ(x) ≤ φ(x₀)` for all
`x ∈ S`. -/
def IsSupportingHyperplane (S : Set E) (x₀ : E) (φ : E →L[ℝ] ℝ) : Prop :=
  φ ≠ 0 ∧ x₀ ∈ closure S ∧ ∀ x ∈ S, φ x ≤ φ x₀

/-- **Theorem 2.39 (Separation theorem)**: Two nonempty disjoint convex sets,
one of which is open, can be separated by a hyperplane. That is, there
exists a nonzero continuous linear functional `φ` and a constant `c` such
that `φ(x) ≤ c ≤ φ(y)` for all `x ∈ S` and `y ∈ T`. -/
theorem separation_of_convex_open
    [CompleteSpace E]
    {S T : Set E}
    (hS : Convex ℝ S) (hSne : S.Nonempty) (hSo : IsOpen S)
    (hT : Convex ℝ T) (hTne : T.Nonempty)
    (hdisj : Disjoint S T) :
    ∃ (φ : E →L[ℝ] ℝ), φ ≠ 0 ∧ ∀ x ∈ S, ∀ y ∈ T, φ x ≤ φ y := by
  obtain ⟨f, u, hfS, hfT⟩ := geometric_hahn_banach_open hS hSo hT hdisj
  refine ⟨f, ?_, fun x hx y hy => le_of_lt (lt_of_lt_of_le (hfS x hx) (hfT y hy))⟩
  intro hf0
  obtain ⟨a, ha⟩ := hSne
  obtain ⟨b, hb⟩ := hTne
  have h1 := hfS a ha
  have h2 := hfT b hb
  simp [hf0] at h1 h2
  linarith

/-- **Theorem 2.39 (Strict separation)**: Two nonempty disjoint convex sets,
one compact and one closed, can be strictly separated. -/
theorem strict_separation_of_convex_compact
    [CompleteSpace E] [FiniteDimensional ℝ E]
    {S T : Set E}
    (hS : Convex ℝ S) (_hSne : S.Nonempty) (hSc : IsCompact S)
    (hT : Convex ℝ T) (_hTne : T.Nonempty) (hTcl : IsClosed T)
    (hdisj : Disjoint S T) :
    ∃ (φ : E →L[ℝ] ℝ) (c₁ c₂ : ℝ),
      c₁ < c₂ ∧ (∀ x ∈ S, φ x < c₁) ∧ (∀ y ∈ T, c₂ < φ y) := by
  obtain ⟨f, u, v, hfu, huv, hfv⟩ := geometric_hahn_banach_compact_closed hS hSc hT hTcl hdisj
  exact ⟨f, u, v, huv, hfu, hfv⟩

end Separation

/-! ## Section H*: Relative Interiors -/

section RelativeInteriors

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Proposition 2.40 (a)**: The relative interior of a convex set is
nonempty (in finite dimensions). -/
theorem nonempty_relInterior_of_convex
    [FiniteDimensional ℝ E]
    {S : Set E} (hS : Convex ℝ S) (hSne : S.Nonempty) :
    (intrinsicInterior ℝ S).Nonempty :=
  hSne.intrinsicInterior hS

/-- **Proposition 2.40 (b)** in the full-space case:
if a convex set has nonempty interior, then `closure (interior S) = closure S`. -/
theorem closure_interior_eq_closure
    {S : Set E} (hS : Convex ℝ S)
    (hint : (interior S).Nonempty) :
    closure (interior S) = closure S :=
  hS.closure_interior_eq_closure_of_nonempty_interior hint

end RelativeInteriors

end RW
