/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: cyclical monotonicity in one dimension

This file formalizes Exercise 12.26.  On the line every monotone mapping is
cyclically monotone: for a cycle `(xᵢ, vᵢ)` in `gph T` the families `v` and `x`
vary together (any two graph points are ordered componentwise, 12.9(a)), so the
rearrangement inequality gives `Σ vᵢ x_{i+1} ≤ Σ vᵢ xᵢ`, which is 12(7).  Hence
a maximal monotone `T : ℝ ⇉ ℝ` is maximal cyclically monotone, and by 12.25 it
is `∂f` for a proper lsc convex `f : ℝ → ℝ̄`.  Example 8.52 identifies `∂f(x)`
with the interval between the one-sided derivatives `f'₋(x) ≤ v ≤ f'₊(x)` on
`dom f`, and `∂f(x) = ∅` off `dom f`.

The guide's route through the representation 12.9(b) is replaced by the
rearrangement inequality, which needs only the monotonicity of `T`.
-/

import RockafellarWets.Chapter12.CyclicalMonotonicity
import RockafellarWets.Chapter8.ConvexOneDimensionalSlopes
import Mathlib.Algebra.Order.Rearrangement

open Set
open scoped InnerProductSpace

namespace RW

private theorem inner_real_eq_mul_aux (a b : ℝ) : ⟪a, b⟫_ℝ = a * b := by
  simp [mul_comm]

/-- **Exercise 12.26**: every monotone mapping `T : ℝ ⇉ ℝ` is cyclically
monotone, by the rearrangement inequality. -/
theorem SvMonotone.svCyclicallyMonotone_real {T : ℝ → Set ℝ} (hT : SvMonotone T) :
    SvCyclicallyMonotone T := by
  intro m _ x v hv
  have hmono : Monovary v x := by
    intro i j hij
    have h := hT (hv i) (hv j)
    rw [inner_real_eq_mul_aux] at h
    by_contra hcon
    push_neg at hcon
    nlinarith
  have hr := hmono.sum_mul_comp_perm_le_sum_mul (σ := finRotate (m + 1))
  unfold cyclicSum
  simp only [inner_real_eq_mul_aux, mul_sub, Finset.sum_sub_distrib]
  linarith

/-- **Exercise 12.26**: every maximal monotone `T : ℝ ⇉ ℝ` is maximal
cyclically monotone. -/
theorem SvMaximalMonotone.svMaximalCyclicallyMonotone_real {T : ℝ → Set ℝ}
    (hT : SvMaximalMonotone T) : SvMaximalCyclicallyMonotone T :=
  ⟨hT.1.svCyclicallyMonotone_real, fun _ hT' hsub ↦ hT.eq_of_subset hT'.svMonotone hsub⟩

/-- **Exercise 12.26**: the maximal monotone mappings `T : ℝ ⇉ ℝ` are exactly
the subgradient mappings of proper lsc convex functions `f : ℝ → ℝ̄`. -/
theorem svMaximalMonotone_real_iff_exists_subdifferential {T : ℝ → Set ℝ} :
    SvMaximalMonotone T ↔ ∃ f : ℝ → EReal, IsProper f ∧ LowerSemicontinuous f ∧
      Convex ℝ (epigraph f) ∧ T = subdifferential f := by
  constructor
  · intro hT
    exact (exists_eq_subdifferential_iff_svMaximalCyclicallyMonotone T).2
      hT.svMaximalCyclicallyMonotone_real
  · rintro ⟨f, hp, hl, hc, rfl⟩
    exact svMaximalMonotone_subdifferential_of_convex hp hl hc

/-- **Exercise 12.26** with 8.52: on `dom f`, `∂f(x) = {v | f'₋(x) ≤ v ≤ f'₊(x)}`. -/
theorem subdifferential_real_of_mem_effectiveDomain {f : ℝ → EReal} (hp : IsProper f)
    (hc : Convex ℝ (epigraph f)) {x : ℝ} (hx : x ∈ effectiveDomain f) :
    subdifferential f x = {v : ℝ | leftSlope f x ≤ (v : EReal) ∧ (v : EReal) ≤ rightSlope f x} :=
  (subdifferentials_eq_slopeInterval hc hp
    (EReal.coe_toReal (ne_of_lt hx) (hp.2 x).ne').symm).1

/-- **Exercise 12.26**: off `dom f`, `∂f(x) = ∅`. -/
theorem subdifferential_real_of_not_mem_effectiveDomain {f : ℝ → EReal} {x : ℝ}
    (hx : x ∉ effectiveDomain f) : subdifferential f x = ∅ := by
  have htop : f x = ⊤ := by
    simp only [effectiveDomain, mem_setOf_eq, not_lt, top_le_iff] at hx
    exact hx
  exact subdifferential_eq_empty_of_eq_top htop

/-- **Exercise 12.26 (cyclical monotonicity in one dimension).**  Every maximal
monotone `T : ℝ ⇉ ℝ` is maximal cyclically monotone; the maximal monotone
mappings `T : ℝ ⇉ ℝ` are precisely the subgradient mappings `∂f` of proper lsc
convex `f : ℝ → ℝ̄`; and for such `f`, `∂f(x)` is the set of `v` with
`f'₋(x) ≤ v ≤ f'₊(x)` when `x ∈ dom f`, and is empty when `x ∉ dom f`. -/
theorem cyclical_monotonicity_in_one_dimension :
    (∀ T : ℝ → Set ℝ, SvMaximalMonotone T → SvMaximalCyclicallyMonotone T) ∧
      (∀ T : ℝ → Set ℝ, SvMaximalMonotone T ↔ ∃ f : ℝ → EReal, IsProper f ∧
        LowerSemicontinuous f ∧ Convex ℝ (epigraph f) ∧ T = subdifferential f) ∧
      ∀ f : ℝ → EReal, IsProper f → Convex ℝ (epigraph f) →
        (∀ x ∈ effectiveDomain f, subdifferential f x =
          {v : ℝ | leftSlope f x ≤ (v : EReal) ∧ (v : EReal) ≤ rightSlope f x}) ∧
        ∀ x ∉ effectiveDomain f, subdifferential f x = ∅ :=
  ⟨fun _ hT ↦ hT.svMaximalCyclicallyMonotone_real,
    fun _ ↦ svMaximalMonotone_real_iff_exists_subdifferential,
    fun _ hp hc ↦ ⟨fun _ hx ↦ subdifferential_real_of_mem_effectiveDomain hp hc hx,
      fun _ hx ↦ subdifferential_real_of_not_mem_effectiveDomain hx⟩⟩

end RW
