/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: subgradient mappings of convex functions

This file formalizes Theorem 12.17 (monotonicity versus convexity) and
Corollary 12.18 (normal cone mappings).

The subgradient mapping `∂f : E ⇉ E` is the Chapter 8 limiting subdifferential
`subdifferential f`.  Its membership requires a finite value, so convention
12(5), `∂f(x) = ∅` for `x ∉ dom f`, holds by definition; see
`subdifferential_eq_empty_of_eq_top`.  Likewise the Chapter 6 normal cone is
empty off the set, which is convention 12(6).

* `svMonotone_subdifferential_of_convex`: a proper convex function has a
  monotone subgradient mapping (no closedness needed).
* `convex_epigraph_iff_svMonotone_subdifferential`: a proper lsc function is
  convex if and only if `∂f` is monotone.  The converse half is
  `convex_epigraph_of_svMonotone_subdifferential` from
  `ConvexityFromMonotoneSubgradients`.
* `svMaximalMonotone_subdifferential_of_convex`: then `∂f` is maximal monotone.
  The proof is the direct form of the argument through 12.12: for a pair
  `(x, v)` monotonically related to the graph, the proximal point `p` of
  `x + v` satisfies `x + v - p ∈ ∂f(p)`, and the monotonicity inequality
  against this pair forces `p = x`.
* `isAlmostStrictlyConvex_iff_svStrictlyMonotone_subdifferential`: such a
  function is almost strictly convex exactly when `∂f` is strictly monotone.
  Strict monotonicity of `∂f` amounts to single-valuedness of `(∂f)⁻¹ = ∂f*`,
  which is the characterization of almost strict convexity in 11.13.
-/

import RockafellarWets.Chapter12.ConvexityFromMonotoneSubgradients
import RockafellarWets.Chapter11.EssentialStrictConvexity
import RockafellarWets.Chapter3.ExtendedProximalCancellationCompletion
import RockafellarWets.Chapter8.IndicatorSubgradients

open Set Filter Topology
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Convention 12(5): the subgradient mapping is empty outside `dom f`. -/
theorem subdifferential_eq_empty_of_eq_top {f : E → EReal} {x : E} (hx : f x = ⊤) :
    subdifferential f x = ∅ := by
  ext v
  simp only [mem_empty_iff_false, iff_false]
  rintro ⟨⟨c, hc⟩, -⟩
  rw [hx] at hc
  exact EReal.coe_ne_top c hc.symm

/-- The domain of `∂f` lies in `dom f`. -/
theorem svDom_subdifferential_subset_effectiveDomain (f : E → EReal) :
    svDom (subdifferential f) ⊆ effectiveDomain f := by
  rintro x ⟨v, hv⟩
  obtain ⟨c, hc⟩ := hv.1
  change f x < ⊤
  rw [hc]
  exact EReal.coe_lt_top c

variable [FiniteDimensional ℝ E]

/-- **Theorem 12.17**, first assertion: the subgradient mapping of a proper
convex function is monotone.  Lower semicontinuity is not needed. -/
theorem svMonotone_subdifferential_of_convex {f : E → EReal} (hp : IsProper f)
    (hc : Convex ℝ (epigraph f)) : SvMonotone (subdifferential f) := by
  intro x₀ v₀ h₀ x₁ v₁ h₁
  obtain ⟨a₀, ha₀⟩ := h₀.1
  obtain ⟨a₁, ha₁⟩ := h₁.1
  have i₀ := (mem_subdifferential_iff_of_convex hc hp ha₀).1 h₀ x₁
  have i₁ := (mem_subdifferential_iff_of_convex hc hp ha₁).1 h₁ x₀
  rw [ha₁, EReal.coe_le_coe_iff] at i₀
  rw [ha₀, EReal.coe_le_coe_iff] at i₁
  have hrw : ⟪v₁ - v₀, x₁ - x₀⟫_ℝ = -(⟪v₀, x₁ - x₀⟫_ℝ + ⟪v₁, x₀ - x₁⟫_ℝ) := by
    rw [inner_sub_left, show x₀ - x₁ = -(x₁ - x₀) by abel, inner_neg_right]
    ring
  rw [hrw]
  linarith

/-- **Theorem 12.17**: a proper lower semicontinuous function is convex if and
only if its subgradient mapping is monotone. -/
theorem convex_epigraph_iff_svMonotone_subdifferential {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) :
    Convex ℝ (epigraph f) ↔ SvMonotone (subdifferential f) :=
  ⟨svMonotone_subdifferential_of_convex hp, convex_epigraph_of_svMonotone_subdifferential hp hl⟩

/-- **Theorem 12.17**: the subgradient mapping of a proper lsc convex function
is maximal monotone. -/
theorem svMaximalMonotone_subdifferential_of_convex {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) :
    SvMaximalMonotone (subdifferential f) := by
  refine svMaximalMonotone_iff_forall_inner_nonneg.2
    ⟨svMonotone_subdifferential_of_convex hp hc, fun x v h ↦ ?_⟩
  obtain ⟨p, hpP⟩ := proximalMappingEReal_nonempty hc hl hp one_pos (x + v)
  obtain ⟨u, hu, hpu⟩ :=
    proximalMappingEReal_subset_inverse_subgradientShift hp one_pos (x + v) hpP
  have hpu' : p + u = x + v := by simpa using hpu
  have h1 := h p u hu
  have hvu : v - u = p - x := sub_eq_sub_iff_add_eq_add.2 (by rw [hpu', add_comm])
  have hsq : ⟪p - x, x - p⟫_ℝ = -‖x - p‖ ^ 2 := by
    rw [show p - x = -(x - p) by abel, inner_neg_left, real_inner_self_eq_norm_sq]
  rw [hvu, hsq] at h1
  have h0 : ‖x - p‖ ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
  rw [sq_eq_zero_iff, norm_eq_zero, sub_eq_zero] at h0
  subst h0
  rw [add_left_cancel hpu'] at hu
  exact hu

/-- For a proper convex function, strict monotonicity of `∂f` is the
single-valuedness of the inverse relation `(∂f)⁻¹`.  If two subgradients have
vanishing monotonicity pairing, both subgradient inequalities are equalities
and the first slope is a subgradient at the second point too. -/
theorem svStrictlyMonotone_subdifferential_iff_forall_subsingleton {f : E → EReal}
    (hp : IsProper f) (hc : Convex ℝ (epigraph f)) :
    SvStrictlyMonotone (subdifferential f) ↔
      ∀ v, (svInv (subdifferential f) v).Subsingleton := by
  constructor
  · intro hs v x₀ hx₀ x₁ hx₁
    by_contra hne
    have h := hs hx₀ hx₁ hne
    simp at h
  · intro hsub x₀ v₀ h₀ x₁ v₁ h₁ hne
    rcases (svMonotone_subdifferential_of_convex hp hc h₀ h₁).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      obtain ⟨a₀, ha₀⟩ := h₀.1
      obtain ⟨a₁, ha₁⟩ := h₁.1
      have s₀ := (mem_subdifferential_iff_of_convex hc hp ha₀).1 h₀
      have i₀ := s₀ x₁
      have i₁ := (mem_subdifferential_iff_of_convex hc hp ha₁).1 h₁ x₀
      rw [ha₁, EReal.coe_le_coe_iff] at i₀
      rw [ha₀, EReal.coe_le_coe_iff] at i₁
      have hrw₁ : ⟪v₁, x₀ - x₁⟫_ℝ = -⟪v₁, x₁ - x₀⟫_ℝ := by
        rw [show x₀ - x₁ = -(x₁ - x₀) by abel, inner_neg_right]
      rw [inner_sub_left] at heq
      have ha : a₁ = a₀ + ⟪v₀, x₁ - x₀⟫_ℝ := by linarith
      have hv₀ : v₀ ∈ subdifferential f x₁ := by
        rw [mem_subdifferential_iff_of_convex hc hp ha₁]
        intro z
        have hz : a₁ + ⟪v₀, z - x₁⟫_ℝ = a₀ + ⟪v₀, z - x₀⟫_ℝ := by
          rw [ha, add_assoc, ← inner_add_right]
          congr 2
          abel
        rw [hz]
        exact s₀ z
      exact hne (hsub v₀ h₀ hv₀)

/-- **Theorem 12.17**, last assertion: a proper lsc convex function is almost
strictly convex if and only if its subgradient mapping is strictly monotone. -/
theorem isAlmostStrictlyConvex_iff_svStrictlyMonotone_subdifferential {f : E → EReal}
    (hp : IsProper f) (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) :
    IsAlmostStrictlyConvex f ↔ SvStrictlyMonotone (subdifferential f) := by
  rw [isAlmostStrictlyConvex_iff_conjugate_subdifferential_subsingleton hp hl hc,
    svStrictlyMonotone_subdifferential_iff_forall_subsingleton hp hc]
  refine forall_congr' fun v ↦ ?_
  rw [congrFun (subdifferential_fenchelConjugate_eq_inverse hp hl hc).1 v]

/-- **Theorem 12.17**, all assertions for a proper lsc function: convexity is
equivalent to monotonicity of `∂f`, in which case `∂f` is maximal monotone,
and almost strict convexity is then equivalent to strict monotonicity. -/
theorem monotonicity_versus_convexity {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) :
    (Convex ℝ (epigraph f) ↔ SvMonotone (subdifferential f)) ∧
      (Convex ℝ (epigraph f) → SvMaximalMonotone (subdifferential f) ∧
        (IsAlmostStrictlyConvex f ↔ SvStrictlyMonotone (subdifferential f))) :=
  ⟨convex_epigraph_iff_svMonotone_subdifferential hp hl, fun hc ↦
    ⟨svMaximalMonotone_subdifferential_of_convex hp hl hc,
      isAlmostStrictlyConvex_iff_svStrictlyMonotone_subdifferential hp hl hc⟩⟩

omit [FiniteDimensional ℝ E] in
/-- The indicator of a nonempty closed convex set is proper, lsc and convex. -/
theorem indicatorVA_proper_lsc_convex {C : Set E} (hC : IsClosed C) (hconv : Convex ℝ C)
    (hne : C.Nonempty) :
    IsProper (indicatorVA C) ∧ LowerSemicontinuous (indicatorVA C) ∧
      Convex ℝ (epigraph (indicatorVA C)) :=
  ⟨(indicatorVA_isProper_iff C).2 hne, lowerSemicontinuous_indicatorVA hC, by
    rw [epigraph_indicatorVA]
    exact hconv.prod (convex_Ici 0)⟩

/-- The subgradient mapping of an indicator is its normal cone mapping (8.14). -/
theorem subdifferential_indicatorVA_eq_normalCone (C : Set E) :
    subdifferential (indicatorVA C) = normalCone C :=
  funext (subdifferential_indicatorVA C)

/-- **Corollary 12.18 (normal cone mappings).** For a nonempty closed convex
set `C`, the normal cone mapping `N_C`, empty off `C` by 12(6), is maximal
monotone. -/
theorem svMaximalMonotone_normalCone {C : Set E} (hC : IsClosed C) (hconv : Convex ℝ C)
    (hne : C.Nonempty) : SvMaximalMonotone (normalCone C) := by
  obtain ⟨hp, hl, hc⟩ := indicatorVA_proper_lsc_convex hC hconv hne
  rw [← subdifferential_indicatorVA_eq_normalCone]
  exact svMaximalMonotone_subdifferential_of_convex hp hl hc

omit [FiniteDimensional ℝ E] in
/-- Convention 12(6): `N_C(x) = ∅` for `x ∉ C`. -/
theorem normalCone_eq_empty_of_not_mem {C : Set E} {x : E} (hx : x ∉ C) :
    normalCone C x = ∅ :=
  normalCone_eq_empty hx

end RW
