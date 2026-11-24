/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: hypomonotone mappings

This file formalizes Example 12.28.  `T` is hypomonotone at `x̄` when for some
neighborhood `V` of `x̄` and `ρ ≥ 0` the mapping `T + ρI`, restricted to `V`, is
monotone (`svShiftOn T ρ V`); cyclical hypomonotonicity asks the same restriction
to be cyclically monotone.

* (a) a strictly continuous single-valued mapping satisfies the inequality with
  `ρ` a local Lipschitz constant;
* (b) for proper lsc `f`, `∂(f + ½ρ‖·‖²)(x) = ∂f(x) + ρx` (8.8(c)), so
  hypomonotonicity of `∂f` at `x̄` is monotonicity of `∂(f + ½ρ‖·‖²)` near `x̄`.
  The localized form of 12.17 (`convex_epigraph_add_indicator_ball_of_monotoneOn`)
  turns this into convexity of `f + ½ρ‖·‖²` on a ball, and conversely the
  subgradients of a convex function are cyclically monotone (12.25), which also
  gives cyclical hypomonotonicity.  "Convex on a neighborhood `V`" is convexity
  of `f + ½ρ‖·‖² + δ_V` for a convex `V`, as in the detail of the example;
* (c) combines (b) with Theorem 10.33 (lower-`C²` functions are locally finite
  convex functions minus quadratics) and the existence of subgradients of finite
  convex functions on open sets.
-/

import RockafellarWets.Chapter12.CyclicalMonotonicity
import RockafellarWets.Chapter12.ConvexityFromMonotoneSubgradients
import RockafellarWets.Chapter12.StrongConvexity
import RockafellarWets.Chapter11.Lagrangians
import RockafellarWets.Chapter10.SubsmoothQuadratic
import RockafellarWets.Chapter10.SubsmoothCalculus
import RockafellarWets.Chapter10.SubsmoothRepresentations
import RockafellarWets.Chapter9.LipschitzSubgradientLimits
import RockafellarWets.Chapter9.LipschitzModulus

open Set Filter Topology Metric
open scoped InnerProductSpace NNReal

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Definitions

/-- The mapping `T + ρI` restricted to `V`. -/
def svShiftOn (T : E → Set E) (ρ : ℝ) (V : Set E) (x : E) : Set E :=
  {w | x ∈ V ∧ ∃ v ∈ T x, w = v + ρ • x}

/-- **Example 12.28**: `T` is hypomonotone at `x̄` if `T + ρI` is monotone on a
neighborhood `V` of `x̄` for some `ρ ≥ 0`. -/
def SvHypomonotoneAt (T : E → Set E) (xbar : E) : Prop :=
  ∃ V ∈ 𝓝 xbar, ∃ ρ : ℝ, 0 ≤ ρ ∧ SvMonotone (svShiftOn T ρ V)

/-- **Example 12.28**: hypomonotonicity at every point of `O`. -/
def SvHypomonotoneOn (T : E → Set E) (O : Set E) : Prop :=
  ∀ xbar ∈ O, SvHypomonotoneAt T xbar

/-- **Example 12.28**: cyclical hypomonotonicity at `x̄`, defined analogously. -/
def SvCyclicallyHypomonotoneAt (T : E → Set E) (xbar : E) : Prop :=
  ∃ V ∈ 𝓝 xbar, ∃ ρ : ℝ, 0 ≤ ρ ∧ SvCyclicallyMonotone (svShiftOn T ρ V)

/-- Cyclical hypomonotonicity at every point of `O`. -/
def SvCyclicallyHypomonotoneOn (T : E → Set E) (O : Set E) : Prop :=
  ∀ xbar ∈ O, SvCyclicallyHypomonotoneAt T xbar

theorem inner_shift_eq (ρ : ℝ) (x₀ x₁ v₀ v₁ : E) :
    ⟪(v₁ + ρ • x₁) - (v₀ + ρ • x₀), x₁ - x₀⟫_ℝ = ⟪v₁ - v₀, x₁ - x₀⟫_ℝ + ρ * ‖x₁ - x₀‖ ^ 2 := by
  have e : (v₁ + ρ • x₁) - (v₀ + ρ • x₀) = (v₁ - v₀) + ρ • (x₁ - x₀) := by
    rw [smul_sub]
    abel
  rw [e, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]

/-- The displayed form of hypomonotonicity:
`⟪v₁ - v₀, x₁ - x₀⟫ ≥ -ρ‖x₁ - x₀‖²` for `xᵢ ∈ V`, `vᵢ ∈ T(xᵢ)`. -/
theorem svMonotone_svShiftOn_iff {T : E → Set E} {ρ : ℝ} {V : Set E} :
    SvMonotone (svShiftOn T ρ V) ↔ ∀ x₀ ∈ V, ∀ x₁ ∈ V, ∀ v₀ ∈ T x₀, ∀ v₁ ∈ T x₁,
      -ρ * ‖x₁ - x₀‖ ^ 2 ≤ ⟪v₁ - v₀, x₁ - x₀⟫_ℝ := by
  constructor
  · intro h x₀ hx₀ x₁ hx₁ v₀ hv₀ v₁ hv₁
    have := h ⟨hx₀, v₀, hv₀, rfl⟩ ⟨hx₁, v₁, hv₁, rfl⟩
    rw [inner_shift_eq] at this
    linarith
  · rintro h x₀ w₀ ⟨hx₀, v₀, hv₀, rfl⟩ x₁ w₁ ⟨hx₁, v₁, hv₁, rfl⟩
    rw [inner_shift_eq]
    linarith [h x₀ hx₀ x₁ hx₁ v₀ hv₀ v₁ hv₁]

theorem svHypomonotoneAt_iff {T : E → Set E} {xbar : E} :
    SvHypomonotoneAt T xbar ↔ ∃ V ∈ 𝓝 xbar, ∃ ρ : ℝ, 0 ≤ ρ ∧
      ∀ x₀ ∈ V, ∀ x₁ ∈ V, ∀ v₀ ∈ T x₀, ∀ v₁ ∈ T x₁,
        -ρ * ‖x₁ - x₀‖ ^ 2 ≤ ⟪v₁ - v₀, x₁ - x₀⟫_ℝ := by
  simp only [SvHypomonotoneAt, svMonotone_svShiftOn_iff]

/-- Cyclical hypomonotonicity implies hypomonotonicity. -/
theorem SvCyclicallyHypomonotoneAt.svHypomonotoneAt {T : E → Set E} {xbar : E}
    (h : SvCyclicallyHypomonotoneAt T xbar) : SvHypomonotoneAt T xbar := by
  obtain ⟨V, hV, ρ, hρ, hc⟩ := h
  exact ⟨V, hV, ρ, hρ, hc.svMonotone⟩

end Definitions

section PartA

/-- **Example 12.28(a)**: a single-valued mapping that is strictly continuous at
every point of an open set `O` is hypomonotone on `O`. -/
theorem svHypomonotoneOn_of_strictlyContinuousAt {F : E → E} {O : Set E}
    (hF : ∀ x ∈ O, StrictlyContinuousAt F x) :
    SvHypomonotoneOn (fun x ↦ ({F x} : Set E)) O := by
  intro xbar hxbar
  obtain ⟨k, V, hV, hlip⟩ := strictlyContinuousAt_iff.1 (hF xbar hxbar)
  refine svHypomonotoneAt_iff.2 ⟨V, hV, k, k.2, fun x₀ hx₀ x₁ hx₁ v₀ hv₀ v₁ hv₁ ↦ ?_⟩
  rw [mem_singleton_iff] at hv₀ hv₁
  subst hv₀ hv₁
  have hd := hlip.dist_le_mul x₁ hx₁ x₀ hx₀
  rw [dist_eq_norm, dist_eq_norm] at hd
  have hcs := neg_le_of_abs_le (abs_real_inner_le_norm (F x₁ - F x₀) (x₁ - x₀))
  have hk : ‖F x₁ - F x₀‖ * ‖x₁ - x₀‖ ≤ k * ‖x₁ - x₀‖ * ‖x₁ - x₀‖ :=
    mul_le_mul_of_nonneg_right hd (norm_nonneg _)
  nlinarith

end PartA

section Subgradients

variable [FiniteDimensional ℝ E]

/-- Subgradients of a function with convex epigraph are cyclically monotone,
without a properness assumption. -/
theorem svCyclicallyMonotone_subdifferential_of_convex_epigraph {g : E → EReal}
    (hc : Convex ℝ (epigraph g)) : SvCyclicallyMonotone (subdifferential g) := by
  intro m _ x v hv
  choose a ha using fun i ↦ (hv i).1
  have hineq : ∀ i, ⟪v i, x (finRotate _ i) - x i⟫_ℝ ≤ a (finRotate _ i) - a i := by
    intro i
    have h := forall_le_of_mem_subdifferential_of_convex hc (ha i) (hv i) (x (finRotate _ i))
    rw [ha (finRotate _ i), EReal.coe_le_coe_iff] at h
    linarith
  calc cyclicSum x v ≤ ∑ i, (a (finRotate _ i) - a i) :=
        Finset.sum_le_sum fun i _ ↦ hineq i
    _ = 0 := by rw [Finset.sum_sub_distrib, Equiv.sum_comp, sub_self]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem add_half_sq_eq_sub_quadratic (f : E → EReal) (ρ : ℝ) :
    (fun z ↦ f z + ((ρ / 2 * ‖z‖ ^ 2 : ℝ) : EReal)) =
      fun z ↦ f z - (((-ρ) / 2 * ‖z‖ ^ 2 : ℝ) : EReal) := by
  funext z
  rw [sub_eq_add_neg, ← EReal.coe_neg]
  congr 2
  ring

/-- 8.8(c) for the quadratic `½ρ‖·‖²`: `v ∈ ∂(f + ½ρ‖·‖²)(x) ↔ v - ρx ∈ ∂f(x)`. -/
theorem mem_subdifferential_add_half_sq_iff {f : E → EReal} {ρ : ℝ} {x v : E} :
    v ∈ subdifferential (fun z ↦ f z + ((ρ / 2 * ‖z‖ ^ 2 : ℝ) : EReal)) x ↔
      v - ρ • x ∈ subdifferential f x := by
  rw [add_half_sq_eq_sub_quadratic, mem_subdifferential_sub_quadratic_iff, neg_smul,
    ← sub_eq_add_neg]

/-- Subgradients only depend on the function near the point. -/
theorem subdifferential_eq_of_eventuallyEq {f g : E → EReal} {x : E} (he : f =ᶠ[𝓝 x] g) :
    subdifferential f x = subdifferential g x := by
  by_cases hfin : ∃ c : ℝ, f x = c
  · obtain ⟨c, hc⟩ := hfin
    exact subdifferential_congr_nhds_of_finite hc he
  · have hgx : ¬∃ c : ℝ, g x = c := by
      rwa [← (he.self_of_nhds : f x = g x)]
    ext v
    constructor
    · intro hv
      exact absurd hv.1 hfin
    · intro hv
      exact absurd hv.1 hgx

omit [FiniteDimensional ℝ E] in
/-- Convexity of `g + δ_C` gives convexity of `g` on `C` for real values. -/
theorem convexOn_of_convex_epigraph_eq_coe {G : E → EReal} {C : Set E} {φ : E → ℝ}
    (hC : Convex ℝ C) (hG : Convex ℝ (epigraph G)) (hGφ : ∀ y ∈ C, G y = (φ y : EReal)) :
    ConvexOn ℝ C φ := by
  refine ⟨hC, fun x hx y hy a b ha hb hab ↦ ?_⟩
  have hxe : (x, φ x) ∈ epigraph G := by rw [mem_epigraph_iff, hGφ x hx]
  have hye : (y, φ y) ∈ epigraph G := by rw [mem_epigraph_iff, hGφ y hy]
  have h := hG hxe hye ha hb hab
  have he : a • ((x, φ x) : E × ℝ) + b • (y, φ y) = (a • x + b • y, a * φ x + b * φ y) := by
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  rw [he, mem_epigraph_iff, hGφ _ (hC hx hy ha hb hab), EReal.coe_le_coe_iff] at h
  simpa only [smul_eq_mul] using h

omit [FiniteDimensional ℝ E] in
open Classical in
/-- A real function convex on `C`, extended by `∞` off `C`, has a convex epigraph. -/
theorem convex_epigraph_restrict_of_convexOn {C : Set E} {φ : E → ℝ} (hφ : ConvexOn ℝ C φ) :
    Convex ℝ (epigraph fun y ↦ if y ∈ C then (φ y : EReal) else ⊤) := by
  classical
  rintro ⟨x, α⟩ hx ⟨y, β⟩ hy a b ha hb hab
  rw [mem_epigraph_iff] at hx hy
  have hxC : x ∈ C := by
    by_contra hn
    rw [if_neg hn] at hx
    exact absurd hx (not_le.2 (EReal.coe_lt_top _))
  have hyC : y ∈ C := by
    by_contra hn
    rw [if_neg hn] at hy
    exact absurd hy (not_le.2 (EReal.coe_lt_top _))
  rw [if_pos hxC, EReal.coe_le_coe_iff] at hx
  rw [if_pos hyC, EReal.coe_le_coe_iff] at hy
  have he : a • ((x, α) : E × ℝ) + b • (y, β) = (a • x + b • y, a * α + b * β) := by
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  rw [he, mem_epigraph_iff, if_pos (hφ.1 hxC hyC ha hb hab), EReal.coe_le_coe_iff]
  have h := hφ.2 hxC hyC ha hb hab
  simp only [smul_eq_mul] at h
  nlinarith

end Subgradients

section PartB

variable [FiniteDimensional ℝ E]

/-- **Example 12.28(b)**, the necessity half: hypomonotonicity of `∂f` at `x̄`
makes `f + ½ρ‖·‖²` convex on a ball around `x̄`. -/
theorem exists_convex_of_svHypomonotoneAt_subdifferential {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) {xbar : E} (h : SvHypomonotoneAt (subdifferential f) xbar) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ∃ r > 0,
      Convex ℝ (epigraph fun x ↦ f x + ((ρ / 2 * ‖x‖ ^ 2 : ℝ) : EReal) +
        indicatorVA (ball xbar r) x) ∧
      SvMonotone (svShiftOn (subdifferential f) ρ (ball xbar r)) := by
  obtain ⟨V, hV, ρ, hρ, hmono⟩ := h
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.1 hV
  have hg : ∀ y, ⊥ < f y + ((ρ / 2 * ‖y‖ ^ 2 : ℝ) : EReal) :=
    (isProper_add_coe hp fun y : E ↦ ρ / 2 * ‖y‖ ^ 2).2
  have hgl : LowerSemicontinuous fun y ↦ f y + ((ρ / 2 * ‖y‖ ^ 2 : ℝ) : EReal) :=
    lowerSemicontinuous_add_coe hl (by fun_prop)
  have hmonoB : SvMonotone (svShiftOn (subdifferential f) ρ (ball xbar r)) := by
    rintro x₀ w₀ ⟨hx₀, v₀, hv₀, rfl⟩ x₁ w₁ ⟨hx₁, v₁, hv₁, rfl⟩
    exact hmono ⟨hrV hx₀, v₀, hv₀, rfl⟩ ⟨hrV hx₁, v₁, hv₁, rfl⟩
  refine ⟨ρ, hρ, r, hr, ?_, hmonoB⟩
  refine convex_epigraph_add_indicator_ball_of_monotoneOn hg hgl xbar hr ?_
  intro x₀ u₀ hx₀ hu₀ x₁ u₁ hx₁ hu₁
  rw [mem_subdifferential_add_half_sq_iff] at hu₀ hu₁
  have := hmonoB ⟨hx₀, u₀ - ρ • x₀, hu₀, by abel⟩ ⟨hx₁, u₁ - ρ • x₁, hu₁, by abel⟩
  exact this

/-- **Example 12.28(b)**, the sufficiency half with cyclical hypomonotonicity:
if `f + ½ρ‖·‖²` is convex on a convex neighborhood `V` of `x̄`, then `∂f + ρI`
is cyclically monotone on the interior of `V`. -/
theorem svCyclicallyMonotone_svShiftOn_of_convex {f : E → EReal} {ρ : ℝ} {V : Set E}
    (hc : Convex ℝ (epigraph fun x ↦ f x + ((ρ / 2 * ‖x‖ ^ 2 : ℝ) : EReal) + indicatorVA V x)) :
    SvCyclicallyMonotone (svShiftOn (subdifferential f) ρ (interior V)) := by
  refine (svCyclicallyMonotone_subdifferential_of_convex_epigraph hc).mono ?_
  rintro x w ⟨hx, v, hv, rfl⟩
  have he : (fun y ↦ f y + ((ρ / 2 * ‖y‖ ^ 2 : ℝ) : EReal) + indicatorVA V y) =ᶠ[𝓝 x]
      fun y ↦ f y + ((ρ / 2 * ‖y‖ ^ 2 : ℝ) : EReal) := by
    filter_upwards [interior_mem_nhds.2 (mem_interior_iff_mem_nhds.1 hx)] with y hy
    rw [indicatorVA_apply_mem (interior_subset hy), add_zero]
  rw [subdifferential_eq_of_eventuallyEq he, mem_subdifferential_add_half_sq_iff,
    add_sub_cancel_right]
  exact hv

/-- **Example 12.28(b) (hypomonotone subgradient mappings).**  For a proper lsc
`f`, `∂f` is hypomonotone at `x̄` exactly when `f + ½ρ‖·‖²` is convex on a
(convex) neighborhood of `x̄` for some `ρ ≥ 0`, and then `∂f` is cyclically
hypomonotone at `x̄`. -/
theorem svHypomonotoneAt_subdifferential_iff {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (xbar : E) :
    (SvHypomonotoneAt (subdifferential f) xbar ↔
      ∃ ρ : ℝ, 0 ≤ ρ ∧ ∃ V ∈ 𝓝 xbar, Convex ℝ V ∧
        Convex ℝ (epigraph fun x ↦ f x + ((ρ / 2 * ‖x‖ ^ 2 : ℝ) : EReal) + indicatorVA V x)) ∧
      (SvHypomonotoneAt (subdifferential f) xbar →
        SvCyclicallyHypomonotoneAt (subdifferential f) xbar) := by
  have hsuff : ∀ ρ : ℝ, 0 ≤ ρ → ∀ V ∈ 𝓝 xbar,
      Convex ℝ (epigraph fun x ↦ f x + ((ρ / 2 * ‖x‖ ^ 2 : ℝ) : EReal) + indicatorVA V x) →
      SvCyclicallyHypomonotoneAt (subdifferential f) xbar :=
    fun ρ hρ V hV hc ↦ ⟨interior V, interior_mem_nhds.2 hV, ρ, hρ,
      svCyclicallyMonotone_svShiftOn_of_convex hc⟩
  have hnec : SvHypomonotoneAt (subdifferential f) xbar →
      ∃ ρ : ℝ, 0 ≤ ρ ∧ ∃ V ∈ 𝓝 xbar, Convex ℝ V ∧
        Convex ℝ (epigraph fun x ↦ f x + ((ρ / 2 * ‖x‖ ^ 2 : ℝ) : EReal) + indicatorVA V x) := by
    intro h
    obtain ⟨ρ, hρ, r, hr, hc, -⟩ := exists_convex_of_svHypomonotoneAt_subdifferential hp hl h
    exact ⟨ρ, hρ, ball xbar r, ball_mem_nhds xbar hr, convex_ball xbar r, hc⟩
  refine ⟨⟨hnec, fun ⟨ρ, hρ, V, hV, _, hc⟩ ↦ (hsuff ρ hρ V hV hc).svHypomonotoneAt⟩, fun h ↦ ?_⟩
  obtain ⟨ρ, hρ, V, hV, -, hc⟩ := hnec h
  exact hsuff ρ hρ V hV hc

end PartB

section PartC

variable [FiniteDimensional ℝ E]

/-- **Example 12.28(c)**, necessity: a lower-`C²` function on an open set `O` is
finite and lsc there, with `∂f` nonempty-valued and hypomonotone on `O`. -/
theorem properties_of_isLowerCOn_two {f : E → EReal} {O : Set E} (hO : IsOpen O)
    (hfin : ∀ x ∈ O, f x ≠ ⊥ ∧ f x ≠ ⊤) (hf : IsLowerCOn 2 (fun x ↦ (f x).toReal) O) :
    LowerSemicontinuousOn f O ∧ (∀ x ∈ O, (subdifferential f x).Nonempty) ∧
      SvHypomonotoneOn (subdifferential f) O := by
  classical
  have hfeq : ∀ x ∈ O, f x = (((f x).toReal : ℝ) : EReal) := fun x hx ↦
    (EReal.coe_toReal (hfin x hx).2 (hfin x hx).1).symm
  have hcont := hf.continuousOn (by norm_num)
  refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · have hca : ContinuousAt (fun y ↦ (((f y).toReal : ℝ) : EReal)) x :=
      continuous_coe_real_ereal.continuousAt.comp (hcont.continuousAt (hO.mem_nhds hx))
    have he : (fun y ↦ (((f y).toReal : ℝ) : EReal)) =ᶠ[𝓝 x] f := by
      filter_upwards [hO.mem_nhds hx] with y hy using (hfeq y hy).symm
    exact (hca.congr he).lowerSemicontinuousAt.lowerSemicontinuousWithinAt O
  all_goals
    obtain ⟨δ, hδ, hδO, ρ, hρ, hconv⟩ := hf.exists_convex_sub_quadratic x hx
    set φ : E → ℝ := fun y ↦ (f y).toReal + ρ * ‖y‖ ^ 2 with hφ
    set G : E → EReal := fun y ↦ if y ∈ ball x δ then (φ y : EReal) else ⊤ with hG
    have hGc : Convex ℝ (epigraph G) := convex_epigraph_restrict_of_convexOn hconv
    have hloc : ∀ y ∈ ball x δ,
        G =ᶠ[𝓝 y] fun z ↦ f z + (((2 * ρ) / 2 * ‖z‖ ^ 2 : ℝ) : EReal) := by
      intro y hy
      filter_upwards [isOpen_ball.mem_nhds hy] with z hz
      simp only [hG, if_pos hz, hφ]
      rw [hfeq z (hδO hz), EReal.toReal_coe, ← EReal.coe_add]
      congr 1
      ring
    have hsub : ∀ y ∈ ball x δ, ∀ v, v ∈ subdifferential G y ↔
        v - (2 * ρ) • y ∈ subdifferential f y := by
      intro y hy v
      rw [subdifferential_eq_of_eventuallyEq (hloc y hy), mem_subdifferential_add_half_sq_iff]
  · obtain ⟨v, hv⟩ := exists_subgradient_of_convexOn isOpen_ball hconv (mem_ball_self hδ)
    have hGx : G x = ((φ x : ℝ) : EReal) := by simp only [hG, if_pos (mem_ball_self hδ)]
    have hvG : v ∈ subdifferential G x := by
      refine (mem_subdifferential_iff_of_convex_of_eq_coe hGc hGx).2 fun w ↦ ?_
      by_cases hw : w ∈ ball x δ
      · simp only [hG, if_pos hw, EReal.coe_le_coe_iff]
        exact hv w hw
      · simp only [hG, if_neg hw]
        exact le_top
    exact ⟨_, (hsub x (mem_ball_self hδ) v).1 hvG⟩
  · refine ⟨ball x δ, ball_mem_nhds x hδ, 2 * ρ, by positivity, ?_⟩
    rintro x₀ w₀ ⟨hx₀, v₀, hv₀, rfl⟩ x₁ w₁ ⟨hx₁, v₁, hv₁, rfl⟩
    have h₀ : v₀ + (2 * ρ) • x₀ ∈ subdifferential G x₀ := by
      rw [hsub x₀ hx₀, add_sub_cancel_right]
      exact hv₀
    have h₁ : v₁ + (2 * ρ) • x₁ ∈ subdifferential G x₁ := by
      rw [hsub x₁ hx₁, add_sub_cancel_right]
      exact hv₁
    exact (svCyclicallyMonotone_subdifferential_of_convex_epigraph hGc).svMonotone h₀ h₁

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Lower semicontinuity relative to a neighborhood is lower semicontinuity. -/
theorem lowerSemicontinuousAt_of_withinAt_of_mem_nhds {k : E → EReal} {s : Set E} {x : E}
    (h : LowerSemicontinuousWithinAt k s x) (hs : s ∈ 𝓝 x) : LowerSemicontinuousAt k x := by
  intro a ha
  have h' := h a ha
  rw [nhdsWithin_eq_nhds.2 hs] at h'
  exact h'

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
open Classical in
/-- Restricting a function that is lsc on an open set to a closed ball inside
it, with value `∞` outside the ball, gives an lsc function. -/
theorem lowerSemicontinuous_restrict_closedBall {k : E → EReal} {O : Set E} (hO : IsOpen O)
    (hl : LowerSemicontinuousOn k O) {c : E} {r : ℝ} (hcr : closedBall c r ⊆ O) :
    LowerSemicontinuous fun y ↦ if y ∈ closedBall c r then k y else ⊤ := by
  intro y a ha
  by_cases hy : y ∈ closedBall c r
  · simp only [if_pos hy] at ha
    have hk : LowerSemicontinuousAt k y :=
      lowerSemicontinuousAt_of_withinAt_of_mem_nhds (hl y (hcr hy)) (hO.mem_nhds (hcr hy))
    filter_upwards [hk a ha] with z hz
    by_cases hzc : z ∈ closedBall c r
    · simp only [if_pos hzc]
      exact hz
    · simp only [if_neg hzc]
      exact lt_of_lt_of_le hz le_top
  · simp only [if_neg hy] at ha
    filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hy] with z hz
    simp only [if_neg (show z ∉ closedBall c r from hz)]
    exact ha

/-- **Example 12.28(c)**, sufficiency: if `f` is finite and lsc on an open `O`
and `∂f` is hypomonotone on `O`, then `f` is lower-`C²` on `O`. -/
theorem isLowerCOn_two_of_svHypomonotoneOn {f : E → EReal} {O : Set E} (hO : IsOpen O)
    (hfin : ∀ x ∈ O, f x ≠ ⊥ ∧ f x ≠ ⊤) (hl : LowerSemicontinuousOn f O)
    (hh : SvHypomonotoneOn (subdifferential f) O) :
    IsLowerCOn 2 (fun x ↦ (f x).toReal) O := by
  classical
  have hfeq : ∀ x ∈ O, f x = (((f x).toReal : ℝ) : EReal) := fun x hx ↦
    (EReal.coe_toReal (hfin x hx).2 (hfin x hx).1).symm
  refine isLowerCOn_two_iff_locally_convex_sub.2 fun x hx ↦ ?_
  obtain ⟨V, hV, ρ, hρ, hmono⟩ := hh x hx
  obtain ⟨r, hr, hrOV⟩ := Metric.mem_nhds_iff.1 (inter_mem (hO.mem_nhds hx) hV)
  set c : ℝ := r / 2
  have hc : 0 < c := half_pos hr
  have hcl : closedBall x c ⊆ O ∩ V := (closedBall_subset_ball (half_lt_self hr)).trans hrOV
  set k : E → EReal := fun y ↦ f y + ((ρ / 2 * ‖y‖ ^ 2 : ℝ) : EReal) with hk
  set h : E → EReal := fun y ↦ if y ∈ closedBall x c then k y else ⊤ with hhdef
  have hkl : LowerSemicontinuousOn k O := fun y hy ↦
    (lowerSemicontinuousAt_of_withinAt_of_mem_nhds (hl y hy) (hO.mem_nhds hy)).add'
      (continuous_coe_real_ereal.comp
      (by fun_prop : Continuous fun z : E ↦ ρ / 2 * ‖z‖ ^ 2)).continuousAt.lowerSemicontinuousAt
      (EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inl (hfin y hy).1))
      |>.lowerSemicontinuousWithinAt O
  have hhl : LowerSemicontinuous h :=
    lowerSemicontinuous_restrict_closedBall hO hkl (hcl.trans inter_subset_left)
  have hhb : ∀ y, ⊥ < h y := by
    intro y
    by_cases hy : y ∈ closedBall x c
    · simp only [hhdef, if_pos hy, hk]
      exact EReal.bot_lt_add_iff.2 ⟨bot_lt_iff_ne_bot.2 (hfin y (hcl hy).1).1, EReal.bot_lt_coe _⟩
    · simp only [hhdef, if_neg hy]
      exact bot_lt_top
  have hloc : ∀ y ∈ ball x c, h =ᶠ[𝓝 y] k := by
    intro y hy
    filter_upwards [isOpen_ball.mem_nhds hy] with z hz
    simp only [hhdef, if_pos (ball_subset_closedBall hz)]
  have hconv := convex_epigraph_add_indicator_ball_of_monotoneOn hhb hhl x hc (by
    intro x₀ u₀ hx₀ hu₀ x₁ u₁ hx₁ hu₁
    rw [subdifferential_eq_of_eventuallyEq (hloc x₀ hx₀), hk,
      mem_subdifferential_add_half_sq_iff] at hu₀
    rw [subdifferential_eq_of_eventuallyEq (hloc x₁ hx₁), hk,
      mem_subdifferential_add_half_sq_iff] at hu₁
    exact hmono ⟨(hcl (ball_subset_closedBall hx₀)).2, u₀ - ρ • x₀, hu₀, by abel⟩
      ⟨(hcl (ball_subset_closedBall hx₁)).2, u₁ - ρ • x₁, hu₁, by abel⟩)
  have hφ : ConvexOn ℝ (ball x c) (fun y ↦ (f y).toReal + ρ / 2 * ‖y‖ ^ 2) := by
    refine convexOn_of_convex_epigraph_eq_coe (convex_ball x c) hconv fun y hy ↦ ?_
    simp only [hhdef, if_pos (ball_subset_closedBall hy), hk, indicatorVA_apply_mem hy, add_zero]
    rw [hfeq y (hcl (ball_subset_closedBall hy)).1, EReal.toReal_coe, ← EReal.coe_add]
  refine ⟨ball x c, isOpen_ball, mem_ball_self hc,
    ball_subset_closedBall.trans (hcl.trans inter_subset_left),
    fun y ↦ (f y).toReal + ρ / 2 * ‖y‖ ^ 2, fun y ↦ ρ / 2 * ‖y‖ ^ 2, hφ, ?_, fun y _ ↦ by ring⟩
  exact (contDiff_const.mul (contDiff_id.norm_sq ℝ)).contDiffOn

/-- **Example 12.28(c)**: `f` is lower-`C²` on an open set `O` if and only if `f`
is finite and lsc on `O` with `∂f` nonempty-valued and hypomonotone on `O`. -/
theorem isLowerCOn_two_iff_svHypomonotoneOn {f : E → EReal} {O : Set E} (hO : IsOpen O) :
    ((∀ x ∈ O, f x ≠ ⊥ ∧ f x ≠ ⊤) ∧ IsLowerCOn 2 (fun x ↦ (f x).toReal) O) ↔
      (∀ x ∈ O, f x ≠ ⊥ ∧ f x ≠ ⊤) ∧ LowerSemicontinuousOn f O ∧
        (∀ x ∈ O, (subdifferential f x).Nonempty) ∧ SvHypomonotoneOn (subdifferential f) O := by
  constructor
  · rintro ⟨hfin, hf⟩
    exact ⟨hfin, properties_of_isLowerCOn_two hO hfin hf⟩
  · rintro ⟨hfin, hl, -, hh⟩
    exact ⟨hfin, isLowerCOn_two_of_svHypomonotoneOn hO hfin hl hh⟩

end PartC

end RW
