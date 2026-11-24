/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: monotone mappings from convex-concave functions

This file formalizes Example 12.27.  The product `ℝⁿ × ℝᵐ` is the Euclidean
product `WithLp 2 (E × P)`, and for `l : E → P → ℝ̄` the mapping is
`T(x, y) = ∂ₓl(x, y) × ∂_y[-l](x, y)`.

Monotonicity follows the book's detail: the four subgradient inequalities, at
points where the values are finite, add up to the monotonicity inequality.  The
subgradient inequalities hold for functions with convex epigraphs without a
properness assumption (`forall_le_of_mem_subdifferential_of_convex`).

In the Lagrangian case `l(x, y) = inf_u {f(x, u) - ⟨y, u⟩}` with `f` proper,
lsc and convex, 11.48 gives `(v, u) ∈ T(x, y) ⟺ (v, y) ∈ ∂f(x, u)`, so `T` is
the partial inverse of `∂f`.  The partial swap preserves the monotonicity
pairing, and the maximal monotonicity of `∂f` (12.17) passes to `T`.
-/

import RockafellarWets.Chapter12.ConvexSubgradientMappings
import RockafellarWets.Chapter11.Lagrangians

open Set
open scoped InnerProductSpace

namespace RW

variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]

/-- The mapping `T(x, y) = ∂ₓl(x, y) × ∂_y[-l](x, y)` of Example 12.27. -/
def convexConcaveSubgradientMapping (l : E → P → EReal) (p : WithLp 2 (E × P)) :
    Set (WithLp 2 (E × P)) :=
  {q | q.fst ∈ subdifferential (fun x ↦ l x p.snd) p.fst ∧
    q.snd ∈ subdifferential (fun y ↦ -l p.fst y) p.snd}

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P] in
/-- Two finite lower bounds for `z` and `-z` add to at most zero. -/
theorem add_nonpos_of_coe_le_of_coe_le_neg {A B : ℝ} {z : EReal} (hA : (A : EReal) ≤ z)
    (hB : (B : EReal) ≤ -z) : A + B ≤ 0 := by
  induction z using EReal.rec with
  | bot => exact absurd hA (not_le.2 (EReal.bot_lt_coe A))
  | top =>
    rw [EReal.neg_top] at hB
    exact absurd hB (not_le.2 (EReal.bot_lt_coe B))
  | coe c =>
    rw [EReal.coe_le_coe_iff] at hA
    rw [← EReal.coe_neg, EReal.coe_le_coe_iff] at hB
    linarith

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
theorem inner_withLp_prod_sub (q₀ q₁ p₀ p₁ : WithLp 2 (E × P)) :
    ⟪q₁ - q₀, p₁ - p₀⟫_ℝ =
      ⟪q₁.fst - q₀.fst, p₁.fst - p₀.fst⟫_ℝ + ⟪q₁.snd - q₀.snd, p₁.snd - p₀.snd⟫_ℝ := by
  rw [WithLp.prod_inner_apply]
  rfl

/-- **Example 12.27**, first assertion: if `l` is convex in `x` and concave in
`y`, then `T(x, y) = ∂ₓl(x, y) × ∂_y[-l](x, y)` is monotone. -/
theorem svMonotone_convexConcaveSubgradientMapping {l : E → P → EReal}
    (hx : ∀ y, Convex ℝ (epigraph fun x ↦ l x y)) (hy : ∀ x, Convex ℝ (epigraph fun y ↦ -l x y)) :
    SvMonotone (convexConcaveSubgradientMapping l) := by
  intro p₀ q₀ h₀ p₁ q₁ h₁
  obtain ⟨a₀, ha₀⟩ := h₀.1.1
  obtain ⟨a₁, ha₁⟩ := h₁.1.1
  obtain ⟨b₀, hb₀⟩ := h₀.2.1
  obtain ⟨b₁, hb₁⟩ := h₁.2.1
  have hab₀ : b₀ = -a₀ := by
    change -l p₀.fst p₀.snd = (b₀ : EReal) at hb₀
    change l p₀.fst p₀.snd = (a₀ : EReal) at ha₀
    rw [ha₀, ← EReal.coe_neg] at hb₀
    exact (EReal.coe_injective hb₀).symm
  have hab₁ : b₁ = -a₁ := by
    change -l p₁.fst p₁.snd = (b₁ : EReal) at hb₁
    change l p₁.fst p₁.snd = (a₁ : EReal) at ha₁
    rw [ha₁, ← EReal.coe_neg] at hb₁
    exact (EReal.coe_injective hb₁).symm
  have i₁ := forall_le_of_mem_subdifferential_of_convex (hx p₀.snd) ha₀ h₀.1 p₁.fst
  have i₂ := forall_le_of_mem_subdifferential_of_convex (hx p₁.snd) ha₁ h₁.1 p₀.fst
  have i₃ := forall_le_of_mem_subdifferential_of_convex (hy p₀.fst) hb₀ h₀.2 p₁.snd
  have i₄ := forall_le_of_mem_subdifferential_of_convex (hy p₁.fst) hb₁ h₁.2 p₀.snd
  have s₁ := add_nonpos_of_coe_le_of_coe_le_neg i₁ i₄
  have s₂ := add_nonpos_of_coe_le_of_coe_le_neg i₂ i₃
  rw [inner_withLp_prod_sub, inner_sub_left, inner_sub_left, ← neg_sub p₁.fst p₀.fst,
    inner_neg_right, ← neg_sub p₁.snd p₀.snd, inner_neg_right] at *
  rw [hab₀] at s₂
  rw [hab₁] at s₁
  have e₁ : ⟪q₁.fst, p₁.fst - p₀.fst⟫_ℝ = -⟪q₁.fst, p₀.fst - p₁.fst⟫_ℝ := by
    rw [← inner_neg_right, neg_sub]
  have e₂ : ⟪q₀.snd, p₁.snd - p₀.snd⟫_ℝ = -⟪q₀.snd, p₀.snd - p₁.snd⟫_ℝ := by
    rw [← inner_neg_right, neg_sub]
  linarith

/-- **Example 12.27**, the Lagrangian case through 11.48: `T` is the partial
inverse of `∂f`, `(v, u) ∈ T(x, y) ⟺ (v, y) ∈ ∂f(x, u)`. -/
theorem mem_convexConcaveSubgradientMapping_lagrangian_iff {f : WithLp 2 (E × P) → EReal}
    (hp : IsProper f) (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f))
    (x v : E) (y u : P) :
    WithLp.toLp 2 (v, u) ∈ convexConcaveSubgradientMapping (lagrangian f) (WithLp.toLp 2 (x, y)) ↔
      WithLp.toLp 2 (v, y) ∈ subdifferential f (WithLp.toLp 2 (x, u)) :=
  ((isDualizingParameterization_of_convex hp hl hc).mem_subdifferential_iff_lagrangian
    hc x v u y).symm

/-- **Example 12.27**, second assertion: in the Lagrangian case
`l(x, y) = inf_u {f(x, u) - ⟨y, u⟩}` for a proper lsc convex `f`, the mapping
`T` is maximal monotone. -/
theorem svMaximalMonotone_convexConcaveSubgradientMapping_lagrangian
    {f : WithLp 2 (E × P) → EReal} (hp : IsProper f) (hl : LowerSemicontinuous f)
    (hc : Convex ℝ (epigraph f)) :
    SvMaximalMonotone (convexConcaveSubgradientMapping (lagrangian f)) := by
  have hmono : SvMonotone (convexConcaveSubgradientMapping (lagrangian f)) :=
    svMonotone_convexConcaveSubgradientMapping (convex_epigraph_lagrangian_of_convex hc)
      fun x ↦ (lagrangian_usc_concave f x).2
  have hmax := svMaximalMonotone_subdifferential_of_convex hp hl hc
  refine svMaximalMonotone_iff_forall_inner_nonneg.2 ⟨hmono, fun p q h ↦ ?_⟩
  obtain ⟨⟨x, y⟩, rfl⟩ := (WithLp.toLp_surjective 2) p
  obtain ⟨⟨v, u⟩, rfl⟩ := (WithLp.toLp_surjective 2) q
  rw [mem_convexConcaveSubgradientMapping_lagrangian_iff hp hl hc]
  refine (svMaximalMonotone_iff_forall_inner_nonneg.1 hmax).2 _ _ fun p' q' hq' ↦ ?_
  obtain ⟨⟨x', u'⟩, rfl⟩ := (WithLp.toLp_surjective 2) p'
  obtain ⟨⟨v', y'⟩, rfl⟩ := (WithLp.toLp_surjective 2) q'
  have hT := h (WithLp.toLp 2 (x', y')) (WithLp.toLp 2 (v', u'))
    ((mem_convexConcaveSubgradientMapping_lagrangian_iff hp hl hc x' v' y' u').2 hq')
  rw [inner_withLp_prod_sub] at hT ⊢
  simp only [WithLp.toLp_fst, WithLp.toLp_snd] at hT ⊢
  rw [real_inner_comm (u - u') (y - y')]
  exact hT

/-- **Example 12.27 (monotone mappings from convex-concave functions).**  If
`l(x, y)` is convex in `x` and concave in `y`, the mapping
`T(x, y) = ∂ₓl(x, y) × ∂_y[-l](x, y)` is monotone; in the Lagrangian case
`l(x, y) = inf_u {f(x, u) - ⟨y, u⟩}` for a proper lsc convex `f`, it is maximal
monotone. -/
theorem monotone_mappings_from_convex_concave_functions :
    (∀ l : E → P → EReal, (∀ y, Convex ℝ (epigraph fun x ↦ l x y)) →
        (∀ x, Convex ℝ (epigraph fun y ↦ -l x y)) →
        SvMonotone (convexConcaveSubgradientMapping l)) ∧
      ∀ f : WithLp 2 (E × P) → EReal, IsProper f → LowerSemicontinuous f →
        Convex ℝ (epigraph f) →
          SvMaximalMonotone (convexConcaveSubgradientMapping (lagrangian f)) :=
  ⟨fun _ hx hy ↦ svMonotone_convexConcaveSubgradientMapping hx hy,
    fun _ hp hl hc ↦ svMaximalMonotone_convexConcaveSubgradientMapping_lagrangian hp hl hc⟩

end RW
