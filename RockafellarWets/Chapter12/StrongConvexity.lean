/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Strong convexity (Definition 12.58)

A proper function `f : ℝⁿ → ℝ̄` is *strongly convex* if for some `σ > 0`
`f((1 - τ)x₀ + τx₁) ≤ (1 - τ)f(x₀) + τf(x₁) - ½στ(1 - τ)|x₀ - x₁|²` for all
`x₀, x₁` and `τ ∈ (0, 1)`.

* `RW.StronglyConvexWith σ f` is this inequality with constant `σ`, written in
  extended-real arithmetic for an arbitrary real `σ`.  For functions that never
  take the value `-∞` (in particular proper functions) the convention
  `⊥ + ⊤ = ⊥` of `EReal` is never invoked, so the inequality is the book's.
  A negative constant gives the hypoconvexity inequality of 12.61(c).
* `RW.IsStronglyConvex f` is Definition 12.58: `f` is proper and satisfies the
  inequality for some `σ > 0`.
* `RW.SegmentConvex g` is the ordinary convexity inequality along open
  segments; `RW.convex_epigraph_iff_segmentConvex` identifies it with epigraph
  convexity for functions without the value `-∞`.

The shifted-quadratic equivalence of Exercise 12.59 (b) ⇔ (c), that `f` is
strongly convex with constant `σ` exactly when `f - (σ/2)|·|²` is convex, is
`RW.stronglyConvexWith_iff_convex_epigraph_sub`, with the additive form
`RW.stronglyConvexWith_add_quadratic_iff_convex` and the representation form
`RW.stronglyConvexWith_iff_exists_add_quadratic`.  It rests on the identity
`RW.quadratic_segment_identity`.  Further consequences: monotonicity in the
constant, convexity for nonnegative constants, suprema of families, and real
quadratics `⟪a, x⟫ + c + (σ/2)|x - b|²`, which satisfy the inequality with
equality.

For subgradients (finite dimensions), `RW.mem_subdifferential_sub_quadratic_iff`
shifts limiting subgradients by the quadratic, and
`RW.StronglyConvexWith.le_of_mem_subdifferential` gives the quadratic minorant
`f(y) ≥ f(x) + ⟪v, y - x⟫ + (σ/2)|y - x|²` at each `v ∈ ∂f(x)`.  Consequently
`RW.StronglyConvexWith.inner_sub_ge_of_mem_subdifferential` gives the strong
monotonicity inequality of 12.59 (b) ⇒ (a), and
`RW.subdifferential_inner_ge_iff_svMonotone_sub` reduces strong monotonicity of
`∂f` to monotonicity of `∂(f - (σ/2)|·|²)`, the step that 12.59 (a) ⇒ (c)
completes with Theorem 12.17.
-/

import RockafellarWets.Chapter3.PositiveHomogeneity
import RockafellarWets.Chapter8.ConvexSubgradients
import RockafellarWets.Chapter8.SubgradientsAndGradients
import RockafellarWets.Chapter12.MonotoneMappings

open Set
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Definition 12.58**, the strong convexity inequality with constant `σ`. -/
def StronglyConvexWith (σ : ℝ) (f : E → EReal) : Prop :=
  ∀ ⦃x₀ x₁ : E⦄ ⦃τ : ℝ⦄, 0 < τ → τ < 1 →
    f ((1 - τ) • x₀ + τ • x₁) ≤
      ((1 - τ : ℝ) : EReal) * f x₀ + (τ : EReal) * f x₁ -
        ((σ / 2 * τ * (1 - τ) * ‖x₀ - x₁‖ ^ 2 : ℝ) : EReal)

/-- **Definition 12.58** (strong convexity). -/
def IsStronglyConvex (f : E → EReal) : Prop :=
  IsProper f ∧ ∃ σ : ℝ, 0 < σ ∧ StronglyConvexWith σ f

/-- The convexity inequality along open segments. -/
def SegmentConvex (g : E → EReal) : Prop :=
  ∀ ⦃x₀ x₁ : E⦄ ⦃τ : ℝ⦄, 0 < τ → τ < 1 →
    g ((1 - τ) • x₀ + τ • x₁) ≤ ((1 - τ : ℝ) : EReal) * g x₀ + (τ : EReal) * g x₁

/-- The quadratic identity behind the shifted-quadratic equivalence. -/
theorem quadratic_segment_identity (σ τ : ℝ) (x₀ x₁ : E) :
    (1 - τ) * (σ / 2 * ‖x₀‖ ^ 2) + τ * (σ / 2 * ‖x₁‖ ^ 2) -
        σ / 2 * τ * (1 - τ) * ‖x₀ - x₁‖ ^ 2 =
      σ / 2 * ‖(1 - τ) • x₀ + τ • x₁‖ ^ 2 := by
  have h : ‖(1 - τ) • x₀ + τ • x₁‖ ^ 2 =
      (1 - τ) ^ 2 * ‖x₀‖ ^ 2 + 2 * ((1 - τ) * τ) * ⟪x₀, x₁⟫_ℝ + τ ^ 2 * ‖x₁‖ ^ 2 := by
    rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
      mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
    ring
  rw [h, norm_sub_sq_real]
  ring

private theorem ereal_comb_add_coe (a b : EReal) (r s c τ : ℝ) (hτ₀ : 0 < τ) (hτ₁ : τ < 1) :
    ((1 - τ : ℝ) : EReal) * (a + (r : EReal)) + (τ : EReal) * (b + (s : EReal)) - (c : EReal) =
      (((1 - τ : ℝ) : EReal) * a + (τ : EReal) * b) + (((1 - τ) * r + τ * s - c : ℝ) : EReal) := by
  have h1 : (0 : ℝ) < 1 - τ := sub_pos.mpr hτ₁
  cases a <;> cases b <;>
    simp [EReal.coe_mul_bot_of_pos, EReal.coe_mul_top_of_pos, hτ₀, h1, ← EReal.coe_add,
      ← EReal.coe_mul, ← EReal.coe_sub]
  ring

/-- **12.59 (b) ⇔ (c)**, pointwise form: adding `(σ/2)|·|²` turns the convexity
inequality into the strong convexity inequality with constant `σ`. -/
theorem stronglyConvexWith_add_quadratic_iff {g : E → EReal} {σ : ℝ} :
    StronglyConvexWith σ (fun x ↦ g x + ((σ / 2 * ‖x‖ ^ 2 : ℝ) : EReal)) ↔ SegmentConvex g := by
  have key : ∀ ⦃x₀ x₁ : E⦄ ⦃τ : ℝ⦄, 0 < τ → τ < 1 →
      (((1 - τ : ℝ) : EReal) * (g x₀ + ((σ / 2 * ‖x₀‖ ^ 2 : ℝ) : EReal)) +
          (τ : EReal) * (g x₁ + ((σ / 2 * ‖x₁‖ ^ 2 : ℝ) : EReal)) -
          ((σ / 2 * τ * (1 - τ) * ‖x₀ - x₁‖ ^ 2 : ℝ) : EReal)) =
        (((1 - τ : ℝ) : EReal) * g x₀ + (τ : EReal) * g x₁) +
          ((σ / 2 * ‖(1 - τ) • x₀ + τ • x₁‖ ^ 2 : ℝ) : EReal) := by
    intro x₀ x₁ τ h0 h1
    rw [ereal_comb_add_coe _ _ _ _ _ _ h0 h1, quadratic_segment_identity]
  constructor
  · intro h x₀ x₁ τ h0 h1
    have hh := h (x₀ := x₀) (x₁ := x₁) h0 h1
    simp only at hh
    rw [key h0 h1] at hh
    exact (EReal.addLECancellable_coe _).add_le_add_iff_right.mp hh
  · intro h x₀ x₁ τ h0 h1
    simp only
    rw [key h0 h1]
    exact (EReal.addLECancellable_coe _).add_le_add_iff_right.mpr (h h0 h1)

/-- The segment convexity inequality gives a convex epigraph, with no
restriction on the values of the function. -/
theorem SegmentConvex.convex_epigraph {g : E → EReal} (h : SegmentConvex g) :
    Convex ℝ (epigraph g) := by
  rintro ⟨x, α⟩ hx ⟨y, β⟩ hy a b ha hb hab
  rw [mem_epigraph_iff] at hx hy
  rcases ha.eq_or_lt with rfl | ha'
  · have hb1 : b = 1 := by linarith
    subst hb1
    simpa using hy
  rcases hb.eq_or_lt with rfl | hb'
  · have ha1 : a = 1 := by linarith
    subst ha1
    simpa using hx
  have ha1 : a = 1 - b := by linarith
  subst ha1
  have hb1 : b < 1 := by linarith
  change g ((1 - b) • x + b • y) ≤ (((1 - b) * α + b * β : ℝ) : EReal)
  calc g ((1 - b) • x + b • y) ≤ ((1 - b : ℝ) : EReal) * g x + (b : EReal) * g y := h hb' hb1
    _ ≤ ((1 - b : ℝ) : EReal) * (α : EReal) + (b : EReal) * (β : EReal) := by
      have h1 : (0 : EReal) ≤ ((1 - b : ℝ) : EReal) := by exact_mod_cast ha
      have h2 : (0 : EReal) ≤ (b : EReal) := by exact_mod_cast hb
      gcongr
    _ = (((1 - b) * α + b * β : ℝ) : EReal) := by
      rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]

/-- For functions that never take the value `-∞`, epigraph convexity is the
segment convexity inequality. -/
theorem convex_epigraph_iff_segmentConvex {g : E → EReal} (hg : ∀ x, g x ≠ ⊥) :
    Convex ℝ (epigraph g) ↔ SegmentConvex g := by
  refine ⟨fun h x₀ x₁ τ h0 h1 ↦ ?_, SegmentConvex.convex_epigraph⟩
  exact convex_inequality_of_convex_epigraph_of_ne_bot h hg (by linarith) h0.le (by ring)

/-- Subtracting a real number from a value other than `-∞` gives a value other than `-∞`. -/
theorem ereal_sub_coe_ne_bot {a : EReal} (ha : a ≠ ⊥) (r : ℝ) : a - (r : EReal) ≠ ⊥ := by
  cases a with
  | bot => exact absurd rfl ha
  | top => simp
  | coe a => exact (EReal.coe_sub a r) ▸ EReal.coe_ne_bot _

omit [InnerProductSpace ℝ E] in
/-- Subtracting the quadratic and adding it back recovers the function. -/
theorem sub_quadratic_add_quadratic (f : E → EReal) (σ : ℝ) :
    (fun x ↦ (f x - ((σ / 2 * ‖x‖ ^ 2 : ℝ) : EReal)) + ((σ / 2 * ‖x‖ ^ 2 : ℝ) : EReal)) = f :=
  funext fun _ ↦ EReal.sub_add_cancel

/-- **12.59 (b) ⇒ (c)**: a strongly convex function minus `(σ/2)|·|²` has a
convex epigraph. -/
theorem StronglyConvexWith.convex_epigraph_sub {f : E → EReal} {σ : ℝ}
    (h : StronglyConvexWith σ f) :
    Convex ℝ (epigraph (fun x ↦ f x - ((σ / 2 * ‖x‖ ^ 2 : ℝ) : EReal))) := by
  rw [← sub_quadratic_add_quadratic f σ] at h
  exact (stronglyConvexWith_add_quadratic_iff.mp h).convex_epigraph

/-- **12.59 (b) ⇔ (c)**, the shifted-quadratic equivalence: a function without
the value `-∞` is strongly convex with constant `σ` exactly when
`f - (σ/2)|·|²` is convex. -/
theorem stronglyConvexWith_iff_convex_epigraph_sub {f : E → EReal} (hf : ∀ x, f x ≠ ⊥) (σ : ℝ) :
    StronglyConvexWith σ f ↔
      Convex ℝ (epigraph (fun x ↦ f x - ((σ / 2 * ‖x‖ ^ 2 : ℝ) : EReal))) := by
  refine ⟨StronglyConvexWith.convex_epigraph_sub, fun h ↦ ?_⟩
  rw [← sub_quadratic_add_quadratic f σ]
  exact stronglyConvexWith_add_quadratic_iff.mpr
    ((convex_epigraph_iff_segmentConvex fun x ↦ ereal_sub_coe_ne_bot (hf x) _).mp h)

/-- **12.59 (b) ⇔ (c)**, additive form: `g + (σ/2)|·|²` is strongly convex with
constant `σ` exactly when `g` is convex. -/
theorem stronglyConvexWith_add_quadratic_iff_convex {g : E → EReal} (hg : ∀ x, g x ≠ ⊥) (σ : ℝ) :
    StronglyConvexWith σ (fun x ↦ g x + ((σ / 2 * ‖x‖ ^ 2 : ℝ) : EReal)) ↔
      Convex ℝ (epigraph g) := by
  rw [stronglyConvexWith_add_quadratic_iff, convex_epigraph_iff_segmentConvex hg]

/-- **12.59 (b) ⇔ (c)**, representation form: `f` is strongly convex with
constant `σ` exactly when `f = g + (σ/2)|·|²` for a convex `g`. -/
theorem stronglyConvexWith_iff_exists_add_quadratic {f : E → EReal} (hf : ∀ x, f x ≠ ⊥) (σ : ℝ) :
    StronglyConvexWith σ f ↔ ∃ g : E → EReal, (∀ x, g x ≠ ⊥) ∧ Convex ℝ (epigraph g) ∧
      f = fun x ↦ g x + ((σ / 2 * ‖x‖ ^ 2 : ℝ) : EReal) := by
  constructor
  · intro h
    exact ⟨fun x ↦ f x - ((σ / 2 * ‖x‖ ^ 2 : ℝ) : EReal),
      fun x ↦ ereal_sub_coe_ne_bot (hf x) _, h.convex_epigraph_sub,
      (sub_quadratic_add_quadratic f σ).symm⟩
  · rintro ⟨g, hg, hc, rfl⟩
    exact (stronglyConvexWith_add_quadratic_iff_convex hg σ).mpr hc

/-- Strong convexity with a constant gives strong convexity with every
smaller constant. -/
theorem StronglyConvexWith.mono {f : E → EReal} {σ σ' : ℝ} (h : StronglyConvexWith σ f)
    (hσ : σ' ≤ σ) : StronglyConvexWith σ' f := by
  intro x₀ x₁ τ h0 h1
  refine (h h0 h1).trans (EReal.sub_le_sub le_rfl (EReal.coe_le_coe_iff.mpr ?_))
  have : 0 ≤ τ * (1 - τ) * ‖x₀ - x₁‖ ^ 2 := by
    have : 0 < 1 - τ := sub_pos.mpr h1
    positivity
  nlinarith

/-- With a nonnegative constant, strong convexity includes the convexity
inequality. -/
theorem StronglyConvexWith.segmentConvex {f : E → EReal} {σ : ℝ} (h : StronglyConvexWith σ f)
    (hσ : 0 ≤ σ) : SegmentConvex f := by
  intro x₀ x₁ τ h0 h1
  have := h.mono hσ (x₀ := x₀) (x₁ := x₁) h0 h1
  simpa using this

/-- With a nonnegative constant, a strongly convex function is convex. -/
theorem StronglyConvexWith.convex_epigraph {f : E → EReal} {σ : ℝ} (h : StronglyConvexWith σ f)
    (hσ : 0 ≤ σ) : Convex ℝ (epigraph f) :=
  (h.segmentConvex hσ).convex_epigraph

/-- Strong convexity with constant `0` is convexity. -/
theorem stronglyConvexWith_zero_iff {f : E → EReal} (hf : ∀ x, f x ≠ ⊥) :
    StronglyConvexWith 0 f ↔ Convex ℝ (epigraph f) := by
  rw [convex_epigraph_iff_segmentConvex hf]
  refine ⟨fun h ↦ h.segmentConvex le_rfl, fun h x₀ x₁ τ h0 h1 ↦ ?_⟩
  simpa using h h0 h1

/-- A strongly convex function is convex. -/
theorem IsStronglyConvex.convex_epigraph {f : E → EReal} (h : IsStronglyConvex f) :
    Convex ℝ (epigraph f) := by
  obtain ⟨-, σ, hσ, h⟩ := h
  exact h.convex_epigraph hσ.le

/-- A pointwise supremum of functions that are strongly convex with the same
constant is strongly convex with that constant. -/
theorem StronglyConvexWith.iSup {ι : Sort*} {F : ι → E → EReal} {σ : ℝ}
    (h : ∀ i, StronglyConvexWith σ (F i)) : StronglyConvexWith σ (fun x ↦ ⨆ i, F i x) := by
  intro x₀ x₁ τ h0 h1
  have ha : (0 : EReal) ≤ ((1 - τ : ℝ) : EReal) := by exact_mod_cast (sub_pos.mpr h1).le
  have hb : (0 : EReal) ≤ (τ : EReal) := by exact_mod_cast h0.le
  refine iSup_le fun i ↦ (h i h0 h1).trans (EReal.sub_le_sub ?_ le_rfl)
  gcongr
  · exact le_iSup (fun i ↦ F i x₀) i
  · exact le_iSup (fun i ↦ F i x₁) i

/-- Real quadratic functions `⟪a, x⟫ + c + (σ/2)|x - b|²` are strongly convex with
constant `σ`, with equality in the defining inequality. -/
theorem stronglyConvexWith_quadratic (σ : ℝ) (a b : E) (c : ℝ) :
    StronglyConvexWith σ (fun x ↦ ((⟪a, x⟫_ℝ + c + σ / 2 * ‖x - b‖ ^ 2 : ℝ) : EReal)) := by
  intro x₀ x₁ τ h0 h1
  simp only [← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_sub, EReal.coe_le_coe_iff]
  have hid := quadratic_segment_identity σ τ (x₀ - b) (x₁ - b)
  have hx : (1 - τ) • x₀ + τ • x₁ - b = (1 - τ) • (x₀ - b) + τ • (x₁ - b) := by
    module
  have hd : x₀ - b - (x₁ - b) = x₀ - x₁ := by abel
  rw [hd, ← hx] at hid
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  nlinarith [hid]

section Subgradients

/-- The gradient of `(σ/2)|·|²` at `x` is `σ x`. -/
theorem hasGradientAt_half_mul_norm_sq [CompleteSpace E] (σ : ℝ) (x : E) :
    HasGradientAt (fun z : E ↦ σ / 2 * ‖z‖ ^ 2) (σ • x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h := ((hasFDerivAt_id x).norm_sq).const_mul (σ / 2)
  convert h using 1
  ext w
  simp
  ring

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- Subtracting a real-valued function preserves properness. -/
theorem isProper_sub_coe {f : E → EReal} (hp : IsProper f) (k : E → ℝ) :
    IsProper (fun x ↦ f x - (k x : EReal)) := by
  obtain ⟨⟨z, hz⟩, hb⟩ := hp
  refine ⟨⟨z, ?_⟩, fun x ↦ lt_of_le_of_ne bot_le (ereal_sub_coe_ne_bot (hb x).ne' _).symm⟩
  cases h : f z with
  | bot => exact absurd h (hb z).ne'
  | top => rw [h] at hz; exact absurd hz (lt_irrefl _)
  | coe a =>
    change f z - (k z : EReal) < ⊤
    rw [h, ← EReal.coe_sub]
    exact EReal.coe_lt_top _

variable [FiniteDimensional ℝ E]

/-- Subgradients of `f - (σ/2)|·|²` are the subgradients of `f` shifted by `-σx`
(Exercise 8.8(c) for the quadratic). -/
theorem mem_subdifferential_sub_quadratic_iff {f : E → EReal} {σ : ℝ} {x v : E} :
    v ∈ subdifferential (fun z ↦ f z - ((σ / 2 * ‖z‖ ^ 2 : ℝ) : EReal)) x ↔
      v + σ • x ∈ subdifferential f x := by
  by_cases hfin : ∃ c : ℝ, f x = c
  · obtain ⟨c, hc⟩ := hfin
    let q : E → ℝ := fun z ↦ σ / 2 * ‖z‖ ^ 2
    let g : E → EReal := fun z ↦ f z - (q z : EReal)
    have hgx : g x = ((c - q x : ℝ) : EReal) := by simp [g, hc, EReal.coe_sub]
    have hk : ContDiffAt ℝ 1 q x := (contDiff_const.mul (contDiff_id.norm_sq ℝ)).contDiffAt
    have hsum := (subdifferentials_add_smooth hgx hk).2.1
    have hfg : (fun z ↦ g z + (q z : EReal)) = f := sub_quadratic_add_quadratic f σ
    have hgrad : gradient q x = σ • x := (hasGradientAt_half_mul_norm_sq σ x).gradient
    simp only [hfg, hgrad] at hsum
    change v ∈ subdifferential g x ↔ _
    rw [hsum]
    constructor
    · intro hv
      exact ⟨v, hv, rfl⟩
    · rintro ⟨u, hu, hu'⟩
      rwa [add_right_cancel hu'] at hu
  · have h1 : v + σ • x ∉ subdifferential f x := fun h ↦ hfin h.1
    have h2 : v ∉ subdifferential (fun z ↦ f z - ((σ / 2 * ‖z‖ ^ 2 : ℝ) : EReal)) x := by
      rintro ⟨⟨c, hc⟩, -⟩
      apply hfin
      refine ⟨c + σ / 2 * ‖x‖ ^ 2, ?_⟩
      have := congrArg (fun a : EReal ↦ a + ((σ / 2 * ‖x‖ ^ 2 : ℝ) : EReal)) hc
      simp only [EReal.sub_add_cancel] at this
      rw [this, EReal.coe_add]
    exact iff_of_false h2 h1

/-- The strong subgradient inequality: if `f` is proper and strongly convex with
constant `σ` (any real `σ`), each subgradient `v ∈ ∂f(x)` gives the quadratic
minorant `f(y) ≥ f(x) + ⟪v, y - x⟫ + (σ/2)|y - x|²`. -/
theorem StronglyConvexWith.le_of_mem_subdifferential {f : E → EReal} {σ : ℝ}
    (hp : IsProper f) (h : StronglyConvexWith σ f) {x v : E} (hv : v ∈ subdifferential f x)
    (y : E) : f x + ((⟪v, y - x⟫_ℝ + σ / 2 * ‖y - x‖ ^ 2 : ℝ) : EReal) ≤ f y := by
  obtain ⟨c, hc⟩ := hv.1
  let q : E → ℝ := fun z ↦ σ / 2 * ‖z‖ ^ 2
  let g : E → EReal := fun z ↦ f z - (q z : EReal)
  have hgp : IsProper g := isProper_sub_coe hp q
  have hgc : Convex ℝ (epigraph g) := h.convex_epigraph_sub
  have hgx : g x = ((c - q x : ℝ) : EReal) := by simp [g, hc, EReal.coe_sub]
  have hu : v - σ • x ∈ subdifferential g x := by
    apply mem_subdifferential_sub_quadratic_iff.mpr
    simpa using hv
  have hineq := (mem_subdifferential_iff_of_convex hgc hgp hgx).mp hu y
  rw [hc]
  by_cases hyt : f y = ⊤
  · rw [hyt]
    exact le_top
  · have hy : f y = ((f y).toReal : EReal) := (EReal.coe_toReal hyt (hp.2 y).ne').symm
    have hgy : g y = (((f y).toReal - q y : ℝ) : EReal) := by
      change f y - (q y : EReal) = _
      rw [hy, ← EReal.coe_sub, EReal.toReal_coe]
    rw [hgy, EReal.coe_le_coe_iff] at hineq
    rw [hy, ← EReal.coe_add, EReal.coe_le_coe_iff]
    simp only [q] at hineq
    rw [inner_sub_left, real_inner_smul_left, inner_sub_right, inner_sub_right,
      real_inner_self_eq_norm_sq] at hineq
    rw [norm_sub_sq_real, inner_sub_right, real_inner_comm x y]
    linarith

/-- **12.59 (b) ⇒ (a)**: the subgradients of a proper function that is strongly
convex with constant `σ` satisfy `⟪v₁ - v₀, x₁ - x₀⟫ ≥ σ|x₁ - x₀|²`. -/
theorem StronglyConvexWith.inner_sub_ge_of_mem_subdifferential {f : E → EReal} {σ : ℝ}
    (hp : IsProper f) (h : StronglyConvexWith σ f) {x₀ v₀ x₁ v₁ : E}
    (h₀ : v₀ ∈ subdifferential f x₀) (h₁ : v₁ ∈ subdifferential f x₁) :
    σ * ‖x₁ - x₀‖ ^ 2 ≤ ⟪v₁ - v₀, x₁ - x₀⟫_ℝ := by
  obtain ⟨c₀, hc₀⟩ := h₀.1
  obtain ⟨c₁, hc₁⟩ := h₁.1
  have e₀ := h.le_of_mem_subdifferential hp h₀ x₁
  have e₁ := h.le_of_mem_subdifferential hp h₁ x₀
  rw [hc₀, hc₁, ← EReal.coe_add, EReal.coe_le_coe_iff] at e₀
  rw [hc₀, hc₁, ← EReal.coe_add, EReal.coe_le_coe_iff] at e₁
  rw [norm_sub_rev x₀ x₁] at e₁
  have hi : ⟪v₁ - v₀, x₁ - x₀⟫_ℝ = -⟪v₀, x₁ - x₀⟫_ℝ - ⟪v₁, x₀ - x₁⟫_ℝ := by
    rw [inner_sub_left, ← neg_sub x₁ x₀, inner_neg_right]
    ring
  rw [hi]
  linarith

/-- Strong monotonicity of `∂f` with constant `σ` is monotonicity of
`∂(f - (σ/2)|·|²)` (the reduction used for **12.59 (a) ⇔ (c)**). -/
theorem subdifferential_inner_ge_iff_svMonotone_sub {f : E → EReal} {σ : ℝ} :
    (∀ ⦃x₀ v₀ x₁ v₁ : E⦄, v₀ ∈ subdifferential f x₀ → v₁ ∈ subdifferential f x₁ →
        σ * ‖x₁ - x₀‖ ^ 2 ≤ ⟪v₁ - v₀, x₁ - x₀⟫_ℝ) ↔
      SvMonotone (subdifferential (fun z ↦ f z - ((σ / 2 * ‖z‖ ^ 2 : ℝ) : EReal))) := by
  have hrw : ∀ x₀ v₀ x₁ v₁ : E, ⟪(v₁ + σ • x₁) - (v₀ + σ • x₀), x₁ - x₀⟫_ℝ =
      ⟪v₁ - v₀, x₁ - x₀⟫_ℝ + σ * ‖x₁ - x₀‖ ^ 2 := by
    intro x₀ v₀ x₁ v₁
    have : (v₁ + σ • x₁) - (v₀ + σ • x₀) = (v₁ - v₀) + σ • (x₁ - x₀) := by module
    rw [this, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  constructor
  · intro h x₀ v₀ h₀ x₁ v₁ h₁
    have := h (mem_subdifferential_sub_quadratic_iff.mp h₀)
      (mem_subdifferential_sub_quadratic_iff.mp h₁)
    rw [hrw] at this
    linarith
  · intro h x₀ v₀ x₁ v₁ h₀ h₁
    have h₀' : v₀ - σ • x₀ ∈ subdifferential (fun z ↦ f z - ((σ / 2 * ‖z‖ ^ 2 : ℝ) : EReal)) x₀ :=
      mem_subdifferential_sub_quadratic_iff.mpr (by simpa using h₀)
    have h₁' : v₁ - σ • x₁ ∈ subdifferential (fun z ↦ f z - ((σ / 2 * ‖z‖ ^ 2 : ℝ) : EReal)) x₁ :=
      mem_subdifferential_sub_quadratic_iff.mpr (by simpa using h₁)
    have := h h₀' h₁'
    have e := hrw x₀ (v₀ - σ • x₀) x₁ (v₁ - σ • x₁)
    simp only [sub_add_cancel] at e
    linarith

end Subgradients

end RW
