/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 11: the linear-quadratic test on line segments

**Lemma 11.15**: a function is linear-quadratic relative to a convex set `C` (given there by a
formula `½⟪x, Ax⟫ + ⟪a, x⟫ + α`) iff it is linear-quadratic relative to every line segment in `C`
(`isLinearQuadraticOn_iff_segments`).
-/

import RockafellarWets.Chapter10.PiecewiseLinearQuadratic
import Mathlib.Analysis.Convex.Intrinsic

open Set Filter
open scoped InnerProductSpace

namespace RW

/-! ### One- and two-variable polynomial identities -/

/-- A quadratic polynomial on `[-1, 1]` is the interpolant of its values at `-1, 0, 1`. -/
theorem quadratic_interp {g : ℝ → ℝ}
    (hg : ∃ c₀ c₁ c₂ : ℝ, ∀ θ ∈ Icc (-1 : ℝ) 1, g θ = c₀ + c₁ * θ + c₂ * θ ^ 2) {θ : ℝ}
    (hθ : θ ∈ Icc (-1 : ℝ) 1) :
    g θ = g 0 + θ * ((g 1 - g (-1)) / 2) + θ ^ 2 * ((g 1 + g (-1)) / 2 - g 0) := by
  obtain ⟨c₀, c₁, c₂, h⟩ := hg
  rw [h θ hθ, h 0 ⟨by norm_num, by norm_num⟩, h 1 ⟨by norm_num, by norm_num⟩,
    h (-1) ⟨by norm_num, by norm_num⟩]
  ring

/-- A quartic polynomial vanishing on `[-1, 1]` has vanishing cubic and quartic coefficients. -/
theorem quartic_top_coeffs_eq_zero {e₀ e₁ e₂ e₃ e₄ : ℝ}
    (h : ∀ θ ∈ Icc (-1 : ℝ) 1, e₀ + e₁ * θ + e₂ * θ ^ 2 + e₃ * θ ^ 3 + e₄ * θ ^ 4 = 0) :
    e₃ = 0 ∧ e₄ = 0 := by
  have h0 := h 0 ⟨by norm_num, by norm_num⟩
  have h1 := h 1 ⟨by norm_num, by norm_num⟩
  have h2 := h (-1) ⟨by norm_num, by norm_num⟩
  have h3 := h (1 / 2) ⟨by norm_num, by norm_num⟩
  have h4 := h (-1 / 2) ⟨by norm_num, by norm_num⟩
  norm_num at h0 h1 h2 h3 h4
  constructor <;> linarith

/-- The plane lemma behind 11.15: a function on `[-1, 1]²` that is quadratic along horizontal
lines, along the three vertical lines `s ∈ {-1, 0, 1}` and along both diagonals is a polynomial of
degree at most two, with coefficients given by its values on `{-1, 0, 1}²`. -/
theorem plane_quadratic {ψ : ℝ → ℝ → ℝ}
    (hH : ∀ t ∈ Icc (-1 : ℝ) 1, ∃ c₀ c₁ c₂ : ℝ, ∀ s ∈ Icc (-1 : ℝ) 1,
      ψ s t = c₀ + c₁ * s + c₂ * s ^ 2)
    (hV : ∀ σ : ℝ, σ = -1 ∨ σ = 0 ∨ σ = 1 → ∃ c₀ c₁ c₂ : ℝ, ∀ t ∈ Icc (-1 : ℝ) 1,
      ψ σ t = c₀ + c₁ * t + c₂ * t ^ 2)
    (hD₁ : ∃ c₀ c₁ c₂ : ℝ, ∀ θ ∈ Icc (-1 : ℝ) 1, ψ θ θ = c₀ + c₁ * θ + c₂ * θ ^ 2)
    (hD₂ : ∃ c₀ c₁ c₂ : ℝ, ∀ θ ∈ Icc (-1 : ℝ) 1, ψ θ (-θ) = c₀ + c₁ * θ + c₂ * θ ^ 2)
    {s t : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) (ht : t ∈ Icc (-1 : ℝ) 1) :
    ψ s t = ψ 0 0 + s * ((ψ 1 0 - ψ (-1) 0) / 2) + t * ((ψ 0 1 - ψ 0 (-1)) / 2)
      + s ^ 2 * ((ψ 1 0 + ψ (-1) 0) / 2 - ψ 0 0) + t ^ 2 * ((ψ 0 1 + ψ 0 (-1)) / 2 - ψ 0 0)
      + s * t * ((ψ 1 1 - ψ 1 (-1) - ψ (-1) 1 + ψ (-1) (-1)) / 4) := by
  set a := ψ 0 0 with ha
  set b := ψ 1 0 with hb
  set c := ψ (-1) 0 with hc
  set d := ψ 0 1 with hd
  set e := ψ 0 (-1) with he
  set p := ψ 1 1 with hp
  set q := ψ 1 (-1) with hq
  set r := ψ (-1) 1 with hr
  set u := ψ (-1) (-1) with hu
  -- the nine coefficients of the Lagrange expansion
  have hP : ∀ s ∈ Icc (-1 : ℝ) 1, ∀ t ∈ Icc (-1 : ℝ) 1, ψ s t =
      a + (d - e) / 2 * t + ((d + e) / 2 - a) * t ^ 2
      + (b - c) / 2 * s + ((p - q) / 2 - (r - u) / 2) / 2 * s * t
      + (((p + q) / 2 - b) - ((r + u) / 2 - c)) / 2 * s * t ^ 2
      + ((b + c) / 2 - a) * s ^ 2 + (((p - q) / 2 + (r - u) / 2) / 2 - (d - e) / 2) * s ^ 2 * t
      + ((((p + q) / 2 - b) + ((r + u) / 2 - c)) / 2 - ((d + e) / 2 - a)) * s ^ 2 * t ^ 2 := by
    intro s hs t ht
    have hs1 := quadratic_interp (g := fun s ↦ ψ s t) (hH t ht) hs
    have hv : ∀ σ : ℝ, σ = -1 ∨ σ = 0 ∨ σ = 1 →
        ψ σ t = ψ σ 0 + t * ((ψ σ 1 - ψ σ (-1)) / 2) + t ^ 2 * ((ψ σ 1 + ψ σ (-1)) / 2 - ψ σ 0) :=
      fun σ hσ ↦ quadratic_interp (g := fun t ↦ ψ σ t) (hV σ hσ) ht
    simp only at hs1
    rw [hs1, hv 0 (Or.inr (Or.inl rfl)), hv 1 (Or.inr (Or.inr rfl)), hv (-1) (Or.inl rfl)]
    ring
  have hm1 : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  -- the two diagonals kill the cubic and quartic terms
  have key₁ : (((p - q) / 2 + (r - u) / 2) / 2 - (d - e) / 2)
      + (((p + q) / 2 - b) - ((r + u) / 2 - c)) / 2 = 0 ∧
      ((((p + q) / 2 - b) + ((r + u) / 2 - c)) / 2 - ((d + e) / 2 - a)) = 0 := by
    obtain ⟨c₀, c₁, c₂, h⟩ := hD₁
    refine quartic_top_coeffs_eq_zero (e₀ := a - c₀) (e₁ := (d - e) / 2 + (b - c) / 2 - c₁)
      (e₂ := ((d + e) / 2 - a) + ((p - q) / 2 - (r - u) / 2) / 2 + ((b + c) / 2 - a) - c₂)
      fun θ hθ ↦ ?_
    linear_combination h θ hθ - hP θ hθ θ hθ
  have key₂ : (((p + q) / 2 - b) - ((r + u) / 2 - c)) / 2
      - (((p - q) / 2 + (r - u) / 2) / 2 - (d - e) / 2) = 0 ∧
      ((((p + q) / 2 - b) + ((r + u) / 2 - c)) / 2 - ((d + e) / 2 - a)) = 0 := by
    obtain ⟨c₀, c₁, c₂, h⟩ := hD₂
    refine quartic_top_coeffs_eq_zero (e₀ := a - c₀) (e₁ := -((d - e) / 2) + (b - c) / 2 - c₁)
      (e₂ := ((d + e) / 2 - a) - ((p - q) / 2 - (r - u) / 2) / 2 + ((b + c) / 2 - a) - c₂)
      fun θ hθ ↦ ?_
    have hθ' : -θ ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
    linear_combination h θ hθ - hP θ hθ (-θ) hθ'
  have h21 : ((p - q) / 2 + (r - u) / 2) / 2 - (d - e) / 2 = 0 := by linarith [key₁.1, key₂.1]
  have h12 : (((p + q) / 2 - b) - ((r + u) / 2 - c)) / 2 = 0 := by linarith [key₁.1, key₂.1]
  linear_combination hP s hs t ht + s ^ 2 * t * h21 + s * t ^ 2 * h12 + s ^ 2 * t ^ 2 * key₁.2

/-! ### Linear-quadratic functions on subsets -/

section LinearQuadratic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `φ` is linear-quadratic relative to `S`: on `S` it is given by `½⟪x, Ax⟫ + ⟪a, x⟫ + α` with
`A` symmetric. -/
def IsLinearQuadraticOn (φ : E → ℝ) (S : Set E) : Prop :=
  ∃ q : QuadraticPiece E, ∀ x ∈ S, φ x = q.eval x

theorem IsLinearQuadraticOn.mono {φ : E → ℝ} {S T : Set E} (h : IsLinearQuadraticOn φ T)
    (hST : S ⊆ T) : IsLinearQuadraticOn φ S := by
  obtain ⟨q, hq⟩ := h
  exact ⟨q, fun x hx ↦ hq x (hST hx)⟩

/-- A linear-quadratic function restricted to a line is a quadratic polynomial. -/
theorem QuadraticPiece.eval_line (q : QuadraticPiece E) (p d : E) (s : ℝ) :
    q.eval (p + s • d) = q.eval p + (⟪d, q.matrix p⟫_ℝ + ⟪q.linear, d⟫_ℝ) * s
      + ((1 / 2) * ⟪d, q.matrix d⟫_ℝ) * s ^ 2 := by
  have hsym : ⟪p, q.matrix d⟫_ℝ = ⟪d, q.matrix p⟫_ℝ := by
    rw [← q.symmetric p d, real_inner_comm]
  simp only [QuadraticPiece.eval, map_add, map_smul, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, RCLike.conj_to_real, hsym]
  ring

theorem segment_param_mem (p d : E) {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) :
    p + s • d ∈ segment ℝ (p - d) (p + d) := by
  refine ⟨(1 - s) / 2, (1 + s) / 2, by linarith [hs.2], by linarith [hs.1], by ring, ?_⟩
  module

/-- Linear-quadratic on the segment `[p - d, p + d]`: a quadratic polynomial in `s ∈ [-1, 1]`. -/
theorem IsLinearQuadraticOn.line {φ : E → ℝ} {p d : E}
    (h : IsLinearQuadraticOn φ (segment ℝ (p - d) (p + d))) :
    ∃ c₀ c₁ c₂ : ℝ, ∀ s ∈ Icc (-1 : ℝ) 1, φ (p + s • d) = c₀ + c₁ * s + c₂ * s ^ 2 := by
  obtain ⟨q, hq⟩ := h
  exact ⟨q.eval p, ⟪d, q.matrix p⟫_ℝ + ⟪q.linear, d⟫_ℝ, (1 / 2) * ⟪d, q.matrix d⟫_ℝ,
    fun s hs ↦ by rw [hq _ (segment_param_mem p d hs), q.eval_line]⟩

/-- Linear-quadratic on the segment `[x, y]`: a quadratic polynomial in `θ ∈ [0, 1]`. -/
theorem IsLinearQuadraticOn.segment_poly {φ : E → ℝ} {x y : E}
    (h : IsLinearQuadraticOn φ (segment ℝ x y)) :
    ∃ c₀ c₁ c₂ : ℝ, ∀ θ ∈ Icc (0 : ℝ) 1, φ (x + θ • (y - x)) = c₀ + c₁ * θ + c₂ * θ ^ 2 := by
  obtain ⟨q, hq⟩ := h
  refine ⟨q.eval x, ⟪y - x, q.matrix x⟫_ℝ + ⟪q.linear, y - x⟫_ℝ,
    (1 / 2) * ⟪y - x, q.matrix (y - x)⟫_ℝ, fun θ hθ ↦ ?_⟩
  rw [hq _ ?_, q.eval_line]
  refine ⟨1 - θ, θ, by linarith [hθ.2], hθ.1, by ring, ?_⟩
  rw [smul_sub, sub_smul, one_smul]
  abel

/-- A finite sum of products of linear forms, plus a linear form and a constant, is
linear-quadratic. -/
theorem QuadraticPiece.exists_eq_sum {ι : Type*} [Fintype ι] (u : ι → E) (M : ι → ι → ℝ)
    (hM : ∀ i j, M i j = M j i) (L : ι → ℝ) (α : ℝ) :
    ∃ q : QuadraticPiece E, ∀ y, q.eval y =
      α + ∑ i, ⟪u i, y⟫_ℝ * L i + (1 / 2) * ∑ i, ∑ j, ⟪u i, y⟫_ℝ * ⟪u j, y⟫_ℝ * M i j := by
  let A : E →L[ℝ] E := ∑ i, ∑ j, M i j • (innerSL ℝ (u j)).smulRight (u i)
  have hA : ∀ x, A x = ∑ i, ∑ j, (M i j * ⟪u j, x⟫_ℝ) • u i := fun x ↦ by
    simp [A, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply, smul_smul]
  have hinner : ∀ x y, ⟪y, A x⟫_ℝ = ∑ i, ∑ j, M i j * ⟪u j, x⟫_ℝ * ⟪u i, y⟫_ℝ := fun x y ↦ by
    rw [hA, inner_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [real_inner_smul_right, real_inner_comm (u i) y]
  refine ⟨⟨A, fun x y ↦ ?_, ∑ i, L i • u i, α⟩, fun y ↦ ?_⟩
  · rw [real_inner_comm, hinner, hinner, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hM]
    ring
  · simp only [QuadraticPiece.eval]
    rw [hinner, sum_inner]
    have h1 : ∑ i, ⟪L i • u i, y⟫_ℝ = ∑ i, ⟪u i, y⟫_ℝ * L i :=
      Finset.sum_congr rfl fun i _ ↦ by rw [real_inner_smul_left]; ring
    have h2 : ∑ i, ∑ j, M i j * ⟪u j, y⟫_ℝ * ⟪u i, y⟫_ℝ
        = ∑ i, ∑ j, ⟪u i, y⟫_ℝ * ⟪u j, y⟫_ℝ * M i j :=
      Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
    rw [h1, h2]
    ring

/-- Linear-quadratic functions are invariant under translation of the variable. -/
theorem QuadraticPiece.exists_eq_translate (q : QuadraticPiece E) (x₀ : E) :
    ∃ q' : QuadraticPiece E, ∀ x, q'.eval x = q.eval (x - x₀) := by
  refine ⟨⟨q.matrix, q.symmetric, q.linear - q.matrix x₀, q.eval x₀ - ⟪q.linear, x₀⟫_ℝ * 2⟩,
    fun x ↦ ?_⟩
  have h2 : ⟪x, q.matrix x₀⟫_ℝ = ⟪x₀, q.matrix x⟫_ℝ := by
    rw [← q.symmetric x x₀, real_inner_comm]
  simp only [QuadraticPiece.eval, map_sub, inner_sub_left, inner_sub_right]
  rw [q.symmetric x₀ x, h2]
  ring

end LinearQuadratic

/-! ### Proof of the sufficiency in Lemma 11.15 -/

section Sufficiency

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A point of a nonempty convex set with a ball of the affine span around it inside the set. -/
theorem exists_relative_ball {C : Set E} (hC : Convex ℝ C) (hne : C.Nonempty) :
    ∃ x₀ ∈ C, ∃ R > 0, ∀ v ∈ (affineSpan ℝ C).direction, ‖v‖ < R → x₀ + v ∈ C := by
  obtain ⟨x₀, hx₀⟩ := hne.intrinsicInterior hC
  obtain ⟨y, hy, rfl⟩ := mem_intrinsicInterior.1 hx₀
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.1 isOpen_interior y hy
  refine ⟨y, (show y ∈ ((↑) ⁻¹' C : Set (affineSpan ℝ C)) from interior_subset hy), R, hR,
    fun v hv hvR ↦ ?_⟩
  have hmem : v +ᵥ (y : E) ∈ affineSpan ℝ C := AffineSubspace.vadd_mem_of_mem_direction hv y.2
  have hb : (⟨v +ᵥ (y : E), hmem⟩ : affineSpan ℝ C) ∈ Metric.ball y R := by
    rw [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm]
    simpa [vadd_eq_add] using hvR
  have h2 := interior_subset (hball hb)
  simpa [vadd_eq_add, add_comm] using h2

omit [FiniteDimensional ℝ E] in
/-- The plane formula: if a square `x₀ + [-1, 1] h₁ + [-1, 1] h₂` lies in `C`, then on it `φ` is the
quadratic polynomial determined by its values at `x₀ + {-1, 0, 1} h₁ + {-1, 0, 1} h₂`. -/
theorem plane_formula {φ : E → ℝ} {C : Set E}
    (h : ∀ x ∈ C, ∀ y ∈ C, IsLinearQuadraticOn φ (segment ℝ x y)) {x₀ h₁ h₂ : E}
    (hsq : ∀ s ∈ Icc (-1 : ℝ) 1, ∀ t ∈ Icc (-1 : ℝ) 1, x₀ + s • h₁ + t • h₂ ∈ C)
    {s t : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) (ht : t ∈ Icc (-1 : ℝ) 1) :
    φ (x₀ + s • h₁ + t • h₂) = φ x₀ + s * ((φ (x₀ + h₁) - φ (x₀ - h₁)) / 2)
      + t * ((φ (x₀ + h₂) - φ (x₀ - h₂)) / 2)
      + s ^ 2 * ((φ (x₀ + h₁) + φ (x₀ - h₁)) / 2 - φ x₀)
      + t ^ 2 * ((φ (x₀ + h₂) + φ (x₀ - h₂)) / 2 - φ x₀)
      + s * t * ((φ (x₀ + h₁ + h₂) - φ (x₀ + h₁ - h₂) - φ (x₀ - h₁ + h₂)
        + φ (x₀ - h₁ - h₂)) / 4) := by
  have hm1 : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hp1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have hseg : ∀ p d : E, p - d ∈ C → p + d ∈ C →
      ∃ c₀ c₁ c₂ : ℝ, ∀ s ∈ Icc (-1 : ℝ) 1, φ (p + s • d) = c₀ + c₁ * s + c₂ * s ^ 2 :=
    fun p d hm hp ↦ (h _ hm _ hp).line
  have key := plane_quadratic (ψ := fun s t ↦ φ (x₀ + s • h₁ + t • h₂))
    (fun t ht ↦ by
      obtain ⟨c₀, c₁, c₂, hc⟩ := hseg (x₀ + t • h₂) h₁
        (by convert hsq (-1) hm1 t ht using 1; module)
        (by convert hsq 1 hp1 t ht using 1; module)
      exact ⟨c₀, c₁, c₂, fun s hs ↦ by
        show φ (x₀ + s • h₁ + t • h₂) = _
        rw [← hc s hs, add_right_comm]⟩)
    (fun σ hσ ↦ by
      have hσ' : σ ∈ Icc (-1 : ℝ) 1 := by
        rcases hσ with rfl | rfl | rfl <;> norm_num
      obtain ⟨c₀, c₁, c₂, hc⟩ := hseg (x₀ + σ • h₁) h₂
        (by convert hsq σ hσ' (-1) hm1 using 1; module)
        (by convert hsq σ hσ' 1 hp1 using 1; module)
      exact ⟨c₀, c₁, c₂, fun t ht ↦ by rw [← hc t ht]⟩)
    (by
      obtain ⟨c₀, c₁, c₂, hc⟩ := hseg x₀ (h₁ + h₂)
        (by convert hsq (-1) hm1 (-1) hm1 using 1; module)
        (by convert hsq 1 hp1 1 hp1 using 1; module)
      exact ⟨c₀, c₁, c₂, fun θ hθ ↦ by
        show φ (x₀ + θ • h₁ + θ • h₂) = _
        rw [← hc θ hθ]
        congr 1
        module⟩)
    (by
      obtain ⟨c₀, c₁, c₂, hc⟩ := hseg x₀ (h₁ - h₂)
        (by convert hsq (-1) hm1 1 hp1 using 1; module)
        (by convert hsq 1 hp1 (-1) hm1 using 1; module)
      exact ⟨c₀, c₁, c₂, fun θ hθ ↦ by
        show φ (x₀ + θ • h₁ + (-θ) • h₂) = _
        rw [← hc θ hθ]
        congr 1
        module⟩)
    hs ht
  simp only at key
  have e1 : x₀ + (1 : ℝ) • h₁ + (0 : ℝ) • h₂ = x₀ + h₁ := by module
  have e2 : x₀ + (-1 : ℝ) • h₁ + (0 : ℝ) • h₂ = x₀ - h₁ := by module
  have e3 : x₀ + (0 : ℝ) • h₁ + (1 : ℝ) • h₂ = x₀ + h₂ := by module
  have e4 : x₀ + (0 : ℝ) • h₁ + (-1 : ℝ) • h₂ = x₀ - h₂ := by module
  have e5 : x₀ + (0 : ℝ) • h₁ + (0 : ℝ) • h₂ = x₀ := by module
  have e6 : x₀ + (1 : ℝ) • h₁ + (1 : ℝ) • h₂ = x₀ + h₁ + h₂ := by module
  have e7 : x₀ + (1 : ℝ) • h₁ + (-1 : ℝ) • h₂ = x₀ + h₁ - h₂ := by module
  have e8 : x₀ + (-1 : ℝ) • h₁ + (1 : ℝ) • h₂ = x₀ - h₁ + h₂ := by module
  have e9 : x₀ + (-1 : ℝ) • h₁ + (-1 : ℝ) • h₂ = x₀ - h₁ - h₂ := by module
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9] at key
  exact key

/-- Two quadratic polynomials agreeing at `0, η, 2η` with `η ≠ 0` have the same coefficients. -/
theorem quadratic_eq_of_three {c₀ c₁ c₂ d₀ d₁ d₂ η : ℝ} (hη : η ≠ 0)
    (h0 : c₀ = d₀) (h1 : c₀ + c₁ * η + c₂ * η ^ 2 = d₀ + d₁ * η + d₂ * η ^ 2)
    (h2 : c₀ + c₁ * (2 * η) + c₂ * (2 * η) ^ 2 = d₀ + d₁ * (2 * η) + d₂ * (2 * η) ^ 2) :
    c₁ = d₁ ∧ c₂ = d₂ := by
  have hη2 : η ^ 2 ≠ 0 := pow_ne_zero 2 hη
  have e2 : (c₂ - d₂) * (2 * η ^ 2) = 0 := by linear_combination h2 - 2 * h1 + h0
  have hc2 : c₂ = d₂ := by
    have := (mul_eq_zero.1 e2).resolve_right (by positivity)
    linarith
  have e1 : (c₁ - d₁) * η = 0 := by rw [hc2] at h1; linear_combination h1 - h0
  exact ⟨by have := (mul_eq_zero.1 e1).resolve_right hη; linarith, hc2⟩

/-- The polarization step of 11.15: functions `ℓ`, `Q` and `β` satisfying, on small vectors of a
subspace `V`, the identities of a linear form, a quadratic form and its polar form, are given
there by a linear-quadratic expression. -/
theorem exists_quadraticPiece_of_polar {V : Submodule ℝ E} {R : ℝ} (hR : 0 < R) {ℓ Q : E → ℝ}
    {β : E → E → ℝ}
    (hL1 : ∀ v ∈ V, ∀ w ∈ V, ‖v‖ + ‖w‖ < R → ∀ s ∈ Icc (-1 : ℝ) 1, ∀ t ∈ Icc (-1 : ℝ) 1,
      ℓ (s • v + t • w) = s * ℓ v + t * ℓ w)
    (hQ1 : ∀ v ∈ V, ∀ w ∈ V, ‖v‖ + ‖w‖ < R → ∀ s ∈ Icc (-1 : ℝ) 1, ∀ t ∈ Icc (-1 : ℝ) 1,
      Q (s • v + t • w) = s ^ 2 * Q v + t ^ 2 * Q w + s * t * β v w)
    (hβsymm : ∀ v w, β v w = β w v)
    (hβself : ∀ v ∈ V, ‖v‖ + ‖v‖ < R → β v v = 2 * Q v)
    (hβhom : ∀ v ∈ V, ∀ w ∈ V, ‖v‖ + ‖w‖ < R → ∀ s ∈ Icc (-1 : ℝ) 1, β (s • v) w = s * β v w)
    (hβadd : ∀ x ∈ V, ∀ y ∈ V, ∀ z ∈ V, ‖x‖ < R / 8 → ‖y‖ < R / 8 → ‖z‖ < R / 8 →
      β (x + y) z = β x z + β y z) (α : ℝ) :
    ∃ ε > 0, ∃ q : QuadraticPiece E, ∀ v ∈ V, ‖v‖ ≤ ε → q.eval v = α + ℓ v + Q v := by
  classical
  have hp1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have hz : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have h00 : ‖(0 : E)‖ + ‖(0 : E)‖ < R := by simpa using hR
  have hℓ0 : ℓ 0 = 0 := by
    simpa using hL1 0 V.zero_mem 0 V.zero_mem h00 0 hz 0 hz
  have hQ0 : Q 0 = 0 := by
    simpa using hQ1 0 V.zero_mem 0 V.zero_mem h00 0 hz 0 hz
  have hβ0 : ∀ w ∈ V, ‖w‖ < R → β 0 w = 0 := fun w hw hwR ↦ by
    simpa using hβhom 0 V.zero_mem w hw (by simpa using hwR) 0 hz
  -- an orthonormal basis of `V`, scaled to small vectors
  set n := Module.finrank ℝ V with hn
  let b := stdOrthonormalBasis ℝ V
  set u : Fin n → E := fun i ↦ ((b i : V) : E) with hu
  have huV : ∀ i, u i ∈ V := fun i ↦ (b i).2
  have hun : ∀ i, ‖u i‖ = 1 := fun i ↦ (Submodule.norm_coe (b i)).trans (b.orthonormal.1 i)
  set ε : ℝ := R / (16 * ((n : ℝ) + 1)) with hε
  have hεpos : 0 < ε := by positivity
  have hε0 : ε ≠ 0 := hεpos.ne'
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  have hεR : ε ≤ R / 16 := by
    rw [hε, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hnε : (n : ℝ) * ε < R / 16 := by
    rw [hε, mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set e : Fin n → E := fun i ↦ ε • u i with he
  have heV : ∀ i, e i ∈ V := fun i ↦ V.smul_mem ε (huV i)
  have hen : ∀ i, ‖e i‖ = ε := fun i ↦ by
    simp only [he, norm_smul, hun i, Real.norm_eq_abs, abs_of_pos hεpos, mul_one]
  have hsumV : ∀ (c : Fin n → ℝ) (S : Finset (Fin n)), ∑ i ∈ S, c i • e i ∈ V :=
    fun c S ↦ V.sum_mem fun i _ ↦ V.smul_mem _ (heV i)
  have hsumn : ∀ c : Fin n → ℝ, (∀ i, |c i| ≤ 1) → ∀ S : Finset (Fin n),
      ‖∑ i ∈ S, c i • e i‖ < R / 16 := by
    intro c hc S
    calc ‖∑ i ∈ S, c i • e i‖ ≤ ∑ i ∈ S, ‖c i • e i‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ S, ε := Finset.sum_le_sum fun i _ ↦ by
          rw [norm_smul, hen i, Real.norm_eq_abs]
          exact mul_le_of_le_one_left hεpos.le (hc i)
      _ = S.card * ε := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ n * ε := mul_le_mul_of_nonneg_right
          (by exact_mod_cast S.card_le_univ.trans_eq (Fintype.card_fin n)) hεpos.le
      _ < R / 16 := hnε
  -- expansion of `ℓ`, `β` and `Q` along the scaled basis
  have hexp : ∀ c : Fin n → ℝ, (∀ i, |c i| ≤ 1) → ∀ S : Finset (Fin n),
      ℓ (∑ i ∈ S, c i • e i) = ∑ i ∈ S, c i * ℓ (e i) ∧
      (∀ j, β (∑ i ∈ S, c i • e i) (e j) = ∑ i ∈ S, c i * β (e i) (e j)) ∧
      Q (∑ i ∈ S, c i • e i) = (1 / 2) * ∑ i ∈ S, ∑ j ∈ S, c i * c j * β (e i) (e j) := by
    intro c hc S
    induction S using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty, mul_zero]
      exact ⟨hℓ0, fun j ↦ hβ0 (e j) (heV j) (by rw [hen]; linarith), hQ0⟩
    | insert k S hk ih =>
      obtain ⟨ihℓ, ihβ, ihQ⟩ := ih
      have hxV := hsumV c S
      have hxn := hsumn c hc S
      set x := ∑ i ∈ S, c i • e i with hx
      have hins : ∑ i ∈ insert k S, c i • e i = c k • e k + x := Finset.sum_insert hk
      have hck : c k ∈ Icc (-1 : ℝ) 1 := abs_le.1 (hc k)
      have hkx : ‖e k‖ + ‖x‖ < R := by rw [hen]; linarith
      have hkk : ‖e k‖ + ‖e k‖ < R := by rw [hen]; linarith
      have hsplit : c k • e k + x = c k • e k + (1 : ℝ) • x := by rw [one_smul]
      rw [hins]
      refine ⟨?_, fun j ↦ ?_, ?_⟩
      · rw [Finset.sum_insert hk, hsplit, hL1 (e k) (heV k) x hxV hkx (c k) hck 1 hp1, ihℓ]
        ring
      · have hkj : ‖e k‖ + ‖e j‖ < R := by rw [hen, hen]; linarith
        have hckn : ‖c k • e k‖ < R / 8 := by
          rw [norm_smul, hen, Real.norm_eq_abs]
          have := mul_le_of_le_one_left hεpos.le (hc k)
          linarith
        rw [Finset.sum_insert hk, hβadd (c k • e k) (V.smul_mem _ (heV k)) x hxV (e j) (heV j)
          hckn (by linarith) (by rw [hen]; linarith),
          hβhom (e k) (heV k) (e j) (heV j) hkj (c k) hck, ihβ j]
      · have hQk : Q (e k) = β (e k) (e k) / 2 := by
          have := hβself (e k) (heV k) hkk
          linarith
        have hs1 : ∑ j ∈ S, c k * c j * β (e k) (e j) = c k * ∑ i ∈ S, c i * β (e i) (e k) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ ↦ by rw [hβsymm (e k) (e j)]; ring
        have hs2 : ∑ i ∈ S, c i * c k * β (e i) (e k) = c k * ∑ i ∈ S, c i * β (e i) (e k) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ ↦ by ring
        rw [hsplit, hQ1 (e k) (heV k) x hxV hkx (c k) hck 1 hp1, hβsymm (e k) x, ihβ k, ihQ, hQk,
          Finset.sum_insert hk]
        simp_rw [Finset.sum_insert hk]
        rw [Finset.sum_add_distrib, hs1, hs2]
        ring
  obtain ⟨q, hq⟩ := QuadraticPiece.exists_eq_sum u (fun i j ↦ β (e i) (e j) / ε ^ 2)
    (fun i j ↦ congrArg (· / ε ^ 2) (hβsymm (e i) (e j))) (fun i ↦ ℓ (e i) / ε) α
  refine ⟨ε, hεpos, q, fun v hv hvε ↦ ?_⟩
  set c : Fin n → ℝ := fun i ↦ ⟪u i, v⟫_ℝ / ε with hc
  have hc1 : ∀ i, |c i| ≤ 1 := fun i ↦ by
    rw [hc, abs_div, abs_of_pos hεpos, div_le_one hεpos]
    calc |⟪u i, v⟫_ℝ| ≤ ‖u i‖ * ‖v‖ := abs_real_inner_le_norm _ _
      _ = ‖v‖ := by rw [hun i, one_mul]
      _ ≤ ε := hvε
  have hvsum : ∑ i, c i • e i = v := by
    have h2 : ((∑ i, ⟪b i, (⟨v, hv⟩ : V)⟫_ℝ • b i : V) : E) = v := by rw [b.sum_repr']
    rw [Submodule.coe_sum] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    calc c i • e i = ⟪u i, v⟫_ℝ • u i := by
          simp only [hc, he]
          rw [smul_smul, div_mul_cancel₀ _ hε0]
      _ = _ := by rw [Submodule.coe_smul, Submodule.coe_inner]
  obtain ⟨hA, -, hC⟩ := hexp c hc1 Finset.univ
  have s1 : ∑ i, c i * ℓ (e i) = ∑ i, ⟪u i, v⟫_ℝ * (ℓ (e i) / ε) :=
    Finset.sum_congr rfl fun i _ ↦ by simp only [hc]; ring
  have s2 : ∑ i, ∑ j, c i * c j * β (e i) (e j)
      = ∑ i, ∑ j, ⟪u i, v⟫_ℝ * ⟪u j, v⟫_ℝ * (β (e i) (e j) / ε ^ 2) :=
    Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by
      simp only [hc]
      field_simp
  have hℓv : ℓ v = ∑ i, ⟪u i, v⟫_ℝ * (ℓ (e i) / ε) := by rw [← s1, ← hA, hvsum]
  have hQv : Q v = (1 / 2) * ∑ i, ∑ j, ⟪u i, v⟫_ℝ * ⟪u j, v⟫_ℝ * (β (e i) (e j) / ε ^ 2) := by
    rw [← s2, ← hC, hvsum]
  rw [hq, hℓv, hQv]

omit [FiniteDimensional ℝ E] in
/-- The ray step of 11.15: a function that is linear-quadratic relative to the segments of `C` and
agrees with a linear-quadratic function near `x₀ ∈ C` in the directions of `C` agrees with it on
`C`. -/
theorem eq_eval_of_segments {φ : E → ℝ} {C : Set E} {x₀ : E} {V : Submodule ℝ E} {ε : ℝ}
    (hε : 0 < ε) (h : ∀ x ∈ C, ∀ y ∈ C, IsLinearQuadraticOn φ (segment ℝ x y)) (hx₀ : x₀ ∈ C)
    (hCV : ∀ x ∈ C, x - x₀ ∈ V) (q : QuadraticPiece E)
    (hlocal : ∀ v ∈ V, ‖v‖ ≤ ε → φ (x₀ + v) = q.eval (x₀ + v)) {x : E} (hx : x ∈ C) :
    φ x = q.eval x := by
  set d := x - x₀ with hd
  have hdV : d ∈ V := hCV x hx
  obtain ⟨c₀, c₁, c₂, hpoly⟩ := (h x₀ hx₀ x hx).segment_poly
  have hp : ∀ θ ∈ Icc (0 : ℝ) 1, φ (x₀ + θ • d) = c₀ + c₁ * θ + c₂ * θ ^ 2 := hpoly
  set A₁ := ⟪d, q.matrix x₀⟫_ℝ + ⟪q.linear, d⟫_ℝ with hA₁
  set A₂ := (1 / 2) * ⟪d, q.matrix d⟫_ℝ with hA₂
  have hgline : ∀ θ : ℝ, q.eval (x₀ + θ • d) = q.eval x₀ + A₁ * θ + A₂ * θ ^ 2 :=
    fun θ ↦ q.eval_line x₀ d θ
  obtain ⟨η, hη0, hη1, hηd⟩ : ∃ η : ℝ, 0 < η ∧ 2 * η ≤ 1 ∧ 2 * η * ‖d‖ ≤ ε := by
    refine ⟨ε / (2 * (‖d‖ + ε)), by positivity, ?_, ?_⟩
    · rw [mul_div_assoc', div_le_one (by positivity)]
      nlinarith [norm_nonneg d]
    · rw [mul_div_assoc', div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [norm_nonneg d]
  have hagree : ∀ θ, 0 ≤ θ → θ ≤ 2 * η → φ (x₀ + θ • d) = q.eval (x₀ + θ • d) := by
    intro θ hθ0 hθ1
    refine hlocal (θ • d) (V.smul_mem θ hdV) ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ0]
    calc θ * ‖d‖ ≤ 2 * η * ‖d‖ := mul_le_mul_of_nonneg_right hθ1 (norm_nonneg d)
      _ ≤ ε := hηd
  have h0 := hp 0 ⟨le_rfl, zero_le_one⟩
  have h1 := hp η ⟨hη0.le, by linarith⟩
  have h2 := hp (2 * η) ⟨by linarith, hη1⟩
  rw [hagree 0 le_rfl (by linarith), hgline] at h0
  rw [hagree η hη0.le (by linarith), hgline] at h1
  rw [hagree (2 * η) (by linarith) le_rfl, hgline] at h2
  have hc0 : c₀ = q.eval x₀ := by
    simp only [mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow] at h0
    linarith
  obtain ⟨hc1, hc2⟩ := quadratic_eq_of_three hη0.ne' hc0 h1.symm h2.symm
  have hx' : x₀ + (1 : ℝ) • d = x := by rw [one_smul, hd]; abel
  have hfin := hp 1 ⟨zero_le_one, le_rfl⟩
  have hg1 := hgline 1
  rw [hx'] at hfin hg1
  rw [hfin, hg1, hc0, hc1, hc2]

/-- **Lemma 11.15**, sufficiency: a function that is linear-quadratic relative to every line
segment in a convex set `C` is linear-quadratic relative to `C`. -/
theorem isLinearQuadraticOn_of_segments {φ : E → ℝ} {C : Set E} (hC : Convex ℝ C)
    (h : ∀ x ∈ C, ∀ y ∈ C, IsLinearQuadraticOn φ (segment ℝ x y)) :
    IsLinearQuadraticOn φ C := by
  classical
  rcases C.eq_empty_or_nonempty with rfl | hne
  · exact ⟨⟨0, fun _ _ ↦ by simp, 0, 0⟩, fun x hx ↦ absurd hx (Set.notMem_empty x)⟩
  obtain ⟨x₀, hx₀C, R, hR, hball⟩ := exists_relative_ball hC hne
  set V := (affineSpan ℝ C).direction with hVdef
  set ℓ : E → ℝ := fun v ↦ (φ (x₀ + v) - φ (x₀ - v)) / 2 with hℓ
  set Q : E → ℝ := fun v ↦ (φ (x₀ + v) + φ (x₀ - v)) / 2 - φ x₀ with hQ
  set β : E → E → ℝ := fun v w ↦
    (φ (x₀ + v + w) - φ (x₀ + v - w) - φ (x₀ - v + w) + φ (x₀ - v - w)) / 4 with hβ
  have hm1 : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hp1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have hz : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hneg : ∀ s ∈ Icc (-1 : ℝ) 1, -s ∈ Icc (-1 : ℝ) 1 := fun s hs ↦
    ⟨by linarith [hs.2], by linarith [hs.1]⟩
  -- squares of small vectors of `V` around `x₀` lie in `C`
  have hsq : ∀ v ∈ V, ∀ w ∈ V, ‖v‖ + ‖w‖ < R →
      ∀ s ∈ Icc (-1 : ℝ) 1, ∀ t ∈ Icc (-1 : ℝ) 1, x₀ + s • v + t • w ∈ C := by
    intro v hv w hw hvw s hs t ht
    rw [add_assoc]
    refine hball _ (V.add_mem (V.smul_mem s hv) (V.smul_mem t hw)) ?_
    calc ‖s • v + t • w‖ ≤ ‖s • v‖ + ‖t • w‖ := norm_add_le _ _
      _ = |s| * ‖v‖ + |t| * ‖w‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ 1 * ‖v‖ + 1 * ‖w‖ := add_le_add
          (mul_le_mul_of_nonneg_right (abs_le.2 ⟨hs.1, hs.2⟩) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (abs_le.2 ⟨ht.1, ht.2⟩) (norm_nonneg _))
      _ < R := by linarith
  have hP : ∀ v ∈ V, ∀ w ∈ V, ‖v‖ + ‖w‖ < R → ∀ s ∈ Icc (-1 : ℝ) 1, ∀ t ∈ Icc (-1 : ℝ) 1,
      φ (x₀ + s • v + t • w) = φ x₀ + s * ℓ v + t * ℓ w + s ^ 2 * Q v + t ^ 2 * Q w
        + s * t * β v w := fun v hv w hw hvw s hs t ht ↦
    plane_formula h (hsq v hv w hw hvw) hs ht
  have hL1 : ∀ v ∈ V, ∀ w ∈ V, ‖v‖ + ‖w‖ < R → ∀ s ∈ Icc (-1 : ℝ) 1, ∀ t ∈ Icc (-1 : ℝ) 1,
      ℓ (s • v + t • w) = s * ℓ v + t * ℓ w := by
    intro v hv w hw hvw s hs t ht
    have h1 := hP v hv w hw hvw s hs t ht
    have h2 := hP v hv w hw hvw (-s) (hneg s hs) (-t) (hneg t ht)
    have e1 : x₀ + (s • v + t • w) = x₀ + s • v + t • w := (add_assoc _ _ _).symm
    have e2 : x₀ - (s • v + t • w) = x₀ + (-s) • v + (-t) • w := by module
    show (φ (x₀ + (s • v + t • w)) - φ (x₀ - (s • v + t • w))) / 2 = _
    rw [e1, e2, h1, h2]
    ring
  have hQ1 : ∀ v ∈ V, ∀ w ∈ V, ‖v‖ + ‖w‖ < R → ∀ s ∈ Icc (-1 : ℝ) 1, ∀ t ∈ Icc (-1 : ℝ) 1,
      Q (s • v + t • w) = s ^ 2 * Q v + t ^ 2 * Q w + s * t * β v w := by
    intro v hv w hw hvw s hs t ht
    have h1 := hP v hv w hw hvw s hs t ht
    have h2 := hP v hv w hw hvw (-s) (hneg s hs) (-t) (hneg t ht)
    have e1 : x₀ + (s • v + t • w) = x₀ + s • v + t • w := (add_assoc _ _ _).symm
    have e2 : x₀ - (s • v + t • w) = x₀ + (-s) • v + (-t) • w := by module
    show (φ (x₀ + (s • v + t • w)) + φ (x₀ - (s • v + t • w))) / 2 - φ x₀ = _
    rw [e1, e2, h1, h2]
    ring
  have hval : ∀ v, φ (x₀ + v) = φ x₀ + ℓ v + Q v := fun v ↦ by
    show φ (x₀ + v) = φ x₀ + (φ (x₀ + v) - φ (x₀ - v)) / 2 + ((φ (x₀ + v) + φ (x₀ - v)) / 2 - φ x₀)
    ring
  have hβsymm : ∀ v w, β v w = β w v := by
    intro v w
    show (φ (x₀ + v + w) - φ (x₀ + v - w) - φ (x₀ - v + w) + φ (x₀ - v - w)) / 4
      = (φ (x₀ + w + v) - φ (x₀ + w - v) - φ (x₀ - w + v) + φ (x₀ - w - v)) / 4
    rw [show x₀ + w + v = x₀ + v + w by abel, show x₀ + w - v = x₀ - v + w by abel,
      show x₀ - w + v = x₀ + v - w by abel, show x₀ - w - v = x₀ - v - w by abel]
    ring
  have hβself : ∀ v ∈ V, ‖v‖ + ‖v‖ < R → β v v = 2 * Q v := by
    intro v hv hvv
    have h1 := hP v hv v hv hvv 1 hp1 1 hp1
    have h2 := hP v hv v hv hvv (-1) hm1 (-1) hm1
    rw [show x₀ + (1 : ℝ) • v + (1 : ℝ) • v = x₀ + v + v by module] at h1
    rw [show x₀ + (-1 : ℝ) • v + (-1 : ℝ) • v = x₀ - v - v by module] at h2
    have hdef : β v v = (φ (x₀ + v + v) - φ (x₀ + v - v) - φ (x₀ - v + v) + φ (x₀ - v - v)) / 4 :=
      rfl
    rw [show x₀ + v - v = x₀ by abel, show x₀ - v + v = x₀ by abel, h1, h2] at hdef
    linarith
  have hβhom : ∀ v ∈ V, ∀ w ∈ V, ‖v‖ + ‖w‖ < R → ∀ s ∈ Icc (-1 : ℝ) 1,
      β (s • v) w = s * β v w := by
    intro v hv w hw hvw s hs
    have hsv : ‖s • v‖ + ‖w‖ < R := by
      rw [norm_smul, Real.norm_eq_abs]
      have := mul_le_of_le_one_left (norm_nonneg v) (abs_le.2 ⟨hs.1, hs.2⟩)
      linarith
    have h1 := hQ1 (s • v) (V.smul_mem s hv) w hw hsv 1 hp1 1 hp1
    have h2 := hQ1 v hv w hw hvw s hs 1 hp1
    have h3 := hQ1 v hv w hw hvw s hs 0 hz
    simp only [one_smul, zero_smul, add_zero, one_pow, one_mul, mul_one, zero_pow two_ne_zero,
      zero_mul] at h1 h2 h3
    rw [h3] at h1
    linarith
  -- polarization (Jordan–von Neumann): additivity of `β` in its first argument
  have hpar : ∀ u ∈ V, ∀ w ∈ V, ‖u‖ + ‖w‖ < R → Q (u + w) + Q (u - w) = 2 * Q u + 2 * Q w := by
    intro u hu w hw huw
    have h1 := hQ1 u hu w hw huw 1 hp1 1 hp1
    have h2 := hQ1 u hu w hw huw 1 hp1 (-1) hm1
    rw [one_smul, one_smul] at h1
    rw [one_smul, neg_one_smul, ← sub_eq_add_neg] at h2
    linarith
  have hdif : ∀ u ∈ V, ∀ z ∈ V, ‖u‖ + ‖z‖ < R → Q (u + z) - Q (u - z) = 2 * β u z := by
    intro u hu z hz' huz
    have h1 := hQ1 u hu z hz' huz 1 hp1 1 hp1
    have h2 := hQ1 u hu z hz' huz 1 hp1 (-1) hm1
    rw [one_smul, one_smul] at h1
    rw [one_smul, neg_one_smul, ← sub_eq_add_neg] at h2
    linarith
  have hβadd : ∀ x ∈ V, ∀ y ∈ V, ∀ z ∈ V, ‖x‖ < R / 8 → ‖y‖ < R / 8 → ‖z‖ < R / 8 →
      β (x + y) z = β x z + β y z := by
    intro x hx y hy z hz' hxn hyn hzn
    set a : E := (1 / 2 : ℝ) • (x + y) with ha
    set w : E := (1 / 2 : ℝ) • (x - y) with hw
    have haV : a ∈ V := V.smul_mem _ (V.add_mem hx hy)
    have hwV : w ∈ V := V.smul_mem _ (V.sub_mem hx hy)
    have han : ‖a‖ < R / 8 := by
      rw [ha, norm_smul]
      have := norm_add_le x y
      norm_num
      linarith
    have hwn : ‖w‖ < R / 8 := by
      rw [hw, norm_smul]
      have := norm_sub_le x y
      norm_num
      linarith
    have e1 : (a + z) + w = x + z := by rw [ha, hw]; module
    have e2 : (a + z) - w = y + z := by rw [ha, hw]; module
    have e3 : (a - z) + w = x - z := by rw [ha, hw]; module
    have e4 : (a - z) - w = y - z := by rw [ha, hw]; module
    have hazn : ‖a + z‖ < R / 4 := by have := norm_add_le a z; linarith
    have hazn' : ‖a - z‖ < R / 4 := by have := norm_sub_le a z; linarith
    have p1 := hpar (a + z) (V.add_mem haV hz') w hwV (by linarith)
    have p2 := hpar (a - z) (V.sub_mem haV hz') w hwV (by linarith)
    rw [e1, e2] at p1
    rw [e3, e4] at p2
    have d1 := hdif x hx z hz' (by linarith)
    have d2 := hdif y hy z hz' (by linarith)
    have d3 := hdif a haV z hz' (by linarith)
    have hxy : ‖x + y‖ + ‖z‖ < R := by have := norm_add_le x y; linarith
    have hh := hβhom (x + y) (V.add_mem hx hy) z hz' hxy (1 / 2) ⟨by norm_num, by norm_num⟩
    rw [← ha] at hh
    linarith
  obtain ⟨ε, hε, q₀, hq₀⟩ :=
    exists_quadraticPiece_of_polar hR hL1 hQ1 hβsymm hβself hβhom hβadd (φ x₀)
  obtain ⟨q, hq⟩ := q₀.exists_eq_translate x₀
  refine ⟨q, fun x hx ↦ eq_eval_of_segments (V := V) hε h hx₀C (fun y hy ↦ ?_) q
    (fun v hv hvε ↦ ?_) hx⟩
  · simpa [vsub_eq_sub] using AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ C hy)
      (subset_affineSpan ℝ C hx₀C)
  · rw [hq, add_sub_cancel_left, hq₀ v hv hvε]
    exact hval v

/-- **Lemma 11.15** (linear-quadratic test on line segments): a real function is linear-quadratic
relative to a convex set iff it is linear-quadratic relative to every line segment in the set. -/
theorem isLinearQuadraticOn_iff_segments {φ : E → ℝ} {C : Set E} (hC : Convex ℝ C) :
    IsLinearQuadraticOn φ C ↔ ∀ x ∈ C, ∀ y ∈ C, IsLinearQuadraticOn φ (segment ℝ x y) :=
  ⟨fun h _ hx _ hy ↦ h.mono (hC.segment_subset hx hy), isLinearQuadraticOn_of_segments hC⟩

end Sufficiency

/-! ### Extended-real-valued functions and quadratic polynomials along segments -/

section Segments

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An extended-real-valued function is linear-quadratic relative to `S` when it agrees on `S` with
a (finite) linear-quadratic formula. -/
def IsLinearQuadraticOnEReal (f : E → EReal) (S : Set E) : Prop :=
  ∃ q : QuadraticPiece E, ∀ x ∈ S, f x = (q.eval x : EReal)

/-- A function that is a quadratic polynomial along the parametrized segment `x + θ (y - x)`,
`θ ∈ [0, 1]`, is linear-quadratic relative to the segment. -/
theorem isLinearQuadraticOn_segment_of_poly {φ : E → ℝ} {x y : E} {c₀ c₁ c₂ : ℝ}
    (h : ∀ θ ∈ Icc (0 : ℝ) 1, φ (x + θ • (y - x)) = c₀ + c₁ * θ + c₂ * θ ^ 2) :
    IsLinearQuadraticOn φ (segment ℝ x y) := by
  rcases eq_or_ne x y with rfl | hxy
  · refine ⟨⟨0, fun _ _ ↦ by simp, 0, φ x⟩, fun z hz ↦ ?_⟩
    rw [segment_same, mem_singleton_iff] at hz
    subst hz
    simp [QuadraticPiece.eval]
  set d := y - x with hd
  have hd0 : d ≠ 0 := sub_ne_zero.2 hxy.symm
  set r : ℝ := ⟪d, d⟫_ℝ with hr
  have hr0 : r ≠ 0 := by rw [hr, real_inner_self_eq_norm_sq]; positivity
  obtain ⟨q₀, hq₀⟩ := QuadraticPiece.exists_eq_sum (ι := Unit) (fun _ ↦ d)
    (fun _ _ ↦ 2 * c₂ / r ^ 2) (fun _ _ ↦ rfl) (fun _ ↦ c₁ / r) c₀
  obtain ⟨q, hq⟩ := q₀.exists_eq_translate x
  refine ⟨q, fun z hz ↦ ?_⟩
  rw [segment_eq_image'] at hz
  obtain ⟨θ, hθ, rfl⟩ := hz
  rw [h θ hθ, hq, hq₀, add_sub_cancel_left]
  simp only [Finset.univ_unique, Finset.sum_singleton, real_inner_smul_right]
  field_simp
  ring

/-- **Lemma 11.15** for extended-real-valued functions: finiteness on `C` comes from the
degenerate segments. -/
theorem isLinearQuadraticOnEReal_iff_segments [FiniteDimensional ℝ E] {f : E → EReal}
    {C : Set E} (hC : Convex ℝ C) :
    IsLinearQuadraticOnEReal f C ↔
      ∀ x ∈ C, ∀ y ∈ C, IsLinearQuadraticOnEReal f (segment ℝ x y) := by
  constructor
  · rintro ⟨q, hq⟩ x hx y hy
    exact ⟨q, fun z hz ↦ hq z (hC.segment_subset hx hy hz)⟩
  · intro h
    have hfin : ∀ x ∈ C, f x = ((f x).toReal : EReal) := fun x hx ↦ by
      obtain ⟨q, hq⟩ := h x hx x hx
      rw [hq x (by simp), EReal.toReal_coe]
    obtain ⟨q, hq⟩ := isLinearQuadraticOn_of_segments (φ := fun x ↦ (f x).toReal) hC
      fun x hx y hy ↦ by
        obtain ⟨q, hq⟩ := h x hx y hy
        exact ⟨q, fun z hz ↦ by simp only [hq z hz, EReal.toReal_coe]⟩
    exact ⟨q, fun x hx ↦ by rw [hfin x hx, ← hq x hx]⟩

end Segments

end RW
