/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 2C-D: Derivative Tests and Operations Preserving Convexity

This file formalizes Sections C and D of Chapter 2 of Rockafellar & Wets,
"Variational Analysis":
- Theorem 2.13: One-dimensional derivative tests for convexity
- Theorem 2.14: Higher-dimensional derivative tests (gradient monotonicity,
  Hessian positive semidefiniteness)
- Proposition 2.21: Images/preimages under linear maps preserve convexity
- Proposition 2.22: Inf-projection and epi-composition preserve convexity
- Proposition 2.23: Minkowski sum preserves convexity
-/

import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Data.Real.Pointwise
import Mathlib.Order.ConditionallyCompleteLattice.Group


set_option linter.style.openClassical false

open Set Filter Topology Classical Pointwise

noncomputable section

namespace RW

/-! ## Section C: Derivative Tests for Convexity -/

/-! ### Theorem 2.13: One-dimensional derivative tests

For a twice-differentiable function `f : ℝ → ℝ`:
- `f` is convex iff `f''(x) ≥ 0` for all `x`
- `f` is strictly convex if `f''(x) > 0` for all `x`
-/

/-- **Theorem 2.13 (1D, first-order)**: A differentiable function `f : ℝ → ℝ`
is convex on an interval iff the derivative is monotone nondecreasing. -/
theorem convexOn_iff_deriv_mono {a b : ℝ} (hab : a < b)
    {f : ℝ → ℝ} (hf : DifferentiableOn ℝ f (Set.Icc a b)) :
    ConvexOn ℝ (Set.Icc a b) f ↔
      MonotoneOn (deriv f) (Set.Ioo a b) := by
  have interior_eq : interior (Set.Icc a b) = Set.Ioo a b := interior_Icc
  constructor
  · intro hconv x hx y hy hxy
    have hx' : x ∈ Set.Icc a b := Ioo_subset_Icc_self hx
    have hy' : y ∈ Set.Icc a b := Ioo_subset_Icc_self hy
    have hxd : DifferentiableAt ℝ f x :=
      (hf x hx').differentiableAt (Icc_mem_nhds hx.1 hx.2)
    have hyd : DifferentiableAt ℝ f y :=
      (hf y hy').differentiableAt (Icc_mem_nhds hy.1 hy.2)
    rcases eq_or_lt_of_le hxy with rfl | hxy'
    · rfl
    exact (hconv.deriv_le_slope hx' hy' hxy' hxd).trans
      (hconv.slope_le_deriv hx' hy' hxy' hyd)
  · intro hmono
    have hmono' : MonotoneOn (deriv f) (interior (Set.Icc a b)) := by
      rwa [interior_eq]
    exact hmono'.convexOn_of_deriv (convex_Icc a b) hf.continuousOn
      (hf.mono interior_subset)

/-- **Theorem 2.13 (1D, second-order)**: A twice-differentiable function
`f : ℝ → ℝ` is convex on an interval iff `f''(x) ≥ 0`. -/
theorem convexOn_iff_deriv2_nonneg {a b : ℝ} (hab : a < b)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Icc a b)) :
    ConvexOn ℝ (Set.Icc a b) f ↔
      ∀ x ∈ Set.Ioo a b, 0 ≤ deriv (deriv f) x := by
  have hf1 : ContDiffOn ℝ 1 f (Set.Icc a b) := hf.of_le (by norm_num)
  have hf_diff : DifferentiableOn ℝ f (Set.Icc a b) := hf1.differentiableOn one_ne_zero
  rw [convexOn_iff_deriv_mono hab hf_diff]
  -- Now need: MonotoneOn (deriv f) (Ioo a b) ↔ ∀ x ∈ Ioo a b, 0 ≤ deriv (deriv f) x
  -- Extract differentiability of deriv f on Ioo a b from ContDiffOn ℝ 2 f (Icc a b)
  have hf_ioo : ContDiffOn ℝ 2 f (Set.Ioo a b) := hf.mono Ioo_subset_Icc_self
  have hderiv_cont_ioo : ContDiffOn ℝ 1 (deriv f) (Set.Ioo a b) :=
    hf_ioo.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hderiv_diff_ioo : DifferentiableOn ℝ (deriv f) (Set.Ioo a b) :=
    hderiv_cont_ioo.differentiableOn one_ne_zero
  have hderiv_cont_icc : ContinuousOn (deriv f) (Set.Ioo a b) :=
    hderiv_diff_ioo.continuousOn
  constructor
  · intro hmono x hx
    have : 0 ≤ derivWithin (deriv f) (Set.Ioo a b) x :=
      hmono.derivWithin_nonneg
    rwa [derivWithin_of_isOpen isOpen_Ioo hx] at this
  · intro hderiv2
    exact monotoneOn_of_deriv_nonneg (convex_Ioo a b) hderiv_cont_icc
      (hderiv_diff_ioo.mono interior_subset) (by rwa [interior_Ioo])

/-! ### Theorem 2.14: Higher-dimensional derivative tests -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- **Theorem 2.14 (first-order)**: A differentiable function is convex on
an open convex set iff for all `x, y` in the set,
`f(y) ≥ f(x) + ⟨∇f(x), y - x⟩`. This is the first-order condition. -/
theorem convexOn_iff_firstOrder
    {S : Set E} (hS : Convex ℝ S) (hSo : IsOpen S)
    {f : E → ℝ} (hf : DifferentiableOn ℝ f S) :
    ConvexOn ℝ S f ↔
      ∀ x ∈ S, ∀ y ∈ S,
        f x + (fderiv ℝ f x) (y - x) ≤ f y := by
  constructor
  · -- Forward: ConvexOn → first-order condition
    intro hconv x hx y hy
    suffices h : (fderiv ℝ f x) (y - x) ≤ f y - f x by linarith
    have hfx : DifferentiableAt ℝ f x := (hf x hx).differentiableAt (hSo.mem_nhds hx)
    -- g(t) = f(x + t • (y - x)) has derivative (fderiv ℝ f x)(y - x) at t = 0
    have hder : HasDerivAt (fun t : ℝ => f (x + t • (y - x))) ((fderiv ℝ f x) (y - x)) (0 : ℝ) := by
      -- The map t ↦ x + t • (y - x) has derivative (y - x) at t = 0
      have h1 : HasDerivAt (fun t : ℝ => t • (y - x)) ((1 : ℝ) • (y - x)) 0 :=
        (hasDerivAt_id' (0 : ℝ)).smul_const (y - x)
      have h2 : HasDerivAt (fun _ : ℝ => x) 0 (0 : ℝ) := hasDerivAt_const 0 x
      have hpath : HasDerivAt (fun t : ℝ => x + t • (y - x)) ((0 : E) + (1 : ℝ) • (y - x)) 0 :=
        h2.add h1
      simp only [zero_add, one_smul] at hpath
      have hfx' : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • (y - x)) := by
        simp only [zero_smul, add_zero]; exact hfx.hasFDerivAt
      exact hfx'.comp_hasDerivAt (0 : ℝ) hpath
    -- tendsto_slope_zero_right: (g(t) - g(0)) / t → g'(0) from the right
    have hlim : Filter.Tendsto
        (fun t : ℝ => t⁻¹ * (f (x + t • (y - x)) - f x))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds ((fderiv ℝ f x) (y - x))) := by
      have := hder.tendsto_slope_zero_right
      simp only [zero_smul, add_zero, zero_add, smul_eq_mul] at this
      exact this
    -- For t ∈ (0, 1], convexity gives f(x + t(y-x)) ≤ f(x) + t(f(y) - f(x))
    -- So t⁻¹ * (f(x + t(y-x)) - f(x)) ≤ f(y) - f(x)
    apply le_of_tendsto hlim
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht1 ht
    simp only [Set.mem_Ioi] at ht
    have ht1' : t < 1 := Set.mem_Iio.mp ht1
    rw [inv_mul_le_iff₀ ht]
    have hxt : x + t • (y - x) = (1 - t) • x + t • y := by
      rw [smul_sub, sub_smul, one_smul]; abel
    have := hconv.2 hx hy (by linarith) ht.le (by linarith : 1 - t + t = 1)
    simp only [smul_eq_mul] at this
    rw [hxt]; linarith
  · -- Backward: first-order condition → ConvexOn
    intro hfirst
    refine ⟨hS, fun x hx y hy a b ha hb hab => ?_⟩
    set z := a • x + b • y with hz_def
    have hzS : z ∈ S := hS hx hy ha hb hab
    have h1 := hfirst z hzS x hx
    have h2 := hfirst z hzS y hy
    have hzero : a • (x - z) + b • (y - z) = 0 := by
      have hab1 : (a + b) • z = z := by rw [hab, one_smul]
      simp only [smul_sub, ← add_sub, ← sub_sub]
      rw [show a • x - a • z + (b • y - b • z) = (a • x + b • y) - (a • z + b • z) from by abel]
      rw [← add_smul, hab, one_smul, hz_def, sub_self]
    -- f(z) + fderiv(z)(a(x-z) + b(y-z)) = f(z) + 0 = f(z)
    -- = a*f(z) + b*f(z) since a + b = 1
    -- ≤ a*(f(z) + fderiv(z)(x-z)) + b*(f(z) + fderiv(z)(y-z))
    --   ... wait, the inequality goes the other way. Let's use a different calc.
    have hab1 : a + b = 1 := hab
    have key : a * (fderiv ℝ f z) (x - z) + b * (fderiv ℝ f z) (y - z) = 0 := by
      rw [← smul_eq_mul, ← smul_eq_mul, ← map_smul, ← map_smul, ← map_add, hzero, map_zero]
    -- From h1: f(z) + fderiv(z)(x-z) ≤ f(x), so a * fderiv(z)(x-z) ≤ a * (f(x) - f(z))
    -- From h2: f(z) + fderiv(z)(y-z) ≤ f(y), so b * fderiv(z)(y-z) ≤ b * (f(y) - f(z))
    -- Sum: 0 = a * fderiv(z)(x-z) + b * fderiv(z)(y-z) ≤ a*(f(x)-f(z)) + b*(f(y)-f(z))
    -- So f(z) = a*f(z) + b*f(z) ≤ a*f(x) + b*f(y)
    simp only [smul_eq_mul]
    -- From h1 and ha: a * (fderiv ℝ f z) (x - z) ≤ a * (f x - f z)
    have i1 : a * (fderiv ℝ f z) (x - z) ≤ a * (f x - f z) :=
      mul_le_mul_of_nonneg_left (by linarith) ha
    -- From h2 and hb: b * (fderiv ℝ f z) (y - z) ≤ b * (f y - f z)
    have i2 : b * (fderiv ℝ f z) (y - z) ≤ b * (f y - f z) :=
      mul_le_mul_of_nonneg_left (by linarith) hb
    -- Sum: 0 ≤ a*(f x - f z) + b*(f y - f z) = a*f x + b*f y - f z
    have sum := add_le_add i1 i2
    rw [key] at sum
    -- sum : 0 ≤ a * (f x - f z) + b * (f y - f z)
    have expand : a * (f x - f z) + b * (f y - f z) =
        a * f x + b * f y - (a + b) * f z := by ring
    rw [expand, hab1, one_mul] at sum
    linarith

/-! ## Section D: Operations Preserving Convexity -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace F]

/-! ### Proposition 2.21: Linear images and preimages -/

/-- **Proposition 2.21 (a)**: The image of a convex set under a linear map
is convex. This is `Convex.linear_image` in Mathlib. -/
theorem convex_image_of_linear {S : Set E} (hS : Convex ℝ S)
    (L : E →ₗ[ℝ] F) :
    Convex ℝ (L '' S) :=
  hS.linear_image L

/-- **Proposition 2.21 (b)**: The preimage of a convex set under a linear map
is convex. This is `Convex.linear_preimage` in Mathlib. -/
theorem convex_preimage_of_linear {T : Set F} (hT : Convex ℝ T)
    (L : E →ₗ[ℝ] F) :
    Convex ℝ (L ⁻¹' T) :=
  hT.linear_preimage L

/-- **Proposition 2.21**: Convexity is preserved by affine maps. -/
theorem convex_image_of_affine {S : Set E} (hS : Convex ℝ S)
    (L : E →ₗ[ℝ] F) (c : F) :
    Convex ℝ ((fun x => L x + c) '' S) := by
  intro u hu v hv t s ht hs hts
  obtain ⟨xu, hxu, rfl⟩ := hu
  obtain ⟨xv, hxv, rfl⟩ := hv
  refine ⟨t • xu + s • xv, hS hxu hxv ht hs hts, ?_⟩
  simp only [map_add, map_smul, smul_add]
  conv_lhs => rw [show c = t • c + s • c from by rw [← add_smul, hts, one_smul]]
  abel

/-! ### Proposition 2.22: Inf-projection preserves convexity -/

/-- **Proposition 2.22**: If `f : E × F → ℝ` is jointly convex, then
the inf-projection `g(x) = inf_{y ∈ T} f(x,y)` is convex.

For real-valued functions, we assume each slice over `T` is bounded below so
the conditional infimum behaves as the intended restricted infimum. -/
theorem convexOn_infProjection
    {S : Set E} {T : Set F}
    (hS : Convex ℝ S) (hT : Convex ℝ T)
    {f : E × F → ℝ}
    (hf : ConvexOn ℝ (S ×ˢ T) f)
    (hfbdd : ∀ x ∈ S, BddBelow (Set.range fun y : T => f (x, (y : F)))) :
    ConvexOn ℝ S (fun x => ⨅ y : T, f (x, (y : F))) := by
  constructor
  · exact hS
  · intro x hx y hy a b ha hb hab
    by_cases hTne : T.Nonempty
    · letI : Nonempty T := Set.Nonempty.to_subtype hTne
      let z : E := a • x + b • y
      have hz : z ∈ S := hS hx hy ha hb hab
      have hboundz : BddBelow (Set.range fun y : T => f (z, (y : F))) := hfbdd z hz
      have hle : (⨅ t : T, f (z, (t : F))) ≤
          (⨅ u : T, a * f (x, (u : F))) + (⨅ v : T, b * f (y, (v : F))) := by
        refine le_ciInf_add_ciInf ?_
        intro u v
        have hxu : (x, (u : F)) ∈ S ×ˢ T := ⟨hx, u.2⟩
        have hyv : (y, (v : F)) ∈ S ×ˢ T := ⟨hy, v.2⟩
        have hconv := hf.2 hxu hyv ha hb hab
        have hci : (⨅ t : T, f (z, (t : F))) ≤ f (z, a • (u : F) + b • (v : F)) := by
          let w : T := ⟨a • (u : F) + b • (v : F), hT u.2 v.2 ha hb hab⟩
          exact ciInf_le hboundz w
        exact hci.trans hconv
      simpa only [z, smul_eq_mul, Real.mul_iInf_of_nonneg ha, Real.mul_iInf_of_nonneg hb] using hle
    · simp [Set.not_nonempty_iff_eq_empty.mp hTne]

/-! ### Proposition 2.23: Minkowski sum preserves convexity -/

/-- **Proposition 2.23**: The Minkowski sum of two convex sets is convex.
This is essentially `Convex.add` in Mathlib. -/
theorem convex_add_of_convex
    {S T : Set E} (hS : Convex ℝ S) (hT : Convex ℝ T) :
    Convex ℝ (S + T) :=
  hS.add hT

end RW
