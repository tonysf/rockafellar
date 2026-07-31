/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3: Proximal Cancellation Completion

This file completes the missing direction of Corollary 3.37 within the
project's real-valued coercive API.  A coercive convex function has a proximal
minimizer at every positive parameter.  Choosing such minimizers and applying
a midpoint argument gives a globally `2`-Lipschitz selection (the sharper
standard result is firm nonexpansiveness).

Equality of proximal mappings therefore supplies a common Lipschitz selection.
This gives a quadratic increment bound on the difference of the corresponding
Moreau envelopes, so that difference has zero Fréchet derivative and is
constant.  The cancellation endpoint in `Cancellation.lean` then determines
the original functions up to an additive constant.
-/

import RockafellarWets.Chapter3.Cancellation
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Mul

open Bornology EReal Set Topology

noncomputable section

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A proximal mapping admits a selection with some finite global Lipschitz
constant.  The standard proximal map is in fact nonexpansive; a finite bound is
all that the cancellation argument below needs. -/
def HasLipschitzProximalSelection (f : E → ℝ) (lam : ℝ) : Prop :=
  ∃ K : NNReal, ∃ P : E → E, LipschitzWith K P ∧
    ∀ x : E, P x ∈ proximalMapping f lam x

/-- The sharper standard regularity predicate, retained as a convenient API
for callers that already know the proximal map is nonexpansive. -/
def HasNonexpansiveProximalSelection (f : E → ℝ) (lam : ℝ) : Prop :=
  ∃ P : E → E, LipschitzWith 1 P ∧
    ∀ x : E, P x ∈ proximalMapping f lam x

omit [InnerProductSpace ℝ E] in
/-- A nonexpansive proximal selection is, in particular, a Lipschitz proximal
selection. -/
theorem HasNonexpansiveProximalSelection.hasLipschitz
    {f : E → ℝ} {lam : ℝ}
    (h : HasNonexpansiveProximalSelection f lam) :
    HasLipschitzProximalSelection f lam := by
  rcases h with ⟨P, hP, hmem⟩
  exact ⟨1, P, hP, hmem⟩

omit [InnerProductSpace ℝ E] in
/-- A global lower bound on `f` bounds below every positive-parameter Moreau
slice. -/
private theorem moreauSlice_bddBelow_of_bddBelow_range
    {f : E → ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hf : BddBelow (Set.range f)) (x : E) :
    BddBelow (Set.range fun w : E ↦
      f w + (1 / (2 * lam)) * ‖w - x‖ ^ 2) := by
  obtain ⟨b, hb⟩ := hf
  refine ⟨b, ?_⟩
  rintro _ ⟨w, rfl⟩
  have hfw : b ≤ f w := hb ⟨w, rfl⟩
  have hpen : 0 ≤ (1 / (2 * lam)) * ‖w - x‖ ^ 2 := by positivity
  linarith

/-- The squared-distance identity at the midpoint of two vectors. -/
private theorem norm_midpoint_sub_sq (u v x : E) :
    ‖(2 : ℝ)⁻¹ • u + (2 : ℝ)⁻¹ • v - x‖ ^ 2 =
      (2 : ℝ)⁻¹ * ‖u - x‖ ^ 2 + (2 : ℝ)⁻¹ * ‖v - x‖ ^ 2 -
        (4 : ℝ)⁻¹ * ‖u - v‖ ^ 2 := by
  have hvec :
      (2 : ℝ)⁻¹ • u + (2 : ℝ)⁻¹ • v - x =
        (2 : ℝ)⁻¹ • ((u - x) + (v - x)) := by
    module
  have hsub : (u - x) - (v - x) = u - v := by abel
  have hpara := parallelogram_law_with_norm ℝ (u - x) (v - x)
  rw [hsub] at hpara
  rw [hvec, norm_smul, Real.norm_eq_abs]
  norm_num
  nlinarith

/-- A finite-dimensional real-valued convex coercive function has a proximal
minimizer at every positive parameter and every base point. -/
private theorem exists_mem_proximalMapping_real_coercive
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {f : E → ℝ}
    (hconv : Convex ℝ (epigraph (fun w ↦ (f w : EReal))))
    (hf : IsCoercive (fun w : E ↦ (f w : EReal)))
    {lam : ℝ} (hlam : 0 < lam) (x : E) :
    ∃ w : E, w ∈ proximalMapping f lam x := by
  let a : ℝ := 1 / (2 * lam)
  let q : E → ℝ := fun w ↦ f w + a * ‖w - x‖ ^ 2
  have hconvf : ConvexOn ℝ Set.univ f := by
    rw [← convex_epigraph_iff_convexOn f Set.univ convex_univ]
    simpa [epigraph, ge_iff_le] using hconv
  have hdistSq : ConvexOn ℝ Set.univ (fun w : E ↦ ‖w - x‖ ^ 2) := by
    simpa only [dist_eq_norm] using
      (convexOn_univ_dist x).pow (fun _ _ ↦ dist_nonneg) 2
  have hpen : ConvexOn ℝ Set.univ (fun w : E ↦ a * ‖w - x‖ ^ 2) := by
    simpa only [smul_eq_mul] using hdistSq.smul (by dsimp [a]; positivity)
  have hconvq : ConvexOn ℝ Set.univ q := by
    simpa only [q, Pi.add_apply] using hconvf.add hpen
  have hconvqE : Convex ℝ (epigraph (fun w ↦ (q w : EReal))) := by
    have hreal := hconvq
    rw [← convex_epigraph_iff_convexOn q Set.univ convex_univ] at hreal
    simpa [epigraph, ge_iff_le] using hreal
  have hcontq : Continuous q := by
    rw [← continuousOn_univ]
    exact continuous_of_convexOn_open isOpen_univ convex_univ hconvq
  have hlscq : LowerSemicontinuous (fun w ↦ (q w : EReal)) :=
    (continuous_coe_real_ereal.comp hcontq).lowerSemicontinuous
  have hproperq : IsProper (fun w ↦ (q w : EReal)) := by
    exact ⟨⟨0, EReal.coe_lt_top _⟩, fun w ↦ EReal.bot_lt_coe _⟩
  have hcoerq : IsCoercive (fun w ↦ (q w : EReal)) := by
    intro γ hγ
    obtain ⟨β, hβ⟩ := hf γ hγ
    refine ⟨β, ?_⟩
    intro w
    apply EReal.coe_le_coe_iff.mpr
    have hfw : γ * ‖w‖ + β ≤ f w := EReal.coe_le_coe_iff.mp (hβ w)
    have hpen_nonneg : 0 ≤ a * ‖w - x‖ ^ 2 := by
      dsimp [a]
      positivity
    dsimp only [q]
    linarith
  have hifc : IsInfCompact (fun w ↦ (q w : EReal)) :=
    isInfCompact_of_isCoercive hconvqE hlscq hproperq hcoerq
  obtain ⟨w, hw⟩ :=
    exists_isMinOn_of_isInfCompact_of_lsc_of_isProper hifc hlscq hproperq
  have hwmin : ∀ z : E, q w ≤ q z := by
    intro z
    exact EReal.coe_le_coe_iff.mp (hw (by simp))
  have hbdd := moreauSlice_bddBelow_of_bddBelow_range
    hlam (bddBelow_of_isCoercive_real hf) x
  refine ⟨w, ?_⟩
  simp only [proximalMapping, Set.mem_setOf_eq]
  change q w = moreauEnvelope f lam x
  apply le_antisymm
  · unfold moreauEnvelope
    exact le_ciInf hwmin
  · unfold moreauEnvelope
    exact ciInf_le hbdd w

/-- Any two proximal minimizers of a convex function satisfy a global factor
two Lipschitz estimate.  The midpoint proof is sufficient here; the sharper
firmly-nonexpansive estimate is not needed for cancellation. -/
private theorem norm_sub_proximal_le_two_mul
    {f : E → ℝ}
    (hconv : Convex ℝ (epigraph (fun w ↦ (f w : EReal))))
    (hf : IsCoercive (fun w : E ↦ (f w : EReal)))
    {lam : ℝ} (hlam : 0 < lam) {x y u v : E}
    (hu : u ∈ proximalMapping f lam x)
    (hv : v ∈ proximalMapping f lam y) :
    ‖u - v‖ ≤ 2 * ‖x - y‖ := by
  let a : ℝ := 1 / (2 * lam)
  let m : E := (2 : ℝ)⁻¹ • u + (2 : ℝ)⁻¹ • v
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hbdd : BddBelow (Set.range f) := bddBelow_of_isCoercive_real hf
  have hconvf : ConvexOn ℝ Set.univ f := by
    rw [← convex_epigraph_iff_convexOn f Set.univ convex_univ]
    simpa [epigraph, ge_iff_le] using hconv
  have hfmid : f m ≤ (2 : ℝ)⁻¹ * f u + (2 : ℝ)⁻¹ * f v := by
    have h := hconvf.2 (Set.mem_univ u) (Set.mem_univ v)
      (show 0 ≤ (2 : ℝ)⁻¹ by norm_num)
      (show 0 ≤ (2 : ℝ)⁻¹ by norm_num)
      (show (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = 1 by norm_num)
    simpa only [m, smul_eq_mul] using h
  have humin : f u + a * ‖u - x‖ ^ 2 = moreauEnvelope f lam x := by
    simpa only [proximalMapping, Set.mem_setOf_eq, a] using hu
  have hvmin : f v + a * ‖v - y‖ ^ 2 = moreauEnvelope f lam y := by
    simpa only [proximalMapping, Set.mem_setOf_eq, a] using hv
  have hu_le (z : E) :
      f u + a * ‖u - x‖ ^ 2 ≤ f z + a * ‖z - x‖ ^ 2 := by
    rw [humin]
    unfold moreauEnvelope
    exact ciInf_le (moreauSlice_bddBelow_of_bddBelow_range hlam hbdd x) z
  have hv_le (z : E) :
      f v + a * ‖v - y‖ ^ 2 ≤ f z + a * ‖z - y‖ ^ 2 := by
    rw [hvmin]
    unfold moreauEnvelope
    exact ciInf_le (moreauSlice_bddBelow_of_bddBelow_range hlam hbdd y) z
  have hmid_x :
      f m + a * ‖m - x‖ ^ 2 ≤
        (2 : ℝ)⁻¹ * (f u + a * ‖u - x‖ ^ 2) +
          (2 : ℝ)⁻¹ * (f v + a * ‖v - x‖ ^ 2) -
            a * (4 : ℝ)⁻¹ * ‖u - v‖ ^ 2 := by
    rw [norm_midpoint_sub_sq u v x]
    nlinarith
  have hmid_y :
      f m + a * ‖m - y‖ ^ 2 ≤
        (2 : ℝ)⁻¹ * (f u + a * ‖u - y‖ ^ 2) +
          (2 : ℝ)⁻¹ * (f v + a * ‖v - y‖ ^ 2) -
            a * (4 : ℝ)⁻¹ * ‖u - v‖ ^ 2 := by
    rw [norm_midpoint_sub_sq u v y]
    nlinarith
  have hstrong_x :
      f u + a * ‖u - x‖ ^ 2 + a * (2 : ℝ)⁻¹ * ‖u - v‖ ^ 2 ≤
        f v + a * ‖v - x‖ ^ 2 := by
    nlinarith [hu_le m, hmid_x]
  have hstrong_y :
      f v + a * ‖v - y‖ ^ 2 + a * (2 : ℝ)⁻¹ * ‖u - v‖ ^ 2 ≤
        f u + a * ‖u - y‖ ^ 2 := by
    nlinarith [hv_le m, hmid_y]
  have hsum :
      ‖u - v‖ ^ 2 ≤
        ‖v - x‖ ^ 2 - ‖u - x‖ ^ 2 +
          ‖u - y‖ ^ 2 - ‖v - y‖ ^ 2 := by
    nlinarith
  have hcross :
      ‖v - x‖ ^ 2 - ‖u - x‖ ^ 2 +
          ‖u - y‖ ^ 2 - ‖v - y‖ ^ 2 =
        2 * inner ℝ (u - v) (x - y) := by
    simp only [norm_sub_sq_real, inner_sub_left, inner_sub_right]
    ring
  rw [hcross] at hsum
  have hinner : inner ℝ (u - v) (x - y) ≤ ‖u - v‖ * ‖x - y‖ :=
    (le_abs_self _).trans (abs_real_inner_le_norm _ _)
  have hsq : ‖u - v‖ ^ 2 ≤ 2 * (‖u - v‖ * ‖x - y‖) :=
    hsum.trans (by gcongr)
  by_cases huv : u = v
  · simp [huv]
  · have hnorm : 0 < ‖u - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr huv)
    nlinarith [norm_nonneg (x - y)]

/-- Every finite-dimensional real-valued convex coercive function admits a
globally `2`-Lipschitz proximal selection at a positive parameter. -/
theorem hasLipschitzProximalSelection_real_coercive
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {f : E → ℝ}
    (hconv : Convex ℝ (epigraph (fun w ↦ (f w : EReal))))
    (hf : IsCoercive (fun w : E ↦ (f w : EReal)))
    {lam : ℝ} (hlam : 0 < lam) :
    HasLipschitzProximalSelection f lam := by
  classical
  choose P hP using fun x : E ↦
    exists_mem_proximalMapping_real_coercive hconv hf hlam x
  refine ⟨2, P, ?_, hP⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm, NNReal.coe_ofNat] using
    norm_sub_proximal_le_two_mul hconv hf hlam (hP x) (hP y)

omit [InnerProductSpace ℝ E] in
/-- Comparing a Moreau minimizer at `x` with the same candidate at `y`
bounds the corresponding envelope increment. -/
private theorem moreauEnvelope_increment_le_of_mem_proximal
    {f : E → ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hf : BddBelow (Set.range f)) {P : E → E} {x y : E}
    (hx : P x ∈ proximalMapping f lam x) :
    moreauEnvelope f lam y - moreauEnvelope f lam x ≤
      (1 / (2 * lam)) * (‖P x - y‖ ^ 2 - ‖P x - x‖ ^ 2) := by
  have hcand : moreauEnvelope f lam y ≤
      f (P x) + (1 / (2 * lam)) * ‖P x - y‖ ^ 2 := by
    unfold moreauEnvelope
    exact ciInf_le (moreauSlice_bddBelow_of_bddBelow_range hlam hf y) (P x)
  have hmin : f (P x) + (1 / (2 * lam)) * ‖P x - x‖ ^ 2 =
      moreauEnvelope f lam x := by
    simpa only [proximalMapping, Set.mem_setOf_eq] using hx
  rw [← hmin]
  linarith

/-- The difference of two Moreau envelopes with a common Lipschitz
proximal selection has a quadratic modulus of continuity. -/
private theorem moreauEnvelope_sub_quadratic_bound_of_common_selection
    {f₁ f₂ : E → ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hf₁ : BddBelow (Set.range f₁)) (hf₂ : BddBelow (Set.range f₂))
    {K : NNReal} {P : E → E} (hP : LipschitzWith K P)
    (hP₁ : ∀ x : E, P x ∈ proximalMapping f₁ lam x)
    (hP₂ : ∀ x : E, P x ∈ proximalMapping f₂ lam x)
    (x y : E) :
    |(moreauEnvelope f₁ lam y - moreauEnvelope f₂ lam y) -
        (moreauEnvelope f₁ lam x - moreauEnvelope f₂ lam x)| ≤
      ((K : ℝ) / lam) * ‖y - x‖ ^ 2 := by
  let a : ℝ := 1 / (2 * lam)
  let A : ℝ := a * (‖P x - y‖ ^ 2 - ‖P x - x‖ ^ 2)
  let B : ℝ := a * (‖P y - y‖ ^ 2 - ‖P y - x‖ ^ 2)
  have h₁upper :
      moreauEnvelope f₁ lam y - moreauEnvelope f₁ lam x ≤ A := by
    simpa only [a, A] using
      moreauEnvelope_increment_le_of_mem_proximal hlam hf₁ (hP₁ x : _)
  have h₁lower : B ≤
      moreauEnvelope f₁ lam y - moreauEnvelope f₁ lam x := by
    have h := moreauEnvelope_increment_le_of_mem_proximal
      hlam hf₁ (hP₁ y : P y ∈ proximalMapping f₁ lam y)
      (y := x)
    dsimp only [a, B]
    linarith
  have h₂upper :
      moreauEnvelope f₂ lam y - moreauEnvelope f₂ lam x ≤ A := by
    simpa only [a, A] using
      moreauEnvelope_increment_le_of_mem_proximal hlam hf₂ (hP₂ x : _)
  have h₂lower : B ≤
      moreauEnvelope f₂ lam y - moreauEnvelope f₂ lam x := by
    have h := moreauEnvelope_increment_le_of_mem_proximal
      hlam hf₂ (hP₂ y : P y ∈ proximalMapping f₂ lam y)
      (y := x)
    dsimp only [a, B]
    linarith
  have habs :
      |(moreauEnvelope f₁ lam y - moreauEnvelope f₂ lam y) -
          (moreauEnvelope f₁ lam x - moreauEnvelope f₂ lam x)| ≤ A - B := by
    rw [abs_le]
    constructor <;> linarith
  have hgap : A - B = (1 / lam) * inner ℝ (y - x) (P y - P x) := by
    dsimp only [a, A, B]
    simp only [norm_sub_sq_real, inner_sub_left, inner_sub_right]
    rw [real_inner_comm (P x) y, real_inner_comm (P x) x,
      real_inner_comm (P y) y, real_inner_comm (P y) x]
    field_simp [ne_of_gt hlam]
    ring
  calc
    |(moreauEnvelope f₁ lam y - moreauEnvelope f₂ lam y) -
        (moreauEnvelope f₁ lam x - moreauEnvelope f₂ lam x)|
        ≤ A - B := habs
    _ = (1 / lam) * inner ℝ (y - x) (P y - P x) := hgap
    _ ≤ (1 / lam) * |inner ℝ (y - x) (P y - P x)| := by
      gcongr
      exact le_abs_self _
    _ ≤ (1 / lam) * (‖y - x‖ * ‖P y - P x‖) := by
      gcongr
      exact abs_real_inner_le_norm _ _
    _ ≤ (1 / lam) * (‖y - x‖ * ((K : ℝ) * ‖y - x‖)) := by
      gcongr
      simpa only [dist_eq_norm] using hP.dist_le_mul y x
    _ = ((K : ℝ) / lam) * ‖y - x‖ ^ 2 := by ring

/-- A real-valued function with a global quadratic increment bound has zero
Fréchet derivative. -/
private theorem hasFDerivAt_zero_of_quadratic_bound
    {D : E → ℝ} {K : ℝ} (x : E)
    (hD : ∀ y : E, |D y - D x| ≤ K * ‖y - x‖ ^ 2) :
    HasFDerivAt D (0 : E →L[ℝ] ℝ) x := by
  rw [hasFDerivAt_iff_tendsto]
  apply squeeze_zero (g := fun y : E ↦ K * ‖y - x‖)
  · intro y
    positivity
  · intro y
    simp only [ContinuousLinearMap.zero_apply, sub_zero, Real.norm_eq_abs]
    by_cases hy : y = x
    · simp [hy]
    · have hnorm : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hy)
      calc
        ‖y - x‖⁻¹ * |D y - D x| ≤
            ‖y - x‖⁻¹ * (K * ‖y - x‖ ^ 2) := by
          gcongr
          exact hD y
        _ = K * ‖y - x‖ := by
          field_simp
  · simpa only [mul_zero] using
      tendsto_const_nhds.mul (tendsto_norm_sub_self x)

/-- A common Lipschitz proximal selection forces two Moreau envelopes to
differ by a constant.  This is the analytic bridge needed in Corollary 3.37. -/
theorem moreauEnvelope_eq_add_const_of_common_lipschitz_proximalSelection
    {f₁ f₂ : E → ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hf₁ : BddBelow (Set.range f₁)) (hf₂ : BddBelow (Set.range f₂))
    {K : NNReal} {P : E → E} (hP : LipschitzWith K P)
    (hP₁ : ∀ x : E, P x ∈ proximalMapping f₁ lam x)
    (hP₂ : ∀ x : E, P x ∈ proximalMapping f₂ lam x) :
    ∃ c : ℝ, moreauEnvelope f₁ lam =
      fun x ↦ moreauEnvelope f₂ lam x + c := by
  let D : E → ℝ := fun x ↦
    moreauEnvelope f₁ lam x - moreauEnvelope f₂ lam x
  have hquad (x y : E) : |D y - D x| ≤
      ((K : ℝ) / lam) * ‖y - x‖ ^ 2 := by
    exact moreauEnvelope_sub_quadratic_bound_of_common_selection
      hlam hf₁ hf₂ hP hP₁ hP₂ x y
  have hderiv (x : E) : HasFDerivAt D 0 x :=
    hasFDerivAt_zero_of_quadratic_bound x (hquad x)
  have hdiff : Differentiable ℝ D := fun x ↦ (hderiv x).differentiableAt
  have hfderiv : ∀ x : E, fderiv ℝ D x = 0 := fun x ↦ (hderiv x).fderiv
  let x₀ : E := 0
  refine ⟨D x₀, funext fun x ↦ ?_⟩
  have hconst : D x = D x₀ := is_const_of_fderiv_eq_zero hdiff hfderiv x x₀
  dsimp only [D] at hconst ⊢
  linarith

/-- Explicit-selection form of the real-valued coercive Corollary 3.37.  A
common finite-Lipschitz proximal selection turns equality of one
positive-parameter proximal mapping into equality up to an additive constant. -/
theorem corollary337_eq_add_const_of_proximalMapping_eq_of_lipschitzSelection_real_coercive
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {f₁ f₂ : E → ℝ}
    (hconv₁ : Convex ℝ (epigraph (fun x ↦ (f₁ x : EReal))))
    (hlsc₁ : LowerSemicontinuous (fun x ↦ (f₁ x : EReal)))
    (hconv₂ : Convex ℝ (epigraph (fun x ↦ (f₂ x : EReal))))
    (hlsc₂ : LowerSemicontinuous (fun x ↦ (f₂ x : EReal)))
    (hf₁ : IsCoercive (fun x : E ↦ (f₁ x : EReal)))
    (hf₂ : IsCoercive (fun x : E ↦ (f₂ x : EReal)))
    {lam : ℝ} (hlam : 0 < lam)
    (hprox : proximalMapping f₁ lam = proximalMapping f₂ lam)
    (hselection : HasLipschitzProximalSelection f₁ lam) :
    ∃ c : ℝ, f₁ = fun x ↦ f₂ x + c := by
  rcases hselection with ⟨K, P, hP, hP₁⟩
  have hP₂ : ∀ x : E, P x ∈ proximalMapping f₂ lam x := by
    intro x
    rw [← congrFun hprox x]
    exact hP₁ x
  obtain ⟨c, henv⟩ :=
    moreauEnvelope_eq_add_const_of_common_lipschitz_proximalSelection
      hlam (bddBelow_of_isCoercive_real hf₁)
      (bddBelow_of_isCoercive_real hf₂) hP hP₁ hP₂
  refine ⟨c, ?_⟩
  exact corollary337_eq_add_const_of_moreauEnvelope_eq_add_const_real_coercive
    hconv₁ hlsc₁ hconv₂ hlsc₂ hf₁ hf₂ hlam henv

/-- **Corollary 3.37 (real-valued coercive adaptation).** Equality of the
proximal mappings for one positive parameter determines two finite-dimensional
real-valued closed convex coercive functions up to an additive constant.  No
selection or differentiability hypothesis is required. -/
theorem corollary337_eq_add_const_of_proximalMapping_eq_real_coercive
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {f₁ f₂ : E → ℝ}
    (hconv₁ : Convex ℝ (epigraph (fun x ↦ (f₁ x : EReal))))
    (hlsc₁ : LowerSemicontinuous (fun x ↦ (f₁ x : EReal)))
    (hconv₂ : Convex ℝ (epigraph (fun x ↦ (f₂ x : EReal))))
    (hlsc₂ : LowerSemicontinuous (fun x ↦ (f₂ x : EReal)))
    (hf₁ : IsCoercive (fun x : E ↦ (f₁ x : EReal)))
    (hf₂ : IsCoercive (fun x : E ↦ (f₂ x : EReal)))
    {lam : ℝ} (hlam : 0 < lam)
    (hprox : proximalMapping f₁ lam = proximalMapping f₂ lam) :
    ∃ c : ℝ, f₁ = fun x ↦ f₂ x + c := by
  exact
    corollary337_eq_add_const_of_proximalMapping_eq_of_lipschitzSelection_real_coercive
      hconv₁ hlsc₁ hconv₂ hlsc₂ hf₁ hf₂ hlam hprox
      (hasLipschitzProximalSelection_real_coercive hconv₁ hf₁ hlam)

end RW
