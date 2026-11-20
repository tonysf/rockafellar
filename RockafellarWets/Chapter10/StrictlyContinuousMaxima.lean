/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 10: subgradients of a pointwise max of strictly continuous functions

**Corollary 10.51** for `f = max {f₁, …, f_m}` with each `fᵢ` strictly continuous on `ℝⁿ`; `f` is
then strictly continuous (`strictlyContinuousAt_finiteMax`), and
`∂f(x̄) ⊂ {∑_{i ∈ I(x̄)} λᵢvᵢ | vᵢ ∈ ∂fᵢ(x̄), λᵢ ≥ 0, ∑_{i ∈ I(x̄)} λᵢ = 1}` with `I(x̄)` the active
indices (`subdifferential_finiteMax_subset_of_strictlyContinuous`); the weights are indexed by all
`i` and vanish off `I(x̄)`.  As in the book this is 10.49 with `F = (f₁, …, f_m)` and
`g = vecmax` (8.26), together with the finite sum rule 10.9 and the positive homogeneity of
coderivatives (`coderivative_smul`), which gives `∂(λh)(x̄) = λ∂h(x̄)` for `λ > 0` and strictly
continuous `h` (`subdifferential_const_mul`, from `subdifferential_inner_smul`).

If every active `fᵢ` is strictly differentiable at `x̄`, then `f` is regular at `x̄` and the
inclusion is an equation (`subdifferential_finiteMax_eq_of_strictlyDifferentiable`), from the
regular case of 10.49: `vecmax` is convex and finite, hence regular, and each `yF` with `y`
supported on `I(x̄)` is strictly differentiable at `x̄`.
-/

import RockafellarWets.Chapter10.LipschitzConstraintNormals
import RockafellarWets.Chapter10.FiniteSumSubgradients
import RockafellarWets.Chapter8.NormAndMaxSubgradients
import RockafellarWets.Chapter9.CoderivativeNorms
import RockafellarWets.Chapter9.StrictContinuityCriteria
import RockafellarWets.Chapter9.ConstancyCriterion

open Filter Function Metric Set Topology
open scoped NNReal ENNReal InnerProductSpace Pointwise

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Coderivatives are positively homogeneous: `r D*S(x̄|ū)(y) ⊂ D*S(x̄|ū)(ry)` for `r > 0`. -/
theorem smul_coderivative_subset {S : E → Set F} {x : E} {u : F} (hu : u ∈ S x) (y : F) {r : ℝ}
    (hr : 0 < r) : r • coderivative S x u y ⊆ coderivative S x u (r • y) := by
  rintro _ ⟨v, hv, rfl⟩
  have h := (isCone_normalCone (C := euclideanSvGraph S) (x := WithLp.toLp 2 (x, u))
    (show WithLp.toLp 2 (x, u) ∈ euclideanSvGraph S from hu)).2
    (show WithLp.toLp 2 (v, -y) ∈ normalCone (euclideanSvGraph S) (WithLp.toLp 2 (x, u)) from hv)
    hr
  show WithLp.toLp 2 (r • v, -(r • y)) ∈ normalCone (euclideanSvGraph S) (WithLp.toLp 2 (x, u))
  rw [← smul_neg, ← Prod.smul_mk, WithLp.toLp_smul]
  exact h

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Coderivatives are positively homogeneous: `D*S(x̄|ū)(ry) = r D*S(x̄|ū)(y)` for `r > 0`. -/
theorem coderivative_smul {S : E → Set F} {x : E} {u : F} (hu : u ∈ S x) (y : F) {r : ℝ}
    (hr : 0 < r) : coderivative S x u (r • y) = r • coderivative S x u y := by
  refine Subset.antisymm (fun v hv ↦ ?_) (smul_coderivative_subset hu y hr)
  have h := smul_coderivative_subset hu (r • y) (inv_pos.2 hr) (smul_mem_smul_set hv)
  rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul] at h
  exact ⟨r⁻¹ • v, h, show r • r⁻¹ • v = v by rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]⟩

omit [FiniteDimensional ℝ F] in
/-- `∂((ry)F)(x̄) = r ∂(yF)(x̄)` for `r > 0` and `F` strictly continuous at `x̄`. -/
theorem subdifferential_inner_smul {G : E → F} {x : E} (hG : StrictlyContinuousAt G x) (y : F)
    {r : ℝ} (hr : 0 < r) :
    subdifferential (fun a ↦ ((⟪r • y, G a⟫_ℝ : ℝ) : EReal)) x =
      r • subdifferential (fun a ↦ ((⟪y, G a⟫_ℝ : ℝ) : EReal)) x := by
  rw [← coderivative_svSingleton_eq_subdifferential hG,
    ← coderivative_svSingleton_eq_subdifferential hG]
  exact coderivative_smul (S := svSingleton G) (mem_singleton (G x)) y hr

theorem real_inner_one_left' (t : ℝ) : ⟪(1 : ℝ), t⟫_ℝ = t := by simp

theorem real_inner_eq_mul' (r t : ℝ) : ⟪r, t⟫_ℝ = r * t := by
  simp [mul_comm]

/-- `∂(rh)(x̄) = r ∂h(x̄)` for `r > 0` and `h` real-valued and strictly continuous at `x̄`. -/
theorem subdifferential_const_mul {h : E → ℝ} {x : E} (hh : StrictlyContinuousAt h x) {r : ℝ}
    (hr : 0 < r) :
    subdifferential (fun a ↦ ((r * h a : ℝ) : EReal)) x =
      r • subdifferential (fun a ↦ ((h a : ℝ) : EReal)) x := by
  have h1 := subdifferential_inner_smul hh (1 : ℝ) hr
  simp only [smul_eq_mul, mul_one, real_inner_eq_mul', one_mul] at h1
  exact h1

theorem ereal_coe_finset_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    ((∑ i ∈ s, a i : ℝ) : EReal) = ∑ i ∈ s, (a i : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, EReal.coe_add, ih]

section Max

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The vector `(f₁(x), …, f_m(x))` of values. -/
noncomputable def valueVector (fs : ι → E → ℝ) (z : E) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i ↦ fs i z)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι]
  [Nonempty ι] in
theorem valueVector_apply (fs : ι → E → ℝ) (z : E) (i : ι) : valueVector fs z i = fs i z := rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem finiteMax_eq_vecMax (fs : ι → E → ℝ) (z : E) :
    finiteMax fs z = vecMax (valueVector fs z) := rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nonempty ι] in
theorem inner_valueVector (fs : ι → E → ℝ) (y : EuclideanSpace ℝ ι) (z : E) :
    ⟪y, valueVector fs z⟫_ℝ = ∑ i, y i * fs i z := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [valueVector_apply, real_inner_eq_mul']

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nonempty ι] in
/-- Strict continuity of the components gives strict continuity of the value vector. -/
theorem strictlyContinuousAt_valueVector {fs : ι → E → ℝ} {x : E}
    (hs : ∀ i, StrictlyContinuousAt (fs i) x) : StrictlyContinuousAt (valueVector fs) x := by
  choose k U hU hL using fun i ↦ strictlyContinuousAt_iff.1 (hs i)
  refine (strictlyContinuousAt_iff_inner _ x).2 fun v ↦ strictlyContinuousAt_iff.2
    ⟨∑ i, ‖v i‖₊ * k i, ⋂ i, U i, iInter_mem.2 hU,
      LipschitzOnWith.of_dist_le_mul fun a ha b hb ↦ ?_⟩
  rw [mem_iInter] at ha hb
  simp only [inner_valueVector, Real.dist_eq]
  rw [← Finset.sum_sub_distrib, NNReal.coe_sum, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [← mul_sub, abs_mul, NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have h := (hL i).dist_le_mul a (ha i) b (hb i)
  rwa [Real.dist_eq] at h

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Corollary 10.51**: a pointwise max of finitely many functions strictly continuous at `x̄` is
strictly continuous at `x̄`. -/
theorem strictlyContinuousAt_finiteMax {fs : ι → E → ℝ} {x : E}
    (hs : ∀ i, StrictlyContinuousAt (fs i) x) : StrictlyContinuousAt (finiteMax fs) x := by
  choose k U hU hL using fun i ↦ strictlyContinuousAt_iff.1 (hs i)
  refine strictlyContinuousAt_iff.2 ⟨∑ i, k i, ⋂ i, U i, iInter_mem.2 hU,
    LipschitzOnWith.of_dist_le_mul fun a ha b hb ↦ ?_⟩
  rw [mem_iInter] at ha hb
  have hk : ∀ i, |fs i a - fs i b| ≤ ((∑ j, k j : ℝ≥0) : ℝ) * dist a b := fun i ↦ by
    have h := (hL i).dist_le_mul a (ha i) b (hb i)
    rw [Real.dist_eq] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ dist_nonneg)
    rw [NNReal.coe_sum]
    exact Finset.single_le_sum (f := fun j ↦ ((k j : ℝ≥0) : ℝ)) (fun j _ ↦ (k j).2)
      (Finset.mem_univ i)
  rw [Real.dist_eq, abs_le]
  constructor
  · have h : finiteMax fs b ≤ finiteMax fs a + ((∑ j, k j : ℝ≥0) : ℝ) * dist a b :=
      finiteMax_le_iff.2 fun i ↦ by
        have := (abs_le.1 (hk i)).1
        linarith [le_finiteMax fs a i]
    linarith
  · have h : finiteMax fs a ≤ finiteMax fs b + ((∑ j, k j : ℝ≥0) : ℝ) * dist a b :=
      finiteMax_le_iff.2 fun i ↦ by
        have := (abs_le.1 (hk i)).2
        linarith [le_finiteMax fs b i]
    linarith

/-- **Corollary 10.51**: for `f = max {f₁, …, f_m}` with each `fᵢ` strictly continuous,
`∂f(x̄) ⊂ {∑ λᵢvᵢ | vᵢ ∈ ∂fᵢ(x̄), λᵢ ≥ 0, ∑ λᵢ = 1, λᵢ = 0 for i ∉ I(x̄)}`. -/
theorem subdifferential_finiteMax_subset_of_strictlyContinuous {fs : ι → E → ℝ}
    (hs : ∀ i z, StrictlyContinuousAt (fs i) z) (x : E) :
    subdifferential (fun z ↦ ((finiteMax fs z : ℝ) : EReal)) x ⊆
      {v | ∃ l : ι → ℝ, ∃ w : ι → E, (∀ i, 0 ≤ l i) ∧
        (∀ i, fs i x ≠ finiteMax fs x → l i = 0) ∧ ∑ i, l i = 1 ∧
        (∀ i, w i ∈ subdifferential (fun z ↦ ((fs i z : ℝ) : EReal)) x) ∧ v = ∑ i, l i • w i} := by
  intro v hv
  have hG := strictlyContinuousAt_valueVector (fun i ↦ hs i x)
  have hcont : ∀ i, Continuous (fs i) := fun i ↦
    continuous_iff_continuousAt.2 fun z ↦ (hs i z).continuousAt
  have hvm : Continuous (fun w : EuclideanSpace ℝ ι ↦ vecMax w) :=
    Continuous.finset_sup'_apply Finset.univ_nonempty fun i _ ↦ by fun_prop
  have hl : LowerSemicontinuous (fun w : EuclideanSpace ℝ ι ↦ ((vecMax w : ℝ) : EReal)) :=
    (continuous_coe_real_ereal.comp hvm).lowerSemicontinuous
  obtain ⟨y, hy, hvy⟩ := (subdifferential_comp_subset_of_strictlyContinuous
    (g := fun w : EuclideanSpace ℝ ι ↦ ((vecMax w : ℝ) : EReal)) (G := valueVector fs) (x := x)
    (c := vecMax (valueVector fs x)) hl hG rfl (by
      intro y hy _
      rw [horizonSubdifferential_vecMax] at hy
      exact hy)).1 hv
  obtain ⟨hpos, hzero, hsum⟩ := (mem_subdifferential_vecMax_iff y (valueVector fs x)).1 hy
  -- the sum rule for `⟪y, F⟫ = ∑ yᵢ fᵢ`
  set f : ι → E → EReal := fun i z ↦ ((y i * fs i z : ℝ) : EReal) with hf
  have hfun : (fun a ↦ ((⟪y, valueVector fs a⟫_ℝ : ℝ) : EReal)) = fun z ↦ ∑ i, f i z := by
    funext z
    rw [inner_valueVector, ereal_coe_finset_sum]
  have hER : ∀ i, ERealStrictlyContinuousAt (f i) x := fun i ↦ by
    have h := (hs i x).eRealStrictlyContinuousAt_inner (y i)
    simp only [real_inner_eq_mul'] at h
    exact h
  have hlsc : ∀ i, LowerSemicontinuous (f i) := fun i ↦
    (continuous_coe_real_ereal.comp (continuous_const.mul (hcont i))).lowerSemicontinuous
  have hprop : ∀ i, IsProper (f i) := fun i ↦
    ⟨⟨x, EReal.coe_lt_top _⟩, fun z ↦ EReal.bot_lt_coe _⟩
  have hhor : ∀ i, horizonSubdifferential (f i) x = {0} := fun i ↦
    (eRealStrictlyContinuousAt_iff_horizonSubdifferential_eq_zero (f := f i) (x := x)
      (c := y i * fs i x) rfl
      (isLocallyLscAt_of_lowerSemicontinuousOn isOpen_univ ((hlsc i).lowerSemicontinuousOn _)
        (mem_univ _) (EReal.coe_ne_bot _) (EReal.coe_ne_top _))).1 (hER i)
  have hrule := subdifferential_finiteSum_subset (f := f) (x := x) (c := fun i ↦ y i * fs i x)
    hprop hlsc (fun i ↦ rfl) (by
      intro u hu _ i
      have h := hu i
      rw [hhor i] at h
      exact h)
  rw [hfun] at hvy
  obtain ⟨z, hz, rfl⟩ := hrule hvy
  have hdec : ∀ i, ∃ w, w ∈ subdifferential (fun a ↦ ((fs i a : ℝ) : EReal)) x ∧
      z i = y i • w := by
    intro i
    have hne : (subdifferential (fun a ↦ ((fs i a : ℝ) : EReal)) x).Nonempty := by
      have h := (hs i x).eRealStrictlyContinuousAt_inner (1 : ℝ)
      simp only [real_inner_one_left'] at h
      exact h.subdifferential_nonempty_compact.1
    by_cases hact : fs i x = finiteMax fs x
    · rcases (hpos i hact).lt_or_eq with hlt | heq
      · have h : z i ∈ subdifferential (fun a ↦ ((y i * fs i a : ℝ) : EReal)) x := hz i
        rw [subdifferential_const_mul (hs i x) hlt] at h
        obtain ⟨w, hw, hzw⟩ := h
        exact ⟨w, hw, hzw.symm⟩
      · obtain ⟨w₀, hw₀⟩ := hne
        refine ⟨w₀, hw₀, ?_⟩
        have h : z i ∈ subdifferential (f i) x := hz i
        have hc : f i = fun _ ↦ ((0 : ℝ) : EReal) := by
          funext a
          simp [hf, ← heq]
        rw [hc, (hasStrictGradientAt_zero_of_eventually_eq (c := 0)
          (Eventually.of_forall fun _ ↦ rfl)).subdifferential_eq] at h
        rw [h, ← heq, zero_smul]
    · obtain ⟨w₀, hw₀⟩ := hne
      refine ⟨w₀, hw₀, ?_⟩
      have h0 := hzero i hact
      have h : z i ∈ subdifferential (f i) x := hz i
      have hc : f i = fun _ ↦ ((0 : ℝ) : EReal) := by
        funext a
        simp [hf, h0]
      rw [hc, (hasStrictGradientAt_zero_of_eventually_eq (c := 0)
        (Eventually.of_forall fun _ ↦ rfl)).subdifferential_eq] at h
      rw [h, h0, zero_smul]
  choose w hw hzw using hdec
  refine ⟨fun i ↦ y i, w, fun i ↦ ?_, fun i hi ↦ hzero i hi, hsum, hw, ?_⟩
  · by_cases hact : fs i x = finiteMax fs x
    · exact hpos i hact
    · exact (hzero i hact).ge
  · exact Finset.sum_congr rfl fun i _ ↦ hzw i

omit [FiniteDimensional ℝ E] [Nonempty ι] in
/-- If `fᵢ` has strict gradient `gᵢ` at `x̄` whenever `yᵢ ≠ 0`, then `yF = ∑ yᵢfᵢ` has strict
gradient `∑ yᵢgᵢ` at `x̄`. -/
theorem hasStrictGradientAt_inner_valueVector {fs : ι → E → ℝ} {x : E} {y : EuclideanSpace ℝ ι}
    {g : ι → E} (hg : ∀ i, y i ≠ 0 → HasStrictFDerivAt (fs i) (innerSL ℝ (g i)) x) :
    HasStrictGradientAt (fun a ↦ ((⟪y, valueVector fs a⟫_ℝ : ℝ) : EReal)) (∑ i, y i • g i) x := by
  refine ⟨Eventually.of_forall fun _ ↦ by rw [EReal.toReal_coe], ?_⟩
  simp only [EReal.toReal_coe, inner_valueVector]
  have hsum : HasStrictFDerivAt (fun a ↦ ∑ i, y i * fs i a)
      (∑ i, y i • innerSL ℝ (g i)) x := by
    refine HasStrictFDerivAt.fun_sum (u := Finset.univ) (A := fun i a ↦ y i * fs i a)
      (A' := fun i ↦ y i • innerSL ℝ (g i)) fun i _ ↦ ?_
    by_cases hyi : y i = 0
    · simp only [hyi, zero_smul, zero_mul]
      exact hasStrictFDerivAt_const (0 : ℝ) x
    · exact (hg i hyi).const_mul (y i)
  convert hsum using 1
  ext u
  simp

omit [FiniteDimensional ℝ E] [Nonempty ι] in
theorem lowerSemicontinuous_vecMax [Nonempty ι] :
    LowerSemicontinuous (fun w : EuclideanSpace ℝ ι ↦ ((vecMax w : ℝ) : EReal)) :=
  (continuous_coe_real_ereal.comp (Continuous.finset_sup'_apply Finset.univ_nonempty
    fun i _ ↦ by fun_prop)).lowerSemicontinuous

/-- **Corollary 10.51**, equality case: if every active `fᵢ` is strictly differentiable at `x̄`,
then `f = max {f₁, …, f_m}` is regular at `x̄` and
`∂f(x̄) = {∑ λᵢvᵢ | vᵢ ∈ ∂fᵢ(x̄), λᵢ ≥ 0, ∑ λᵢ = 1, λᵢ = 0 for i ∉ I(x̄)}`. -/
theorem subdifferential_finiteMax_eq_of_strictlyDifferentiable {fs : ι → E → ℝ}
    (hs : ∀ i z, StrictlyContinuousAt (fs i) z) {x : E}
    (hd : ∀ i, fs i x = finiteMax fs x →
      StrictlyDifferentiableAt (fun z ↦ ((fs i z : ℝ) : EReal)) x) :
    IsSubdifferentiallyRegularAt (fun z ↦ ((finiteMax fs z : ℝ) : EReal)) x ∧
      subdifferential (fun z ↦ ((finiteMax fs z : ℝ) : EReal)) x =
        {v | ∃ l : ι → ℝ, ∃ w : ι → E, (∀ i, 0 ≤ l i) ∧
          (∀ i, fs i x ≠ finiteMax fs x → l i = 0) ∧ ∑ i, l i = 1 ∧
          (∀ i, w i ∈ subdifferential (fun z ↦ ((fs i z : ℝ) : EReal)) x) ∧
          v = ∑ i, l i • w i} := by
  have hG := strictlyContinuousAt_valueVector (fun i ↦ hs i x)
  have hex : ∀ i, ∃ g : E, fs i x = finiteMax fs x →
      HasStrictGradientAt (fun z ↦ ((fs i z : ℝ) : EReal)) g x := by
    intro i
    by_cases hact : fs i x = finiteMax fs x
    · obtain ⟨g, hg⟩ := hd i hact
      exact ⟨g, fun _ ↦ hg⟩
    · exact ⟨0, fun h ↦ absurd h hact⟩
  choose g hg using hex
  have hgF : ∀ i, fs i x = finiteMax fs x → HasStrictFDerivAt (fs i) (innerSL ℝ (g i)) x := by
    intro i hi
    have h := (hg i hi).2
    simp only [EReal.toReal_coe] at h
    exact h
  -- `yF` has a strict gradient whenever `y` vanishes off the active indices
  have hgrad : ∀ y : EuclideanSpace ℝ ι, (∀ i, fs i x ≠ finiteMax fs x → y i = 0) →
      HasStrictGradientAt (fun a ↦ ((⟪y, valueVector fs a⟫_ℝ : ℝ) : EReal))
        (∑ i, y i • g i) x := fun y hy ↦
    hasStrictGradientAt_inner_valueVector fun i hyi ↦
      hgF i (by by_contra hna; exact hyi (hy i hna))
  have hconv : Convex ℝ (epigraph (fun w : EuclideanSpace ℝ ι ↦ ((vecMax w : ℝ) : EReal))) := by
    rw [← funext (fun z : EuclideanSpace ℝ ι ↦ (supportFunction_canonicalSimplex z).1)]
    exact convex_epigraph_of_sublinear (sublinear_supportFunction _)
  have hrg : IsSubdifferentiallyRegularAt
      (fun w : EuclideanSpace ℝ ι ↦ ((vecMax w : ℝ) : EReal)) (valueVector fs x) :=
    (isSubdifferentiallyRegularAt_of_convex hconv
      (isLocallyLscAt_of_lowerSemicontinuousOn isOpen_univ
        (lowerSemicontinuous_vecMax.lowerSemicontinuousOn _) (mem_univ _)
        (EReal.coe_ne_bot _) (EReal.coe_ne_top _))).1
  obtain ⟨hreg, heq, -⟩ := comp_regular_of_strictlyContinuous
    (g := fun w : EuclideanSpace ℝ ι ↦ ((vecMax w : ℝ) : EReal)) (G := valueVector fs) (x := x)
    (c := vecMax (valueVector fs x)) lowerSemicontinuous_vecMax hG rfl (by
      intro y hy _
      rw [horizonSubdifferential_vecMax] at hy
      exact hy) hrg (by
      rintro y (⟨r, hr, y', hy', rfl⟩ | hy)
      · have h := ((mem_subdifferential_vecMax_iff y' (valueVector fs x)).1 hy').2.1
        refine (hgrad _ fun i hi ↦ ?_).isSubdifferentiallyRegularAt
        rw [PiLp.smul_apply, h i hi, smul_zero]
      · rw [horizonSubdifferential_vecMax, mem_singleton_iff] at hy
        refine (hgrad y fun i _ ↦ ?_).isSubdifferentiallyRegularAt
        rw [hy]
        rfl)
  refine ⟨hreg, Subset.antisymm (subdifferential_finiteMax_subset_of_strictlyContinuous hs x) ?_⟩
  rintro v ⟨l, w, hl0, hlz, hl1, hw, rfl⟩
  have heq' : subdifferential (fun z ↦ ((finiteMax fs z : ℝ) : EReal)) x =
      {v | ∃ y ∈ subdifferential (fun w : EuclideanSpace ℝ ι ↦ ((vecMax w : ℝ) : EReal))
          (valueVector fs x),
        v ∈ subdifferential (fun a ↦ ((⟪y, valueVector fs a⟫_ℝ : ℝ) : EReal)) x} := heq
  rw [heq']
  refine ⟨WithLp.toLp 2 l, (mem_subdifferential_vecMax_iff _ _).2
    ⟨fun i _ ↦ hl0 i, fun i hi ↦ hlz i hi, hl1⟩, ?_⟩
  rw [(hgrad (WithLp.toLp 2 l) fun i hi ↦ hlz i hi).subdifferential_eq, mem_singleton_iff]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  by_cases hact : fs i x = finiteMax fs x
  · have h := hw i
    rw [(hg i hact).subdifferential_eq, mem_singleton_iff] at h
    rw [h]
  · show l i • w i = l i • g i
    rw [hlz i hact, zero_smul, zero_smul]

end Max

end RW
