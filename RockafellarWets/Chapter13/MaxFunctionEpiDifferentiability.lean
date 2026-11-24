/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Second-order epi-differentiability of max functions

Example 13.16.  For `f = max{f₁, …, f_m}` with `fᵢ` of class `C²`, write `f = g ∘ F` with
`F = (f₁, …, f_m)` and `g = vecmax`, convex and piecewise linear.  Theorem 13.14 applies (the
qualification is void since `g` is finite), `d²g(F(x̄)) = 0` (13.9 and 13.10 for the coordinate
functions), and `∂g(F(x̄))` consists of the probability vectors supported on `I(x̄)` (8.26).  Hence
`f` is properly twice epi-differentiable at `x̄` for every `v ∈ ∂f(x̄) = con{∇fᵢ(x̄) | i ∈ I(x̄)}`,
with `d²f(x̄ | v)(w) = δ_{K(x̄,v)}(w) + max{Σ yᵢ⟪w, ∇²fᵢ(x̄)w⟫ | y ≥ 0, Σ yᵢ = 1, Σ yᵢ∇fᵢ(x̄) = v}`
(`y` supported on `I(x̄)`), and `w ∈ K(x̄, v)` exactly when `v ∈ con{∇fᵢ(x̄) | i ∈ I'(x̄, w)}`.
-/

import RockafellarWets.Chapter13.SecondOrderChainRule
import RockafellarWets.Chapter13.MaxFunctionSecondOrder
import RockafellarWets.Chapter10.AmenableFiniteMaximum
import RockafellarWets.Chapter8.NormAndMaxSubgradients
import RockafellarWets.Chapter8.FiniteMaxSubgradients

open Filter Set Topology Metric
open scoped InnerProductSpace

namespace RW

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type u} [Fintype ι] [Nonempty ι] {fs : ι → E → ℝ}

/-- The mapping `F = (f₁, …, f_m)` into Euclidean coordinates. -/
noncomputable def maxComponents (fs : ι → E → ℝ) (y : E) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i ↦ fs i y)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι]
  [Nonempty ι] in
theorem maxComponents_apply (y : E) (i : ι) : maxComponents fs y i = fs i y := rfl

omit [FiniteDimensional ℝ E] [Nonempty ι] in
theorem contDiff_maxComponents (hs : ∀ i, ContDiff ℝ 2 (fs i)) :
    ContDiff ℝ 2 (maxComponents fs) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℝ)).symm.contDiff.comp (contDiff_pi.mpr hs)

omit [FiniteDimensional ℝ E] [Nonempty ι] in
theorem fderiv_maxComponents_apply (hs : ∀ i, ContDiff ℝ 2 (fs i)) (x w : E) (i : ι) :
    fderiv ℝ (maxComponents fs) x w i = fderiv ℝ (fs i) x w := by
  have hd : ∀ j, HasFDerivAt (fs j) (fderiv ℝ (fs j) x) x :=
    fun j ↦ ((hs j).differentiable (by norm_num) x).hasFDerivAt
  have hpi : HasFDerivAt (fun y ↦ fun j ↦ fs j y) (ContinuousLinearMap.pi fun j ↦ fderiv ℝ (fs j) x)
      x := hasFDerivAt_pi.2 fun j ↦ hd j
  have hF : HasFDerivAt (maxComponents fs)
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℝ)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.pi fun j ↦ fderiv ℝ (fs j) x)) x :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℝ)).symm.toContinuousLinearMap.hasFDerivAt.comp x
      hpi
  rw [hF.fderiv]
  rfl

omit [Nonempty ι] in
theorem adjoint_fderiv_maxComponents (hs : ∀ i, ContDiff ℝ 2 (fs i)) (x : E)
    (y : EuclideanSpace ℝ ι) :
    (fderiv ℝ (maxComponents fs) x).adjoint y = ∑ i, y i • gradient (fs i) x := by
  refine ext_inner_right ℝ fun w ↦ ?_
  rw [ContinuousLinearMap.adjoint_inner_left, sum_inner]
  simp only [real_inner_smul_left, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    star_trivial]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [fderiv_maxComponents_apply hs, ← fderiv_apply_eq_inner_gradient]
  simp [mul_comm]

omit [Nonempty ι] in
/-- `⟪y, ∇²F(x̄)(w, w)⟫ = Σ yᵢ ⟪w, ∇²fᵢ(x̄)w⟫`, by uniqueness of the limits of second-order
quotients along the ray `w`. -/
theorem inner_fderiv_fderiv_maxComponents (hs : ∀ i, ContDiff ℝ 2 (fs i)) (x w : E)
    (y : EuclideanSpace ℝ ι) :
    ⟪y, fderiv ℝ (fderiv ℝ (maxComponents fs)) x w w⟫_ℝ =
      ∑ i, y i * fderiv ℝ (fderiv ℝ (fs i)) x w w := by
  have hray : Tendsto (fun τ : ℝ ↦ (τ, (0 : E))) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 0) :=
    tendsto_id.prodMk tendsto_const_nhds
  have h1 := (tendsto_mapSecondDifferenceQuotient (contDiff_maxComponents hs) x w 0).comp hray
  rw [map_zero, zero_add] at h1
  have h1' : Tendsto (fun τ : ℝ ↦ ⟪y, mapSecondDifferenceQuotient (maxComponents fs) x w τ 0⟫_ℝ)
      (𝓝[>] (0 : ℝ)) (𝓝 ⟪y, fderiv ℝ (fderiv ℝ (maxComponents fs)) x w w⟫_ℝ) :=
    (tendsto_const_nhds (x := y)).inner h1
  have h2 : ∀ i, Tendsto (fun τ : ℝ ↦ mapSecondDifferenceQuotient (fs i) x w τ 0) (𝓝[>] (0 : ℝ))
      (𝓝 (fderiv ℝ (fderiv ℝ (fs i)) x w w)) := fun i ↦ by
    have := (tendsto_mapSecondDifferenceQuotient (hs i) x w 0).comp hray
    rwa [map_zero, zero_add] at this
  have h3 := tendsto_finset_sum (Finset.univ : Finset ι) fun i _ ↦ (h2 i).const_mul (y i)
  refine tendsto_nhds_unique h1' (h3.congr' (Eventually.of_forall fun τ ↦ ?_))
  simp only [mapSecondDifferenceQuotient, smul_zero, add_zero]
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [maxComponents_apply, fderiv_maxComponents_apply hs, mul_comm, smul_eq_mul]

/-- The vector maximum has vanishing second subderivatives. -/
theorem secondSubderivativeAt_vecMax (u z : EuclideanSpace ℝ ι) :
    secondSubderivativeAt (fun v ↦ (vecMax v : EReal)) u z = 0 := by
  have hlin : ∀ i : ι, ContDiff ℝ 2 (fun v : EuclideanSpace ℝ ι ↦ v i) := fun i ↦
    (EuclideanSpace.proj i : EuclideanSpace ℝ ι →L[ℝ] ℝ).contDiff
  have hplq : IsPiecewiseLinearQuadratic (fun v : EuclideanSpace ℝ ι ↦ (vecMax v : EReal)) :=
    (finiteMaximumAmenableModel (fun i (v : EuclideanSpace ℝ ι) ↦ v i) u true hlin).plq rfl
  have hconv : Convex ℝ (epigraph (fun v : EuclideanSpace ℝ ι ↦ (vecMax v : EReal))) :=
    (finiteMaximumAmenableModel (fun i (v : EuclideanSpace ℝ ι) ↦ v i) u true hlin).convex
  have hu : u ∈ effectiveDomain (fun v : EuclideanSpace ℝ ι ↦ (vecMax v : EReal)) :=
    EReal.coe_lt_top _
  have h13 := ((piecewise_linear_quadratic_second_order hplq hconv hu).1.2.2 z).2
  have h10 := tendsto_secondDifferenceQuotientAt_finiteMax hlin u z
  have hzero : maxSecondDerivative (fun i (v : EuclideanSpace ℝ ι) ↦ v i) u z = 0 := by
    unfold maxSecondDerivative
    have : ∀ i : ι, fderiv ℝ (fderiv ℝ (fun v : EuclideanSpace ℝ ι ↦ v i)) u z z = 0 := by
      intro i
      have hf : fderiv ℝ (fun v : EuclideanSpace ℝ ι ↦ v i) =
          fun _ ↦ (EuclideanSpace.proj i : EuclideanSpace ℝ ι →L[ℝ] ℝ) := by
        funext v
        exact (EuclideanSpace.proj i : EuclideanSpace ℝ ι →L[ℝ] ℝ).fderiv
      rw [hf]
      simp
    simp only [this]
    exact Finset.sup'_const _ _
  rw [hzero] at h10
  exact tendsto_nhds_unique h13 h10

/-- **Example 13.16** (second-order epi-differentiability of max functions). -/
theorem second_order_epi_differentiability_of_max_functions (hs : ∀ i, ContDiff ℝ 2 (fs i))
    (x : E) :
    (∀ v, v ∈ subdifferential (fun y ↦ (finiteMax fs y : EReal)) x ↔
      v ∈ convexHull ℝ (maxActiveGradients fs x)) ∧
    ∀ v ∈ subdifferential (fun y ↦ (finiteMax fs y : EReal)) x,
      ProperlyTwiceEpiDifferentiableAt (fun y ↦ (finiteMax fs y : EReal)) x v ∧
      (∀ w, secondSubderivative (fun y ↦ (finiteMax fs y : EReal)) x v w =
        indicatorVA {w | subderivative (fun y ↦ (finiteMax fs y : EReal)) x w =
          ((⟪v, w⟫_ℝ : ℝ) : EReal)} w +
        ⨆ y ∈ {y : EuclideanSpace ℝ ι | (∀ i, 0 ≤ y i) ∧ (∀ i ∉ maxActiveIndices fs x, y i = 0) ∧
            ∑ i, y i = 1 ∧ ∑ i, y i • gradient (fs i) x = v},
          ((∑ i, y i * fderiv ℝ (fderiv ℝ (fs i)) x w w : ℝ) : EReal)) ∧
      (∀ w, ∃ y₀ ∈ {y : EuclideanSpace ℝ ι | (∀ i, 0 ≤ y i) ∧
          (∀ i ∉ maxActiveIndices fs x, y i = 0) ∧ ∑ i, y i = 1 ∧ ∑ i, y i • gradient (fs i) x = v},
        ∀ y ∈ {y : EuclideanSpace ℝ ι | (∀ i, 0 ≤ y i) ∧ (∀ i ∉ maxActiveIndices fs x, y i = 0) ∧
          ∑ i, y i = 1 ∧ ∑ i, y i • gradient (fs i) x = v},
        ∑ i, y i * fderiv ℝ (fderiv ℝ (fs i)) x w w ≤
          ∑ i, y₀ i * fderiv ℝ (fderiv ℝ (fs i)) x w w) ∧
      (∀ w, subderivative (fun y ↦ (finiteMax fs y : EReal)) x w = ((⟪v, w⟫_ℝ : ℝ) : EReal) ↔
        v ∈ convexHull ℝ ((fun i ↦ gradient (fs i) x) '' (maxCriticalIndices fs x w : Set ι))) := by
  classical
  have hs1 : ∀ i, ContDiff ℝ 1 (fs i) := fun i ↦ (hs i).of_le (by norm_num)
  have hG : ContDiff ℝ 2 (maxComponents fs) := contDiff_maxComponents hs
  have hlin : ∀ i : ι, ContDiff ℝ 2 (fun v : EuclideanSpace ℝ ι ↦ v i) := fun i ↦
    (EuclideanSpace.proj i : EuclideanSpace ℝ ι →L[ℝ] ℝ).contDiff
  set u := maxComponents fs x with hu
  have hgplq : IsPiecewiseLinearQuadratic (fun v : EuclideanSpace ℝ ι ↦ (vecMax v : EReal)) :=
    (finiteMaximumAmenableModel (fun i (v : EuclideanSpace ℝ ι) ↦ v i) u true hlin).plq rfl
  have hgc : Convex ℝ (epigraph (fun v : EuclideanSpace ℝ ι ↦ (vecMax v : EReal))) :=
    (finiteMaximumAmenableModel (fun i (v : EuclideanSpace ℝ ι) ↦ v i) u true hlin).convex
  have hp : IsProper (fun v : EuclideanSpace ℝ ι ↦ (vecMax v : EReal)) :=
    ⟨⟨0, EReal.coe_lt_top _⟩, fun _ ↦ EReal.bot_lt_coe _⟩
  have hx : u ∈ effectiveDomain (fun v : EuclideanSpace ℝ ι ↦ (vecMax v : EReal)) :=
    EReal.coe_lt_top _
  have hQ : ∀ y ∈ horizonSubdifferential (fun v : EuclideanSpace ℝ ι ↦ (vecMax v : EReal)) u,
      (fderiv ℝ (maxComponents fs) x).adjoint y = 0 → y = 0 := by
    intro y hy _
    rw [horizonSubdifferential_vecMax] at hy
    exact hy
  have hcomp : (fun v : EuclideanSpace ℝ ι ↦ (vecMax v : EReal)) ∘ maxComponents fs =
      fun y ↦ (finiteMax fs y : EReal) := rfl
  have hl := hgplq.lowerSemicontinuous
  have hfin : (fun v : EuclideanSpace ℝ ι ↦ (vecMax v : EReal)) u = ((vecMax u : ℝ) : EReal) := rfl
  have hlsc := isLocallyLscAt_of_isLocallyClosedAt_epigraph
    (f := fun v : EuclideanSpace ℝ ι ↦ (vecMax v : EReal)) (x := u) hfin
    (RW.IsClosed.isLocallyClosedAt (isClosed_epigraph_of_lsc_ereal _ hl) _)
  have hr := (isSubdifferentiallyRegularAt_of_convex hgc hlsc).1
  have hdf : ∀ w, subderivative (fun y ↦ (finiteMax fs y : EReal)) x w =
      subderivative (fun v : EuclideanSpace ℝ ι ↦ (vecMax v : EReal)) u
        (fderiv ℝ (maxComponents fs) x w) := by
    intro w
    rw [← hcomp]
    exact subderivative_comp_eq_of_regular (hG.of_le (by norm_num)) hl hr hQ w
  -- the multiplier set is the set of weights
  have hY : ∀ v, multiplierSet (maxComponents fs) (fun v : EuclideanSpace ℝ ι ↦ (vecMax v : EReal))
      x v = {y : EuclideanSpace ℝ ι | (∀ i, 0 ≤ y i) ∧ (∀ i ∉ maxActiveIndices fs x, y i = 0) ∧
        ∑ i, y i = 1 ∧ ∑ i, y i • gradient (fs i) x = v} := by
    intro v
    ext y
    simp only [multiplierSet, mem_setOf_eq, mem_subdifferential_vecMax_iff,
      adjoint_fderiv_maxComponents hs, mem_maxActiveIndices]
    have hvm : vecMax u = finiteMax fs x := rfl
    simp only [hu, maxComponents_apply, hvm]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      refine ⟨fun i ↦ ?_, fun i hi ↦ h2 i hi, h3, h4⟩
      by_cases hi : fs i x = finiteMax fs x
      · exact h1 i hi
      · rw [h2 i hi]
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨fun i _ ↦ h1 i, fun i hi ↦ h2 i hi, h3⟩, h4⟩
  refine ⟨fun v ↦ by rw [subdifferential_finiteMax hs1 x], fun v hv ↦ ?_⟩
  have hv' : v ∈ subdifferential ((fun v : EuclideanSpace ℝ ι ↦ (vecMax v : EReal)) ∘
      maxComponents fs) x := hv
  obtain ⟨hsup, -, -, -, hpte, -⟩ := chain_rule_second_subderivatives_plq hG hgplq hgc hx hQ hv'
  obtain ⟨hYne, -, hYcpt⟩ := multiplierSet_properties hG hl hr hQ hv'
  obtain ⟨M⟩ := hgplq.nonempty_localModel u
  refine ⟨hpte, fun w ↦ ?_, fun w ↦ ?_, fun w ↦ ?_⟩
  pick_goal 2
  · -- the maximum is attained
    rw [hY v] at hYne hYcpt
    have hcont : Continuous (fun y : EuclideanSpace ℝ ι ↦
        ∑ i, y i * fderiv ℝ (fderiv ℝ (fs i)) x w w) :=
      continuous_finset_sum _ fun i _ ↦
        ((EuclideanSpace.proj i : EuclideanSpace ℝ ι →L[ℝ] ℝ).continuous.mul continuous_const)
    obtain ⟨y₀, hy₀, hmax⟩ := hYcpt.exists_isMaxOn hYne hcont.continuousOn
    exact ⟨y₀, hy₀, fun y hy ↦ hmax hy⟩
  · -- the formula
    set K := {w | subderivative (fun y ↦ (finiteMax fs y : EReal)) x w =
      ((⟪v, w⟫_ℝ : ℝ) : EReal)} with hKdef
    have hterm : ∀ y ∈ multiplierSet (maxComponents fs)
        (fun v : EuclideanSpace ℝ ι ↦ (vecMax v : EReal)) x v,
        secondSubderivative (fun v : EuclideanSpace ℝ ι ↦ (vecMax v : EReal)) u y
          (fderiv ℝ (maxComponents fs) x w) = indicatorVA K w := by
      intro y hy
      have hyv := inner_le_subderivative_of_convex hp hgc hfin hy.1
      rw [M.secondSubderivative_eq hgplq hx hyv, ← M.secondSubderivativeAt_eq hgplq hx,
        secondSubderivativeAt_vecMax, ← ContinuousLinearMap.adjoint_inner_left, hy.2, ← hdf]
      by_cases hK : subderivative (fun y ↦ (finiteMax fs y : EReal)) x w =
          ((⟪v, w⟫_ℝ : ℝ) : EReal)
      · rw [if_pos hK, indicatorVA_apply_mem (show w ∈ K from hK)]
      · rw [if_neg hK, indicatorVA_apply_not_mem (show w ∉ K from hK)]
    rw [← hcomp, hsup w]
    simp only [inner_fderiv_fderiv_maxComponents hs]
    rw [← hY v]
    by_cases hK : subderivative (fun y ↦ (finiteMax fs y : EReal)) x w = ((⟪v, w⟫_ℝ : ℝ) : EReal)
    · rw [indicatorVA_apply_mem (show w ∈ K from hK), zero_add]
      refine iSup_congr fun y ↦ iSup_congr fun hy ↦ ?_
      rw [hterm y hy, indicatorVA_apply_mem (show w ∈ K from hK), zero_add]
    · rw [indicatorVA_apply_not_mem (show w ∉ K from hK)]
      obtain ⟨y₀, hy₀⟩ := hYne
      have htop : (⊤ : EReal) + ⨆ y ∈ multiplierSet (maxComponents fs)
          (fun v : EuclideanSpace ℝ ι ↦ (vecMax v : EReal)) x v,
          ((∑ i, y i * fderiv ℝ (fderiv ℝ (fs i)) x w w : ℝ) : EReal) = ⊤ := by
        refine EReal.top_add_of_ne_bot (ne_bot_of_le_ne_bot (EReal.coe_ne_bot
          (∑ i, y₀ i * fderiv ℝ (fderiv ℝ (fs i)) x w w)) ?_)
        exact le_iSup₂ (f := fun y _ ↦ ((∑ i, y i * fderiv ℝ (fderiv ℝ (fs i)) x w w : ℝ) :
          EReal)) y₀ hy₀
      rw [htop, eq_top_iff]
      refine le_trans (le_of_eq ?_) (le_iSup₂ (f := fun y _ ↦
        secondSubderivative (fun v : EuclideanSpace ℝ ι ↦ (vecMax v : EReal)) u y
          (fderiv ℝ (maxComponents fs) x w) +
        ((∑ i, y i * fderiv ℝ (fderiv ℝ (fs i)) x w w : ℝ) : EReal)) y₀ hy₀)
      rw [hterm y₀ hy₀, indicatorVA_apply_not_mem (show w ∉ K from hK), EReal.top_add_coe]
  · -- the critical cone
    have hdmax : subderivative (fun y ↦ (finiteMax fs y : EReal)) x w =
        (maxDirectionalDerivative fs x w : EReal) := subderivative_finiteMax hs1 x w
    rw [hdmax, EReal.coe_eq_coe_iff]
    constructor
    · intro hK
      obtain ⟨y, hy⟩ := hYne
      rw [hY v] at hy
      obtain ⟨hy0, hyI, hy1, hyv⟩ := hy
      set t := maxCriticalIndices fs x w
      -- the weights vanish off `I'(x̄, w)`
      have hvw : ∑ i, y i * ⟪gradient (fs i) x, w⟫_ℝ = maxDirectionalDerivative fs x w := by
        rw [hK, ← hyv, sum_inner]
        simp only [real_inner_smul_left]
      have hle : ∀ i ∈ maxActiveIndices fs x,
          ⟪gradient (fs i) x, w⟫_ℝ ≤ maxDirectionalDerivative fs x w := fun i hi ↦
        Finset.le_sup' (fun i ↦ ⟪gradient (fs i) x, w⟫_ℝ) hi
      have hzero : ∀ i ∉ t, y i = 0 := by
        intro i hit
        by_cases hiI : i ∈ maxActiveIndices fs x
        · have hlt : ⟪gradient (fs i) x, w⟫_ℝ < maxDirectionalDerivative fs x w :=
            lt_of_le_of_ne (hle i hiI) (fun h ↦ hit (mem_maxCriticalIndices.2 ⟨hiI, h⟩))
          have hsum : ∑ j, y j * (maxDirectionalDerivative fs x w - ⟪gradient (fs j) x, w⟫_ℝ) =
              0 := by
            simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hy1, one_mul, hvw,
              sub_self]
          have hnn : ∀ j ∈ Finset.univ,
              0 ≤ y j * (maxDirectionalDerivative fs x w - ⟪gradient (fs j) x, w⟫_ℝ) := by
            intro j _
            by_cases hjI : j ∈ maxActiveIndices fs x
            · exact mul_nonneg (hy0 j) (by linarith [hle j hjI])
            · rw [hyI j hjI, zero_mul]
          have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum i (Finset.mem_univ i)
          rcases mul_eq_zero.1 h0 with h | h
          · exact h
          · linarith
        · exact hyI i hiI
      rw [← hyv]
      have hsplit : ∑ i, y i • gradient (fs i) x = ∑ i ∈ t, y i • gradient (fs i) x :=
        (Finset.sum_subset (Finset.subset_univ t) fun i _ hit ↦ by rw [hzero i hit, zero_smul]).symm
      have ht1 : ∑ i ∈ t, y i = 1 := by
        rw [← hy1]
        exact Finset.sum_subset (Finset.subset_univ t) fun i _ hit ↦ hzero i hit
      rw [hsplit]
      exact (convex_convexHull ℝ _).sum_mem (fun i _ ↦ hy0 i) ht1
        fun i hi ↦ subset_convexHull ℝ _ ⟨i, hi, rfl⟩
    · intro hconv
      have hsub : (fun i ↦ gradient (fs i) x) '' (maxCriticalIndices fs x w : Set ι) ⊆
          {u : E | ⟪u, w⟫_ℝ = maxDirectionalDerivative fs x w} := by
        rintro _ ⟨i, hi, rfl⟩
        exact (mem_maxCriticalIndices.1 hi).2
      have hc : Convex ℝ {u : E | ⟪u, w⟫_ℝ = maxDirectionalDerivative fs x w} := by
        have : {u : E | ⟪u, w⟫_ℝ = maxDirectionalDerivative fs x w} =
            (innerSL ℝ w) ⁻¹' {maxDirectionalDerivative fs x w} := by
          ext u; simp [real_inner_comm]
        rw [this]
        exact (convex_singleton _).linear_preimage (innerSL ℝ w).toLinearMap
      have := convexHull_min hsub hc hconv
      exact this.symm

end RW
