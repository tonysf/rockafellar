/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 7: Regularity of max functions

Example 7.28: for a set `C ⊆ ℝⁿ` and finitely many smooth `fᵢ`, the function
`f = δ_C + max_{i ∈ I} fᵢ` is subdifferentially regular and epi-differentiable
at every `x̄ ∈ C` where `C` is Clarke regular, and semidifferentiable at every
`x̄ ∈ int C`.

The proof is the book's: in `ℝⁿ × ℝ` (Euclidean), `epi f` is the constraint
set `X ∩ F⁻¹(D)` with `X = C × ℝ`, `F(x, α) = (fᵢ(x) - α)_{i ∈ I}` and `D` the
nonpositive orthant of `ℝ^I`, and Theorem 6.14 applies.  The constraint
qualification holds because a normal `y ∈ N_D(F(x̄, ᾱ))` has `yᵢ ≥ 0`, while the
second component of `-∇F(x̄, ᾱ)* y` is `∑ yᵢ` and must vanish since normals to
`C × ℝ` have zero `ℝ`-component.  The repository's 6.14 assumes `X` closed;
since the book only asks `C` to be regular, hence locally closed, at `x̄`, the
set `C` is first replaced by a closed piece `C ∩ V`, Clarke regularity being a
local property (`isClarkeRegularAt_inter_nhds_iff`).

`I` is a nonempty finite type, as the maximum over an empty family would be
`-∞`; "smooth" is read as `C¹`.
-/

import RockafellarWets.Chapter7.SubdifferentialRegularity
import RockafellarWets.Chapter6.ConstraintNormals
import RockafellarWets.Chapter6.ProductCones
import Mathlib.Analysis.InnerProductSpace.PiL2

open Filter Set Topology Metric
open scoped InnerProductSpace

namespace RW

/-! ### Locality of Clarke regularity -/

section LocalClosed

variable {X : Type*} [TopologicalSpace X] [RegularSpace X]

/-- Local closedness only depends on the set near the point. -/
theorem isLocallyClosedAt_inter_nhds_iff {S W : Set X} {z : X} (hW : W ∈ 𝓝 z) :
    IsLocallyClosedAt (S ∩ W) z ↔ IsLocallyClosedAt S z := by
  obtain ⟨W', ⟨hW'n, hW'c⟩, hW'W⟩ := (closed_nhds_basis z).mem_iff.1 hW
  have key : ∀ V : Set X, S ∩ W ∩ (V ∩ W') = S ∩ (V ∩ W') := by
    intro V
    ext y
    simp only [mem_inter_iff]
    constructor
    · rintro ⟨⟨hS, -⟩, hV, hW'⟩
      exact ⟨hS, hV, hW'⟩
    · rintro ⟨hS, hV, hW'⟩
      exact ⟨⟨hS, hW'W hW'⟩, hV, hW'⟩
  constructor
  · rintro ⟨V, hV, hVc, hSV⟩
    refine ⟨V ∩ W', inter_mem hV hW'n, hVc.inter hW'c, ?_⟩
    rw [← key, ← inter_assoc]
    exact hSV.inter hW'c
  · rintro ⟨V, hV, hVc, hSV⟩
    refine ⟨V ∩ W', inter_mem hV hW'n, hVc.inter hW'c, ?_⟩
    rw [key, ← inter_assoc]
    exact hSV.inter hW'c

end LocalClosed

section Localization

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Clarke regularity only depends on the set near the point. -/
theorem isClarkeRegularAt_inter_nhds_iff {S W : Set F} {z : F} (hW : W ∈ 𝓝 z) :
    IsClarkeRegularAt (S ∩ W) z ↔ IsClarkeRegularAt S z := by
  unfold IsClarkeRegularAt
  rw [isLocallyClosedAt_inter_nhds_iff hW, normalCone_inter_nhds hW,
    regularNormalCone_inter_nhds hW]

theorem isClarkeRegularAt_congr_of_inter_eq {S S' W : Set F} {z : F} (hW : W ∈ 𝓝 z)
    (h : S ∩ W = S' ∩ W) : IsClarkeRegularAt S z ↔ IsClarkeRegularAt S' z := by
  rw [← isClarkeRegularAt_inter_nhds_iff hW, h, isClarkeRegularAt_inter_nhds_iff hW]

end Localization

/-! ### Example 7.28 -/

section MaxFunctionDefs

variable {E : Type*} {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The pointwise maximum `max_{i ∈ I} fᵢ(x)` of finitely many real functions. -/
noncomputable def finiteMax (fs : ι → E → ℝ) (x : E) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i ↦ fs i x

theorem le_finiteMax (fs : ι → E → ℝ) (x : E) (i : ι) : fs i x ≤ finiteMax fs x :=
  Finset.le_sup' (fun i ↦ fs i x) (Finset.mem_univ i)

theorem finiteMax_le_iff {fs : ι → E → ℝ} {x : E} {a : ℝ} :
    finiteMax fs x ≤ a ↔ ∀ i, fs i x ≤ a := by
  rw [finiteMax, Finset.sup'_le_iff]
  simp

/-- The function `f = δ_C + max_{i ∈ I} fᵢ` of Example 7.28. -/
noncomputable def indicatorAddMax (C : Set E) (fs : ι → E → ℝ) (x : E) : EReal :=
  indicatorVA C x + ((finiteMax fs x : ℝ) : EReal)

theorem indicatorAddMax_of_mem {C : Set E} {fs : ι → E → ℝ} {x : E} (hx : x ∈ C) :
    indicatorAddMax C fs x = ((finiteMax fs x : ℝ) : EReal) := by
  rw [indicatorAddMax, indicatorVA_apply_mem hx, zero_add]

theorem indicatorAddMax_of_not_mem {C : Set E} {fs : ι → E → ℝ} {x : E} (hx : x ∉ C) :
    indicatorAddMax C fs x = ⊤ := by
  rw [indicatorAddMax, indicatorVA_apply_not_mem hx, EReal.top_add_coe]

end MaxFunctionDefs

section ConstraintMap

variable {E : Type*} {ι : Type*}

/-- The constraint map `(x, α) ↦ (fᵢ(x) - α)_{i ∈ I}` of the proof of 7.28. -/
noncomputable def maxConstraintMap (fs : ι → E → ℝ) (z : WithLp 2 (E × ℝ)) :
    EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i ↦ fs i z.fst - z.snd)

theorem maxConstraintMap_apply (fs : ι → E → ℝ) (z : WithLp 2 (E × ℝ)) (i : ι) :
    maxConstraintMap fs z i = fs i z.fst - z.snd := rfl

/-- The nonpositive orthant of `ℝ^I`. -/
def nonposOrthant (ι : Type*) : Set (EuclideanSpace ℝ ι) := {y | ∀ i, y i ≤ 0}

theorem isClosed_nonposOrthant : IsClosed (nonposOrthant ι) := by
  have h : nonposOrthant ι = ⋂ i, (fun y : EuclideanSpace ℝ ι ↦ y i) ⁻¹' Iic 0 := by
    ext y
    simp [nonposOrthant]
  rw [h]
  exact isClosed_iInter fun i ↦
    isClosed_Iic.preimage (PiLp.continuous_apply 2 (fun _ : ι ↦ ℝ) i)

theorem convex_nonposOrthant : Convex ℝ (nonposOrthant ι) := by
  intro y hy z hz a b ha hb _ i
  have h1 := hy i
  have h2 := hz i
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  nlinarith [mul_nonneg ha (neg_nonneg.2 h1), mul_nonneg hb (neg_nonneg.2 h2)]

end ConstraintMap

section ConstraintEpigraph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The epigraph of `δ_C + max fᵢ` in `ℝⁿ × ℝ` as a constraint set. -/
theorem l2Epigraph_indicatorAddMax (C : Set E) (fs : ι → E → ℝ) :
    l2Epigraph (indicatorAddMax C fs) =
      l2ProdSet C univ ∩ maxConstraintMap fs ⁻¹' nonposOrthant ι := by
  ext z
  show indicatorAddMax C fs z.fst ≤ (z.snd : EReal) ↔ _
  by_cases hz : z.fst ∈ C
  · rw [indicatorAddMax_of_mem hz, EReal.coe_le_coe_iff, finiteMax_le_iff]
    simp [hz, nonposOrthant, maxConstraintMap_apply, mem_l2ProdSet]
  · rw [indicatorAddMax_of_not_mem hz]
    simp [hz, mem_l2ProdSet]

end ConstraintEpigraph

section ConstraintDerivative

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι]

theorem contDiff_maxConstraintMap {fs : ι → E → ℝ} (hfs : ∀ i, ContDiff ℝ 1 (fs i)) :
    ContDiff ℝ 1 (maxConstraintMap fs) := by
  have hfst : ContDiff ℝ 1 (fun z : WithLp 2 (E × ℝ) ↦ z.fst) :=
    (WithLp.fstL 2 ℝ E ℝ).contDiff
  have hsnd : ContDiff ℝ 1 (fun z : WithLp 2 (E × ℝ) ↦ z.snd) :=
    (WithLp.sndL 2 ℝ E ℝ).contDiff
  have hpi : ContDiff ℝ 1 (fun z : WithLp 2 (E × ℝ) ↦ fun i ↦ fs i z.fst - z.snd) :=
    contDiff_pi.2 fun i ↦ ((hfs i).comp hfst).sub hsnd
  exact (EuclideanSpace.equiv ι ℝ).symm.contDiff.comp hpi

/-- Along the `ℝ`-direction the constraint map is affine with slope `(-1, …, -1)`,
which identifies the derivative there. -/
theorem fderiv_maxConstraintMap_snd {fs : ι → E → ℝ} (hfs : ∀ i, ContDiff ℝ 1 (fs i))
    (z : WithLp 2 (E × ℝ)) :
    fderiv ℝ (maxConstraintMap fs) z (WithLp.toLp 2 (0, 1)) =
      WithLp.toLp 2 (fun _ : ι ↦ (-1 : ℝ)) := by
  set v : WithLp 2 (E × ℝ) := WithLp.toLp 2 (0, 1) with hv
  set c : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun _ : ι ↦ (-1 : ℝ)) with hc
  have hline : ∀ t : ℝ, maxConstraintMap fs (z + t • v) = maxConstraintMap fs z + t • c := by
    intro t
    ext i
    simp [maxConstraintMap_apply, hv, hc]
    ring
  have hdiff : DifferentiableAt ℝ (maxConstraintMap fs) z :=
    ((contDiff_maxConstraintMap hfs).differentiable (by norm_num)) z
  have hpath : HasDerivAt (fun t : ℝ ↦ z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have h1 : HasDerivAt (fun t : ℝ ↦ maxConstraintMap fs (z + t • v))
      (fderiv ℝ (maxConstraintMap fs) z v) 0 :=
    hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hpath (by simp)
  have h2 : HasDerivAt (fun t : ℝ ↦ maxConstraintMap fs (z + t • v)) c 0 := by
    simp_rw [hline]
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const c).const_add (maxConstraintMap fs z)
  exact h1.unique h2

end ConstraintDerivative

section MaxFunctions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι]

/-- The constraint qualification of 6.14 for the max-function epigraph. -/
theorem normalConstraintQualification_maxConstraint {C : Set E} {fs : ι → E → ℝ}
    (hfs : ∀ i, ContDiff ℝ 1 (fs i)) {z : WithLp 2 (E × ℝ)}
    (hzD : maxConstraintMap fs z ∈ nonposOrthant ι) :
    NormalConstraintQualification (l2ProdSet C univ) (nonposOrthant ι)
      (fderiv ℝ (maxConstraintMap fs) z) z (maxConstraintMap fs z) := by
  classical
  intro y hy hneg
  set A := fderiv ℝ (maxConstraintMap fs) z with hA
  set u := maxConstraintMap fs z with hu
  rw [normalCone_eq_of_convex convex_nonposOrthant hzD] at hy
  have hnonneg : ∀ i, 0 ≤ y i := by
    intro i
    have hmem : u - EuclideanSpace.single i (1 : ℝ) ∈ nonposOrthant ι := by
      intro j
      have hj := hzD j
      by_cases hji : j = i
      · subst hji
        simp only [PiLp.sub_apply, EuclideanSpace.single_apply, if_true]
        linarith
      · simp only [PiLp.sub_apply, EuclideanSpace.single_apply, if_neg hji, sub_zero]
        exact hj
    have := hy _ hmem
    rw [sub_sub_cancel_left, inner_neg_right, EuclideanSpace.inner_single_right] at this
    simpa using this
  have hzeq : z = WithLp.toLp 2 (z.fst, z.snd) := rfl
  have hnegmem := hneg
  rw [hzeq, normalCone_l2ProdSet C univ z.fst z.snd, mem_l2ProdSet, normalCone_univ,
    mem_singleton_iff] at hnegmem
  have hsnd : (A.adjoint y).snd = 0 := by
    have h := hnegmem.2
    simpa using h
  have hpair : ⟪A.adjoint y, WithLp.toLp 2 ((0 : E), (1 : ℝ))⟫_ℝ = (A.adjoint y).snd := by
    simp [WithLp.prod_inner_apply]
  have hadj : ⟪A.adjoint y, WithLp.toLp 2 ((0 : E), (1 : ℝ))⟫_ℝ =
      ⟪y, A (WithLp.toLp 2 ((0 : E), (1 : ℝ)))⟫_ℝ :=
    ContinuousLinearMap.adjoint_inner_left A _ y
  rw [hA, fderiv_maxConstraintMap_snd hfs z] at hadj
  have hsum : ⟪y, (WithLp.toLp 2 (fun _ : ι ↦ (-1 : ℝ)) : EuclideanSpace ℝ ι)⟫_ℝ =
      -∑ i, y i := by
    simp [PiLp.inner_apply, Finset.sum_neg_distrib]
  have hzero : ∑ i, y i = 0 := by
    have : (A.adjoint y).snd = -∑ i, y i := by rw [← hpair, hadj, hsum]
    linarith [this, hsnd]
  have hall := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ hnonneg i).1 hzero
  ext i
  simpa using hall i (Finset.mem_univ i)

variable [Nonempty ι]

/-- **Example 7.28**: `f = δ_C + max_{i ∈ I} fᵢ` with `C¹` functions `fᵢ` is
subdifferentially regular and epi-differentiable at every `x̄ ∈ C` where `C`
is Clarke regular. -/
theorem isSubdifferentiallyRegularAt_indicatorAddMax {C : Set E} {fs : ι → E → ℝ}
    (hfs : ∀ i, ContDiff ℝ 1 (fs i)) {x : E} (hx : x ∈ C) (hC : IsClarkeRegularAt C x) :
    IsSubdifferentiallyRegularAt (indicatorAddMax C fs) x ∧
      EpiDifferentiableAt (indicatorAddMax C fs) x := by
  obtain ⟨V, hV, -, hCV⟩ := hC.1
  have hxV : x ∈ V := mem_of_mem_nhds hV
  have hC'reg : IsClarkeRegularAt (C ∩ V) x := (isClarkeRegularAt_inter_nhds_iff hV).2 hC
  have hfx : indicatorAddMax C fs x = ((finiteMax fs x : ℝ) : EReal) := indicatorAddMax_of_mem hx
  set z : WithLp 2 (E × ℝ) := WithLp.toLp 2 (x, finiteMax fs x) with hz
  have hzD : maxConstraintMap fs z ∈ nonposOrthant ι := fun i ↦ by
    rw [maxConstraintMap_apply, sub_nonpos]
    exact le_finiteMax fs x i
  have hzX : z ∈ l2ProdSet (C ∩ V) univ := ⟨⟨hx, hxV⟩, mem_univ _⟩
  have hXreg : IsClarkeRegularAt (l2ProdSet (C ∩ V) univ) z :=
    (isClarkeRegularAt_l2ProdSet_iff hCV isClosed_univ ⟨hx, hxV⟩ (mem_univ _)).2
      ⟨hC'reg, isClarkeRegularAt_univ _⟩
  have hDreg : IsClarkeRegularAt (nonposOrthant ι) (maxConstraintMap fs z) :=
    isClarkeRegularAt_of_convex convex_nonposOrthant hzD
      (IsClosed.isLocallyClosedAt isClosed_nonposOrthant _)
  have hreg' : IsClarkeRegularAt (l2Epigraph (indicatorAddMax (C ∩ V) fs)) z := by
    rw [l2Epigraph_indicatorAddMax]
    exact (clarkeRegularity_constraints (isClosed_l2ProdSet hCV isClosed_univ)
      isClosed_nonposOrthant (contDiff_maxConstraintMap hfs)
      (show z ∈ l2ProdSet (C ∩ V) univ ∩ maxConstraintMap fs ⁻¹' nonposOrthant ι from ⟨hzX, hzD⟩)
      (normalConstraintQualification_maxConstraint hfs hzD) hXreg hDreg).1
  have hW : (fun w : WithLp 2 (E × ℝ) ↦ w.fst) ⁻¹' V ∈ 𝓝 z :=
    (WithLp.continuous_fst 2 E ℝ).continuousAt.preimage_mem_nhds hV
  have hloc : l2Epigraph (indicatorAddMax C fs) ∩ (fun w : WithLp 2 (E × ℝ) ↦ w.fst) ⁻¹' V =
      l2Epigraph (indicatorAddMax (C ∩ V) fs) ∩ (fun w : WithLp 2 (E × ℝ) ↦ w.fst) ⁻¹' V := by
    rw [l2Epigraph_indicatorAddMax, l2Epigraph_indicatorAddMax]
    ext w
    simp only [mem_inter_iff, mem_preimage, mem_l2ProdSet, mem_univ, and_true]
    tauto
  have hreg : IsClarkeRegularAt (l2Epigraph (indicatorAddMax C fs)) z :=
    (isClarkeRegularAt_congr_of_inter_eq hW hloc).2 hreg'
  have hfull : IsSubdifferentiallyRegularAt (indicatorAddMax C fs) x := by
    refine ⟨by rw [hfx]; exact EReal.coe_ne_bot _, by rw [hfx]; exact EReal.coe_ne_top _, ?_⟩
    rw [hfx, EReal.toReal_coe]
    exact hreg
  exact ⟨hfull, hfull.epiDifferentiableAt⟩

/-- **Example 7.28**: `f = δ_C + max_{i ∈ I} fᵢ` is semidifferentiable at every
`x̄ ∈ int C`. -/
theorem semidifferentiableAt_indicatorAddMax {C : Set E} {fs : ι → E → ℝ}
    (hfs : ∀ i, ContDiff ℝ 1 (fs i)) {x : E} (hx : x ∈ interior C) :
    SemidifferentiableAt (indicatorAddMax C fs) x := by
  have hreg := (isSubdifferentiallyRegularAt_indicatorAddMax hfs (interior_subset hx)
    (isClarkeRegularAt_of_mem_interior hx)).1
  refine hreg.semidifferentiableAt_iff.2 fun w ↦ ?_
  -- slopes of the `fᵢ` along `w` converge, hence are eventually bounded
  have hslope : ∀ i, Tendsto (fun t : ℝ ↦ t⁻¹ * (fs i (x + t • w) - fs i x)) (𝓝[>] 0)
      (𝓝 (fderiv ℝ (fs i) x ((1 : ℝ) • w))) := by
    intro i
    have hpath : HasDerivAt (fun t : ℝ ↦ x + t • w) ((1 : ℝ) • w) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add x
    have hd : HasDerivAt (fun t : ℝ ↦ fs i (x + t • w)) (fderiv ℝ (fs i) x ((1 : ℝ) • w)) 0 :=
      (((hfs i).differentiable (by norm_num)) x).hasFDerivAt.comp_hasDerivAt_of_eq
        (0 : ℝ) hpath (by simp)
    have := hd.tendsto_slope_zero_right
    simpa [smul_eq_mul] using this
  set K : ℝ := ∑ i, |fderiv ℝ (fs i) x ((1 : ℝ) • w)| + 1 with hK
  have hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, t⁻¹ * (fs i (x + t • w) - fs i x) < K := by
    rw [Filter.eventually_all]
    intro i
    refine (hslope i).eventually (gt_mem_nhds ?_)
    have h1 := le_abs_self (fderiv ℝ (fs i) x ((1 : ℝ) • w))
    have h2 : |fderiv ℝ (fs i) x ((1 : ℝ) • w)| ≤ ∑ j, |fderiv ℝ (fs j) x ((1 : ℝ) • w)| :=
      Finset.single_le_sum (f := fun j ↦ |fderiv ℝ (fs j) x ((1 : ℝ) • w)|)
        (fun j _ ↦ abs_nonneg _) (Finset.mem_univ i)
    linarith
  have hpathC : ∀ᶠ t in 𝓝[>] (0 : ℝ), x + t • w ∈ interior C := by
    have hcont : Tendsto (fun t : ℝ ↦ x + t • w) (𝓝 0) (𝓝 x) := by
      have h0 : Tendsto (fun t : ℝ ↦ x + t • w) (𝓝 0) (𝓝 (x + (0 : ℝ) • w)) :=
        (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
      rwa [zero_smul, add_zero] at h0
    exact (hcont.mono_left nhdsWithin_le_nhds).eventually (isOpen_interior.mem_nhds hx)
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), differenceQuotient (indicatorAddMax C fs) x t w ≤ K := by
    filter_upwards [hbound, hpathC, self_mem_nhdsWithin] with t ht htC htpos
    have htpos' : (0 : ℝ) < t := htpos
    rw [differenceQuotient_eq_coe (indicatorAddMax_of_mem (interior_subset hx))
      (indicatorAddMax_of_mem (interior_subset htC))]
    apply EReal.coe_le_coe_iff.2
    have hmax : finiteMax fs (x + t • w) ≤ finiteMax fs x + t * K := by
      rw [finiteMax_le_iff]
      intro i
      have h1 := ht i
      have h2 := le_finiteMax fs x i
      have h3 : fs i (x + t • w) - fs i x < t * K := by
        have := mul_lt_mul_of_pos_left h1 htpos'
        rwa [← mul_assoc, mul_inv_cancel₀ htpos'.ne', one_mul] at this
      linarith
    rw [inv_mul_le_iff₀ htpos']
    linarith
  have hfreq : ∃ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w,
      differenceQuotient (indicatorAddMax C fs) x p.1 p.2 ≤ K :=
    (tendsto_pair_const w).frequently hev.frequently
  exact lt_of_le_of_lt (liminf_le_of_frequently_le' hfreq) (EReal.coe_lt_top K)

end MaxFunctions

end RW
