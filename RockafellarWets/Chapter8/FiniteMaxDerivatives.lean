/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Directional derivatives of elementary maxima
-/

import RockafellarWets.Chapter7.MaxFunctionRegularity
import RockafellarWets.Chapter8.SmoothSubderivativeRegularity
import RockafellarWets.Chapter8.SupportFunctions
import Mathlib.Analysis.Calculus.Gradient.Basic

open Set Filter Topology
open scoped InnerProductSpace Gradient

namespace RW

variable {ι E : Type*} [Fintype ι] [Nonempty ι]

/-- The indices of the functions attaining their pointwise maximum at `x`. -/
noncomputable def maxActiveIndices (fs : ι → E → ℝ) (x : E) : Finset ι := by
  classical exact Finset.univ.filter fun i ↦ fs i x = finiteMax fs x

@[simp] theorem mem_maxActiveIndices {fs : ι → E → ℝ} {x : E} {i : ι} :
    i ∈ maxActiveIndices fs x ↔ fs i x = finiteMax fs x := by
  classical simp [maxActiveIndices]

theorem maxActiveIndices_nonempty (fs : ι → E → ℝ) (x : E) : (maxActiveIndices fs x).Nonempty := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ) Finset.univ_nonempty (fun i ↦ fs i x)
  exact ⟨i, mem_maxActiveIndices.2 hi.symm⟩

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem isSubdifferentiallyRegularAt_finiteMax {fs : ι → E → ℝ} (hs : ∀ i, ContDiff ℝ 1 (fs i)) (x : E) :
    IsSubdifferentiallyRegularAt (fun y ↦ (finiteMax fs y : EReal)) x := by
  have he : indicatorAddMax univ fs = _ := funext (fun y ↦ indicatorAddMax_of_mem (fs := fs) (mem_univ y))
  rw [← he]
  exact (isSubdifferentiallyRegularAt_indicatorAddMax hs (mem_univ x)
    (isClarkeRegularAt_of_mem_interior (by simp))).1

local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The gradients of the active functions at `x`. -/
noncomputable def maxActiveGradients (fs : ι → E → ℝ) (x : E) : Set E :=
  (fun i ↦ ∇ (fs i) x) '' (maxActiveIndices fs x : Set ι)

/-- **Exercise 8.31.** The directional subderivative of a finite maximum of smooth functions
is the largest directional derivative among its active indices. -/
theorem subderivative_finiteMax {fs : ι → E → ℝ} (hs : ∀ i, ContDiff ℝ 1 (fs i)) (x w : E) :
    subderivative (fun y ↦ (finiteMax fs y : EReal)) x w =
      ((maxActiveIndices fs x).sup' (maxActiveIndices_nonempty fs x) (fun i ↦ ⟪∇ (fs i) x, w⟫_ℝ) : ℝ) := by
  classical
  let s := maxActiveIndices fs x
  have hn : s.Nonempty := maxActiveIndices_nonempty fs x
  obtain ⟨i₀, hi₀⟩ := maxActiveIndices_nonempty fs x
  let q := fun i (t : ℝ) ↦ t⁻¹ * (fs i (x + t • w) - fs i x)
  have hpath : Tendsto (fun t : ℝ ↦ x + t • w) (𝓝[>] 0) (𝓝 x) := by
    have hc : Continuous (fun t : ℝ ↦ x + t • w) := by fun_prop
    simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hinactive : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, i ∉ s → fs i (x + t • w) < fs i₀ (x + t • w) := by
    rw [Filter.eventually_all]
    intro i
    by_cases hi : i ∈ s
    · exact Eventually.of_forall fun _ hh ↦ (hh hi).elim
    · have hlt : fs i x < fs i₀ x := by
        rw [mem_maxActiveIndices.1 hi₀]
        exact lt_of_le_of_ne (le_finiteMax fs x i) (fun h ↦ hi (mem_maxActiveIndices.2 h))
      exact ((((hs i).continuous.tendsto x).comp hpath).eventually_lt
        (((hs i₀).continuous.tendsto x).comp hpath) hlt).mono fun _ ht _ ↦ ht
  have hd (i : ι) : Tendsto (q i) (𝓝[>] 0) (𝓝 ⟪∇ (fs i) x,w⟫_ℝ) := by
    have hi := ((hs i).differentiable (by norm_num)) x
    rw [inner_gradient_left hi]
    have hline : HasDerivAt (fun t : ℝ ↦ x + t • w) ((1 : ℝ) • w) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add x
    have hdiff := hi.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
    simpa [q, Function.comp_def, smul_eq_mul] using hdiff.tendsto_slope_zero_right
  have hlim := Tendsto.finset_sup'_nhds_apply hn (fun i _ ↦ hd i)
  let f := fun y ↦ (finiteMax fs y : EReal)
  have he : indicatorAddMax univ fs = f := funext fun y ↦ indicatorAddMax_of_mem (mem_univ y)
  have hsem := semidifferentiableAt_indicatorAddMax (fs := fs) hs (C := univ) (x := x) (by simp)
  rw [he] at hsem
  refine tendsto_nhds_unique ((hsem w).hasSemiderivative.hasOneSidedDirDeriv.2.2) ((EReal.tendsto_coe.2 hlim).congr' ?_)
  filter_upwards [hinactive,self_mem_nhdsWithin] with t ht htpos
  have htp : 0 < t := htpos
  rw [differenceQuotient_eq_coe (f := f) (c := finiteMax fs x) rfl (r := finiteMax fs (x+t•w)) rfl]
  apply congrArg ((↑) : ℝ → EReal)
  obtain ⟨j,_,hj⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ) Finset.univ_nonempty (fun i ↦ fs i (x+t•w))
  change finiteMax fs (x+t•w) = fs j (x+t•w) at hj
  have hjs : j ∈ s := by
    by_contra h
    exact (ht j h).not_ge ((le_finiteMax fs _ i₀).trans_eq hj)
  refine le_antisymm ((Finset.sup'_le_iff _ _).2 (fun i hi ↦ ?_)) ?_
  · exact mul_le_mul_of_nonneg_left (sub_le_sub (le_finiteMax fs _ i) (mem_maxActiveIndices.1 hi).ge) (inv_nonneg.2 htp.le)
  · have hjl := Finset.le_sup' (fun i ↦ q i t) hjs
    simpa only [q, mem_maxActiveIndices.1 hjs, ← hj] using hjl

/-- The equivalent expression in 8.31 in terms of the component subderivatives. -/
theorem subderivative_finiteMax_eq_max_subderivatives {fs : ι → E → ℝ} (hs : ∀ i, ContDiff ℝ 1 (fs i)) (x w : E) :
    subderivative (fun y ↦ (finiteMax fs y : EReal)) x w =
      (maxActiveIndices fs x).sup' (maxActiveIndices_nonempty fs x)
        (fun i ↦ subderivative (fun y ↦ (fs i y : EReal)) x w) := by
  classical
  have he (i : ι) : subderivative (fun y ↦ (fs i y : EReal)) x w = (⟪∇ (fs i) x, w⟫_ℝ : EReal) := by
    rw [(regularSubderivatives_of_smooth (U := univ) univ_mem (hs i).contDiffOn).2.1,
      inner_gradient_left (((hs i).differentiable (by norm_num)) x)]
  rw [subderivative_finiteMax hs]
  simp_rw [he]
  have hn := maxActiveIndices_nonempty fs x
  obtain ⟨j,hj,hval⟩ := Finset.exists_mem_eq_sup' hn (fun i ↦ ⟪∇ (fs i) x,w⟫_ℝ)
  refine le_antisymm ?_ ((Finset.sup'_le_iff _ _).2 fun i hi ↦ EReal.coe_le_coe_iff.2 (Finset.le_sup' (fun k ↦ ⟪∇ (fs k) x,w⟫_ℝ) hi))
  rw [hval]
  exact Finset.le_sup' (fun i ↦ (⟪∇ (fs i) x,w⟫_ℝ : EReal)) hj

/-- The subderivative is the support function of the active gradients. -/
theorem subderivative_finiteMax_eq_supportFunction {fs : ι → E → ℝ} (hs : ∀ i, ContDiff ℝ 1 (fs i)) (x : E) :
    subderivative (fun y ↦ (finiteMax fs y : EReal)) x = supportFunction (maxActiveGradients fs x) := by
  funext w
  rw [subderivative_finiteMax hs]
  have hn := maxActiveIndices_nonempty fs x
  obtain ⟨j,hj,he⟩ := Finset.exists_mem_eq_sup' hn (fun i ↦ ⟪∇ (fs i) x,w⟫_ℝ)
  refine le_antisymm ?_ ((supportFunction_le_iff _ _ _).2 ?_)
  · rw [he]
    exact inner_le_supportFunction (D := maxActiveGradients fs x) (Set.mem_image_of_mem (fun i ↦ ∇ (fs i) x) hj) w
  · rintro _ ⟨i,hi,rfl⟩
    exact EReal.coe_le_coe_iff.2 (Finset.le_sup' (fun k ↦ ⟪∇ (fs k) x,w⟫_ℝ) hi)

end RW
