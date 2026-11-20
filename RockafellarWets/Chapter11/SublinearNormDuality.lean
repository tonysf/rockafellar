/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Inner and outer norm duality for sublinear mappings
-/
import RockafellarWets.Chapter11.AdjointDistance
import Mathlib.Analysis.Normed.Group.Pointwise

open Set Metric
open scoped InnerProductSpace Pointwise ENNReal NNReal
namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The outer norm is the maximum support value over the dual unit ball. -/
theorem svOuterNorm_eq_iSup_supportFunction (H : E → Set F) :
    svOuterNorm H = ⨆y∈closedBall (0:F) 1,
      (supportFunction (svImage H (closedBall (0:E) 1)) y).toENNReal := by
  apply le_antisymm
  · apply svOuterNorm_le_iff_ball.mpr
    intro w hw z hz
    have hzC : z ∈ svImage H (closedBall (0:E) 1) := mem_svImage.mpr ⟨w,mem_closedBall_zero_iff.mpr hw,hz⟩
    have hsupport : supportFunction (closedBall (0:F) 1) z ≤
        ⨆y∈closedBall (0:F) 1, supportFunction (svImage H (closedBall (0:E) 1)) y := by
      apply (supportFunction_le_iff _ _ _).mpr
      intro y hy
      have hi : (⟪y,z⟫_ℝ:EReal) ≤ supportFunction (svImage H (closedBall (0:E) 1)) y := by
        simpa only [real_inner_comm] using inner_le_supportFunction hzC y
      exact hi.trans (le_iSup₂_of_le y hy le_rfl)
    have h := EReal.toENNReal_le_toENNReal hsupport
    rw [(supportFunction_unitBall z).1] at h
    simpa only [ereal_toENNReal_iSup,EReal.real_coe_toENNReal,← coe_nnnorm,
      ENNReal.ofReal_coe_nnreal] using h
  · apply iSup₂_le
    intro y hy
    rw [supportFunction,ereal_toENNReal_iSup]
    apply iSup_le
    intro z
    obtain ⟨w,hw,hz⟩ := mem_svImage.mp z.property
    have hinner : ⟪(z:F),y⟫_ℝ ≤ ‖(z:F)‖ := by
      have hn : ‖y‖ ≤ 1 := mem_closedBall_zero_iff.mp hy
      exact (real_inner_le_norm _ _).trans (by nlinarith [norm_nonneg (z:F)])
    have h := EReal.toENNReal_le_toENNReal (EReal.coe_le_coe_iff.mpr hinner)
    have hn : ((⟪(z:F),y⟫_ℝ:EReal)).toENNReal ≤ (‖(z:F)‖₊:ℝ≥0∞) := by
      simpa only [EReal.real_coe_toENNReal,← coe_nnnorm,ENNReal.ofReal_coe_nnreal] using h
    exact hn.trans (coe_nnnorm_le_svOuterNorm (mem_closedBall_zero_iff.mp hw) hz)

theorem svOuterNorm_neg_reflection (H : E → Set F) :
    svOuterNorm (fun w ↦ -(H (-w))) = svOuterNorm H := by
  have hbound (G : E → Set F) : svOuterNorm (fun w ↦ -(G (-w))) ≤ svOuterNorm G := by
    apply svOuterNorm_le_iff_ball.mpr
    intro w hw z hz
    have h := coe_nnnorm_le_svOuterNorm (H := G) (w := -w) (z := -z)
      (by simpa using hw) (show -z ∈ G (-w) from hz)
    simpa using h
  refine le_antisymm (hbound H) ?_
  simpa only [neg_neg] using hbound (fun w ↦ -(H (-w)))

theorem svInnerNorm_neg_reflection (H : E → Set F) :
    svInnerNorm (fun w ↦ -(H (-w))) = svInnerNorm H := by
  have hbound (G : E → Set F) : svInnerNorm (fun w ↦ -(G (-w))) ≤ svInnerNorm G := by
    rw [svInnerNorm_eq_iSup_infEDist,svInnerNorm_eq_iSup_infEDist]
    apply iSup₂_le
    intro w hw
    have he : infEDist 0 (-(G (-w))) = infEDist 0 (G (-w)) := by
      simpa only [neg_zero] using infEDist_neg_neg (0:F) (G (-w))
    rw [he]
    exact le_iSup₂_of_le (-w) (by simpa using hw) le_rfl
  refine le_antisymm (hbound H) ?_
  simpa only [neg_neg] using hbound (fun w ↦ -(H (-w)))

theorem svAdjoint_norms_eq (H : E → Set F) :
    svOuterNorm (svLowerAdjoint H) = svOuterNorm (svUpperAdjoint H) ∧
      svInnerNorm (svLowerAdjoint H) = svInnerNorm (svUpperAdjoint H) := by
  have he : svLowerAdjoint H = fun y ↦ -(svUpperAdjoint H (-y)) :=
    funext (svLowerAdjoint_eq_neg_upperAdjoint H)
  rw [he]
  exact ⟨svOuterNorm_neg_reflection _,svInnerNorm_neg_reflection _⟩

theorem svOuterNorm_eq_svInnerNorm_lowerAdjoint {H : E → Set F}
    (hh : SvSublinear H) (ho : SvOsc H) : svOuterNorm H = svInnerNorm (svLowerAdjoint H) := by
  rw [svOuterNorm_eq_iSup_supportFunction,svInnerNorm_eq_iSup_infEDist]
  simp only [supportFunction_svImage_eq_infEDist_lowerAdjoint hh ho,EReal.toENNReal_coe]

/-- Both inner/outer norm correspondences of Example 11.29, including infinite norms. -/
theorem sublinear_adjoint_norm_duality {H : E → Set F} (hh : SvSublinear H) (ho : SvOsc H) :
    svOuterNorm H = svInnerNorm (svUpperAdjoint H) ∧
      svOuterNorm H = svInnerNorm (svLowerAdjoint H) ∧
      svInnerNorm H = svOuterNorm (svUpperAdjoint H) ∧
      svInnerNorm H = svOuterNorm (svLowerAdjoint H) := by
  have hl := svOuterNorm_eq_svInnerNorm_lowerAdjoint hh ho
  have hi := svOuterNorm_eq_svInnerNorm_lowerAdjoint (svUpperAdjoint_properties H).2
    (svUpperAdjoint_properties H).1
  rw [svLowerAdjoint_svUpperAdjoint hh ho] at hi
  exact ⟨hl.trans (svAdjoint_norms_eq H).2,hl,hi.symm,hi.symm.trans (svAdjoint_norms_eq H).1.symm⟩

end RW
