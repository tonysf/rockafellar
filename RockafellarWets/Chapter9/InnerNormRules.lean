/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Sum and composition rules for inner norms

The composition bound requires excluding both indeterminate products with
zero and infinity. Empty fibers make this necessary even when the second
mapping has zero inner norm.
-/

import RockafellarWets.Chapter9.OuterNormRules
import Mathlib.Algebra.Order.Field.Pointwise

open Set Metric
open scoped NNReal ENNReal Pointwise

namespace RW

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The inner norm bounds the distance of every fiber from zero. -/
theorem SvPositivelyHomogeneous.iInf_nnnorm_le_svInnerNorm_mul
    {H : E → Set F} (h : SvPositivelyHomogeneous H) (w : E) :
    (⨅ z ∈ H w, (‖z‖₊ : ℝ≥0∞)) ≤ svInnerNorm H * ‖w‖₊ := by
  by_cases hw : w = 0
  · subst w
    simp only [nnnorm_zero,ENNReal.coe_zero,mul_zero]
    exact iInf₂_le_of_le (0:F) h.1 (by simp)
  have hwpos := norm_pos_iff.mpr hw
  have he : H w = ‖w‖ • H (‖w‖⁻¹ • w) := by
    simpa only [smul_smul,mul_inv_cancel₀ hwpos.ne',one_smul] using
      h.2 (‖w‖⁻¹ • w) ‖w‖ hwpos
  have hn : ‖‖w‖⁻¹ • w‖ ≤ 1 := by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hwpos.le),inv_mul_cancel₀ hwpos.ne']
  have hle : (⨅ z ∈ H (‖w‖⁻¹ • w), (‖z‖₊ : ℝ≥0∞)) ≤ svInnerNorm H :=
    le_iSup₂_of_le (‖w‖⁻¹ • w) (mem_closedBall_zero_iff.mpr hn) le_rfl
  have h0 : (‖(‖w‖:ℝ)‖₊ : ℝ≥0∞) ≠ 0 := by simpa using hw
  calc
    (⨅ z ∈ H w, (‖z‖₊ : ℝ≥0∞)) =
        (‖(‖w‖:ℝ)‖₊ : ℝ≥0∞) * ⨅ z ∈ H (‖w‖⁻¹ • w), (‖z‖₊ : ℝ≥0∞) := by
      rw [he,← Set.image_smul,iInf_image]
      simp only [nnnorm_smul,ENNReal.coe_mul,
        ENNReal.mul_iInf_of_ne h0 ENNReal.coe_ne_top]
    _ ≤ (‖(‖w‖:ℝ)‖₊ : ℝ≥0∞) * svInnerNorm H := mul_le_mul_right hle _
    _ = svInnerNorm H * ‖w‖₊ := by simp [mul_comm]

/-- The inner norm sum bound, including empty fibers and infinite norms. -/
theorem svInnerNorm_svAdd_le (H₁ H₂ : E → Set F) :
    svInnerNorm (svAdd H₁ H₂) ≤ svInnerNorm H₁ + svInnerNorm H₂ := by
  apply iSup₂_le
  intro w hw
  have hpt : (⨅ z ∈ svAdd H₁ H₂ w, (‖z‖₊ : ℝ≥0∞)) ≤
      (⨅ z ∈ H₁ w, (‖z‖₊ : ℝ≥0∞)) + ⨅ z ∈ H₂ w, (‖z‖₊ : ℝ≥0∞) := by
    simp only [ENNReal.iInf_add,ENNReal.add_iInf]
    refine le_iInf₂ fun a ha ↦ le_iInf₂ fun b hb ↦ ?_
    apply iInf₂_le_of_le (b+a) (Set.mem_add.mpr ⟨b,hb,a,ha,rfl⟩)
    exact_mod_cast nnnorm_add_le b a
  exact hpt.trans (add_le_add (le_iSup₂_of_le w hw le_rfl) (le_iSup₂_of_le w hw le_rfl))

/-- The inner norm composition rule outside the indeterminate products.
Only the second mapping needs positive homogeneity. -/
theorem svInnerNorm_svComp_le {H₁ : E → Set F} {H₂ : F → Set G}
    (h₂ : SvPositivelyHomogeneous H₂)
    (hleft : svInnerNorm H₂ ≠ ⊤ ∨ svInnerNorm H₁ ≠ 0)
    (hright : svInnerNorm H₂ ≠ 0 ∨ svInnerNorm H₁ ≠ ⊤) :
    svInnerNorm (svComp H₂ H₁) ≤ svInnerNorm H₂ * svInnerNorm H₁ := by
  by_cases htop : svInnerNorm H₂ = ⊤
  · rw [htop,ENNReal.top_mul (hleft.resolve_left (not_not.mpr htop))]
    exact le_top
  have hpt (w : E) (v : F) (hv : v ∈ H₁ w) :
      (⨅ z ∈ svComp H₂ H₁ w, (‖z‖₊ : ℝ≥0∞)) ≤ svInnerNorm H₂ * ‖v‖₊ := by
    apply le_trans _ (h₂.iInf_nnnorm_le_svInnerNorm_mul v)
    exact le_iInf₂ fun z hz ↦ iInf₂_le_of_le z (mem_svImage.mpr ⟨v,hv,hz⟩) le_rfl
  apply iSup₂_le
  intro w hw
  have hle : (⨅ v ∈ H₁ w, (‖v‖₊ : ℝ≥0∞)) ≤ svInnerNorm H₁ :=
    le_iSup₂_of_le w hw le_rfl
  by_cases hzero : svInnerNorm H₂ = 0
  · have hfin := hright.resolve_left (not_not.mpr hzero)
    have hne : (H₁ w).Nonempty := by
      by_contra hn
      have hem := Set.not_nonempty_iff_eq_empty.mp hn
      simp only [hem,Set.mem_empty_iff_false,iInf_of_empty,iInf_const] at hle
      exact hfin (top_le_iff.mp hle)
    obtain ⟨v,hv⟩ := hne
    simpa only [hzero,zero_mul] using hpt w v hv
  calc
    _ ≤ ⨅ v ∈ H₁ w, svInnerNorm H₂ * (‖v‖₊ : ℝ≥0∞) := le_iInf₂ (hpt w)
    _ = svInnerNorm H₂ * ⨅ v ∈ H₁ w, (‖v‖₊ : ℝ≥0∞) := by
      simp only [ENNReal.mul_iInf_of_ne hzero htop]
    _ ≤ _ := mul_le_mul_right hle _

/-- Scalar multiplication includes the zero scalar when the relevant fibers
are nonempty. This is the complementary case to `svInnerNorm_smul`. -/
theorem svInnerNorm_smul_of_nonempty (c : ℝ) (H : E → Set F)
    (hne : ∀ w ∈ closedBall (0:E) 1, (H w).Nonempty) :
    svInnerNorm (fun w ↦ c • H w) = ‖c‖₊ * svInnerNorm H := by
  by_cases hc : c = 0
  · subst c
    simp only [nnnorm_zero,ENNReal.coe_zero,zero_mul]
    apply le_antisymm _ bot_le
    apply iSup₂_le
    intro w hw
    obtain ⟨z,hz⟩ := hne w hw
    have hm : (0:F) ∈ (0:ℝ) • H w := ⟨z,hz,zero_smul ℝ z⟩
    exact iInf₂_le_of_le (0:F) hm (by simp)
  · exact svInnerNorm_smul hc H

/-! Both excluded indeterminate products can fail for homogeneous mappings. -/

/-- Zero inner norm does not repair empty fibers in the first mapping. -/
theorem svInnerNorm_svComp_zero_top_counterexample :
    ∃ H₁ H₂ : ℝ → Set ℝ, SvPositivelyHomogeneous H₁ ∧ SvPositivelyHomogeneous H₂ ∧
      svInnerNorm H₁ = ⊤ ∧ svInnerNorm H₂ = 0 ∧ svInnerNorm (svComp H₂ H₁) = ⊤ := by
  let H₁ : ℝ → Set ℝ := fun w ↦ if w = 0 then {0} else ∅
  let H₂ : ℝ → Set ℝ := fun _ ↦ {0}
  have hh₂ : SvPositivelyHomogeneous H₂ := ⟨by simp [H₂],fun w c hc ↦ by simp [H₂]⟩
  have hzero : svInnerNorm H₂ = 0 := by simp [svInnerNorm,H₂]
  have he : svComp H₂ H₁ = H₁ := by
    funext w
    ext z
    rw [svComp,mem_svImage]
    by_cases hw : w = 0 <;> simp [H₁,H₂,hw]
  exact ⟨H₁,H₂,svOuterNorm_lt_svInnerNorm_example.1,hh₂,
    svOuterNorm_lt_svInnerNorm_example.2.2,hzero,by rw [he]; exact svOuterNorm_lt_svInnerNorm_example.2.2⟩

/-- Positive open fibers can approach zero without meeting the domain of the
second mapping. This refutes the other indeterminate product. -/
theorem svInnerNorm_svComp_top_zero_counterexample :
    ∃ H₁ H₂ : ℝ → Set ℝ, SvPositivelyHomogeneous H₁ ∧ SvPositivelyHomogeneous H₂ ∧
      svInnerNorm H₁ = 0 ∧ svInnerNorm H₂ = ⊤ ∧ svInnerNorm (svComp H₂ H₁) = ⊤ := by
  let H₁ : ℝ → Set ℝ := fun w ↦ if w = 0 then {0} else Ioi 0
  let H₂ : ℝ → Set ℝ := fun w ↦ if w = 0 then {0} else ∅
  have hh₁ : SvPositivelyHomogeneous H₁ := by
    refine ⟨by simp [H₁],fun w c hc ↦ ?_⟩
    by_cases hw : w = 0
    · simp [H₁,hw]
    · simp [H₁,hw,hc.ne',LinearOrderedField.smul_Ioi hc]
  have hzero : svInnerNorm H₁ = 0 := by
    apply le_antisymm _ bot_le
    apply iSup₂_le
    intro w hw
    by_cases hw0 : w = 0
    · simp [H₁,hw0]
    · apply ENNReal.le_of_forall_pos_le_add
      intro ε hε _
      simp only [H₁,hw0,ite_false,zero_add]
      exact iInf₂_le_of_le (ε:ℝ) (show 0 < (ε:ℝ) from hε) (by simp)
  have he : svComp H₂ H₁ = H₂ := by
    funext w
    ext z
    rw [svComp,mem_svImage]
    by_cases hw : w = 0
    · simp [H₁,H₂,hw]
    · simp only [H₁,H₂,hw,ite_false,mem_Ioi,mem_empty_iff_false,iff_false]
      rintro ⟨v,hv,hz⟩
      simpa only [if_neg hv.ne',mem_empty_iff_false] using hz
  exact ⟨H₁,H₂,hh₁,svOuterNorm_lt_svInnerNorm_example.1,hzero,
    svOuterNorm_lt_svInnerNorm_example.2.2,by rw [he]; exact svOuterNorm_lt_svInnerNorm_example.2.2⟩

end RW
