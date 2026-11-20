/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: elementary rules for outer and inner norms

The rules listed after 9(5), for `|·|⁺ = svOuterNorm` and `|·|⁻ = svInnerNorm`
with values in `[0, ∞]` and the convention `0 · ∞ = 0`:

* `|λH|⁺ = |λ| |H|⁺` (`svOuterNorm_smul`), for every `λ`;
* `|H₁ + H₂|⁺ ≤ |H₁|⁺ + |H₂|⁺` (`svOuterNorm_svAdd_le`);
* `|H₂ ∘ H₁|⁺ ≤ |H₂|⁺ |H₁|⁺` for positively homogeneous `H₂`, provided the
  right side is not the product `∞ · 0` (`svOuterNorm_svComp_le`).  Without that
  proviso the rule fails: `svOuterNorm_svComp_counterexample` has `H₁ ≡ {0}` and
  `H₂ ≡ ℝ`, so that `|H₁|⁺ = 0`, `|H₂|⁺ = ∞` and `|H₂ ∘ H₁|⁺ = ∞`;
* `|λH|⁻ = |λ| |H|⁻` for `λ ≠ 0` (`svInnerNorm_smul`); for `λ = 0` it fails when
  `H` has empty values (`svInnerNorm_zero_smul_counterexample`).

The remaining inner-norm sum and composition rules are proved in
`InnerNormRules`. Its composition rule excludes both indeterminate products;
formal counterexamples show the need for each exclusion.
-/

import RockafellarWets.Chapter9.HomogeneousMappingNorms
import RockafellarWets.Chapter5.PerturbedMappings
import RockafellarWets.Chapter5.MappingOperations

open Filter Set Topology Metric
open scoped ENNReal NNReal Pointwise

namespace RW

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

omit [NormedSpace ℝ F] in
private theorem coe_nnnorm_eq_ofReal (z : F) : (‖z‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖z‖ := by
  rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]

omit [NormedSpace ℝ E] in
/-- The rule `|λH|⁺ = |λ| |H|⁺`. -/
theorem svOuterNorm_smul (c : ℝ) (H : E → Set F) :
    svOuterNorm (fun w ↦ c • H w) = ‖c‖₊ * svOuterNorm H := by
  refine le_antisymm (svOuterNorm_le_iff_ball.2 fun w hw z hz ↦ ?_) ?_
  · obtain ⟨z₀, hz₀, rfl⟩ := hz
    rw [nnnorm_smul, ENNReal.coe_mul]
    exact mul_le_mul_right (coe_nnnorm_le_svOuterNorm hw hz₀) _
  · rcases eq_or_ne c 0 with rfl | hc
    · simp
    · have hc0 : (‖c‖₊ : ℝ≥0∞) ≠ 0 := by simpa using hc
      rw [ENNReal.mul_le_iff_le_inv hc0 ENNReal.coe_ne_top]
      refine svOuterNorm_le_iff_ball.2 fun w hw z hz ↦ ?_
      have h1 := coe_nnnorm_le_svOuterNorm (H := fun w ↦ c • H w) hw (smul_mem_smul_set hz)
      rw [nnnorm_smul, ENNReal.coe_mul] at h1
      exact (ENNReal.mul_le_iff_le_inv hc0 ENNReal.coe_ne_top).1 h1

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- The rule `|H₁ + H₂|⁺ ≤ |H₁|⁺ + |H₂|⁺`. -/
theorem svOuterNorm_svAdd_le (H₁ H₂ : E → Set F) :
    svOuterNorm (svAdd H₁ H₂) ≤ svOuterNorm H₁ + svOuterNorm H₂ := by
  refine svOuterNorm_le_iff_ball.2 fun w hw z hz ↦ ?_
  have hz' : z ∈ H₁ w + H₂ w := hz
  obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := Set.mem_add.1 hz'
  calc (‖z₁ + z₂‖₊ : ℝ≥0∞) ≤ ‖z₁‖₊ + ‖z₂‖₊ := by exact_mod_cast nnnorm_add_le z₁ z₂
    _ ≤ svOuterNorm H₁ + svOuterNorm H₂ :=
      add_le_add (coe_nnnorm_le_svOuterNorm hw hz₁) (coe_nnnorm_le_svOuterNorm hw hz₂)

omit [NormedSpace ℝ E] in
/-- The rule `|H₂ ∘ H₁|⁺ ≤ |H₂|⁺ |H₁|⁺` for positively homogeneous `H₂`, outside the
case where the right side is the product `∞ · 0`. -/
theorem svOuterNorm_svComp_le {H₁ : E → Set F} {H₂ : F → Set G}
    (h₂ : SvPositivelyHomogeneous H₂) (h : svOuterNorm H₂ ≠ ⊤ ∨ svOuterNorm H₁ ≠ 0) :
    svOuterNorm (svComp H₂ H₁) ≤ svOuterNorm H₂ * svOuterNorm H₁ := by
  rcases eq_or_ne (svOuterNorm H₂) ⊤ with htop | hfin
  · have h1 : svOuterNorm H₁ ≠ 0 := h.resolve_left (not_not.2 htop)
    rw [htop, ENNReal.top_mul h1]
    exact le_top
  · refine svOuterNorm_le_iff_ball.2 fun w hw z hz ↦ ?_
    have hz' : z ∈ svImage H₂ (H₁ w) := hz
    obtain ⟨z₁, hz₁, hz₂⟩ := mem_svImage.1 hz'
    have h1 := h₂.norm_le_svOuterNorm_mul hfin hz₂
    calc (‖z‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖z‖ := coe_nnnorm_eq_ofReal z
      _ ≤ ENNReal.ofReal ((svOuterNorm H₂).toReal * ‖z₁‖) := ENNReal.ofReal_le_ofReal h1
      _ = svOuterNorm H₂ * ‖z₁‖₊ := by
          rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin,
            ← coe_nnnorm_eq_ofReal]
      _ ≤ svOuterNorm H₂ * svOuterNorm H₁ :=
          mul_le_mul_right (coe_nnnorm_le_svOuterNorm hw hz₁) _

/-- With `0 · ∞ = 0` the printed rule `|H₂ ∘ H₁|⁺ ≤ |H₂|⁺ |H₁|⁺` fails: `H₁ ≡ {0}`
and `H₂ ≡ ℝ` on `ℝ` are positively homogeneous, `|H₁|⁺ = 0`, `|H₂|⁺ = ∞`, and
`H₂ ∘ H₁ ≡ ℝ` has `|H₂ ∘ H₁|⁺ = ∞`. -/
theorem svOuterNorm_svComp_counterexample :
    SvPositivelyHomogeneous (fun _ : ℝ ↦ ({0} : Set ℝ)) ∧
      SvPositivelyHomogeneous (fun _ : ℝ ↦ (univ : Set ℝ)) ∧
      svOuterNorm (fun _ : ℝ ↦ ({0} : Set ℝ)) = 0 ∧
      svOuterNorm (fun _ : ℝ ↦ (univ : Set ℝ)) = ⊤ ∧
      svOuterNorm (svComp (fun _ : ℝ ↦ (univ : Set ℝ)) (fun _ : ℝ ↦ ({0} : Set ℝ))) = ⊤ := by
  have htop : svOuterNorm (fun _ : ℝ ↦ (univ : Set ℝ)) = ⊤ := by
    refine ENNReal.eq_top_of_forall_nnreal_le fun r ↦ ?_
    have h1 := coe_nnnorm_le_svOuterNorm (H := fun _ : ℝ ↦ (univ : Set ℝ)) (w := 0)
      (by simp) (mem_univ (r : ℝ))
    refine le_trans (ENNReal.coe_le_coe.2 ?_) h1
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    simp
  have hcomp : svComp (fun _ : ℝ ↦ (univ : Set ℝ)) (fun _ : ℝ ↦ ({0} : Set ℝ)) =
      fun _ ↦ (univ : Set ℝ) := by
    funext w
    ext z
    simp only [svComp, mem_univ, iff_true]
    exact mem_svImage.2 ⟨0, mem_singleton 0, mem_univ z⟩
  refine ⟨⟨mem_singleton 0, fun w c _ ↦ by simp⟩, ⟨mem_univ 0, fun w c hc ↦ ?_⟩, ?_, htop, ?_⟩
  · exact (Set.smul_set_univ₀ hc.ne').symm
  · refine le_antisymm (svOuterNorm_le_iff_ball.2 fun w _ z hz ↦ ?_) (zero_le _)
    rw [mem_singleton_iff.1 hz]
    simp
  · rw [hcomp]
    exact htop

omit [NormedSpace ℝ E] in
/-- The rule `|λH|⁻ = |λ| |H|⁻` for `λ ≠ 0`. -/
theorem svInnerNorm_smul {c : ℝ} (hc : c ≠ 0) (H : E → Set F) :
    svInnerNorm (fun w ↦ c • H w) = ‖c‖₊ * svInnerNorm H := by
  have h0 : (‖c‖₊ : ℝ≥0∞) ≠ 0 := by simpa using hc
  have hpt : ∀ w, ⨅ z ∈ c • H w, (‖z‖₊ : ℝ≥0∞) = ‖c‖₊ * ⨅ z ∈ H w, (‖z‖₊ : ℝ≥0∞) := by
    intro w
    rw [← Set.image_smul, iInf_image, ENNReal.mul_iInf_of_ne h0 ENNReal.coe_ne_top]
    refine iInf_congr fun z ↦ ?_
    rw [ENNReal.mul_iInf_of_ne h0 ENNReal.coe_ne_top]
    refine iInf_congr fun _ ↦ ?_
    rw [nnnorm_smul, ENNReal.coe_mul]
  simp only [svInnerNorm, hpt, ENNReal.mul_iSup]

/-- For `λ = 0` the rule `|λH|⁻ = |λ| |H|⁻` fails: with `gph H = {(0, 0)}` on `ℝ`,
`0 · H = H`, so `|0 · H|⁻ = ∞` while `0 · |H|⁻ = 0`. -/
theorem svInnerNorm_zero_smul_counterexample :
    svInnerNorm (fun w : ℝ ↦ (0 : ℝ) • (if w = 0 then ({0} : Set ℝ) else ∅)) = ⊤ ∧
      (‖(0 : ℝ)‖₊ : ℝ≥0∞) * svInnerNorm (fun w : ℝ ↦ if w = 0 then ({0} : Set ℝ) else ∅) = 0 := by
  have h1 : (fun w : ℝ ↦ (0 : ℝ) • (if w = 0 then ({0} : Set ℝ) else ∅)) =
      fun w : ℝ ↦ if w = 0 then ({0} : Set ℝ) else ∅ := by
    funext w
    split_ifs <;> simp
  refine ⟨?_, by simp⟩
  rw [h1]
  exact svOuterNorm_lt_svInnerNorm_example.2.2

end RW
