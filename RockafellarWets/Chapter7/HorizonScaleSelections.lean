/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Positive scalings in the outer horizon limit
-/

import RockafellarWets.Chapter4.TotalLinearImages

open Filter Function Set Topology

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The outer horizon limit always contains zero. All its other members
are genuine limits of points taken from a subsequence of the sets and
multiplied by positive scalars tending to zero. -/
theorem mem_horizonOuterSetLimit_iff_zero_or_scaling {C : ℕ → Set E} {w : E} :
    w ∈ horizonOuterSetLimit C ↔ w = 0 ∨
      ∃ (φ : ℕ → ℕ) (z : ℕ → E) (s : ℕ → ℝ), StrictMono φ ∧
        (∀ n, z n ∈ C (φ n)) ∧ (∀ n, 0 < s n) ∧ Tendsto s atTop (𝓝 0) ∧
        Tendsto (fun n ↦ s n • z n) atTop (𝓝 w) := by
  constructor
  · rintro (hw | ⟨u, hu, r, hr, rfl⟩)
    · exact Or.inl hw
    · obtain ⟨φ, z, hφ, hz, hzu⟩ :=
        mem_horizonOuterSetLimit_iff_exists_cosmicDirection_subsequence.mp
          (cosmicDirection_mem_outer_ordinaryCosmicSequence_iff.mp hu)
      obtain ⟨s, hs, hs0, hst⟩ := exists_scaling_of_tendsto_cosmicDirection hzu
      refine Or.inr ⟨φ, z, fun n ↦ r * s n, hφ, hz, fun n ↦ mul_pos hr (hs n), ?_, ?_⟩
      · simpa only [mul_zero] using hs0.const_mul r
      · simpa only [mul_smul] using hst.const_smul r
  · rintro (rfl | ⟨φ, z, s, hφ, hz, hs, hs0, hst⟩)
    · exact (isCone_horizonOuterSetLimit C).1
    · by_cases hw : w = 0
      · simpa only [hw] using (isCone_horizonOuterSetLimit C).1
      let u := cosmicDirectionOf w hw
      have hu : (u : E) ∈ horizonOuterSetLimit C := by
        apply mem_horizonOuterSetLimit_iff_exists_cosmicDirection_subsequence.mpr
        refine ⟨φ, z, hφ, hz, tendsto_cosmicDirection_of_scaling (scale := fun n ↦ ‖w‖⁻¹ * s n)
          (fun n ↦ mul_pos (inv_pos.mpr (norm_pos_iff.mpr hw)) (hs n)) ?_ ?_⟩
        · simpa only [mul_zero] using hs0.const_mul ‖w‖⁻¹
        · simpa only [u, coe_cosmicDirectionOf, NormedSpace.normalize, mul_smul] using
            hst.const_smul ‖w‖⁻¹
      simpa only [u, coe_cosmicDirectionOf, NormedSpace.norm_smul_normalize] using
        (isCone_horizonOuterSetLimit C).smul_mem hu (norm_nonneg w)

/-- Any sequence can be scaled to zero by strictly positive factors tending
to zero, even when its norms grow arbitrarily fast. -/
theorem exists_positive_scale_to_zero (z : ℕ → E) :
    ∃ s : ℕ → ℝ, (∀ n, 0 < s n) ∧ Tendsto s atTop (𝓝 0) ∧
      Tendsto (fun n ↦ s n • z n) atTop (𝓝 0) := by
  let t := fun n : ℕ ↦ 1 / ((n : ℝ) + 1)
  have ht (n : ℕ) : 0 < t n := by dsimp [t]; positivity
  let s := fun n ↦ t n / (‖z n‖ + 1)
  have hs (n : ℕ) : 0 < s n := div_pos (ht n) (by positivity)
  refine ⟨s, hs, squeeze_zero (fun n ↦ (hs n).le) (fun n ↦ ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
  · exact div_le_self (ht n).le (by linarith [norm_nonneg (z n)])
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    rw [norm_smul_of_nonneg (hs n).le]
    change t n / (‖z n‖ + 1) * ‖z n‖ ≤ t n
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [ht n]

end RW
