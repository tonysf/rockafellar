/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Scaled sequences for horizon subgradients
-/

import RockafellarWets.Chapter8.SubderivativeFormulas
import RockafellarWets.Chapter5.ConvergingImages
import RockafellarWets.Chapter5.SequentialLimits

open Filter Set Topology

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The nonzero vectors in a horizon outer limit are exactly limits of
positive, vanishing rescalings of points in the moving sets. -/
theorem mem_horizonOuterSetLimitAlong_iff_zero_or_scaledSeq {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {S : ι → Set E} {v : E} :
    v ∈ horizonOuterSetLimitAlong l S ↔ v = 0 ∨
      ∃ (i : ℕ → ι) (w : ℕ → E) (t : ℕ → ℝ), Tendsto i atTop l ∧
        (∀ n, w n ∈ S (i n)) ∧ (∀ n, 0 < t n) ∧ Tendsto t atTop (𝓝 0) ∧
        Tendsto (fun n ↦ t n • w n) atTop (𝓝 v) := by
  constructor
  · rintro (rfl | ⟨u, hu, a, ha, rfl⟩)
    · exact Or.inl rfl
    obtain ⟨i, p, hi, hp, hpu⟩ := mem_outerSetLimitAlong_iff_exists_seq.mp hu
    have hw (n : ℕ) : ∃ w ∈ S (i n), cosmicEmbed w = p n := by
      rcases mem_cosmicSet.mp (hp n) with h | ⟨b, hb, _⟩
      · exact h
      · have hb0 : (b : E) = 0 := hb
        have hb1 := mem_sphere_zero_iff_norm.mp b.property
        simp [hb0] at hb1
    choose w hw hwp using hw
    have h := exists_scaling_of_tendsto_cosmicDirection
      (show Tendsto (fun n ↦ cosmicEmbed (w n)) atTop (𝓝 (cosmicDirection u)) by
        simpa only [hwp] using hpu)
    obtain ⟨t, ht, hzero, hlim⟩ := h
    exact Or.inr ⟨i, w, fun n ↦ a * t n, hi, hw, fun n ↦ mul_pos ha (ht n),
      by simpa using hzero.const_mul a, by simpa [mul_smul] using hlim.const_smul a⟩
  · rintro (rfl | ⟨i, w, t, hi, hw, ht, hzero, hlim⟩)
    · exact (isCone_horizonOuterSetLimitAlong l S).1
    have h := mem_horizonOuterSetLimit_of_seq_smul (C := S ∘ i) (φ := id)
      strictMono_id hw ht hzero hlim
    exact cosmicDirectionCone_mono
      (outerSetLimit_comp_subset (C := ordinaryCosmicFamily S) hi) h

/-- **Definition 8.3(c)**, scaled regular subgradient formula. -/
theorem mem_horizonSubdifferential_iff_zero_or_scaledSeq {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {f : F → EReal} {x v : F} {c : ℝ} (hx : f x = c) :
    v ∈ horizonSubdifferential f x ↔ v = 0 ∨
      ∃ (y w : ℕ → F) (t : ℕ → ℝ), Tendsto y atTop (attentiveNhds f x) ∧
        (∀ n, w n ∈ regularSubdifferential f (y n)) ∧ (∀ n, 0 < t n) ∧
        Tendsto t atTop (𝓝 0) ∧ Tendsto (fun n ↦ t n • w n) atTop (𝓝 v) := by
  rw [horizonSubdifferential_of_finite hx, mem_horizonOuterSetLimitAlong_iff_zero_or_scaledSeq]

end RW
