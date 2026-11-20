/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Attainment in the auxiliary epi-distance
-/

import RockafellarWets.Chapter1.Semicontinuity
import RockafellarWets.Chapter7.AuxEpiDistance

open Filter Metric Set Topology
open scoped NNReal

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

/-- At the exact auxiliary distance one can choose comparison points in
the closed ball of that radius, in both directions. -/
theorem auxEpiAdmissible_at_distance {r : ℝ≥0} {f g : E → EReal}
    (hf : LowerSemicontinuous f) (hg : LowerSemicontinuous g)
    (hnf : (effectiveDomain f).Nonempty) (hng : (effectiveDomain g).Nonempty) :
    auxEpiAdmissible r f g (auxEpiDistance r f g) := by
  let d := auxEpiDistance r f g
  have hd : 0 ≤ d := auxEpiDistance_nonneg hnf hng
  let e (n : ℕ) : ℝ := d + 1 / (n + 1 : ℝ)
  have hed (n : ℕ) : d < e n := lt_add_of_pos_right _ (by positivity)
  have he : Tendsto e atTop (𝓝 d) := by
    simpa [e] using tendsto_const_nhds (x := d) |>.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hh (n : ℕ) := auxEpiAdmissible_of_lt hnf hng (hed n)
  have hdir {u v : E → EReal} (hv : LowerSemicontinuous v)
      (hall : ∀ n, auxEpiComparison r u v (e n)) : auxEpiComparison r u v d := by
    intro x hx
    let α := max (u x) ((-(r : ℝ) : ℝ) : EReal)
    by_cases hα : α = ⊤
    · refine ⟨x, by simpa using hd, ?_⟩
      change v x ≤ α + (d : EReal)
      simp [hα]
    have hαb : α ≠ ⊥ := ((EReal.bot_lt_coe _).trans_le (le_max_right _ _)).ne'
    let a := α.toReal
    have ha : (a : EReal) = α := EReal.coe_toReal hα hαb
    choose y hy hval using fun n ↦ hall n x hx
    have hball (n : ℕ) : y n ∈ closedBall x (d+1) := by
      rw [mem_closedBall, dist_comm]
      apply (hy n).trans
      exact add_le_add_right ((div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n] : 1 ≤ (n:ℝ)+1)) d
    obtain ⟨z, _, φ, hφ, hz⟩ := (isCompact_closedBall x (d+1)).isSeqCompact hball
    have hd' : dist x z ≤ d := le_of_tendsto_of_tendsto'
      (tendsto_const_nhds.dist hz) (he.comp hφ.tendsto_atTop) (fun n ↦ hy (φ n))
    have hseq : ∀ n, (y (φ n), a + e (φ n)) ∈ epigraph v := by
      intro n
      change v _ ≤ ((a + e (φ n) : ℝ) : EReal)
      rw [EReal.coe_add, ha]
      exact hval _
    have hlim := (isClosed_epigraph_of_lsc_ereal v hv).mem_of_tendsto
      (hz.prodMk_nhds (tendsto_const_nhds.add (he.comp hφ.tendsto_atTop))) (.of_forall hseq)
    refine ⟨z, hd', ?_⟩
    change v z ≤ α + (d : EReal)
    simpa only [mem_epigraph_iff, EReal.coe_add, ha] using hlim
  exact ⟨hd, hdir hg (fun n ↦ (hh n).2.1), hdir hf (fun n ↦ (hh n).2.2)⟩

end RW
