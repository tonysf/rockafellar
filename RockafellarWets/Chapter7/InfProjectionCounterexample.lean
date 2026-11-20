/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A nondecreasing counterexample to inf-projection in Exercise 7.57
-/

import RockafellarWets.Chapter7.TotalEpiProjection
import RockafellarWets.Chapter7.EpiLimitCharacterization

open Filter Set Topology

namespace RW

/-- A fixed point of value zero and a closed half-line of value minus one
which recedes to minus infinity. The parameter plays no role. -/
private noncomputable def escapingValley (n : ℕ) (p : ℝ × ℝ) : EReal :=
  if p.1 = 0 then 0 else if p.1 ≤ -(n : ℝ) - 1 then -1 else ⊤

private theorem escapingValley_lsc (n : ℕ) : LowerSemicontinuous (escapingValley n) := by
  apply lowerSemicontinuous_of_isClosed_epigraph_ereal
  have he : epigraph (escapingValley n) =
      {p : (ℝ × ℝ) × ℝ | p.1.1 = 0 ∧ 0 ≤ p.2} ∪
      {p : (ℝ × ℝ) × ℝ | p.1.1 ≤ -(n : ℝ) - 1 ∧ -1 ≤ p.2} := by
    ext ⟨⟨x, u⟩, a⟩
    by_cases hx : x = 0
    · subst x
      have hcut : ¬ (0 : ℝ) ≤ -(n : ℝ) - 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
      simp [mem_epigraph_iff, escapingValley, hcut]
    · by_cases h : x ≤ -(n : ℝ) - 1 <;>
        simp [mem_epigraph_iff, escapingValley, hx, h, ← EReal.coe_one, ← EReal.coe_neg]
  rw [he]
  exact ((isClosed_eq continuous_fst.fst continuous_const).inter
    (isClosed_le continuous_const continuous_snd)).union
    ((isClosed_le continuous_fst.fst continuous_const).inter (isClosed_le continuous_const continuous_snd))

/-- **Exercise 7.57**, obstruction to the printed nondecreasing alternative.
All functions are proper and lsc, the limiting horizontal horizon condition
holds, and the inf-projections nevertheless fail to epi-converge. -/
theorem valueFunction_monotone_epiConvergence_counterexample :
    ∃ (f : ℕ → ℝ × ℝ → EReal) (g : ℝ × ℝ → EReal),
      (∀ n, IsProper (f n) ∧ LowerSemicontinuous (f n)) ∧ IsProper g ∧ LowerSemicontinuous g ∧
      Monotone f ∧ EpiConverges f g ∧ (∀ x : ℝ, x ≠ 0 → 0 < horizonFunction g (x, 0)) ∧
      ¬ EpiConverges (fun n ↦ valueFunction (f n)) (valueFunction g) := by
  let C := {p : ℝ × ℝ | p.1 = 0}
  let g := indicatorVA C
  have hC : IsClosed C := isClosed_eq continuous_fst continuous_const
  have hcone : IsCone C := ⟨rfl, fun {x} hx r _ ↦ by
    change r * x.1 = 0
    rw [show x.1 = 0 from hx, mul_zero]⟩
  have hg : LowerSemicontinuous g := lowerSemicontinuous_indicatorVA hC
  have hm : Monotone escapingValley := by
    intro i j hij p
    have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
    by_cases hz : p.1 = 0
    · simp [escapingValley, hz]
    by_cases hj : p.1 ≤ -(j : ℝ) - 1
    · have hi : p.1 ≤ -(i : ℝ) - 1 := by linarith
      simp [escapingValley, hz, hj, hi]
    · simp [escapingValley, hz, hj]
  have he : (fun p ↦ ⨆ n, epiClosure (escapingValley n) p) = g := by
    funext p
    simp only [epiClosure_eq_of_lowerSemicontinuous (escapingValley_lsc _)]
    by_cases hz : p.1 = 0
    · simp [escapingValley, C, g, hz]
    · obtain ⟨n, hn⟩ := exists_nat_gt (-p.1)
      have h : ¬ p.1 ≤ -(n : ℝ) - 1 := by linarith
      have htop : escapingValley n p = ⊤ := by simp [escapingValley, hz, h]
      simpa [g, C, indicatorVA, hz] using (top_unique (htop ▸ le_iSup (fun k ↦ escapingValley k p) n))
  refine ⟨escapingValley, g, ?_, (indicatorVA_isProper_iff C).mpr ⟨(0, 0), rfl⟩,
    hg, hm, he ▸ epiConverges_of_monotone hm, ?_, ?_⟩
  · intro n
    refine ⟨⟨⟨(0, 0), by simp [escapingValley]⟩, fun p ↦ ?_⟩, escapingValley_lsc n⟩
    simp only [escapingValley]
    split_ifs <;> norm_num
    simpa only [EReal.coe_neg, EReal.coe_one] using EReal.bot_lt_coe (-1)
  · intro x hx
    rw [horizonFunction_eq_self_of_lowerSemicontinuous_of_positivelyHomogeneous hg
      (positivelyHomogeneous_indicatorVA_iff.mpr hcone)]
    simp [g, C, hx]
  · intro hc
    have hf (n : ℕ) (u : ℝ) : valueFunction (escapingValley n) u = -1 := by
      have hn : -(n : ℝ) - 1 ≠ 0 := by linarith [Nat.cast_nonneg (α := ℝ) n]
      apply le_antisymm
      · exact iInf_le_of_le (-(n : ℝ) - 1) (by simp [escapingValley, hn])
      · refine le_iInf fun x ↦ ?_
        simp only [escapingValley]
        split_ifs <;> norm_num
    have hgv : valueFunction g 0 = 0 := by
      apply le_antisymm
      · exact iInf_le_of_le (0 : ℝ) (by simp [g, C])
      · exact le_iInf fun x ↦ by
          by_cases hx : x = 0 <;> simp [g, C, hx]
    have h := ((epiConverges_iff_liminf_limsup.mp hc) 0).1 (fun _ ↦ 0) tendsto_const_nhds
    simp only [hgv, hf, liminf_const] at h
    have hfals := EReal.coe_le_coe_iff.mp (show ((0 : ℝ) : EReal) ≤ ((-1 : ℝ) : EReal) from
      by simpa only [EReal.coe_zero, EReal.coe_neg, EReal.coe_one] using h)
    linarith

end RW
