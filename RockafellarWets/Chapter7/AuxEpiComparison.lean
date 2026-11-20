/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Comparing the auxiliary epi-distance with truncated epigraph distance
-/

import Mathlib.Analysis.Normed.Lp.ProdLp
import RockafellarWets.Chapter7.AuxEpiDistance
import RockafellarWets.Chapter4.LocalSetDistances

open Metric Set

open scoped NNReal

namespace RW

variable {E : Type*} [NormedAddCommGroup E]

/-- The ordinary epigraph with the Euclidean product norm used for the
book's quantitative estimates. -/
def euclideanEpigraph (f : E → EReal) : Set (WithLp 2 (E × ℝ)) :=
  {p | WithLp.ofLp p ∈ epigraph f}

omit [NormedAddCommGroup E] in
theorem euclideanEpigraph_nonempty {f : E → EReal} (h : (effectiveDomain f).Nonempty) :
    (euclideanEpigraph f).Nonempty := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨a, ha, _⟩ := EReal.exists_between_coe_real (show f x < ⊤ from hx)
  exact ⟨WithLp.toLp 2 (x, a), ha.le⟩

private theorem euclideanEpigraph_subset_cthickening {ρ : ℝ≥0} {η : ℝ} (hη : 0 ≤ η)
    {f g : E → EReal} (hc : auxEpiComparison ρ f g η) :
    euclideanEpigraph f ∩ closedBall 0 (ρ : ℝ) ⊆
      cthickening (Real.sqrt 2 * η) (euclideanEpigraph g) := by
  rintro p ⟨hp, hpρ⟩
  have hp' : ‖p‖ ≤ (ρ : ℝ) := by simpa only [mem_closedBall, dist_zero_right] using hpρ
  have hx : ‖p.fst‖ ≤ ρ := (WithLp.norm_fst_le _ p).trans hp'
  have ha : |p.snd| ≤ ρ := (WithLp.norm_snd_le _ p).trans hp'
  obtain ⟨y, hxy, hgy⟩ := hc p.fst (by simpa only [mem_closedBall, dist_zero_right] using hx)
  let q := WithLp.toLp 2 (y, p.snd + η)
  have hq : q ∈ euclideanEpigraph g := by
    change g y ≤ ((p.snd + η : ℝ) : EReal)
    rw [EReal.coe_add]
    exact hgy.trans (add_le_add_left (max_le hp (EReal.coe_le_coe_iff.mpr (abs_le.mp ha).1)) _)
  apply mem_cthickening_of_dist_le p q _ _ hq
  have hsq := WithLp.prod_norm_sq_eq_of_L2 (p - q)
  change ‖p - q‖ ^ 2 = ‖p.fst - y‖ ^ 2 + ‖p.snd - (p.snd + η)‖ ^ 2 at hsq
  rw [dist_eq_norm] at hxy ⊢
  have h1 := sq_le_sq' (by linarith [norm_nonneg (p.fst-y)]) hxy
  have h2 : ‖p.snd - (p.snd + η)‖ = η := by simp [Real.norm_eq_abs, abs_of_nonneg hη]
  rw [h2] at hsq
  have hroot := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hright : 0 ≤ Real.sqrt 2 * η := mul_nonneg (Real.sqrt_nonneg _) hη
  nlinarith [sq_nonneg (‖p-q‖ + Real.sqrt 2 * η), show (Real.sqrt 2 * η)^2 = 2 * η^2 by rw [mul_pow, hroot]]

/-- **Proposition 7.61**, upper estimate in the Euclidean product norm. -/
theorem rhoHatDistance_euclideanEpigraph_le_aux [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (ρ : ℝ≥0) {f g : E → EReal} (hf : (effectiveDomain f).Nonempty)
    (hg : (effectiveDomain g).Nonempty) :
    rhoHatDistance ρ (euclideanEpigraph f) (euclideanEpigraph g) ≤ Real.sqrt 2 * auxEpiDistance ρ f g := by
  let η := auxEpiDistance ρ f g
  have hc : ContinuousAt (fun e : ℝ ↦ Real.sqrt 2 * e) η := continuousAt_const.mul continuousAt_id
  apply ge_of_tendsto (hc.continuousWithinAt (s := Ioi η))
  apply Filter.mem_of_superset self_mem_nhdsWithin
  intro e he
  have h := auxEpiAdmissible_of_lt hf hg he
  exact (rhoHatDistance_le_iff ρ (euclideanEpigraph_nonempty hf) (euclideanEpigraph_nonempty hg)
    (mul_nonneg (Real.sqrt_nonneg _) h.1)).mpr
    ⟨euclideanEpigraph_subset_cthickening h.1 h.2.1, euclideanEpigraph_subset_cthickening h.1 h.2.2⟩

/-- **Obstruction to the lower estimate in 7.61.** The epigraphs of the
constant functions 2 and 3 both miss the closed unit ball. Their auxiliary
distance is 1 at every nonnegative radius. -/
theorem auxEpiDistance_counterexample (r : ℝ≥0) :
    auxEpiDistance r (fun _ : ℝ ↦ (2 : EReal)) (fun _ ↦ (3 : EReal)) = 1 ∧
    rhoHatDistance 1 (euclideanEpigraph (fun _ : ℝ ↦ (2 : EReal)))
      (euclideanEpigraph (fun _ ↦ (3 : EReal))) = 0 := by
  have hcut (a : ℝ) (ha : 0 ≤ a) : max (a : EReal) ((-(r : ℝ) : ℝ) : EReal) = (a : EReal) :=
    max_eq_left (EReal.coe_le_coe_iff.mpr ((neg_nonpos.mpr r.coe_nonneg).trans ha))
  have hadm : auxEpiAdmissible r (fun _ : ℝ ↦ (2 : EReal)) (fun _ ↦ (3 : EReal)) 1 := by
    refine ⟨zero_le_one, fun x _ ↦ ⟨x, by simp, ?_⟩, fun x _ ↦ ⟨x, by simp, ?_⟩⟩
    · change ((3 : ℝ) : EReal) ≤ max ((2 : ℝ) : EReal) _ + ((1 : ℝ) : EReal)
      rw [hcut 2 (by norm_num), ← EReal.coe_add, EReal.coe_le_coe_iff]
      norm_num
    · change ((2 : ℝ) : EReal) ≤ max ((3 : ℝ) : EReal) _ + ((1 : ℝ) : EReal)
      rw [hcut 3 (by norm_num), ← EReal.coe_add, EReal.coe_le_coe_iff]
      norm_num
  constructor
  · apply le_antisymm (csInf_le (auxEpiAdmissible_bddBelow _ _ _) hadm)
    apply le_csInf (s := {e : ℝ | auxEpiAdmissible r (fun _ : ℝ ↦ (2 : EReal)) (fun _ ↦ (3 : EReal)) e}) ⟨1, hadm⟩
    intro e he
    have he' : auxEpiAdmissible r (fun _ : ℝ ↦ (2 : EReal)) (fun _ ↦ (3 : EReal)) e := he
    obtain ⟨_, _, hy⟩ := he'.2.1 0 (by simp)
    change ((3 : ℝ) : EReal) ≤ max ((2 : ℝ) : EReal) _ + (e : EReal) at hy
    rw [hcut 2 (by norm_num), ← EReal.coe_add, EReal.coe_le_coe_iff] at hy
    linarith
  · have empty (a : ℝ) (ha : 1 < a) :
        euclideanEpigraph (fun _ : ℝ ↦ (a : EReal)) ∩ closedBall 0 (1 : ℝ) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro p ⟨hp, hball⟩
      have hp' : ‖p‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hball
      have hval : a ≤ p.snd := EReal.coe_le_coe_iff.mp hp
      have habs : |p.snd| ≤ 1 := (WithLp.norm_snd_le _ p).trans hp'
      linarith [(abs_le.mp habs).2]
    change (rhoHatEDistance 1 (euclideanEpigraph (fun _ : ℝ ↦ ((2 : ℝ) : EReal)))
      (euclideanEpigraph (fun _ ↦ ((3 : ℝ) : EReal)))).toReal = 0
    simp [rhoHatEDistance, empty 2 (by norm_num), empty 3 (by norm_num)]

end RW
