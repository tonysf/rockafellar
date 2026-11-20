/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 7: Counterexamples for local growth and inverse conditioning
-/

import RockafellarWets.Chapter7.SolutionStability

open Filter Metric Set Topology
open scoped NNReal

namespace RW

/-- A two-point objective. The value at zero is zero and the value at two
is `a`. All other points are infeasible. -/
noncomputable def twoWellObjective (a x : ℝ) : EReal :=
  if x = 0 then 0 else if x = 2 then (a : EReal) else ⊤

private theorem twoWell_lsc (a : ℝ) : LowerSemicontinuous (twoWellObjective a) := by
  apply lowerSemicontinuous_of_isClosed_epigraph_ereal
  have heq : epigraph (twoWellObjective a) = ({0} ×ˢ Ici 0) ∪ ({2} ×ˢ Ici a) := by
    ext ⟨x, b⟩
    by_cases h : x = 0 <;> by_cases h' : x = 2 <;> simp_all [epigraph, twoWellObjective]
  rw [heq]
  exact (isClosed_singleton.prod isClosed_Ici).union (isClosed_singleton.prod isClosed_Ici)

private theorem twoWell_proper (a : ℝ) : IsProper (twoWellObjective a) := by
  refine ⟨⟨0, by simp [twoWellObjective]⟩, fun x ↦ ?_⟩
  by_cases hx : x = 0 <;> by_cases hy : x = 2 <;> simp [twoWellObjective, hx, hy]

private theorem twoWell_levelBounded (a : ℝ) : IsLevelBounded (twoWellObjective a) := by
  intro t
  apply (((finite_singleton (2:ℝ)).insert 0).isBounded).subset
  intro x hx
  by_contra hn
  have hx0 : x ≠ 0 := fun h ↦ hn (Or.inl h)
  have hx2 : x ≠ 2 := fun h ↦ hn (Or.inr h)
  simp [levelSet, twoWellObjective, hx0, hx2] at hx

private theorem twoWell_min {a : ℝ} (ha : 0 ≤ a) : (⨅ x, twoWellObjective a x) = 0 := by
  apply le_antisymm ((iInf_le _ 0).trans (by simp [twoWellObjective]))
  apply le_iInf
  intro x
  by_cases hx : x = 0 <;> by_cases hy : x = 2 <;> simp [twoWellObjective, hx, hy, ha]

private theorem twoWell_argmin {a : ℝ} (ha : 0 < a) : argmin (twoWellObjective a) = {0} := by
  ext x
  rw [mem_argmin_iff_eq_iInf_of_isProper (twoWell_proper _) _, twoWell_min ha.le]
  by_cases hx : x = 0 <;> by_cases hy : x = 2 <;> simp_all [twoWellObjective, ha.ne']

private theorem twoWell_perturbed_minimizer : (2:ℝ) ∈
    argminOn (twoWellObjective 0) (closedBall 0 3) := by
  have hB : (2:ℝ) ∈ closedBall 0 3 := by norm_num [mem_closedBall, Real.dist_eq]
  have hmin : infimumOn (twoWellObjective 0) (closedBall 0 3) = 0 := by
    apply le_antisymm ((infimumOn_le hB).trans (by norm_num [twoWellObjective]))
    exact le_infimumOn fun x _ ↦ (twoWell_min (le_refl 0)) ▸ iInf_le _ x
  exact ⟨hB, by norm_num [twoWellObjective, hmin], hmin.trans_lt (by simp)⟩

private theorem auxEpiDistance_twoWell_le (r : ℝ≥0) {a : ℝ} (ha : 0 ≤ a) :
    auxEpiDistance r (twoWellObjective a) (twoWellObjective 0) ≤ a := by
  have hdir {u v : ℝ} (hval : v ≤ u+a) :
      auxEpiComparison r (twoWellObjective u) (twoWellObjective v) a := by
    intro x _
    refine ⟨x, by simpa using ha, ?_⟩
    apply le_trans _ (add_le_add_left (le_max_left _ _) _)
    by_cases hx : x = 0
    · simp [twoWellObjective, hx, ha]
    by_cases hy : x = 2
    · simpa [twoWellObjective, hx, hy, ← EReal.coe_add] using EReal.coe_le_coe_iff.mpr hval
    · simp [twoWellObjective, hx, hy]
  exact csInf_le (auxEpiAdmissible_bddBelow _ _ _) ⟨ha, hdir (by linarith), hdir (by linarith)⟩

/-- **Obstruction to the printed 7.63 and 7.65(a,b)**. The unique optimum
is zero. Both local growth assumptions hold with ε = γ = 1. A perturbation
of at most 1/4 creates an optimizer at distance two, violating both bounds. -/
theorem local_growth_solution_counterexample :
    let f := twoWellObjective (1/4)
    let g := twoWellObjective 0
    let d := auxEpiDistance 3 f g
    LowerSemicontinuous f ∧ IsProper f ∧ IsLevelBounded f ∧ f 0 = 0 ∧
      (⨅ x, f x) = 0 ∧ argmin f = {0} ∧
      (∀ x : ℝ, ‖x‖ < 1 → ((‖x‖ : ℝ) : EReal) ≤ f x ∧ ((‖x‖^2 : ℝ) : EReal) ≤ f x) ∧
      LowerSemicontinuous g ∧ IsProper g ∧ 0 ≤ d ∧ d ≤ 1/4 ∧ d < min 3 (1/2) ∧
      (2:ℝ) ∈ argminOn g (closedBall 0 3) ∧
      (1 + 2 / (1:ℝ))*d < infDist 2 (argmin f) ∧
      d + Real.sqrt (2*d) < infDist 2 (argmin f) := by
  let f := twoWellObjective (1/4)
  let g := twoWellObjective 0
  let d := auxEpiDistance 3 f g
  have hd : d ≤ 1/4 := auxEpiDistance_twoWell_le _ (by norm_num)
  have hd₀ : 0 ≤ d := auxEpiDistance_nonneg (twoWell_proper _).1 (twoWell_proper _).1
  have hA : argmin f = {0} := twoWell_argmin (by norm_num)
  have hdA : infDist 2 (argmin f) = 2 := by norm_num [hA, Real.dist_eq]
  refine ⟨twoWell_lsc _, twoWell_proper _, twoWell_levelBounded _, by simp [twoWellObjective],
    twoWell_min (by norm_num), hA, ?_, twoWell_lsc _, twoWell_proper _, hd₀, hd, by norm_num; linarith,
    twoWell_perturbed_minimizer, ?_, ?_⟩
  · intro x hx
    by_cases hx0 : x = 0
    · simp [twoWellObjective, hx0]
    · have hx2 : x ≠ 2 := by rintro rfl; norm_num at hx
      simp [twoWellObjective, hx0, hx2]
  · change (1 + 2 / (1:ℝ))*d < infDist 2 (argmin f)
    rw [hdA]; linarith
  · change d + Real.sqrt (2*d) < infDist 2 (argmin f)
    rw [hdA]
    have hs : Real.sqrt (2*d) ≤ 1 := Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
    linarith

private theorem twoWell_radius_lt {a e : ℝ} (ha : 0 < a) (he : 0 ≤ e) (hea : e < a) :
    conditioningRadius (twoWellObjective a) 0 e = 0 := by
  have heq : levelSet (twoWellObjective a) (((0:ℝ) + e : ℝ) : EReal) = {0} := by
    ext x
    by_cases hx : x = 0 <;> by_cases hy : x = 2 <;> simp_all [levelSet, twoWellObjective, not_le.mpr hea]
  unfold conditioningRadius
  rw [heq]
  simp [twoWell_argmin ha]

private theorem twoWell_radius_at {a : ℝ} (ha : 0 < a) :
    conditioningRadius (twoWellObjective a) 0 a = 2 := by
  have heq : levelSet (twoWellObjective a) (((0:ℝ) + a : ℝ) : EReal) = {0, 2} := by
    ext x
    by_cases hx : x = 0 <;> by_cases hy : x = 2 <;> simp_all [levelSet, twoWellObjective, ha.le]
  unfold conditioningRadius
  rw [heq]
  norm_num [twoWell_argmin ha, Set.image_pair, csSup_insert, Real.dist_eq]

/-- **Obstruction to the parenthetical lsc claim in Theorem 7.64**. A
two-point proper lsc level-bounded objective has a jump in its inverse
conditioning radius at η = 1/2, with the larger value attained there. -/
theorem solutionRadius_not_lowerSemicontinuousOn :
    let f := twoWellObjective 1
    LowerSemicontinuous f ∧ IsProper f ∧ IsLevelBounded f ∧ (⨅ x, f x) = 0 ∧
      solutionRadius f 0 (1/2) = 5/2 ∧
      (∀ η ∈ Ico 0 (1/2 : ℝ), solutionRadius f 0 η = η) ∧
      ¬ LowerSemicontinuousOn (solutionRadius f 0) (Ici 0) := by
  have hat : solutionRadius (twoWellObjective 1) 0 (1/2) = 5/2 := by
    norm_num [solutionRadius, twoWell_radius_at (by norm_num : (0:ℝ) < 1)]
  have hbelow {η : ℝ} (hη : η ∈ Ico 0 (1/2 : ℝ)) : solutionRadius (twoWellObjective 1) 0 η = η := by
    rw [solutionRadius, twoWell_radius_lt (by norm_num) (by linarith [hη.1]) (by linarith [hη.2]), add_zero]
  refine ⟨twoWell_lsc _, twoWell_proper _, twoWell_levelBounded _, twoWell_min (by norm_num), hat,
    fun _ h ↦ hbelow h, ?_⟩
  intro hlsc
  have h := hlsc (1/2) (by norm_num : (1/2:ℝ) ∈ Ici 0) 1 (show (1:ℝ) < solutionRadius (twoWellObjective 1) 0 (1/2) by rw [hat]; norm_num)
  have hmem : Ici (0:ℝ) ∈ 𝓝 (1/2:ℝ) := Ici_mem_nhds (by norm_num)
  rw [nhdsWithin_eq_nhds.mpr hmem] at h
  have hboth : ∀ᶠ x : ℝ in 𝓝 (1/2:ℝ), 0 ≤ x ∧ 1 < solutionRadius (twoWellObjective 1) 0 x := by
    filter_upwards [hmem, h] with x hx hx' using ⟨hx, hx'⟩
  obtain ⟨a, ha₀, ha, ha'⟩ := hboth.exists_lt
  have hval := hbelow ⟨ha, ha₀⟩
  rw [hval] at ha'
  linarith

end RW
