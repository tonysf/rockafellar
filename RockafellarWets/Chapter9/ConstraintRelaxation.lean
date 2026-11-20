/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Constraint relaxation by an exact distance penalty

Proposition 9.68. An open neighborhood of the entire closed feasible set
has the same optimal value and minimizers after adding a sufficiently
large distance penalty. The neighborhood is a union of smaller Lipschitz
balls; nearest feasible points remain in the corresponding larger balls.
-/

import RockafellarWets.Chapter9.LipschitzExtension
import RockafellarWets.Chapter9.LipschitzModulusCalculus
import RockafellarWets.Chapter9.DistanceModulus

open Filter Metric Set Topology
open scoped ENNReal NNReal

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

/-- The real-valued distance penalty objective. -/
noncomputable def distancePenalty (f : E → ℝ) (C : Set E) (lam : ℝ≥0) (x : E) : ℝ :=
  f x + lam * infDist x C

@[simp] theorem distancePenalty_eq_of_mem {f : E → ℝ} {C : Set E} {lam : ℝ≥0} {x : E}
    (hx : x ∈ C) : distancePenalty f C lam x = f x := by
  simp [distancePenalty,infDist_zero_of_mem hx]

/-- A uniform strict relaxation of the modulus bound on `C` extends to an
open neighborhood where nearest feasible points admit the same one-sided
Lipschitz comparison. -/
theorem exists_constraintRelaxation_neighborhood {f : E → ℝ} {C : Set E}
    (hC : IsClosed C) (hne : C.Nonempty) {k l : ℝ≥0} (hkl : k < l)
    (hmod : ∀ x ∈ C, lipschitzModulus f x ≤ (k : ℝ≥0∞)) :
    ∃ O : Set E, IsOpen O ∧ C ⊆ O ∧
      (∀ x ∈ O, lipschitzModulus f x ≤ (l : ℝ≥0∞)) ∧
      ∀ x ∈ O, ∃ w ∈ C, infDist x C = dist x w ∧ f w - f x ≤ l * infDist x C := by
  let O : Set E := {x | ∃ c ∈ C, ∃ r : ℝ, 0 < r ∧
    LipschitzOnWith l f (ball c r) ∧ x ∈ ball c (r/3)}
  have hO : IsOpen O := isOpen_iff_mem_nhds.mpr fun x ⟨c,hc,r,hr,hL,hx⟩ ↦
    Filter.mem_of_superset (isOpen_ball.mem_nhds hx) fun y hy ↦ ⟨c,hc,r,hr,hL,hy⟩
  have hCO : C ⊆ O := by
    intro c hc
    obtain ⟨U,hU,hL⟩ := exists_lipschitzOnWith_of_modulus_lt
      ((hmod c hc).trans_lt (ENNReal.coe_lt_coe.mpr hkl))
    obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hU
    exact ⟨c,hc,r,hr,hL.mono hball,mem_ball_self (by positivity)⟩
  refine ⟨O,hO,hCO,?_,?_⟩
  · rintro x ⟨c,hc,r,hr,hL,hx⟩
    have hxr : x ∈ ball c r := by
      have hxc : dist x c < r/3 := hx
      change dist x c < r
      linarith
    exact lipschitzModulus_le (isOpen_ball.mem_nhds hxr) hL
  · rintro x ⟨c,hc,r,hr,hL,hx⟩
    obtain ⟨w,hw,hd⟩ := hC.exists_infDist_eq_dist hne x
    have hxc : dist x c < r/3 := hx
    have hdist : dist x w ≤ dist x c := hd ▸ infDist_le_dist_of_mem hc
    have hwc : w ∈ ball c r := by
      have htri := dist_triangle w x c
      rw [dist_comm w x] at htri
      change dist w c < r
      linarith
    have hxr : x ∈ ball c r := by
      change dist x c < r
      linarith
    refine ⟨w,hw,hd,?_⟩
    have hle := hL.le_add_mul hwc hxr
    rw [dist_comm w x,← hd] at hle
    linarith

/-- Restricted real objectives have the expected constrained infimum,
including the negative-infinite case. -/
theorem iInf_restrictedRealFunction (f : E → ℝ) (C : Set E) :
    (⨅ x, restrictedRealFunction f C x) = ⨅ x ∈ C, (f x : EReal) := by
  apply le_antisymm
  · refine le_iInf fun x ↦ le_iInf fun hx ↦ ?_
    simpa only [restrictedRealFunction,if_pos hx] using iInf_le (restrictedRealFunction f C) x
  · apply le_iInf
    intro x
    by_cases hx : x ∈ C
    · simpa only [restrictedRealFunction,if_pos hx] using
        (iInf₂_le x hx : (⨅ y ∈ C, (f y : EReal)) ≤ (f x : EReal))
    · simp only [restrictedRealFunction,if_neg hx,le_top]

/-- Equality of optimal values and minimizers follows from exact
agreement on the feasible set and strict improvement from every other
point to some feasible point. -/
theorem exactPenalty_of_strict_comparison {f g : E → ℝ} {C O : Set E}
    (hne : C.Nonempty) (hCO : C ⊆ O) (he : EqOn g f C)
    (hcomp : ∀ x ∈ O, ∃ w ∈ C, f w ≤ g x)
    (hstrict : ∀ x ∈ O \ C, ∃ w ∈ C, f w < g x) :
    (⨅ x ∈ O, (g x : EReal)) = (⨅ x ∈ C, (f x : EReal)) ∧
      argmin (restrictedRealFunction g O) = argmin (restrictedRealFunction f C) := by
  have hi : (⨅ x ∈ O, (g x : EReal)) = (⨅ x ∈ C, (f x : EReal)) := by
    apply le_antisymm
    · refine le_iInf fun x ↦ le_iInf fun hx ↦ ?_
      simpa only [he hx] using (iInf₂_le x (hCO hx) : (⨅ y ∈ O, (g y : EReal)) ≤ (g x : EReal))
    · refine le_iInf fun x ↦ le_iInf fun hx ↦ ?_
      obtain ⟨w,hw,hle⟩ := hcomp x hx
      exact (iInf₂_le w hw).trans (EReal.coe_le_coe_iff.mpr hle)
  have hi' : (⨅ x, restrictedRealFunction g O x) = ⨅ x, restrictedRealFunction f C x := by
    simpa only [iInf_restrictedRealFunction] using hi
  obtain ⟨c,hc⟩ := hne
  have hfin : (⨅ x, restrictedRealFunction f C x) < ⊤ :=
    (iInf_le _ c).trans_lt (by simp [restrictedRealFunction,hc])
  refine ⟨hi,?_⟩
  ext x
  by_cases hxC : x ∈ C
  · simp only [mem_argmin_iff,hi']
    simp only [restrictedRealFunction,if_pos hxC,if_pos (hCO hxC),he hxC]
  have hnC : x ∉ argmin (restrictedRealFunction f C) := by
    intro hx
    have hlt := hx.1.trans_lt hx.2
    simpa only [restrictedRealFunction,if_neg hxC,lt_self_iff_false] using hlt
  have hnO : x ∉ argmin (restrictedRealFunction g O) := by
    intro hx
    have hxO : x ∈ O := by
      by_contra hn
      have hlt := hx.1.trans_lt hx.2
      simpa only [restrictedRealFunction,if_neg hn,lt_self_iff_false] using hlt
    obtain ⟨w,hw,hlt⟩ := hstrict x ⟨hxO,hxC⟩
    have hle : (g x : EReal) ≤ (f w : EReal) := by
      calc (g x : EReal) = restrictedRealFunction g O x := by simp [restrictedRealFunction,hxO]
        _ = ⨅ y, restrictedRealFunction g O y := hx.1
        _ ≤ restrictedRealFunction g O w := iInf_le _ w
        _ = (f w : EReal) := by simp [restrictedRealFunction,hCO hw,he hw]
    exact hlt.not_ge (EReal.coe_le_coe_iff.mp hle)
  exact iff_of_false hnO hnC

/-- **Proposition 9.68**, the exact penalty formulas on an open
neighborhood of the entire closed nonempty feasible set. -/
theorem constraintRelaxation {f : E → ℝ} {C : Set E} (hC : IsClosed C) (hne : C.Nonempty)
    {k lam : ℝ≥0} (hkl : k < lam) (hmod : ∀ x ∈ C, lipschitzModulus f x ≤ (k : ℝ≥0∞)) :
    ∃ O : Set E, IsOpen O ∧ C ⊆ O ∧
      (∀ x ∈ O, lipschitzModulus f x < (lam : ℝ≥0∞)) ∧
      (⨅ x ∈ O, (distancePenalty f C lam x : EReal)) = (⨅ x ∈ C, (f x : EReal)) ∧
      argmin (restrictedRealFunction (distancePenalty f C lam) O) = argmin (restrictedRealFunction f C) := by
  obtain ⟨l,hkl',hll⟩ := exists_between hkl
  obtain ⟨O,hO,hCO,hbound,hcomp⟩ := exists_constraintRelaxation_neighborhood hC hne hkl' hmod
  refine ⟨O,hO,hCO,fun x hx ↦ (hbound x hx).trans_lt (ENNReal.coe_lt_coe.mpr hll),?_⟩
  apply exactPenalty_of_strict_comparison hne hCO (fun x hx ↦ distancePenalty_eq_of_mem hx)
  · intro x hx
    obtain ⟨w,hw,hd,hle⟩ := hcomp x hx
    refine ⟨w,hw,?_⟩
    have hll' : (l : ℝ) ≤ lam := NNReal.coe_le_coe.mpr hll.le
    have hmul := mul_le_mul_of_nonneg_right hll' (infDist_nonneg : 0 ≤ infDist x C)
    dsimp [distancePenalty]
    linarith
  · rintro x ⟨hxO,hxC⟩
    obtain ⟨w,hw,hd,hle⟩ := hcomp x hxO
    refine ⟨w,hw,?_⟩
    have hpos := hC.notMem_iff_infDist_pos hne |>.mp hxC
    have hmul := mul_lt_mul_of_pos_right (show (l : ℝ) < lam from hll) hpos
    dsimp [distancePenalty]
    linarith

/-- The distance penalty adds at most its weight to a local Lipschitz
modulus. -/
theorem lipschitzModulus_distancePenalty_le {f : E → ℝ} {C : Set E} {lam l : ℝ≥0} {x : E}
    (hf : lipschitzModulus f x ≤ (l : ℝ≥0∞)) :
    lipschitzModulus (distancePenalty f C lam) x ≤ ((l + lam : ℝ≥0) : ℝ≥0∞) := by
  have hd : LipschitzWith lam (fun y ↦ (lam : ℝ) * infDist y C) := by
    simpa only [Function.comp_def,smul_eq_mul,Real.nnnorm_of_nonneg lam.coe_nonneg,mul_one]
      using (lipschitzWith_smul (lam : ℝ)).comp (lipschitz_infDist_pt C)
  have hdmod : lipschitzModulus (fun y ↦ (lam : ℝ) * infDist y C) x ≤ (lam : ℝ≥0∞) :=
    lipschitzModulus_le univ_mem (fun _ _ _ _ ↦ hd _ _)
  have hadd := lipschitzModulusWithin_add_le f (fun y ↦ (lam : ℝ) * infDist y C) univ x
  exact hadd.trans (by simpa only [ENNReal.coe_add] using add_le_add hf hdmod)

/-- Corrected quantitative remark following **Proposition 9.68**. For any
positive relaxation `ε`, the neighborhood can be chosen with penalty
modulus at most `κ + ε + λ`. -/
theorem constraintRelaxation_with_modulus_relaxation {f : E → ℝ} {C : Set E}
    (hC : IsClosed C) (hne : C.Nonempty) {k lam ε : ℝ≥0} (hkl : k < lam) (hε : 0 < ε)
    (hmod : ∀ x ∈ C, lipschitzModulus f x ≤ (k : ℝ≥0∞)) :
    ∃ O : Set E, IsOpen O ∧ C ⊆ O ∧
      (∀ x ∈ O, lipschitzModulus f x < (lam : ℝ≥0∞)) ∧
      (∀ x ∈ O, lipschitzModulus (distancePenalty f C lam) x ≤ ((k + ε + lam : ℝ≥0) : ℝ≥0∞)) ∧
      (⨅ x ∈ O, (distancePenalty f C lam x : EReal)) = (⨅ x ∈ C, (f x : EReal)) ∧
      argmin (restrictedRealFunction (distancePenalty f C lam) O) = argmin (restrictedRealFunction f C) := by
  obtain ⟨l,hkl',hl⟩ := exists_between (lt_min hkl (lt_add_of_pos_right k hε))
  have hll : l < lam := hl.trans_le (min_le_left _ _)
  have hlε : l ≤ k + ε := hl.le.trans (min_le_right _ _)
  obtain ⟨O,hO,hCO,hbound,hcomp⟩ := exists_constraintRelaxation_neighborhood hC hne hkl' hmod
  refine ⟨O,hO,hCO,fun x hx ↦ (hbound x hx).trans_lt (ENNReal.coe_lt_coe.mpr hll),
    fun x hx ↦ (lipschitzModulus_distancePenalty_le (hbound x hx)).trans
      (ENNReal.coe_le_coe.mpr (add_le_add hlε (le_rfl : lam ≤ lam))),?_⟩
  apply exactPenalty_of_strict_comparison hne hCO (fun x hx ↦ distancePenalty_eq_of_mem hx)
  · intro x hx
    obtain ⟨w,hw,_,hle⟩ := hcomp x hx
    refine ⟨w,hw,?_⟩
    have hmul := mul_le_mul_of_nonneg_right (show (l : ℝ) ≤ lam from hll.le)
      (infDist_nonneg : 0 ≤ infDist x C)
    dsimp [distancePenalty]
    linarith
  · rintro x ⟨hxO,hxC⟩
    obtain ⟨w,hw,_,hle⟩ := hcomp x hxO
    refine ⟨w,hw,?_⟩
    have hmul := mul_lt_mul_of_pos_right (show (l : ℝ) < lam from hll)
      (hC.notMem_iff_infDist_pos hne |>.mp hxC)
    dsimp [distancePenalty]
    linarith

/-- The local-optimum consequence following **Proposition 9.68**. At a
feasible point, a penalty weight strictly larger than the local modulus
preserves local minimality. -/
theorem isLocalMin_distancePenalty_iff {f : E → ℝ} {C : Set E} (hC : IsClosed C)
    {x : E} (hx : x ∈ C) {lam : ℝ≥0} (hmod : lipschitzModulus f x < (lam : ℝ≥0∞)) :
    IsLocalMin (distancePenalty f C lam) x ↔ IsLocalMinOn f C x := by
  constructor
  · intro hm
    change ∀ᶠ y in 𝓝[C] x, f x ≤ f y
    filter_upwards [mem_nhdsWithin_of_mem_nhds hm,self_mem_nhdsWithin] with y hy hyC
    simpa only [distancePenalty_eq_of_mem hx,distancePenalty_eq_of_mem hyC] using hy
  · intro hm
    change ∀ᶠ y in 𝓝 x, distancePenalty f C lam x ≤ distancePenalty f C lam y
    have hnear : ∀ᶠ y in 𝓝 x, y ∈ C → f x ≤ f y := mem_nhdsWithin_iff_eventually.mp hm
    obtain ⟨U,hU,hL⟩ := exists_lipschitzOnWith_of_modulus_lt hmod
    obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (inter_mem hU hnear)
    filter_upwards [ball_mem_nhds x (show 0 < r/3 by positivity)] with y hy
    obtain ⟨w,hw,hd⟩ := hC.exists_infDist_eq_dist ⟨x,hx⟩ y
    have hyx : dist y x < r/3 := hy
    have hdist : dist y w ≤ dist y x := hd ▸ infDist_le_dist_of_mem hx
    have hwB : w ∈ ball x r := by
      have htri := dist_triangle w y x
      rw [dist_comm w y] at htri
      change dist w x < r
      linarith
    have hyB : y ∈ ball x r := by
      change dist y x < r
      linarith
    have hmin := (hball hwB).2 hw
    have hLip := hL.le_add_mul (hball hwB).1 (hball hyB).1
    rw [dist_comm w y,← hd] at hLip
    rw [distancePenalty_eq_of_mem hx]
    exact hmin.trans hLip

end RW
