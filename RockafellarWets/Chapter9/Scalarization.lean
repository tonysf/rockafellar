/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Scalarization of strict continuity and of its exact modulus
-/

import RockafellarWets.Chapter9.LipschitzModulusCalculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Metric Set Topology
open scoped ENNReal NNReal InnerProductSpace

namespace RW

variable {E F : Type*} [MetricSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem lipschitzModulusWithin_inner_le (f : E → F) (X : Set E) (x : E) (v : F) :
    lipschitzModulusWithin (fun y ↦ ⟪v,f y⟫_ℝ) X x ≤
      (‖v‖₊ : ℝ≥0∞) * lipschitzModulusWithin f X x := by
  have hL : LipschitzWith ‖v‖₊ (fun z : F ↦ ⟪v,z⟫_ℝ) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    simpa only [Real.dist_eq,← inner_sub_right,dist_eq_norm,coe_nnnorm] using
      abs_real_inner_le_norm v (a-b)
  exact lipschitzModulusWithin_comp_lipschitzWith hL f X x

theorem lipschitzModulusWithin_sum_le {ι : Type*} (s : Finset ι) (f : ι → E → F)
    (X : Set E) (x : E) :
    lipschitzModulusWithin (fun y ↦ ∑ i ∈ s, f i y) X x ≤
      ∑ i ∈ s, lipschitzModulusWithin (f i) X x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [lipschitzModulusWithin_const]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (lipschitzModulusWithin_add_le _ _ X x).trans (add_le_add le_rfl ih)

variable [FiniteDimensional ℝ F]

/-- Any number below the vector modulus is a lower bound for the modulus
of some unit scalarization. Normalizing the output differences also handles
an infinite vector modulus, without assuming continuity in advance. -/
theorem exists_unit_scalar_modulus_ge {f : E → F} {X : Set E} {x : E} {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < lipschitzModulusWithin f X x) :
    ∃ v : F, ‖v‖ = 1 ∧ (q : ℝ≥0∞) ≤ lipschitzModulusWithin (fun y ↦ ⟪v,f y⟫_ℝ) X x := by
  have hpick (n : ℕ) : ∃ y ∈ ball x (1 / ((n:ℝ)+1)) ∩ X,
      ∃ z ∈ ball x (1 / ((n:ℝ)+1)) ∩ X, (q:ℝ) * dist y z < dist (f y) (f z) := by
    have hbad : ¬ LipschitzOnWith q f (ball x (1 / ((n:ℝ)+1)) ∩ X) := by
      intro hL
      exact hq.not_ge (lipschitzModulusWithin_le
        (inter_mem (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (by positivity))) self_mem_nhdsWithin) hL)
    simpa only [lipschitzOnWith_iff_dist_le_mul,not_forall,not_le,exists_prop] using hbad
  choose y hy z hz hqdist using hpick
  have hyto : Tendsto y atTop (𝓝 x) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ (hy n).1.le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hzto : Tendsto z atTop (𝓝 x) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ (hz n).1.le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hdiff (n : ℕ) : f (y n)-f (z n) ≠ 0 := by
    apply norm_ne_zero_iff.mp
    exact ne_of_gt ((mul_nonneg q.coe_nonneg dist_nonneg).trans_lt
      (by simpa only [dist_eq_norm] using hqdist n))
  let u : ℕ → F := fun n ↦ ‖f (y n)-f (z n)‖⁻¹ • (f (y n)-f (z n))
  have hunorm (n : ℕ) : ‖u n‖ = 1 := by
    simp only [u,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hdiff n))]
  obtain ⟨v,hv,φ,hφ,huto⟩ := (isCompact_sphere (0:F) 1).tendsto_subseq
    (fun n ↦ show u n ∈ sphere (0:F) 1 by simpa using hunorm n)
  have hvnorm : ‖v‖ = 1 := by simpa using hv
  refine ⟨v,hvnorm,?_⟩
  unfold lipschitzModulusWithin
  apply le_iInf
  intro k
  obtain ⟨U,hU,hL⟩ := k.property
  have hywithin : Tendsto y atTop (𝓝[X] x) := tendsto_nhdsWithin_iff.mpr
    ⟨hyto,Eventually.of_forall fun n ↦ (hy n).2⟩
  have hzwithin : Tendsto z atTop (𝓝[X] x) := tendsto_nhdsWithin_iff.mpr
    ⟨hzto,Eventually.of_forall fun n ↦ (hz n).2⟩
  have hbound : ∀ᶠ n in atTop, |⟪v,u (φ n)⟫_ℝ| * (q:ℝ) ≤ (k:ℝ≥0) := by
    filter_upwards [(hywithin.comp hφ.tendsto_atTop).eventually hU,
      (hzwithin.comp hφ.tendsto_atTop).eventually hU] with n hyn hzn
    have hpos : 0 < dist (y (φ n)) (z (φ n)) := by
      apply dist_pos.mpr
      intro he
      simpa only [he,dist_self,mul_zero,lt_self_iff_false] using hqdist (φ n)
    have hrepr : f (y (φ n))-f (z (φ n)) = ‖f (y (φ n))-f (z (φ n))‖ • u (φ n) := by
      simp only [u,smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr (hdiff (φ n))),one_smul]
    have hs := hL.dist_le_mul _ hyn _ hzn
    simp only [Function.comp_def] at hs
    rw [Real.dist_eq,← inner_sub_right,hrepr,inner_smul_right,abs_mul,
      abs_of_nonneg (norm_nonneg _)] at hs
    apply le_of_mul_le_mul_right ?_ hpos
    have hd := mul_le_mul_of_nonneg_left (hqdist (φ n)).le (abs_nonneg ⟪v,u (φ n)⟫_ℝ)
    rw [dist_eq_norm] at hd
    nlinarith
  have hlim : Tendsto (fun n ↦ |⟪v,u (φ n)⟫_ℝ| * (q:ℝ)) atTop (𝓝 (q:ℝ)) := by
    simpa only [Function.comp_def,real_inner_self_eq_norm_sq,hvnorm,one_pow,abs_one,one_mul] using
      (((tendsto_const_nhds (x := v)).inner huto).abs.mul_const (q:ℝ))
  exact ENNReal.coe_le_coe.mpr (NNReal.coe_le_coe.mp (le_of_tendsto hlim hbound))

/-- **Exercise 9.9**, the exact scalarization formula over the unit sphere. -/
theorem lipschitzModulusWithin_eq_iSup_unit_inner (f : E → F) (X : Set E) (x : E) :
    lipschitzModulusWithin f X x =
      ⨆ v : {v : F // ‖v‖ = 1}, lipschitzModulusWithin (fun y ↦ ⟪v.1,f y⟫_ℝ) X x := by
  apply le_antisymm
  · by_contra! hlt
    obtain ⟨q,hq,hqf⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hlt
    obtain ⟨v,hv,hle⟩ := exists_unit_scalar_modulus_ge hqf
    exact hq.not_ge (hle.trans (le_iSup
      (fun v : {v : F // ‖v‖ = 1} ↦ lipschitzModulusWithin (fun y ↦ ⟪v.1,f y⟫_ℝ) X x) ⟨v,hv⟩))
  · apply iSup_le
    intro v
    have hv : ‖v.1‖₊ = 1 := NNReal.eq v.2
    simpa only [hv,ENNReal.coe_one,one_mul] using lipschitzModulusWithin_inner_le f X x v.1

/-- **Exercise 9.9**, the equivalent formula over the closed unit ball. -/
theorem lipschitzModulusWithin_eq_iSup_ball_inner (f : E → F) (X : Set E) (x : E) :
    lipschitzModulusWithin f X x =
      ⨆ v : {v : F // ‖v‖ ≤ 1}, lipschitzModulusWithin (fun y ↦ ⟪v.1,f y⟫_ℝ) X x := by
  apply le_antisymm
  · rw [lipschitzModulusWithin_eq_iSup_unit_inner f X x]
    exact iSup_le fun v ↦ le_iSup_of_le ⟨v.1,v.2.le⟩ le_rfl
  · apply iSup_le
    intro v
    exact (lipschitzModulusWithin_inner_le f X x v.1).trans
      ((mul_le_mul' (show (‖v.1‖₊ : ℝ≥0∞) ≤ 1 from ENNReal.coe_le_coe.mpr v.2) le_rfl).trans_eq (one_mul _))

/-- **Exercise 9.9**, scalar strict continuity is equivalent to vector strict
continuity. Finitely many orthonormal coordinates suffice for the reverse implication. -/
theorem strictlyContinuousWithinAt_iff_inner (f : E → F) {X : Set E} {x : E} (hx : x ∈ X) :
    StrictlyContinuousWithinAt f X x ↔
      ∀ v : F, StrictlyContinuousWithinAt (fun y ↦ ⟪v,f y⟫_ℝ) X x := by
  constructor
  · intro h v
    exact ⟨hx,(lipschitzModulusWithin_inner_le f X x v).trans_lt
      (ENNReal.mul_lt_top ENNReal.coe_lt_top h.2)⟩
  · intro h
    let b := stdOrthonormalBasis ℝ F
    let g := fun i (y : E) ↦ ⟪b i,f y⟫_ℝ • b i
    have hg (i : Fin (Module.finrank ℝ F)) : lipschitzModulusWithin (g i) X x < ⊤ := by
      have hL : LipschitzWith ‖b i‖₊ (fun r : ℝ ↦ r • b i) := by
        apply LipschitzWith.of_dist_le_mul
        intro r s
        simp only [dist_eq_norm,← sub_smul,norm_smul,Real.norm_eq_abs,coe_nnnorm]
        exact le_of_eq (mul_comm ..)
      exact (lipschitzModulusWithin_comp_lipschitzWith hL (fun y ↦ ⟪b i,f y⟫_ℝ) X x).trans_lt
        (ENNReal.mul_lt_top ENNReal.coe_lt_top (h (b i)).2)
    have he : (fun y ↦ ∑ i, g i y) = f := funext fun y ↦ b.sum_repr' (f y)
    refine ⟨hx,?_⟩
    rw [← he]
    exact (lipschitzModulusWithin_sum_le Finset.univ g X x).trans_lt
      (ENNReal.sum_lt_top.mpr fun i _ ↦ hg i)

theorem strictlyContinuousAt_iff_inner (f : E → F) (x : E) :
    StrictlyContinuousAt f x ↔ ∀ v : F, StrictlyContinuousAt (fun y ↦ ⟪v,f y⟫_ℝ) x := by
  simpa only [StrictlyContinuousWithinAt,StrictlyContinuousAt,mem_univ,true_and] using
    strictlyContinuousWithinAt_iff_inner f (X := univ) (x := x) (mem_univ x)

end RW
