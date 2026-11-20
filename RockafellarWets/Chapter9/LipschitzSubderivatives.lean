/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: Subderivatives of strictly continuous functions
-/

import RockafellarWets.Chapter9.SubgradientModulus
import Mathlib.Analysis.Normed.MulAction

open Filter Function Metric Set Topology
open scoped ENNReal NNReal InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → EReal} {x : E} {U : Set E} {k : ℝ≥0}

/-- Uniform comparison of the liminf and limsup of two families of
difference quotients with the same base points and scales. -/
private theorem differenceQuotient_compare {ι : Type*} {l : Filter ι} [l.NeBot]
    (hfin : ∀ z ∈ U, f z = ((f z).toReal : EReal)) (hL : LipschitzOnWith k (fun z ↦ (f z).toReal) U)
    (hU : U ∈ 𝓝 x) {y : ι → E} {t : ι → ℝ} {u v : ι → E} {a b : E}
    (hy : Tendsto y l (𝓝 x)) (ht : Tendsto t l (𝓝[>] 0)) (hu : Tendsto u l (𝓝 a))
    (hv : Tendsto v l (𝓝 b)) :
    let q := fun (g : ι → E) i ↦ differenceQuotient f (y i) (t i) (g i)
    liminf (q u) l ≤ ((k * dist a b : ℝ) : EReal) + liminf (q v) l ∧
    limsup (q u) l ≤ ((k * dist a b : ℝ) : EReal) + limsup (q v) l := by
  intro q
  let d := fun i ↦ ((k * dist (u i) (v i) : ℝ) : EReal)
  have hd : limsup d l = ((k * dist a b : ℝ) : EReal) := (EReal.tendsto_coe.mpr ((hu.dist hv).const_mul (k : ℝ))).limsup_eq
  have hpath {g : ι → E} {w : E} (hg : Tendsto g l (𝓝 w)) : ∀ᶠ i in l, y i + t i • g i ∈ U := by
    have h := hy.add ((ht.mono_right nhdsWithin_le_nhds).smul hg)
    simp only [zero_smul, add_zero] at h
    exact h.eventually hU
  have hcmp : q u ≤ᶠ[l] d + q v := by
    filter_upwards [hy.eventually hU, ht.eventually self_mem_nhdsWithin, hpath hu, hpath hv] with i hi ht hiu hiv
    change 0 < t i at ht
    change differenceQuotient f _ _ _ ≤ _ + differenceQuotient f _ _ _
    rw [differenceQuotient_eq_coe (hfin _ hi) (hfin _ hiu), differenceQuotient_eq_coe (hfin _ hi) (hfin _ hiv),
      ← EReal.coe_add, EReal.coe_le_coe_iff]
    have hb := hL.le_add_mul hiu hiv
    rw [dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_pos ht] at hb
    rw [inv_mul_le_iff₀ ht, mul_add, ← mul_assoc (t i) (t i)⁻¹, mul_inv_cancel₀ ht.ne', one_mul]
    linarith [mul_left_comm (t i) (k : ℝ) (dist (u i) (v i))]
  have hh₁ : limsup d l ≠ ⊥ := hd ▸ EReal.coe_ne_bot _
  have hh₂ : limsup d l ≠ ⊤ := hd ▸ EReal.coe_ne_top _
  exact ⟨(liminf_le_liminf hcmp).trans ((EReal.liminf_add_le (.inl hh₁) (.inl hh₂)).trans_eq (by rw [hd])),
    (limsup_le_limsup hcmp).trans ((EReal.limsup_add_le (.inl hh₁) (.inl hh₂)).trans_eq (by rw [hd]))⟩

private theorem fixedDirection_subderivative (hfin : ∀ z ∈ U, f z = ((f z).toReal : EReal))
    (hL : LipschitzOnWith k (fun z ↦ (f z).toReal) U) (hU : U ∈ 𝓝 x) (w : E) :
    subderivative f x w = liminf (fun t ↦ differenceQuotient f x t w) (𝓝[>] (0 : ℝ)) := by
  let L := 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w
  have ht : Tendsto (Prod.fst : ℝ × E → ℝ) L (𝓝[>] 0) := tendsto_fst
  have hv : Tendsto (Prod.snd : ℝ × E → E) L (𝓝 w) := tendsto_snd
  have hc : Tendsto (fun _ : ℝ × E ↦ w) L (𝓝 w) := tendsto_const_nhds
  have he : liminf (fun p : ℝ × E ↦ differenceQuotient f x p.1 w) L =
      liminf (fun t ↦ differenceQuotient f x t w) (𝓝[>] 0) := by
    change liminf ((fun t ↦ differenceQuotient f x t w) ∘ Prod.fst) L = _
    rw [liminf_comp, map_fst_prod]
  rw [← he]
  apply le_antisymm
  · simpa only [dist_self, mul_zero, EReal.coe_zero, zero_add] using
      (differenceQuotient_compare hfin hL hU tendsto_const_nhds ht hv hc).1
  · simpa only [dist_self, mul_zero, EReal.coe_zero, zero_add] using
      (differenceQuotient_compare hfin hL hU tendsto_const_nhds ht hc hv).1

/-- **Exercise 9.15**, the fixed-direction ordinary subderivative. -/
theorem ERealStrictlyContinuousAt.subderivative_eq_liminf (h : ERealStrictlyContinuousAt f x) (w : E) :
    subderivative f x w = liminf (fun t ↦ differenceQuotient f x t w) (𝓝[>] (0 : ℝ)) := by
  obtain ⟨k, hk, -⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h.2
  obtain ⟨U, hU, -, hfin, hL⟩ := h.exists_lipschitzOnWith hk
  exact fixedDirection_subderivative hfin hL hU w

private theorem subderivative_real_lipschitz (hfin : ∀ z ∈ U, f z = ((f z).toReal : EReal))
    (hL : LipschitzOnWith k (fun z ↦ (f z).toReal) U) (hU : U ∈ 𝓝 x) :
    (∀ w, subderivative f x w = ((subderivative f x w).toReal : EReal)) ∧
      LipschitzWith k (fun w ↦ (subderivative f x w).toReal) := by
  have hreal (w : E) : subderivative f x w = ((subderivative f x w).toReal : EReal) := by
    obtain ⟨hlo, hhi⟩ := subderivative_bounds_of_lipschitzOnWith hfin hL hU w
    exact (EReal.coe_toReal (hhi.trans_lt (EReal.coe_lt_top _)).ne ((EReal.bot_lt_coe _).trans_le hlo).ne').symm
  refine ⟨hreal, LipschitzWith.of_le_add_mul k fun a b ↦ ?_⟩
  have hh := (differenceQuotient_compare hfin hL hU (tendsto_const_nhds (x := x))
    (tendsto_id : Tendsto (fun t : ℝ ↦ t) (𝓝[>] 0) (𝓝[>] 0)) (tendsto_const_nhds (x := a)) (tendsto_const_nhds (x := b))).1
  change liminf (fun t ↦ differenceQuotient f x t a) _ ≤ _ + liminf (fun t ↦ differenceQuotient f x t b) _ at hh
  rw [← fixedDirection_subderivative hfin hL hU a, ← fixedDirection_subderivative hfin hL hU b,
    hreal a, hreal b, ← EReal.coe_add, EReal.coe_le_coe_iff] at hh
  linarith

theorem ERealStrictlyContinuousAt.subderivative_finite (h : ERealStrictlyContinuousAt f x) (w : E) :
    subderivative f x w = ((subderivative f x w).toReal : EReal) := by
  obtain ⟨k, hk, -⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h.2
  obtain ⟨U, hU, -, hfin, hL⟩ := h.exists_lipschitzOnWith hk
  exact (subderivative_real_lipschitz hfin hL hU).1 w

/-- **Exercise 9.15**, global Lipschitz continuity of the ordinary subderivative
with the exact modulus at the base point as the Lipschitz constant. -/
theorem ERealStrictlyContinuousAt.lipschitzWith_subderivative (h : ERealStrictlyContinuousAt f x) :
    LipschitzWith (lipschitzModulus (fun y ↦ (f y).toReal) x).toNNReal (fun w ↦ (subderivative f x w).toReal) := by
  let K := (lipschitzModulus (fun y ↦ (f y).toReal) x).toNNReal
  have he : (K : ℝ≥0∞) = lipschitzModulus (fun y ↦ (f y).toReal) x := ENNReal.coe_toNNReal h.2.ne
  apply LipschitzWith.of_dist_le_mul fun a b ↦ ?_
  apply ge_of_tendsto (x := 𝓝[>] K)
    ((NNReal.continuous_coe.tendsto K).mul_const (dist a b) |>.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin (a := K) (s := Ioi K)] with k hk
  obtain ⟨U, hU, -, hfin, hL⟩ := h.exists_lipschitzOnWith (he ▸ ENNReal.coe_lt_coe.mpr hk)
  exact (subderivative_real_lipschitz hfin hL hU).2.dist_le_mul a b

section Euclidean

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {g : F → EReal} {p : F}

/-- **Exercise 9.15**, the moving-base, fixed-direction formula for the regular subderivative. -/
theorem ERealStrictlyContinuousAt.regularSubderivative_eq_limsup_differenceQuotient
    (h : ERealStrictlyContinuousAt g p) (w : F) : regularSubderivative g p w =
      limsup (fun q : F × ℝ ↦ differenceQuotient g q.1 q.2 w) (𝓝 p ×ˢ 𝓝[>] (0 : ℝ)) := by
  rw [h.regularSubderivative_eq_upperDirectionalSlope, upperDirectionalSlope, h.attentiveNhds_eq]
  let B := 𝓝 p ×ˢ 𝓝[>] (0 : ℝ)
  let L := B ×ˢ 𝓝 w
  have hbase : Tendsto (Prod.fst : (F × ℝ) × F → F × ℝ) L B := tendsto_fst
  have hy := (show Tendsto (Prod.fst : F × ℝ → F) B (𝓝 p) from tendsto_fst).comp hbase
  have ht := (show Tendsto (Prod.snd : F × ℝ → ℝ) B (𝓝[>] 0) from tendsto_snd).comp hbase
  have hv : Tendsto (Prod.snd : (F × ℝ) × F → F) L (𝓝 w) := tendsto_snd
  have hc : Tendsto (fun _ : (F × ℝ) × F ↦ w) L (𝓝 w) := tendsto_const_nhds
  have he : limsup (fun q : (F × ℝ) × F ↦ differenceQuotient g q.1.1 q.1.2 w) L =
      limsup (fun q : F × ℝ ↦ differenceQuotient g q.1 q.2 w) B := by
    change limsup ((fun q : F × ℝ ↦ differenceQuotient g q.1 q.2 w) ∘ Prod.fst) L = _
    rw [limsup_comp, map_fst_prod]
  rw [← he]
  obtain ⟨k, hk, -⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h.2
  obtain ⟨U, hU, -, hfin, hL⟩ := h.exists_lipschitzOnWith hk
  apply le_antisymm
  · simpa only [dist_self, mul_zero, EReal.coe_zero, zero_add] using (differenceQuotient_compare hfin hL hU hy ht hv hc).2
  · simpa only [dist_self, mul_zero, EReal.coe_zero, zero_add] using (differenceQuotient_compare hfin hL hU hy ht hc hv).2

/-- **Exercise 9.15**, the regular subderivative as the upper limit of the
ordinary subderivatives with base point varying and direction fixed. -/
theorem ERealStrictlyContinuousAt.regularSubderivative_eq_limsup_subderivative
    (h : ERealStrictlyContinuousAt g p) (w : F) :
    regularSubderivative g p w = limsup (fun y ↦ subderivative g y w) (𝓝 p) := by
  obtain ⟨k, hk, -⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h.2
  obtain ⟨U, hU, hopen, hfin, hL⟩ := h.exists_lipschitzOnWith hk
  have hepi := epigraph_regularSubderivative_eq_inner_epigraph_subderivative h.isLocallyLscAt
  rw [h.attentiveNhds_eq] at hepi
  apply le_antisymm
  · by_contra! hh
    obtain ⟨b,hb,hb'⟩ := EReal.exists_between_coe_real hh
    apply hb'.not_ge
    change (w,b) ∈ epigraph (regularSubderivative g p)
    rw [hepi]
    intro V hV
    filter_upwards [eventually_lt_of_limsup_lt hb] with y hy
    exact ⟨(w,b),hy.le,mem_of_mem_nhds hV⟩
  · obtain ⟨v,hv,he,-⟩ := h.exists_max_inner_subdifferential w
    let r := ⟪v,w⟫_ℝ
    have hr : (w,r) ∈ innerSetLimitAlong (𝓝 p) (fun y ↦ epigraph (subderivative g y)) := hepi ▸ he.le
    rw [he]
    by_contra! hh
    obtain ⟨b,hb,hb'⟩ := EReal.exists_between_coe_real hh
    have hbr : r < b := EReal.coe_lt_coe_iff.mp hb
    let δ := (b-r) / (1+k)
    have hδ : 0 < δ := div_pos (sub_pos.mpr hbr) (by positivity)
    have heq : δ * (1+k) = b-r := div_mul_cancel₀ _ (by positivity)
    apply hb'.not_ge (limsup_le_of_le (f := 𝓝 p) (by isBoundedDefault) ?_)
    filter_upwards [hr (ball w δ ×ˢ ball r δ) (prod_mem_nhds (ball_mem_nhds _ hδ) (ball_mem_nhds _ hδ)), hU] with y hy hyU
    obtain ⟨⟨z,a⟩,hza,hz,ha⟩ := hy
    obtain ⟨hf,hk⟩ := subderivative_real_lipschitz hfin hL (hopen.mem_nhds hyU)
    have hza' : subderivative g y z ≤ (a : EReal) := hza
    rw [hf z, EReal.coe_le_coe_iff] at hza'
    rw [hf w, EReal.coe_le_coe_iff]
    have hd := hk.le_add_mul w z
    have hz' : dist w z ≤ δ := (dist_comm w z) ▸ (mem_ball.mp hz).le
    have ha' : a-r ≤ δ := (le_abs_self _).trans (mem_ball.mp ha).le
    nlinarith [mul_le_mul_of_nonneg_left hz' k.coe_nonneg]

/-- **Exercise 9.15**, global Lipschitz continuity of the regular subderivative. -/
theorem ERealStrictlyContinuousAt.lipschitzWith_regularSubderivative (h : ERealStrictlyContinuousAt g p) :
    LipschitzWith (lipschitzModulus (fun y ↦ (g y).toReal) p).toNNReal
      (fun w ↦ (regularSubderivative g p w).toReal) := by
  obtain ⟨v,hv,he,hm⟩ := h.exists_subgradient_norm_eq_modulus
  rw [he, ENNReal.toNNReal_coe]
  apply LipschitzWith.of_le_add_mul _ fun a b ↦ ?_
  obtain ⟨s,hs,ha,-⟩ := h.exists_max_inner_subdifferential a
  obtain ⟨z,hz,hb,hmax⟩ := h.exists_max_inner_subdifferential b
  rw [ha,hb,EReal.toReal_coe,EReal.toReal_coe,← sub_le_iff_le_add']
  have hh := real_inner_le_norm s (a-b)
  rw [inner_sub_right] at hh
  change ⟪s,a⟫_ℝ - ⟪z,b⟫_ℝ ≤ ‖v‖ * dist a b
  rw [dist_eq_norm]
  linarith [(mul_le_mul_of_nonneg_right (hm s hs) (norm_nonneg (a-b))), hmax s hs]

end Euclidean

end RW
