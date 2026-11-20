/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: Strict continuity of extended-real functions
-/

import RockafellarWets.Chapter9.LipschitzModulus
import RockafellarWets.Chapter8.InteriorRegularSubderivatives

open Filter Function Metric Set Topology
open scoped ENNReal NNReal

namespace RW

variable {E : Type*} [NormedAddCommGroup E]

/-- The finite real representative is locally Lipschitz, and the function
takes finite values on a whole neighborhood. -/
def ERealStrictlyContinuousAt (f : E → EReal) (x : E) : Prop :=
  (∀ᶠ y in 𝓝 x, f y = ((f y).toReal : EReal)) ∧ StrictlyContinuousAt (fun y ↦ (f y).toReal) x

theorem ERealStrictlyContinuousAt.finite {f : E → EReal} {x : E} (h : ERealStrictlyContinuousAt f x) :
    f x = ((f x).toReal : EReal) := mem_of_mem_nhds (s := {y | f y = ((f y).toReal : EReal)}) h.1

theorem ERealStrictlyContinuousAt.continuousAt {f : E → EReal} {x : E} (h : ERealStrictlyContinuousAt f x) :
    ContinuousAt f x := by
  have he : f =ᶠ[𝓝 x] fun y ↦ ((f y).toReal : EReal) := h.1
  exact (continuous_coe_real_ereal.continuousAt.comp h.2.continuousAt).congr he.symm

theorem ERealStrictlyContinuousAt.attentiveNhds_eq {f : E → EReal} {x : E} (h : ERealStrictlyContinuousAt f x) :
    attentiveNhds f x = 𝓝 x := inf_eq_left.mpr h.continuousAt.le_comap

theorem ERealStrictlyContinuousAt.exists_lipschitzOnWith {f : E → EReal} {x : E} (h : ERealStrictlyContinuousAt f x)
    {k : ℝ≥0} (hk : lipschitzModulus (fun y ↦ (f y).toReal) x < (k : ℝ≥0∞)) :
    ∃ U ∈ 𝓝 x, IsOpen U ∧ (∀ y ∈ U, f y = ((f y).toReal : EReal)) ∧ LipschitzOnWith k (fun y ↦ (f y).toReal) U := by
  obtain ⟨V, hV, hL⟩ := exists_lipschitzOnWith_of_modulus_lt hk
  obtain ⟨U, hsub, hopen, hmem⟩ := _root_.mem_nhds_iff.mp (inter_mem hV h.1)
  exact ⟨U, hopen.mem_nhds hmem, hopen, fun _ hy ↦ (hsub hy).2, hL.mono (hsub.trans inter_subset_left)⟩

theorem ERealStrictlyContinuousAt.isLocallyLscAt {f : E → EReal} {x : E} (h : ERealStrictlyContinuousAt f x) :
    IsLocallyLscAt f x := by
  obtain ⟨k, hk, -⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h.2
  obtain ⟨U, hU, -, hfin, hkU⟩ := h.exists_lipschitzOnWith hk
  obtain ⟨d, hd, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hU
  refine ⟨h.finite ▸ EReal.coe_ne_bot _, h.finite ▸ EReal.coe_ne_top _, d, hd, fun a _ ↦ ?_⟩
  have he : closedBall x d ∩ {y | f y ≤ (a : EReal)} =
      closedBall x d ∩ (fun y ↦ (f y).toReal) ⁻¹' Iic a := by
    ext y
    constructor
    · rintro ⟨hy, hf⟩
      exact ⟨hy, EReal.coe_le_coe_iff.mp (hfin y (hsub hy) ▸ hf)⟩
    · rintro ⟨hy, hf⟩
      exact ⟨hy, (hfin y (hsub hy)).le.trans (EReal.coe_le_coe_iff.mpr hf)⟩
  rw [he]
  exact (hkU.mono hsub).continuousOn.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_Iic

variable [NormedSpace ℝ E]

/-- Real-value difference-quotient bound at two feasible points of a
Lipschitz neighborhood, with no restriction on the direction's size. -/
theorem abs_differenceQuotient_le_of_lipschitzOnWith {f : E → EReal} {U : Set E} {k : ℝ≥0}
    (hfin : ∀ y ∈ U, f y = ((f y).toReal : EReal)) (hf : LipschitzOnWith k (fun y ↦ (f y).toReal) U)
    {y w : E} {t : ℝ} (hy : y ∈ U) (hz : y + t • w ∈ U) (ht : 0 < t) :
    ∃ r : ℝ, differenceQuotient f y t w = r ∧ |r| ≤ k * ‖w‖ := by
  refine ⟨_, differenceQuotient_eq_coe (hfin y hy) (hfin _ hz), ?_⟩
  have h := hf.dist_le_mul _ hz _ hy
  rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht] at h
  rw [abs_mul, abs_of_pos (inv_pos.mpr ht), inv_mul_le_iff₀ ht]
  simpa only [mul_left_comm] using h

theorem subderivative_bounds_of_lipschitzOnWith {f : E → EReal} {U : Set E} {k : ℝ≥0}
    (hfin : ∀ y ∈ U, f y = ((f y).toReal : EReal)) (hf : LipschitzOnWith k (fun y ↦ (f y).toReal) U)
    {y : E} (hy : U ∈ 𝓝 y) (w : E) :
    ((-(k * ‖w‖) : ℝ) : EReal) ≤ subderivative f y w ∧ subderivative f y w ≤ ((k * ‖w‖ : ℝ) : EReal) := by
  let L := 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w
  have ht : Tendsto (fun p : ℝ × E ↦ p.1) L (𝓝 0) := tendsto_fst.mono_right nhdsWithin_le_nhds
  have hw : Tendsto (fun p : ℝ × E ↦ p.2) L (𝓝 w) := tendsto_snd
  have hz : Tendsto (fun p : ℝ × E ↦ y + p.1 • p.2) L (𝓝 y) := by
    simpa only [zero_smul, add_zero] using ((tendsto_const_nhds (x := y)).add (ht.smul hw))
  have hbo : ∀ᶠ p : ℝ × E in L,
      ((-(k * ‖p.2‖) : ℝ) : EReal) ≤ differenceQuotient f y p.1 p.2 ∧
        differenceQuotient f y p.1 p.2 ≤ ((k * ‖p.2‖ : ℝ) : EReal) := by
    filter_upwards [hz.eventually hy, tendsto_fst.eventually (show ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t from self_mem_nhdsWithin)] with p hp ht
    obtain ⟨r, hr, hb⟩ := abs_differenceQuotient_le_of_lipschitzOnWith hfin hf (mem_of_mem_nhds hy) hp ht
    rw [hr]
    exact ⟨EReal.coe_le_coe_iff.mpr (abs_le.mp hb).1, EReal.coe_le_coe_iff.mpr (abs_le.mp hb).2⟩
  have hhi := EReal.tendsto_coe.mpr (hw.norm.const_mul (k : ℝ))
  have hlo := EReal.tendsto_coe.mpr (hw.norm.const_mul (k : ℝ)).neg
  exact ⟨hlo.liminf_eq.symm.trans_le (liminf_le_liminf (hbo.mono fun _ h ↦ h.1)),
    (liminf_le_liminf (hbo.mono fun _ h ↦ h.2)).trans_eq hhi.liminf_eq⟩

end RW
