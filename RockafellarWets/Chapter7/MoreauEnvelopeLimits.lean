/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Limits of Moreau envelopes and proximal objectives

Theorem 7.37 uses the strict gap between a limiting parameter and the
threshold of eventual prox-boundedness. This gap makes the corresponding
proximal objectives eventually level bounded even when both the parameter
and the center vary.
-/

import RockafellarWets.Chapter7.EventualProxBoundedness
import RockafellarWets.Chapter7.ConvergenceInMinimization
import RockafellarWets.Chapter3.ExtendedProximalCancellationCompletion

open Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E]

/-- Adding a moving finite quadratic kernel preserves epi-convergence. -/
theorem epiConverges_proximalObjectives {f : ℕ → E → EReal} {g : E → EReal}
    (h : EpiConverges f g) {xs : ℕ → E} {x : E} (hxs : Tendsto xs atTop (𝓝 x))
    {ts : ℕ → ℝ} {t : ℝ} (hts : Tendsto ts atTop (𝓝 t)) (ht : t ≠ 0) :
    EpiConverges (fun n ↦ proximalObjectiveEReal (f n) (ts n) (xs n))
      (proximalObjectiveEReal g t x) := by
  let Q := fun (n : ℕ) (w : E) ↦ 1 / (2 * ts n) * ‖w - xs n‖ ^ 2
  let q := fun w : E ↦ 1 / (2 * t) * ‖w - x‖ ^ 2
  have hQ (w : E) {ws : ℕ → E} (hw : Tendsto ws atTop (𝓝 w)) :
      Tendsto (fun n ↦ (Q n (ws n) : EReal)) atTop (𝓝 (q w : EReal)) :=
    EReal.tendsto_coe.2 ((tendsto_const_nhds.div (tendsto_const_nhds.mul hts)
      (mul_ne_zero (by norm_num) ht)).mul (((hw.sub hxs).norm).pow 2))
  rw [epiConverges_iff_liminf_limsup]
  intro w
  constructor
  · intro ws hw
    apply le_trans _ (EReal.le_liminf_add (u := fun n ↦ f n (ws n))
      (v := fun n ↦ (Q n (ws n) : EReal)) (f := atTop))
    rw [(hQ w hw).liminf_eq]
    exact add_le_add ((epiConverges_iff_liminf_limsup.1 h w).1 ws hw) le_rfl
  · obtain ⟨ws, hw, hfw⟩ := h.exists_tendsto_values w
    have hsum := Filter.Tendsto.comp (EReal.continuousAt_add
      (p := (g w, (q w : EReal))) (.inr (EReal.coe_ne_bot _)) (.inr (EReal.coe_ne_top _)))
      (hfw.prodMk_nhds (hQ w hw))
    exact ⟨ws, hw, hsum.limsup_eq.le⟩

/-- Every strictly subthreshold positive parameter has a larger admissible
parameter and hence a common eventual quadratic minorant. -/
theorem exists_eventual_minorant_above_of_lt_eventualProxThreshold
    {f : ℕ → E → EReal} {t : ℝ} (ht : (t : EReal) < eventualProxThreshold f) :
    ∃ (s : ℝ) (_ : t < s) (_ : 0 < s) (b : E) (β : ℝ),
      ∀ᶠ n in atTop, ∀ w, ((β - (1 / (2 * s)) * ‖w - b‖ ^ 2 : ℝ) : EReal) ≤ f n w := by
  obtain ⟨s, hs⟩ := lt_iSup_iff.1 ht
  obtain ⟨⟨hspos, b, hb⟩, hts⟩ := lt_iSup_iff.1 hs
  obtain ⟨β, _, hβ⟩ := EReal.exists_between_coe_real hb
  exact ⟨s, EReal.coe_lt_coe_iff.1 hts, hspos, b, β,
    (eventually_lt_of_lt_liminf hβ).mono fun n hn ↦
      (le_moreauEnvelopeEReal_iff_quadratic_minorant s β b).1 hn.le⟩

variable [InnerProductSpace ℝ E]

/-- A quadratic minorant with parameter `s` and a positive upper bound `d < s`
on the regularization parameters give a common linear-growth lower bound. -/
private theorem affine_bound_for_proximalObjective {f : E → EReal} {s d t β R : ℝ}
    {x b : E} (ht : 0 < t) (htd : t ≤ d) (hds : d < s) (hR : ‖x - b‖ ≤ R)
    (hf : ∀ w, ((β - (1 / (2 * s)) * ‖w - b‖ ^ 2 : ℝ) : EReal) ≤ f w) (w : E) :
    let c := 1 / (2 * d) - 1 / (2 * s)
    let k := R / d
    ((‖w‖ + (β - (k + 1) ^ 2 / (4 * c) - ‖b‖) : ℝ) : EReal) ≤
      proximalObjectiveEReal f t x w := by
  dsimp only
  let c := 1 / (2 * d) - 1 / (2 * s)
  let k := R / d
  have hd : 0 < d := ht.trans_le htd
  have hs : 0 < s := hd.trans hds
  have hc : 0 < c := sub_pos.2 (one_div_lt_one_div_of_lt (by positivity) (by linarith))
  have hcoef : 1 / (2 * d) ≤ 1 / (2 * t) := one_div_le_one_div_of_le (by positivity) (by linarith)
  have hquad : ‖w - b‖ ^ 2 - 2 * ‖w - b‖ * R ≤ ‖w - x‖ ^ 2 := by
    have hrew : w - x = (w - b) - (x - b) := by abel
    rw [hrew, norm_sub_sq_real (w-b) (x-b)]
    have hinner := (le_abs_self ⟪w - b, x - b⟫_ℝ).trans (abs_real_inner_le_norm _ _)
    nlinarith [hinner.trans (mul_le_mul_of_nonneg_left hR (norm_nonneg (w-b))), sq_nonneg ‖x-b‖]
  have hsq : ‖w-b‖ - (k+1)^2/(4*c) ≤ c*‖w-b‖^2 - k*‖w-b‖ := by
    have := sq_nonneg (2*c*‖w-b‖ - (k+1))
    field_simp [hc.ne']
    nlinarith
  have hnorm : ‖w‖ - ‖b‖ ≤ ‖w-b‖ := by
    linarith [norm_le_norm_add_norm_sub' w b]
  have hk : k = 2 * (1 / (2 * d)) * R := by dsimp [k]; field_simp
  have hstep : ‖w‖ + (β - (k+1)^2/(4*c) - ‖b‖) ≤
      (β - 1/(2*s) * ‖w-b‖^2) + 1/(2*t)*‖w-x‖^2 := by
    rw [hk] at hsq
    dsimp [c] at hsq ⊢
    rw [hk]
    nlinarith [mul_le_mul_of_nonneg_left hquad (by positivity : 0 ≤ 1/(2*d)),
      mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖w-x‖)]
  apply (EReal.coe_le_coe_iff.2 hstep).trans
  rw [EReal.coe_add]
  exact add_le_add (hf w) le_rfl

/-- The moving proximal objectives are eventually level bounded below the
threshold. This supplies the compactness used by both 7.37 and 7.38. -/
theorem isEventuallyLevelBounded_proximalObjectives {f : ℕ → E → EReal}
    {xs : ℕ → E} {x : E} (hxs : Tendsto xs atTop (𝓝 x)) {ts : ℕ → ℝ} {t : ℝ}
    (hts : Tendsto ts atTop (𝓝 t)) (ht : 0 < t) (hthr : (t : EReal) < eventualProxThreshold f) :
    IsEventuallyLevelBounded (fun n ↦ proximalObjectiveEReal (f n) (ts n) (xs n)) := by
  obtain ⟨s, hts', _, b, β, hβ⟩ := exists_eventual_minorant_above_of_lt_eventualProxThreshold hthr
  obtain ⟨d, htd, hds⟩ := exists_between hts'
  let R := ‖x - b‖ + 1
  let c := 1 / (2 * d) - 1 / (2 * s)
  let k := R / d
  let B := β - (k + 1) ^ 2 / (4 * c) - ‖b‖
  have hR : ∀ᶠ n in atTop, ‖xs n - b‖ ≤ R :=
    (hxs.sub_const b).norm.eventually_le_const (lt_add_one _)
  intro a
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((hts.eventually_const_lt ht).and
    ((hts.eventually_le_const htd).and (hR.and hβ)))
  refine ⟨a - B, N, fun n hn w hw ↦ ?_⟩
  obtain ⟨hnpos, hnd, hnR, hnf⟩ := hN n hn
  have hw' := EReal.coe_le_coe_iff.1
    ((affine_bound_for_proximalObjective hnpos hnd hds hnR hnf w).trans hw)
  rw [mem_closedBall_zero_iff]
  exact le_sub_iff_add_le.2 hw'

variable [FiniteDimensional ℝ E]

/-- **Theorem 7.37**, convergence of envelopes for moving centers and moving
parameters below the threshold, with a finite limiting value. -/
theorem tendsto_moreauEnvelopeEReal_of_epiConverges {f : ℕ → E → EReal} {g : E → EReal}
    (h : EpiConverges f g) (hflsc : ∀ n, LowerSemicontinuous (f n)) (hg : IsProper g)
    {xs : ℕ → E} {x : E} (hxs : Tendsto xs atTop (𝓝 x)) {ts : ℕ → ℝ} {t : ℝ}
    (hts : Tendsto ts atTop (𝓝 t)) (ht : 0 < t) (hthr : (t : EReal) < eventualProxThreshold f) :
    (∃ a : ℝ, moreauEnvelopeEReal g t x = (a : EReal)) ∧
      Tendsto (fun n ↦ moreauEnvelopeEReal (f n) (ts n) (xs n)) atTop
        (𝓝 (moreauEnvelopeEReal g t x)) := by
  have hm := convergence_in_minimization (isEventuallyLevelBounded_proximalObjectives hxs hts ht hthr)
    (epiConverges_proximalObjectives h hxs hts ht.ne')
    (fun n ↦ lowerSemicontinuous_proximalObjectiveEReal (hflsc n) _ _) (isProper_proximalObjectiveEReal hg _ _)
  exact ⟨hm.1, hm.2.2.1⟩

end RW
