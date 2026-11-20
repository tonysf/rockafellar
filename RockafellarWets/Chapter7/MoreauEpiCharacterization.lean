/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Characterization by Moreau envelopes

The converse in Theorem 7.37 uses the same quadratic minorant twice. At a
small parameter it confines near-minimizers to any prescribed neighborhood
of the center. For a lower semicontinuous objective it also recovers its
value there as the positive parameter tends to zero.
-/

import RockafellarWets.Chapter7.MoreauEnvelopeLimits
import RockafellarWets.Chapter7.ExtendedUniformConvergence

open Bornology Filter Metric Set Topology

namespace RW

variable {E : Type*} [NormedAddCommGroup E]

private theorem moreau_le_at_center (f : E → EReal) (t : ℝ) (x : E) :
    moreauEnvelopeEReal f t x ≤ f x := by
  simpa [proximalObjectiveEReal] using (iInf_le (proximalObjectiveEReal f t x) x)

private theorem moreau_antitone_parameter (f : E → EReal) {s t : ℝ} (ht : 0 < t) (hts : t ≤ s)
    (x : E) : moreauEnvelopeEReal f s x ≤ moreauEnvelopeEReal f t x := by
  apply iInf_mono
  intro w
  apply add_le_add le_rfl
  apply EReal.coe_le_coe_iff.2
  exact mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le (by positivity) (by linarith)) (sq_nonneg _)

private theorem outside_ball_kernel_bound (b x : E) (β k A r : ℝ) (hk : 0 ≤ k) (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Ioo (0 : ℝ) δ, ∀ w : E, r ≤ ‖w-x‖ →
      A ≤ β - k*‖w-b‖^2 + (1/(2*t))*‖w-x‖^2 := by
  let C := A - β + 2*k*‖x-b‖^2
  let K := 1 + max 0 (C/r^2)
  have hK : 0 < K := by dsimp [K]; positivity
  have hKr : C ≤ K*r^2 := (div_le_iff₀ (sq_pos_of_pos hr)).1
    ((le_max_right 0 (C/r^2)).trans (by dsimp [K]; linarith))
  have hden : 0 < 2*(2*k+K) := by positivity
  refine ⟨1/(2*(2*k+K)), by positivity, fun t ht w hw ↦ ?_⟩
  have hcoef : 2*k+K ≤ 1/(2*t) := (le_div_iff₀ (by linarith [ht.1])).2
    (by nlinarith [(lt_div_iff₀ hden).1 ht.2])
  have htbound : ‖w-b‖ ≤ ‖w-x‖+‖x-b‖ := by simpa [dist_eq_norm] using dist_triangle w x b
  have hsquare : ‖w-b‖^2 ≤ 2*‖w-x‖^2+2*‖x-b‖^2 := by
    nlinarith [sq_le_sq' (by linarith [norm_nonneg (w-b), norm_nonneg (w-x), norm_nonneg (x-b)]) htbound,
      sq_nonneg (‖w-x‖ - ‖x-b‖)]
  dsimp [C] at hKr
  nlinarith [mul_le_mul_of_nonneg_left hsquare hk, mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖w-x‖),
    mul_le_mul_of_nonneg_left (sq_le_sq' (by linarith [norm_nonneg (w-x)]) hw) hK.le]

/-- At sufficiently small positive parameters the Moreau envelope of a
prox-bounded lower semicontinuous function exceeds any strict real lower
test value at the center. This includes centers of infinite cost. -/
theorem eventually_le_moreauEnvelope_at_zero {g : E → EReal} (hg : IsProxBounded g)
    (hl : LowerSemicontinuous g) {x : E} {a : ℝ} (ha : (a : EReal) < g x) :
    ∃ δ > 0, ∀ t ∈ Ioo (0 : ℝ) δ, (a : EReal) ≤ moreauEnvelopeEReal g t x := by
  obtain ⟨s, hs, b, henv⟩ := (isProxBounded_iff_exists_moreauEnvelopeEReal g).1 hg
  obtain ⟨β, _, hβ⟩ := EReal.exists_between_coe_real henv
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (hl x _ ha)
  let k := 1 / (2*s)
  obtain ⟨δ,hδ,hbound⟩ := outside_ball_kernel_bound b x β k a r (by dsimp [k]; positivity) hr
  refine ⟨δ,hδ, fun t ht ↦ le_iInf fun w ↦ ?_⟩
  have hminor := (le_moreauEnvelopeEReal_iff_quadratic_minorant s β b).1 hβ.le w
  by_cases hw : w ∈ ball x r
  · exact (hball hw).le.trans (le_add_of_nonneg_right (EReal.coe_nonneg.2 (by positivity [ht.1])))
  · have hb := hbound t ht w (by simpa only [← dist_eq_norm] using (le_of_not_gt (mem_ball.not.1 hw)))
    apply (EReal.coe_le_coe_iff.2 hb).trans
    rw [EReal.coe_add]
    exact add_le_add hminor le_rfl


/-- **Theorem 7.37**, pointwise convergence of all sufficiently small
envelopes forces eventual prox-boundedness and epi-convergence. -/
theorem epiConverges_of_tendsto_small_moreauEnvelopes {f : ℕ → E → EReal} {g : E → EReal}
    (hg : IsProxBounded g) (hl : LowerSemicontinuous g) {ε : ℝ} (hε : 0 < ε)
    (hc : ∀ t ∈ Ioo (0 : ℝ) ε, ∀ x : E, Tendsto (fun n ↦ moreauEnvelopeEReal (f n) t x) atTop
      (𝓝 (moreauEnvelopeEReal g t x))) : IsEventuallyProxBounded f ∧ EpiConverges f g := by
  obtain ⟨s, hs, b, hsb⟩ := (isProxBounded_iff_exists_moreauEnvelopeEReal g).1 hg
  obtain ⟨d, hd, hdsε⟩ := exists_between (lt_min hs hε)
  have hdε := hdsε.trans_le (min_le_right s ε)
  have hds := hdsε.trans_le (min_le_left s ε)
  have hdlim := hc d ⟨hd,hdε⟩ b
  have hdbot := hsb.trans_le (moreau_antitone_parameter g hd hds.le b)
  have hbound : IsEventuallyProxBounded f := ⟨d, hd, b, hdlim.liminf_eq.symm ▸ hdbot⟩
  obtain ⟨β, _, hβ⟩ := EReal.exists_between_coe_real hdbot
  have hmins : ∀ᶠ n in atTop, ∀ w : E, ((β-(1/(2*d))*‖w-b‖^2 : ℝ) : EReal) ≤ f n w :=
    (hdlim.eventually_const_lt hβ).mono fun n hn ↦ (le_moreauEnvelopeEReal_iff_quadratic_minorant d β b).1 hn.le
  have hlo : g ≤ epiLowerLimit f := by
    intro x
    by_contra! hx
    obtain ⟨a, hva, hag⟩ := EReal.exists_between_coe_real hx
    obtain ⟨δ,hδ,hM⟩ := eventually_le_moreauEnvelope_at_zero hg hl hag
    obtain ⟨t, ht, ht'⟩ := exists_between (lt_min hδ hε)
    obtain ⟨ys,hys,hyv⟩ := exists_tendsto_liminf_eq_epiLowerLimit f x
    have hv := (hc t ⟨ht, ht'.trans_le (min_le_right _ _)⟩ x).liminf_eq
    have hQ : Tendsto (fun n ↦ 1/(2*t)*‖ys n - x‖^2) atTop (𝓝 0) := by
      simpa using (((hys.sub_const x).norm.pow 2).const_mul (1/(2*t)))
    have hstep := liminf_le_liminf (f := atTop) (Eventually.of_forall fun n ↦ iInf_le (proximalObjectiveEReal (f n) t x) (ys n))
    change liminf (fun n ↦ moreauEnvelopeEReal (f n) t x) atTop ≤ _ at hstep
    have hfinal := (hM t ⟨ht, ht'.trans_le (min_le_left _ _)⟩).trans ((hv ▸ hstep).trans
      (liminf_add_tendsto_real_le (u := fun n ↦ f n (ys n)) hQ))
    exact hva.not_ge (by simpa [hyv] using hfinal)
  have hup : epiUpperLimit f ≤ g := by
    intro x
    apply (epiUpperLimit_le_iff_eventually f x (g x)).2
    intro V hV A hA
    obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.1 hV
    obtain ⟨δ,hδ,hout⟩ := outside_ball_kernel_bound b x β (1/(2*d)) A r (by positivity) hr
    obtain ⟨t, ht, ht'⟩ := exists_between (lt_min hδ hε)
    have hlt := (moreau_le_at_center g t x).trans_lt hA
    filter_upwards [hmins, (hc t ⟨ht, ht'.trans_le (min_le_right _ _)⟩ x).eventually_lt_const hlt] with n hn hnenv
    obtain ⟨w,hw⟩ := iInf_lt_iff.1 hnenv
    have hfe : w ∈ ball x r := by
      by_contra ho
      have hi := EReal.coe_le_coe_iff.2 (hout t ⟨ht, ht'.trans_le (min_le_left _ _)⟩ w
        (by simpa only [← dist_eq_norm] using (le_of_not_gt (mem_ball.not.1 ho))))
      rw [EReal.coe_add] at hi
      exact hw.not_ge (hi.trans (add_le_add (hn w) le_rfl))
    exact ⟨w, hball hfe, (le_add_of_nonneg_right (EReal.coe_nonneg.2 (by positivity))).trans hw.le⟩
  have horder := epiLowerLimit_le_epiUpperLimit f
  exact ⟨hbound, epiConverges_iff_epiLimits_eq.2
    ⟨le_antisymm (horder.trans hup) hlo, le_antisymm hup (hlo.trans horder)⟩⟩

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Theorem 7.37(a,b)**, full equivalence. -/
theorem epiConverges_iff_tendsto_small_moreauEnvelopes {f : ℕ → E → EReal} {g : E → EReal}
    (hf : ∀ n, LowerSemicontinuous (f n)) (hp : IsProper g) (hl : LowerSemicontinuous g) :
    (IsEventuallyProxBounded f ∧ EpiConverges f g) ↔
      IsProxBounded g ∧ ∃ ε > 0, ∀ t ∈ Ioo (0 : ℝ) ε, ∀ x : E,
        Tendsto (fun n ↦ moreauEnvelopeEReal (f n) t x) atTop (𝓝 (moreauEnvelopeEReal g t x)) := by
  constructor
  · rintro ⟨⟨s, hs, b, hb⟩, he⟩
    have hthr : (s : EReal) ≤ eventualProxThreshold f := le_iSup_of_le s (le_iSup_of_le ⟨hs,b,hb⟩ le_rfl)
    have hc (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) s) (x : E) :=
      tendsto_moreauEnvelopeEReal_of_epiConverges he hf hp (tendsto_const_nhds (x := x))
        (tendsto_const_nhds (x := t)) ht.1 ((EReal.coe_lt_coe_iff.2 ht.2).trans_le hthr)
    obtain ⟨t,ht,hts⟩ := exists_between hs
    obtain ⟨a,ha⟩ := (hc t ⟨ht,hts⟩ b).1
    exact ⟨(isProxBounded_iff_exists_moreauEnvelopeEReal g).2 ⟨t,ht,b,ha ▸ EReal.bot_lt_coe _⟩,
      s, hs, fun t ht x ↦ (hc t ht x).2⟩
  · rintro ⟨hg,ε,hε,hc⟩
    exact epiConverges_of_tendsto_small_moreauEnvelopes hg hl hε hc

/-- **Theorem 7.37**, continuous, uniform on bounded sets, and epigraphical
convergence of envelopes throughout the eventual threshold interval. -/
theorem moreauEnvelope_convergence_below_threshold {f : ℕ → E → EReal} {g : E → EReal}
    (h : EpiConverges f g) (hf : ∀ n, LowerSemicontinuous (f n)) (hg : IsProper g)
    {ts : ℕ → ℝ} {t : ℝ} (hts : Tendsto ts atTop (𝓝 t)) (ht : 0 < t)
    (hthr : (t : EReal) < eventualProxThreshold f) :
    let F := fun n ↦ moreauEnvelopeEReal (f n) (ts n)
    let G := moreauEnvelopeEReal g t
    (∀ x, ConvergesContinuouslyWithinAt F G univ x) ∧
      (∀ B : Set E, IsBounded B → ERealConvergesUniformlyOn F G B) ∧ EpiConverges F G := by
  let F := fun n ↦ moreauEnvelopeEReal (f n) (ts n)
  let G := moreauEnvelopeEReal g t
  have hcc (x : E) : ConvergesContinuouslyWithinAt F G univ x := fun xs _ hxs ↦
    (tendsto_moreauEnvelopeEReal_of_epiConverges h hf hg hxs hts ht hthr).2
  have hunif := (convergesContinuouslyOn_iff_continuousOn_and_erealConvergesUniformlyOn.1
    (fun x _ ↦ hcc x)).2
  refine ⟨hcc, fun B hb ρ hρ ↦ (hunif (closure B) (subset_univ _) hb.isCompact_closure ρ hρ).mono subset_closure,
    epiConverges_iff_liminf_limsup.2 (fun x ↦ ?_)⟩
  exact ⟨fun xs hx ↦ (hcc x xs (fun _ ↦ mem_univ _) hx).liminf_eq.ge,
    fun _ ↦ x, tendsto_const_nhds, (hcc x _ (fun _ ↦ mem_univ _) tendsto_const_nhds).limsup_eq.le⟩

/-- **Theorem 7.37**, ordinary real uniform convergence on bounded sets.
The approximating envelopes are eventually finite simultaneously throughout
the chosen set, so their real projections represent their actual values. -/
theorem moreauEnvelope_tendstoUniformlyOn_of_bounded {f : ℕ → E → EReal} {g : E → EReal}
    (h : EpiConverges f g) (hf : ∀ n, LowerSemicontinuous (f n)) (hg : IsProper g)
    {ts : ℕ → ℝ} {t : ℝ} (hts : Tendsto ts atTop (𝓝 t)) (ht : 0 < t)
    (hthr : (t : EReal) < eventualProxThreshold f) {B : Set E} (hb : IsBounded B) :
    let F := fun n ↦ moreauEnvelopeEReal (f n) (ts n)
    let G := moreauEnvelopeEReal g t
    (∀ᶠ n in atTop, ∀ x ∈ B, ((F n x).toReal : EReal) = F n x) ∧
      TendstoUniformlyOn (fun n x ↦ (F n x).toReal) (fun x ↦ (G x).toReal) atTop B := by
  let F := fun n ↦ moreauEnvelopeEReal (f n) (ts n)
  let G := moreauEnvelopeEReal g t
  have hcoe (x : E) : ((G x).toReal : EReal) = G x := by
    obtain ⟨a,ha⟩ := (tendsto_moreauEnvelopeEReal_of_epiConverges h hf hg (tendsto_const_nhds (x := x))
      hts ht hthr).1
    change ((moreauEnvelopeEReal g t x).toReal : EReal) = moreauEnvelopeEReal g t x
    rw [ha, EReal.toReal_coe]
  obtain ⟨hcc, hu, _⟩ := moreauEnvelope_convergence_below_threshold h hf hg hts ht hthr
  have hcc' : ∀ x ∈ (univ : Set E), ConvergesContinuouslyWithinAt
      (fun n y ↦ ((F n y).toReal : EReal)) (fun y ↦ ((G y).toReal : EReal)) univ x := by
    intro x _ ys hys hy
    apply EReal.tendsto_coe.2
    exact (EReal.tendsto_toReal ((hcoe x).symm.trans_ne (EReal.coe_ne_top _))
      ((hcoe x).symm.trans_ne (EReal.coe_ne_bot _))).comp (hcc x ys hys hy)
  obtain ⟨hcont,huni⟩ := convergesContinuouslyOn_iff_continuousOn_and_erealConvergesUniformlyOn.1 hcc'
  have hreal : Continuous (fun x ↦ (G x).toReal) := EReal.continuous_coe_iff.1 (continuousOn_univ.1 hcont)
  obtain ⟨M,hM⟩ := hb.isCompact_closure.bddAbove_image hreal.abs.continuousOn
  have hbound : ∀ x ∈ B, |(G x).toReal| ≤ max 0 M := fun x hx ↦
    (hM (mem_image_of_mem _ (subset_closure hx))).trans (le_max_right _ _)
  have hu' : ERealConvergesUniformlyOn F (fun x ↦ ((G x).toReal : EReal)) B := by
    simpa only [hcoe] using hu B hb
  refine ⟨?_, ERealConvergesUniformlyOn.tendstoUniformlyOn_of_bounded
    (fun ρ hρ ↦ (huni (closure B) (subset_univ _) hb.isCompact_closure ρ hρ).mono subset_closure)
    (le_max_left _ _) hbound⟩
  filter_upwards [hu'.eventually_bounded_of_bounded_limit (le_max_left _ _) hbound] with n hn
  intro x hx
  obtain ⟨r,hr,_⟩ := hn x hx
  change ((F n x).toReal : EReal) = F n x
  rw [hr, EReal.toReal_coe]

end RW
