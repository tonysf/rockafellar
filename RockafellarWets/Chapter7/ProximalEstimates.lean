/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 7: Quantitative stability of Moreau envelopes and proximal points
-/

import RockafellarWets.Chapter3.ExtendedProximalCancellationCompletion
import RockafellarWets.Chapter7.SharpAuxEpiDistance

open Filter Metric Set Topology
open scoped NNReal

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem proximalObjective_chord {f : E → EReal} (hc : Convex ℝ (epigraph f))
    {lam : ℝ} {a x y : E} {u v t : ℝ} (ht : t ∈ Icc 0 1)
    (hx : proximalObjectiveEReal f lam a x ≤ (u : EReal))
    (hy : proximalObjectiveEReal f lam a y ≤ (v : EReal)) :
    proximalObjectiveEReal f lam a ((1-t) • x + t • y) ≤
      (((1-t)*u + t*v - (1/(2*lam))*t*(1-t)*‖x-y‖^2 : ℝ) : EReal) := by
  let c := 1 / (2 * lam)
  have hepi {w : E} {h : ℝ} (hw : proximalObjectiveEReal f lam a w ≤ (h : EReal)) :
      (w, h-c*‖w-a‖^2) ∈ epigraph f := by
    rw [mem_epigraph_iff, EReal.coe_sub]
    exact (EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))).2 hw
  have hz := hc (hepi hx) (hepi hy) (sub_nonneg.2 ht.2) ht.1 (by ring : 1-t+t=1)
  let z := (1-t) • x + t • y
  have hval : f z ≤ ((((1-t)*(u-c*‖x-a‖^2) + t*(v-c*‖y-a‖^2)) : ℝ) : EReal) := by
    simpa [z, mem_epigraph_iff, Prod.smul_mk, smul_eq_mul] using hz
  have hnorm : ‖z-a‖^2 = (1-t)*‖x-a‖^2 + t*‖y-a‖^2 - t*(1-t)*‖x-y‖^2 := by
    have hz' : z-a = (1-t) • (x-a) + t • (y-a) := by dsimp [z]; module
    have hxy : x-y = (x-a)-(y-a) := by abel
    rw [hz', norm_add_sq_real, hxy, norm_sub_sq_real (x-a) (y-a)]
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1, abs_of_nonneg (sub_nonneg.2 ht.2),
      real_inner_smul_left, real_inner_smul_right]
    ring
  calc
    proximalObjectiveEReal f lam a z ≤ _ := add_le_add_left hval (↑(c * ‖z-a‖^2) : EReal)
    _ = _ := by rw [← EReal.coe_add, hnorm]; congr 1; dsimp [c]; ring

/-- Formula 7(34). The increase from a proximal minimizer controls the
squared distance, with coefficient exactly `1 / (2 * lam)`. -/
theorem proximalObjectiveEReal_quadratic_growth {f : E → EReal} (hc : Convex ℝ (epigraph f))
    {lam : ℝ} {a x y : E} {m h : ℝ} (hx : x ∈ proximalMappingEReal f lam a)
    (hm : moreauEnvelopeEReal f lam a = (m : EReal))
    (hy : proximalObjectiveEReal f lam a y ≤ (h : EReal)) :
    m + (1 / (2 * lam)) * ‖x - y‖ ^ 2 ≤ h := by
  have hxv := (mem_proximalMappingEReal_iff.1 hx).1.trans hm
  have hbound (t : ℝ) (ht : 0 < t) (ht' : t ≤ 1) :
      m + (1/(2*lam))*(1-t)*‖x-y‖^2 ≤ h := by
    have hseg := proximalObjective_chord hc ⟨ht.le, ht'⟩ hxv.le hy
    have hmin : (m : EReal) ≤ proximalObjectiveEReal f lam a ((1-t) • x + t • y) := by
      rw [← hm]; exact iInf_le _ _
    have hreal := EReal.coe_le_coe_iff.1 (hmin.trans hseg)
    apply le_of_mul_le_mul_left (a := t) _ ht
    nlinarith only [hreal]
  have htend : Tendsto (fun t : ℝ ↦ m + (1/(2*lam))*(1-t)*‖x-y‖^2) (𝓝[>] 0)
      (𝓝 (m + (1/(2*lam))*‖x-y‖^2)) := by
    have hc' : Continuous (fun t : ℝ ↦ m + (1/(2*lam))*(1-t)*‖x-y‖^2) := by fun_prop
    simpa using (hc'.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  apply le_of_tendsto htend
  filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds]
    with t ht ht' using hbound t ht ht'.le

private theorem convex_levelSet_proximalObjective {f : E → EReal} (hc : Convex ℝ (epigraph f))
    {lam : ℝ} (hl : 0 < lam) (a : E) (h : ℝ) : Convex ℝ (levelSet (proximalObjectiveEReal f lam a) h) := by
  intro x hx y hy s t hs ht hst
  have hs' : s = 1-t := by linarith
  subst s
  have h := proximalObjective_chord hc ⟨ht, by linarith⟩ hx hy
  exact h.trans (EReal.coe_le_coe_iff.2 (by
    have hnon := mul_nonneg (mul_nonneg (mul_nonneg (by positivity : 0 ≤ 1 / (2*lam)) ht) hs)
      (sq_nonneg ‖x-y‖)
    linarith only [hnon]))

/-- The two estimates in Example 7.66 hold for any admissible comparison
radius whose induced displacement fits in the truncation ball. -/
theorem proximal_estimates_of_auxEpiAdmissible {f g : E → EReal}
    (hf : Convex ℝ (epigraph f)) (hg : Convex ℝ (epigraph g))
    {lam : ℝ} (hl : 0 < lam) {a x y : E} (hx : x ∈ proximalMappingEReal f lam a)
    (hy : y ∈ proximalMappingEReal g lam a) {m k : ℝ}
    (hm : moreauEnvelopeEReal f lam a = (m : EReal))
    (hk : moreauEnvelopeEReal g lam a = (k : EReal)) {r : ℝ≥0} {η : ℝ}
    (had : auxEpiAdmissible r (proximalObjectiveEReal f lam a) (proximalObjectiveEReal g lam a) η)
    (hfloor : -(r : ℝ) + η < m) (hroom : ‖x‖ + η + 2 * √(lam*η) < r) :
    |k - m| ≤ η ∧ ‖y - x‖ ≤ η + 2 * √(lam*η) := by
  have hn := had.1
  have hs := Real.sqrt_nonneg (lam*η)
  let F := proximalObjectiveEReal f lam a
  let G := proximalObjectiveEReal g lam a
  have hxv : F x = (m : EReal) := (mem_proximalMappingEReal_iff.1 hx).1.trans hm
  have hyv : G y = (k : EReal) := (mem_proximalMappingEReal_iff.1 hy).1.trans hk
  have hgm (z : E) : (k : EReal) ≤ G z := hk ▸ iInf_le _ z
  have hfm (z : E) : (m : EReal) ≤ F z := hm ▸ iInf_le _ z
  have hfloor' : -(r : ℝ) ≤ m := by linarith
  obtain ⟨z, hxz, hz⟩ := had.2.1 x (mem_closedBall_zero_iff.2 (by linarith))
  change G z ≤ max (F x) _ + _ at hz
  rw [hxv, max_eq_left (EReal.coe_le_coe_iff.2 hfloor'), ← EReal.coe_add] at hz
  have hkm : k ≤ m + η := EReal.coe_le_coe_iff.1 ((hgm z).trans hz)
  let S := levelSet G (m+η)
  have hzS : z ∈ S := hz
  have hyS : y ∈ S := hyv.le.trans (EReal.coe_le_coe_iff.2 hkm)
  have hcb {w : E} (hw : w ∈ S) (hrw : ‖w‖ ≤ r) : ‖w-x‖ ≤ η + 2 * √(lam*η) := by
    obtain ⟨v, hwv, hv⟩ := had.2.2 w (mem_closedBall_zero_iff.2 hrw)
    have hupper : F v ≤ (((m + 2*η : ℝ)) : EReal) := by
      have hmax : max (G w) (((-(r : ℝ)) : ℝ) : EReal) ≤ ((m+η : ℝ) : EReal) :=
        max_le hw (EReal.coe_le_coe_iff.2 (by linarith))
      refine hv.trans ((add_le_add_left hmax _).trans_eq ?_)
      rw [← EReal.coe_add]; congr 1; ring
    have hgr := proximalObjectiveEReal_quadratic_growth hf hx hm hupper
    have hq : ‖x-v‖^2 ≤ 4*lam*η := calc
      ‖x-v‖^2 = (2*lam)*((1/(2*lam))*‖x-v‖^2) := by field_simp
      _ ≤ (2*lam)*(2*η) := mul_le_mul_of_nonneg_left (by linarith only [hgr]) (by positivity)
      _ = _ := by ring
    have hdist : ‖x-v‖ ≤ 2 * √(lam*η) := by
      nlinarith only [hq, Real.sq_sqrt (mul_nonneg hl.le hn), hs, norm_nonneg (x-v)]
    calc
      ‖w-x‖ = dist w x := (dist_eq_norm _ _).symm
      _ ≤ dist w v + dist v x := dist_triangle _ _ _
      _ ≤ _ := add_le_add hwv (by simpa [dist_eq_norm, norm_sub_rev v x] using hdist)
  have hzball : ‖z‖ ≤ r := by
    have h := dist_triangle z x 0
    rw [dist_zero_right, dist_comm z x, dist_zero_right] at h
    linarith
  have hyball : ‖y‖ ≤ r := by
    by_contra! hyout
    have hconn := (convex_levelSet_proximalObjective hg hl a (m+η)).isPreconnected
    obtain ⟨w, hw, hwNorm⟩ := hconn.intermediate_value hzS hyS continuous_norm.continuousOn
      (show (r : ℝ) ∈ Icc ‖z‖ ‖y‖ from ⟨hzball, hyout.le⟩)
    have hclose := hcb hw hwNorm.le
    have hnorm := norm_add_le (w-x) x
    rw [sub_add_cancel] at hnorm
    linarith
  refine ⟨abs_le.2 ⟨?_, by linarith⟩, hcb hyS hyball⟩
  obtain ⟨v, _, hv⟩ := had.2.2 y (mem_closedBall_zero_iff.2 hyball)
  have hrev := (hfm v).trans hv
  change (m : EReal) ≤ max (G y) _ + _ at hrev
  rw [hyv] at hrev
  rcases le_total k (-(r : ℝ)) with h | h
  · rw [max_eq_right (EReal.coe_le_coe_iff.2 h), ← EReal.coe_add, EReal.coe_le_coe_iff] at hrev
    linarith
  · rw [max_eq_left (EReal.coe_le_coe_iff.2 h), ← EReal.coe_add, EReal.coe_le_coe_iff] at hrev
    linarith


/-- **Example 7.66 (proximal estimates).** The two envelopes and any
corresponding proximal points satisfy the printed moduli at a common center. -/
theorem proximal_estimates [FiniteDimensional ℝ E] {f g : E → EReal}
    (hf : Convex ℝ (epigraph f)) (hfl : LowerSemicontinuous f) (hfp : IsProper f)
    (hg : Convex ℝ (epigraph g)) (hgl : LowerSemicontinuous g) (hgp : IsProper g)
    {lam : ℝ} (hl : 0 < lam) {a x y : E} (hx : x ∈ proximalMappingEReal f lam a)
    (hy : y ∈ proximalMappingEReal g lam a) {b : ℝ} {r : ℝ≥0}
    (hm : ((-b : ℝ) : EReal) ≤ moreauEnvelopeEReal f lam a) (hb : ‖x‖ ≤ b)
    (hr : b + 8*lam < r)
    (hd : auxEpiDistance r (proximalObjectiveEReal f lam a) (proximalObjectiveEReal g lam a) ≤ 4*lam) :
    let d := auxEpiDistance r (proximalObjectiveEReal f lam a) (proximalObjectiveEReal g lam a)
    |(moreauEnvelopeEReal g lam a).toReal - (moreauEnvelopeEReal f lam a).toReal| ≤ d ∧
      ‖y-x‖ ≤ d + 2 * √(lam*d) := by
  let F := proximalObjectiveEReal f lam a
  let G := proximalObjectiveEReal g lam a
  let d := auxEpiDistance r F G
  let m := (moreauEnvelopeEReal f lam a).toReal
  let k := (moreauEnvelopeEReal g lam a).toReal
  change |k-m| ≤ d ∧ ‖y-x‖ ≤ d + 2 * √(lam*d)
  letI := FiniteDimensional.complete ℝ E
  obtain ⟨hmB, hmT⟩ := moreauEnvelopeEReal_finite hf hfl hfp hl a
  obtain ⟨hkB, hkT⟩ := moreauEnvelopeEReal_finite hg hgl hgp hl a
  have hm' : moreauEnvelopeEReal f lam a = (m : EReal) := (EReal.coe_toReal hmT.ne hmB.ne').symm
  have hk' : moreauEnvelopeEReal g lam a = (k : EReal) := (EReal.coe_toReal hkT.ne hkB.ne').symm
  have hmb := EReal.coe_le_coe_iff.1 (hm.trans_eq hm')
  have hF : (effectiveDomain F).Nonempty := (isProper_proximalObjectiveEReal hfp lam a).1
  have hG : (effectiveDomain G).Nonempty := (isProper_proximalObjectiveEReal hgp lam a).1
  have hnon : 0 ≤ d := auxEpiDistance_nonneg hF hG
  change d ≤ 4*lam at hd
  have hs : √(lam*d) ≤ 2*lam := by
    apply Real.sqrt_le_iff.2
    exact ⟨by positivity, by nlinarith [mul_le_mul_of_nonneg_left hd hl.le]⟩
  have had := auxEpiAdmissible_at_distance (r := r) (lowerSemicontinuous_proximalObjectiveEReal hfl lam a)
    (lowerSemicontinuous_proximalObjectiveEReal hgl lam a) hF hG
  exact proximal_estimates_of_auxEpiAdmissible hf hg hl hx hy hm' hk' had (by linarith) (by linarith)

end RW
