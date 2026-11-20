/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Local minimization on moving balls

Exercise 7.45 treats the center and radius as parameters. Negative radii give
empty feasible sets. The relative continuity proof includes zero radii.
-/

import RockafellarWets.Chapter7.ConstrainedSolutionMappings

open Bornology Filter Metric Set Topology

namespace RW

variable {E : Type*} [NormedAddCommGroup E]

/-- The feasible triples `(y,x,r)` of the moving-ball problem. -/
def ballConstraint (E : Type*) [PseudoMetricSpace E] : Set (E × (E × ℝ)) :=
  {z | dist z.1 z.2.1 ≤ z.2.2}

/-- The extended objective whose marginal is the local infimum in **7.45**. -/
noncomputable def localMinIntegrand (f : E → EReal) : E × (E × ℝ) → EReal :=
  constrainedObjective (f ∘ Prod.fst) (ballConstraint E)

/-- The center-radius pairs admitting a decision with finite-above objective. -/
def localMinDomain (f : E → EReal) : Set (E × ℝ) :=
  {p | 0 ≤ p.2 ∧ ((effectiveDomain f) ∩ closedBall p.1 p.2).Nonempty}

private theorem localMinIntegrand_feasible {f : E → EReal} {p : E × ℝ} {y : E}
    (hy : y ∈ closedBall p.1 p.2) : localMinIntegrand f (y,p) = f y := by
  classical
  simp [localMinIntegrand, constrainedObjective, ballConstraint, mem_closedBall.1 hy]

private theorem localMinIntegrand_mem_ball {f : E → EReal} {p : E × ℝ} {y : E}
    (hy : localMinIntegrand f (y,p) < ⊤) : y ∈ closedBall p.1 p.2 := by
  classical
  by_contra h
  simp [localMinIntegrand, constrainedObjective, ballConstraint, mt mem_closedBall.2 h] at hy

private theorem paramArgmin_localMinIntegrand_subset (f : E → EReal) (p : E × ℝ) :
    paramArgmin (localMinIntegrand f) p ⊆ closedBall p.1 p.2 := fun _ hy ↦
  localMinIntegrand_mem_ball (hy.1.trans_lt hy.2)

/-- The marginal of the moving-ball integrand is exactly the infimum on
the closed ball, including empty balls. -/
theorem valueFunction_localMinIntegrand (f : E → EReal) (p : E × ℝ) :
    valueFunction (localMinIntegrand f) p = infimumOn f (closedBall p.1 p.2) := by
  classical
  apply le_antisymm
  · exact le_infimumOn fun y hy ↦ (iInf_le (fun w ↦ localMinIntegrand f (w,p)) y).trans_eq
      (localMinIntegrand_feasible hy)
  · apply le_iInf
    intro y
    by_cases hy : y ∈ closedBall p.1 p.2
    · rw [localMinIntegrand_feasible hy]
      exact infimumOn_le hy
    · simp [localMinIntegrand, constrainedObjective, ballConstraint, mt mem_closedBall.2 hy]

/-- Membership in the local optimal set is attainment of the infimum on the
ball by a feasible point. -/
theorem mem_paramArgmin_localMinIntegrand (f : E → EReal) (p : E × ℝ) (y : E) :
    y ∈ paramArgmin (localMinIntegrand f) p ↔ y ∈ closedBall p.1 p.2 ∧
      f y = infimumOn f (closedBall p.1 p.2) ∧ f y < ⊤ := by
  constructor
  · intro hy
    have hw := paramArgmin_localMinIntegrand_subset f p hy
    obtain ⟨he,ht⟩ := (mem_paramArgmin_iff _ _ _).1 hy
    rw [localMinIntegrand_feasible hw, valueFunction_localMinIntegrand] at he
    exact ⟨hw,he,he.trans_lt (by rwa [← valueFunction_localMinIntegrand])⟩
  · rintro ⟨hw,he,ht⟩
    rw [mem_paramArgmin_iff, localMinIntegrand_feasible hw, valueFunction_localMinIntegrand]
    exact ⟨he,he.symm.trans_lt ht⟩

private theorem localMinIntegrand_isProper {f : E → EReal} (hp : IsProper f) :
    IsProper (localMinIntegrand f) := by
  classical
  obtain ⟨y, hy⟩ := hp.1
  refine ⟨⟨(y, y, 0), ?_⟩, ?_⟩
  · rw [localMinIntegrand_feasible (p := (y,(0:ℝ))) (mem_closedBall_self le_rfl)]
    exact hy
  · rintro ⟨w,p⟩
    by_cases hw : w ∈ closedBall p.1 p.2
    · rw [localMinIntegrand_feasible hw]
      exact hp.2 w
    · simp [localMinIntegrand, constrainedObjective, ballConstraint, mt mem_closedBall.2 hw]

private theorem localMinIntegrand_lsc {f : E → EReal} (hl : LowerSemicontinuous f) :
    LowerSemicontinuous (localMinIntegrand f) :=
  lowerSemicontinuous_constrainedObjective (isClosed_le (by fun_prop) (by fun_prop))
    ((hl.comp continuous_fst).lowerSemicontinuousOn _)

/-- A single ball contains all feasible decisions as the input varies within
unit distance of a fixed center-radius pair. -/
private theorem moving_ball_bound {p q : E × ℝ} (hq : q ∈ closedBall p 1)
    {y : E} (hy : y ∈ closedBall q.1 q.2) : y ∈ closedBall p.1 (p.2 + 2) := by
  have hc := (max_le_iff.1 (show max (dist q.1 p.1) (dist q.2 p.2) ≤ 1 from hq))
  have hr := (abs_le.1 (show |q.2 - p.2| ≤ 1 from hc.2)).2
  exact mem_closedBall.2 (by linarith [dist_triangle y q.1 p.1, mem_closedBall.1 hy, hc.1])

private theorem localMinIntegrand_levelBounded (f : E → EReal) :
    IsLevelBoundedInXLocallyUniformly (localMinIntegrand f) := by
  intro p a
  refine ⟨1, one_pos, (isBounded_closedBall.prod isBounded_closedBall).subset
    (t := closedBall p.1 (p.2+2) ×ˢ closedBall p 1) ?_⟩
  rintro ⟨y,q⟩ ⟨⟨_, hq⟩, hy⟩
  exact ⟨moving_ball_bound hq (localMinIntegrand_mem_ball (lt_of_le_of_lt hy (EReal.coe_lt_top a))), hq⟩

theorem effectiveDomain_localMinValue (f : E → EReal) :
    effectiveDomain (valueFunction (localMinIntegrand f)) = localMinDomain f := by
  ext p
  constructor
  · intro hp
    change (⨅ y, localMinIntegrand f (y,p)) < ⊤ at hp
    obtain ⟨y, hy⟩ := iInf_lt_iff.1 hp
    have hb := localMinIntegrand_mem_ball hy
    exact ⟨dist_nonneg.trans (mem_closedBall.1 hb), y, (localMinIntegrand_feasible (f := f) hb).symm.trans_lt hy, hb⟩
  · rintro ⟨_, y, hy, hb⟩
    change (⨅ y, localMinIntegrand f (y,p)) < ⊤
    apply (iInf_le _ y).trans_lt
    rwa [localMinIntegrand_feasible hb]

/-- **Exercise 7.45**, the interior is exactly the set of parameters with
a strictly feasible finite-above decision. -/
theorem interior_localMinDomain (f : E → EReal) : interior (localMinDomain f) =
    {p | 0 < p.2 ∧ ((effectiveDomain f) ∩ ball p.1 p.2).Nonempty} := by
  ext p
  constructor
  · intro hp
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hp)
    have hin : (p.1, p.2 - δ/2) ∈ ball p δ := by
      simp only [mem_ball, Prod.dist_eq, dist_self, Real.dist_eq, sub_sub_cancel_left,
        abs_neg, abs_of_pos (half_pos hδ), max_eq_right (half_pos hδ).le]
      exact half_lt_self hδ
    obtain ⟨hr, y, hy, hb⟩ := hball hin
    exact ⟨by dsimp at hr; linarith, y, hy,
      mem_ball.2 (by have := mem_closedBall.1 hb; dsimp at this; linarith)⟩
  · rintro ⟨_, y, hy, hb⟩
    let O : Set (E × ℝ) := {q | dist y q.1 < q.2}
    have hopen : IsOpen O := isOpen_lt (by fun_prop) continuous_snd
    have hsub : O ⊆ localMinDomain f := fun q hq ↦
      ⟨dist_nonneg.trans (show dist y q.1 < q.2 from hq).le, y, hy, (show dist y q.1 < q.2 from hq).le⟩
    exact interior_maximal hsub hopen hb

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A proper lower semicontinuous objective with locally uniform level bounds
has a lower semicontinuous marginal. -/
theorem lowerSemicontinuous_valueFunction_of_localUniform {U : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] {g : E × U → EReal} (hl : LowerSemicontinuous g)
    (hp : IsProper g) (hb : IsLevelBoundedInXLocallyUniformly g) : LowerSemicontinuous (valueFunction g) := by
  apply (lsc_iff_epigraph_closed_ereal _).2
  apply isSeqClosed_iff_isClosed.1
  intro zs p hzs hto
  choose xs hxs using fun n ↦ paramArgmin_nonempty hl hp hb
    (lt_of_le_of_lt (hzs n) (EReal.coe_lt_top _))
  obtain ⟨R, N, hN⟩ := isEventuallyLevelBounded_slices hb hto.fst_nhds (p.2+1)
  have hex : ∀ᶠ n in atTop, xs n ∈ closedBall 0 R := by
    filter_upwards [eventually_ge_atTop N, hto.snd_nhds.eventually_le_const (lt_add_one p.2)] with n hn ha
    exact hN n hn ((hxs n).1.trans_le ((hzs n).trans (EReal.coe_le_coe_iff.2 ha)))
  obtain ⟨x, _, φ, hφ, hxt⟩ := (isCompact_closedBall _ _).tendsto_subseq' hex.frequently
  have hmem := (isClosed_epigraph_of_lsc_ereal g hl).mem_of_tendsto
    ((hxt.prodMk_nhds (hto.fst_nhds.comp hφ.tendsto_atTop)).prodMk_nhds (hto.snd_nhds.comp hφ.tendsto_atTop))
    (Eventually.of_forall (fun n ↦ (hxs (φ n)).1.trans_le (hzs (φ n))))
  exact (iInf_le (fun y ↦ g (y,p.1)) x).trans hmem

/-- **Exercise 7.45**, properness, lower semicontinuity, closed optimal sets,
local boundedness and the common domain. -/
theorem localMinValue_and_argmin {f : E → EReal} (hp : IsProper f) (hl : LowerSemicontinuous f) :
    let g := localMinIntegrand f
    IsProper (valueFunction g) ∧ LowerSemicontinuous (valueFunction g) ∧
      (∀ p, IsClosed (paramArgmin g p)) ∧ SvLocallyBounded (paramArgmin g) ∧
      effectiveDomain (valueFunction g) = localMinDomain f ∧ svDom (paramArgmin g) = localMinDomain f := by
  have hpg := localMinIntegrand_isProper hp
  have hlg := localMinIntegrand_lsc hl
  have hbg := localMinIntegrand_levelBounded f
  obtain ⟨hcomp, hdom⟩ := paramArgmin_compact_and_dom hlg hpg hbg
  refine ⟨isProper_valueFunction_of_lsc_localUniform hlg hpg hbg,
    lowerSemicontinuous_valueFunction_of_localUniform hlg hpg hbg, fun p ↦ (hcomp p).isClosed, ?_,
    effectiveDomain_localMinValue f, hdom.trans (effectiveDomain_localMinValue f)⟩
  intro p
  refine ⟨closedBall p 1, closedBall_mem_nhds _ one_pos, isBounded_closedBall.subset
    (t := closedBall p.1 (p.2+2)) ?_⟩
  intro y hy
  obtain ⟨q,hq,hyq⟩ := mem_svImage.1 hy
  exact moving_ball_bound hq (paramArgmin_localMinIntegrand_subset f q hyq)

omit [FiniteDimensional ℝ E] in
private theorem localMinIntegrand_convex {f : E → EReal} (hc : Convex ℝ (epigraph f)) :
    Convex ℝ (epigraph (localMinIntegrand f)) := by
  rintro ⟨⟨y,p⟩, a⟩ hva ⟨⟨z,q⟩, b⟩ hvb s t hs ht hst
  have hy := localMinIntegrand_mem_ball (lt_of_le_of_lt hva (EReal.coe_lt_top a))
  have hz := localMinIntegrand_mem_ball (lt_of_le_of_lt hvb (EReal.coe_lt_top b))
  have hy' : f y ≤ (a : EReal) := (localMinIntegrand_feasible (f := f) hy).symm.trans_le hva
  have hz' : f z ≤ (b : EReal) := (localMinIntegrand_feasible (f := f) hz).symm.trans_le hvb
  have hfeas : s • y + t • z ∈ closedBall (s • p.1 + t • q.1) (s*p.2+t*q.2) := by
    rw [mem_closedBall, dist_eq_norm]
    have heq : s • y + t • z - (s • p.1 + t • q.1) = s • (y-p.1) + t • (z-q.1) := by
      simp only [smul_sub]; abel
    rw [heq]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hs, abs_of_nonneg ht]
    exact add_le_add (mul_le_mul_of_nonneg_left (by simpa [dist_eq_norm] using mem_closedBall.1 hy) hs)
      (mul_le_mul_of_nonneg_left (by simpa [dist_eq_norm] using mem_closedBall.1 hz) ht)
  change localMinIntegrand f (s • y + t • z, s • p + t • q) ≤ _
  rw [localMinIntegrand_feasible hfeas]
  exact hc (x := (y,a)) hy' (y := (z,b)) hz' hs ht hst

/-- **Exercise 7.45**, the convex case on the interior of the common domain. -/
theorem localMinValue_continuous_of_convex {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) {p : E × ℝ}
    (hd : p ∈ interior (localMinDomain f)) :
    ContinuousAt (valueFunction (localMinIntegrand f)) p ∧
      SvOscAt (paramArgmin (localMinIntegrand f)) p := by
  rw [← effectiveDomain_localMinValue] at hd
  obtain ⟨hval, _, hosc⟩ := convex_paramArgmin_interior (f := localMinIntegrand f) (u := p) (localMinIntegrand_lsc hl)
    (localMinIntegrand_isProper hp) (localMinIntegrand_levelBounded f) (localMinIntegrand_convex hc)
    hd
  exact ⟨hval, hosc⟩

omit [FiniteDimensional ℝ E] in
/-- A point in the closed limiting ball can be followed through nonnegative
radii, including the case of a limiting ball of radius zero. -/
private theorem exists_tendsto_mem_moving_ball {ps : ℕ → E × ℝ} {p : E × ℝ}
    (ht : Tendsto ps atTop (𝓝 p)) (hr : ∀ n, 0 ≤ (ps n).2) {y : E} (hy : y ∈ closedBall p.1 p.2) :
    ∃ ys : ℕ → E, Tendsto ys atTop (𝓝 y) ∧ ∀ n, ys n ∈ closedBall (ps n).1 (ps n).2 := by
  rcases (dist_nonneg.trans (mem_closedBall.1 hy)).eq_or_lt with hzero | hpos
  · have heq : y = p.1 := dist_le_zero.1 (hzero ▸ mem_closedBall.1 hy)
    exact ⟨fun n ↦ (ps n).1, heq ▸ ht.fst_nhds, fun n ↦ mem_closedBall_self (hr n)⟩
  · let ys := fun n ↦ (ps n).1 + ((ps n).2 / p.2) • (y-p.1)
    refine ⟨ys, ?_, fun n ↦ ?_⟩
    · simpa [div_self hpos.ne', add_sub_cancel] using
        ht.fst_nhds.add ((ht.snd_nhds.div_const p.2).smul_const (y-p.1))
    · rw [mem_closedBall, dist_eq_norm]
      simp only [ys, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hr n) hpos.le)]
      calc
        (ps n).2 / p.2 * ‖y-p.1‖ ≤ (ps n).2 / p.2 * p.2 :=
          mul_le_mul_of_nonneg_left (by simpa [dist_eq_norm] using mem_closedBall.1 hy) (div_nonneg (hr n) hpos.le)
        _ = _ := div_mul_cancel₀ _ hpos.ne'

/-- **Exercise 7.45**, continuity of the objective gives continuity of the
marginal and relative outer semicontinuity on the full feasible domain. -/
theorem localMinValue_continuous_of_continuous {f : E → EReal} (hp : IsProper f) (hc : Continuous f) :
    ContinuousOn (valueFunction (localMinIntegrand f)) (localMinDomain f) ∧
      SvOscOn (paramArgmin (localMinIntegrand f)) (localMinDomain f) := by
  have hl := localMinIntegrand_lsc hc.lowerSemicontinuous
  suffices h : ContinuousOn (valueFunction (localMinIntegrand f)) (localMinDomain f) from
    ⟨h, fun p hD ↦ svOscWithinAt_paramArgmin hl ((Set.ext_iff.1 (effectiveDomain_localMinValue f) p).2 hD)
      (h p hD).upperSemicontinuousWithinAt⟩
  intro p hD
  apply continuousWithinAt_valueFunction_of_epiContinuousWithinAt hl (localMinIntegrand_isProper hp)
    (localMinIntegrand_levelBounded f) hD ((Set.ext_iff.1 (effectiveDomain_localMinValue f) p).2 hD)
  refine ⟨(epiLscWithinAt_iff_forall_liminf hD).2 (fun ps _ hps x xs hxs ↦
    (epiLscAt_iff_forall_liminf.1 ((forall_epiLscAt_iff_lowerSemicontinuous _).2 hl p)) ps hps x xs hxs),
    (epiUscWithinAt_iff_exists_limsup hD).2 ?_⟩
  intro ps hDps hps y
  by_cases hy : localMinIntegrand f (y,p) < ⊤
  · have hb := localMinIntegrand_mem_ball hy
    obtain ⟨ys, hys, hw⟩ := exists_tendsto_mem_moving_ball hps (fun n ↦ (hDps n).1) hb
    refine ⟨ys, hys, ?_⟩
    simp only [localMinIntegrand_feasible (hw _), localMinIntegrand_feasible hb]
    exact ((hc.tendsto y).comp hys).limsup_eq.le
  · exact ⟨fun _ ↦ y, tendsto_const_nhds, (eq_top_iff.2 (le_of_not_gt hy)) ▸ le_top⟩

/-- **Exercise 7.45**, strict convexity makes the solution unique at every
feasible parameter and continuous relative to the common domain. -/
theorem localMinArgmin_continuous_of_strictConvex {f : E → EReal} (hp : IsProper f) (hc : Continuous f)
    (hs : StrictConvexOn ℝ (effectiveDomain f) (fun x ↦ (f x).toReal)) :
    ∀ p ∈ localMinDomain f, (∃ x, paramArgmin (localMinIntegrand f) p = {x}) ∧
      SvContinuousWithinAt (paramArgmin (localMinIntegrand f)) (localMinDomain f) p := by
  intro p hD
  let g := fun y ↦ localMinIntegrand f (y,p)
  have hdom : effectiveDomain g = effectiveDomain f ∩ closedBall p.1 p.2 := by
    ext y
    constructor
    · intro hy
      have hw := localMinIntegrand_mem_ball hy
      exact ⟨(localMinIntegrand_feasible (f := f) hw).symm.trans_lt hy, hw⟩
    · rintro ⟨hy,hw⟩
      change localMinIntegrand f (y,p) < ⊤
      rwa [localMinIntegrand_feasible hw]
  have hsg : StrictConvexOn ℝ (effectiveDomain g) (fun y ↦ (g y).toReal) := by
    rw [hdom]
    exact (hs.subset inter_subset_left (hs.1.inter (convex_closedBall _ _))).congr
      (fun _ hy ↦ congrArg EReal.toReal (localMinIntegrand_feasible hy.2).symm)
  have hpg := localMinIntegrand_isProper hp
  have hlg := localMinIntegrand_lsc hc.lowerSemicontinuous
  have hbg := localMinIntegrand_levelBounded f
  have hf : ∀ q ∈ localMinDomain f, valueFunction (localMinIntegrand f) q < ⊤ :=
    fun q hq ↦ (Set.ext_iff.1 (effectiveDomain_localMinValue f) q).2 hq
  obtain ⟨x,hx⟩ := paramArgmin_nonempty hlg hpg hbg (hf p hD)
  have hsing := (argmin_subsingleton_of_strictConvexOn (fun x ↦ hpg.2 (x,p)) hsg).eq_singleton_of_mem hx
  exact ⟨⟨x, hsing⟩, svContinuousWithinAt_paramArgmin hlg hpg hbg hf hD
    ((localMinValue_continuous_of_continuous hp hc).1 p hD) hsing⟩

end RW
