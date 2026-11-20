/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Optimal-set mappings

Theorem 7.41. The printed attentive convergence uses the extended-real
topology. At an infeasible limiting parameter the limiting optimal set is
empty, so the attentive outer semicontinuity assertion requires a feasible
limit. The endpoint obstruction is proved in `attentiveArgmin_top_obstruction`.
-/

import RockafellarWets.Chapter7.ParameterEpiContinuity
import RockafellarWets.Chapter7.ConvergenceInMinimization
import RockafellarWets.Chapter5.OptimalSetMappings
import RockafellarWets.Chapter5.ConvexSemicontinuity

open Bornology Filter Metric Set Topology

namespace RW

/-- Convergence on the graph of an extended-real value function. -/
def AttentiveTendsto {U : Type*} [TopologicalSpace U] (p : U → EReal) (us : ℕ → U) (u : U) :
    Prop := Tendsto us atTop (𝓝 u) ∧ Tendsto (p ∘ us) atTop (𝓝 (p u))

variable {E U : Type*} [NormedAddCommGroup E] [NormedAddCommGroup U]
variable {f : E × U → EReal} {u : U} {D : Set U}

/-- **Theorem 7.41(a)**, attentive outer semicontinuity at every feasible limit. -/
theorem mem_paramArgmin_of_attentiveTendsto (hf : LowerSemicontinuous f)
    (hu : u ∈ effectiveDomain (valueFunction f)) {us : ℕ → U}
    (hus : AttentiveTendsto (valueFunction f) us u) {xs : ℕ → E} {x : E}
    (hxs : Tendsto xs atTop (𝓝 x)) (hm : ∀ᶠ n in atTop, xs n ∈ paramArgmin f (us n)) :
    x ∈ paramArgmin f u := by
  have h := (epiLscAt_iff_forall_liminf.1
    ((forall_epiLscAt_iff_lowerSemicontinuous f).2 hf u)) us hus.1 x xs hxs
  have heq : (fun n ↦ f (xs n, us n)) =ᶠ[atTop] valueFunction f ∘ us :=
    hm.mono fun n hn ↦ ((mem_paramArgmin_iff f (us n) (xs n)).1 hn).1
  rw [(hus.2.congr' heq.symm).liminf_eq] at h
  exact ⟨le_antisymm h (iInf_le _ x), hu⟩

/-- **Theorem 7.41(a)**, local boundedness on any set of bounded optimal values. -/
theorem svLocallyBoundedWithinAt_paramArgmin_of_uniform_upper_bound
    (hb : IsLevelBoundedInXLocallyUniformly f) {a : ℝ}
    (hD : ∀ v ∈ D, valueFunction f v ≤ (a : EReal)) (u : U) :
    SvLocallyBoundedWithinAt (paramArgmin f) D u :=
  svLocallyBoundedWithinAt_paramArgmin hb ⟨a, (show ∀ᶠ v in 𝓝[D] u, v ∈ D from self_mem_nhdsWithin).mono hD⟩

/-- **Theorem 7.41(b)**, continuity of the optimal value yields both properties
of the optimal-set map relative to the same parameter set. -/
theorem paramArgmin_regular_of_continuousWithinAt (hf : LowerSemicontinuous f)
    (hb : IsLevelBoundedInXLocallyUniformly f) (hu : valueFunction f u < ⊤)
    (hc : ContinuousWithinAt (valueFunction f) D u) :
    SvLocallyBoundedWithinAt (paramArgmin f) D u ∧ SvOscWithinAt (paramArgmin f) D u := by
  obtain ⟨a, ha, _⟩ := EReal.exists_between_coe_real hu
  exact ⟨svLocallyBoundedWithinAt_paramArgmin hb
    ⟨a, (hc.upperSemicontinuousWithinAt _ ha).mono fun _ h ↦ h.le⟩,
    svOscWithinAt_paramArgmin hf hu hc.upperSemicontinuousWithinAt⟩

/-- Locally uniform level bounds yield eventual level bounds on slices along
every converging parameter sequence. -/
theorem isEventuallyLevelBounded_slices (hb : IsLevelBoundedInXLocallyUniformly f)
    {us : ℕ → U} (hu : Tendsto us atTop (𝓝 u)) :
    IsEventuallyLevelBounded (fun n x ↦ f (x, us n)) := by
  intro a
  obtain ⟨V, hV, hbound⟩ :=
    (isLevelBoundedInXLocallyUniformly_iff_svLocallyBounded f).1 hb a u
  obtain ⟨R, hR⟩ := hbound.subset_closedBall (0 : E)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hu.eventually hV)
  exact ⟨R, N, fun n hn x hx ↦ hR (mem_svImage.2 ⟨us n, hN n hn, hx⟩)⟩

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Theorem 7.41(a)**, compact fibers and equality of the two effective domains. -/
theorem paramArgmin_compact_and_dom (hf : LowerSemicontinuous f) (hp : IsProper f)
    (hb : IsLevelBoundedInXLocallyUniformly f) :
    (∀ u, IsCompact (paramArgmin f u)) ∧ svDom (paramArgmin f) = effectiveDomain (valueFunction f) := by
  constructor
  · intro u
    by_cases hu : valueFunction f u < ⊤
    · have hs := hf.comp (continuous_id.prodMk (continuous_const (y := u)))
      have hl : IsLevelBounded (fun x ↦ f (x, u)) := fun a ↦
        ((isLevelBoundedInXLocallyUniformly_iff_svLocallyBounded f).1 hb a u).isBounded_apply
      exact isCompact_argmin_of_isInfCompact_of_lsc_of_isProper
        (isInfCompact_of_isLevelBounded_of_lsc hs hl) hs ⟨iInf_lt_iff.1 hu, fun x ↦ hp.2 (x,u)⟩
    · have he : paramArgmin f u = ∅ := eq_empty_iff_forall_notMem.2 fun x hx ↦ hu hx.2
      rw [he]
      exact isCompact_empty
  · ext u
    exact ⟨fun ⟨x, hx⟩ ↦ hx.2, paramArgmin_nonempty hf hp hb⟩

/-- **Theorem 7.41(b)**, epi-continuity of the slices gives continuity of their
optimal value at a feasible parameter. -/
theorem continuousWithinAt_valueFunction_of_epiContinuousWithinAt (hf : LowerSemicontinuous f)
    (hp : IsProper f) (hb : IsLevelBoundedInXLocallyUniformly f)
    (hu : u ∈ D) (hfin : valueFunction f u < ⊤) (hc : EpiContinuousWithinAt f D u) :
    ContinuousWithinAt (valueFunction f) D u := by
  apply Filter.tendsto_iff_seq_tendsto.2
  intro us hus
  obtain ⟨vs, hvD, hvt, heq⟩ := exists_seq_mem_of_tendsto_nhdsWithin hu hus
  have hepi := (epiContinuousWithinAt_iff_epiConverges hu).1 hc
  have hps : IsProper (fun x ↦ f (x, u)) := ⟨iInf_lt_iff.1 hfin, fun x ↦ hp.2 (x,u)⟩
  have ht := (convergence_in_minimization (isEventuallyLevelBounded_slices hb hvt)
    (hepi vs hvD hvt) (fun n ↦ hf.comp (continuous_id.prodMk continuous_const)) hps).2.2.1
  exact ht.congr' (heq.fun_comp (valueFunction f))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup U] in
/-- The epigraphical mapping and marginal function have the same domain. -/
theorem svDom_parameterEpigraph (f : E × U → EReal) :
    svDom (parameterEpigraph f) = effectiveDomain (valueFunction f) := by
  ext u
  constructor
  · rintro ⟨⟨x, a⟩, hx⟩
    exact (iInf_le (fun y ↦ f (y,u)) x).trans_lt (lt_of_le_of_lt hx (EReal.coe_lt_top a))
  · intro hu
    change (⨅ x, f (x, u)) < ⊤ at hu
    obtain ⟨x, hx⟩ := iInf_lt_iff.1 hu
    obtain ⟨a, hxa, _⟩ := EReal.exists_between_coe_real hx
    exact ⟨(x, a), hxa.le⟩

variable [NormedSpace ℝ U]

/-- **Theorem 7.41(b)**, convex joint objectives are epi-continuous in their
parameter on the interior of the marginal domain. -/
theorem epiContinuousAt_of_convex_epigraph [FiniteDimensional ℝ U]
    (hf : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f))
    (hu : u ∈ interior (effectiveDomain (valueFunction f))) : EpiContinuousAt f u := by
  have hg : SvGraphConvex (parameterEpigraph f) := by
    rintro ⟨v, x, a⟩ hv ⟨w, y, b⟩ hw s t hs ht hst
    exact hc (x := ((x,v), a)) hv (y := ((y,w), b)) hw hs ht hst
  rw [← svDom_parameterEpigraph f] at hu
  exact ⟨(forall_epiLscAt_iff_lowerSemicontinuous f).2 hf u, hg.svIscAt hu⟩

/-- **Theorem 7.41(b)**, convex marginal values are continuous in the interior
and the optimal-set mapping is locally bounded and outer semicontinuous there. -/
theorem convex_paramArgmin_interior [FiniteDimensional ℝ U]
    (hf : LowerSemicontinuous f) (hp : IsProper f) (hb : IsLevelBoundedInXLocallyUniformly f)
    (hc : Convex ℝ (epigraph f)) (hu : u ∈ interior (effectiveDomain (valueFunction f))) :
    ContinuousAt (valueFunction f) u ∧ SvLocallyBoundedAt (paramArgmin f) u ∧
      SvOscAt (paramArgmin f) u := by
  have hfin : u ∈ effectiveDomain (valueFunction f) := interior_subset hu
  have hepi := epiContinuousAt_of_convex_epigraph hf hc hu
  have hcval := continuousWithinAt_valueFunction_of_epiContinuousWithinAt hf hp hb (mem_univ u)
    hfin ((svContinuousWithinAt_univ).2 hepi)
  obtain ⟨hloc, hosc⟩ := paramArgmin_regular_of_continuousWithinAt hf hb hfin hcval
  exact ⟨(continuousWithinAt_univ _ _).1 hcval, svLocallyBoundedWithinAt_univ.1 hloc,
    svOscWithinAt_univ.1 hosc⟩

/-- The attentive assertion in **7.41(a)** fails at an infeasible parameter.
The only feasible decision is zero, and its cost tends to infinity as the
parameter approaches zero. -/
theorem attentiveArgmin_top_obstruction :
    ∃ (f : ℝ × ℝ → EReal) (us : ℕ → ℝ), LowerSemicontinuous f ∧ IsProper f ∧
      IsLevelBoundedInXLocallyUniformly f ∧ AttentiveTendsto (valueFunction f) us 0 ∧
      (∀ n, (0 : ℝ) ∈ paramArgmin f (us n)) ∧ (0 : ℝ) ∉ paramArgmin f 0 := by
  let p : ℝ → EReal := fun u ↦ ((ENNReal.ofReal |u|)⁻¹ : ENNReal)
  let f : ℝ × ℝ → EReal := fun z ↦ max (indicatorVA {0} z.1) (p z.2)
  have hp : Continuous p := continuous_coe_ennreal_ereal.comp ((ENNReal.continuous_ofReal.comp
    continuous_abs).inv)
  have hp0 : p 0 = ⊤ := by simp [p]
  have hpfin {u : ℝ} (hu : u ≠ 0) : p u < ⊤ := by
    apply lt_top_iff_ne_top.2
    simpa [p, EReal.coe_ennreal_eq_top_iff, ENNReal.inv_eq_top, ENNReal.ofReal_eq_zero] using
      (not_le_of_gt (abs_pos.2 hu))
  have hf0 (u : ℝ) : f (0,u) = p u := by
    simp [f, indicatorVA]
    exact EReal.coe_ennreal_nonneg _
  have hval : valueFunction f = p := by
    funext u
    exact (iInf_le (fun x ↦ f (x,u)) 0 |>.trans_eq (hf0 u)).antisymm
      (le_iInf fun _ ↦ le_max_right _ _)
  let us := fun n : ℕ ↦ 1 / (n + 1 : ℝ)
  have hus : Tendsto us atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨f, us, ((lowerSemicontinuous_indicatorVA isClosed_singleton).comp continuous_fst).sup
    (hp.comp continuous_snd).lowerSemicontinuous, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨⟨(0,1), ?_⟩, fun z ↦ lt_of_lt_of_le (EReal.bot_lt_coe_ennreal _) (le_max_right _ _)⟩
    rw [hf0]
    exact hpfin one_ne_zero
  · intro u a
    refine ⟨1, one_pos, ((isBounded_singleton : IsBounded ({0} : Set ℝ)).prod (isBounded_closedBall (x := u) (r := 1))).subset ?_⟩
    rintro ⟨x,v⟩ ⟨⟨_, hv⟩, hfv⟩
    refine ⟨?_, hv⟩
    by_contra hx
    change x ≠ 0 at hx
    change f (x,v) ≤ (a : EReal) at hfv
    simp [f, indicatorVA, hx] at hfv
  · rw [hval]
    exact ⟨hus, (hp.tendsto _).comp hus⟩
  · intro n
    rw [mem_paramArgmin_iff, hf0, hval]
    exact ⟨rfl, hpfin (by dsimp [us]; positivity)⟩
  · simp [mem_paramArgmin_iff, hval, hp0]

end RW
