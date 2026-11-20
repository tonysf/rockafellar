/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Graphical convergence of proximal mappings

Exercise 7.38. Eventual local boundedness uses a joint choice of indices,
centers converging to the point under test, and proximal points. The unique
minimizer conclusion in 7.33 gives inner graphical convergence in the
single-valued case.
-/

import RockafellarWets.Chapter7.MoreauEnvelopeLimits
import RockafellarWets.Chapter5.LocalBoundedness

open Bornology Filter Metric Set Topology

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem epiConverges_subseq_for_prox {f : ℕ → E → EReal} {g : E → EReal}
    (h : EpiConverges f g) {φ : ℕ → ℕ} (hφ : StrictMono φ) : EpiConverges (f ∘ φ) g := by
  have hl : epigraph g ⊆ innerSetLimit (fun n ↦ epigraph (f (φ n))) :=
    (PKConverges.inner_eq h).ge.trans (innerSetLimit_subset_subsequence hφ)
  have hu : outerSetLimit (fun n ↦ epigraph (f (φ n))) ⊆ epigraph g :=
    (outerSetLimit_subsequence_subset hφ).trans (PKConverges.outer_eq h).le
  exact ⟨((innerSetLimit_subset_outerSetLimit _).trans hu).antisymm hl,
    hu.antisymm (hl.trans (innerSetLimit_subset_outerSetLimit _))⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem lt_eventualProxThreshold_subseq {f : ℕ → E → EReal} {t : ℝ}
    (ht : (t : EReal) < eventualProxThreshold f) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    (t : EReal) < eventualProxThreshold (f ∘ φ) := by
  obtain ⟨s, hts, hs, b, β, hβ⟩ := exists_eventual_minorant_above_of_lt_eventualProxThreshold ht
  have hev := (hφ.tendsto_atTop.eventually hβ).mono fun n hn ↦
    (le_moreauEnvelopeEReal_iff_quadratic_minorant s β b).2 hn
  have hb := (EReal.bot_lt_coe β).trans_le (le_liminf_of_le (by isBoundedDefault) hev)
  exact (EReal.coe_lt_coe_iff.2 hts).trans_le
    (le_iSup_of_le s (le_iSup_of_le ⟨hs, b, hb⟩ le_rfl))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Exercise 7.38**, the graphical outer inclusion for proximal mappings. -/
theorem graphicalOuterLimit_proximalMappingEReal_subset {f : ℕ → E → EReal} {g : E → EReal}
    (h : EpiConverges f g) (hg : IsProper g) {ts : ℕ → ℝ} {t : ℝ}
    (hts : Tendsto ts atTop (𝓝 t)) (ht : 0 < t) (x : E) :
    graphicalOuterLimit (fun n ↦ proximalMappingEReal (f n) (ts n)) x ⊆
      proximalMappingEReal g t x := by
  intro w hw
  obtain ⟨φ, xs, ws, hφ, hws, hxto, hwto⟩ := mem_graphicalOuterLimit_iff.1 hw
  have hobj := epiConverges_proximalObjectives (epiConverges_subseq_for_prox h hφ)
    hxto (hts.comp hφ.tendsto_atTop) ht.ne'
  apply outerSetLimit_approxArgmin_subset_argmin_of_epiConverges hobj
    (iInf_lt_top_of_isProper (isProper_proximalObjectiveEReal hg _ _)) (ε := fun _ ↦ 0)
    tendsto_const_nhds
  apply mem_outerSetLimit_iff_exists_subsequence.2
  refine ⟨id, ws, strictMono_id, fun k ↦ ?_, hwto⟩
  simpa only [approxArgmin, mem_setOf_eq, EReal.coe_zero, add_zero] using (hws k).1.le

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem exists_nhds_eventuallyBounded_of_selections {S : ℕ → E → Set E} {x : E}
    (hb : ∀ (φ : ℕ → ℕ) (xs vs : ℕ → E), StrictMono φ → Tendsto xs atTop (𝓝 x) →
      (∀ k, vs k ∈ S (φ k) (xs k)) → IsBounded (range vs)) :
    ∃ V ∈ 𝓝 x, EventuallyBounded (fun n ↦ svImage (S n) V) := by
  by_contra hn
  let r := fun k : ℕ ↦ 1 / ((k : ℝ) + 1)
  have hr : ∀ k, 0 < r k := fun k ↦ by dsimp [r]; positivity
  have hfreq : ∀ k : ℕ, ∃ᶠ n in atTop,
      ∃ y ∈ ball x (r k), ∃ v ∈ S n y, (k : ℝ) < ‖v‖ := by
    intro k
    by_contra hnot
    have hev := not_frequently.1 hnot
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    apply hn ⟨ball x (r k), ball_mem_nhds x (hr k), k, N, ?_⟩
    intro n hn v hv
    obtain ⟨y, hy, hv⟩ := mem_iUnion₂.1 hv
    rw [mem_closedBall_zero_iff]
    exact le_of_not_gt (fun hh ↦ hN n hn ⟨y, hy, v, hv, hh⟩)
  obtain ⟨φ, hφ, hsel⟩ := extraction_forall_of_frequently hfreq
  choose xs hxs vs hvs hvnorm using hsel
  have hxto : Tendsto xs atTop (𝓝 x) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨N, hN⟩ := eventually_atTop.1
      (tendsto_one_div_add_atTop_nhds_zero_nat.eventually_lt_const hδ)
    exact ⟨N, fun n hn ↦ (hxs n).trans (hN n hn)⟩
  obtain ⟨R, hR⟩ := (hb φ xs vs hφ hxto hvs).subset_closedBall (0 : E)
  obtain ⟨k, hk⟩ := exists_nat_gt R
  exact (hk.trans (hvnorm k)).not_ge (mem_closedBall_zero_iff.1 (hR (mem_range_self k)))

omit [FiniteDimensional ℝ E] in
/-- **Exercise 7.38**, eventual local boundedness at every center. -/
theorem eventually_locallyBounded_proximalMappingEReal {f : ℕ → E → EReal} {g : E → EReal}
    (h : EpiConverges f g) (hg : IsProper g) {ts : ℕ → ℝ} {t : ℝ}
    (hts : Tendsto ts atTop (𝓝 t)) (ht : 0 < t) (hthr : (t : EReal) < eventualProxThreshold f)
    (x : E) : ∃ V ∈ 𝓝 x, EventuallyBounded (fun n ↦ svImage (proximalMappingEReal (f n) (ts n)) V) := by
  apply exists_nhds_eventuallyBounded_of_selections
  intro φ xs vs hφ hxto hvs
  have ht' := hts.comp hφ.tendsto_atTop
  have hb := isEventuallyLevelBounded_proximalObjectives hxto ht' ht (lt_eventualProxThreshold_subseq hthr hφ)
  have hobj := epiConverges_proximalObjectives (epiConverges_subseq_for_prox h hφ) hxto ht' ht.ne'
  apply (bounded_approxMinimizers_and_cluster_points hb hobj (isProper_proximalObjectiveEReal hg _ _)
    (ε := fun _ ↦ 0) tendsto_const_nhds (xs := vs) ?_).1
  exact Eventually.of_forall fun k ↦ by
    simpa only [approxArgmin, mem_setOf_eq, EReal.coe_zero, add_zero] using (hvs k).1.le

/-- **Exercise 7.38**, graphical convergence when each fiber of the limiting
proximal mapping has at most one point. -/
theorem graphicalConverges_proximalMappingEReal_of_subsingleton {f : ℕ → E → EReal} {g : E → EReal}
    (h : EpiConverges f g) (hflsc : ∀ n, LowerSemicontinuous (f n)) (hg : IsProper g)
    {ts : ℕ → ℝ} {t : ℝ} (hts : Tendsto ts atTop (𝓝 t)) (ht : 0 < t)
    (hthr : (t : EReal) < eventualProxThreshold f) (hone : ∀ x, (proximalMappingEReal g t x).Subsingleton) :
    GraphicalConverges (fun n ↦ proximalMappingEReal (f n) (ts n)) (proximalMappingEReal g t) := by
  classical
  refine graphicalConverges_iff.2 ⟨graphicalOuterLimit_proximalMappingEReal_subset h hg hts ht, ?_⟩
  intro x w hw
  have hxto : Tendsto (fun _ : ℕ ↦ x) atTop (𝓝 x) := tendsto_const_nhds
  have hb := isEventuallyLevelBounded_proximalObjectives hxto hts ht hthr
  have hobj := epiConverges_proximalObjectives h hxto hts ht.ne'
  have hproper := isProper_proximalObjectiveEReal hg t x
  obtain ⟨_, _, _, hne, _, _⟩ := convergence_in_minimization hb hobj
    (fun n ↦ lowerSemicontinuous_proximalObjectiveEReal (hflsc n) _ _) hproper
  let P := fun n ↦ proximalMappingEReal (f n) (ts n) x
  let ws := fun n ↦ if hp : (P n).Nonempty then hp.choose else w
  have hwmem : ∀ᶠ n in atTop, ws n ∈ P n := hne.mono fun n hn ↦ by
      change (P n).Nonempty at hn
      simpa only [ws, dif_pos hn] using hn.choose_spec
  have hwε : ∀ᶠ n in atTop, ws n ∈ approxArgmin (proximalObjectiveEReal (f n) (ts n) x) 0 :=
    hwmem.mono fun n hn ↦ by simpa [approxArgmin] using hn.1.le
  have hsingle : proximalMappingEReal g t x = {w} := (hone x).eq_singleton_of_mem hw
  exact mem_graphicalInnerLimit_iff.2 ⟨_, ws, hwmem, hxto, tendsto_approxMinimizers_of_argmin_singleton
    hb hobj hproper (ε := fun _ ↦ 0) tendsto_const_nhds hwε hsingle⟩

/-- **Exercise 7.38**, the convex case. -/
theorem graphicalConverges_proximalMappingEReal_of_convex {f : ℕ → E → EReal} {g : E → EReal}
    (h : EpiConverges f g) (hflsc : ∀ n, LowerSemicontinuous (f n)) (hg : IsProper g)
    (hc : Convex ℝ (epigraph g)) {ts : ℕ → ℝ} {t : ℝ}
    (hts : Tendsto ts atTop (𝓝 t)) (ht : 0 < t) (hthr : (t : EReal) < eventualProxThreshold f) :
    GraphicalConverges (fun n ↦ proximalMappingEReal (f n) (ts n)) (proximalMappingEReal g t) := by
  apply graphicalConverges_proximalMappingEReal_of_subsingleton h hflsc hg hts ht hthr
  intro x u hu v hv
  have hlsc := lowerSemicontinuous_of_isClosed_epigraph_ereal g (PKConverges.isClosed h)
  have hh := norm_sub_proximalEReal_le_two_mul hc hlsc hg ht hu hv
  simpa only [sub_self, norm_zero, mul_zero, norm_le_zero_iff, sub_eq_zero] using hh

end RW
