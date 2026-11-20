/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Convergence in minimization

Theorem 7.33. A single compact sublevel, with level strictly above the
infimum, suffices for eventual attainment. This avoids assuming that any
individual `f n` is level bounded at its higher levels.
-/

import RockafellarWets.Chapter7.InfimaAndMinimizers
import RockafellarWets.Chapter7.EventualLevelBoundedness

open Bornology Filter Metric Set Topology

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem argmin_nonempty_of_isCompact_sublevel {f : E → EReal} {a : ℝ}
    (hlsc : LowerSemicontinuous f) (hc : IsCompact (levelSet f a))
    (hv : (⨅ x, f x) < (a : EReal)) : (argmin f).Nonempty := by
  obtain ⟨y, hy⟩ := iInf_lt_iff.mp hv
  obtain ⟨x, hx, hmin⟩ := (hlsc.lowerSemicontinuousOn _).exists_isMinOn ⟨y, hy.le⟩ hc
  refine ⟨x, le_antisymm (le_iInf fun z ↦ ?_) (iInf_le _ _), hv.trans (EReal.coe_lt_top _)⟩
  by_cases hz : z ∈ levelSet f a
  · exact hmin hz
  · exact (show f x ≤ (a : EReal) from hx).trans (le_of_not_ge hz)

/-- **Theorem 7.33**, the limiting infimum is finite and attained, and the
optimal values converge to it. Eventually the minimizer sets are nonempty
and lie in a single closed ball. -/
theorem convergence_in_minimization {f : ℕ → E → EReal} {g : E → EReal}
    (hb : IsEventuallyLevelBounded f) (h : EpiConverges f g)
    (hf : ∀ n, LowerSemicontinuous (f n)) (hg : IsProper g) :
    (∃ a : ℝ, (⨅ x, g x) = (a : EReal)) ∧ (argmin g).Nonempty ∧
      Tendsto (fun n ↦ ⨅ x, f n x) atTop (𝓝 (⨅ x, g x)) ∧
      (∀ᶠ n in atTop, (argmin (f n)).Nonempty) ∧
      EventuallyBounded (fun n ↦ argmin (f n)) ∧
      outerSetLimit (fun n ↦ argmin (f n)) ⊆ argmin g := by
  have hglsc := lowerSemicontinuous_of_isClosed_epigraph_ereal g (PKConverges.isClosed h)
  have hgmin := argmin_nonempty_of_isInfCompact_of_lsc_of_isProper
    (isInfCompact_of_isEventuallyLevelBounded h hb) hglsc hg
  obtain ⟨x, hx⟩ := hgmin
  have hnt : (⨅ y, g y) < ⊤ := hx.2
  have hnb : ⊥ < ⨅ y, g y := hx.1 ▸ hg.2 x
  let a := (⨅ y, g y).toReal
  have ha : (⨅ y, g y) = (a : EReal) := (EReal.coe_toReal hnt.ne hnb.ne').symm
  let A := a + 1
  have hupper := limsup_iInf_le_of_epiUpperLimit_le (epiConverges_iff_epiLimits_eq.1 h).2.le
  have hval := eventually_lt_of_limsup_lt (hupper.trans_lt (ha ▸ EReal.coe_lt_coe_iff.2 (lt_add_one a)))
  obtain ⟨R, N, hN⟩ := hb A
  have hev : ∀ᶠ n in atTop, (argmin (f n)).Nonempty ∧
      argmin (f n) ⊆ closedBall 0 R := by
    filter_upwards [hval, eventually_ge_atTop N] with n hn hnN
    have hc : IsCompact (levelSet (f n) A) := Metric.isCompact_iff_isClosed_bounded.2
      ⟨isClosed_levelSet_of_lsc_ereal (hf n) _, isBounded_closedBall.subset (hN n hnN)⟩
    exact ⟨argmin_nonempty_of_isCompact_sublevel (hf n) hc hn, fun y hy ↦
      hN n hnN (hy.1.trans_le hn.le)⟩
  have ht : Tendsto (fun n ↦ ⨅ x, f n x) atTop (𝓝 (a : EReal)) := by
    apply (tendsto_iInf_iff_compact_approximation h ha).2
    intro ε hε
    refine ⟨closedBall 0 R, isCompact_closedBall _ _, ?_⟩
    filter_upwards [hev] with n hn
    obtain ⟨y, hy⟩ := hn.1
    exact (infimumOn_le (hn.2 hy)).trans (hy.1.trans_le
      (le_add_of_nonneg_right (EReal.coe_nonneg.2 hε.le)))
  refine ⟨⟨a, ha⟩, ⟨x, hx⟩, ha ▸ ht, hev.mono (fun _ hn ↦ hn.1), ?_, ?_⟩
  · obtain ⟨M, hM⟩ := eventually_atTop.1 (hev.mono (fun _ hn ↦ hn.2))
    exact ⟨R, M, hM⟩
  · apply Subset.trans (outerSetLimit_mono (D := fun n ↦ approxArgmin (f n) 0) ?_)
      (outerSetLimit_approxArgmin_subset_argmin_of_epiConverges h hnt tendsto_const_nhds)
    intro n y hy
    simpa only [approxArgmin, mem_setOf_eq, EReal.coe_zero, add_zero] using hy.1.le

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Theorem 7.33**, any sequence of vanishing-error minimizers is bounded
and every cluster point minimizes the limit problem. -/
theorem bounded_approxMinimizers_and_cluster_points {f : ℕ → E → EReal} {g : E → EReal}
    (hb : IsEventuallyLevelBounded f) (h : EpiConverges f g) (hg : IsProper g)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) {xs : ℕ → E}
    (hxs : ∀ᶠ n in atTop, xs n ∈ approxArgmin (f n) (ε n)) :
    IsBounded (range xs) ∧ ∀ x, MapClusterPt x atTop xs → x ∈ argmin g := by
  have hnt := iInf_lt_top_of_isProper hg
  obtain ⟨a, ha, _⟩ := EReal.exists_between_coe_real hnt
  have hupper := limsup_iInf_le_of_epiUpperLimit_le (epiConverges_iff_epiLimits_eq.1 h).2.le
  have hax := limsup_le_of_mem_approxArgmin hupper hε strictMono_id hxs
  simp only [id_eq, EReal.coe_zero, add_zero] at hax
  have hval := eventually_lt_of_limsup_lt (hax.trans_lt ha)
  obtain ⟨R, N, hN⟩ := hb a
  have hev : ∀ᶠ n in atTop, xs n ∈ closedBall 0 R := by
    filter_upwards [hval, eventually_ge_atTop N] with n hn hnN
    exact hN n hnN hn.le
  constructor
  · obtain ⟨M, hM⟩ := eventually_atTop.1 hev
    have hbound : IsBounded ((xs '' Iio M) ∪ closedBall 0 R) :=
      ((Set.finite_Iio M).image xs).isBounded.union isBounded_closedBall
    apply hbound.subset
    rintro _ ⟨n, rfl⟩
    exact (lt_or_ge n M).elim (fun hn ↦ Or.inl ⟨n, hn, rfl⟩) (fun hn ↦ Or.inr (hM n hn))
  · intro x hx
    apply outerSetLimit_approxArgmin_subset_argmin_of_epiConverges h hnt hε
    intro V hV
    exact ((mapClusterPt_iff_frequently.1 hx V hV).and_eventually hxs).mono
      fun n hn ↦ ⟨xs n, hn.2, hn.1⟩

/-- **Theorem 7.33**, uniqueness gives convergence of the whole sequence. -/
theorem tendsto_approxMinimizers_of_argmin_singleton {f : ℕ → E → EReal} {g : E → EReal}
    (hb : IsEventuallyLevelBounded f) (h : EpiConverges f g) (hg : IsProper g)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) {xs : ℕ → E}
    (hxs : ∀ᶠ n in atTop, xs n ∈ approxArgmin (f n) (ε n)) {x : E} (hx : argmin g = {x}) :
    Tendsto xs atTop (𝓝 x) := by
  obtain ⟨hs, hcl⟩ := bounded_approxMinimizers_and_cluster_points hb h hg hε hxs
  apply hs.isCompact_closure.tendsto_nhds_of_unique_mapClusterPt
    (Eventually.of_forall fun n ↦ subset_closure (mem_range_self n))
  intro y _ hy
  exact mem_singleton_iff.1 (hx ▸ hcl y hy)

end RW
