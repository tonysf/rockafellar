/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Epi-continuity with respect to parameters

Definition 7.39 and Exercise 7.40. These properties concern the epigraph as
a set-valued function of the parameter. In the upper-semicontinuity test the
decision sequence may be chosen, while the lower test quantifies over all
decision sequences. The relative tests restrict only the parameters.
-/

import RockafellarWets.Chapter7.EpiLimitCharacterization
import RockafellarWets.Chapter5.SequentialLimits

open Filter Metric Set Topology

namespace RW

section Definitions

variable {E U : Type*} [TopologicalSpace E] [TopologicalSpace U]

/-- Epigraphical mapping of a parameter-dependent objective. -/
def parameterEpigraph (f : E × U → EReal) (u : U) : Set (E × ℝ) := epigraph (fun x ↦ f (x, u))

/-- **Definition 7.39**, epi-lower semicontinuity relative to a set of parameters. -/
def EpiLscWithinAt (f : E × U → EReal) (D : Set U) (u : U) : Prop :=
  SvOscWithinAt (parameterEpigraph f) D u

/-- **Definition 7.39**, epi-upper semicontinuity relative to a set of parameters. -/
def EpiUscWithinAt (f : E × U → EReal) (D : Set U) (u : U) : Prop :=
  SvIscWithinAt (parameterEpigraph f) D u

/-- **Definition 7.39**, epi-continuity relative to a set of parameters. -/
def EpiContinuousWithinAt (f : E × U → EReal) (D : Set U) (u : U) : Prop :=
  SvContinuousWithinAt (parameterEpigraph f) D u

/-- **Definition 7.39**, epi-lower semicontinuity at a parameter. -/
def EpiLscAt (f : E × U → EReal) (u : U) : Prop := SvOscAt (parameterEpigraph f) u

/-- **Definition 7.39**, epi-upper semicontinuity at a parameter. -/
def EpiUscAt (f : E × U → EReal) (u : U) : Prop := SvIscAt (parameterEpigraph f) u

/-- **Definition 7.39**, epi-continuity at a parameter. -/
def EpiContinuousAt (f : E × U → EReal) (u : U) : Prop := SvContinuousAt (parameterEpigraph f) u

end Definitions

section Sequences

variable {E U : Type*} [PseudoMetricSpace E] [PseudoMetricSpace U]

/-- **Exercise 7.40**, the lower sequential test, including the relative case. -/
theorem epiLscWithinAt_iff_forall_liminf {f : E × U → EReal} {D : Set U} {u : U} (hu : u ∈ D) :
    EpiLscWithinAt f D u ↔ ∀ (us : ℕ → U), (∀ n, us n ∈ D) → Tendsto us atTop (𝓝 u) →
      ∀ (x : E) (xs : ℕ → E), Tendsto xs atTop (𝓝 x) →
        f (x, u) ≤ liminf (fun n ↦ f (xs n, us n)) atTop := by
  rw [EpiLscWithinAt, SvOscWithinAt, svOuterLimitWithin_eq_iUnion _ hu, iUnion₂_subset_iff]
  constructor
  · intro h us hus huto x xs hxto
    have hgraph := h us ⟨hus, huto⟩
    change outerSetLimit (fun n ↦ epigraph (fun y ↦ f (y, us n))) ⊆ epigraph (fun y ↦ f (y, u)) at hgraph
    rw [← epigraph_epiLowerLimit, epigraph_subset_epigraph_iff] at hgraph
    exact (hgraph x).trans (epiLowerLimit_le_liminf hxto)
  · intro h us hus
    change outerSetLimit (fun n ↦ epigraph (fun y ↦ f (y, us n))) ⊆ epigraph (fun y ↦ f (y, u))
    rw [← epigraph_epiLowerLimit, epigraph_subset_epigraph_iff]
    intro x
    obtain ⟨xs, hx, hv⟩ := exists_tendsto_liminf_eq_epiLowerLimit (fun n y ↦ f (y, us n)) x
    exact hv ▸ h us hus.1 hus.2 x xs hx

/-- **Exercise 7.40**, the upper recovery-sequence test, including the relative case. -/
theorem epiUscWithinAt_iff_exists_limsup {f : E × U → EReal} {D : Set U} {u : U} (hu : u ∈ D) :
    EpiUscWithinAt f D u ↔ ∀ (us : ℕ → U), (∀ n, us n ∈ D) → Tendsto us atTop (𝓝 u) →
      ∀ x : E, ∃ xs : ℕ → E, Tendsto xs atTop (𝓝 x) ∧
        limsup (fun n ↦ f (xs n, us n)) atTop ≤ f (x, u) := by
  rw [EpiUscWithinAt, svIscWithinAt_iff_forall_seq hu]
  constructor
  · intro h us hus huto x
    have hgraph := h us hus huto
    change epigraph (fun y ↦ f (y, u)) ⊆ innerSetLimit (fun n ↦ epigraph (fun y ↦ f (y, us n))) at hgraph
    rw [← epigraph_epiUpperLimit, epigraph_subset_epigraph_iff] at hgraph
    obtain ⟨xs, hxto, hv⟩ := exists_tendsto_limsup_eq_epiUpperLimit (fun n y ↦ f (y, us n)) x
    exact ⟨xs, hxto, hv.le.trans (hgraph x)⟩
  · intro h us hus huto
    change epigraph (fun y ↦ f (y, u)) ⊆ innerSetLimit (fun n ↦ epigraph (fun y ↦ f (y, us n)))
    rw [← epigraph_epiUpperLimit, epigraph_subset_epigraph_iff]
    intro x
    obtain ⟨xs, hx, hv⟩ := h us hus huto x
    exact (epiUpperLimit_le_limsup hx).trans hv

/-- **Definition 7.39** in the equivalent form of epi-convergence along every
parameter sequence. -/
theorem epiContinuousWithinAt_iff_epiConverges {f : E × U → EReal} {D : Set U} {u : U} (hu : u ∈ D) :
    EpiContinuousWithinAt f D u ↔ ∀ (us : ℕ → U), (∀ n, us n ∈ D) → Tendsto us atTop (𝓝 u) →
      EpiConverges (fun n x ↦ f (x, us n)) (fun x ↦ f (x, u)) := by
  change EpiLscWithinAt f D u ∧ EpiUscWithinAt f D u ↔ _
  rw [epiLscWithinAt_iff_forall_liminf hu, epiUscWithinAt_iff_exists_limsup hu]
  constructor
  · rintro ⟨hl, hupp⟩ us hus huto
    exact epiConverges_iff_liminf_limsup.2 fun x ↦ ⟨hl us hus huto x, hupp us hus huto x⟩
  · intro h
    exact ⟨fun us hus huto x ↦ (epiConverges_iff_liminf_limsup.1 (h us hus huto) x).1,
      fun us hus huto x ↦ (epiConverges_iff_liminf_limsup.1 (h us hus huto) x).2⟩

/-- The absolute version of the lower test in **Exercise 7.40**. -/
theorem epiLscAt_iff_forall_liminf {f : E × U → EReal} {u : U} :
    EpiLscAt f u ↔ ∀ (us : ℕ → U), Tendsto us atTop (𝓝 u) →
      ∀ (x : E) (xs : ℕ → E), Tendsto xs atTop (𝓝 x) → f (x,u) ≤ liminf (fun n ↦ f (xs n, us n)) atTop := by
  simpa [EpiLscWithinAt, EpiLscAt, svOscWithinAt_univ] using
    (epiLscWithinAt_iff_forall_liminf (f := f) (mem_univ u))

/-- The absolute version of the upper test in **Exercise 7.40**. -/
theorem epiUscAt_iff_exists_limsup {f : E × U → EReal} {u : U} :
    EpiUscAt f u ↔ ∀ (us : ℕ → U), Tendsto us atTop (𝓝 u) →
      ∀ x : E, ∃ xs : ℕ → E, Tendsto xs atTop (𝓝 x) ∧ limsup (fun n ↦ f (xs n, us n)) atTop ≤ f (x,u) := by
  simpa [EpiUscWithinAt, EpiUscAt, svIscWithinAt_univ] using
    (epiUscWithinAt_iff_exists_limsup (f := f) (mem_univ u))

/-- **Exercise 7.40**, joint lower semicontinuity is exactly epi-lower
semicontinuity at every parameter. -/
theorem forall_epiLscAt_iff_lowerSemicontinuous (f : E × U → EReal) :
    (∀ u, EpiLscAt f u) ↔ LowerSemicontinuous f := by
  change SvOsc (parameterEpigraph f) ↔ LowerSemicontinuous f
  rw [← isClosed_svGraph_iff_svOsc, lsc_iff_epigraph_closed_ereal]
  constructor
  · intro h
    exact h.preimage (continuous_fst.snd.prodMk (continuous_fst.fst.prodMk continuous_snd))
  · intro h
    exact h.preimage ((continuous_snd.fst.prodMk continuous_fst).prodMk continuous_snd.snd)

/-- **Exercise 7.40**, joint upper semicontinuity is sufficient. -/
theorem epiUscAt_of_upperSemicontinuous {f : E × U → EReal} (hf : UpperSemicontinuous f) (u : U) :
    EpiUscAt f u := by
  rw [epiUscAt_iff_exists_limsup]
  intro us hus x
  refine ⟨fun _ ↦ x, tendsto_const_nhds, ?_⟩
  change limsup (f ∘ (fun n ↦ (x, us n))) atTop ≤ f (x, u)
  rw [limsup_comp]
  exact (limsup_le_limsup_of_le (tendsto_const_nhds.prodMk_nhds hus)).trans (hf.limsup_le _)

/-- **Exercise 7.40**, continuity of the joint objective is sufficient. -/
theorem epiContinuousAt_of_continuous {f : E × U → EReal} (hf : Continuous f) (u : U) :
    EpiContinuousAt f u := ⟨(forall_epiLscAt_iff_lowerSemicontinuous f).2 hf.lowerSemicontinuous u,
      epiUscAt_of_upperSemicontinuous hf.upperSemicontinuous u⟩

/-- **Exercise 7.40**, the jointly discontinuous indicator of the decision
constraint `{0}` is epi-continuous as a constant function of the parameter. -/
theorem epiContinuousAt_not_jointly_upperSemicontinuous_example :
    let f : ℝ × ℝ → EReal := fun p ↦ indicatorVA {0} p.1
    (∀ u, EpiContinuousAt f u) ∧ ¬ UpperSemicontinuous f := by
  let g : ℝ → EReal := indicatorVA {0}
  have hg := lowerSemicontinuous_indicatorVA (C := ({0} : Set ℝ)) isClosed_singleton
  refine ⟨fun u ↦ ⟨(forall_epiLscAt_iff_lowerSemicontinuous _).2 (hg.comp continuous_fst) u, ?_⟩, ?_⟩
  · apply epiUscAt_iff_exists_limsup.2
    intro us hus x
    refine ⟨fun _ ↦ x, tendsto_const_nhds, ?_⟩
    change limsup (fun _ : ℕ ↦ g x) atTop ≤ g x
    rw [limsup_const]
  · intro hbad
    have h0 : indicatorVA ({0} : Set ℝ) 0 < (1 : EReal) := by simp [indicatorVA]
    have hev := hbad (0,0) 1 h0
    let ys := fun n : ℕ ↦ 1 / (n + 1 : ℝ)
    have hy : Tendsto (fun n ↦ (ys n, (0 : ℝ))) atTop (𝓝 (0, 0)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.prodMk_nhds tendsto_const_nhds
    obtain ⟨n, hn⟩ := (hy.eventually hev).exists
    have hne : ys n ≠ 0 := by dsimp [ys]; positivity
    simp [indicatorVA, hne] at hn

end Sequences

end RW
