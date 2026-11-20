/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Local closedness and the absolute graphical localization theorem
-/

import RockafellarWets.Chapter9.AubinLocalization
import RockafellarWets.Chapter5.PerturbedMappings

open Filter Metric Set Topology
open scoped NNReal ENNReal

namespace RW

variable {E F : Type*} [MetricSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {S : E → Set F} {X Y U K : Set E} {x : E} {u : F} {r k : ℝ≥0}

/-- Strict continuity depends only on the input neighborhood filter. -/
theorem SvStrictlyContinuousWithinAt.of_nhdsWithin_eq
    (h : SvStrictlyContinuousWithinAt S Y x) (hx : x ∈ X) (heq : 𝓝[Y] x = 𝓝[X] x) :
    SvStrictlyContinuousWithinAt S X x := by
  refine ⟨hx,heq ▸ h.2.1,fun r ↦ ?_⟩
  obtain ⟨k,V,hV,hL⟩ := (strictlyContinuousWithinAt_iff.mp ⟨h.1,h.2.2 r⟩).2
  exact (lipschitzModulusWithin_le (heq ▸ hV) hL).trans_lt ENNReal.coe_lt_top

/-- The local transport characterization only requires eventual nonempty,
closed fibers, as in the definition of strict continuity itself. -/
theorem svStrictlyContinuousWithinAt_iff_local_transport_of_eventually (hx : x ∈ X)
    (hS : ∀ᶠ a in 𝓝[X] x, (S a).Nonempty ∧ IsClosed (S a)) :
    SvStrictlyContinuousWithinAt S X x ↔
      ∀ r : ℝ≥0, ∃ k : ℝ≥0, ∃ U ∈ 𝓝[X] x, RhoTransport k r S U := by
  obtain ⟨V,hV,hVS⟩ := eventually_nhdsWithin_iff_exists_nhds.mp hS
  let Y := X ∩ V
  have hxY : x ∈ Y := ⟨hx,mem_of_mem_nhds hV⟩
  have hYS : NonemptyClosedValuedOn S Y := hVS
  have heq : 𝓝[Y] x = 𝓝[X] x := by
    simpa only [Y,inter_comm] using (nhdsWithin_inter_of_mem (t := X) (mem_nhdsWithin_of_mem_nhds hV))
  constructor
  · intro h
    have hY := h.of_nhdsWithin_eq hxY heq.symm
    intro r
    obtain ⟨k,U,hU,H⟩ := (svStrictlyContinuousWithinAt_iff_local_transport hxY hYS).mp hY r
    exact ⟨k,U,heq ▸ hU,H⟩
  · intro h
    apply SvStrictlyContinuousWithinAt.of_nhdsWithin_eq (Y := Y) (hx := hx) (heq := heq)
    apply (svStrictlyContinuousWithinAt_iff_local_transport hxY hYS).mpr
    intro r
    obtain ⟨k,U,hU,H⟩ := h r
    exact ⟨k,U,heq.symm ▸ hU,H⟩

/-- A bounded graph portion is closed when uniform transport holds on its
closed input neighborhood and the comparison fibers are closed. -/
theorem RhoTransport.isClosed_graph_inter (h : RhoTransport k r S U)
    (hK : IsClosed K) (hKU : K ⊆ U) (hS : NonemptyClosedValuedOn S K) :
    IsClosed (svGraph S ∩ (K ×ˢ closedBall (0:F) (r:ℝ))) := by
  apply IsSeqClosed.isClosed
  intro p q hp hpq
  have hq : q ∈ K ×ˢ closedBall (0:F) (r:ℝ) :=
    (hK.prod isClosed_closedBall).mem_of_tendsto hpq (Eventually.of_forall fun n ↦ (hp n).2)
  refine ⟨?_,hq⟩
  have hd : ∀ᶠ n in atTop, infDist (p n).2 (S q.1) ≤ (k:ℝ)*dist (p n).1 q.1 := by
    apply Eventually.of_forall
    intro n
    obtain ⟨w,hw,hwd⟩ := h (p n).1 (hKU (hp n).2.1) q.1 (hKU hq.1)
      (p n).2 ⟨(hp n).1,(hp n).2.2⟩
    exact (infDist_le_dist_of_mem hw).trans hwd
  have hle := le_of_tendsto_of_tendsto
    ((continuous_infDist_pt (S q.1)).tendsto q.2 |>.comp ((continuous_snd.tendsto q).comp hpq))
    (show Tendsto (fun n ↦ (k:ℝ)*dist (p n).1 q.1) atTop (𝓝 0) by
      simpa using (((continuous_fst.tendsto q).comp hpq).dist (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ q.1) atTop (𝓝 q.1))).const_mul (k:ℝ)) hd
  exact ((hS q.1 hq.1).2.mem_iff_infDist_zero (hS q.1 hq.1).1).mpr (le_antisymm hle infDist_nonneg)

/-- Absolute strict continuity gives local closedness of the full graph at
each output point, without assumptions on distant fibers. -/
theorem SvStrictlyContinuousAt.isLocallyClosedAt_graph (h : SvStrictlyContinuousAt S x) (u : F) :
    IsLocallyClosedAt (svGraph S) (x,u) := by
  let r : ℝ≥0 := ‖u‖₊+1
  obtain ⟨k,U,hU,H⟩ := (svStrictlyContinuousWithinAt_iff_local_transport_of_eventually h.1 h.2.1).mp h r
  have hUS : U ∩ {a | (S a).Nonempty ∧ IsClosed (S a)} ∈ 𝓝 x := by
    simpa only [nhdsWithin_univ] using inter_mem hU h.2.1
  obtain ⟨d,hd,hD⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hUS
  refine ⟨closedBall x d ×ˢ closedBall (0:F) (r:ℝ),
    prod_mem_nhds (closedBall_mem_nhds _ hd) (closedBall_mem_nhds_of_mem (by dsimp [r]; simp)),
    isClosed_closedBall.prod isClosed_closedBall,?_⟩
  exact H.isClosed_graph_inter isClosed_closedBall (fun _ ha ↦ (hD ha).1) (fun _ ha ↦ (hD ha).2)

/-- The absolute direction of Theorem 9.38 gives the full Aubin property. -/
theorem SvStrictlyContinuousAt.hasAubinPropertyAt (h : SvStrictlyContinuousAt S x) (hu : u ∈ S x) :
    HasAubinPropertyAt S x u :=
  ⟨mem_univ x,hu,h.isLocallyClosedAt_graph u,h.exists_aubinEstimate u⟩

/-- **Theorem 9.38**, the absolute equivalence for a closed-valued mapping
with nonempty base fiber. The base nonemptiness prevents a vacuous converse. -/
theorem svStrictlyContinuousAt_iff_osc_aubin (hclosed : ∀ a, IsClosed (S a)) (hne : (S x).Nonempty) :
    SvStrictlyContinuousAt S x ↔ SvOscAt S x ∧ ∀ u ∈ S x, HasAubinPropertyAt S x u := by
  constructor
  · intro h
    have hosc : SvOscWithinAt S univ x := by
      obtain ⟨V,hV,hVS⟩ := eventually_nhdsWithin_iff_exists_nhds.mp h.2.1
      have heq : 𝓝[V] x = 𝓝[univ] x := by rw [nhdsWithin_eq_nhds.mpr hV,nhdsWithin_univ]
      have hVstrict := h.of_nhdsWithin_eq (mem_of_mem_nhds hV) heq.symm
      have hVosc := hVstrict.svOscWithinAt (fun a ha ↦ hVS a ⟨mem_univ a,ha⟩)
      simpa only [SvOscWithinAt,svOuterLimitWithin,heq] using hVosc
    exact ⟨by simpa only [svOscWithinAt_univ] using hosc,fun u hu ↦ h.hasAubinPropertyAt hu⟩
  · rintro ⟨ho,hA⟩
    obtain ⟨u,hu⟩ := hne
    obtain ⟨k,V,hV,W,hW,H⟩ := (hA u hu).2.2.2
    have hneV (a : E) (ha : a ∈ V) : (S a).Nonempty := by
      obtain ⟨w,hw,_⟩ := H x ⟨mem_univ x,mem_of_mem_nhds hV⟩ a ⟨mem_univ a,ha⟩ u ⟨hu,mem_of_mem_nhds hW⟩
      exact ⟨w,hw⟩
    have hS : ∀ᶠ a in 𝓝[univ] x, (S a).Nonempty ∧ IsClosed (S a) := by
      rw [nhdsWithin_univ]
      exact Filter.eventually_of_mem hV fun a ha ↦ ⟨hneV a ha,hclosed a⟩
    apply (svStrictlyContinuousWithinAt_iff_local_transport_of_eventually (mem_univ x) hS).mpr
    exact exists_local_transport_of_aubinEstimates (mem_univ x) (hclosed x) (by simpa only [svOscWithinAt_univ] using ho) (fun u hu ↦ (hA u hu).2.2.2)

/-- The nonempty-base-fiber hypothesis in the absolute equivalence is
necessary: an empty mapping satisfies the right side vacuously. -/
theorem empty_mapping_graphical_localization_counterexample :
    SvOscAt (fun _ : ℝ ↦ (∅ : Set ℝ)) 0 ∧
      (∀ u ∈ (∅ : Set ℝ), HasAubinPropertyAt (fun _ : ℝ ↦ (∅ : Set ℝ)) 0 u) ∧
      ¬ SvStrictlyContinuousAt (fun _ : ℝ ↦ (∅ : Set ℝ)) 0 := by
  refine ⟨svOscAt_const isClosed_empty _,fun _ hu ↦ hu.elim,?_⟩
  intro h
  have hh := mem_of_mem_nhdsWithin (mem_univ (0:ℝ)) h.2.1
  exact hh.1.ne_empty rfl

end RW
