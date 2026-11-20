/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Generic continuity of subgradient and coderivative mappings
-/

import RockafellarWets.Chapter8.GraphicalRegularity
import RockafellarWets.Chapter8.SubgradientLimits
import RockafellarWets.Chapter5.GenericContinuity
import RockafellarWets.Chapter5.GraphMetric

open Filter Set Topology

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The finite graph coordinates of the function-attentive topology on
a subset of the domain. -/
def attentiveGraphOn (f : E → EReal) (X : Set E) : Set (E × ℝ) :=
  {p | p.1 ∈ X ∧ f p.1 = (p.2 : EReal)}

omit [InnerProductSpace ℝ E] in
theorem tendsto_fst_attentiveGraphOn {f : E → EReal} {X : Set E} {p : E × ℝ}
    (hp : p ∈ attentiveGraphOn f X) :
    Tendsto Prod.fst (𝓝[attentiveGraphOn f X] p) (attentiveNhds f p.1) := by
  have hs := (continuous_snd.tendsto p).mono_left (nhdsWithin_le_nhds (s := attentiveGraphOn f X))
  refine tendsto_attentiveNhds_iff.mpr ⟨(continuous_fst.tendsto p).mono_left nhdsWithin_le_nhds,?_⟩
  rw [hp.2]
  apply (EReal.tendsto_coe.mpr hs).congr'
  filter_upwards [self_mem_nhdsWithin] with q hq using hq.2.symm

omit [InnerProductSpace ℝ E] in
private theorem svOscOn_attentiveGraphOn {F : Type*} [TopologicalSpace F] {f : E → EReal}
    {D : E → Set F} (X : Set E)
    (ho : ∀ x ∈ X, ∀ c : ℝ, f x = c → outerSetLimitAlong (attentiveNhds f x) D ⊆ D x) :
    SvOscOn (fun p : E × ℝ ↦ D p.1) (attentiveGraphOn f X) := by
  intro p hp
  exact (outerSetLimitAlong_mono_filter (tendsto_fst_attentiveGraphOn hp) D).trans
    (ho p.1 hp.1 p.2 hp.2)

variable [FiniteDimensional ℝ E]

/-- **Exercise 8.54(a)**. The ordinary and cosmic subgradient mappings have
meager sets of discontinuity points in the attentive topology on their
domains. More generally, each assertion holds relative to any chosen
subset of the finite graph. -/
theorem isMeagre_subgradient_discontinuities (f : E → EReal) (X : Set E) :
    IsMeagre {p : attentiveGraphOn f X | ¬ SvContinuousWithinAt
      (fun q : E × ℝ ↦ subdifferential f q.1) (attentiveGraphOn f X) p.val} ∧
    IsMeagre {p : attentiveGraphOn f X | ¬ SvContinuousWithinAt
      (fun q : E × ℝ ↦ cosmicSet (subdifferential f q.1) (horizonSubdifferential f q.1))
      (attentiveGraphOn f X) p.val} :=
  ⟨isMeagre_not_svContinuousWithinAt_of_svOscOn (svOscOn_attentiveGraphOn X
    (fun _ _ _ hx ↦ outerSetLimitAlong_subdifferential_subset hx)),
    isMeagre_not_svContinuousWithinAt_of_svOscOn (svOscOn_attentiveGraphOn X
      (fun _ _ _ hx ↦ outerSetLimitAlong_cosmicSubdifferential_subset hx))⟩

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The coderivative as a point of the metrized space of nonempty graphs
of outer semicontinuous mappings. -/
def coderivativeModel (S : E → Set F) (p : euclideanSvGraph S) : OscMapModel F E where
  toFun := coderivative S p.val.fst p.val.snd
  svOsc' := (graphicalDerivative_properties (S := S) p.property).2.2.1.1
  dom_nonempty := ⟨0,0,(graphicalDerivative_properties (S := S) p.property).2.2.1.2.1⟩

/-- **Exercise 8.54(b)**, continuity is measured in the graphical topology
on the space of coderivatives, relative to the original graph. -/
theorem isMeagre_coderivative_discontinuities (S : E → Set F) :
    IsMeagre {p : euclideanSvGraph S | ¬ ContinuousAt (coderivativeModel S) p} := by
  let C := euclideanSvGraph S
  let G := fun p : WithLp 2 (E × F) ↦ svGraph (coderivative S p.fst p.snd)
  have hosc : SvOscOn G C := by
    intro p hp y hy
    let T := euclideanNormalCoordinates (E := E) (F := F)
    apply svOscOn_normalCone C p hp
    intro V hV
    refine (hy (T ⁻¹' V) (T.continuous.continuousAt hV)).mono ?_
    rintro q ⟨v,hv,hvV⟩
    exact ⟨T v,hv,hvV⟩
  apply (isMeagre_not_svContinuousWithinAt_of_svOscOn hosc).mono
  intro p hn
  change ¬ ContinuousAt (coderivativeModel S) p at hn
  intro hc
  apply hn
  apply tendsto_nhds_iff_seq_tendsto.mpr
  intro ps hps
  apply OscMapModel.tendsto_iff_graphicalConverges.mpr
  let pseq (n : ℕ) := (ps n).val
  have hpseq : Tendsto pseq atTop (𝓝[C] p.val) := tendsto_nhdsWithin_of_forall_mem
    (fun n ↦ (ps n).property) ((continuous_subtype_val.tendsto p).comp hps)
  have hi := hc.2.trans (innerSetLimitAlong_subset_innerSetLimit_comp (C := G) hpseq)
  have ho := (outerSetLimit_comp_subset (C := G) hpseq).trans hc.1
  have hio := innerSetLimit_subset_outerSetLimit (G ∘ pseq)
  exact ⟨Subset.antisymm (hio.trans ho) hi,Subset.antisymm ho (hi.trans hio)⟩

end RW
