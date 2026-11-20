/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Metric regularity and linear openness
-/

import RockafellarWets.Chapter9.InverseEstimates

open Filter Metric Set Topology
open scoped NNReal ENNReal

namespace RW

variable {E F : Type*} [MetricSpace E] [MetricSpace F]
    {S : E → Set F} {x : E} {u : F} {k l : ℝ≥0}

/-- Local closedness of the graph survives inversion. -/
theorem IsLocallyClosedAt.inverseGraph (hl : IsLocallyClosedAt (svGraph S) (x,u)) :
    IsLocallyClosedAt (svGraph (svInv S)) (u,x) := by
  obtain ⟨V,hV,hVc,hC⟩ := hl
  refine ⟨Prod.swap ⁻¹' V,continuous_swap.continuousAt.preimage_mem_nhds hV,
    hVc.preimage continuous_swap,?_⟩
  exact hC.preimage continuous_swap

/-- The fixed-constant local distance inequality of 9.43(b). -/
def MetricRegularityEstimate (S : E → Set F) (x : E) (u : F) (k : ℝ≥0) : Prop :=
  ∃ V ∈ 𝓝 x, ∃ W ∈ 𝓝 u, InverseMetricEstimate S univ W V k

/-- Linear openness in 9.43(c), expressed by the realizing point in the
preimage of each nearby target. -/
def LinearOpenEstimate (S : E → Set F) (x : E) (u : F) (k : ℝ≥0) : Prop :=
  ∃ V ∈ 𝓝 x, ∃ W ∈ 𝓝 u, InverseOpenEstimate S univ W V k

/-- Inverting the extended Aubin estimate gives the transport formulation of
linear openness with the same constant. -/
theorem linearOpenEstimate_iff_extendedAubinInverse :
    LinearOpenEstimate S x u k ↔ ExtendedAubinEstimate (svInv S) univ u x k := by
  simp only [LinearOpenEstimate,← inverseTransportEstimate_iff_openEstimate]
  constructor
  · rintro ⟨V,hV,W,hW,H⟩
    exact ⟨W,hW,V,hV,fun a _ b hb y hy ↦ H a trivial b hb.2 y hy.2 hy.1⟩
  · rintro ⟨W,hW,V,hV,H⟩
    exact ⟨V,hV,W,hW,fun a _ b hb y hy ha ↦ H a trivial b ⟨trivial,hb⟩ y ⟨ha,hy⟩⟩

/-- A positive linear openness constant is a metric regularity constant. -/
theorem LinearOpenEstimate.metricEstimate (h : LinearOpenEstimate S x u k) (hk : 0 < k) :
    MetricRegularityEstimate S x u k := by
  obtain ⟨V,hV,W,hW,H⟩ := h
  exact ⟨V,hV,W,hW,((inverseTransportEstimate_iff_openEstimate).mpr H).metricEstimate hk⟩

/-- An arbitrarily larger constant converts metric regularity to linear
openness, without any global closed-graph hypothesis. -/
theorem MetricRegularityEstimate.linearOpenEstimate_of_lt (h : MetricRegularityEstimate S x u k) (hkl : k < l) :
    LinearOpenEstimate S x u l := by
  obtain ⟨V,hV,W,hW,H⟩ := h
  exact ⟨V,hV,W,hW,inverseTransportEstimate_iff_openEstimate.mp (H.transportEstimate_of_lt hkl)⟩

/-- **Theorem 9.43(a–c).** Local inverse Lipschitz behavior is equivalent
to a metric regularity estimate. -/
theorem hasAubinProperty_inverse_iff_metricRegularity (hu : u ∈ S x)
    (hl : IsLocallyClosedAt (svGraph S) (x,u)) :
    HasAubinPropertyAt (svInv S) u x ↔ ∃ k : ℝ≥0, MetricRegularityEstimate S x u k := by
  constructor
  · rintro ⟨_,_,_,k,hk⟩
    have hpos : 0 < k+1 := by positivity
    have h := (extendedAubinEstimate_iff_of_pos (mem_univ u) hu hpos).mpr (hk.mono (by simp))
    exact ⟨k+1,(linearOpenEstimate_iff_extendedAubinInverse.mpr h).metricEstimate hpos⟩
  · rintro ⟨k,hk⟩
    exact ⟨trivial,hu,hl.inverseGraph,k+1,(linearOpenEstimate_iff_extendedAubinInverse.mp
      (hk.linearOpenEstimate_of_lt (by simp))).toAubinEstimate⟩

/-- **Theorem 9.43(a–c)** in terms of linear openness. -/
theorem hasAubinProperty_inverse_iff_linearOpen (hu : u ∈ S x)
    (hl : IsLocallyClosedAt (svGraph S) (x,u)) :
    HasAubinPropertyAt (svInv S) u x ↔ ∃ k : ℝ≥0, LinearOpenEstimate S x u k := by
  constructor
  · rintro ⟨_,_,_,k,hk⟩
    exact ⟨k+1,linearOpenEstimate_iff_extendedAubinInverse.mpr
      ((extendedAubinEstimate_iff_of_pos (mem_univ u) hu (by positivity)).mpr (hk.mono (by simp)))⟩
  · rintro ⟨k,hk⟩
    exact ⟨trivial,hu,hl.inverseGraph,k,(linearOpenEstimate_iff_extendedAubinInverse.mp hk).toAubinEstimate⟩

/-- **Theorem 9.43**, equality of the metric regularity infimum and the exact
inverse graphical Lipschitz modulus. -/
theorem graphicalLipschitzModulus_inverse_eq_iInf_metric (hu : u ∈ S x) :
    graphicalLipschitzModulus (svInv S) u x =
      ⨅ k : {k : ℝ≥0 // MetricRegularityEstimate S x u k}, ((k : ℝ≥0) : ℝ≥0∞) := by
  apply le_antisymm
  · apply le_iInf
    intro k
    by_contra! hgt
    obtain ⟨l,hl₁,hl₂⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hgt
    have h := (linearOpenEstimate_iff_extendedAubinInverse.mp
      (k.2.linearOpenEstimate_of_lt (ENNReal.coe_lt_coe.mp hl₁))).toAubinEstimate.modulus_le
    exact hl₂.not_ge h
  · by_contra! hgt
    obtain ⟨k,hk₁,hk₂⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hgt
    have hk : 0 < k := ENNReal.coe_pos.mp (lt_of_le_of_lt bot_le hk₁)
    have h := linearOpenEstimate_iff_extendedAubinInverse.mpr
      ((extendedAubinEstimate_iff_of_pos (mem_univ u) hu hk).mpr (aubinEstimate_of_modulus_lt hk₁))
    exact hk₂.not_ge (iInf_le (fun k : {k : ℝ≥0 // MetricRegularityEstimate S x u k} ↦ ((k:ℝ≥0):ℝ≥0∞))
      ⟨k,h.metricEstimate hk⟩)

/-- The linear openness infimum has the same exact value, also at zero or
infinite modulus. -/
theorem graphicalLipschitzModulus_inverse_eq_iInf_open (hu : u ∈ S x) :
    graphicalLipschitzModulus (svInv S) u x =
      ⨅ k : {k : ℝ≥0 // LinearOpenEstimate S x u k}, ((k : ℝ≥0) : ℝ≥0∞) := by
  apply le_antisymm
  · exact le_iInf fun k ↦ (linearOpenEstimate_iff_extendedAubinInverse.mp k.2).toAubinEstimate.modulus_le
  · by_contra! hgt
    obtain ⟨k,hk₁,hk₂⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hgt
    have hk : 0 < k := ENNReal.coe_pos.mp (lt_of_le_of_lt bot_le hk₁)
    have h := linearOpenEstimate_iff_extendedAubinInverse.mpr
      ((extendedAubinEstimate_iff_of_pos (mem_univ u) hu hk).mpr (aubinEstimate_of_modulus_lt hk₁))
    exact hk₂.not_ge (iInf_le (fun k : {k : ℝ≥0 // LinearOpenEstimate S x u k} ↦ ((k:ℝ≥0):ℝ≥0∞)) ⟨k,h⟩)

end RW
