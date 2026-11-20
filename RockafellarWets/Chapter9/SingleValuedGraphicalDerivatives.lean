/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Graphical derivatives of strictly continuous single-valued mappings
-/

import RockafellarWets.Chapter9.GraphicalDerivativeLipschitz
import RockafellarWets.Chapter9.SemidifferentiabilityFromAubin
import RockafellarWets.Chapter9.HomogeneousMappingNorms
import RockafellarWets.Chapter8.SingleValuedSemiderivatives
import RockafellarWets.Chapter6.ElementaryCones

open Filter Metric Set Topology
open scoped NNReal ENNReal

namespace RW

section Metric

variable {E F : Type*} [MetricSpace E] [MetricSpace F] {f : E → F} {x : E} {k : ℝ≥0}

theorem aubinEstimate_singleton_of_lipschitz {U : Set E} (hU : U ∈ 𝓝 x)
    (hf : LipschitzOnWith k f U) : AubinEstimate (svSingleton f) univ x (f x) k := by
  refine ⟨U,hU,univ,univ_mem,?_⟩
  intro a ha b hb v hv
  have he : v = f a := hv.1
  exact ⟨f b,rfl,he ▸ hf.dist_le_mul a ha.2 b hb.2⟩

theorem aubinEstimate_singleton_iff (hc : ContinuousAt f x) :
    AubinEstimate (svSingleton f) univ x (f x) k ↔ ∃ U ∈ 𝓝 x, LipschitzOnWith k f U := by
  refine ⟨?_,fun ⟨U,hU,hf⟩ ↦ aubinEstimate_singleton_of_lipschitz hU hf⟩
  rintro ⟨V,hV,W,hW,H⟩
  refine ⟨V ∩ f ⁻¹' W,inter_mem hV (hc.preimage_mem_nhds hW),
    LipschitzOnWith.of_dist_le_mul fun a ha b hb ↦ ?_⟩
  obtain ⟨z,hz,hd⟩ := H a ⟨trivial,ha.1⟩ b ⟨trivial,hb.1⟩ (f a) ⟨rfl,ha.2⟩
  have he : z = f b := hz
  simpa only [he] using hd

/-- At continuous single-valued mappings the graphical modulus is the
ordinary local Lipschitz modulus. -/
theorem graphicalLipschitzModulus_singleton (hc : ContinuousAt f x) :
    graphicalLipschitzModulus (svSingleton f) x (f x) = lipschitzModulus f x := by
  apply le_antisymm
  · apply le_iInf
    intro k
    obtain ⟨U,hU,hf⟩ := k.2
    exact (aubinEstimate_singleton_of_lipschitz (by simpa only [nhdsWithin_univ] using hU) hf).modulus_le
  · apply le_iInf
    intro k
    obtain ⟨U,hU,hf⟩ := (aubinEstimate_singleton_iff hc).mp k.2
    exact lipschitzModulus_le hU hf

/-- Interior points of a single-valued domain have an Aubin estimate under
relative strict continuity. -/
theorem StrictlyContinuousWithinAt.exists_aubinEstimate_restrict_singleton {D : Set E}
    (hf : StrictlyContinuousWithinAt f D x) (hx : x ∈ interior D) :
    ∃ k, AubinEstimate (svRestrict (svSingleton f) D) univ x (f x) k := by
  obtain ⟨_,k,U,hU,hL⟩ := strictlyContinuousWithinAt_iff.mp hf
  have hD : D ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp hx
  rw [nhdsWithin_eq_nhds.mpr hD] at hU
  refine ⟨k,U ∩ D,inter_mem hU hD,univ,univ_mem,?_⟩
  intro a ha b hb v hv
  have he : v = f a := hv.1.1
  exact ⟨f b,⟨rfl,hb.2.2⟩,he ▸ hL.dist_le_mul a ha.2.1 b hb.2.1⟩

end Metric

section Normed

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : E → F} {x : E}

omit [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
theorem StrictlyContinuousAt.hasAubinProperty_singleton (hf : StrictlyContinuousAt f x) :
    HasAubinPropertyAt (svSingleton f) x (f x) := by
  obtain ⟨k,U,hU,hL⟩ := strictlyContinuousAt_iff.mp hf
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp hU
  have hsub : closedBall x (r/2) ⊆ U := fun y hy ↦ hrU
    (show dist y x < r from lt_of_le_of_lt hy (half_lt_self hr))
  have hc := (isCompact_closedBall x (r/2)).image_of_continuousOn
    (continuousOn_id.prodMk (hL.mono hsub).continuousOn)
  have he : svGraph (svSingleton f) ∩ (closedBall x (r/2) ×ˢ (univ : Set F)) =
      (fun y ↦ (y,f y)) '' closedBall x (r/2) := by
    ext ⟨y,v⟩
    constructor
    · rintro ⟨hv,hy,_⟩
      exact ⟨y,hy,Prod.ext rfl (show f y = v from hv.symm)⟩
    · rintro ⟨a,ha,he⟩
      cases he
      exact ⟨rfl,ha,trivial⟩
  refine ⟨trivial,rfl,?_,k,aubinEstimate_singleton_of_lipschitz hU hL⟩
  exact ⟨closedBall x (r/2) ×ˢ univ,prod_mem_nhds (closedBall_mem_nhds _ (half_pos hr)) univ_mem,
    isClosed_closedBall.prod isClosed_univ,he ▸ hc.isClosed⟩

/-- **Exercise 9.49(b)**: the exact ordinary modulus is a global Lipschitz
constant for the single-valued mapping's graphical derivative. -/
theorem StrictlyContinuousAt.graphicalDerivative_lipschitz (hf : StrictlyContinuousAt f x) :
    SvLipschitzOnWith (lipschitzModulus f x).toNNReal
      (graphicalDerivative (svSingleton f) x (f x)) univ := by
  simpa only [graphicalLipschitzModulus_singleton hf.continuousAt] using
    hf.hasAubinProperty_singleton.graphicalDerivative_lipschitz

/-- **Exercise 9.49(b)**: all derivative fibers are locally bounded, since
the zero-direction fiber is the zero singleton. -/
theorem StrictlyContinuousAt.graphicalDerivative_locallyBounded (hf : StrictlyContinuousAt f x) :
    SvLocallyBounded (graphicalDerivative (svSingleton f) x (f x)) := by
  obtain ⟨k,hk⟩ := hf.hasAubinProperty_singleton.2.2.2
  have hzero : graphicalDerivative (svSingleton f) x (f x) 0 = {0} := by
    rw [hk.graphicalDerivative_zero]
    exact tangentCone_singleton _
  have hom : SvPositivelyHomogeneous (graphicalDerivative (svSingleton f) x (f x)) :=
    svPositivelyHomogeneous_iff_isCone_svGraph.mpr ((svGraph_graphicalDerivative (svSingleton f) x (f x)) ▸
      isCone_tangentCone (show (x,f x) ∈ svGraph (svSingleton f) from rfl))
  apply hom.svLocallyBounded_of_svOuterNorm_lt_top
  apply lt_of_le_of_lt (hom.svOuterNorm_le_iff.mpr ?_) (ENNReal.coe_lt_top (r := k))
  intro w z hz
  obtain ⟨v,hv,hd⟩ := hk.graphicalDerivative_transport hz 0
  have hv0 : v = 0 := by simpa only [hzero,mem_singleton_iff] using hv
  simpa [hv0] using hd

/-- **Exercise 9.49(b)**, the fixed-direction difference quotient formula. -/
theorem StrictlyContinuousAt.graphicalDerivative_eq_outer_fixed (hf : StrictlyContinuousAt f x) (w : E) :
    graphicalDerivative (svSingleton f) x (f x) w =
      outerSetLimitAlong (𝓝[>] (0:ℝ)) (fun t ↦ mappingDifferenceQuotient (svSingleton f) x (f x) t w) := by
  obtain ⟨k,hk⟩ := hf.hasAubinProperty_singleton.2.2.2
  exact hk.graphicalDerivative_eq_outer_fixed w

omit [FiniteDimensional ℝ E] in
/-- **Proposition 9.50(b)**: relative strict continuity at an interior point
of the domain makes proto-differentiability equivalent to semidifferentiability. -/
theorem hasMappingSemiderivative_restrict_singleton_iff_proto {D : Set E}
    (hf : StrictlyContinuousWithinAt f D x) (hx : x ∈ interior D) :
    HasMappingSemiderivative (svRestrict (svSingleton f) D) x (f x)
      (graphicalDerivative (svRestrict (svSingleton f) D) x (f x)) ↔
        IsProtoDifferentiableAt (svRestrict (svSingleton f) D) x (f x) := by
  obtain ⟨k,hk⟩ := hf.exists_aubinEstimate_restrict_singleton hx
  exact ⟨fun h ↦ h.protoDerivative.1,hk.hasMappingSemiderivative⟩

omit [FiniteDimensional ℝ E] in
/-- The calmness clause of **Proposition 9.50(b)**. A single-valued graphical
derivative and a local growth bound already force semidifferentiability. -/
theorem hasMappingSemiderivative_restrict_singleton_of_calm {D : Set E} {A : E → F}
    (hx : x ∈ interior D)
    (hc : ∃ k : ℝ, 0 ≤ k ∧ ∀ᶠ y in 𝓝[D] x, dist (f y) (f x) ≤ k*dist y x)
    (hd : graphicalDerivative (svRestrict (svSingleton f) D) x (f x) = svSingleton A) :
    HasMappingSemiderivative (svRestrict (svSingleton f) D) x (f x) (svSingleton A) := by
  obtain ⟨k,hk,hc⟩ := hc
  have hD : D ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp hx
  rw [nhdsWithin_eq_nhds.mpr hD] at hc
  apply hasMappingSemiderivative_of_linearGrowth hd
  refine ⟨k,hk,?_⟩
  filter_upwards [hD,hc] with y hy hcy
  refine ⟨⟨f y,rfl,hy⟩,fun v hv ↦ ?_⟩
  have he : v = f y := hv.1
  simpa only [he,dist_eq_norm] using hcy

end Normed
end RW
