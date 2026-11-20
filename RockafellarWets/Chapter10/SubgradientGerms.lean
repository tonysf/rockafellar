/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Locality of subgradient calculus
-/

import RockafellarWets.Chapter9.LipschitzSubgradientLimits
import RockafellarWets.Chapter9.LocalizationDerivatives

open Filter Set Topology

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f g : E → EReal} {x : E} {a : ℝ}

theorem euclideanEpigraph_eventuallyEq_of_eventuallyEq (he : f =ᶠ[𝓝 x] g) (a : ℝ) :
    euclideanEpigraph f =ᶠ[𝓝 (WithLp.toLp 2 (x,a))] euclideanEpigraph g := by
  filter_upwards [((WithLp.continuous_fst 2 E ℝ).tendsto (WithLp.toLp 2 (x,a))).eventually he] with q hq
  change (f q.fst ≤ (q.snd:EReal)) = (g q.fst ≤ (q.snd:EReal))
  rw [hq]

theorem regularSubdifferential_congr_nhds_of_finite (hf : f x = a) (he : f =ᶠ[𝓝 x] g) :
    regularSubdifferential f x = regularSubdifferential g x := by
  have hg : g x = a := he.eq_of_nhds.symm.trans hf
  ext v
  rw [mem_regularSubdifferential_iff_epigraph_normal hf,mem_regularSubdifferential_iff_epigraph_normal hg,
    regularNormalCone_congr_nhds (euclideanEpigraph_eventuallyEq_of_eventuallyEq he a)]

theorem horizonSubdifferential_congr_nhds_of_locallyLsc
    (hf : f x = a) (hlf : IsLocallyLscAt f x) (hlg : IsLocallyLscAt g x) (he : f =ᶠ[𝓝 x] g) :
    horizonSubdifferential f x = horizonSubdifferential g x := by
  have hg : g x = a := he.eq_of_nhds.symm.trans hf
  ext v
  rw [mem_horizonSubdifferential_iff_epigraph_normal_of_locallyLsc hlf hf,
    mem_horizonSubdifferential_iff_epigraph_normal_of_locallyLsc hlg hg,
    normalCone_congr_nhds (euclideanEpigraph_eventuallyEq_of_eventuallyEq he a)]

theorem IsLocallyLscAt.congr_nhds (hl : IsLocallyLscAt f x) (he : f =ᶠ[𝓝 x] g) :
    IsLocallyLscAt g x := by
  have hf : f x = ((f x).toReal : EReal) := (EReal.coe_toReal hl.2.1 hl.1).symm
  have hg : g x = ((f x).toReal : EReal) := he.eq_of_nhds.symm.trans hf
  apply isLocallyLscAt_of_isLocallyClosedAt_epigraph hg
  apply hl.isLocallyClosedAt_epigraph.congr_nhds
  filter_upwards [(continuous_fst.tendsto (x,(f x).toReal)).eventually he] with q hq
  change (f q.1 ≤ (q.2:EReal)) = (g q.1 ≤ (q.2:EReal))
  rw [hq]

theorem IsSubdifferentiallyRegularAt.congr_nhds (hr : IsSubdifferentiallyRegularAt f x)
    (he : f =ᶠ[𝓝 x] g) : IsSubdifferentiallyRegularAt g x := by
  have hx := he.eq_of_nhds
  have hE := euclideanEpigraph_eventuallyEq_of_eventuallyEq he (f x).toReal
  refine ⟨hx ▸ hr.1,hx ▸ hr.2.1,?_⟩
  change IsClarkeRegularAt (euclideanEpigraph g) (WithLp.toLp 2 (x,(g x).toReal))
  rw [← hx]
  refine ⟨hr.2.2.1.congr_nhds hE,?_⟩
  rw [← normalCone_congr_nhds hE,← regularNormalCone_congr_nhds hE]
  exact hr.2.2.2

end RW
