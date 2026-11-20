/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Closed convex adjoints of sublinear mappings
-/
import RockafellarWets.Chapter8.GraphicalRegularity
import RockafellarWets.Chapter11.PolarConeOperations

open Set
open scoped InnerProductSpace Pointwise
namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem mem_svLowerAdjoint_iff_polarCone {H : E → Set F} {y : F} {v : E} :
    v ∈ svLowerAdjoint H y ↔ WithLp.toLp 2 (-v,y) ∈ polarCone (euclideanSvGraph H) := by
  constructor
  · intro h p hp
    have hh := h p.fst p.snd hp
    change ⟪WithLp.toLp 2 (-v,y),p⟫_ℝ ≤ 0
    simpa [WithLp.prod_inner_apply,inner_neg_left] using sub_nonpos.mpr hh
  · intro h w z hz
    have hh := h (WithLp.toLp 2 (w,z)) hz
    simpa [WithLp.prod_inner_apply,inner_neg_left] using hh

theorem svLowerAdjoint_eq_neg_upperAdjoint (H : E → Set F) (y : F) :
    svLowerAdjoint H y = -(svUpperAdjoint H (-y)) := by
  ext v
  simp only [mem_neg,svLowerAdjoint,svUpperAdjoint,mem_setOf_eq,inner_neg_left,neg_le_neg_iff]

theorem svUpperAdjoint_properties (H : E → Set F) :
    SvOsc (svUpperAdjoint H) ∧ SvSublinear (svUpperAdjoint H) := by
  have he : svGraph (svUpperAdjoint H) = (euclideanNormalCoordinates (E := E) (F := F)) ⁻¹' polarCone (euclideanSvGraph H) := by
    exact congrArg svGraph (svOfEuclideanNormals_polarCone (euclideanSvGraph H)).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [← isClosed_svGraph_iff_svOsc,he]
    exact (isClosed_polarCone _).preimage (euclideanNormalCoordinates (E := E) (F := F)).continuous
  · rw [svPositivelyHomogeneous_iff_isCone_svGraph,he]
    exact LinearMap.isCone_preimage (euclideanNormalCoordinates (E := E) (F := F)).toLinearMap (isCone_polarCone _)
  · change Convex ℝ (svGraph (svUpperAdjoint H))
    rw [he]
    exact (convex_polarCone _).linear_preimage (euclideanNormalCoordinates (E := E) (F := F)).toLinearMap

theorem svLowerAdjoint_properties (H : E → Set F) :
    SvOsc (svLowerAdjoint H) ∧ SvSublinear (svLowerAdjoint H) := by
  have he : svGraph (svLowerAdjoint H) = (-(euclideanNormalCoordinates (E := E) (F := F))) ⁻¹' polarCone (euclideanSvGraph H) := by
    ext p
    change p.2 ∈ svLowerAdjoint H p.1 ↔ WithLp.toLp 2 (-p.2,- -p.1) ∈ polarCone (euclideanSvGraph H)
    simpa only [neg_neg] using (mem_svLowerAdjoint_iff_polarCone (H := H) (y := p.1) (v := p.2))
  refine ⟨?_, ?_, ?_⟩
  · rw [← isClosed_svGraph_iff_svOsc,he]
    exact (isClosed_polarCone _).preimage (-(euclideanNormalCoordinates (E := E) (F := F))).continuous
  · rw [svPositivelyHomogeneous_iff_isCone_svGraph,he]
    exact LinearMap.isCone_preimage (-(euclideanNormalCoordinates (E := E) (F := F))).toLinearMap (isCone_polarCone _)
  · change Convex ℝ (svGraph (svLowerAdjoint H))
    rw [he]
    exact (convex_polarCone _).linear_preimage (-(euclideanNormalCoordinates (E := E) (F := F))).toLinearMap

theorem SvSublinear.convex_euclideanSvGraph {H : E → Set F} (hh : SvSublinear H) :
    Convex ℝ (euclideanSvGraph H) :=
  hh.2.linear_preimage (WithLp.prodContinuousLinearEquiv 2 ℝ E F).toLinearMap

theorem SvSublinear.isCone_euclideanSvGraph {H : E → Set F} (hh : SvSublinear H) :
    IsCone (euclideanSvGraph H) :=
  LinearMap.isCone_preimage (WithLp.prodContinuousLinearEquiv 2 ℝ E F).toLinearMap
    (svPositivelyHomogeneous_iff_isCone_svGraph.mp hh.1)

theorem SvOsc.isClosed_euclideanSvGraph {H : E → Set F} (hh : SvOsc H) :
    IsClosed (euclideanSvGraph H) :=
  (isClosed_svGraph_iff_svOsc.mpr hh).preimage (WithLp.prodContinuousLinearEquiv 2 ℝ E F).continuous

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- Upper and lower adjoints are inverse correspondences on closed convex graphs. -/
theorem svLowerAdjoint_svUpperAdjoint {H : E → Set F} (hh : SvSublinear H) (ho : SvOsc H) :
    svLowerAdjoint (svUpperAdjoint H) = H := by
  letI := FiniteDimensional.complete ℝ (WithLp 2 (E×F))
  have he := svOfEuclideanGraph_polarCone (polarCone (euclideanSvGraph H))
  rw [svOfEuclideanNormals_polarCone] at he
  rw [polarCone_bipolar_eq_self ho.isClosed_euclideanSvGraph hh.convex_euclideanSvGraph
    hh.isCone_euclideanSvGraph] at he
  exact he.symm

end RW
