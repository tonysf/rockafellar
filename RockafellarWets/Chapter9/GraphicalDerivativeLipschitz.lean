/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lipschitz properties and horizons of graphical derivatives
-/

import RockafellarWets.Chapter9.AubinGraphicalDerivatives
import RockafellarWets.Chapter3.PointedCones

open Filter Metric Set Topology
open scoped NNReal ENNReal Pointwise

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {S : E → Set F} {x : E} {u : F} {k : ℝ≥0}

/-- An Aubin estimate makes every graphical derivative fiber nonempty and closed. -/
theorem AubinEstimate.graphicalDerivative_nonemptyClosedValued (h : AubinEstimate S univ x u k)
    (hu : u ∈ S x) : NonemptyClosedValuedOn (graphicalDerivative S x u) univ := by
  intro w _
  refine ⟨(h.exists_graphicalDerivative_norm_le hu w).imp fun _ hz ↦ hz.1,?_⟩
  exact (isClosed_tangentCone (euclideanSvGraph S) (WithLp.toLp 2 (x,u))).preimage
    ((WithLp.prod_continuous_toLp 2 E F).comp (continuous_const.prodMk continuous_id))

/-- Every admissible Aubin constant is a global Lipschitz constant for the
graphical derivative mapping. -/
theorem AubinEstimate.graphicalDerivative_lipschitz (h : AubinEstimate S univ x u k)
    (hu : u ∈ S x) : SvLipschitzOnWith k (graphicalDerivative S x u) univ := by
  apply (svLipschitzOnWith_iff_transport (h.graphicalDerivative_nonemptyClosedValued hu)).mpr
  exact fun _ _ b _ _ hv ↦ h.graphicalDerivative_transport hv b

/-- **Exercise 9.49(a)**: the exact, possibly zero, graphical modulus is a
global Lipschitz constant for the derivative. -/
theorem HasAubinPropertyAt.graphicalDerivative_lipschitz (h : HasAubinPropertyAt S x u) :
    SvLipschitzOnWith (graphicalLipschitzModulus S x u).toNNReal
      (graphicalDerivative S x u) univ := by
  obtain ⟨_,hu,_,k,hk⟩ := h
  letI : Nonempty {k : ℝ≥0 // AubinEstimate S univ x u k} := ⟨⟨k,hk⟩⟩
  have hfin : graphicalLipschitzModulus S x u ≠ ⊤ :=
    (hk.modulus_le.trans_lt ENNReal.coe_lt_top).ne
  refine ⟨hk.graphicalDerivative_nonemptyClosedValued hu,fun a _ b _ ↦ ?_⟩
  have hb : hausdorffEDist (graphicalDerivative S x u a) (graphicalDerivative S x u b) ≤
      graphicalLipschitzModulus S x u * edist a b := by
    rw [graphicalLipschitzModulus,graphicalLipschitzModulusWithin,
      ENNReal.iInf_mul (by intro he; exact (edist_ne_top a b he).elim)]
    apply le_iInf
    intro l
    simpa [edist_dist,ENNReal.ofReal_mul] using
      (l.2.graphicalDerivative_lipschitz hu).2 a trivial b trivial
  simpa [ENNReal.ofReal_mul,ENNReal.coe_toNNReal hfin,edist_dist] using hb

/-- **Exercise 9.49(a)**: the derivative in the zero direction is the tangent
cone to the fiber at the base point. -/
theorem AubinEstimate.graphicalDerivative_zero (h : AubinEstimate S univ x u k) :
    graphicalDerivative S x u 0 = tangentCone (S x) u := by
  rw [h.graphicalDerivative_eq_outer_fixed,tangentCone_eq_outerSetLimitAlong]
  congr 1
  funext t
  simp only [mappingDifferenceQuotient,smul_zero,add_zero,blowUp]

/-- Bounded transport between two derivative fibers makes their horizon
cones equal. -/
theorem AubinEstimate.graphicalDerivative_horizons_eq (h : AubinEstimate S univ x u k) (a b : E) :
    horizonCone (graphicalDerivative S x u a) = horizonCone (graphicalDerivative S x u b) := by
  have hsub (a b : E) : graphicalDerivative S x u a ⊆
      graphicalDerivative S x u b + closedBall (0:F) (k*dist a b) := by
    intro v hv
    obtain ⟨z,hz,hd⟩ := h.graphicalDerivative_transport hv b
    exact ⟨z,hz,v-z,by simpa only [mem_closedBall_zero_iff,dist_eq_norm] using hd,by abel⟩
  have hhor (a b : E) : horizonCone (graphicalDerivative S x u a) ⊆
      horizonCone (graphicalDerivative S x u b) := by
    have hh := horizonCone_mono (hsub a b)
    rwa [horizonCone_add_eq_of_bounded_right (nonempty_closedBall.mpr (by positivity))
      isBounded_closedBall] at hh
  exact Subset.antisymm (hhor a b) (hhor b a)

/-- **Exercise 9.49(a)**: every derivative fiber has the tangent cone of the
original fiber as its horizon cone. -/
theorem AubinEstimate.horizon_graphicalDerivative (h : AubinEstimate S univ x u k)
    (hu : u ∈ S x) (w : E) :
    horizonCone (graphicalDerivative S x u w) = graphicalDerivative S x u 0 := by
  rw [h.graphicalDerivative_horizons_eq w 0,h.graphicalDerivative_zero,
    horizonCone_eq_self_of_isClosed_isCone (isClosed_tangentCone _ _) (isCone_tangentCone hu)]

end RW
