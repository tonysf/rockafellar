/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Convex parametric minimization

The exact multiplier and directional formulas in Theorem 10.13.
-/

import RockafellarWets.Chapter10.ParametricSubderivatives
import RockafellarWets.Chapter8.ConvexSubgradients
import RockafellarWets.Chapter8.RegularSupportDuality

open Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

noncomputable section

variable {E P : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]

theorem convex_epigraph_parametricValue {f : WithLp 2 (E × P) → EReal}
    (hc : Convex ℝ (epigraph f)) (hl : LowerSemicontinuous f) (hb : IsParametricallyLevelBounded f) :
    Convex ℝ (epigraph (parametricValue f)) := by
  have hce : Convex ℝ (euclideanEpigraph (parametricValue f)) := by
    rw [euclideanEpigraph_parametricValue hl hb]
    exact (convex_preimage_continuousLinearEquiv (l2ProdEquiv (WithLp 2 (E × P))) hc).linear_image
      parametricEpigraphProjection.toLinearMap
  have he : (l2ProdEquiv P) '' euclideanEpigraph (parametricValue f) =
      epigraph (parametricValue f) := (l2ProdEquiv P).surjective.image_preimage _
  rw [← he]
  exact hce.linear_image (l2ProdEquiv P).toLinearMap

/-- **Theorem 10.13**, every optimal decision gives the same exact
subgradient multiplier set in the convex case. -/
theorem subdifferential_parametricValue_eq_at_minimizer {f : WithLp 2 (E × P) → EReal}
    (hc : Convex ℝ (epigraph f)) (hl : LowerSemicontinuous f) (hb : IsParametricallyLevelBounded f)
    {u : P} {a : ℝ} (hu : parametricValue f u = a) {x : E} (hx : x ∈ parametricMinimizers f u) :
    subdifferential (parametricValue f) u =
      {y | WithLp.toLp 2 ((0:E),y) ∈ subdifferential f (WithLp.toLp 2 (x,u))} := by
  have hxval := (mem_parametricMinimizers.mp hx).1.trans hu
  have he := normalCone_linear_image_of_convex (C := euclideanEpigraph f) parametricEpigraphProjection
    (convex_preimage_continuousLinearEquiv (l2ProdEquiv (WithLp 2 (E × P))) hc)
    (show WithLp.toLp 2 (WithLp.toLp 2 (x,u),a) ∈ euclideanEpigraph f from hxval.le)
  rw [← euclideanEpigraph_parametricValue hl hb] at he
  change normalCone (euclideanEpigraph (parametricValue f)) (WithLp.toLp 2 (u,a)) = _ at he
  ext y
  rw [mem_subdifferential_iff_epigraph_normal hu,he,mem_preimage,parametricEpigraphProjection_adjoint]
  exact (mem_subdifferential_iff_epigraph_normal hxval).symm

/-- The analogous exact horizon multiplier set. -/
theorem horizonSubdifferential_parametricValue_eq_at_minimizer {f : WithLp 2 (E × P) → EReal}
    (hc : Convex ℝ (epigraph f)) (hl : LowerSemicontinuous f) (hp : IsProper f)
    (hb : IsParametricallyLevelBounded f) {u : P} {a : ℝ} (hu : parametricValue f u = a)
    {x : E} (hx : x ∈ parametricMinimizers f u) :
    horizonSubdifferential (parametricValue f) u =
      {y | WithLp.toLp 2 ((0:E),y) ∈ horizonSubdifferential f (WithLp.toLp 2 (x,u))} := by
  have hxval := (mem_parametricMinimizers.mp hx).1.trans hu
  have hlx := isLocallyLscAt_of_isLocallyClosedAt_epigraph hxval
    (RW.IsClosed.isLocallyClosedAt (isClosed_epigraph_of_lsc_ereal f hl) _)
  have hlu := isLocallyLscAt_of_isLocallyClosedAt_epigraph hu
    (RW.IsClosed.isLocallyClosedAt (isClosed_epigraph_of_lsc_ereal _
      (lowerSemicontinuous_parametricValue hl hp hb)) _)
  have he := normalCone_linear_image_of_convex (C := euclideanEpigraph f) parametricEpigraphProjection
    (convex_preimage_continuousLinearEquiv (l2ProdEquiv (WithLp 2 (E × P))) hc)
    (show WithLp.toLp 2 (WithLp.toLp 2 (x,u),a) ∈ euclideanEpigraph f from hxval.le)
  rw [← euclideanEpigraph_parametricValue hl hb] at he
  change normalCone (euclideanEpigraph (parametricValue f)) (WithLp.toLp 2 (u,a)) = _ at he
  ext y
  rw [mem_horizonSubdifferential_iff_epigraph_normal_of_locallyLsc hlu hu,he,mem_preimage,
    parametricEpigraphProjection_adjoint]
  exact (mem_horizonSubdifferential_iff_epigraph_normal_of_locallyLsc hlx hxval).symm

theorem subdifferentials_parametricValue_eq_multipliers_of_convex {f : WithLp 2 (E × P) → EReal}
    (hc : Convex ℝ (epigraph f)) (hl : LowerSemicontinuous f) (hp : IsProper f)
    (hb : IsParametricallyLevelBounded f) {u : P} {a : ℝ} (hu : parametricValue f u = a) :
    subdifferential (parametricValue f) u = parametricMultipliers f u ∧
      horizonSubdifferential (parametricValue f) u = horizonParametricMultipliers f u := by
  constructor
  · apply Subset.antisymm (subdifferential_parametricValue_subset hl hb hu)
    rintro y ⟨x,hx,hy⟩
    rw [subdifferential_parametricValue_eq_at_minimizer hc hl hb hu hx]
    exact hy
  · apply Subset.antisymm (horizonSubdifferential_parametricValue_subset hl hb hu)
    rintro y ⟨x,hx,hy⟩
    rw [horizonSubdifferential_parametricValue_eq_at_minimizer hc hl hp hb hu hx]
    exact hy

/-- **Theorem 10.13**, the lower closure of the infimum of the lifted
subderivatives is the marginal subderivative. -/
theorem subderivative_parametricValue_eq_epiClosure {f : WithLp 2 (E × P) → EReal}
    (hc : Convex ℝ (epigraph f)) (hl : LowerSemicontinuous f) (hb : IsParametricallyLevelBounded f)
    {u : P} {a : ℝ} (hu : parametricValue f u = a) {x : E} (hx : x ∈ parametricMinimizers f u) :
    subderivative (parametricValue f) u =
      epiClosure (parametricValue (subderivative f (WithLp.toLp 2 (x,u)))) := by
  have hxval := (mem_parametricMinimizers.mp hx).1.trans hu
  have he := tangentCone_linear_image_of_convex (C := euclideanEpigraph f) parametricEpigraphProjection
    (convex_preimage_continuousLinearEquiv (l2ProdEquiv (WithLp 2 (E × P))) hc)
    (show WithLp.toLp 2 (WithLp.toLp 2 (x,u),a) ∈ euclideanEpigraph f from hxval.le)
  rw [← euclideanEpigraph_parametricValue hl hb] at he
  change tangentCone (euclideanEpigraph (parametricValue f)) (WithLp.toLp 2 (u,a)) = _ at he
  rw [← euclideanEpigraph_subderivative hu,← euclideanEpigraph_subderivative hxval,
    ← closure_euclideanEpigraph_parametricValue] at he
  apply eq_of_epigraph_eq
  apply (l2ProdEquiv P).surjective.preimage_injective
  change euclideanEpigraph (subderivative (parametricValue f) u) =
    (l2ProdEquiv P) ⁻¹' epigraph (epiClosure _)
  rw [epigraph_epiClosure]
  have hcl (S : Set (P × ℝ)) : (l2ProdEquiv P) ⁻¹' closure S =
      closure ((l2ProdEquiv P) ⁻¹' S) := (l2ProdEquiv P).toHomeomorph.preimage_closure S
  rw [hcl]
  exact he

/-- The nondegeneracy equivalence in the convex clause of 10.13. -/
theorem subdifferential_parametricValue_nonempty_iff {f : WithLp 2 (E × P) → EReal}
    (hc : Convex ℝ (epigraph f)) (hl : LowerSemicontinuous f) (hp : IsProper f)
    (hb : IsParametricallyLevelBounded f) {u : P} {a : ℝ} (hu : parametricValue f u = a) :
    (subdifferential (parametricValue f) u).Nonempty ↔ subderivative (parametricValue f) u 0 ≠ ⊥ := by
  have hlu := isLocallyLscAt_of_isLocallyClosedAt_epigraph hu
    (RW.IsClosed.isLocallyClosedAt (isClosed_epigraph_of_lsc_ereal _
      (lowerSemicontinuous_parametricValue hl hp hb)) _)
  exact (isSubdifferentiallyRegularAt_of_convex (convex_epigraph_parametricValue hc hl hb) hlu).1.subdifferential_nonempty_iff

/-- **Theorem 10.13**, the support formula when the subdifferential is nonempty. -/
theorem subderivative_parametricValue_eq_support_of_convex {f : WithLp 2 (E × P) → EReal}
    (hc : Convex ℝ (epigraph f)) (hl : LowerSemicontinuous f) (hp : IsProper f)
    (hb : IsParametricallyLevelBounded f) {u : P} {a : ℝ} (hu : parametricValue f u = a)
    (hn : (subdifferential (parametricValue f) u).Nonempty) {x : E} (hx : x ∈ parametricMinimizers f u) :
    subderivative (parametricValue f) u =
      supportFunction {y | WithLp.toLp 2 ((0:E),y) ∈ subdifferential f (WithLp.toLp 2 (x,u))} := by
  have hlu := isLocallyLscAt_of_isLocallyClosedAt_epigraph hu
    (RW.IsClosed.isLocallyClosedAt (isClosed_epigraph_of_lsc_ereal _
      (lowerSemicontinuous_parametricValue hl hp hb)) _)
  have hr := (isSubdifferentiallyRegularAt_of_convex (convex_epigraph_parametricValue hc hl hb) hlu).1
  rw [← subdifferential_parametricValue_eq_at_minimizer hc hl hb hu hx]
  exact (hr.subderivative_support_duality hn).2.2.1

end

end RW
