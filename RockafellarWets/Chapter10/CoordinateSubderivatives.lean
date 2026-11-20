/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 10: Subderivatives and regularity under changes of coordinates
-/

import RockafellarWets.Chapter10.CoordinateSubgradients
import RockafellarWets.Chapter10.BasicChainSubderivatives

open Set

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  {G : E → F} {g : F → EReal} {x : E} {c : ℝ}

/-- **Exercise 10.7**, exact subderivatives under a full-rank map. -/
theorem subderivative_comp_eq_of_surjective (hG : ContDiff ℝ 1 G)
    (hx : g (G x) = c) (hs : Function.Surjective (fderiv ℝ G x)) (w : E) :
    subderivative (g ∘ G) x w = subderivative g (G x) (fderiv ℝ G x w) := by
  have hd : HasFDerivAt G (fderiv ℝ G x) x := (hG.differentiable (by norm_num) x).hasFDerivAt
  have hde := (hasFDerivAt_epigraphChainMap hd c).fderiv
  have ht := (contDiff_epigraphChainMap hG).contDiffAt (x := WithLp.toLp 2 (x,c)) |>.hasStrictFDerivAt (by norm_num : (1:WithTop ℕ∞) ≠ 0)
  rw [hde] at ht
  apply le_antisymm ?_ (subderivative_comp_ge hd hx w)
  by_contra! h
  obtain ⟨a,ha,hb⟩ := EReal.exists_between_coe_real h
  have hh := (mem_tangentCone_euclideanEpigraph_iff hx).mpr ha.le
  have hh' : WithLp.toLp 2 (w,a) ∈ tangentCone (euclideanEpigraph (g ∘ G)) (WithLp.toLp 2 (x,c)) := by
    rw [euclideanEpigraph_comp,tangentCone_preimage_of_surjective ht (epigraphChainDerivative_surjective hs)]
    exact hh
  exact hb.not_ge ((mem_tangentCone_euclideanEpigraph_iff (f := g ∘ G) (y := x) hx).mp hh')

/-- **Exercise 10.7**, exact regular subderivatives under a full-rank map. -/
theorem regularSubderivative_comp_eq_of_surjective (hG : ContDiff ℝ 1 G)
    (hl : LowerSemicontinuous g) (hx : g (G x) = c) (hs : Function.Surjective (fderiv ℝ G x))
    (w : E) :
    regularSubderivative (g ∘ G) x w = regularSubderivative g (G x) (fderiv ℝ G x w) := by
  have hd : HasFDerivAt G (fderiv ℝ G x) x := (hG.differentiable (by norm_num) x).hasFDerivAt
  have hde := (hasFDerivAt_epigraphChainMap hd c).fderiv
  have ht := (contDiff_epigraphChainMap hG).contDiffAt (x := WithLp.toLp 2 (x,c)) |>.hasStrictFDerivAt (by norm_num : (1:WithTop ℕ∞) ≠ 0)
  rw [hde] at ht
  have he (a : ℝ) : regularSubderivative (g ∘ G) x w ≤ (a:EReal) ↔
      regularSubderivative g (G x) (fderiv ℝ G x w) ≤ (a:EReal) := by
    rw [← mem_regularTangentCone_euclideanEpigraph_iff (f := g ∘ G) (y := x) hx ((hl.comp hG.continuous) x),
      euclideanEpigraph_comp,regularTangentCone_preimage_of_surjective ht
        (epigraphChainDerivative_surjective hs) (euclideanEpigraph g) hx.le]
    exact mem_regularTangentCone_euclideanEpigraph_iff hx (hl (G x))
  apply le_antisymm
  · by_contra! h
    obtain ⟨a,ha,hb⟩ := EReal.exists_between_coe_real h
    exact hb.not_ge ((he a).mpr ha.le)
  · by_contra! h
    obtain ⟨a,ha,hb⟩ := EReal.exists_between_coe_real h
    exact hb.not_ge ((he a).mp ha.le)

/-- **Exercise 10.7**, equivalence of subdifferential regularity. -/
theorem isSubdifferentiallyRegularAt_comp_iff_of_surjective (hG : ContDiff ℝ 1 G)
    (hl : LowerSemicontinuous g) (hx : g (G x) = c) (hs : Function.Surjective (fderiv ℝ G x)) :
    IsSubdifferentiallyRegularAt (g ∘ G) x ↔ IsSubdifferentiallyRegularAt g (G x) := by
  constructor
  · intro h
    apply isSubdifferentiallyRegularAt_iff_subderivative_eq_regularSubderivative.mpr
    refine ⟨locallyLscAt_of_lowerSemicontinuous_finite hl hx,?_⟩
    ext v
    obtain ⟨w,rfl⟩ := hs v
    rw [← subderivative_comp_eq_of_surjective hG hx hs w,
      ← regularSubderivative_comp_eq_of_surjective hG hl hx hs w,
      (isSubdifferentiallyRegularAt_iff_subderivative_eq_regularSubderivative.mp h).2]
  · intro h
    apply h.comp_of_horizon_qualification hG hl
    intro y _ hy
    exact adjoint_injective_of_surjective hs (by simpa using hy)

end RW
