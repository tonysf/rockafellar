/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 10: Subderivatives in the basic chain rule
-/

import RockafellarWets.Chapter10.BasicChainRule
import RockafellarWets.Chapter8.ClarkeSubgradients

open Set
open scoped InnerProductSpace

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  {G : E → F} {g : F → EReal} {x : E} {c : ℝ}

theorem mem_tangentCone_euclideanEpigraph_iff {f : E → EReal} {y w : E} {a b : ℝ}
    (hy : f y = a) :
    WithLp.toLp 2 (w,b) ∈ tangentCone (euclideanEpigraph f) (WithLp.toLp 2 (y,a)) ↔
      subderivative f y w ≤ (b:EReal) := by
  change WithLp.toLp 2 (w,b) ∈ tangentCone ((l2ProdEquiv E) ⁻¹' epigraph f) _ ↔ _
  rw [tangentCone_preimage_continuousLinearEquiv,mem_preimage,l2ProdEquiv_toLp,
    ← epigraph_subderivative_eq_tangentCone hy]
  rfl

theorem mem_regularTangentCone_euclideanEpigraph_iff {f : E → EReal} {y w : E} {a b : ℝ}
    (hy : f y = a) (hl : LowerSemicontinuousAt f y) :
    WithLp.toLp 2 (w,b) ∈ regularTangentCone (euclideanEpigraph f) (WithLp.toLp 2 (y,a)) ↔
      regularSubderivative f y w ≤ (b:EReal) := by
  change WithLp.toLp 2 (w,b) ∈ regularTangentCone ((l2ProdEquiv E) ⁻¹' epigraph f) _ ↔ _
  rw [regularTangentCone_preimage_continuousLinearEquiv (l2ProdEquiv E) hy.le,
    mem_preimage,l2ProdEquiv_toLp,← epigraph_regularSubderivative_eq_regularTangentCone hy hl]
  rfl

/-- **Theorem 10.6**, the unconditional subderivative inequality. -/
theorem subderivative_comp_ge {A : E →L[ℝ] F} (hG : HasFDerivAt G A x)
    (hx : g (G x) = c) (w : E) :
    subderivative g (G x) (A w) ≤ subderivative (g ∘ G) x w := by
  by_contra! h
  obtain ⟨a,ha,hb⟩ := EReal.exists_between_coe_real h
  have ht := (mem_tangentCone_euclideanEpigraph_iff (f := g ∘ G) (y := x) hx).mpr ha.le
  have hh := image_tangentCone_subset (hasFDerivAt_epigraphChainMap hG c)
    (euclideanEpigraph (g ∘ G)) ⟨WithLp.toLp 2 (w,a),ht,rfl⟩
  have hh' := tangentCone_mono (show epigraphChainMap G '' euclideanEpigraph (g ∘ G) ⊆ euclideanEpigraph g from
    fun _ ⟨q,hq,he⟩ ↦ he ▸ hq) (WithLp.toLp 2 (G x,c)) hh
  exact hb.not_ge ((mem_tangentCone_euclideanEpigraph_iff hx).mp hh')

/-- **Theorem 10.6**, the regular-subderivative inequality under the
horizon qualification. -/
theorem regularSubderivative_comp_le (hG : ContDiff ℝ 1 G) (hl : LowerSemicontinuous g)
    (hx : g (G x) = c)
    (hQ : ∀ y ∈ horizonSubdifferential g (G x), (fderiv ℝ G x).adjoint y = 0 → y = 0)
    (w : E) :
    regularSubderivative (g ∘ G) x w ≤ regularSubderivative g (G x) (fderiv ℝ G x w) := by
  by_contra! h
  obtain ⟨a,ha,hb⟩ := EReal.exists_between_coe_real h
  have hD : IsClosed (euclideanEpigraph g) :=
    (isClosed_epigraph_of_lsc_ereal g hl).preimage (l2ProdEquiv F).continuous
  have hd : HasFDerivAt G (fderiv ℝ G x) x := (hG.differentiable (by norm_num) x).hasFDerivAt
  have hde := (hasFDerivAt_epigraphChainMap hd c).fderiv
  have ht := (mem_regularTangentCone_euclideanEpigraph_iff hx (hl (G x))).mpr ha.le
  have hh := regularTangentCone_constraints_superset isClosed_univ hD (contDiff_epigraphChainMap hG)
    (show WithLp.toLp 2 (x,c) ∈ univ ∩ epigraphChainMap G ⁻¹' euclideanEpigraph g from ⟨mem_univ _,hx.le⟩)
    (epigraphChain_constraintQualification hG hl hx hQ)
    (show WithLp.toLp 2 (w,a) ∈ regularTangentCone univ (WithLp.toLp 2 (x,c)) ∩
      (fderiv ℝ (epigraphChainMap G) (WithLp.toLp 2 (x,c))) ⁻¹'
        regularTangentCone (euclideanEpigraph g) (WithLp.toLp 2 (G x,c)) from
      ⟨by rw [← tangentCone_eq_regularTangentCone_of_isClarkeRegularAt (mem_univ _) (isClarkeRegularAt_univ _),tangentCone_univ]; trivial,by simpa only [hde,epigraphChainDerivative_apply] using ht⟩)
  have hh' : WithLp.toLp 2 (w,a) ∈ regularTangentCone (euclideanEpigraph (g ∘ G)) (WithLp.toLp 2 (x,c)) := by
    simpa only [univ_inter,← euclideanEpigraph_comp] using hh
  exact hb.not_ge ((mem_regularTangentCone_euclideanEpigraph_iff (f := g ∘ G) (y := x)
    hx ((hl.comp hG.continuous) x)).mp hh')

/-- **Theorem 10.6**, exact subderivatives when the outer function is regular. -/
theorem subderivative_comp_eq_of_regular (hG : ContDiff ℝ 1 G) (hl : LowerSemicontinuous g)
    (hr : IsSubdifferentiallyRegularAt g (G x))
    (hQ : ∀ y ∈ horizonSubdifferential g (G x), (fderiv ℝ G x).adjoint y = 0 → y = 0)
    (w : E) :
    subderivative (g ∘ G) x w = subderivative g (G x) (fderiv ℝ G x w) := by
  have hx := (EReal.coe_toReal hr.2.1 hr.1).symm
  have hd := (hG.differentiable (by norm_num) x).hasFDerivAt
  apply le_antisymm ?_ (subderivative_comp_ge hd hx w)
  have he := (isSubdifferentiallyRegularAt_iff_subderivative_eq_regularSubderivative.mp hr).2
  exact (subderivative_le_regularSubderivative (f := g ∘ G) (x := x) hx w).trans
    (by simpa only [← he] using regularSubderivative_comp_le hG hl hx hQ w)

end RW
