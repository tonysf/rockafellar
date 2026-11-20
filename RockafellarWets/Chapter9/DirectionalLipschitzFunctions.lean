/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: Directionally Lipschitz functions

Exercise 9.42(b,c), using the actual epigraph representation established in
`EpiLipschitzSets`.
-/

import RockafellarWets.Chapter9.EpiLipschitzSets
import RockafellarWets.Chapter8.ClarkeSubgradientRepresentations
import RockafellarWets.Chapter8.InteriorRegularSubderivatives
import RockafellarWets.Chapter8.SubderivativeRegularityCriterion

open Filter Metric Set Topology
open scoped InnerProductSpace Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {f : E → EReal} {x : E} {c : ℝ}

/-- Directional Lipschitz continuity means that the epigraph is locally a
Lipschitz epigraph when viewed from some direction, possibly oblique to the
original vertical axis. The finite-value hypothesis is stated in the results. -/
def IsDirectionallyLipschitzAt (f : E → EReal) (x : E) : Prop :=
  IsEpiLipschitzAt (euclideanEpigraph f) (WithLp.toLp 2 (x,(f x).toReal))

private theorem epigraph_normal_pointed_iff (hx : f x = c) (hl : IsLocallyLscAt f x) :
    IsPointed (normalCone (euclideanEpigraph f) (WithLp.toLp 2 (x,c))) ↔
      IsPointed (horizonSubdifferential f x) := by
  refine ⟨?_,isPointed_normalCone_epigraph hx hl⟩
  intro h n v hv hs i
  let J : E →L[ℝ] WithLp 2 (E × ℝ) :=
    (l2ProdEquiv E).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hJ (y : E) : J y = WithLp.toLp 2 (y,(0:ℝ)) := rfl
  have hmem (j : Fin n) : J (v j) ∈ normalCone (euclideanEpigraph f) (WithLp.toLp 2 (x,c)) :=
    (mem_horizonSubdifferential_iff_epigraph_normal_of_locallyLsc hl hx).mp (hv j)
  have hsum : ∑ j, J (v j) = 0 := by rw [← map_sum,hs,map_zero]
  have hz := congrArg WithLp.fst (h n (fun j ↦ J (v j)) hmem hsum i)
  simpa only [hJ,WithLp.toLp_fst] using hz

omit [FiniteDimensional ℝ E] in
private theorem locallyClosed_epigraph_iff (hx : f x = c) :
    IsLocallyClosedAt (euclideanEpigraph f) (WithLp.toLp 2 (x,c)) ↔ IsLocallyLscAt f x := by
  constructor
  · intro h
    have hh := IsLocallyClosedAt.preimage_continuousLinearEquiv (l2ProdEquiv E).symm h
    apply isLocallyLscAt_of_isLocallyClosedAt_epigraph hx
    convert hh using 1
  · intro h
    have hh : IsLocallyClosedAt (epigraph f) (x,c) := by simpa [hx] using h.isLocallyClosedAt_epigraph
    exact hh.preimage_continuousLinearEquiv (l2ProdEquiv E)

/-- **Exercise 9.42(b)**, the horizon-subgradient criterion. -/
theorem isDirectionallyLipschitzAt_iff_locallyLsc_pointed (hx : f x = c) :
    IsDirectionallyLipschitzAt f x ↔
      IsLocallyLscAt f x ∧ IsPointed (horizonSubdifferential f x) := by
  unfold IsDirectionallyLipschitzAt
  rw [hx,EReal.toReal_coe,isEpiLipschitzAt_iff_locallyClosed_pointed (show
    WithLp.toLp 2 (x,c) ∈ euclideanEpigraph f from hx.le),locallyClosed_epigraph_iff hx]
  exact and_congr_right (fun hl ↦ epigraph_normal_pointed_iff hx hl)

private theorem interior_epigraph_tangent_nonempty_iff (hx : f x = c) (hl : IsLocallyLscAt f x) :
    (interior (regularTangentCone (euclideanEpigraph f) (WithLp.toLp 2 (x,c)))).Nonempty ↔
      (interior (effectiveDomain (regularSubderivative f x))).Nonempty := by
  let L := l2ProdEquiv E
  have hp : L (WithLp.toLp 2 (x,c)) ∈ epigraph f := hx.le
  have hT : regularTangentCone (euclideanEpigraph f) (WithLp.toLp 2 (x,c)) =
      L ⁻¹' epigraph (regularSubderivative f x) := by
    rw [epigraph_regularSubderivative_eq_regularTangentCone hx hl.lowerSemicontinuousAt]
    exact regularTangentCone_preimage_continuousLinearEquiv L hp
  rw [hT]
  have hI : L ⁻¹' interior (epigraph (regularSubderivative f x)) =
      interior (L ⁻¹' epigraph (regularSubderivative f x)) := L.toHomeomorph.preimage_interior _
  rw [← hI]
  have hc := convex_epigraph_regularSubderivative hx hl.lowerSemicontinuousAt
  constructor
  · rintro ⟨w,hw⟩
    exact ⟨(L w).1,((mem_interior_epigraph_iff_of_convex hc).mp hw).1⟩
  · rintro ⟨w,hw⟩
    obtain ⟨a,ha,-⟩ := EReal.exists_between_coe_real
      (show regularSubderivative f x w < ⊤ from interior_subset (s := effectiveDomain (regularSubderivative f x)) hw)
    refine ⟨L.symm (w,a),?_⟩
    change L (L.symm (w,a)) ∈ interior (epigraph (regularSubderivative f x))
    rw [L.apply_symm_apply]
    exact (mem_interior_epigraph_iff_of_convex hc).mpr ⟨hw,ha⟩

/-- **Exercise 9.42(b)**, the interior regular-subderivative-domain criterion. -/
theorem isDirectionallyLipschitzAt_iff_interior_domain (hx : f x = c)
    (hl : IsLocallyLscAt f x) :
    IsDirectionallyLipschitzAt f x ↔
      (interior (effectiveDomain (regularSubderivative f x))).Nonempty := by
  rw [isDirectionallyLipschitzAt_iff_locallyLsc_pointed hx,and_iff_right hl,
    ← epigraph_normal_pointed_iff hx hl,
    isPointed_normalCone_iff_interior_regularTangentCone_nonempty
      (show WithLp.toLp 2 (x,c) ∈ euclideanEpigraph f from hx.le)
      ((locallyClosed_epigraph_iff hx).mpr hl),interior_epigraph_tangent_nonempty_iff hx hl]

/-- **Exercise 9.42(b)**, the finite upper-slope criterion. -/
theorem isDirectionallyLipschitzAt_iff_exists_upperSlope (hx : f x = c)
    (hl : IsLocallyLscAt f x) :
    IsDirectionallyLipschitzAt f x ↔ ∃ w, upperDirectionalSlope f x w < ⊤ := by
  rw [isDirectionallyLipschitzAt_iff_interior_domain hx hl,
    interior_effectiveDomain_regularSubderivative hx hl]
  rfl

/-- In positive dimension the direction in the upper-slope criterion can be
chosen nonzero, as in the directional limit in Exercise 9.42(b). -/
theorem isDirectionallyLipschitzAt_iff_exists_nonzero_upperSlope [Nontrivial E]
    (hx : f x = c) (hl : IsLocallyLscAt f x) :
    IsDirectionallyLipschitzAt f x ↔ ∃ w ≠ 0, upperDirectionalSlope f x w < ⊤ := by
  constructor
  · intro h
    obtain ⟨w,hw⟩ := (isDirectionallyLipschitzAt_iff_interior_domain hx hl).mp h
    have hinf := infinite_of_mem_nhds w (isOpen_interior.mem_nhds hw)
    obtain ⟨v,hv,hv0⟩ := (hinf.diff (finite_singleton (0:E))).nonempty
    refine ⟨v,by simpa using hv0,?_⟩
    rw [interior_effectiveDomain_regularSubderivative hx hl] at hv
    exact hv
  · rintro ⟨w,-,hw⟩
    exact (isDirectionallyLipschitzAt_iff_exists_upperSlope hx hl).mpr ⟨w,hw⟩

/-- **Exercise 9.42(c)**. Decrease along a cone with nonempty interior supplies
an open family of epigraph recession directions. No global lower
semicontinuity or properness assumption is needed. -/
theorem isDirectionallyLipschitzAt_of_nonincreasing_cone (hx : f x = c)
    (hl : IsLocallyLscAt f x) {K : Set E} (hK : IsCone K)
    (hi : (interior K).Nonempty) (hf : ∀ y, ∀ w ∈ K, f (y+w) ≤ f y) :
    IsDirectionallyLipschitzAt f x := by
  obtain ⟨w,hw⟩ := hi
  let L := l2ProdEquiv E
  let p := WithLp.toLp 2 (x,c)
  let d := WithLp.toLp 2 (w,(1:ℝ))
  have hp : p ∈ euclideanEpigraph f := hx.le
  have hc := (locallyClosed_epigraph_iff hx).mpr hl
  have htan : d ∈ interior (regularTangentCone (euclideanEpigraph f) p) := by
    apply (mem_interior_regularTangentCone_iff_uniform_recession hp hc).mpr
    let W := L ⁻¹' (interior K ×ˢ Ioi (0:ℝ))
    have hW : W ∈ nhds d := (L.continuous.tendsto d).eventually
      ((isOpen_interior.prod isOpen_Ioi).mem_nhds (show L d ∈ interior K ×ˢ Ioi (0:ℝ) from ⟨hw,by change (0:ℝ) < 1; norm_num⟩))
    refine ⟨W,hW,univ,univ_mem,1,one_pos,?_⟩
    intro q hq t ht z hz
    have hmono := hf q.fst (t • z.fst) (hK.smul_mem (interior_subset hz.1) ht.1)
    have hbase : f q.fst ≤ (q.snd:EReal) := hq.1
    change f (q.fst+t • z.fst) ≤ ((q.snd+t*z.snd:ℝ):EReal)
    exact hmono.trans (hbase.trans (EReal.coe_le_coe_iff.mpr
      (le_add_of_nonneg_right (mul_nonneg ht.1 hz.2.le))))
  apply (isDirectionallyLipschitzAt_iff_interior_domain hx hl).mpr
  exact (interior_epigraph_tangent_nonempty_iff hx hl).mp ⟨d,htan⟩

end RW
