/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: The support-function correspondence
-/

import RockafellarWets.Chapter8.SupportPolarity
import RockafellarWets.Chapter8.ConvexEnvelopes
import RockafellarWets.Chapter3.ConvexHullFunctions
import RockafellarWets.Chapter3.HomogeneousCompletion
import RockafellarWets.Chapter7.EpiLimitProperties

open Filter Set Topology
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Linear minorants are exactly the homogeneous affine inequalities obeyed
by every point of the real epigraph. -/
theorem mem_linearMinorantSet_iff_epigraph (f : E → EReal) (v : E) :
    v ∈ linearMinorantSet f ↔ ∀ p ∈ epigraph f, ⟪v,p.1⟫_ℝ ≤ p.2 := by
  refine ⟨fun h p hp ↦ EReal.coe_le_coe_iff.1 ((h p.1).trans hp), fun h w ↦ ?_⟩
  by_contra! hn
  obtain ⟨a,ha,haz⟩ := EReal.exists_between_coe_real hn
  exact (EReal.coe_lt_coe_iff.1 haz).not_ge (h (w,a) ha.le)

omit [InnerProductSpace ℝ E] in
/-- The closed convex hull of a function has the closed convex hull of its
epigraph as its real epigraph. -/
theorem epigraph_epiClosure_convexHullFunction [NormedSpace ℝ E] (f : E → EReal) :
    epigraph (epiClosure (convexHullFunction f)) = closure (convexHull ℝ (epigraph f)) := by
  rw [epigraph_epiClosure]
  refine Subset.antisymm (closure_minimal ?_ isClosed_closure)
    (closure_mono (convexHull_epigraph_subset_epigraph_convexHullFunction f))
  rintro ⟨x,a⟩ ha
  let S := convexHull ℝ (epigraph f)
  have hsub : Ioi a ⊆ (Prod.mk x) ⁻¹' closure S := by
    intro b hb
    have hh := (show convexHullFunction f x ≤ (a : EReal) from ha).trans_lt (EReal.coe_lt_coe_iff.2 hb)
    obtain ⟨c,hc⟩ := iInf_lt_iff.1 hh
    have hcb := EReal.coe_lt_coe_iff.1 hc
    have hm := add_nonnegative_vertical_mem_convexHull_epigraph (f := f) (p := (x,(c : ℝ)))
      (d := b-c) c.2 (sub_nonneg.2 hcb.le)
    exact subset_closure (by simpa [S] using hm)
  have hcl := closure_minimal hsub (isClosed_closure.preimage (continuous_const.prodMk continuous_id))
  exact hcl (show a ∈ closure (Ioi a) by simp [closure_Ioi])

theorem linearMinorantSet_epiClosure_convexHullFunction (f : E → EReal) :
    linearMinorantSet (epiClosure (convexHullFunction f)) = linearMinorantSet f := by
  ext v
  rw [mem_linearMinorantSet_iff_epigraph, mem_linearMinorantSet_iff_epigraph, epigraph_epiClosure_convexHullFunction]
  refine ⟨fun h p hp ↦ h p (subset_closure (subset_convexHull _ _ hp)), fun h ↦ ?_⟩
  let l : E × ℝ →L[ℝ] ℝ := (innerSL ℝ v).comp (ContinuousLinearMap.fst ℝ E ℝ) - ContinuousLinearMap.snd ℝ E ℝ
  have hsub : epigraph f ⊆ {p : E × ℝ | l p ≤ 0} := fun p hp ↦ sub_nonpos.2 (h p hp)
  have hc := closure_minimal (convexHull_min hsub (convex_halfSpace_le l.toLinearMap.isLinear _))
    (isClosed_le l.continuous continuous_const)
  exact fun p hp ↦ sub_nonpos.1 (show l p ≤ 0 from hc hp)

variable [FiniteDimensional ℝ E]

/-- Proper lower semicontinuous sublinear functions are the support functions
of their linear minorant sets. -/
theorem supportFunction_linearMinorantSet {h : E → EReal} (hs : Sublinear h)
    (hl : LowerSemicontinuous h) (hp : IsProper h) : supportFunction (linearMinorantSet h) = h := by
  letI := FiniteDimensional.complete ℝ E
  funext w
  refine le_antisymm ((supportFunction_le_iff _ _ _).2 fun v hv ↦ hv w) ?_
  rw [eq_iSup_linearMinorants hs hl hp w]
  apply iSup_le
  rintro ⟨l,hl⟩
  let v := (InnerProductSpace.toDual ℝ E).symm l
  have hv : v ∈ linearMinorantSet h := fun z ↦ by simpa [v] using hl z
  simpa [v] using inner_le_supportFunction hv w

omit [FiniteDimensional ℝ E] in
/-- A closed convex conic epigraph containing a finite function value has no downward vertical line. -/
theorem has_no_bot_of_closed_convex_cone_epigraph_of_finite {g : E → EReal}
    (hcl : IsClosed (epigraph g)) (hconv : Convex ℝ (epigraph g)) (hc : IsCone (epigraph g))
    {x : E} {b : ℝ} (hx : g x = (b : EReal)) : ∀ y, ⊥ < g y := by
  intro y
  by_contra! hbot
  have hy := le_bot_iff.1 hbot
  have hvert : ((0,-1) : E × ℝ) ∈ epigraph g := by
    have hlim : Tendsto (fun t : ℝ ↦ (t • y,(-1 : ℝ))) (𝓝[>] 0) (𝓝 ((0:E),-1)) := by
      have ht : Continuous (fun t : ℝ ↦ (t • y,(-1 : ℝ))) := by fun_prop
      simpa using (ht.tendsto 0).mono_left nhdsWithin_le_nhds
    apply hcl.mem_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hp : (y,-1/t) ∈ epigraph g := by simp [mem_epigraph_iff,hy]
    have h := hc.2 hp (show 0 < t from ht)
    have ht' : t ≠ 0 := (show 0 < t from ht).ne'
    simpa [Prod.smul_mk, smul_eq_mul, show t*(-1/t) = -1 by field_simp] using h
  have hxb : (x,b) ∈ epigraph g := hx.le
  have hb := add_mem_of_convex_isCone hconv hc hxb hvert
  change g (x+0) ≤ ((b + -1 : ℝ) : EReal) at hb
  rw [add_zero, hx, EReal.coe_le_coe_iff] at hb
  linarith

/-- **Theorem 8.24**, closed convexification of an arbitrary positively
homogeneous function, including the case without any linear minorants. -/
theorem supportFunction_closed_convexHull_of_positivelyHomogeneous {h : E → EReal}
    (hh : PositivelyHomogeneous h) :
    let g := epiClosure (convexHullFunction h)
    ((linearMinorantSet h).Nonempty → supportFunction (linearMinorantSet h) = g) ∧
      (linearMinorantSet h = ∅ → ¬IsProper g ∧ ∀ x (b : ℝ), g x ≠ (b : EReal)) := by
  let g := epiClosure (convexHullFunction h)
  have he : epigraph g = closure (convexHull ℝ (epigraph h)) := epigraph_epiClosure_convexHullFunction h
  have hcl : IsClosed (epigraph g) := he ▸ isClosed_closure
  have hc : Convex ℝ (epigraph g) := he ▸ (convex_convexHull ℝ _).closure
  have hk : IsCone (epigraph g) := he ▸ (isCone_convexHull (isCone_epigraph_of_positivelyHomogeneous hh)).closure
  have heq := linearMinorantSet_epiClosure_convexHullFunction h
  have hrepr (hp : IsProper g) : supportFunction (linearMinorantSet h) = g := by
    rw [← heq]
    exact supportFunction_linearMinorantSet ((sublinear_iff_convex_isCone_epigraph_of_isProper hp).2 ⟨hc,hk⟩)
      (lowerSemicontinuous_of_isClosed_epigraph_ereal g hcl) hp
  have h0 : g 0 ≤ (0 : EReal) := hk.1
  have hdom : (effectiveDomain g).Nonempty := ⟨0, h0.trans_lt (EReal.coe_lt_top _)⟩
  constructor
  · rintro ⟨v,hv⟩
    have hminor : v ∈ linearMinorantSet g := heq.symm ▸ hv
    exact hrepr ⟨hdom,fun w ↦ (EReal.bot_lt_coe _).trans_le (hminor w)⟩
  · intro hemp
    have himp : ¬IsProper g := by
      intro hp
      have hbot := congrFun (hrepr hp) 0
      rw [hemp,supportFunction_empty] at hbot
      exact (hp.2 0).ne hbot
    exact ⟨himp,fun x b hx ↦ himp ⟨hdom,has_no_bot_of_closed_convex_cone_epigraph_of_finite hcl hc hk hx⟩⟩

/-- The one-to-one correspondence in Theorem 8.24. -/
noncomputable def closedConvexSetEquivSublinear :
    {D : Set E // D.Nonempty ∧ IsClosed D ∧ Convex ℝ D} ≃
      {h : E → EReal // IsProper h ∧ LowerSemicontinuous h ∧ Sublinear h} where
  toFun D := ⟨supportFunction D.val, isProper_supportFunction D.2.1, lowerSemicontinuous_supportFunction D.val,
    sublinear_supportFunction D.val⟩
  invFun f := ⟨linearMinorantSet f, by
    by_contra! he
    have hz := congrFun (supportFunction_linearMinorantSet f.2.2.2 f.2.2.1 f.2.1) 0
    rw [he, supportFunction_empty] at hz
    exact (f.2.1.2 0).ne hz, isClosed_linearMinorantSet _, convex_linearMinorantSet _⟩
  left_inv D := Subtype.ext (by change linearMinorantSet (supportFunction D.val) = D.val; rw [linearMinorantSet_supportFunction, D.2.2.2.convexHull_eq, D.2.2.1.closure_eq])
  right_inv f := Subtype.ext (supportFunction_linearMinorantSet f.2.2.2 f.2.2.1 f.2.1)

end RW
