/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Exact PLQ calculus without constraint qualifications
-/
import RockafellarWets.Chapter10.PLQSubgradients

open Set Filter Topology Classical
open scoped InnerProductSpace Pointwise

namespace RW
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Support functions turn Minkowski addition into extended-real addition. -/
theorem supportFunction_add (C D : Set E) (w : E) :
    supportFunction (C+D) w = supportFunction C w + supportFunction D w := by
  apply le_antisymm
  · apply (supportFunction_le_iff _ _ _).mpr
    rintro _ ⟨v,hv,z,hz,rfl⟩
    rw [inner_add_left,EReal.coe_add]
    exact add_le_add (inner_le_supportFunction hv w) (inner_le_supportFunction hz w)
  · apply EReal.add_le_of_forall_lt
    intro a ha b hb
    obtain ⟨v,hv⟩ := lt_iSup_iff.mp ha
    obtain ⟨z,hz⟩ := lt_iSup_iff.mp hb
    exact (add_le_add hv.le hz.le).trans (by
      simpa only [← EReal.coe_add,← inner_add_left] using
        inner_le_supportFunction (show (v:E)+(z:E) ∈ C+D from ⟨v,v.property,z,z.property,rfl⟩) w)

/-- Linear images act on support functions by the adjoint. -/
theorem supportFunction_adjoint_image (A : E →L[ℝ] F) (C : Set F) (w : E) :
    supportFunction (A.adjoint '' C) w = supportFunction C (A w) := by
  apply le_antisymm
  · apply (supportFunction_le_iff _ _ _).mpr
    rintro _ ⟨v,hv,rfl⟩
    simpa only [ContinuousLinearMap.adjoint_inner_left] using inner_le_supportFunction hv (A w)
  · apply (supportFunction_le_iff _ _ _).mpr
    intro v hv
    simpa only [ContinuousLinearMap.adjoint_inner_left] using
      inner_le_supportFunction (mem_image_of_mem A.adjoint hv) w

/-- **Exercise 10.22(b)**, exact affine subderivatives without qualification. -/
theorem IsPiecewiseLinearQuadratic.subderivative_compAffine {g : F → EReal}
    (hg : IsPiecewiseLinearQuadratic g) (A : E →L[ℝ] F) (a : F)
    {x : E} (hx : A x+a ∈ effectiveDomain g) (w : E) :
    subderivative (fun y ↦ g (A y+a)) x w = subderivative g (A x+a) (A w) := by
  have he (t : ℝ) : differenceQuotient (fun y ↦ g (A y+a)) x t w =
      differenceQuotient g (A x+a) t (A w) := by
    simp only [differenceQuotient,map_add,map_smul]
    rw [add_right_comm (A x) (t • A w) a]
  exact tendsto_nhds_unique ((hg.compAffine A a).hasOneSidedDirDeriv hx w).2.2
    (by simpa only [he] using (hg.hasOneSidedDirDeriv hx (A w)).2.2)

/-- Difference quotients distribute over addition when neither function
has a negative infinite value and both base values are finite. -/
theorem differenceQuotient_add_of_ne_bot {f g : E → EReal} (hf : ∀y, f y ≠ ⊥)
    (hg : ∀y, g y ≠ ⊥) {x : E} {c d : ℝ} (hx : f x = c) (hy : g x = d)
    {t : ℝ} (ht : 0 < t) (w : E) :
    differenceQuotient (fun y ↦ f y+g y) x t w =
      differenceQuotient f x t w + differenceQuotient g x t w := by
  unfold differenceQuotient
  dsimp only
  rw [hx,hy]
  generalize hfv : f (x+t • w) = u
  generalize hgv : g (x+t • w) = v
  have hub : u ≠ ⊥ := hfv ▸ hf _
  have hvb : v ≠ ⊥ := hgv ▸ hg _
  cases u using EReal.rec <;> cases v using EReal.rec
  all_goals first | contradiction | skip
  all_goals simp only [← EReal.coe_add,← EReal.coe_sub,← EReal.coe_mul,
    EReal.top_add_coe,EReal.coe_add_top,EReal.top_add_top,EReal.top_sub_coe,
    EReal.coe_mul_top_of_pos (inv_pos.mpr ht)]
  congr 1
  ring

/-- **Exercise 10.22(a)**, exact binary addition of subderivatives. -/
theorem IsPiecewiseLinearQuadratic.subderivative_add {f g : E → EReal}
    (hf : IsPiecewiseLinearQuadratic f) (hg : IsPiecewiseLinearQuadratic g)
    {x : E} (hx : x ∈ effectiveDomain f) (hy : x ∈ effectiveDomain g) (w : E) :
    subderivative (fun y ↦ f y+g y) x w = subderivative f x w + subderivative g x w := by
  have hfx := (EReal.coe_toReal (ne_of_lt hx) (hf.ne_bot x)).symm
  have hgx := (EReal.coe_toReal (ne_of_lt hy) (hg.ne_bot x)).symm
  have hsum : x ∈ effectiveDomain (fun y ↦ f y+g y) := by
    change f x+g x < ⊤
    rw [hfx,hgx,← EReal.coe_add]
    exact EReal.coe_lt_top _
  have hb := (hf.subderivative_piecewiseLinear hx).1.isPiecewiseLinearQuadratic.ne_bot w
  have hc := (hg.subderivative_piecewiseLinear hy).1.isPiecewiseLinearQuadratic.ne_bot w
  apply tendsto_nhds_unique ((hf.add hg).hasOneSidedDirDeriv hsum w).2.2
  have ht := (EReal.continuousAt_add (Or.inr hc) (Or.inl hb)).tendsto.comp
    (((hf.hasOneSidedDirDeriv hx w).2.2).prodMk_nhds ((hg.hasOneSidedDirDeriv hy w).2.2))
  apply ht.congr'
  filter_upwards [(self_mem_nhdsWithin : Ioi (0:ℝ) ∈ 𝓝[>] 0)] with t ht
  exact (differenceQuotient_add_of_ne_bot hf.ne_bot hg.ne_bot hfx hgx ht w).symm

/-- Affine precomposition preserves convexity of the epigraph. -/
theorem convex_epigraph_compAffine {g : F → EReal} (hg : Convex ℝ (epigraph g))
    (A : E →L[ℝ] F) (a : F) : Convex ℝ (epigraph (fun x ↦ g (A x+a))) := by
  intro p hp q hq s t hs ht hst
  have hh := hg (show (A p.1+a,p.2) ∈ epigraph g from hp)
    (show (A q.1+a,q.2) ∈ epigraph g from hq) hs ht hst
  change g (A (s • p.1+t • q.1)+a) ≤ ((s*p.2+t*q.2 : ℝ):EReal)
  change g (s • (A p.1+a)+t • (A q.1+a)) ≤ ((s*p.2+t*q.2 : ℝ):EReal) at hh
  have he : s • (A p.1+a)+t • (A q.1+a) = A (s • p.1+t • q.1)+a := by
    rw [smul_add,smul_add,add_add_add_comm,← add_smul,hst,one_smul,map_add,map_smul,map_smul]
  rwa [he] at hh

/-- Addition preserves convex epigraphs for functions without `-∞`. -/
theorem convex_epigraph_add_of_ne_bot {f g : E → EReal}
    (hf : Convex ℝ (epigraph f)) (hg : Convex ℝ (epigraph g))
    (hfb : ∀y, f y ≠ ⊥) (hgb : ∀y, g y ≠ ⊥) :
    Convex ℝ (epigraph (fun x ↦ f x+g x)) := by
  have hfinite {y : E} {a : ℝ} (hy : f y+g y ≤ (a:EReal)) :
      f y = ((f y).toReal:EReal) ∧ g y = ((g y).toReal:EReal) := by
    have hft : f y ≠ ⊤ := by
      intro he
      rw [he,EReal.top_add_of_ne_bot (hgb y)] at hy
      exact (EReal.coe_lt_top a).not_ge hy
    have hgt : g y ≠ ⊤ := by
      intro he
      rw [he,EReal.add_top_of_ne_bot (hfb y)] at hy
      exact (EReal.coe_lt_top a).not_ge hy
    exact ⟨(EReal.coe_toReal hft (hfb y)).symm,(EReal.coe_toReal hgt (hgb y)).symm⟩
  intro p hp q hq a b ha hb hab
  obtain ⟨hfp,hgp⟩ := hfinite hp
  obtain ⟨hfq,hgq⟩ := hfinite hq
  have hf' := hf (show (p.1,(f p.1).toReal) ∈ epigraph f from hfp.le)
    (show (q.1,(f q.1).toReal) ∈ epigraph f from hfq.le) ha hb hab
  have hg' := hg (show (p.1,(g p.1).toReal) ∈ epigraph g from hgp.le)
    (show (q.1,(g q.1).toReal) ∈ epigraph g from hgq.le) ha hb hab
  change f p.1+g p.1 ≤ (p.2:EReal) at hp
  change f q.1+g q.1 ≤ (q.2:EReal) at hq
  rw [hfp,hgp,← EReal.coe_add,EReal.coe_le_coe_iff] at hp
  rw [hfq,hgq,← EReal.coe_add,EReal.coe_le_coe_iff] at hq
  change f (a • p.1+b • q.1) ≤ ((a*(f p.1).toReal+b*(f q.1).toReal:ℝ):EReal) at hf'
  change g (a • p.1+b • q.1) ≤ ((a*(g p.1).toReal+b*(g q.1).toReal:ℝ):EReal) at hg'
  refine (add_le_add hf' hg').trans ?_
  change ((a*(f p.1).toReal+b*(f q.1).toReal:ℝ):EReal)+
      ((a*(g p.1).toReal+b*(g q.1).toReal:ℝ):EReal) ≤ ((a*p.2+b*q.2:ℝ):EReal)
  rw [← EReal.coe_add,EReal.coe_le_coe_iff]
  nlinarith [mul_le_mul_of_nonneg_left hp ha,mul_le_mul_of_nonneg_left hq hb]

/-- The support representation for convex PLQ functions. -/
theorem IsPiecewiseLinearQuadratic.subderivative_eq_support {f : E → EReal}
    (hf : IsPiecewiseLinearQuadratic f) (hc : Convex ℝ (epigraph f))
    {x : E} (hx : x ∈ effectiveDomain f) :
    subderivative f x = supportFunction (subdifferential f x) := by
  have hfin := (EReal.coe_toReal (ne_of_lt hx) (hf.ne_bot x)).symm
  have hl := isLocallyLscAt_of_isLocallyClosedAt_epigraph hfin
    (RW.IsClosed.isLocallyClosedAt (isClosed_epigraph_of_lsc_ereal f hf.lowerSemicontinuous) _)
  exact ((isSubdifferentiallyRegularAt_of_convex hc hl).1.subderivative_support_duality
    (hf.convex_subgradient_properties hc hx).1).2.2.1

/-- **Exercise 10.22(b)**: the convex affine subgradient formula needs no CQ. -/
theorem IsPiecewiseLinearQuadratic.subdifferential_compAffine {g : F → EReal}
    (hg : IsPiecewiseLinearQuadratic g) (hc : Convex ℝ (epigraph g))
    (A : E →L[ℝ] F) (a : F) {x : E} (hx : A x+a ∈ effectiveDomain g) :
    subdifferential (fun y ↦ g (A y+a)) x = A.adjoint '' subdifferential g (A x+a) := by
  have hf := hg.compAffine A a
  have hfc := convex_epigraph_compAffine hc A a
  have hpoly : IsPolyhedral (A.adjoint '' subdifferential g (A x+a)) :=
    ((hg.convex_subgradient_properties hc hx).2.1).linear_image A.adjoint.toLinearMap
  have he : supportFunction (subdifferential (fun y ↦ g (A y+a)) x) =
      supportFunction (A.adjoint '' subdifferential g (A x+a)) := by
    ext w
    rw [← hf.subderivative_eq_support hfc hx,hg.subderivative_compAffine A a hx,
      supportFunction_adjoint_image,← hg.subderivative_eq_support hc hx]
  have hh := congrArg linearMinorantSet he
  rw [linearMinorantSet_supportFunction,linearMinorantSet_supportFunction,
    (hf.convex_subgradient_properties hfc hx).2.1.convex.convexHull_eq,
    (hf.convex_subgradient_properties hfc hx).2.1.isClosed.closure_eq,
    hpoly.convex.convexHull_eq,hpoly.isClosed.closure_eq] at hh
  exact hh

/-- **Exercise 10.22(a)**: the convex sum formula needs no CQ. -/
theorem IsPiecewiseLinearQuadratic.subdifferential_add {f g : E → EReal}
    (hf : IsPiecewiseLinearQuadratic f) (hg : IsPiecewiseLinearQuadratic g)
    (hfc : Convex ℝ (epigraph f)) (hgc : Convex ℝ (epigraph g))
    {x : E} (hx : x ∈ effectiveDomain f) (hy : x ∈ effectiveDomain g) :
    subdifferential (fun y ↦ f y+g y) x = subdifferential f x+subdifferential g x := by
  have hsum := hf.add hg
  have hsc := convex_epigraph_add_of_ne_bot hfc hgc hf.ne_bot hg.ne_bot
  have hz : x ∈ effectiveDomain (fun y ↦ f y+g y) := by
    change f x+g x < ⊤
    rw [← EReal.coe_toReal (ne_of_lt hx) (hf.ne_bot x),
      ← EReal.coe_toReal (ne_of_lt hy) (hg.ne_bot x),← EReal.coe_add]
    exact EReal.coe_lt_top _
  have hpoly := ((hf.convex_subgradient_properties hfc hx).2.1).add
    (hg.convex_subgradient_properties hgc hy).2.1
  have he : supportFunction (subdifferential (fun y ↦ f y+g y) x) =
      supportFunction (subdifferential f x+subdifferential g x) := by
    ext w
    rw [← hsum.subderivative_eq_support hsc hz,hf.subderivative_add hg hx hy,
      supportFunction_add,← hf.subderivative_eq_support hfc hx,← hg.subderivative_eq_support hgc hy]
  have hh := congrArg linearMinorantSet he
  rw [linearMinorantSet_supportFunction,linearMinorantSet_supportFunction,
    (hsum.convex_subgradient_properties hsc hz).2.1.convex.convexHull_eq,
    (hsum.convex_subgradient_properties hsc hz).2.1.isClosed.closure_eq,
    hpoly.convex.convexHull_eq,hpoly.isClosed.closure_eq] at hh
  exact hh

end RW
