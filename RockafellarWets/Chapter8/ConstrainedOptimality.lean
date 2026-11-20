/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Optimality relative to a closed set
-/

import RockafellarWets.Chapter8.SubdifferentialRegularityCriterion
import RockafellarWets.Chapter8.ConvexSubgradients
import RockafellarWets.Chapter8.CalmSubgradients
import RockafellarWets.Chapter6.IntersectionCones

open Filter Set Topology
open scoped InnerProductSpace Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {C D : Set E} {f : E → EReal} {x : E} {c : ℝ}

/-- The two-set specialization of the limiting normal inclusion in 6.42. -/
theorem normalCone_inter_subset_add (hC : IsClosed C) (hD : IsClosed D)
    (hCQ : ∀ v ∈ normalCone C x, -v ∈ normalCone D x → v = 0) :
    normalCone (C ∩ D) x ⊆ normalCone C x + normalCone D x := by
  let S : Fin 2 → Set E := ![C,D]
  have he : (⋂ i, S i) = C ∩ D := by ext z; simp [S,Fin.forall_fin_two]
  have hcl (i : Fin 2) : IsClosed (S i) := by fin_cases i <;> assumption
  have hq : IntersectionConstraintQualification S x := by
    intro z hz hs i
    rw [Fin.sum_univ_two] at hs
    have hneg : -(z 0) = z 1 := (neg_eq_iff_add_eq_zero).mpr hs
    have h0 := hCQ (z 0) (hz 0) (hneg.symm ▸ hz 1)
    fin_cases i
    · exact h0
    · simpa [h0] using hneg.symm
  intro v hv
  obtain ⟨z,hz,hs⟩ := normalCone_iInter_subset_finiteSetSum hcl hq (he.symm ▸ hv)
  exact ⟨z 0,hz 0,z 1,hz 1,(Fin.sum_univ_two z).symm.trans hs⟩

private abbrev constrainedEpigraph (f : E → EReal) (C : Set E) :=
  euclideanEpigraph f ∩ l2ProdSet C (univ : Set ℝ)

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] in
private theorem locallyLsc_of_lsc_finite (hl : LowerSemicontinuous f) (hx : f x = c) :
    IsLocallyLscAt f x := by
  refine isLocallyLscAt_of_isLocallyClosedAt_epigraph hx ?_
  exact IsClosed.isLocallyClosedAt (isClosed_epigraph_of_lsc_ereal f hl) _

/-- Decompose the downward normal to the constrained epigraph using 6.42.
The horizontal normals are exactly the ones tested in the qualification. -/
private theorem exists_subgradient_neg_normal_of_downward (hC : IsClosed C)
    (hl : LowerSemicontinuous f) (hx : f x = c)
    (hCQ : ∀ v ∈ horizonSubdifferential f x, -v ∈ normalCone C x → v = 0)
    (hn : WithLp.toLp 2 ((0:E),(-1:ℝ)) ∈ normalCone (constrainedEpigraph f C) (WithLp.toLp 2 (x,c))) :
    ∃ v ∈ subdifferential f x, -v ∈ normalCone C x := by
  let p := WithLp.toLp 2 (x,c)
  let D := l2ProdSet C (univ : Set ℝ)
  have hp : IsLocallyLscAt f x := locallyLsc_of_lsc_finite hl hx
  have hprod : normalCone D p = l2ProdSet (normalCone C x) {(0:ℝ)} := by
    rw [show normalCone D p = _ from normalCone_l2ProdSet C univ x c, normalCone_univ]
  have hq : ∀ n ∈ normalCone (euclideanEpigraph f) p, -n ∈ normalCone D p → n = 0 := by
    rintro n hn hneg
    obtain ⟨⟨v,b⟩,rfl⟩ := (WithLp.toLp_surjective 2) n
    rw [hprod] at hneg
    have hb : -b = 0 := hneg.2
    have h0 := neg_eq_zero.mp hb
    subst b
    have hv := hCQ v ((mem_horizonSubdifferential_iff_epigraph_normal_of_locallyLsc hp hx).mpr hn) hneg.1
    exact hv ▸ rfl
  have hecl := (isClosed_epigraph_of_lsc_ereal f hl).preimage (l2ProdEquiv E).continuous
  obtain ⟨a,ha,b,hb,hab⟩ := normalCone_inter_subset_add hecl (isClosed_l2ProdSet hC isClosed_univ) hq hn
  rw [hprod] at hb
  obtain ⟨⟨u,r⟩,rfl⟩ := (WithLp.toLp_surjective 2) a
  obtain ⟨⟨v,s⟩,rfl⟩ := (WithLp.toLp_surjective 2) b
  have hs : s = 0 := hb.2
  have hr : r + s = -1 := congrArg (fun p : WithLp 2 (E × ℝ) ↦ p.snd) hab
  have hu : u + v = 0 := congrArg (fun p : WithLp 2 (E × ℝ) ↦ p.fst) hab
  rw [hs,add_zero] at hr
  exact ⟨u,(mem_subdifferential_iff_epigraph_normal hx).mpr (hr ▸ ha),
    (neg_eq_iff_add_eq_zero.mpr hu).symm ▸ hb.1⟩

/-- **Theorem 8.15**, necessary stationarity at a finite local minimum. -/
theorem IsLocalMinOn.exists_subgradient_neg_mem_normalCone (hC : IsClosed C) (hl : LowerSemicontinuous f)
    (hxC : x ∈ C) (hx : f x = c) (hm : IsLocalMinOn f C x)
    (hCQ : ∀ v ∈ horizonSubdifferential f x, -v ∈ normalCone C x → v = 0) :
    ∃ v ∈ subdifferential f x, -v ∈ normalCone C x := by
  apply exists_subgradient_neg_normal_of_downward hC hl hx hCQ
  apply regularNormalCone_subset_normalCone
  refine ⟨⟨hx.le,hxC,mem_univ _⟩, fun ε hε ↦ ?_⟩
  let p := WithLp.toLp 2 (x,c)
  have ht : Tendsto (fun q : WithLp 2 (E × ℝ) ↦ q.fst) (𝓝[constrainedEpigraph f C] p) (𝓝[C] x) :=
    tendsto_nhdsWithin_iff.mpr ⟨((WithLp.continuous_fst 2 E ℝ).tendsto p).mono_left nhdsWithin_le_nhds,
      mem_of_superset self_mem_nhdsWithin fun _ h ↦ h.2.1⟩
  filter_upwards [ht.eventually hm,self_mem_nhdsWithin] with q hq hmem
  have hheight : c ≤ q.snd := EReal.coe_le_coe_iff.mp (hx ▸ hq.trans hmem.1)
  change ⟪(0:E),q.fst-x⟫_ℝ + (q.snd-c)*(-1) ≤ _
  simpa using (show -(q.snd-c) ≤ ε * ‖q-p‖ from (by linarith : -(q.snd-c) ≤ 0).trans
    (mul_nonneg hε.le (norm_nonneg _)))

private theorem downward_regularNormal_of_tangent_nonneg (hxC : x ∈ C) (hx : f x = c)
    (ht : ∀ w ∈ tangentCone C x, 0 ≤ subderivative f x w) :
    WithLp.toLp 2 ((0:E),(-1:ℝ)) ∈ regularNormalCone (constrainedEpigraph f C) (WithLp.toLp 2 (x,c)) := by
  apply mem_regularNormalCone_of_forall_inner_nonpos (show WithLp.toLp 2 (x,c) ∈ constrainedEpigraph f C
    from ⟨hx.le,hxC,mem_univ _⟩)
  intro w hw
  have hwC := tangentCone_l2ProdSet_subset C (univ : Set ℝ) x c (tangentCone_mono inter_subset_right _ hw)
  have hdf := tangentCone_mono (show constrainedEpigraph f C ⊆ euclideanEpigraph f from inter_subset_left) _ hw
  rw [← euclideanEpigraph_subderivative hx] at hdf
  have hs : (0:ℝ) ≤ w.snd := EReal.coe_le_coe_iff.mp ((ht w.fst hwC.1).trans hdf)
  change ⟪(0:E),w.fst⟫_ℝ + w.snd * (-1) ≤ 0
  simpa using hs

/-- **Theorem 8.15**, stationarity versus nonnegative directional growth
when the function and feasible set are both regular. -/
theorem subgradient_stationarity_iff_tangent_nonneg (hC : IsClosed C) (hl : LowerSemicontinuous f)
    (hxC : x ∈ C) (hx : f x = c) (hr : IsSubdifferentiallyRegularAt f x) (hrC : IsClarkeRegularAt C x)
    (hCQ : ∀ v ∈ horizonSubdifferential f x, -v ∈ normalCone C x → v = 0) :
    (∃ v ∈ subdifferential f x, -v ∈ normalCone C x) ↔ ∀ w ∈ tangentCone C x, 0 ≤ subderivative f x w := by
  constructor
  · rintro ⟨v,hv,hn⟩ w hw
    rw [hr.subdifferential_eq_regularSubdifferential] at hv
    rw [hrC.2,mem_regularNormalCone_iff_inner_nonpos hxC] at hn
    have hinner : 0 ≤ ⟪v,w⟫_ℝ := by simpa using hn w hw
    exact (EReal.coe_le_coe_iff.mpr hinner).trans (inner_le_subderivative_of_mem_regularSubdifferential hv w)
  · intro ht
    exact exists_subgradient_neg_normal_of_downward hC hl hx hCQ (regularNormalCone_subset_normalCone _ _
      (downward_regularNormal_of_tangent_nonneg hxC hx ht))

/-- **Theorem 8.15**, convex sufficiency without a constraint qualification. -/
theorem isMinOn_of_convex_subgradient_stationarity (hc : Convex ℝ (epigraph f)) (hp : IsProper f)
    (hC : Convex ℝ C) (hxC : x ∈ C) (hx : f x = c)
    (hstat : ∃ v ∈ subdifferential f x, -v ∈ normalCone C x) : IsMinOn f C x := by
  rintro y hy
  obtain ⟨v,hv,hn⟩ := hstat
  rw [normalCone_eq_of_convex hC hxC] at hn
  have hinner : 0 ≤ ⟪v,y-x⟫_ℝ := by simpa using hn y hy
  rw [hx]
  exact (EReal.coe_le_coe_iff.mpr (le_add_of_nonneg_right hinner)).trans
    ((mem_subdifferential_iff_of_convex hc hp hx).mp hv y)

/-- The tangent condition also suffices in the convex case, including
intersections without a constraint qualification. -/
theorem isMinOn_of_convex_subderivative_nonneg (hc : Convex ℝ (epigraph f)) (hp : IsProper f)
    (hC : Convex ℝ C) (hxC : x ∈ C) (hx : f x = c) (ht : ∀ w ∈ tangentCone C x, 0 ≤ subderivative f x w) :
    IsMinOn f C x := by
  have hn := downward_regularNormal_of_tangent_nonneg hxC hx ht
  have hconv : Convex ℝ (constrainedEpigraph f C) := (convex_preimage_continuousLinearEquiv (l2ProdEquiv E) hc).inter
    (convex_preimage_continuousLinearEquiv (l2ProdEquiv E) (hC.prod convex_univ))
  rw [regularNormalCone_eq_of_convex hconv (show WithLp.toLp 2 (x,c) ∈ constrainedEpigraph f C
    from ⟨hx.le,hxC,mem_univ _⟩)] at hn
  intro y hy
  by_cases htop : f y = ⊤
  · simp [htop]
  have he := EReal.coe_toReal htop (hp.2 y).ne'
  have h := hn (WithLp.toLp 2 (y,(f y).toReal)) ⟨he.ge,hy,mem_univ _⟩
  change ⟪(0:E),y-x⟫_ℝ + ((f y).toReal-c)*(-1) ≤ 0 at h
  simp at h
  change f x ≤ f y
  exact hx ▸ (EReal.coe_le_coe_iff.mpr h).trans_eq he

end RW
