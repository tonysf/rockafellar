/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Subderivatives of distance functions
-/

import RockafellarWets.Chapter8.RegularSubgradientBridge
import Mathlib.Analysis.InnerProductSpace.Calculus
import RockafellarWets.Chapter6.RegularTangentChangeOfCoordinates
import RockafellarWets.Chapter6.ProximalNormals
import RockafellarWets.Chapter5.ProjectionGraphicalConvergence

open Bornology Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {C : Set E} {x : E}

/-- The real distance to a set, regarded as an extended-real-valued function
for subdifferentiation. The distance formulas below assume a nonempty set. -/
noncomputable def distanceVA (C : Set E) (x : E) : EReal := (infDist x C : EReal)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem continuous_distanceVA (C : Set E) : Continuous (distanceVA C) :=
  continuous_coe_real_ereal.comp (continuous_infDist_pt C)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem norm_sub_eq_infDist {x p : E} (hp : p ∈ projMapping C x) :
    ‖x-p‖ = infDist x C := by simpa only [dist_eq_norm] using (mem_projMapping_iff_dist.mp hp).2

/-- The projection of a moving point has a subsequence approaching a
projection of the limiting point. -/
theorem exists_tendsto_subseq_projMapping (hC : IsClosed C) (hne : C.Nonempty)
    {xs ps : ℕ → E} (hxs : Tendsto xs atTop (𝓝 x)) (hp : ∀ n, ps n ∈ projMapping C (xs n)) :
    ∃ p ∈ projMapping C x, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (ps ∘ φ) atTop (𝓝 p) := by
  obtain ⟨V,hV,hB⟩ := svLocallyBounded_projMapping hne x
  have hm : ∀ᶠ n in atTop, ps n ∈ closure (svImage (projMapping C) V) :=
    (hxs.eventually hV).mono fun n hn ↦ subset_closure (mem_svImage.mpr ⟨xs n,hn,hp n⟩)
  obtain ⟨p,_,φ,hφ,hp'⟩ := hB.isCompact_closure.tendsto_subseq' hm.frequently
  exact ⟨p,(isClosed_svGraph_projMapping hC).mem_of_tendsto
    ((hxs.comp hφ.tendsto_atTop).prodMk_nhds hp') (.of_forall fun n ↦ hp (φ n)),φ,hφ,hp'⟩

/-- The inclusion from the distance epigraph tangent into the distance
epigraph of the tangent set. The normalized projections are bounded by
the convergent argument and height quotients. -/
private theorem infDist_tangent_le_of_tangent_distanceVA (hC : IsClosed C) (hx : x ∈ C) {w : E} {b : ℝ}
    (h : (w,b) ∈ tangentCone (epigraph (distanceVA C)) (x,0)) : infDist w (tangentCone C x) ≤ b := by
  obtain ⟨q,t,hq,_,ht,ht₀,hlim⟩ := h
  let d n := (t n)⁻¹ • ((q n).1 - x)
  let a n := (t n)⁻¹ * (q n).2
  have hd : Tendsto d atTop (𝓝 w) := (continuous_fst.tendsto _).comp hlim
  have ha : Tendsto a atTop (𝓝 b) := by
    have hh := (continuous_snd.tendsto _).comp hlim
    change Tendsto (fun n ↦ (t n)⁻¹ * ((q n).2 - 0)) atTop (𝓝 b) at hh
    simpa only [a,sub_zero] using hh
  choose p hp using fun n ↦ projMapping_nonempty hC ⟨x,hx⟩ (q n).1
  let v n := (t n)⁻¹ • (p n-x)
  have hdist (n : ℕ) : ‖d n-v n‖ ≤ a n := by
    have hh : infDist (q n).1 C ≤ (q n).2 := EReal.coe_le_coe_iff.mp (hq n)
    rw [← norm_sub_eq_infDist (hp n)] at hh
    change ‖(t n)⁻¹ • ((q n).1-x) - (t n)⁻¹ • (p n-x)‖ ≤ (t n)⁻¹ * (q n).2
    rw [← smul_sub,sub_sub_sub_cancel_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (ht n))]
    exact mul_le_mul_of_nonneg_left hh (inv_pos.mpr (ht n)).le
  obtain ⟨D,hD⟩ := (Metric.isBounded_range_of_tendsto _ hd).exists_norm_le
  obtain ⟨M,hM⟩ := (Metric.isBounded_range_of_tendsto _ ha).exists_norm_le
  have hvB (n : ℕ) : v n ∈ closedBall (0:E) (D+M) := by
    apply mem_closedBall_zero_iff.mpr
    have hh := norm_add_le (v n-d n) (d n)
    rw [sub_add_cancel,norm_sub_rev] at hh
    exact hh.trans ((add_le_add ((hdist n).trans ((le_abs_self _).trans (hM _ (mem_range_self n)))) (hD _ (mem_range_self n))).trans_eq (add_comm ..))
  obtain ⟨v₀,_,φ,hφ,hv⟩ := (isCompact_closedBall _ _).tendsto_subseq hvB
  have hvT : v₀ ∈ tangentCone C x := mem_tangentCone_of_forall
    (xs := p ∘ φ) (τs := t ∘ φ) (fun n ↦ (hp _).1) (fun n ↦ ht _) (ht₀.comp hφ.tendsto_atTop) hv
  have hh := le_of_tendsto_of_tendsto (((hd.comp hφ.tendsto_atTop).sub hv).norm)
    (ha.comp hφ.tendsto_atTop) (.of_forall fun n ↦ hdist (φ n))
  exact (infDist_le_dist_of_mem hvT).trans (by simpa only [dist_eq_norm] using hh)

/-- **Example 8.53**, at a feasible point the subderivative of the distance
is the distance to the tangent cone. -/
theorem subderivative_distanceVA_of_mem (hC : IsClosed C) (hx : x ∈ C) :
    subderivative (distanceVA C) x = distanceVA (tangentCone C x) := by
  have hx₀ : distanceVA C x = ((0:ℝ):EReal) := congrArg ((↑) : ℝ → EReal) (infDist_zero_of_mem hx)
  apply eq_of_epigraph_eq
  rw [epigraph_subderivative_eq_tangentCone hx₀]
  ext p
  obtain ⟨w,b⟩ := p
  constructor
  · intro h
    exact EReal.coe_le_coe_iff.mpr (infDist_tangent_le_of_tangent_distanceVA hC hx h)
  · intro hb
    obtain ⟨v,hv⟩ := projMapping_nonempty (isClosed_tangentCone C x) ⟨0,(isCone_tangentCone hx).1⟩ w
    have hd := (norm_sub_eq_infDist hv).le.trans (EReal.coe_le_coe_iff.mp hb)
    obtain ⟨ys,t,hys,_,ht,ht₀,hvto⟩ := hv.1
    let q n : E × ℝ := (ys n+t n • (w-v), t n*b)
    have hq (n : ℕ) : q n ∈ epigraph (distanceVA C) := by
      apply EReal.coe_le_coe_iff.mpr
      calc
        infDist (ys n+t n • (w-v)) C ≤ dist (ys n+t n • (w-v)) (ys n) := infDist_le_dist_of_mem (hys n)
        _ = t n * ‖w-v‖ := by rw [dist_eq_norm,add_sub_cancel_left,norm_smul_of_nonneg (ht n).le]
        _ ≤ _ := mul_le_mul_of_nonneg_left hd (ht n).le
    apply mem_tangentCone_of_forall hq ht ht₀
    have he (n : ℕ) : (t n)⁻¹ • (q n-(x,0)) = ((t n)⁻¹ • (ys n-x)+(w-v),b) := by
      apply Prod.ext
      · change (t n)⁻¹ • (ys n + t n • (w-v)-x) = _
        rw [add_sub_right_comm,smul_add,inv_smul_smul₀ (ht n).ne']
      · change (t n)⁻¹ * (t n*b-0) = b
        field_simp [(ht n).ne']
        ring
    simp_rw [he]
    simpa using (hvto.add_const (w-v)).prodMk_nhds (tendsto_const_nhds (x := b))

omit [FiniteDimensional ℝ E] in
/-- For a moving, nonzero base vector, normalized differences of norms
converge to the projection of the limiting direction on its unit vector. -/
private theorem tendsto_scaled_norm_sub {ι : Type*} {l : Filter ι} {a w : E} (ha : a ≠ 0)
    {p q : ι → E} {k : ι → ℝ} (hp : Tendsto p l (𝓝 a)) (hq : Tendsto q l (𝓝 a))
    (hd : Tendsto (fun i ↦ k i • (p i-q i)) l (𝓝 w)) :
    Tendsto (fun i ↦ k i * (‖p i‖-‖q i‖)) l (𝓝 (⟪a,w⟫_ℝ/‖a‖)) := by
  have hs := RW.HasStrictFDerivAt.tendsto_scaled_sub (hasStrictFDerivAt_norm_sq a) hp hq hd
  have hsq : Tendsto (fun i ↦ k i*(‖p i‖^2-‖q i‖^2)) l (𝓝 (2*⟪a,w⟫_ℝ)) := by
    simpa [smul_eq_mul,innerSL_apply_apply] using hs
  have hden := hp.norm.add hq.norm
  have hpos := norm_pos_iff.mpr ha
  have hlim := hsq.div hden (show ‖a‖+‖a‖ ≠ 0 by positivity)
  have he : 2*⟪a,w⟫_ℝ/(‖a‖+‖a‖) = ⟪a,w⟫_ℝ/‖a‖ := by field_simp; ring
  rw [he] at hlim
  apply hlim.congr'
  filter_upwards [hden.eventually_ne (show ‖a‖+‖a‖ ≠ 0 by positivity)] with i hi
  change k i*(‖p i‖^2-‖q i‖^2)/(‖p i‖+‖q i‖) = k i*(‖p i‖-‖q i‖)
  rw [div_eq_iff hi]
  ring

omit [FiniteDimensional ℝ E] in
/-- Every projection supplies an upper bound on the distance subderivative
outside the set. The perturbed epigraph heights are the distances to this
fixed projection. -/
theorem distance_subderivative_le_projection {p : E} (hx : x ∉ C)
    (hp : p ∈ projMapping C x) (w : E) :
    subderivative (distanceVA C) x w ≤ ((⟪x-p,w⟫_ℝ / infDist x C : ℝ) : EReal) := by
  have hne : x-p ≠ 0 := sub_ne_zero.mpr fun h ↦ hx (h ▸ hp.1)
  change (w,⟪x-p,w⟫_ℝ / infDist x C) ∈ epigraph (subderivative (distanceVA C) x)
  rw [epigraph_subderivative_eq_tangentCone (show distanceVA C x = ((infDist x C : ℝ):EReal) from rfl)]
  let t (n : ℕ) : ℝ := 1/((n:ℝ)+1)
  have ht (n : ℕ) : 0 < t n := by dsimp [t]; positivity
  have ht₀ : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let y n := x+t n • w
  have hy : Tendsto y atTop (𝓝 x) := by simpa [y] using (tendsto_const_nhds (x := x)).add (ht₀.smul_const w)
  have hq (n : ℕ) : (t n)⁻¹ • (y n-x) = w := by simp [y,smul_smul,(ht n).ne']
  have hheight := tendsto_scaled_norm_sub hne (hy.sub_const p) (tendsto_const_nhds (x := x-p))
    (k := fun n ↦ (t n)⁻¹) (w := w) (by simp [sub_sub_sub_cancel_right,hq])
  apply mem_tangentCone_of_forall (xs := fun n ↦ (y n,‖y n-p‖))
    (fun n ↦ EReal.coe_le_coe_iff.mpr (show infDist (y n) C ≤ ‖y n-p‖ by simpa only [dist_eq_norm] using infDist_le_dist_of_mem (x := y n) hp.1))
    ht ht₀
  have h₁ : Tendsto (fun n ↦ (t n)⁻¹ • (y n-x)) atTop (𝓝 w) := by simp [hq]
  exact h₁.prodMk_nhds (by simpa only [norm_sub_eq_infDist hp] using hheight)

/-- Conversely, any real tangent epigraph height dominates the directional
slope of some projection. Moving projections can be chosen independently
at every step; compactness identifies their subsequential limit. -/
private theorem exists_projection_slope_le_of_distance_tangent (hC : IsClosed C) (hne : C.Nonempty)
    (hx : x ∉ C) {w : E} {b : ℝ}
    (h : (w,b) ∈ tangentCone (epigraph (distanceVA C)) (x,infDist x C)) :
    ∃ p ∈ projMapping C x, ⟪x-p,w⟫_ℝ/infDist x C ≤ b := by
  obtain ⟨q,t,hq,hq₀,ht,_,hlim⟩ := h
  let y n := (q n).1
  have hy : Tendsto y atTop (𝓝 x) := (continuous_fst.tendsto _).comp hq₀
  have hd : Tendsto (fun n ↦ (t n)⁻¹ • (y n-x)) atTop (𝓝 w) := (continuous_fst.tendsto _).comp hlim
  have hb : Tendsto (fun n ↦ (t n)⁻¹ * ((q n).2-infDist x C)) atTop (𝓝 b) := (continuous_snd.tendsto _).comp hlim
  choose ps hps using fun n ↦ projMapping_nonempty hC hne (y n)
  obtain ⟨p,hp,φ,hφ,hlimp⟩ := exists_tendsto_subseq_projMapping hC hne hy hps
  have hne' : x-p ≠ 0 := sub_ne_zero.mpr fun h ↦ hx (h ▸ hp.1)
  have hs := tendsto_scaled_norm_sub hne' ((hy.comp hφ.tendsto_atTop).sub hlimp)
    (tendsto_const_nhds.sub hlimp) (k := fun n ↦ (t (φ n))⁻¹) (w := w)
    (by simpa only [Function.comp_def,sub_sub_sub_cancel_right] using hd.comp hφ.tendsto_atTop)
  refine ⟨p,hp,?_⟩
  rw [← norm_sub_eq_infDist hp]
  apply le_of_tendsto_of_tendsto hs (hb.comp hφ.tendsto_atTop)
  filter_upwards with n
  change (t (φ n))⁻¹ * (‖y (φ n)-ps (φ n)‖-‖x-ps (φ n)‖) ≤ _
  apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr (ht _)).le
  apply sub_le_sub
  · rw [norm_sub_eq_infDist (hps _)]
    exact EReal.coe_le_coe_iff.mp (hq _)
  · simpa only [dist_eq_norm] using infDist_le_dist_of_mem (x := x) (hps (φ n)).1

/-- A projection farthest down the tested direction attains the minimum in
the formula for the distance subderivative. -/
theorem subderivative_distanceVA_of_notMem (hC : IsClosed C) (hne : C.Nonempty)
    (hx : x ∉ C) (w : E) : ∃ p ∈ projMapping C x,
      subderivative (distanceVA C) x w = ((⟪x-p,w⟫_ℝ / infDist x C : ℝ):EReal) ∧
      ∀ q ∈ projMapping C x, ⟪x-p,w⟫_ℝ ≤ ⟪x-q,w⟫_ℝ := by
  let h := subderivative (distanceVA C) x w
  have hupper (p : E) (hp : p ∈ projMapping C x) := distance_subderivative_le_projection hx hp w
  obtain ⟨p₀,hp₀⟩ := projMapping_nonempty hC hne x
  have hbot : h ≠ ⊥ := by
    intro he
    let b := -‖w‖-1
    have hz : (w,b) ∈ epigraph (subderivative (distanceVA C) x) := (show h ≤ (b:EReal) from he ▸ bot_le)
    rw [epigraph_subderivative_eq_tangentCone (show distanceVA C x = ((infDist x C : ℝ):EReal) from rfl)] at hz
    obtain ⟨p,hp,hpb⟩ := exists_projection_slope_le_of_distance_tangent hC hne hx hz
    have hpos := (hC.notMem_iff_infDist_pos hne).mp hx
    have habs := abs_real_inner_le_norm (x-p) w
    rw [norm_sub_eq_infDist hp] at habs
    have hlower : -‖w‖ ≤ ⟪x-p,w⟫_ℝ/infDist x C := by
      rw [le_div_iff₀ hpos]
      linarith [neg_abs_le ⟪x-p,w⟫_ℝ,mul_comm (infDist x C) ‖w‖]
    dsimp [b] at hpb
    linarith
  have hfin : h = (h.toReal:EReal) := (EReal.coe_toReal ((hupper p₀ hp₀).trans_lt (EReal.coe_lt_top _)).ne hbot).symm
  have hT : (w,h.toReal) ∈ epigraph (subderivative (distanceVA C) x) := hfin.le
  rw [epigraph_subderivative_eq_tangentCone (show distanceVA C x = ((infDist x C : ℝ):EReal) from rfl)] at hT
  obtain ⟨p,hp,hpmin⟩ := exists_projection_slope_le_of_distance_tangent hC hne hx hT
  refine ⟨p,hp,le_antisymm (hupper p hp) ((EReal.coe_le_coe_iff.mpr hpmin).trans hfin.ge),fun q hq ↦ ?_⟩
  exact (div_le_div_iff_of_pos_right ((hC.notMem_iff_infDist_pos hne).mp hx)).mp
    (hpmin.trans (EReal.coe_le_coe_iff.mp (hfin.ge.trans (hupper q hq))))

end RW
