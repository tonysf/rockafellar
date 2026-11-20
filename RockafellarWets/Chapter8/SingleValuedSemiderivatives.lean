/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: A single-valued semiderivative under a growth bound
-/

import RockafellarWets.Chapter8.MappingSemiderivatives

open Bornology Filter Metric Set Topology
open scoped Pointwise

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S H : E → Set F} {x : E} {u : F} {A : E → F}

/-- The quantitative assumption in Exercise 8.43(e). -/
def HasMappingLinearGrowth (S : E → Set F) (x : E) (u : F) : Prop :=
  ∃ κ : ℝ, 0 ≤ κ ∧ ∀ᶠ y in 𝓝 x, (S y).Nonempty ∧ ∀ v ∈ S y, ‖v-u‖ ≤ κ * ‖y-x‖

/-- The expansion in 8.43(f), with a common little-o error for all values
of the mapping at the moving point. -/
def HasMappingFirstOrderExpansion (S : E → Set F) (x : E) (u : F) (A : E → F) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ y in 𝓝 x, (S y).Nonempty ∧ ∀ v ∈ S y, ‖v-u-A (y-x)‖ ≤ ε*‖y-x‖

theorem hasMappingSemiderivative_iff_uniformAlong [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] :
    HasMappingSemiderivative S x u H ↔ SvContinuousOn H univ ∧
      ∀ B : Set E, IsBounded B → ∀ ε > 0, ∀ ρ > 0, ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ w ∈ B,
        mappingDifferenceQuotient S x u t w ∩ closedBall 0 ρ ⊆ thickening ε (H w) ∧
          H w ∩ closedBall 0 ρ ⊆ thickening ε (mappingDifferenceQuotient S x u t w) := by
  rw [hasMappingSemiderivative_iff_uniform]
  constructor
  · rintro ⟨hc,hU⟩
    refine ⟨hc,fun B hB ε hε ρ hρ ↦ ?_⟩
    by_contra h
    obtain ⟨τ,ht,hfail⟩ := exists_seq_forall_of_frequently (not_eventually.mp h)
    exact ((hU τ ht B hB ε hε ρ hρ).and (.of_forall hfail)).exists.elim fun _ hp ↦ hp.2 hp.1
  · rintro ⟨hc,hU⟩
    exact ⟨hc,fun τ ht B hB ε hε ρ hρ ↦ ht.eventually (hU B hB ε hε ρ hρ)⟩

private theorem quotient_outer_subset (S : E → Set F) (x w : E) (u : F) :
    outerSetLimitAlong ((𝓝[>] (0:ℝ)) ×ˢ 𝓝 w) (fun p ↦ mappingDifferenceQuotient S x u p.1 p.2) ⊆
      graphicalDerivative S x u w := by
  intro z hz
  change (w,z) ∈ svGraph (graphicalDerivative S x u)
  rw [svGraph_graphicalDerivative_eq_outerLimit]
  intro U hU
  rw [nhds_prod_eq] at hU
  obtain ⟨V,hV,Z,hZ,hVZ⟩ := mem_prod_iff.mp hU
  rw [frequently_iff]
  intro T hT
  obtain ⟨⟨t,q⟩, ⟨v,hv,hvZ⟩,ht,hq⟩ := ((hz _ hZ).and_eventually (prod_mem_prod hT hV)).exists
  exact ⟨t,ht,(q,v),hv,hVZ ⟨hq,hvZ⟩⟩

private theorem quotient_norm_bound {t : ℝ} (ht : 0 < t) {κ : ℝ} {q : E}
    (hb : ∀ v ∈ S (x+t • q), ‖v-u‖ ≤ κ*‖(x+t • q)-x‖) {z : F}
    (hz : z ∈ mappingDifferenceQuotient S x u t q) : ‖z‖ ≤ κ*‖q‖ := by
  obtain ⟨v,hv,rfl⟩ := hz
  have h := hb v hv
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht] at h
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht), inv_mul_le_iff₀ ht]
  linarith only [h,mul_left_comm κ t ‖q‖]

private theorem quotient_error_bound (hom : ∀ q (t : ℝ), 0 < t → A (t • q) = t • A q)
    {t : ℝ} (ht : 0 < t) {ε : ℝ} {q : E}
    (hb : ∀ v ∈ S (x+t • q), ‖v-u-A ((x+t • q)-x)‖ ≤ ε*‖(x+t • q)-x‖) {z : F}
    (hz : z ∈ mappingDifferenceQuotient S x u t q) : ‖z-A q‖ ≤ ε*‖q‖ := by
  obtain ⟨v,hv,rfl⟩ := hz
  have h := hb v hv
  rw [add_sub_cancel_left,hom q t ht,norm_smul,Real.norm_eq_abs,abs_of_pos ht] at h
  have he : t⁻¹ • (v-u) - A q = t⁻¹ • (v-u-t • A q) := by simp [smul_sub, ht.ne']
  rw [he,norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht), inv_mul_le_iff₀ ht]
  linarith only [h,mul_left_comm ε t ‖q‖]

omit [NormedSpace ℝ F] in
private theorem pkConvergesAlong_singleton_of_tubes {ι : Type*} {l : Filter ι} [l.NeBot]
    {C : ι → Set F} {z : F} (hne : ∀ᶠ i in l, (C i).Nonempty)
    (ht : ∀ ε > 0, ∀ᶠ i in l, ∀ v ∈ C i, dist v z < ε) : PKConvergesAlong l C {z} := by
  have hi : {z} ⊆ innerSetLimitAlong l C := by
    rintro _ rfl U hU
    obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp hU
    filter_upwards [hne,ht ε hε] with i ⟨v,hv⟩ hb
    exact ⟨v,hv,hsub (hb v hv)⟩
  have ho : outerSetLimitAlong l C ⊆ {z} := by
    intro v hv
    by_contra hn
    have hd : 0 < dist v z := dist_pos.mpr hn
    have he : 0 < dist v z /2 := half_pos hd
    obtain ⟨i,⟨q,hq,hqv⟩,hb⟩ := ((hv _ (ball_mem_nhds v he)).and_eventually (ht _ he)).exists
    have hqz := hb q hq
    have hdvq : dist v q < dist v z /2 := by simpa [dist_comm] using (mem_ball.mp hqv)
    linarith [dist_triangle v q z]
  have hio := innerSetLimitAlong_subset_outerSetLimitAlong (l := l) C
  exact ⟨Subset.antisymm (hio.trans ho) hi,Subset.antisymm ho (hi.trans hio)⟩

/-- **Exercise 8.43(e) implies (a)**. The growth bound makes every moving
quotient fiber eventually bounded, so any failure to cluster at its unique
graphical derivative would produce a second graphical derivative. -/
theorem hasMappingSemiderivative_of_linearGrowth [FiniteDimensional ℝ F]
    (hd : graphicalDerivative S x u = svSingleton A) (h : HasMappingLinearGrowth S x u) :
    HasMappingSemiderivative S x u (svSingleton A) := by
  obtain ⟨κ,hκ,hg⟩ := h
  intro w
  let l := (𝓝[>] (0:ℝ)) ×ˢ 𝓝 w
  let C := fun p : ℝ × E ↦ mappingDifferenceQuotient S x u p.1 p.2
  have hout : outerSetLimitAlong l C ⊆ {A w} := by
    have ho := quotient_outer_subset S x w u
    rw [hd] at ho
    exact ho
  have ht : Tendsto (Prod.fst : ℝ × E → ℝ) l (𝓝 0) := tendsto_fst.mono_right nhdsWithin_le_nhds
  have hy : Tendsto (fun p : ℝ × E ↦ x+p.1 • p.2) l (𝓝 x) := by
    simpa using (tendsto_const_nhds (x := x)).add (ht.smul (tendsto_snd (f := 𝓝[>] (0:ℝ)) (g := 𝓝 w)))
  have hne : ∀ᶠ p in l, (C p).Nonempty := (hy.eventually hg).mono fun _ hp ↦ hp.1.image _
  have hq : ∀ᶠ p : ℝ × E in l, ‖p.2‖ < ‖w‖ + 1 :=
    (continuous_norm.tendsto w).comp tendsto_snd |>.eventually_lt_const (by linarith)
  let K := closedBall (0:F) (κ*(‖w‖+1))
  have hb : ∀ᶠ p in l, C p ⊆ K := by
    filter_upwards [hy.eventually hg,tendsto_fst.eventually (self_mem_nhdsWithin : Ioi (0:ℝ) ∈ 𝓝[>] 0),hq]
      with p hp ht' hpq z hz
    exact mem_closedBall_zero_iff.mpr ((quotient_norm_bound ht' hp.2 hz).trans (mul_le_mul_of_nonneg_left hpq.le hκ))
  apply pkConvergesAlong_singleton_of_tubes hne
  intro ε hε
  by_contra hfail
  have hfreq : ∃ᶠ p in l, (C p ∩ (K ∩ (ball (A w) ε)ᶜ)).Nonempty := by
    refine ((not_eventually.mp hfail).and_eventually hb).mono ?_
    rintro p ⟨hn,hK⟩
    push_neg at hn
    obtain ⟨v,hv,hvε⟩ := hn
    exact ⟨v,hv,hK hv,not_lt.mpr hvε⟩
  obtain ⟨v,hv,_,hnot⟩ := outerSetLimitAlong_inter_nonempty_of_frequently
    ((isCompact_closedBall _ _).inter_right isOpen_ball.isClosed_compl) hfreq
  exact hnot ((mem_singleton_iff.mp (hout hv)) ▸ mem_ball_self hε)

private theorem singleton_homogeneous_iff :
    SvPositivelyHomogeneous (svSingleton A) ↔ A 0 = 0 ∧ ∀ w (r : ℝ), 0 < r → A (r • w) = r • A w := by
  constructor
  · rintro ⟨hz,hs⟩
    refine ⟨(mem_singleton_iff.mp hz).symm,fun w r hr ↦ ?_⟩
    have he := hs w r hr
    simpa [svSingleton,smul_set_singleton] using he
  · rintro ⟨hz,hs⟩
    exact ⟨by simp [svSingleton,hz],fun w r hr ↦ by simp [svSingleton,hs w r hr,smul_set_singleton]⟩

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- The fiber at the base point in 8.43(e,f). -/
theorem HasMappingLinearGrowth.baseFiber (h : HasMappingLinearGrowth S x u) : S x = {u} := by
  obtain ⟨κ,_,hg⟩ := h
  obtain ⟨⟨z,hz⟩,hb⟩ := mem_of_mem_nhds hg
  have he : ∀ v ∈ S x, v = u := by
    intro v hv
    have hh := hb v hv
    exact sub_eq_zero.mp (by simpa using hh)
  exact Subset.antisymm he (singleton_subset_iff.mpr (he z hz ▸ hz))

/-- **Exercise 8.43(f) implies (a)**. The uniform error is evaluated in a
bounded neighborhood of the test direction. -/
theorem hasMappingSemiderivative_of_expansion (hc : Continuous A)
    (hom : SvPositivelyHomogeneous (svSingleton A)) (he : HasMappingFirstOrderExpansion S x u A) :
    HasMappingSemiderivative S x u (svSingleton A) := by
  intro w
  let l := (𝓝[>] (0:ℝ)) ×ˢ 𝓝 w
  have ht : Tendsto (Prod.fst : ℝ × E → ℝ) l (𝓝 0) := tendsto_fst.mono_right nhdsWithin_le_nhds
  have hy : Tendsto (fun p : ℝ × E ↦ x+p.1 • p.2) l (𝓝 x) := by
    simpa using (tendsto_const_nhds (x := x)).add (ht.smul (tendsto_snd (f := 𝓝[>] (0:ℝ)) (g := 𝓝 w)))
  apply pkConvergesAlong_singleton_of_tubes ((hy.eventually (he 1 one_pos)).mono fun _ hp ↦ hp.1.image _)
  intro ε hε
  have hM : 0 < ‖w‖+1 := by positivity
  let η := (ε/2)/(‖w‖+1)
  have hη : 0 < η := div_pos (half_pos hε) hM
  have hq : ∀ᶠ p : ℝ × E in l, ‖p.2‖ < ‖w‖+1 :=
    ((continuous_norm.tendsto w).comp tendsto_snd).eventually_lt_const (by linarith)
  have hA : ∀ᶠ p : ℝ × E in l, dist (A p.2) (A w) < ε/2 :=
    ((hc.tendsto w).comp tendsto_snd).eventually (ball_mem_nhds _ (half_pos hε))
  filter_upwards [hy.eventually (he η hη),tendsto_fst.eventually (self_mem_nhdsWithin : Ioi (0:ℝ) ∈ 𝓝[>] 0),
    hq,hA] with p hp htp hpq hAp z hz
  have h1 := quotient_error_bound (singleton_homogeneous_iff.mp hom).2 htp hp.2 hz
  have h2 : η*‖p.2‖ < ε/2 := calc
    _ < η*(‖w‖+1) := mul_lt_mul_of_pos_left hpq hη
    _ = _ := div_mul_cancel₀ _ hM.ne'
  rw [← dist_eq_norm] at h1
  linarith [dist_triangle z (A p.2) (A w)]

/-- A continuous, positively homogeneous single-valued mapping is bounded
on the unit ball and grows at most linearly on the whole space. -/
private theorem exists_linear_bound_singleton [FiniteDimensional ℝ E] (hc : Continuous A)
    (hom : SvPositivelyHomogeneous (svSingleton A)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y, ‖A y‖ ≤ M*‖y‖ := by
  obtain ⟨K,hK⟩ := (isCompact_closedBall (0:E) 1).bddAbove_image hc.norm.continuousOn
  obtain ⟨h₀,hs⟩ := singleton_homogeneous_iff.mp hom
  refine ⟨max 0 K,le_max_left _ _,fun y ↦ ?_⟩
  by_cases hy : y = 0
  · simp [hy,h₀]
  have hr := norm_pos_iff.mpr hy
  let q := ‖y‖⁻¹ • y
  have hq : ‖q‖ = 1 := by simp [q,norm_smul,hr.ne']
  have hq' : q ∈ closedBall (0:E) 1 := mem_closedBall_zero_iff.mpr hq.le
  have he : ‖y‖ • q = y := smul_inv_smul₀ hr.ne' y
  have hAy : A y = ‖y‖ • A q := by simpa only [he] using hs q ‖y‖ hr
  rw [hAy,norm_smul,Real.norm_eq_abs,abs_of_pos hr,mul_comm]
  exact mul_le_mul_of_nonneg_right ((hK (mem_image_of_mem _ hq')).trans (le_max_right _ _)) hr.le

/-- **Exercise 8.43(f) implies (e)**: the expansion gives both the
graphical derivative and the uniform linear growth bound. -/
theorem graphicalDerivative_and_linearGrowth_of_expansion [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (hc : Continuous A) (hom : SvPositivelyHomogeneous (svSingleton A))
    (he : HasMappingFirstOrderExpansion S x u A) :
    graphicalDerivative S x u = svSingleton A ∧ HasMappingLinearGrowth S x u := by
  obtain ⟨M,hM,hMb⟩ := exists_linear_bound_singleton hc hom
  refine ⟨(hasMappingSemiderivative_of_expansion hc hom he).protoDerivative.2,M+1,by linarith,?_⟩
  filter_upwards [he 1 one_pos] with y hy
  refine ⟨hy.1,fun v hv ↦ ?_⟩
  have ht := norm_sub_le (v-u-A (y-x)) (-A (y-x))
  simp only [sub_neg_eq_add,sub_add_cancel,norm_neg] at ht
  linarith [hy.2 v hv,hMb (y-x)]

/-- **Exercise 8.43(e) implies (f)**. Uniform convergence on the normalized
directions controls every quotient value, since the growth estimate places
all of them inside a single output ball. -/
theorem expansion_of_graphicalDerivative_and_linearGrowth [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (hd : graphicalDerivative S x u = svSingleton A) (hg : HasMappingLinearGrowth S x u) :
    Continuous A ∧ SvPositivelyHomogeneous (svSingleton A) ∧ HasMappingFirstOrderExpansion S x u A := by
  have hsemi := hasMappingSemiderivative_of_linearGrowth hd hg
  have hfib := hg.baseFiber
  have hx : u ∈ S x := hfib.ge (mem_singleton _)
  obtain ⟨_,hom,hcont,_⟩ := hsemi.properties hx
  have hc : Continuous A := continuous_iff_continuousAt.mpr fun w ↦
    (svContinuousAt_svSingleton_iff A w).mp (svContinuousWithinAt_univ.mp (hcont w (mem_univ _)))
  refine ⟨hc,hom,fun ε hε ↦ ?_⟩
  obtain ⟨hA₀,hAhom⟩ := singleton_homogeneous_iff.mp hom
  obtain ⟨κ,hκ,hbound⟩ := hg
  have hU := (hasMappingSemiderivative_iff_uniformAlong.mp hsemi).2 (closedBall (0:E) 1)
    isBounded_closedBall ε hε (κ+1) (by linarith)
  have hver : Tendsto (fun y : E ↦ ‖y-x‖) (𝓝 x) (𝓝 0) := by
    simpa using (continuous_id.sub (continuous_const (y := x))).norm.tendsto x
  filter_upwards [hbound,hver.eventually (eventually_nhdsWithin_iff.mp hU)] with y hy hU
  refine ⟨hy.1,fun v hv ↦ ?_⟩
  by_cases hxy : y = x
  · subst y
    have he : v = u := hfib.le hv
    simp [he,hA₀]
  let t := ‖y-x‖
  let w := t⁻¹ • (y-x)
  let z := t⁻¹ • (v-u)
  have ht : 0 < t := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hw : ‖w‖ = 1 := by simp [w,norm_smul,t, (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)).ne']
  have hwB : w ∈ closedBall (0:E) 1 := mem_closedBall_zero_iff.mpr hw.le
  have htw : t • w = y-x := smul_inv_smul₀ ht.ne' _
  have hyw : x+t • w = y := by rw [htw,add_sub_cancel]
  have hz : z ∈ mappingDifferenceQuotient S x u t w := ⟨v,hyw ▸ hv,rfl⟩
  have hzB : z ∈ closedBall (0:F) (κ+1) := by
    have hzκ := quotient_norm_bound ht (show ∀ v ∈ S (x+t • w), _ from hyw ▸ hy.2) hz
    rw [hw,mul_one] at hzκ
    exact mem_closedBall_zero_iff.mpr (by linarith)
  obtain ⟨v',hv',hdist⟩ := mem_thickening_iff.mp ((hU ht w hwB).1 ⟨hz,hzB⟩)
  have he : v' = A w := hv'
  rw [he,dist_eq_norm] at hdist
  have htz : t • z = v-u := smul_inv_smul₀ ht.ne' _
  have hAy : A (y-x) = t • A w := by simpa only [htw] using hAhom w t ht
  rw [hAy,← htz,← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos ht,mul_comm]
  exact mul_le_mul_of_nonneg_right hdist.le ht.le

/-- The full equivalence of the single-valued clauses 8.43(e) and (f). -/
theorem graphicalDerivative_and_linearGrowth_iff_expansion [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] :
    graphicalDerivative S x u = svSingleton A ∧ HasMappingLinearGrowth S x u ↔
      Continuous A ∧ SvPositivelyHomogeneous (svSingleton A) ∧ HasMappingFirstOrderExpansion S x u A :=
  ⟨fun h ↦ expansion_of_graphicalDerivative_and_linearGrowth h.1 h.2,
    fun h ↦ graphicalDerivative_and_linearGrowth_of_expansion h.1 h.2.1 h.2.2⟩

end RW
