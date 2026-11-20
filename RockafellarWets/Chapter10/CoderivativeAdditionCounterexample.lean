/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A missing closed-graph hypothesis in Exercise 10.43

A strictly differentiable perturbation can remove all limiting normals
when selected boundary points of a nonclosed graph become downward cusps.
-/
import RockafellarWets.Chapter10.GraphicalAddition
import RockafellarWets.Chapter6.BoundaryNormals
import RockafellarWets.Chapter9.StrictDifferentiability

open Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

abbrev AdditionCounterPlane := WithLp 2 (ℝ × ℝ)
private abbrev Space := WithLp 2 (AdditionCounterPlane × ℝ)
private def pt (a b c : ℝ) : Space := WithLp.toLp 2 (WithLp.toLp 2 (a,b),c)

/-- The endpoint of the open ray is retained on just the nonnegative axis. -/
def additionCounterMapping (x : AdditionCounterPlane) : Set ℝ :=
  {u | -|x.fst| < u ∨ (0 ≤ x.fst ∧ x.snd = 0 ∧ u = -|x.fst|)}

noncomputable def additionCounterPerturbation (x : AdditionCounterPlane) : ℝ := -x.fst * |x.snd|

/-- Pointwise outer semicontinuity at the base does not repair the rule. -/
theorem additionCounterMapping_svOscAt_zero : SvOscAt additionCounterMapping 0 := by
  intro u hu
  obtain ⟨a,b,ha,hab,hb⟩ := mem_outerSetLimitAlong_iff_exists_seq.mp hu
  have hlow (n : ℕ) : -|(a n).fst| ≤ b n := by
    rcases hab n with h | ⟨_,_,h⟩
    · exact h.le
    · exact h.ge
  have hzero : Tendsto (fun n ↦ -|(a n).fst|) atTop (𝓝 (0:ℝ)) := by
    simpa only [WithLp.zero_fst,abs_zero,neg_zero] using
      (((WithLp.continuous_fst 2 ℝ ℝ).tendsto 0).comp ha).abs.neg
  have hu0 : 0 ≤ u := le_of_tendsto_of_tendsto hzero hb (Eventually.of_forall hlow)
  rcases lt_or_eq_of_le hu0 with h | h
  · left
    simpa only [WithLp.zero_fst,abs_zero,neg_zero] using h
  · right
    exact ⟨le_rfl,rfl,by simpa only [WithLp.zero_fst,abs_zero,neg_zero] using h.symm⟩

private noncomputable def height (x : AdditionCounterPlane) : ℝ := -|x.fst|-x.fst*|x.snd|
private def altered (x : AdditionCounterPlane) : Set ℝ :=
  {u | height x < u ∨ (0 ≤ x.fst ∧ x.snd = 0 ∧ u = height x)}

private theorem continuous_height : Continuous height :=
  (WithLp.continuous_fst 2 ℝ ℝ).abs.neg.sub
    ((WithLp.continuous_fst 2 ℝ ℝ).mul (WithLp.continuous_snd 2 ℝ ℝ).abs)

private theorem altered_eq : altered = svAdd additionCounterMapping (svSingleton additionCounterPerturbation) := by
  funext x
  ext u
  rw [mem_svAdd_single]
  change (height x < u ∨ (0 ≤ x.fst ∧ x.snd = 0 ∧ u = height x)) ↔
    (-|x.fst| < u-additionCounterPerturbation x ∨
      (0 ≤ x.fst ∧ x.snd = 0 ∧ u-additionCounterPerturbation x = -|x.fst|))
  dsimp [height,additionCounterPerturbation]
  constructor <;> rintro (h | ⟨ha,hb,hc⟩)
  · left; linarith
  · right; exact ⟨ha,hb,by linarith⟩
  · left; linarith
  · right; exact ⟨ha,hb,by linarith⟩

/-- Despite its cusps, the perturbation has strict derivative zero at zero. -/
theorem additionCounterPerturbation_hasStrictFDerivAt :
    HasStrictFDerivAt additionCounterPerturbation (0 : AdditionCounterPlane →L[ℝ] ℝ) 0 := by
  refine HasStrictFDerivAt.of_isLittleO (Asymptotics.IsLittleO.of_bound fun ε hε ↦ ?_)
  filter_upwards [prod_mem_nhds (ball_mem_nhds (0:AdditionCounterPlane) (show 0<ε/2 by positivity))
    (ball_mem_nhds (0:AdditionCounterPlane) (show 0<ε/2 by positivity))] with p hp
  have ha : |p.1.fst| < ε/2 := (WithLp.norm_fst_le ℝ p.1).trans_lt (by simpa only [mem_ball,dist_zero_right] using hp.1)
  have hb : |p.2.snd| < ε/2 := (WithLp.norm_snd_le ℝ p.2).trans_lt (by simpa only [mem_ball,dist_zero_right] using hp.2)
  have hd1 : |p.1.fst-p.2.fst| ≤ ‖p.1-p.2‖ := WithLp.norm_fst_le ℝ (p.1-p.2)
  have hd2 : |p.1.snd-p.2.snd| ≤ ‖p.1-p.2‖ := WithLp.norm_snd_le ℝ (p.1-p.2)
  simp only [ContinuousLinearMap.zero_apply,sub_zero,Real.norm_eq_abs]
  have he : additionCounterPerturbation p.1-additionCounterPerturbation p.2 =
      -p.1.fst*(|p.1.snd|-|p.2.snd|)-(p.1.fst-p.2.fst)*|p.2.snd| := by
    dsimp [additionCounterPerturbation]; ring
  rw [he]
  calc
    _ ≤ abs (-p.1.fst*(|p.1.snd|-|p.2.snd|))+abs ((p.1.fst-p.2.fst)*|p.2.snd|) := abs_sub _ _
    _ = |p.1.fst| * abs (|p.1.snd|-|p.2.snd|)+|p.1.fst-p.2.fst| * |p.2.snd| := by simp only [abs_mul,abs_neg,abs_abs]
    _ ≤ |p.1.fst| * ‖p.1-p.2‖+‖p.1-p.2‖*|p.2.snd| := add_le_add
      (mul_le_mul_of_nonneg_left ((abs_abs_sub_abs_le ..).trans hd2) (abs_nonneg _))
      (mul_le_mul_of_nonneg_right hd1 (abs_nonneg _))
    _ ≤ (ε/2)*‖p.1-p.2‖+‖p.1-p.2‖*(ε/2) := add_le_add
      (mul_le_mul_of_nonneg_right ha.le (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hb.le (norm_nonneg _))
    _ = ε*‖p.1-p.2‖ := by ring

private theorem height_mem_closure (x : AdditionCounterPlane) :
    WithLp.toLp 2 (x,height x) ∈ closure (euclideanSvGraph altered) := by
  let t : ℕ → ℝ := fun n ↦ 1/((n:ℝ)+1)
  have ht : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hl : Tendsto (fun n ↦ WithLp.toLp 2 (x,height x+t n)) atTop
      (𝓝 (WithLp.toLp 2 (x,height x))) := by
    simpa only [add_zero] using (WithLp.prod_continuous_toLp 2 AdditionCounterPlane ℝ).tendsto
      (x,height x+0) |>.comp (tendsto_const_nhds.prodMk_nhds (tendsto_const_nhds.add ht))
  apply mem_closure_of_tendsto hl
  exact Eventually.of_forall fun n ↦ Or.inl (by change height x < height x+t n; apply lt_add_of_pos_right; dsimp [t]; positivity)

private theorem inner_nonpos_of_closure_ray {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {C : Set V} {x v w : V} (hv : v ∈ regularNormalCone C x)
    (hr : ∀ t : ℝ, 0<t → x+t • w ∈ closure C) : ⟪v,w⟫_ℝ ≤ 0 := by
  apply inner_nonpos_of_mem_regularNormalCone (regularNormalCone_subset_closure C x hv)
  let t : ℕ → ℝ := fun n ↦ 1/((n:ℝ)+1)
  have ht (n : ℕ) : 0<t n := by dsimp [t]; positivity
  apply mem_tangentCone_of_forall (xs := fun n ↦ x+t n • w) (fun n ↦ hr (t n) (ht n)) ht
    tendsto_one_div_add_atTop_nhds_zero_nat
  simpa only [add_sub_cancel_left,inv_smul_smul₀ (ht _).ne'] using (tendsto_const_nhds (x := w))

private theorem altered_regular_vertical_zero {p v : Space}
    (hv : v ∈ regularNormalCone (euclideanSvGraph altered) p) : v.snd = 0 := by
  rcases hv.1 with hp | ⟨ha,hb,hc⟩
  · have ho : IsOpen {q : Space | height q.fst < q.snd} :=
      isOpen_lt (continuous_height.comp (WithLp.continuous_fst 2 AdditionCounterPlane ℝ))
        (WithLp.continuous_snd 2 AdditionCounterPlane ℝ)
    have hi : p ∈ interior (euclideanSvGraph altered) := interior_maximal (fun q hq ↦ Or.inl hq) ho hp
    have hz : v=0 := by simpa only [regularNormalCone_eq_singleton_of_mem_interior hi,mem_singleton_iff] using hv
    simp only [hz,WithLp.zero_snd]
  · have hbase : p = pt p.fst.fst 0 (-p.fst.fst) := by
      apply WithLp.ofLp_injective
      apply Prod.ext
      · apply WithLp.ofLp_injective
        exact Prod.ext rfl hb
      · dsimp [height] at hc
        simpa only [hb,abs_zero,mul_zero,sub_zero,abs_of_nonneg ha] using hc
    let a := p.fst.fst
    have hvertical := inner_nonpos_of_closure_ray hv (w := pt 0 0 1) (by
      intro t ht
      apply subset_closure
      left
      rw [hbase]
      change -|a+t*0|-(a+t*0)*|0+t*0| < -a+t*1
      simp only [mul_zero,add_zero,mul_one,abs_zero,sub_zero,abs_of_nonneg (show 0 ≤ a from ha)]
      linarith)
    have hvle : v.snd ≤ 0 := by simpa [pt,WithLp.prod_inner_apply] using hvertical
    by_cases hapos : 0<a
    · have hright := inner_nonpos_of_closure_ray hv (w := pt 0 1 (-a)) (by
        intro t ht
        rw [hbase]
        convert height_mem_closure (WithLp.toLp 2 (a,t)) using 1
        apply WithLp.ofLp_injective
        apply Prod.ext
        · change WithLp.toLp 2 (a+t*0,0+t*1) = WithLp.toLp 2 (a,t)
          simp
        · change -a+t*(-a) = -|a|-a*|t|
          rw [abs_of_pos hapos,abs_of_pos ht]
          ring)
      have hleft := inner_nonpos_of_closure_ray hv (w := pt 0 (-1) (-a)) (by
        intro t ht
        rw [hbase]
        convert height_mem_closure (WithLp.toLp 2 (a,-t)) using 1
        apply WithLp.ofLp_injective
        apply Prod.ext
        · change WithLp.toLp 2 (a+t*0,0+t*(-1)) = WithLp.toLp 2 (a,-t)
          congr 1 <;> simp
        · change -a+t*(-a) = -|a|-a*|-t|
          rw [abs_of_pos hapos,abs_neg,abs_of_pos ht]
          ring)
      have hr : v.fst.snd-a*v.snd ≤ 0 := by simpa [pt,WithLp.prod_inner_apply] using hright
      have hl : -v.fst.snd-a*v.snd ≤ 0 := by simpa [pt,WithLp.prod_inner_apply] using hleft
      apply le_antisymm hvle
      by_contra! hneg
      have hprod := mul_neg_of_pos_of_neg hapos hneg
      linarith
    · have ha0 : a=0 := le_antisymm (le_of_not_gt hapos) ha
      have hp0 : p=0 := by
        have hpa : p.fst.fst=0 := ha0
        simpa only [hpa,neg_zero,pt] using hbase
      have hr := inner_nonpos_of_closure_ray hv (w := pt 1 0 (-1)) (by
        intro t ht
        rw [hp0,zero_add]
        convert height_mem_closure (WithLp.toLp 2 (t,0)) using 1
        apply WithLp.ofLp_injective
        apply Prod.ext
        · change WithLp.toLp 2 (t*1,t*0) = WithLp.toLp 2 (t,0)
          simp
        · change t*(-1) = -|t|-t*|0|
          rw [abs_of_pos ht,abs_zero,mul_zero,sub_zero]; ring)
      have hl := inner_nonpos_of_closure_ray hv (w := pt (-1) 0 (-1)) (by
        intro t ht
        rw [hp0,zero_add]
        convert height_mem_closure (WithLp.toLp 2 (-t,0)) using 1
        apply WithLp.ofLp_injective
        apply Prod.ext
        · change WithLp.toLp 2 (t*(-1),t*0) = WithLp.toLp 2 (-t,0)
          simp
        · change t*(-1) = -|-t|-(-t)*|0|
          rw [abs_neg,abs_of_pos ht,abs_zero,mul_zero,sub_zero]; ring)
      have hr' : v.fst.fst-v.snd ≤ 0 := by simpa [pt,WithLp.prod_inner_apply] using hr
      have hl' : -v.fst.fst-v.snd ≤ 0 := by simpa [pt,WithLp.prod_inner_apply] using hl
      linarith

private theorem original_endpoint_normal {a : ℝ} (ha : 0<a) :
    pt (-1) 0 (-1) ∈ regularNormalCone (euclideanSvGraph additionCounterMapping) (pt a 0 (-a)) := by
  refine ⟨Or.inr ⟨ha.le,rfl,by simp [pt,abs_of_pos ha]⟩,fun ε hε ↦ ?_⟩
  have hpos : ∀ᶠ q : Space in 𝓝 (pt a 0 (-a)), 0<q.fst.fst :=
    (((WithLp.continuous_fst 2 ℝ ℝ).comp (WithLp.continuous_fst 2 AdditionCounterPlane ℝ)).continuousAt.eventually
      (Ioi_mem_nhds ha))
  filter_upwards [self_mem_nhdsWithin,hpos.filter_mono nhdsWithin_le_nhds] with q hq hqa
  have hheight : -q.fst.fst ≤ q.snd := by
    rcases hq with hq | ⟨_,_,hq⟩
    · simpa only [abs_of_pos hqa] using hq.le
    · simpa only [abs_of_pos hqa] using hq.ge
  apply le_trans _ (mul_nonneg hε.le (norm_nonneg _))
  simp only [pt,WithLp.prod_inner_apply,WithLp.ofLp_sub,
    Prod.fst_sub,Prod.snd_sub]
  change (q.fst.fst-a)*(-1)+(q.fst.snd-0)*0+(q.snd-(-a))*(-1) ≤ 0
  linarith

private theorem original_limiting_normal :
    pt (-1) 0 (-1) ∈ normalCone (euclideanSvGraph additionCounterMapping) 0 := by
  let t : ℕ → ℝ := fun n ↦ 1/((n:ℝ)+1)
  have ht (n : ℕ) : 0<t n := by dsimp [t]; positivity
  have ht0 : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hpt : Tendsto (fun n ↦ pt (t n) 0 (-t n)) atTop (𝓝 (0:Space)) := by
    have hinner : Tendsto (fun n ↦ WithLp.toLp 2 (t n,(0:ℝ))) atTop (𝓝 (0:AdditionCounterPlane)) := by
      simpa using (WithLp.prod_continuous_toLp 2 ℝ ℝ).tendsto ((0:ℝ),0) |>.comp (ht0.prodMk_nhds tendsto_const_nhds)
    simpa [pt] using (WithLp.prod_continuous_toLp 2 AdditionCounterPlane ℝ).tendsto ((0:AdditionCounterPlane),0) |>.comp
      (hinner.prodMk_nhds (by simpa only [neg_zero] using ht0.neg))
  exact mem_normalCone_of_forall (Or.inr ⟨le_rfl,rfl,by simp⟩) hpt
    (fun n ↦ original_endpoint_normal (ht n)) tendsto_const_nhds

private theorem altered_limiting_vertical_zero {v : Space}
    (hv : v ∈ normalCone (euclideanSvGraph altered) 0) : v.snd=0 := by
  obtain ⟨_,ps,vs,_,_,hvs,hlim⟩ := hv
  have he (n : ℕ) : (vs n).snd=0 := altered_regular_vertical_zero (hvs n)
  exact tendsto_nhds_unique (((WithLp.continuous_snd 2 AdditionCounterPlane ℝ).tendsto v).comp hlim)
    (by simpa only [Function.comp_def,he] using (tendsto_const_nhds (x := (0:ℝ))))

/-- The coderivative assertion of 10.43 is false for arbitrary graphs,
even when the perturbation has strict derivative zero at the base point. -/
theorem coderivative_addition_without_closed_graph_counterexample :
    (0:ℝ) ∈ additionCounterMapping 0 ∧
    HasStrictFDerivAt additionCounterPerturbation (0 : AdditionCounterPlane →L[ℝ] ℝ) 0 ∧
    WithLp.toLp 2 ((-1:ℝ),0) ∈ coderivative additionCounterMapping 0 0 1 ∧
    WithLp.toLp 2 ((-1:ℝ),0) ∉
      coderivative (svAdd additionCounterMapping (svSingleton additionCounterPerturbation)) 0
        (0+additionCounterPerturbation 0) 1 := by
  refine ⟨Or.inr ⟨le_rfl,rfl,by simp⟩,additionCounterPerturbation_hasStrictFDerivAt,?_,?_⟩
  · exact original_limiting_normal
  · intro hv
    have hval : 0+additionCounterPerturbation 0 = 0 := by simp [additionCounterPerturbation]
    rw [hval,← altered_eq] at hv
    have hh := altered_limiting_vertical_zero hv
    norm_num at hh

end RW
