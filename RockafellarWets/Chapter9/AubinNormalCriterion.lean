/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: Sufficiency of the normal bound for the Aubin property
-/

import RockafellarWets.Chapter9.AubinNormalBounds
import RockafellarWets.Chapter6.Optimality
import Mathlib.Analysis.InnerProductSpace.Calculus

open Filter Metric Set Topology
open scoped InnerProductSpace NNReal ENNReal

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {S : E → Set F} {x : E} {u : F} {k l : ℝ≥0}

local notation "P" => WithLp 2 (E × F)

/-- The penalty whose smoothed output distance has gradient of norm at most one.
Its nonsmooth input distance has gradient of norm exactly the penalty weight
whenever the input differs from the target. -/
noncomputable def aubinPenalty (a : E) (v : F) (c d : ℝ) (p : P) : ℝ :=
  c * ‖p.fst-a‖ + Real.sqrt (‖p.snd-v‖^2+d^2)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] in
theorem continuous_aubinPenalty (a : E) (v : F) (c d : ℝ) :
    Continuous (aubinPenalty a v c d) :=
  (continuous_const.mul (((WithLp.continuous_fst 2 E F).sub continuous_const).norm)).add
    (((((WithLp.continuous_snd 2 E F).sub continuous_const).norm).pow 2).add continuous_const).sqrt

theorem aubinPenalty_gradient (a : E) (v : F) {c d : ℝ} (hc : 0 ≤ c) (hd : 0 < d)
    (p : P) (hp : p.fst ≠ a) : ∃ g : P, HasGradientAt (aubinPenalty a v c d) g p ∧
      ‖g.fst‖ = c ∧ ‖g.snd‖ ≤ 1 := by
  let A := p.fst-a
  let B := p.snd-v
  let r := Real.sqrt (‖B‖^2+d^2)
  have hA : 0 < ‖A‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hp)
  have hr : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hB : ‖B‖ ≤ r := by
    dsimp [r]
    rw [Real.le_sqrt (norm_nonneg _) (by positivity)]
    linarith [sq_nonneg d]
  let g := WithLp.toLp 2 ((c/‖A‖) • A,r⁻¹ • B)
  refine ⟨g,?_,?_,?_⟩
  · have H₁ := ((((WithLp.fstL 2 ℝ E F).hasFDerivAt (x := p)).sub_const a).norm_sq.sqrt
      (show ‖p.fst-a‖^2 ≠ 0 from pow_ne_zero _ hA.ne'))
    have H₂ := (((((WithLp.sndL 2 ℝ E F).hasFDerivAt (x := p)).sub_const v).norm_sq.add_const (d^2)).sqrt
      (show ‖p.snd-v‖^2+d^2 ≠ 0 by positivity))
    apply hasGradientAt_iff_hasFDerivAt.mpr
    convert (H₁.const_mul c).add H₂ using 1
    · ext q
      simp [aubinPenalty]
    · ext w
      change ⟪g,w⟫_ℝ = _
      simp [g,A,B,r,WithLp.prod_inner_apply,real_inner_smul_left,inner_sub_left,smul_eq_mul,
        ContinuousLinearMap.coe_comp',Function.comp_apply]
      field_simp
  · change ‖(c/‖A‖) • A‖ = c
    rw [norm_smul_of_nonneg (div_nonneg hc hA.le),div_mul_cancel₀ _ hA.ne']
  · change ‖r⁻¹ • B‖ ≤ 1
    rw [norm_smul_of_nonneg (inv_pos.mpr hr).le,← div_eq_inv_mul,div_le_one hr]
    exact hB

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] in
theorem aubinPenalty_bounds {a : E} {v : F} {c d R : ℝ} (hc : 0 < c) {p : P}
    (hp : aubinPenalty a v c d p ≤ R) : dist p.fst a ≤ R / c ∧ dist p.snd v ≤ R := by
  have h₁ : 0 ≤ c * ‖p.fst-a‖ := mul_nonneg hc.le (norm_nonneg _)
  have h₂ : ‖p.snd-v‖ ≤ Real.sqrt (‖p.snd-v‖^2+d^2) := by
    rw [Real.le_sqrt (norm_nonneg _) (by positivity)]
    linarith [sq_nonneg d]
  change c * ‖p.fst-a‖ + _ ≤ R at hp
  rw [dist_eq_norm,dist_eq_norm,le_div_iff₀ hc]
  constructor <;> linarith [Real.sqrt_nonneg (‖p.snd-v‖^2+d^2),mul_comm c ‖p.fst-a‖]

/-- Sufficiency in **Theorem 9.40**. A base-point normal bound gives an Aubin
estimate with every strictly larger constant. Minimization takes place on a
compact piece of the graph and eventually in the interior of its cutoff. -/
theorem GraphNormalBound.aubinEstimate_of_lt (h : GraphNormalBound S x u k)
    (hu : u ∈ S x) (hl : IsLocallyClosedAt (svGraph S) (x,u)) (hkl : k < l) :
    AubinEstimate S univ x u l := by
  obtain ⟨k',hk',hk'l⟩ := exists_between hkl
  obtain ⟨c,hc',hcl⟩ := exists_between hk'l
  have hc : 0 < (c:ℝ) := lt_of_le_of_lt k'.2 hc'
  let L := WithLp.prodContinuousLinearEquiv 2 ℝ E F
  let C := euclideanSvGraph S
  let p₀ := WithLp.toLp 2 (x,u)
  have hl' : IsLocallyClosedAt C p₀ := IsLocallyClosedAt.preimage_continuousLinearEquiv L hl
  obtain ⟨V,hV,_,hclosed⟩ := hl'
  let U := V ∩ closedBall p₀ 1
  have hU : U ∈ 𝓝 p₀ := inter_mem hV (closedBall_mem_nhds _ zero_lt_one)
  have hcomp : IsCompact (C ∩ U) := by
    rw [show C ∩ U = (C ∩ V) ∩ closedBall p₀ 1 by ext p; exact and_assoc.symm]
    exact (isCompact_closedBall _ _).inter_left hclosed
  have hnon : (C ∩ U).Nonempty := ⟨p₀,hu,mem_of_mem_nhds hU⟩
  let good (p : (E × E) × F) := p.2 ∈ S p.1.1 →
    ∃ z ∈ S p.1.2, dist p.2 z ≤ l * dist p.1.1 p.1.2
  suffices HG : ∀ᶠ p in 𝓝 ((x,x),u), good p by
    rw [nhds_prod_eq] at HG
    obtain ⟨T,hT,W,hW,hTW⟩ := mem_prod_iff.mp HG
    rw [nhds_prod_eq] at hT
    obtain ⟨V₁,hV₁,V₂,hV₂,hTV⟩ := mem_prod_iff.mp hT
    exact ⟨V₁ ∩ V₂,inter_mem hV₁ hV₂,W,hW,fun a ha b hb v hv ↦
      hTW (show ((a,b),v) ∈ T ×ˢ W from ⟨hTV ⟨ha.2.1,hb.2.2⟩,hv.2⟩) hv.1⟩
  by_contra HH
  obtain ⟨q,hq,hbad⟩ := exists_seq_forall_of_frequently (not_eventually.mp HH)
  let a n := (q n).1.1
  let b n := (q n).1.2
  let v n := (q n).2
  have ha : Tendsto a atTop (𝓝 x) := continuousAt_fst.tendsto.comp (continuousAt_fst.tendsto.comp hq)
  have hb : Tendsto b atTop (𝓝 x) := continuousAt_snd.tendsto.comp (continuousAt_fst.tendsto.comp hq)
  have hv : Tendsto v atTop (𝓝 u) := continuousAt_snd.tendsto.comp hq
  have hfail (n : ℕ) : v n ∈ S (a n) ∧ ∀ z ∈ S (b n), (l:ℝ)*dist (a n) (b n) < dist (v n) z := by
    simpa only [good,Classical.not_imp,not_exists,not_and,not_le,a,b,v] using hbad n
  let R n := (l:ℝ)*dist (a n) (b n)
  let d n := ((l:ℝ)-c)*dist (a n) (b n)
  have hd (n : ℕ) : 0 < d n := by
    apply mul_pos (sub_pos.mpr (show (c:ℝ) < l from hcl)) (dist_pos.mpr ?_)
    intro he
    have hh := (hfail n).2 (v n) (he ▸ (hfail n).1)
    simp [he] at hh
  have hR : Tendsto R atTop (𝓝 0) := by simpa [R] using (tendsto_const_nhds (x := (l:ℝ))).mul (ha.dist hb)
  choose p hp hm using fun n ↦ hcomp.exists_isMinOn hnon
    (continuous_aubinPenalty (b n) (v n) c (d n)).continuousOn
  have hsrc : Tendsto (fun n ↦ WithLp.toLp 2 (a n,v n)) atTop (𝓝 p₀) :=
    (L.symm.continuous.tendsto _).comp (ha.prodMk_nhds hv)
  have hbounds : ∀ᶠ n in atTop, dist (p n).fst (b n) ≤ R n / c ∧ dist (p n).snd (v n) ≤ R n := by
    filter_upwards [hsrc.eventually hU] with n hn
    apply aubinPenalty_bounds hc
    have hm' := hm n (show WithLp.toLp 2 (a n,v n) ∈ C ∩ U from ⟨(hfail n).1,hn⟩)
    apply hm'.trans
    simp only [aubinPenalty,WithLp.toLp_fst,WithLp.toLp_snd,sub_self,norm_zero,ne_eq,OfNat.ofNat_ne_zero,
      not_false_eq_true,zero_pow,zero_add,Real.sqrt_sq (hd n).le]
    change (c:ℝ)*‖a n-b n‖ + ((l:ℝ)-c)*dist (a n) (b n) ≤ (l:ℝ)*dist (a n) (b n)
    rw [dist_eq_norm]
    linarith
  have hp₁ : Tendsto (fun n ↦ (p n).fst) atTop (𝓝 x) := by
    apply tendsto_of_tendsto_of_dist hb
    exact squeeze_zero' (.of_forall fun _ ↦ dist_nonneg) (hbounds.mono fun n h ↦ (dist_comm (p n).fst (b n)) ▸ h.1)
      (by simpa only [zero_div] using hR.div_const (c:ℝ))
  have hp₂ : Tendsto (fun n ↦ (p n).snd) atTop (𝓝 u) := by
    apply tendsto_of_tendsto_of_dist hv
    exact squeeze_zero' (.of_forall fun _ ↦ dist_nonneg) (hbounds.mono fun n h ↦ (dist_comm (p n).snd (v n)) ▸ h.2) hR
  have hp₀ : Tendsto p atTop (𝓝 p₀) := (L.symm.continuous.tendsto _).comp (hp₁.prodMk_nhds hp₂)
  obtain ⟨n,hn,hUn,hbn⟩ := ((hp₀.eventually (h.eventually_of_lt hu hk')).and
    ((hp₀.eventually (isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hU))).and hbounds)).exists
  have hne : (p n).fst ≠ b n := by
    intro he
    exact ((hfail n).2 _ (he ▸ (hp n).1)).not_ge ((dist_comm (p n).snd (v n)) ▸ hbn.2)
  have hmin : IsLocalMinOn (aubinPenalty (b n) (v n) c (d n)) C (p n) := by
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hUn)]
      with t ht htU using hm n ⟨ht,htU⟩
  obtain ⟨g,hg,hgf,hgs⟩ := aubinPenalty_gradient (b n) (v n) hc.le (hd n) (p n) hne
  have hgN := regularNormalCone_subset_normalCone C (p n) (IsLocalMinOn.neg_gradient_mem_regularNormalCone (hp n).1 hmin hg)
  have hcontra := hn (-g) hgN
  change ‖-g.fst‖ ≤ (k':ℝ)*‖-g.snd‖ at hcontra
  simp only [norm_neg,hgf] at hcontra
  exact (show (k':ℝ) < c from hc').not_ge (hcontra.trans (mul_le_of_le_one_right k'.2 hgs))

end RW
