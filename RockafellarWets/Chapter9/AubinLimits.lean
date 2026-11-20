/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Stability of an exact Aubin constant under graphical outer limits
-/

import RockafellarWets.Chapter9.MordukhovichCriterion
import RockafellarWets.Chapter8.CoderivativeApproximation

open Filter Metric Set Topology
open scoped NNReal InnerProductSpace

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {S : E → Set F} {x : E} {u : F} {k : ℝ≥0}

private theorem strict_failure_larger_constant (hS : IsClosed (svGraph S)) {a b : E} {v : F}
    (hv : v ∈ S a) (hfail : ∀ z ∈ S b, (k:ℝ)*dist a b < dist v z) :
    ∃ l : ℝ≥0, k < l ∧ l ≤ k+1 ∧ ∀ z ∈ S b, (l:ℝ)*dist a b < dist v z := by
  have hd : 0 < dist a b := dist_pos.mpr fun he ↦ by
    have h := hfail v (he ▸ hv)
    simpa only [he,dist_self,mul_zero,lt_self_iff_false] using h
  by_cases hne : (S b).Nonempty
  · have hclosed : IsClosed (S b) := hS.preimage (continuous_const.prodMk continuous_id)
    obtain ⟨z,hz,he⟩ := hclosed.exists_infDist_eq_dist hne v
    have hlt : (k:ℝ) < min ((k:ℝ)+1) (infDist v (S b)/dist a b) := by
      apply lt_min (by linarith)
      rw [lt_div_iff₀ hd,he]
      exact hfail z hz
    obtain ⟨l,hkl,hl⟩ := exists_between hlt
    refine ⟨⟨l,k.coe_nonneg.trans hkl.le⟩,hkl,(lt_min_iff.mp hl).1.le,fun z hz ↦ ?_⟩
    exact ((lt_div_iff₀ hd).mp (lt_min_iff.mp hl).2).trans_le (infDist_le_dist_of_mem hz)
  · exact ⟨k+1,by simp,le_rfl,fun z hz ↦ (hne ⟨z,hz⟩).elim⟩

/-- A normal bound throughout a fixed neighborhood gives an attained Aubin
constant. Uniformity of the neighborhood is essential at the endpoint. -/
theorem aubinEstimate_of_eventually_graphNormalBound (hS : IsClosed (svGraph S)) (hu : u ∈ S x)
    (hnear : ∀ᶠ p : WithLp 2 (E × F) in 𝓝 (WithLp.toLp 2 (x,u)),
      GraphNormalBound S p.fst p.snd k) : AubinEstimate S univ x u k := by
  let L := WithLp.prodContinuousLinearEquiv 2 ℝ E F
  let C := euclideanSvGraph S
  let p₀ := WithLp.toLp 2 (x,u)
  let U := closedBall p₀ 1
  have hU : U ∈ 𝓝 p₀ := closedBall_mem_nhds _ zero_lt_one
  have hcomp : IsCompact (C ∩ U) := (isCompact_closedBall _ _).inter_left
    (hS.preimage L.continuous)
  have hnon : (C ∩ U).Nonempty := ⟨p₀,hu,mem_of_mem_nhds hU⟩
  let good (p : (E × E) × F) := p.2 ∈ S p.1.1 →
    ∃ z ∈ S p.1.2, dist p.2 z ≤ k*dist p.1.1 p.1.2
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
  have hfail (n : ℕ) : v n ∈ S (a n) ∧ ∀ z ∈ S (b n), (k:ℝ)*dist (a n) (b n) < dist (v n) z := by
    simpa only [good,Classical.not_imp,not_exists,not_and,not_le,a,b,v] using hbad n
  choose l hkl hlmax hlfail using fun n ↦ strict_failure_larger_constant hS (hfail n).1 (hfail n).2
  let c n : ℝ := ((k:ℝ)+l n)/2
  have hkc (n : ℕ) : (k:ℝ) < c n := by dsimp [c]; linarith [show (k:ℝ) < l n from hkl n]
  have hcl (n : ℕ) : c n < l n := by dsimp [c]; linarith [show (k:ℝ) < l n from hkl n]
  have hc (n : ℕ) : 0 < c n := k.coe_nonneg.trans_lt (hkc n)
  let R n := (l n:ℝ)*dist (a n) (b n)
  let d n := ((l n:ℝ)-c n)*dist (a n) (b n)
  have hd (n : ℕ) : 0 < d n := by
    apply mul_pos (sub_pos.mpr (hcl n)) (dist_pos.mpr ?_)
    intro he
    have hh := (hfail n).2 (v n) (he ▸ (hfail n).1)
    simp [he] at hh
  have hR : Tendsto R atTop (𝓝 0) := by
    apply squeeze_zero (fun n ↦ mul_nonneg (l n).coe_nonneg dist_nonneg)
      (fun n ↦ mul_le_mul_of_nonneg_right (show (l n:ℝ) ≤ (k:ℝ)+1 from hlmax n) dist_nonneg)
    simpa only [dist_self,mul_zero] using (tendsto_const_nhds (x := (k:ℝ)+1)).mul (ha.dist hb)
  choose p hp hm using fun n ↦ hcomp.exists_isMinOn hnon
    (continuous_aubinPenalty (b n) (v n) (c n) (d n)).continuousOn
  have hsrc : Tendsto (fun n ↦ WithLp.toLp 2 (a n,v n)) atTop (𝓝 p₀) :=
    (L.symm.continuous.tendsto _).comp (ha.prodMk_nhds hv)
  have hbounds : ∀ᶠ n in atTop, dist (p n).fst (b n) ≤ 2*dist (a n) (b n) ∧ dist (p n).snd (v n) ≤ R n := by
    filter_upwards [hsrc.eventually hU] with n hn
    have hpen : aubinPenalty (b n) (v n) (c n) (d n) (p n) ≤ R n := by
      apply (hm n (show WithLp.toLp 2 (a n,v n) ∈ C ∩ U from ⟨(hfail n).1,hn⟩)).trans
      simp only [aubinPenalty,WithLp.toLp_fst,WithLp.toLp_snd,sub_self,norm_zero,
        ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,zero_add,Real.sqrt_sq (hd n).le]
      change c n * ‖a n-b n‖ + ((l n:ℝ)-c n)*dist (a n) (b n) ≤ (l n:ℝ)*dist (a n) (b n)
      rw [dist_eq_norm]
      linarith
    obtain ⟨h₁,h₂⟩ := aubinPenalty_bounds (hc n) hpen
    refine ⟨h₁.trans ?_,h₂⟩
    rw [div_le_iff₀ (hc n)]
    dsimp [R,c]
    nlinarith [mul_nonneg k.coe_nonneg (dist_nonneg (x := a n) (y := b n))]
  have hp₁ : Tendsto (fun n ↦ (p n).fst) atTop (𝓝 x) := by
    apply tendsto_of_tendsto_of_dist hb
    exact squeeze_zero' (.of_forall fun _ ↦ dist_nonneg)
      (hbounds.mono fun n h ↦ (dist_comm (p n).fst (b n)) ▸ h.1)
      (by simpa only [dist_self,mul_zero] using (tendsto_const_nhds (x := (2:ℝ))).mul (ha.dist hb))
  have hp₂ : Tendsto (fun n ↦ (p n).snd) atTop (𝓝 u) := by
    apply tendsto_of_tendsto_of_dist hv
    exact squeeze_zero' (.of_forall fun _ ↦ dist_nonneg)
      (hbounds.mono fun n h ↦ (dist_comm (p n).snd (v n)) ▸ h.2) hR
  have hp₀ : Tendsto p atTop (𝓝 p₀) := (L.symm.continuous.tendsto _).comp (hp₁.prodMk_nhds hp₂)
  obtain ⟨n,hn,hUn,hbn⟩ := ((hp₀.eventually hnear).and
    ((hp₀.eventually (isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hU))).and hbounds)).exists
  have hne : (p n).fst ≠ b n := by
    intro he
    exact (hlfail n _ (he ▸ (hp n).1)).not_ge ((dist_comm (p n).snd (v n)) ▸ hbn.2)
  have hmin : IsLocalMinOn (aubinPenalty (b n) (v n) (c n) (d n)) C (p n) := by
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hUn)]
      with t ht htU using hm n ⟨ht,htU⟩
  obtain ⟨g,hg,hgf,hgs⟩ := aubinPenalty_gradient (b n) (v n) (hc n).le (hd n) (p n) hne
  have hgN := regularNormalCone_subset_normalCone C (p n)
    (IsLocalMinOn.neg_gradient_mem_regularNormalCone (hp n).1 hmin hg)
  have hcontra := hn (-g) hgN
  change ‖-g.fst‖ ≤ (k:ℝ)*‖-g.snd‖ at hcontra
  simp only [norm_neg,hgf] at hcontra
  exact (hkc n).not_ge (hcontra.trans (mul_le_of_le_one_right k.coe_nonneg hgs))

/-- Coderivative recovery transfers a common local Aubin constant to the
normal bound at the graphical outer limit. -/
theorem graphNormalBound_graphicalOuterLimit {T : ℕ → E → Set F}
    (hosc : ∀ n, SvOsc (T n)) (hlim : graphicalOuterLimit T = S)
    {V : Set E} {W : Set F} (hV : V ∈ 𝓝 x) (hW : W ∈ 𝓝 u)
    (hA : ∀ n, ∀ a ∈ V, ∀ b ∈ W, b ∈ T n a → AubinEstimate (T n) univ a b k) :
    GraphNormalBound S x u k := by
  apply graphNormalBound_iff_coderivative.mpr
  intro y z hz
  obtain ⟨φ,hφ,p,v,hp,hv,hm⟩ := exists_subsequence_coderivativeRecovery hosc hlim hz
  apply le_of_tendsto_of_tendsto (((continuous_snd.tendsto _).comp hv).norm)
    ((tendsto_const_nhds (x := (k:ℝ))).mul ((continuous_fst.tendsto _).comp hv).norm)
  filter_upwards [hm,hp.eventually (prod_mem_nhds hV hW)] with n hn hpn
  exact graphNormalBound_iff_coderivative.mp
    (hA (φ n) _ hpn.1 _ hpn.2 hn.1).graphNormalBound _ _ hn.2.2

/-- **Proposition 9.59(c).** The graphical outer limit inherits the same
attained Aubin constant, including the endpoint constant zero. -/
theorem aubinEstimate_graphicalOuterLimit {T : ℕ → E → Set F}
    (hosc : ∀ n, SvOsc (T n)) (hlim : graphicalOuterLimit T = S) (hu : u ∈ S x)
    {V : Set E} {W : Set F} (hV : V ∈ 𝓝 x) (hW : W ∈ 𝓝 u)
    (hA : ∀ n, ∀ a ∈ V, ∀ b ∈ W, b ∈ T n a → AubinEstimate (T n) univ a b k) :
    AubinEstimate S univ x u k := by
  have hS : IsClosed (svGraph S) := by
    rw [← hlim,svGraph_graphicalOuterLimit]
    exact isClosed_outerSetLimit _
  apply aubinEstimate_of_eventually_graphNormalBound hS hu
  have hp : interior V ×ˢ interior W ∈ 𝓝 (x,u) := prod_mem_nhds
    (isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hV))
    (isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hW))
  filter_upwards [((WithLp.homeomorphProd 2 E F).continuous.tendsto (WithLp.toLp 2 (x,u))).eventually hp] with p hpn
  exact graphNormalBound_graphicalOuterLimit hosc hlim (mem_interior_iff_mem_nhds.mp hpn.1)
    (mem_interior_iff_mem_nhds.mp hpn.2) hA

theorem hasAubinProperty_graphicalOuterLimit {T : ℕ → E → Set F}
    (hosc : ∀ n, SvOsc (T n)) (hlim : graphicalOuterLimit T = S) (hu : u ∈ S x)
    {V : Set E} {W : Set F} (hV : V ∈ 𝓝 x) (hW : W ∈ 𝓝 u)
    (hA : ∀ n, ∀ a ∈ V, ∀ b ∈ W, b ∈ T n a → AubinEstimate (T n) univ a b k) :
    HasAubinPropertyAt S x u := by
  have hS : IsClosed (svGraph S) := by
    rw [← hlim,svGraph_graphicalOuterLimit]
    exact isClosed_outerSetLimit _
  exact ⟨mem_univ x,hu,RW.IsClosed.isLocallyClosedAt hS _,k,
    aubinEstimate_graphicalOuterLimit hosc hlim hu hV hW hA⟩

end RW
