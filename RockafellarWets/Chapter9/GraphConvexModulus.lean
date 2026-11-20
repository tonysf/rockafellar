/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The quantitative graph-convex strict-continuity bound
-/

import RockafellarWets.Chapter9.GraphConvexStrictContinuity

open Filter Metric Set Topology
open scoped NNReal ENNReal

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {S : E → Set F} {x : E}

/-- Uniform local transport bounds the truncated-inclusion modulus directly,
without requiring nearest points or nonempty fibers outside the neighborhood. -/
theorem RhoTransport.svRhoHatModulus_le {r k : ℝ≥0} {U : Set E}
    (h : RhoTransport k r S U) (hU : U ∈ 𝓝 x) :
    svRhoHatLipschitzModulus S r x ≤ (k : ℝ≥0∞) := by
  apply localPairModulusWithin_le (by simpa only [nhdsWithin_univ] using hU)
  intro a ha b hb
  rw [edist_dist,← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul (p := (k:ℝ)) (q := dist a b) k.2]
  apply (rhoHatEDistance_le_iff r (S a) (S b)).mpr
  constructor
  · intro v hv
    obtain ⟨z,hz,hd⟩ := h a ha b hb v hv
    exact mem_cthickening_iff.mpr ((infEDist_le_edist_of_mem hz).trans (by
      rw [edist_dist]; exact ENNReal.ofReal_le_ofReal hd))
  · intro v hv
    obtain ⟨z,hz,hd⟩ := h b hb a ha v hv
    exact mem_cthickening_iff.mpr ((infEDist_le_edist_of_mem hz).trans (by
      rw [edist_dist]; exact ENNReal.ofReal_le_ofReal (by simpa only [dist_comm b a] using hd)))

/-- Any distance strictly below the distance to the bad fibers gives a
local transport constant. -/
theorem SvGraphConvex.local_truncation_modulus_le (h : SvGraphConvex S)
    {R : ℝ≥0∞} {r d : ℝ≥0} (hR : R ≤ r) (hd : 0 < d)
    (hD : (d:ℝ≥0∞) < svBadFiberDistance S {x} R) :
    svRhoHatLipschitzModulus S r x ≤ ENNReal.ofReal (2*(r:ℝ)/(d:ℝ)) := by
  obtain ⟨e,hde,he⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hD
  have hde' : (d:ℝ) < e := by exact_mod_cast ENNReal.coe_lt_coe.mp hde
  let δ := (e:ℝ)-(d:ℝ)
  have hδ : 0 < δ := sub_pos.mpr hde'
  let U := ball x δ
  have hU : U ∈ 𝓝 x := ball_mem_nhds _ hδ
  have hcover {b : E} (hb : b ∈ U) (c : E) (hc : c ∈ closedBall b (d:ℝ)) :
      (S c ∩ closedBall (0:F) (r:ℝ)).Nonempty := by
    have hcx : dist c x < (e:ℝ) := (dist_triangle c b x).trans_lt (by
      have hb' : dist b x < δ := hb
      have hc' : dist c b ≤ d := hc
      dsimp [δ] at hb'
      linarith)
    have hce : edist c x < (e:ℝ≥0∞) := by
      rw [edist_dist,← ENNReal.ofReal_coe_nnreal]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mpr hcx
    have hinf : infEDist 0 (S c) < (r:ℝ≥0∞) := by
      by_contra! hn
      have hbad := iInf_le (fun w : {z | R ≤ infEDist 0 (S z)} ↦ infEDist (w:E) {x}) ⟨c,hR.trans hn⟩
      exact (hce.trans he).not_ge (hbad.trans (infEDist_le_edist_of_mem (mem_singleton x)))
    obtain ⟨v,hv,hvr⟩ := infEDist_lt_iff.mp hinf
    rw [edist_nndist,ENNReal.coe_lt_coe] at hvr
    exact ⟨v,hv,mem_closedBall_zero_iff.mpr (by
      have hvn : ‖v‖₊ ≤ r := by simpa using hvr.le
      exact_mod_cast hvn)⟩
  let k : ℝ≥0 := ⟨2*(r:ℝ)/(d:ℝ),by positivity⟩
  have ht : RhoTransport k r S U := by
    intro a ha b hb v hv
    obtain ⟨w,hw,hwd⟩ := h.truncation_transport_step (by exact_mod_cast hd) (hcover hb) hv
    refine ⟨w,hw.1,hwd.trans ?_⟩
    calc
      _ ≤ (2*(r:ℝ)*dist b a)/(d:ℝ) := div_le_div_of_nonneg_left (by positivity)
        (by exact_mod_cast hd) (le_add_of_nonneg_right dist_nonneg)
      _ = (k:ℝ)*dist a b := by dsimp [k]; rw [dist_comm b a]; ring
  change svRhoHatLipschitzModulus S r x ≤ ENNReal.ofReal (k:ℝ)
  rw [ENNReal.ofReal_coe_nnreal]
  exact ht.svRhoHatModulus_le hU

/-- **Corollary 9.34**, the exact modulus bound. Extended division includes
an empty bad-fiber set, whose infinite distance gives bound zero. -/
theorem SvGraphConvex.svRhoHatModulus_le_badFiberDistance (h : SvGraphConvex S)
    {R : ℝ≥0∞} {r : ℝ≥0} (hR : R ≤ r) (hD : 0 < svBadFiberDistance S {x} R) :
    svRhoHatLipschitzModulus S r x ≤ ENNReal.ofReal (2*(r:ℝ)) / svBadFiberDistance S {x} R := by
  by_contra! hn
  obtain ⟨k,hlo,hhi⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hn
  have hk : (k:ℝ≥0∞) ≠ 0 := ne_of_gt ((zero_le _).trans_lt hlo)
  have hmul : ENNReal.ofReal (2*(r:ℝ)) < (k:ℝ≥0∞)*svBadFiberDistance S {x} R :=
    (ENNReal.div_lt_iff (.inl hD.ne') (.inr ENNReal.ofReal_ne_top)).mp hlo
  have hdiv := ENNReal.div_lt_of_lt_mul' hmul
  obtain ⟨d,hld,hdd⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hdiv
  have hd : 0 < d := ENNReal.coe_pos.mp ((zero_le _).trans_lt hld)
  have hmul' : ENNReal.ofReal (2*(r:ℝ)) < (d:ℝ≥0∞)*(k:ℝ≥0∞) :=
    (ENNReal.div_lt_iff (.inl hk) (.inl ENNReal.coe_ne_top)).mp hld
  have hfin := h.local_truncation_modulus_le hR hd hdd
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hd),ENNReal.ofReal_coe_nnreal] at hfin
  exact hhi.not_ge (hfin.trans (ENNReal.div_lt_of_lt_mul' hmul').le)

/-- **Corollary 9.34**, with the book's bad-fiber threshold
`d(0,S(x)) + 1`. The radius may equal that threshold. -/
theorem SvGraphConvex.svRhoHatModulus_le_at_interior (h : SvGraphConvex S)
    (hx : x ∈ interior (svDom S)) {r : ℝ≥0}
    (hr : infEDist 0 (S x) + 1 ≤ (r:ℝ≥0∞)) :
    svRhoHatLipschitzModulus S r x ≤ ENNReal.ofReal (2*(r:ℝ)) /
      svBadFiberDistance S {x} (infEDist 0 (S x)+1) := by
  apply h.svRhoHatModulus_le_badFiberDistance hr
  apply h.svBadFiberDistance_pos isCompact_singleton (singleton_subset_iff.mpr hx)
  have hzero : svZeroRadius S {x} = infEDist 0 (S x) := by simp [svZeroRadius]
  rw [hzero]
  exact ENNReal.lt_add_right (infEDist_ne_top (show x ∈ svDom S from interior_subset hx)) one_ne_zero

end RW
