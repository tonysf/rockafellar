/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 10: Limiting subgradients of separable functions
-/

import RockafellarWets.Chapter10.SeparableRegularSubgradients
import RockafellarWets.Chapter8.HorizonSubgradientSequences

open Filter Set Topology

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {f : E → EReal} {g : F → EReal} {x : E} {y : F} {c d : ℝ}

theorem exists_coe_components_of_add_eq_coe {a b : EReal} {r : ℝ} (h : a+b = r) :
    ∃ s t : ℝ, a = s ∧ b = t := by
  cases a <;> cases b <;> simp_all

/-- Attentive convergence of a separable sum and lower semicontinuity
force attentive convergence in each coordinate. -/
theorem tendsto_separable_attentive_fst (hf : LowerSemicontinuousAt f x)
    (hg : LowerSemicontinuousAt g y) (hx : f x = c) (hy : g y = d) :
    Tendsto (fun q : WithLp 2 (E × F) ↦ q.fst)
      (attentiveNhds (separableSum f g) (WithLp.toLp 2 (x,y))) (attentiveNhds f x) := by
  let l := attentiveNhds (separableSum f g) (WithLp.toLp 2 (x,y))
  have hfst : Tendsto (fun q : WithLp 2 (E × F) ↦ q.fst) l (𝓝 x) :=
    ((WithLp.fstL 2 ℝ E F).continuous.tendsto _).mono_left inf_le_left
  have hsnd : Tendsto (fun q : WithLp 2 (E × F) ↦ q.snd) l (𝓝 y) :=
    ((WithLp.sndL 2 ℝ E F).continuous.tendsto _).mono_left inf_le_left
  have hsum : Tendsto (separableSum f g) l (𝓝 (((c+d:ℝ):EReal))) := by
    have hh := (tendsto_attentiveNhds_iff.mp (tendsto_id (x := l))).2
    simpa only [Function.comp_id,separableSum,WithLp.toLp_fst,WithLp.toLp_snd,hx,hy,EReal.coe_add] using hh
  apply tendsto_attentiveNhds_iff.mpr
  refine ⟨hfst,?_⟩
  rw [hx]
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact hfst.eventually (hf a (by simpa only [hx] using ha))
  · intro b hb
    obtain ⟨r,hr,hrb⟩ := EReal.exists_between_coe_real hb
    have hcr : c < r := EReal.coe_lt_coe_iff.mp hr
    let δ := (r-c)/2
    have hδ : 0 < δ := by dsimp [δ]; linarith
    have hlow := hsnd.eventually (hg ((d-δ:ℝ):EReal) (by simpa only [hy] using EReal.coe_lt_coe_iff.mpr (show d-δ < d by linarith)))
    have hupp := hsum.eventually (gt_mem_nhds (EReal.coe_lt_coe_iff.mpr (show c+d < c+d+δ by linarith)))
    filter_upwards [hlow,hupp] with q hqg hqs
    apply lt_trans ?_ hrb
    by_contra! hqr
    have hh := add_le_add hqr hqg.le
    rw [← EReal.coe_add] at hh
    have he : r+(d-δ) = c+d+δ := by dsimp [δ]; ring
    rw [he] at hh
    exact hqs.not_ge hh

theorem tendsto_separable_attentive_snd (hf : LowerSemicontinuousAt f x)
    (hg : LowerSemicontinuousAt g y) (hx : f x = c) (hy : g y = d) :
    Tendsto (fun q : WithLp 2 (E × F) ↦ q.snd)
      (attentiveNhds (separableSum f g) (WithLp.toLp 2 (x,y))) (attentiveNhds g y) := by
  let L := LinearIsometryEquiv.withLpProdComm 2 ℝ E F
  have hL : Tendsto L (attentiveNhds (separableSum f g) (WithLp.toLp 2 (x,y)))
      (attentiveNhds (separableSum g f) (WithLp.toLp 2 (y,x))) := by
    apply tendsto_attentiveNhds_iff.mpr
    refine ⟨L.continuous.continuousAt.mono_left inf_le_left,?_⟩
    have hh := (tendsto_attentiveNhds_iff.mp (tendsto_id (x := attentiveNhds (separableSum f g) (WithLp.toLp 2 (x,y))))).2
    simpa only [Function.comp_id,Function.comp_def,separableSum,L,LinearIsometryEquiv.withLpProdComm_apply,WithLp.toLp_fst,WithLp.toLp_snd,add_comm] using hh
  exact (tendsto_separable_attentive_fst hg hf hy hx).comp hL

theorem mem_regularSubdifferential_separableSum_finite {q v : WithLp 2 (E × F)}
    (hv : v ∈ regularSubdifferential (separableSum f g) q) :
    v.fst ∈ regularSubdifferential f q.fst ∧ v.snd ∈ regularSubdifferential g q.snd := by
  obtain ⟨r,hr,hreg⟩ := hv
  obtain ⟨a,b,ha,hb⟩ := exists_coe_components_of_add_eq_coe hr
  exact (mem_regularSubdifferential_separableSum_iff ha hb v).mp ⟨r,hr,hreg⟩

/-- **Proposition 10.5**, the binary limiting-subgradient product formula. -/
theorem mem_subdifferential_separableSum_iff (hf : LowerSemicontinuousAt f x)
    (hg : LowerSemicontinuousAt g y) (hx : f x = c) (hy : g y = d)
    (v : WithLp 2 (E × F)) :
    v ∈ subdifferential (separableSum f g) (WithLp.toLp 2 (x,y)) ↔
      v.fst ∈ subdifferential f x ∧ v.snd ∈ subdifferential g y := by
  have hxy : separableSum f g (WithLp.toLp 2 (x,y)) = ((c+d:ℝ):EReal) := by
    simp only [separableSum,WithLp.toLp_fst,WithLp.toLp_snd,hx,hy,EReal.coe_add]
  constructor
  · intro hv
    obtain ⟨_,q,z,hq,hqval,hz,hzlim⟩ := mem_subdifferential_iff_exists_seq.mp hv
    have hqa := tendsto_attentiveNhds_iff.mpr ⟨hq,hqval⟩
    have hqa1 := (tendsto_separable_attentive_fst hf hg hx hy).comp hqa
    have hqa2 := (tendsto_separable_attentive_snd hf hg hx hy).comp hqa
    constructor
    · exact mem_subdifferential_iff_exists_seq.mpr ⟨⟨c,hx⟩,fun n ↦ (q n).fst,fun n ↦ (z n).fst,
        (tendsto_attentiveNhds_iff.mp hqa1).1,(tendsto_attentiveNhds_iff.mp hqa1).2,
        fun n ↦ (mem_regularSubdifferential_separableSum_finite (hz n)).1,
        ((WithLp.fstL 2 ℝ E F).continuous.tendsto _).comp hzlim⟩
    · exact mem_subdifferential_iff_exists_seq.mpr ⟨⟨d,hy⟩,fun n ↦ (q n).snd,fun n ↦ (z n).snd,
        (tendsto_attentiveNhds_iff.mp hqa2).1,(tendsto_attentiveNhds_iff.mp hqa2).2,
        fun n ↦ (mem_regularSubdifferential_separableSum_finite (hz n)).2,
        ((WithLp.sndL 2 ℝ E F).continuous.tendsto _).comp hzlim⟩
  · rintro ⟨hv,hw⟩
    obtain ⟨_,a,u,ha,haval,hu,hulim⟩ := mem_subdifferential_iff_exists_seq.mp hv
    obtain ⟨_,b,z,hb,hbval,hz,hzlim⟩ := mem_subdifferential_iff_exists_seq.mp hw
    let L := WithLp.prodContinuousLinearEquiv 2 ℝ E F
    refine mem_subdifferential_iff_exists_seq.mpr ⟨⟨c+d,hxy⟩,
      fun n ↦ WithLp.toLp 2 (a n,b n),fun n ↦ WithLp.toLp 2 (u n,z n),
      (L.symm.continuous.tendsto _).comp (ha.prodMk_nhds hb),?_,?_,
      (L.symm.continuous.tendsto _).comp (hulim.prodMk_nhds hzlim)⟩
    · rw [hx] at haval
      rw [hy] at hbval
      have hh := Filter.Tendsto.comp (EReal.continuousAt_add_coe_coe c d) (haval.prodMk_nhds hbval)
      simpa only [Function.comp_def,separableSum,WithLp.toLp_fst,WithLp.toLp_snd,hx,hy,EReal.coe_add] using hh
    · intro n
      obtain ⟨cn,hcn,-⟩ := hu n
      obtain ⟨dn,hdn,-⟩ := hz n
      exact (mem_regularSubdifferential_separableSum_iff hcn hdn _).mpr ⟨hu n,hz n⟩

/-- **Proposition 10.5**, the binary horizon-subgradient inclusion. -/
theorem horizonSubdifferential_separableSum_subset (hf : LowerSemicontinuousAt f x)
    (hg : LowerSemicontinuousAt g y) (hx : f x = c) (hy : g y = d) :
    horizonSubdifferential (separableSum f g) (WithLp.toLp 2 (x,y)) ⊆
      {v | v.fst ∈ horizonSubdifferential f x ∧ v.snd ∈ horizonSubdifferential g y} := by
  have hxy : separableSum f g (WithLp.toLp 2 (x,y)) = ((c+d:ℝ):EReal) := by
    simp only [separableSum,WithLp.toLp_fst,WithLp.toLp_snd,hx,hy,EReal.coe_add]
  intro v hv
  rcases (mem_horizonSubdifferential_iff_zero_or_scaledSeq hxy).mp hv with rfl | ⟨q,z,t,hq,hz,ht,ht0,hlim⟩
  · exact ⟨(mem_horizonSubdifferential_iff_zero_or_scaledSeq hx).mpr (Or.inl rfl),
      (mem_horizonSubdifferential_iff_zero_or_scaledSeq hy).mpr (Or.inl rfl)⟩
  · constructor
    · exact (mem_horizonSubdifferential_iff_zero_or_scaledSeq hx).mpr (Or.inr
        ⟨fun n ↦ (q n).fst,fun n ↦ (z n).fst,t,(tendsto_separable_attentive_fst hf hg hx hy).comp hq,
          fun n ↦ (mem_regularSubdifferential_separableSum_finite (hz n)).1,ht,ht0,
          ((WithLp.fstL 2 ℝ E F).continuous.tendsto _).comp hlim⟩)
    · exact (mem_horizonSubdifferential_iff_zero_or_scaledSeq hy).mpr (Or.inr
        ⟨fun n ↦ (q n).snd,fun n ↦ (z n).snd,t,(tendsto_separable_attentive_snd hf hg hx hy).comp hq,
          fun n ↦ (mem_regularSubdifferential_separableSum_finite (hz n)).2,ht,ht0,
          ((WithLp.sndL 2 ℝ E F).continuous.tendsto _).comp hlim⟩)

end RW
