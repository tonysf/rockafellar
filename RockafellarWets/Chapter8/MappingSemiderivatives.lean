/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Semidifferentiability of set-valued mappings
-/

import RockafellarWets.Chapter8.ProtoDifferentiability
import RockafellarWets.Chapter7.EpiDistances
import RockafellarWets.Chapter5.GraphicalContinuousConvergence
import RockafellarWets.Chapter5.ContinuousVersusUniform

open Bornology Filter Metric Set Topology
open scoped Pointwise

namespace RW

/-- A countably generated parameter filter can be tested with all its
convergent sequences. The sets in the family may be empty or nonclosed. -/
theorem pkConvergesAlong_iff_forall_seq {ι V : Type*} [TopologicalSpace V]
    [FirstCountableTopology V] {l : Filter ι} [l.IsCountablyGenerated] [l.NeBot]
    {C : ι → Set V} {D : Set V} :
    PKConvergesAlong l C D ↔ ∀ p : ℕ → ι, Tendsto p atTop l → PKConverges (C ∘ p) D := by
  constructor
  · intro h p hp
    have hi := h.1.ge.trans (innerSetLimitAlong_subset_innerSetLimit_comp hp)
    have ho := (outerSetLimit_comp_subset hp).trans h.2.le
    have hio := innerSetLimit_subset_outerSetLimit (C ∘ p)
    exact ⟨Subset.antisymm (hio.trans ho) hi, Subset.antisymm ho (hi.trans hio)⟩
  · intro h
    have ho : outerSetLimitAlong l C ⊆ D := by
      intro v hv
      obtain ⟨p,hp,hv⟩ := exists_seq_mem_innerSetLimit hv
      exact (h p hp).1.le hv
    have hi : D ⊆ innerSetLimitAlong l C := by
      intro v hv
      by_contra hn
      obtain ⟨p,hp,hn⟩ := exists_seq_not_mem_outerSetLimit hn
      exact hn ((h p hp).2.ge hv)
    have hio := innerSetLimitAlong_subset_outerSetLimitAlong (l := l) C
    exact ⟨Subset.antisymm (hio.trans ho) hi, Subset.antisymm ho (hi.trans hio)⟩

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S H : E → Set F} {x : E} {u : F}

/-- The joint set limit in formula 8(29) at every direction. -/
def HasMappingSemiderivative (S : E → Set F) (x : E) (u : F) (H : E → Set F) : Prop :=
  ∀ w, PKConvergesAlong ((𝓝[>] (0:ℝ)) ×ˢ 𝓝 w)
    (fun p ↦ mappingDifferenceQuotient S x u p.1 p.2) (H w)

/-- **Exercise 8.43(a,b)**, continuous convergence of the difference quotients. -/
theorem hasMappingSemiderivative_iff_continuousConvergence :
    HasMappingSemiderivative S x u H ↔ ∀ τ : ℕ → ℝ, Tendsto τ atTop (𝓝[>] 0) →
      SvConvergesContinuously (fun n ↦ mappingDifferenceQuotient S x u (τ n)) H := by
  constructor
  · intro h τ ht w
    refine svConvergesContinuouslyAt_iff_forall_seq.mpr fun v hv ↦ ?_
    exact (pkConvergesAlong_iff_forall_seq (C := fun p : ℝ × E ↦
      mappingDifferenceQuotient S x u p.1 p.2) (D := H w)).mp (h w)
        (fun n ↦ (τ n,v n)) (ht.prodMk hv)
  · intro h w
    refine pkConvergesAlong_iff_forall_seq.mpr fun p hp ↦ ?_
    exact svConvergesContinuouslyAt_iff_forall_seq.mp
      (h (Prod.fst ∘ p) (tendsto_fst.comp hp) w) (Prod.snd ∘ p) (tendsto_snd.comp hp)

/-- Positive rescaling relates two parameters of the difference quotient. -/
theorem mappingDifferenceQuotient_smul_right (S : E → Set F) (x : E) (u : F)
    (τ : ℝ) (w : E) {a : ℝ} (ha : a ≠ 0) :
    mappingDifferenceQuotient S x u τ (a • w) = a • mappingDifferenceQuotient S x u (a * τ) w := by
  have hs : a * (a * τ)⁻¹ = τ⁻¹ := by rw [mul_inv_rev, mul_left_comm, mul_inv_cancel₀ ha, mul_one]
  rw [mappingDifferenceQuotient, mappingDifferenceQuotient, smul_smul, mul_comm τ a]
  ext z
  constructor
  · rintro ⟨v,hv,rfl⟩
    refine ⟨_,⟨v,hv,rfl⟩,?_⟩
    simp only [smul_smul, hs]
  · rintro ⟨_,⟨v,hv,rfl⟩,rfl⟩
    exact ⟨v,hv,by simp only [smul_smul, hs]⟩

/-- The semiderivative determines the proto-derivative, including its graph
at directions with an empty fiber. -/
theorem HasMappingSemiderivative.protoDerivative [FiniteDimensional ℝ F]
    (h : HasMappingSemiderivative S x u H) :
    IsProtoDifferentiableAt S x u ∧ graphicalDerivative S x u = H := by
  have hg : PKConvergesAlong (𝓝[>] (0:ℝ)) (fun τ ↦ svGraph (mappingDifferenceQuotient S x u τ))
      (svGraph H) := by
    refine pkConvergesAlong_iff_forall_seq.mpr fun τ ht ↦ ?_
    apply graphicalConverges_iff_forall_graphicalConvergesAt.mpr
    intro w
    exact (svConvergesContinuouslyAt_iff_graphicalConvergesAt.mp
      ((hasMappingSemiderivative_iff_continuousConvergence.mp h τ ht) w)).1
  have hder : graphicalDerivative S x u = H := svGraph_injective
    ((svGraph_graphicalDerivative_eq_outerLimit S x u).trans hg.2)
  refine ⟨?_,hder⟩
  unfold IsProtoDifferentiableAt
  rw [hder]
  exact hg

/-- **Exercise 8.43(a,c)**, uniform convergence on bounded sets and continuity
of the limit mapping. -/
theorem hasMappingSemiderivative_iff_uniform [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] :
    HasMappingSemiderivative S x u H ↔ SvContinuousOn H univ ∧
      ∀ τ : ℕ → ℝ, Tendsto τ atTop (𝓝[>] 0) → ∀ B : Set E, IsBounded B →
        SvConvergesUniformlyOn (fun n ↦ mappingDifferenceQuotient S x u (τ n)) H B := by
  rw [hasMappingSemiderivative_iff_continuousConvergence]
  constructor
  · intro h
    have hh {τ : ℕ → ℝ} (ht : Tendsto τ atTop (𝓝[>] 0)) :=
      (svConvergesContinuouslyOn_iff (X := univ)).mp
        (show SvConvergesContinuouslyOn (fun n ↦ mappingDifferenceQuotient S x u (τ n)) H univ from
          fun w _ ↦ h τ ht w)
    obtain ⟨τ,hτ⟩ := (𝓝[>] (0:ℝ)).exists_seq_tendsto
    refine ⟨(hh hτ).2, fun t ht B hB ε hε ρ hρ ↦ ?_⟩
    exact ((hh ht).1 (closure B) (subset_univ _) hB.isCompact_closure ε hε ρ hρ).mono
      fun _ hn w hw ↦ hn w (subset_closure hw)
  · rintro ⟨hc,hu⟩ τ ht w
    exact (svConvergesContinuouslyOn_iff.mpr ⟨fun B _ hB ↦ hu τ ht B hB.isBounded,hc⟩) w (mem_univ w)

private theorem exists_pos_smul_mem {W : Set E} (hW : W ∈ 𝓝 0) (w : E) :
    ∃ c : ℝ, 0 < c ∧ c • w ∈ W := by
  have hlim : Tendsto (fun c : ℝ ↦ c • w) (𝓝[>] 0) (𝓝 0) := by
    simpa only [id_eq, zero_smul] using
      (((continuous_id (X := ℝ)).smul (continuous_const (y := w))).tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  exact (Filter.nonempty_of_mem (inter_mem (self_mem_nhdsWithin : Ioi (0:ℝ) ∈ 𝓝[>] 0) (hlim.eventually hW)))

/-- **Exercise 8.43(a,d)**. Equicontinuity is needed only on a neighborhood
of zero, since positive rescaling transports the moving-direction limits. -/
theorem hasMappingSemiderivative_iff_proto_equicontinuous [FiniteDimensional ℝ F]
    (hx : u ∈ S x) :
    HasMappingSemiderivative S x u H ↔ IsProtoDifferentiableAt S x u ∧
      graphicalDerivative S x u = H ∧ ∃ W ∈ 𝓝 (0:E), ∀ w ∈ W,
        ∀ τ : ℕ → ℝ, Tendsto τ atTop (𝓝[>] 0) →
          SvAsymptoticallyEquicontinuousAt (fun n ↦ mappingDifferenceQuotient S x u (τ n)) w := by
  constructor
  · intro h
    refine ⟨h.protoDerivative.1,h.protoDerivative.2,univ,univ_mem,fun w _ τ ht ↦ ?_⟩
    exact (svConvergesContinuouslyAt_iff_graphicalConvergesAt.mp
      ((hasMappingSemiderivative_iff_continuousConvergence.mp h τ ht) w)).2
  · rintro ⟨hp,rfl,W,hW,he⟩
    apply hasMappingSemiderivative_iff_continuousConvergence.mpr
    intro τ ht w
    refine svConvergesContinuouslyAt_iff_forall_seq.mpr fun v hv ↦ ?_
    obtain ⟨a,ha,haW⟩ := exists_pos_smul_mem hW w
    let t (n : ℕ) := (τ n) / a
    have ht' : Tendsto t atTop (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨?_,(ht.eventually self_mem_nhdsWithin).mono fun _ h ↦ div_pos h ha⟩
      simpa only [zero_div] using (ht.mono_right nhdsWithin_le_nhds).div_const a
    have hg := graphicalConverges_iff_forall_graphicalConvergesAt.mp
      (pkConvergesAlong_iff_forall_seq.mp hp t ht') (a • w)
    have hcc := svConvergesContinuouslyAt_iff_graphicalConvergesAt.mpr ⟨hg, he _ haW t ht'⟩
    have hh := svConvergesContinuouslyAt_iff_forall_seq.mp hcc (fun n ↦ a • v n) (hv.const_smul a)
    have hH : SvPositivelyHomogeneous (graphicalDerivative S x u) :=
      svPositivelyHomogeneous_iff_isCone_svGraph.mpr ((svGraph_graphicalDerivative S x u) ▸
        (isCone_tangentCone (show (x,u) ∈ svGraph S from hx)))
    have hq (n : ℕ) : mappingDifferenceQuotient S x u (t n) (a • v n) =
        a • mappingDifferenceQuotient S x u (τ n) (v n) := by
      rw [mappingDifferenceQuotient_smul_right _ _ _ _ _ ha.ne']
      congr 2
      dsimp [t]
      field_simp
    let A : F ≃ₜ F := Homeomorph.smulOfNeZero a ha.ne'
    have hpre (D : Set F) : A.symm ⁻¹' D = a • D := (A.image_eq_preimage_symm D).symm
    apply (pkConverges_preimage_homeomorph_iff A.symm).mp
    simpa only [hpre, hq, hH.2 w a ha] using hh

/-- **Exercise 8.43**, domain and homogeneity conclusions. -/
theorem HasMappingSemiderivative.properties [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (h : HasMappingSemiderivative S x u H) (hx : u ∈ S x) :
    x ∈ interior (svDom S) ∧ SvPositivelyHomogeneous H ∧ SvContinuousOn H univ ∧ svDom H = univ := by
  have hc := (hasMappingSemiderivative_iff_uniform.mp h).1
  have hcone : SvPositivelyHomogeneous H := by
    rw [← h.protoDerivative.2, svPositivelyHomogeneous_iff_isCone_svGraph, svGraph_graphicalDerivative]
    exact isCone_tangentCone (show (x,u) ∈ svGraph S from hx)
  have hdom : svDom H ∈ 𝓝 (0:E) := by
    have hi := (svContinuousWithinAt_univ.mp (hc 0 (mem_univ _))).2 hcone.1 univ univ_mem
    exact hi.mono fun w ⟨z,hz,_⟩ ↦ ⟨z,hz⟩
  have hfull : svDom H = univ := by
    apply eq_univ_of_forall
    intro w
    obtain ⟨a,ha,haw⟩ := exists_pos_smul_mem hdom w
    have hm := hcone.isCone_svDom.2 haw (inv_pos.mpr ha)
    simpa [ha.ne'] using hm
  refine ⟨mem_interior_iff_mem_nhds.mpr ?_,hcone,hc,hfull⟩
  have hi := (h 0).1.ge hcone.1 univ univ_mem
  obtain ⟨T,hT,V,hV,hTV⟩ := mem_prod_iff.mp hi
  obtain ⟨t,ht,htT⟩ := Filter.nonempty_of_mem (inter_mem (self_mem_nhdsWithin : Ioi (0:ℝ) ∈ 𝓝[>] 0) hT)
  have hv : Tendsto (fun y : E ↦ t⁻¹ • (y-x)) (𝓝 x) (𝓝 0) := by
    simpa using ((continuous_id.sub (continuous_const (y := x))).const_smul t⁻¹).tendsto x
  filter_upwards [hv.eventually hV] with y hy
  obtain ⟨_,⟨v,hvS,rfl⟩,_⟩ := hTV (show (t,t⁻¹ • (y-x)) ∈ T ×ˢ V from ⟨htT,hy⟩)
  have htpos : (0:ℝ) < t := ht
  exact ⟨v,by simpa [smul_smul, htpos.ne'] using hvS⟩

end RW
