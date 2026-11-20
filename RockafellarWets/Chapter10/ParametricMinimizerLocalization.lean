/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A common compact decision set near a parameter in Theorem 10.58
-/
import RockafellarWets.Chapter7.OptimalSetContinuity
import RockafellarWets.Chapter10.OuterCompositionLocalization

open Bornology Filter Set Topology

namespace RW

variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- A continuous finite model of the cost near the original minimizers
localizes all nearby minimizers in one compact subset of that decision region.
The marginal is finite there and attains its value on the common compact set. -/
theorem exists_compact_decision_set {f : E × P → EReal} {g : E × P → ℝ}
    {V : Set E} {W : Set P} {u₀ : P} (hf : LowerSemicontinuous f) (hp : IsProper f)
    (hb : IsLevelBoundedInXLocallyUniformly f) (hu₀ : valueFunction f u₀ < ⊤)
    (hV : IsOpen V) (hW : IsOpen W) (huW : u₀ ∈ W) (hPV : paramArgmin f u₀ ⊆ V)
    (hfg : ∀ p ∈ V ×ˢ W, f p = (g p : EReal)) (hg : ContinuousOn g (V ×ˢ W)) :
    ∃ K : Set E, IsCompact K ∧ K ⊆ V ∧ ∃ O : Set P, IsOpen O ∧ u₀ ∈ O ∧ O ⊆ W ∧
      ∀ u ∈ O, (valueFunction f u).toReal = sInf ((fun x ↦ g (x,u)) '' K) ∧
        ((valueFunction f u).toReal : EReal) = valueFunction f u ∧
        (paramArgmin f u).Nonempty ∧ paramArgmin f u ⊆ K := by
  obtain ⟨x₀,hx₀⟩ := paramArgmin_nonempty hf hp hb hu₀
  have hxV := hPV hx₀
  have ht : ContinuousAt (fun u ↦ f (x₀,u)) u₀ := by
    have h := continuous_coe_real_ereal.continuousAt.comp
      (((hg (x₀,u₀) ⟨hxV,huW⟩).continuousAt ((hV.prod hW).mem_nhds ⟨hxV,huW⟩)).comp
        (continuous_const.prodMk continuous_id).continuousAt)
    apply ContinuousAt.congr_of_eventuallyEq h
    filter_upwards [hW.mem_nhds huW] with u hu
    exact hfg _ ⟨hxV,hu⟩
  have hmin := ((mem_paramArgmin_iff f u₀ x₀).mp hx₀).1
  have hupp : UpperSemicontinuousWithinAt (valueFunction f) univ u₀ := by
    intro a ha
    rw [nhdsWithin_univ]
    filter_upwards [ht.tendsto.eventually (gt_mem_nhds (hmin.trans_lt ha))] with u hu
    exact (iInf_le (fun x ↦ f (x,u)) x₀).trans_lt hu
  have ho : SvOscAt (paramArgmin f) u₀ := by
    simpa only [svOscWithinAt_univ] using svOscWithinAt_paramArgmin hf hu₀ hupp
  obtain ⟨a,ha,-⟩ := EReal.exists_between_coe_real hu₀
  obtain ⟨N,hN,hbN⟩ := svLocallyBoundedWithinAt_paramArgmin hb
    ⟨a,(hupp _ ha).mono (fun _ h ↦ h.le)⟩
  have hbp : SvLocallyBoundedAt (paramArgmin f) u₀ := ⟨N,hN,by simpa only [univ_inter] using hbN⟩
  obtain ⟨K,hK,hPK,hKV⟩ := exists_compact_between ((paramArgmin_compact_and_dom hf hp hb).1 u₀) hV hPV
  obtain ⟨U,hU,hUK⟩ := ho.exists_nhds_svImage_subset hbp isOpen_interior hPK
  refine ⟨K,hK,hKV,interior U ∩ W,isOpen_interior.inter hW,⟨mem_interior_iff_mem_nhds.mpr hU,huW⟩,
    inter_subset_right,?_⟩
  intro u hu
  have htop : valueFunction f u < ⊤ := (iInf_le (fun x ↦ f (x,u)) x₀).trans_lt
    ((hfg _ ⟨hxV,hu.2⟩).trans_lt (EReal.coe_lt_top _))
  have hcoe := EReal.coe_toReal htop.ne ((isProper_valueFunction_of_lsc_localUniform hf hp hb).2 u).ne'
  obtain ⟨w,hw⟩ := paramArgmin_nonempty hf hp hb htop
  have hall : paramArgmin f u ⊆ K := fun x hx ↦ interior_subset
    (hUK (mem_svImage.mpr ⟨u,interior_subset hu.1,hx⟩))
  have heq : g (w,u) = (valueFunction f u).toReal := EReal.coe_injective
    ((hfg _ ⟨hKV (hall hw),hu.2⟩).symm.trans (((mem_paramArgmin_iff f u w).mp hw).1.trans hcoe.symm))
  have hleast : IsLeast ((fun x ↦ g (x,u)) '' K) (valueFunction f u).toReal := by
    refine ⟨⟨w,hall hw,heq⟩,?_⟩
    rintro _ ⟨x,hx,rfl⟩
    apply EReal.coe_le_coe_iff.mp
    rw [hcoe,← hfg _ ⟨hKV hx,hu.2⟩]
    exact iInf_le (fun x ↦ f (x,u)) x
  exact ⟨hleast.csInf_eq.symm,hcoe,⟨w,hw⟩,hall⟩

end RW
