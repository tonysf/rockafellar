/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The full Hausdorff modulus of bounded compositions
-/

import RockafellarWets.Chapter10.BoundedCompositionContinuity

open Bornology Filter Metric Set Topology
open scoped NNReal ENNReal

namespace RW

theorem upperSemicontinuous_localPairModulus {X : Type*} [MetricSpace X]
    (q : X → X → ℝ≥0∞) : UpperSemicontinuous (localPairModulusWithin q univ) := by
  intro x a ha
  obtain ⟨k,hka⟩ := iInf_lt_iff.mp ha
  obtain ⟨U,hU,hbound⟩ := k.2
  have hUx : U ∈ 𝓝 x := by simpa only [nhdsWithin_univ] using hU
  filter_upwards [isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hUx)] with y hy
  exact (localPairModulusWithin_le
    (by simpa only [nhdsWithin_univ] using mem_interior_iff_mem_nhds.mp hy) hbound).trans_lt hka

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  {S : E → Set F} {T : F → Set G} {x : E} {u : F}

theorem graphicalLipschitzModulus_le_hausdorffModulus
    (hS : ∀ᶠ a in 𝓝 x, (S a).Nonempty ∧ IsClosed (S a)) (u : F) :
    graphicalLipschitzModulus S x u ≤ svHausdorffLipschitzModulus S x := by
  refine le_iInf fun k ↦ ?_
  obtain ⟨U,hU,hk⟩ := k.2
  have hU' : U ∈ 𝓝 x := by simpa only [nhdsWithin_univ] using hU
  let V := U ∩ {a | (S a).Nonempty ∧ IsClosed (S a)}
  have hV : V ∈ 𝓝[univ] x := by simpa only [nhdsWithin_univ] using inter_mem hU' hS
  have hL : SvLipschitzOnWith k.val S V := ⟨fun _ ha ↦ ha.2,fun a ha b hb ↦ by
    simpa only [ENNReal.ofReal_mul (p := (k.val:ℝ)) (q := dist a b) k.val.2, ENNReal.ofReal_coe_nnreal, edist_dist] using hk a ha.1 b hb.1⟩
  apply (aubinEstimate_of_local_transport (r := ‖u‖₊+1) (by simp) hV ?_).modulus_le
  exact fun a ha b hb v hv ↦ (svLipschitzOnWith_iff_transport hL.1).mp hL a ha b hb v hv.1

theorem svHausdorffLipschitzModulus_le_iSup_graphical
    (ho : SvOscAt S x) (hb : SvLocallyBoundedAt S x)
    (hc : ∀ᶠ a in 𝓝 x, (S a).Nonempty ∧ IsClosed (S a)) :
    svHausdorffLipschitzModulus S x ≤ ⨆ u ∈ S x, graphicalLipschitzModulus S x u := by
  by_contra! h
  obtain ⟨k,hlo,hhi⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
  obtain ⟨V,hV,hbV⟩ := hb
  obtain ⟨r,hr,hball⟩ := hbV.subset_closedBall_lt 0 (0:F)
  have hA : ∀ u ∈ S x ∩ closedBall (0:F) r, AubinEstimate S univ x u k :=
    fun u hu ↦ aubinEstimate_of_modulus_lt ((le_iSup₂ (f := fun u (_ : u ∈ S x) ↦
      graphicalLipschitzModulus S x u) u hu.1).trans_lt hlo)
  obtain ⟨U,hU,H⟩ := exists_local_transport_of_uniform_aubinEstimates ho.isClosed
    (by simpa only [svOscWithinAt_univ] using ho) ⟨r,hr.le⟩ k hA
  let W := U ∩ V ∩ {a | (S a).Nonempty ∧ IsClosed (S a)}
  have hW : W ∈ 𝓝[univ] x := by
    simpa only [nhdsWithin_univ] using inter_mem
      (inter_mem (show U ∈ 𝓝 x by simpa only [nhdsWithin_univ] using hU) hV) hc
  have hL : SvLipschitzOnWith k S W := svLipschitzOnWith_of_bounded_rho_transport
    (r := ⟨r,hr.le⟩) (fun _ ha ↦ ha.2)
    ((svImage_mono (S := S) (show W ⊆ V from fun _ ha ↦ ha.1.2)).trans hball)
    (fun a ha b hb v hv ↦ H a ha.1.1 b hb.1.1 v hv)
  exact hhi.not_ge (localPairModulusWithin_le hW (fun a ha b hb ↦ by
    simpa only [ENNReal.ofReal_mul (p := (k:ℝ)) (q := dist a b) k.2, ENNReal.ofReal_coe_nnreal, edist_dist] using hL.2 a ha b hb))

theorem svHausdorffLipschitzModulus_eq_iSup_graphical
    (ho : SvOscAt S x) (hb : SvLocallyBoundedAt S x)
    (hc : ∀ᶠ a in 𝓝 x, (S a).Nonempty ∧ IsClosed (S a)) :
    svHausdorffLipschitzModulus S x = ⨆ u ∈ S x, graphicalLipschitzModulus S x u :=
  le_antisymm (svHausdorffLipschitzModulus_le_iSup_graphical ho hb hc)
    (iSup₂_le fun u _ ↦ graphicalLipschitzModulus_le_hausdorffModulus hc u)

theorem SvStrictlyContinuousAt.hausdorffModulus_lt_top
    (hs : SvStrictlyContinuousAt S x) (hb : SvLocallyBoundedAt S x) :
    svHausdorffLipschitzModulus S x < ⊤ := by
  have hb' : SvLocallyBoundedWithinAt S univ x := by
    obtain ⟨V,hV,hbV⟩ := hb
    exact ⟨V,hV,by simpa only [univ_inter] using hbV⟩
  obtain ⟨U,hU,k,hk⟩ := hs.exists_svLipschitzOn hb'
  exact (localPairModulusWithin_le (k := k) hU (fun a ha b hb ↦ by
    simpa only [ENNReal.ofReal_mul (p := (k:ℝ)) (q := dist a b) k.2, ENNReal.ofReal_coe_nnreal, edist_dist] using hk.2 a ha b hb)).trans_lt ENNReal.coe_lt_top

/-- The last inequality of 10.38, with a genuine maximum of the outer
Hausdorff modulus on the compact intermediate fiber. -/
theorem exists_max_hausdorff_composition_bound (hS : SvOsc S) (hT : SvOsc T)
    (hsS : SvStrictlyContinuousAt S x) (hbS : SvLocallyBoundedAt S x)
    (hsT : ∀ w ∈ S x, SvStrictlyContinuousAt T w)
    (hbT : ∀ w ∈ S x, SvLocallyBoundedAt T w) :
    ∃ w ∈ S x, IsMaxOn (svHausdorffLipschitzModulus T) (S x) w ∧
      svHausdorffLipschitzModulus (svComp T S) x ≤
        svHausdorffLipschitzModulus S x * svHausdorffLipschitzModulus T w := by
  have hK := Metric.isCompact_of_isClosed_isBounded (hS x).isClosed hbS.isBounded_apply
  obtain ⟨w,hw,hm⟩ := UpperSemicontinuousOn.exists_isMaxOn hsS.nonempty_isClosed.1 hK
    ((upperSemicontinuous_localPairModulus (fun a b ↦ hausdorffEDist (T a) (T b))).upperSemicontinuousOn (S x))
  refine ⟨w,hw,hm,?_⟩
  have hs := svStrictlyContinuousAt_svComp_of_locallyBounded hS hT hsS hbS hsT
  have hbs := svLocallyBoundedAt_svComp (hS x) hbS hbT
  have he : ∀ᶠ a in 𝓝 x, (svComp T S a).Nonempty ∧ IsClosed (svComp T S a) := by
    simpa only [nhdsWithin_univ] using hs.2.1
  apply (svHausdorffLipschitzModulus_le_iSup_graphical
    (svOscAt_svComp_of_locallyBounded hS hT hbS) hbs he).trans
  refine iSup₂_le fun u hu ↦ ?_
  apply (graphicalLipschitzModulus_svComp_le_iSup hS hT hu
    (svLocallyBoundedAt_svCompAux_left hbS u)
    (fun v hv ↦ hsS.hasAubinPropertyAt hv.1)
    (fun v hv ↦ (hsT v hv.1).hasAubinPropertyAt hv.2)).trans
  refine iSup₂_le fun v hv ↦ mul_le_mul'
    (graphicalLipschitzModulus_le_hausdorffModulus (by simpa only [nhdsWithin_univ] using hsS.2.1) v)
    ((graphicalLipschitzModulus_le_hausdorffModulus
      (by simpa only [nhdsWithin_univ] using (hsT v hv.1).2.1) u).trans (hm hv.1))

end RW
