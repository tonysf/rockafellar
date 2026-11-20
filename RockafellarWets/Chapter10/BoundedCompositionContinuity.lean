/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Strict continuity of locally bounded compositions
-/

import RockafellarWets.Chapter10.CompositionLipschitz
import RockafellarWets.Chapter9.ConvexSetValuedBounds

open Bornology Filter Metric Set Topology
open scoped NNReal ENNReal

namespace RW

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  {S : E → Set F} {T : F → Set G} {x : E}

theorem exists_open_superset_bounded_svImage {C : Set F} (hC : IsCompact C)
    (hT : ∀ w ∈ C, SvLocallyBoundedAt T w) :
    ∃ U : Set F, IsOpen U ∧ C ⊆ U ∧ IsBounded (svImage T U) := by
  classical
  choose V hV hb using fun w : C ↦ hT w w.property
  obtain ⟨s,hs⟩ := hC.elim_finite_subcover (fun w : C ↦ interior (V w))
    (fun _ ↦ isOpen_interior)
    (fun w hw ↦ mem_iUnion.mpr ⟨⟨w,hw⟩,mem_interior_iff_mem_nhds.mpr (hV ⟨w,hw⟩)⟩)
  refine ⟨⋃ w ∈ s, interior (V w),isOpen_biUnion (fun _ _ ↦ isOpen_interior),hs,?_⟩
  simp only [svImage_iUnion]
  exact (isBounded_biUnion_finset s).mpr fun w _ ↦ (hb w).subset (svImage_mono interior_subset)

theorem svLocallyBoundedAt_svComp (hS : SvOscAt S x) (hbS : SvLocallyBoundedAt S x)
    (hbT : ∀ w ∈ S x, SvLocallyBoundedAt T w) : SvLocallyBoundedAt (svComp T S) x := by
  obtain ⟨U,hU,hSU,hbU⟩ := exists_open_superset_bounded_svImage
    (Metric.isCompact_of_isClosed_isBounded hS.isClosed hbS.isBounded_apply) hbT
  obtain ⟨V,hV,hVU⟩ := hS.exists_nhds_svImage_subset hbS hU hSU
  exact ⟨V,hV,by rw [svImage_svComp]; exact hbU.subset (svImage_mono hVU)⟩

/-- Local boundedness of the inner map prevents finite output limits from
escaping through unbounded intermediate points. -/
theorem svOscAt_svComp_of_locallyBounded (hS : SvOsc S) (hT : SvOsc T)
    (hb : SvLocallyBoundedAt S x) : SvOscAt (svComp T S) x := by
  intro u hu
  obtain ⟨a,b,ha,hab,hbu⟩ := mem_outerSetLimitAlong_iff_exists_seq.mp hu
  choose w hwS hwT using fun n ↦ mem_svComp.mp (hab n)
  let q : ℕ → WithLp 2 (WithLp 2 (E × G) × F) :=
    fun n ↦ WithLp.toLp 2 (WithLp.toLp 2 (a n,b n),w n)
  have hq : ∀ n, q n ∈ compositionGraphLift T S := fun n ↦ ⟨hwS n,hwT n⟩
  have hp : Tendsto ((WithLp.fstL 2 ℝ (WithLp 2 (E × G)) F) ∘ q) atTop
      (𝓝 (WithLp.toLp 2 (x,u))) := by
    exact (WithLp.prodContinuousLinearEquiv 2 ℝ E G).symm.continuous.continuousAt.tendsto.comp (ha.prodMk_nhds hbu)
  obtain ⟨p,hp,-⟩ := exists_tendsto_subseq_of_image_tendsto
    (isClosed_compositionGraphLift hS hT) (WithLp.fstL 2 ℝ (WithLp 2 (E × G)) F).continuous
    (compositionGraphProjection_bounded_inverse (svLocallyBoundedAt_svCompAux_left hb u)) hq hp
  have he : p.fst = WithLp.toLp 2 (x,u) := hp.2
  exact mem_svComp.mpr ⟨p.snd,by simpa [he] using hp.1.1,by simpa [he] using hp.1.2⟩

theorem SvStrictlyContinuousAt.of_osc_aubin_eventually_closed
    (ho : SvOscAt S x) (hne : (S x).Nonempty)
    (hc : ∀ᶠ a in 𝓝 x, IsClosed (S a))
    (hA : ∀ u ∈ S x, HasAubinPropertyAt S x u) : SvStrictlyContinuousAt S x := by
  obtain ⟨u,hu⟩ := hne
  obtain ⟨k,V,hV,W,hW,H⟩ := (hA u hu).2.2.2
  have hs : ∀ᶠ a in 𝓝[univ] x, (S a).Nonempty ∧ IsClosed (S a) := by
    rw [nhdsWithin_univ]
    filter_upwards [hV,hc] with a ha hac
    obtain ⟨w,hw,-⟩ := H x ⟨mem_univ x,mem_of_mem_nhds hV⟩ a ⟨mem_univ a,ha⟩
      u ⟨hu,mem_of_mem_nhds hW⟩
    exact ⟨⟨w,hw⟩,hac⟩
  apply (svStrictlyContinuousWithinAt_iff_local_transport_of_eventually (mem_univ x) hs).mpr
  exact exists_local_transport_of_aubinEstimates (mem_univ x) ho.isClosed
    (by simpa only [svOscWithinAt_univ] using ho) (fun u hu ↦ (hA u hu).2.2.2)

/-- Corrected strict-continuity clause of 10.38: outer semicontinuity and
eventual closed-valuedness are needed in addition to estimates at graph points. -/
theorem svStrictlyContinuousAt_svComp_of_closed (hS : SvOsc S) (hT : SvOsc T)
    (hsS : SvStrictlyContinuousAt S x)
    (hsT : ∀ w ∈ S x, SvStrictlyContinuousAt T w)
    (hb : ∀ u ∈ svComp T S x, SvLocallyBoundedAt (svCompAux T S) (x,u))
    (ho : SvOscAt (svComp T S) x)
    (hc : ∀ᶠ a in 𝓝 x, IsClosed (svComp T S a)) :
    SvStrictlyContinuousAt (svComp T S) x := by
  have hne : (svComp T S x).Nonempty := by
    obtain ⟨w,hw⟩ := hsS.nonempty_isClosed.1
    obtain ⟨u,hu⟩ := (hsT w hw).nonempty_isClosed.1
    exact ⟨u,mem_svComp.mpr ⟨w,hw,hu⟩⟩
  apply SvStrictlyContinuousAt.of_osc_aubin_eventually_closed ho hne hc
  intro u hu
  exact hasAubinPropertyAt_svComp hS hT hu (hb u hu)
    (fun w hw ↦ hsS.hasAubinPropertyAt hw.1)
    (fun w hw ↦ (hsT w hw.1).hasAubinPropertyAt hw.2)

/-- The locally bounded strict-continuity assertion in 10.38 has all the
closedness it needs and holds without any additional condition. -/
theorem svStrictlyContinuousAt_svComp_of_locallyBounded (hS : SvOsc S) (hT : SvOsc T)
    (hsS : SvStrictlyContinuousAt S x) (hbS : SvLocallyBoundedAt S x)
    (hsT : ∀ w ∈ S x, SvStrictlyContinuousAt T w) :
    SvStrictlyContinuousAt (svComp T S) x := by
  apply svStrictlyContinuousAt_svComp_of_closed hS hT hsS hsT
    (fun u _ ↦ svLocallyBoundedAt_svCompAux_left hbS u)
    (svOscAt_svComp_of_locallyBounded hS hT hbS)
  obtain ⟨V,hV,hbV⟩ := hbS
  filter_upwards [hV] with a ha
  exact hT.isClosed_svImage_of_isCompact
    (Metric.isCompact_of_isClosed_isBounded (hS a).isClosed (hbV.subset (subset_svImage ha)))

end RW
