/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Strict continuity and Hausdorff bounds for bounded finite sums
-/

import RockafellarWets.Chapter10.FiniteSumQualifications
import RockafellarWets.Chapter10.CompositionHausdorffModulus

open Bornology Filter Metric Set Topology
open scoped ENNReal NNReal

namespace RW

variable {ι E F : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {S : ι → E → Set F} {x : E}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The local boundedness of decompositions used in 10.41(a), written in
terms of the neighborhoods and componentwise strict bound from the book. -/
theorem finiteSumMappingAux_locallyBounded_iff {b : F} :
    SvLocallyBoundedAt (finiteSumMappingAux S) (x,b) ↔
      ∃ V ∈ 𝓝 x, ∃ W ∈ 𝓝 b, ∃ r > (0:ℝ), ∀ a ∈ V, ∀ q : ι → F,
        (∀ i, q i ∈ S i a) → (∑ i, q i) ∈ W → ∀ i, ‖q i‖ < r := by
  constructor
  · rintro ⟨U,hU,hb⟩
    obtain ⟨V,hV,W,hW,hVW⟩ := mem_nhds_prod_iff.mp hU
    obtain ⟨r,hr,hball⟩ := hb.subset_closedBall_lt 0 (0 : PiLp 2 (fun _ : ι ↦ F))
    refine ⟨V,hV,W,hW,r+1,by linarith,?_⟩
    intro a ha q hq hs i
    have hmem : WithLp.toLp 2 q ∈ svImage (finiteSumMappingAux S) U :=
      mem_svImage.mpr ⟨(a,∑ j, q j),hVW ⟨ha,hs⟩,hq,rfl⟩
    have hbq := mem_closedBall.mp (hball hmem)
    rw [dist_zero_right] at hbq
    exact ((l2Pi_norm_apply_le (WithLp.toLp 2 q) i).trans hbq).trans_lt (lt_add_one _)
  · rintro ⟨V,hV,W,hW,r,_,H⟩
    refine ⟨V ×ˢ W,prod_mem_nhds hV hW,?_⟩
    apply ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ F)).symm.toContinuousLinearMap.lipschitz.isBounded_image
      (IsBounded.pi (fun _ : ι ↦ (isBounded_closedBall : IsBounded (closedBall (0:F) r))))).subset
    intro q hq
    obtain ⟨p,hp,hq⟩ := mem_svImage.mp hq
    refine ⟨WithLp.ofLp q,fun i _ ↦ ?_,rfl⟩
    rw [mem_closedBall,dist_zero_right]
    apply (H p.1 hp.1 (fun j ↦ q j) hq.1 _ i).le
    rw [hq.2]
    exact hp.2

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem svFiniteSum_eq_comp_product (S : ι → E → Set F) :
    svFiniteSum S = svComp (svSingleton (l2PiSum (ι := ι) (E := F)))
      (fun a ↦ l2PiSet (fun i ↦ S i a)) := by
  funext a
  rw [svFiniteSum, finiteSetSum_eq_l2PiSum_image]
  ext b
  simp only [mem_image,mem_svComp,mem_svSingleton,eq_comm (a := b)]

omit [Fintype ι] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem svOsc_l2PiSet (hS : ∀ i, SvOsc (S i)) :
    SvOsc (fun a ↦ l2PiSet (fun i ↦ S i a)) := by
  apply isClosed_svGraph_iff_svOsc.mp
  have he : svGraph (fun a ↦ l2PiSet (fun i ↦ S i a)) =
      ⋂ i, (fun p : E × PiLp 2 (fun _ : ι ↦ F) ↦ (p.1,p.2 i)) ⁻¹' svGraph (S i) := by
    ext p
    simp only [mem_iInter,mem_preimage,mem_svGraph,mem_l2PiSet]
  rw [he]
  exact isClosed_iInter fun i ↦ (isClosed_svGraph_iff_svOsc.mpr (hS i)).preimage
    (continuous_fst.prodMk ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι ↦ F) i).continuous.comp continuous_snd))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem svLocallyBoundedAt_l2PiSet (hb : ∀ i, SvLocallyBoundedAt (S i) x) :
    SvLocallyBoundedAt (fun a ↦ l2PiSet (fun i ↦ S i a)) x := by
  choose V hV hbV using hb
  refine ⟨⋂ i, V i,Filter.iInter_mem.mpr hV,?_⟩
  apply ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ F)).symm.toContinuousLinearMap.lipschitz.isBounded_image
    (IsBounded.pi hbV)).subset
  intro u hu
  obtain ⟨a,ha,hu⟩ := mem_svImage.mp hu
  exact ⟨fun i ↦ u i,fun i _ ↦ mem_svImage.mpr ⟨a,mem_iInter.mp ha i,hu i⟩,rfl⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem svLocallyBoundedAt_svFiniteSum (hb : ∀ i, SvLocallyBoundedAt (S i) x) :
    SvLocallyBoundedAt (svFiniteSum S) x := by
  obtain ⟨V,hV,hbV⟩ := svLocallyBoundedAt_l2PiSet hb
  refine ⟨V,hV,((l2PiSum (ι := ι) (E := F)).lipschitz.isBounded_image hbV).subset ?_⟩
  intro b hb
  obtain ⟨a,ha,u,hu,rfl⟩ := mem_svImage.mp hb
  exact ⟨WithLp.toLp 2 u,mem_svImage.mpr ⟨a,ha,hu⟩,l2PiSum_apply _⟩

theorem finiteSumMappingAux_locallyBounded (hb : ∀ i, SvLocallyBoundedAt (S i) x) (b : F) :
    SvLocallyBoundedAt (finiteSumMappingAux S) (x,b) := by
  apply finiteSumMappingAux_locallyBounded_of_horizon
  intro z hz _ i
  simpa only [svHorizonOuterLimit_eq_zero_of_svLocallyBoundedAt (hb i),mem_singleton_iff] using hz i

theorem svOscAt_svFiniteSum (hS : ∀ i, SvOsc (S i))
    (hb : ∀ i, SvLocallyBoundedAt (S i) x) : SvOscAt (svFiniteSum S) x := by
  rw [svFiniteSum_eq_comp_product]
  exact svOscAt_svComp_of_locallyBounded (svOsc_l2PiSet hS)
    (fun a ↦ svOscAt_svSingleton_of_continuousAt (l2PiSum (ι := ι) (E := F)).continuous.continuousAt)
    (svLocallyBoundedAt_l2PiSet hb)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem eventually_isClosed_svFiniteSum (hS : ∀ i, SvOsc (S i))
    (hb : ∀ i, SvLocallyBoundedAt (S i) x) : ∀ᶠ a in 𝓝 x, IsClosed (svFiniteSum S a) := by
  obtain ⟨V,hV,hbV⟩ := svLocallyBoundedAt_l2PiSet hb
  filter_upwards [hV] with a ha
  have hK := Metric.isCompact_of_isClosed_isBounded ((svOsc_l2PiSet hS) a).isClosed
    (hbV.subset (subset_svImage (S := fun a ↦ l2PiSet (fun i ↦ S i a)) ha))
  rw [svFiniteSum, finiteSetSum_eq_l2PiSum_image]
  exact (hK.image (l2PiSum (ι := ι) (E := F)).continuous).isClosed

/-- Corrected unrestricted clause of 10.42. -/
theorem svStrictlyContinuousAt_svFiniteSum_of_closed (hS : ∀ i, SvOsc (S i))
    (hs : ∀ i, SvStrictlyContinuousAt (S i) x)
    (hb : ∀ b ∈ svFiniteSum S x, SvLocallyBoundedAt (finiteSumMappingAux S) (x,b))
    (ho : SvOscAt (svFiniteSum S) x)
    (hc : ∀ᶠ a in 𝓝 x, IsClosed (svFiniteSum S a)) :
    SvStrictlyContinuousAt (svFiniteSum S) x := by
  have hne : (svFiniteSum S x).Nonempty := by
    choose u hu using fun i ↦ (hs i).nonempty_isClosed.1
    exact ⟨∑ i, u i,u,hu,rfl⟩
  apply SvStrictlyContinuousAt.of_osc_aubin_eventually_closed ho hne hc
  intro b hbmem
  exact hasAubinPropertyAt_svFiniteSum hS hbmem (hb b hbmem)
    (fun u hu i ↦ (hs i).hasAubinPropertyAt (hu.1 i))

/-- The bounded-value strict-continuity clause in 10.42. -/
theorem svStrictlyContinuousAt_svFiniteSum (hS : ∀ i, SvOsc (S i))
    (hs : ∀ i, SvStrictlyContinuousAt (S i) x)
    (hb : ∀ i, SvLocallyBoundedAt (S i) x) : SvStrictlyContinuousAt (svFiniteSum S) x :=
  svStrictlyContinuousAt_svFiniteSum_of_closed hS hs
    (fun b _ ↦ finiteSumMappingAux_locallyBounded hb b)
    (svOscAt_svFiniteSum hS hb) (eventually_isClosed_svFiniteSum hS hb)

/-- The sharp full Hausdorff modulus estimate in 10.42. -/
theorem svHausdorffLipschitzModulus_svFiniteSum_le (hS : ∀ i, SvOsc (S i))
    (hs : ∀ i, SvStrictlyContinuousAt (S i) x)
    (hb : ∀ i, SvLocallyBoundedAt (S i) x) :
    svHausdorffLipschitzModulus (svFiniteSum S) x ≤ ∑ i, svHausdorffLipschitzModulus (S i) x := by
  have ht := svStrictlyContinuousAt_svFiniteSum hS hs hb
  apply (svHausdorffLipschitzModulus_le_iSup_graphical (svOscAt_svFiniteSum hS hb)
    (svLocallyBoundedAt_svFiniteSum hb) (by simpa only [nhdsWithin_univ] using ht.2.1)).trans
  refine iSup₂_le fun b hbmem ↦ ?_
  apply (graphicalLipschitzModulus_svFiniteSum_le_iSup hS hbmem
    (finiteSumMappingAux_locallyBounded hb b)
    (fun u hu i ↦ (hs i).hasAubinPropertyAt (hu.1 i))).trans
  refine iSup₂_le fun u _ ↦ Finset.sum_le_sum fun i _ ↦ ?_
  exact graphicalLipschitzModulus_le_hausdorffModulus
    (by simpa only [nhdsWithin_univ] using (hs i).2.1) (u i)

end RW
