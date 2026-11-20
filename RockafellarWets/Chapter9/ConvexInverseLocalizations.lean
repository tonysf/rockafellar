/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Convex-valued inverse localizations in equal dimension
-/

import RockafellarWets.Chapter9.InverseLocalizations
import RockafellarWets.Chapter5.MichaelRepresentation

open Filter Metric Set Topology
open scoped NNReal

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Inner semicontinuity is required locally only at graph points whose
output lies near the selected value. This follows from the local truncated
inner-continuity assumption in Theorem 9.54. -/
def SvLocallyIscAtGraph (S : E → Set E) (x u : E) : Prop :=
  ∃ V W : Set E, IsOpen V ∧ x ∈ V ∧ IsOpen W ∧ u ∈ W ∧
    ∀ a ∈ V, ∀ v ∈ S a ∩ W, v ∈ svInnerLimitWithin S V a

/-- The uniform truncated transport hypothesis printed before 9.54 implies
our pointwise local inner-semicontinuity condition. Only its forward transport
half is needed. -/
theorem svLocallyIscAtGraph_of_truncated_transport {S : E → Set E} {x u : E}
    {V W : Set E} (hV : V ∈ 𝓝 x) (hW : W ∈ 𝓝 u)
    (ht : ∀ a ∈ V, ∀ ε > 0, ∃ δ > 0, ∀ b ∈ V, dist b a < δ →
      ∀ v ∈ S a ∩ W, ∃ q ∈ S b, dist v q ≤ ε) : SvLocallyIscAtGraph S x u := by
  obtain ⟨V₀,hV₀V,hV₀o,hxV₀⟩ := _root_.mem_nhds_iff.mp hV
  obtain ⟨W₀,hW₀W,hW₀o,huW₀⟩ := _root_.mem_nhds_iff.mp hW
  refine ⟨V₀,W₀,hV₀o,hxV₀,hW₀o,huW₀,?_⟩
  intro a ha v hv Q hQ
  obtain ⟨ε,hε,hεQ⟩ := Metric.mem_nhds_iff.mp hQ
  obtain ⟨δ,hδ,hδt⟩ := ht a (hV₀V ha) (ε/2) (half_pos hε)
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (ball_mem_nhds a hδ)] with b hb hbδ
  obtain ⟨q,hq,hvq⟩ := hδt b (hV₀V hb) (mem_ball.mp hbδ) v ⟨hv.1,hW₀W hv.2⟩
  exact ⟨q,hq,hεQ (mem_ball.mpr (by rw [dist_comm]; linarith))⟩

/-- Inner semicontinuity on a neighborhood is a convenient sufficient case. -/
theorem SvIscOn.svLocallyIscAtGraph {S : E → Set E} {V : Set E} {x u : E}
    (hi : SvIscOn S V) (hV : IsOpen V) (hx : x ∈ V) : SvLocallyIscAtGraph S x u :=
  ⟨V,univ,hV,hx,isOpen_univ,mem_univ _,fun a ha v hv ↦ hi a ha hv.1⟩

/-- Closing convex truncated fibers allows applying Michael's theorem.
The inverse graph estimate and invariance of domain then force the resulting
selection to take its values in the original, possibly nonclosed fibers. -/
theorem mem_svInnerLimit_inverse_of_convex_local_isc {S : E → Set E} {x u : E}
    (hu : u ∈ S x) (hi : SvLocallyIscAtGraph S x u)
    (hc : ∀ a, Convex ℝ (S a)) {k : ℝ≥0}
    (hk : LocalGraphLipschitzBound (svGraph (svInv S)) (u,x) k) :
    x ∈ svInnerLimit (svInv S) u := by
  classical
  obtain ⟨V,W,hVo,hxV,hWo,huW,hisc⟩ := hi
  obtain ⟨δ,hδ,hbound⟩ := hk
  obtain ⟨ε,hε,hεW⟩ := Metric.mem_nhds_iff.mp (hWo.mem_nhds huW)
  let r := min δ ε
  have hr : 0 < r := lt_min hδ hε
  have hrδ : r ≤ δ := min_le_left _ _
  have hrε : r ≤ ε := min_le_right _ _
  let C : E → Set E := fun a ↦ S a ∩ ball u r
  let K : E → Set E := fun a ↦ closure (C a)
  have hnear : ∀ᶠ a in 𝓝 x, (C a).Nonempty := by
    have h := hisc x hxV u ⟨hu,huW⟩ (ball u r) (ball_mem_nhds u hr)
    rwa [nhdsWithin_eq_nhds.mpr (hVo.mem_nhds hxV)] at h
  obtain ⟨U,hUsub,hUo,hxU⟩ := _root_.mem_nhds_iff.mp
    (hnear.and ((hVo.inter isOpen_ball).mem_nhds ⟨hxV,mem_ball_self hδ⟩))
  have hUC (a : E) (ha : a ∈ U) : (C a).Nonempty := (hUsub ha).1
  have hUV : U ⊆ V := fun a ha ↦ (hUsub ha).2.1
  have hUδ : U ⊆ ball x δ := fun a ha ↦ (hUsub ha).2.2
  have hKi : SvIscOn K U := by
    intro a ha v hv Q hQ
    obtain ⟨P,hPQ,hPo,hvP⟩ := _root_.mem_nhds_iff.mp hQ
    obtain ⟨b,hbP,hbC⟩ := _root_.mem_closure_iff.mp hv P hPo hvP
    have hbW : b ∈ W := hεW (ball_subset_ball hrε hbC.2)
    have h := hisc a (hUV ha) b ⟨hbC.1,hbW⟩ (P ∩ ball u r)
      (inter_mem (hPo.mem_nhds hbP) (isOpen_ball.mem_nhds hbC.2))
    filter_upwards [h.filter_mono (nhdsWithin_mono a hUV)] with y hy
    obtain ⟨b',hb'S,hb'P,hb'B⟩ := hy
    exact ⟨b',subset_closure ⟨hb'S,hb'B⟩,hPQ hb'P⟩
  have hxu : u ∈ K x := subset_closure ⟨hu,mem_ball_self hr⟩
  obtain ⟨s,hscont,hsmem,hsbase⟩ := exists_continuousOn_selection_extension
    (S := K) (X := U) (X₀ := {x})
    (fun a ha ↦ (hUC a ha).mono subset_closure)
    (fun _ _ ↦ isClosed_closure)
    (fun a _ ↦ ((hc a).inter (convex_ball u r)).closure)
    hKi isClosed_singleton (singleton_subset_iff.mpr hxU)
    (s₀ := fun _ ↦ u) continuousOn_const (fun a ha ↦ by simpa only [mem_singleton_iff.mp ha] using hxu)
  have hsx : s x = u := hsbase x (mem_singleton _)
  have hKbound (a : E) (ha : a ∈ U) (b : E) (hb : b ∈ U)
      (v : E) (hv : v ∈ K a) (q : E) (hq : q ∈ K b) :
      dist a b ≤ (k:ℝ)*dist v q := by
    have hactual (v : E) (hv : v ∈ C a) (q : E) (hq : q ∈ C b) :
        dist a b ≤ (k:ℝ)*dist v q := by
      apply hbound (v,a) ⟨hv.1,?_⟩ (q,b) ⟨hq.1,?_⟩
      · rw [← ball_prod_same]
        exact ⟨ball_subset_ball hrδ hv.2,hUδ ha⟩
      · rw [← ball_prod_same]
        exact ⟨ball_subset_ball hrδ hq.2,hUδ hb⟩
    have hqclosed (v : E) (hv : v ∈ C a) :
        ∀ q ∈ K b, dist a b ≤ (k:ℝ)*dist v q := by
      apply (isClosed_le continuous_const (continuous_const.mul (continuous_const.dist continuous_id))).closure_subset_iff.mpr
      exact hactual v hv
    apply ((isClosed_le continuous_const
      (continuous_const.mul (continuous_id.dist continuous_const))).closure_subset_iff.mpr ?_) hv
    intro v hv
    exact hqclosed v hv q hq
  have hinj : InjOn s U := by
    intro a ha b hb hab
    have hd := hKbound a ha b hb (s a) (hsmem a ha) (s b) (hsmem b hb)
    simpa only [hab,dist_self,mul_zero,dist_le_zero] using hd
  have himgOpen := isOpen_image_of_continuousOn_injective_euclidean s U hUo hscont hinj
  have hsactual (a : E) (ha : a ∈ U) : s a ∈ S a := by
    obtain ⟨v,hvimg,hvC⟩ := _root_.mem_closure_iff.mp (hsmem a ha)
      (s '' U) himgOpen ⟨a,ha,rfl⟩
    obtain ⟨b,hb,hsv⟩ := hvimg
    have hd := hKbound a ha b hb v (subset_closure hvC) (s b) (hsmem b hb)
    rw [hsv,dist_self,mul_zero,dist_le_zero] at hd
    subst b
    exact hsv.symm ▸ hvC.1
  intro Q hQ
  obtain ⟨η,hη,hηQ⟩ := Metric.mem_nhds_iff.mp hQ
  have hsmallOpen : IsOpen (U ∩ ball x η) := hUo.inter isOpen_ball
  have hsmallImg := isOpen_image_of_continuousOn_injective_euclidean s _ hsmallOpen
    (hscont.mono inter_subset_left) (hinj.mono inter_subset_left)
  have huimg : u ∈ s '' (U ∩ ball x η) := ⟨x,⟨hxU,mem_ball_self hη⟩,hsx⟩
  filter_upwards [hsmallImg.mem_nhds huimg] with v hv
  obtain ⟨a,ha,hsa⟩ := hv
  exact ⟨a,hsa ▸ hsactual a ha.1,hηQ ha.2⟩

/-- **Theorem 9.54(b)** with the necessary equal-dimension restriction:
local inner semicontinuity and convex values turn the zero strict inverse
kernel into a Lipschitz single-valued inverse localization. -/
theorem hasLipschitzInverseLocalization_iff_strictKernel_zero_of_convex
    {S : E → Set E} {x u : E} (hu : u ∈ S x)
    (hi : SvLocallyIscAtGraph S x u) (hc : ∀ a, Convex ℝ (S a)) :
    HasLipschitzSingleValuedLocalization (svInv S) u x ↔
      svInv (strictGraphicalDerivative S x u) 0 = {0} := by
  have hmem : x ∈ svInv S u := hu
  rw [← strictGraphicalDerivative_svInv]
  constructor
  · intro h
    exact (strictGraphicalDerivative_zero_iff_localGraphLipschitz hmem).mpr
      h.exists_localGraphLipschitzBound
  · intro h
    obtain ⟨k,hk⟩ := (strictGraphicalDerivative_zero_iff_localGraphLipschitz hmem).mp h
    exact hasLipschitzSingleValuedLocalization_of_localGraphLipschitz hmem
      (mem_svInnerLimit_inverse_of_convex_local_isc hu hi hc hk) hk

end RW
