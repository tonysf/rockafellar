/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Calmness and the lower subderivative

The infimum of local calmness moduli need not itself serve as a local modulus.
The directional lower bound does attain this optimal constant.
-/

import RockafellarWets.Chapter8.SubderivativeRelationships
import RockafellarWets.Chapter8.RegularSupportDuality

open Filter Set Topology Metric
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E]

/-- Formula 8(12). A local lower cone of slope `κ` supports the function value at `x`. -/
def IsCalmFromBelowAtWith (f : E → EReal) (x : E) (κ : ℝ) : Prop :=
  0 ≤ κ ∧ ∃ c : ℝ, f x = c ∧ ∀ᶠ y in 𝓝 x, ((c - κ * ‖y-x‖ : ℝ) : EReal) ≤ f y

def IsCalmFromBelowAt (f : E → EReal) (x : E) : Prop := ∃ κ, IsCalmFromBelowAtWith f x κ

/-- Calmness from above is the lower calmness of the negative function. -/
def IsCalmFromAboveAtWith (f : E → EReal) (x : E) (κ : ℝ) : Prop :=
  IsCalmFromBelowAtWith (fun y ↦ -f y) x κ

/-- Formula 8(13). The same local modulus bounds deviations in both directions. -/
def IsCalmAtWith (f : E → EReal) (x : E) (κ : ℝ) : Prop :=
  IsCalmFromBelowAtWith f x κ ∧ IsCalmFromAboveAtWith f x κ

/-- The sharp modulus of calmness from below, used at points where calmness holds. -/
noncomputable def calmFromBelowModulus (f : E → EReal) (x : E) : ℝ :=
  sInf {κ | IsCalmFromBelowAtWith f x κ}

theorem IsCalmFromBelowAt.modulus_nonneg {f : E → EReal} {x : E} (h : IsCalmFromBelowAt f x) :
    0 ≤ calmFromBelowModulus f x := le_csInf h (fun _ hκ ↦ hκ.1)

theorem IsCalmFromBelowAtWith.modulus_le {f : E → EReal} {x : E} {κ : ℝ} (h : IsCalmFromBelowAtWith f x κ) :
    calmFromBelowModulus f x ≤ κ := csInf_le (show BddBelow {r | IsCalmFromBelowAtWith f x r} from
      ⟨0,fun _ hr ↦ hr.1⟩) h

variable [NormedSpace ℝ E]

/-- The lower-bound counterpart of the real epigraph test for difference quotients. -/
theorem coe_le_differenceQuotient_iff {f : E → EReal} {x w : E} {c t α : ℝ}
    (hx : f x = c) (ht : 0 < t) :
    (α : EReal) ≤ differenceQuotient f x t w ↔ ((c + t*α : ℝ) : EReal) ≤ f (x + t • w) := by
  rw [differenceQuotient,hx]
  cases f (x + t • w) with
  | bot => rw [EReal.bot_sub, EReal.coe_mul_bot_of_pos (inv_pos.2 ht)]; simp only [le_bot_iff, EReal.coe_ne_bot]
  | top => simp [EReal.coe_mul_top_of_pos (inv_pos.2 ht)]
  | coe r =>
    rw [← EReal.coe_sub, ← EReal.coe_mul, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff,
      le_inv_mul_iff₀ ht]
    constructor <;> intro h <;> linarith

/-- Every local modulus bounds the subderivative in every direction. -/
theorem IsCalmFromBelowAtWith.le_subderivative {f : E → EReal} {x : E} {κ : ℝ}
    (h : IsCalmFromBelowAtWith f x κ) (w : E) :
    ((-κ*‖w‖ : ℝ) : EReal) ≤ subderivative f x w := by
  obtain ⟨_,c,hx,hlocal⟩ := h
  have hlim : Tendsto (fun p : ℝ × E ↦ ((-κ*‖p.2‖ : ℝ) : EReal)) (𝓝[>] (0:ℝ) ×ˢ 𝓝 w)
      (𝓝 ((-κ*‖w‖ : ℝ) : EReal)) :=
    EReal.tendsto_coe.2 (tendsto_const_nhds.mul tendsto_snd.norm)
  rw [← hlim.liminf_eq]
  refine liminf_le_liminf ?_
  filter_upwards [(tendsto_add_smul_nhds x w).eventually hlocal,
    tendsto_fst.eventually (self_mem_nhdsWithin : Ioi (0:ℝ) ∈ 𝓝[>] 0)] with p hp htp
  rw [coe_le_differenceQuotient_iff hx htp]
  simp only [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (le_of_lt htp)] at hp
  convert hp using 2
  ring

/-- A lower semicontinuous positively homogeneous function with finite value at zero
cannot take the value minus infinity anywhere. -/
theorem PositivelyHomogeneous.bot_lt_of_zero_eq_zero {g : E → EReal} (hh : PositivelyHomogeneous g)
    (hl : LowerSemicontinuous g) (h0 : g 0 = 0) (w : E) : ⊥ < g w := by
  by_contra! h
  have ht : Tendsto (fun t : ℝ ↦ (t • w,(-1 : ℝ))) (𝓝[>] 0) (𝓝 ((0:E),-1)) := by
    have hc : Continuous (fun t : ℝ ↦ (t • w,(-1 : ℝ))) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have he : ((0,-1) : E × ℝ) ∈ epigraph g := (isClosed_epigraph_of_lsc_ereal g hl).mem_of_tendsto ht (by
    filter_upwards [self_mem_nhdsWithin] with t htpos
    change g (t • w) ≤ ((-1:ℝ):EReal)
    rw [hh.2 (show 0 < t from htpos), le_bot_iff.1 h, EReal.coe_mul_bot_of_pos htpos]
    exact bot_le)
  change g 0 ≤ ((-1:ℝ):EReal) at he
  rw [h0] at he
  exact (EReal.coe_le_coe_iff.1 (show ((0:ℝ):EReal) ≤ ((-1:ℝ):EReal) from he)).not_gt (by norm_num)

variable [FiniteDimensional ℝ E]

/-- A strict lower bound on the unit sphere for the subderivative is a local
calmness modulus. Compactness makes the quotient estimates uniform in direction. -/
theorem isCalmFromBelowAtWith_of_lt_subderivative_on_sphere {f : E → EReal} {x : E} {c κ : ℝ}
    (hx : f x = c) (hκ : 0 ≤ κ) (hs : ∀ w ∈ sphere (0:E) 1, ((-κ : ℝ) : EReal) < subderivative f x w) :
    IsCalmFromBelowAtWith f x κ := by
  refine ⟨hκ,c,hx,?_⟩
  have hS : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝ˢ (sphere (0:E) 1),
      ((-κ : ℝ) : EReal) < differenceQuotient f x p.1 p.2 :=
    (isCompact_sphere (0:E) 1).mem_prod_nhdsSet_of_forall fun w hw ↦ eventually_lt_of_lt_liminf (hs w hw)
  have hU : ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ w ∈ sphere (0:E) 1, ((-κ : ℝ) : EReal) < differenceQuotient f x t w := by
    filter_upwards [hS.curry] with t ht w hw
    exact ht.self_of_nhdsSet w hw
  obtain ⟨δ,hδ,hδU⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hU
  filter_upwards [ball_mem_nhds x hδ] with y hy
  rcases eq_or_ne y x with rfl | hyx
  · simp [hx]
  · have ht : 0 < ‖y-x‖ := norm_pos_iff.2 (sub_ne_zero.2 hyx)
    have hu : ‖y-x‖⁻¹ • (y-x) ∈ sphere (0:E) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le), inv_mul_cancel₀ ht.ne']
    have hbound := (coe_le_differenceQuotient_iff hx ht).1
      (hδU ⟨ht, by simpa [mem_ball,dist_eq_norm] using hy⟩ _ hu).le
    simpa only [smul_smul,mul_inv_cancel₀ ht.ne',one_smul,add_sub_cancel,
      mul_neg, ← sub_eq_add_neg, mul_comm ‖y-x‖ κ] using hbound

variable {f : E → EReal} {x : E} {c : ℝ}

/-- **Proposition 8.32.** Calmness from below is equivalent to the lower
subderivative taking value zero at the zero direction. -/
theorem isCalmFromBelowAt_iff_subderivative_zero (hx : f x = c) :
    IsCalmFromBelowAt f x ↔ subderivative f x 0 = 0 := by
  obtain ⟨hl,hh⟩ := lowerSemicontinuous_positivelyHomogeneous_subderivative hx
  constructor
  · rintro ⟨κ,hκ⟩
    have h := hκ.le_subderivative 0
    simp only [norm_zero,mul_zero,EReal.coe_zero] at h
    exact hh.zero_eq_zero_or_bot.resolve_right (fun hb ↦ EReal.zero_ne_bot (le_bot_iff.1 (hb ▸ h)))
  · intro h0
    let B := closedBall (0:E) 1
    have h0B : (0:E) ∈ B := by simp [B]
    obtain ⟨u,hu,hmin⟩ := (hl.lowerSemicontinuousOn B).exists_isMinOn ⟨0,h0B⟩ (isCompact_closedBall _ _)
    obtain ⟨a,_,ha⟩ := EReal.exists_between_coe_real (hh.bot_lt_of_zero_eq_zero hl h0 u)
    refine ⟨max 0 (-a),isCalmFromBelowAtWith_of_lt_subderivative_on_sphere hx (le_max_left ..) (fun w hw ↦ ?_)⟩
    have hb : -max 0 (-a) ≤ a := by linarith [le_max_right 0 (-a)]
    exact (EReal.coe_le_coe_iff.2 hb).trans_lt (ha.trans_le (hmin (sphere_subset_closedBall hw)))

/-- The equivalent condition in 8.32 excluding minus infinity in every direction. -/
theorem isCalmFromBelowAt_iff_subderivative_ne_bot (hx : f x = c) :
    IsCalmFromBelowAt f x ↔ ∀ w, ⊥ < subderivative f x w := by
  obtain ⟨hl,hh⟩ := lowerSemicontinuous_positivelyHomogeneous_subderivative hx
  rw [isCalmFromBelowAt_iff_subderivative_zero hx]
  exact ⟨hh.bot_lt_of_zero_eq_zero hl, fun h ↦ hh.zero_eq_zero_or_bot.resolve_right (h 0).ne'⟩

/-- **Proposition 8.32.** The negative sharp modulus is the attained minimum
of the lower subderivative on the closed unit ball. -/
theorem IsCalmFromBelowAt.exists_unitBall_subderivative_minimizer (h : IsCalmFromBelowAt f x) :
    ∃ u ∈ closedBall (0:E) 1, subderivative f x u = ((-calmFromBelowModulus f x : ℝ) : EReal) ∧
      IsMinOn (subderivative f x) (closedBall (0:E) 1) u := by
  obtain ⟨κ,hκ⟩ := h
  obtain ⟨c,hx,_⟩ := hκ.2
  have hcalm : IsCalmFromBelowAt f x := ⟨κ,hκ⟩
  have h0 := (isCalmFromBelowAt_iff_subderivative_zero hx).mp hcalm
  have hl := (lowerSemicontinuous_positivelyHomogeneous_subderivative hx).1
  have h0B : (0:E) ∈ closedBall (0:E) 1 := by simp
  obtain ⟨u,hu,hmin⟩ := (hl.lowerSemicontinuousOn _).exists_isMinOn ⟨0,h0B⟩ (isCompact_closedBall _ _)
  have hle := (hmin h0B).trans_eq h0
  let d := (subderivative f x u).toReal
  have hfin : subderivative f x u = (d : EReal) := (EReal.coe_toReal
    (hle.trans_lt (EReal.coe_lt_top 0)).ne (((isCalmFromBelowAt_iff_subderivative_ne_bot hx).1 hcalm u).ne')).symm
  have hd : d ≤ 0 := EReal.coe_le_coe_iff.1 (hfin ▸ hle)
  have hum : ‖u‖ ≤ 1 := mem_closedBall_zero_iff.1 hu
  have heq : -d = calmFromBelowModulus f x := by
    apply le_antisymm
    · apply le_csInf hcalm
      intro r hr
      have hh := EReal.coe_le_coe_iff.1 ((IsCalmFromBelowAtWith.le_subderivative hr u).trans_eq hfin)
      nlinarith [mul_nonneg hr.1 (sub_nonneg.2 hum)]
    · apply le_of_forall_gt_imp_ge_of_dense
      intro r hr
      apply IsCalmFromBelowAtWith.modulus_le
      refine isCalmFromBelowAtWith_of_lt_subderivative_on_sphere hx (by linarith) (fun w hw ↦ ?_)
      exact (EReal.coe_lt_coe_iff.2 (by linarith : -r < d)).trans_le (hfin ▸ hmin (sphere_subset_closedBall hw))
  exact ⟨u,hu,by rw [← heq,neg_neg,hfin],hmin⟩

/-- The optimal modulus gives a sharp conical lower bound in every direction. -/
theorem IsCalmFromBelowAt.sharp_le_subderivative (h : IsCalmFromBelowAt f x) (w : E) :
    ((-calmFromBelowModulus f x * ‖w‖ : ℝ) : EReal) ≤ subderivative f x w := by
  obtain ⟨u,_,hu,hmin⟩ := h.exists_unitBall_subderivative_minimizer
  obtain ⟨κ,hκ⟩ := h
  obtain ⟨c,hx,_⟩ := hκ.2
  rcases eq_or_ne w 0 with rfl | hw
  · simp [((isCalmFromBelowAt_iff_subderivative_zero hx).1 ⟨κ,hκ⟩)]
  · have ht := norm_pos_iff.2 hw
    let z := ‖w‖⁻¹ • w
    have hz : ‖z‖ = 1 := norm_smul_inv_norm hw
    have hsq : ‖w‖ • z = w := by simp [z,smul_smul,ht.ne']
    have hle := hmin (show z ∈ closedBall (0:E) 1 by simp [hz])
    rw [hu] at hle
    have hhom := (lowerSemicontinuous_positivelyHomogeneous_subderivative hx).2.2 (x := z) ht
    rw [hsq] at hhom
    rw [hhom,mul_comm, EReal.coe_mul]
    exact mul_le_mul_of_nonneg_left hle (EReal.coe_nonneg.2 ht.le)

end RW
