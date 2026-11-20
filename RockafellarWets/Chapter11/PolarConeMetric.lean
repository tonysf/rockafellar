/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Isometry of cone polarity
-/

import RockafellarWets.Chapter4.ConeSetDistances
import RockafellarWets.Chapter6.Polarity
import RockafellarWets.Chapter6.ProximalNormals
import RockafellarWets.Chapter8.DistanceSubderivatives
import RockafellarWets.Chapter3.HomogeneousCompletion

open Metric Set
open scoped InnerProductSpace NNReal
namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Orthogonality and bipolar membership of the residual of a cone projection. -/
theorem cone_projection_residual {K : Set E} (hc : Convex ℝ K) (hk : IsCone K)
    {v p : E} (hp : p ∈ projMapping K v) :
    v - p ∈ polarCone K ∧ ⟪v - p, p⟫_ℝ = 0 := by
  have hpm := (mem_projMapping.mp hp).1
  have hn := sub_mem_regularNormalCone_of_mem_projMapping hp
  rw [regularNormalCone_eq_of_convex hc hpm] at hn
  have hz := hn 0 hk.1
  have htwo := hn (2 • p) (hk.smul_mem hpm (by norm_num : (0:ℝ) ≤ 2))
  simp only [zero_sub, inner_neg_right] at hz
  rw [inner_sub_right, real_inner_smul_right] at htwo
  have horth : ⟪v-p,p⟫_ℝ = 0 := by linarith
  exact ⟨fun w hw ↦ by have := hn w hw; rw [inner_sub_right,horth,sub_zero] at this; exact this,
    horth⟩

/-- A polar unit vector evaluates every point below its distance to the cone. -/
theorem inner_le_infDist_of_mem_polarCone {K : Set E} (hK : IsClosed K)
    (hne : K.Nonempty) {v : E} (hv : v ∈ polarCone K) (hn : ‖v‖ ≤ 1) (x : E) :
    ⟪v,x⟫_ℝ ≤ infDist x K := by
  obtain ⟨p,hp⟩ := projMapping_nonempty hK hne x
  have hpm := (mem_projMapping.mp hp).1
  have hi := real_inner_le_norm v (x-p)
  have hn' := mul_le_mul_of_nonneg_right hn (norm_nonneg (x-p))
  rw [one_mul,norm_sub_eq_infDist hp] at hn'
  rw [inner_sub_right,norm_sub_eq_infDist hp] at hi
  linarith [hv p hpm]

/-- Formula **11(14)**, the one-sided estimate underlying polar isometry. -/
theorem polarCone_unit_distance_bound {K L : Set E} (hK : IsClosed K)
    (hk : IsCone K) (hL : IsClosed L) (hl : Convex ℝ L) (hlk : IsCone L)
    {e : ℝ} (he : 0 ≤ e)
    (h : ∀ x ∈ closedBall (0:E) 1, infDist x K ≤ infDist x L + e)
    {v : E} (hv : v ∈ polarCone K) (hvn : ‖v‖ ≤ 1) :
    infDist v (polarCone L) ≤ e := by
  obtain ⟨p,hp⟩ := projMapping_nonempty (isClosed_polarCone L) ⟨0,zero_mem_polarCone L⟩ v
  obtain ⟨hq,ho⟩ := cone_projection_residual (convex_polarCone L) (isCone_polarCone L) hp
  rw [polarCone_bipolar_eq_self hL hl hlk] at hq
  let q := v-p
  have hn : ‖q‖ = infDist v (polarCone L) := norm_sub_eq_infDist hp
  by_cases hq0 : q = 0
  · rw [← hn,hq0,norm_zero]; exact he
  have hqn : 0 < ‖q‖ := norm_pos_iff.mpr hq0
  let w := ‖q‖⁻¹ • q
  have hw : w ∈ L := hlk.smul_mem hq (inv_nonneg.mpr hqn.le)
  have hwn : ‖w‖ = 1 := by simp [w,norm_smul,Real.norm_eq_abs,abs_of_pos hqn,hqn.ne']
  have hwb : w ∈ closedBall (0:E) 1 := by simp only [mem_closedBall,dist_zero_right,hwn,le_refl]
  have hvq : ⟪v,q⟫_ℝ = ‖q‖^2 := by
    have hv : v = q+p := by dsimp [q]; module
    rw [hv,inner_add_left,real_inner_self_eq_norm_sq]
    have hzero : ⟪p,q⟫_ℝ = 0 := by simpa only [q,real_inner_comm] using ho
    rw [hzero,add_zero]
  have hvw : ⟪v,w⟫_ℝ = ‖q‖ := by
    change ⟪v, ‖q‖⁻¹ • q⟫_ℝ = ‖q‖
    rw [real_inner_smul_right,hvq]
    field_simp
  calc
    infDist v (polarCone L) = ⟪v,w⟫_ℝ := hn.symm.trans hvw.symm
    _ ≤ infDist w K := inner_le_infDist_of_mem_polarCone hK ⟨0,hk.1⟩ hv hvn w
    _ ≤ infDist w L + e := h w hwb
    _ = e := by rw [infDist_zero_of_mem hw,zero_add]

private theorem rhoDistance_polarCone_le {K L : Set E} (hK : IsClosed K)
    (hk : IsCone K) (hkc : Convex ℝ K) (hL : IsClosed L) (hlk : IsCone L)
    (hlc : Convex ℝ L) :
    rhoDistance 1 (polarCone K) (polarCone L) ≤ rhoDistance 1 K L := by
  rw [← rhoHatDistance_eq_rhoDistance_of_isCone 1 (isClosed_polarCone K)
    (isClosed_polarCone L) (isCone_polarCone K) (isCone_polarCone L)]
  apply (rhoHatDistance_le_iff 1 ⟨0,zero_mem_polarCone K⟩ ⟨0,zero_mem_polarCone L⟩
    (rhoDistance_nonneg 1 K L)).mpr
  constructor
  · intro v hv
    rw [mem_cthickening_iff]
    apply (ENNReal.le_ofReal_iff_toReal_le (infEDist_ne_top ⟨0,zero_mem_polarCone L⟩)
      (rhoDistance_nonneg 1 K L)).mpr
    apply polarCone_unit_distance_bound hK hk hL hlc hlk (rhoDistance_nonneg 1 K L) _ hv.1
      (by simpa only [mem_closedBall,dist_zero_right] using hv.2)
    intro x hx
    have hi := (abs_le.mp (abs_infDist_sub_infDist_le_rhoDistance 1 K L hx)).2
    linarith
  · intro v hv
    rw [mem_cthickening_iff]
    apply (ENNReal.le_ofReal_iff_toReal_le (infEDist_ne_top ⟨0,zero_mem_polarCone K⟩)
      (rhoDistance_nonneg 1 K L)).mpr
    apply polarCone_unit_distance_bound hL hlk hK hkc hk (rhoDistance_nonneg 1 K L) _ hv.1
      (by simpa only [mem_closedBall,dist_zero_right] using hv.2)
    intro x hx
    have hi := (abs_le.mp (abs_infDist_sub_infDist_le_rhoDistance 1 K L hx)).1
    linarith

/-- **Theorem 11.36**, for closed convex cones, at every truncation radius. -/
theorem rhoDistance_polarCone {K L : Set E} (hK : IsClosed K)
    (hk : IsCone K) (hkc : Convex ℝ K) (hL : IsClosed L) (hlk : IsCone L)
    (hlc : Convex ℝ L) (r : ℝ≥0) :
    rhoDistance r (polarCone K) (polarCone L) = rhoDistance r K L := by
  have hone : rhoDistance 1 (polarCone K) (polarCone L) = rhoDistance 1 K L := by
    apply le_antisymm (rhoDistance_polarCone_le hK hk hkc hL hlk hlc)
    have hr := rhoDistance_polarCone_le (isClosed_polarCone K) (isCone_polarCone K)
      (convex_polarCone K) (isClosed_polarCone L) (isCone_polarCone L) (convex_polarCone L)
    simpa only [polarCone_bipolar_eq_self hK hkc hk, polarCone_bipolar_eq_self hL hlc hlk] using hr
  rw [rhoDistance_isCone_eq (isCone_polarCone K) (isCone_polarCone L),
    rhoDistance_isCone_eq hk hlk,hone]

/-- **Theorem 11.36**, polarity is an isometry on convex cones, without a
closedness assumption. -/
theorem integratedSetDistance_polarCone {K L : Set E} (hk : IsCone K)
    (hkc : Convex ℝ K) (hlk : IsCone L) (hlc : Convex ℝ L) :
    integratedSetDistance (polarCone K) (polarCone L) = integratedSetDistance K L := by
  rw [integratedSetDistance_isCone_eq (isCone_polarCone K) (isCone_polarCone L),
    integratedSetDistance_isCone_eq hk hlk]
  have h := rhoDistance_polarCone isClosed_closure hk.closure hkc.closure
    isClosed_closure hlk.closure hlc.closure 1
  simpa only [polarCone_closure,rhoDistance_closure] using h

end RW
