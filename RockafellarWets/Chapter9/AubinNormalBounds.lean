/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: Normal estimates in the Mordukhovich criterion
-/

import RockafellarWets.Chapter9.AubinGraphicalDerivatives
import RockafellarWets.Chapter6.ProximalNormals

open Filter Metric Set Topology
open scoped InnerProductSpace NNReal ENNReal

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {S : E → Set F} {x : E} {u : F} {k l : ℝ≥0}

local notation "P" => WithLp 2 (E × F)

/-- The graphical normal inequality in 9(22), at a single base point. -/
def GraphNormalBound (S : E → Set F) (x : E) (u : F) (k : ℝ≥0) : Prop :=
  ∀ n ∈ normalCone (euclideanSvGraph S) (WithLp.toLp 2 (x,u)), ‖n.fst‖ ≤ k * ‖n.snd‖

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem graphNormalBound_iff_coderivative :
    GraphNormalBound S x u k ↔ ∀ y v, v ∈ coderivative S x u y → ‖v‖ ≤ k*‖y‖ := by
  constructor
  · intro H y v h
    simpa only [WithLp.toLp_fst,WithLp.toLp_snd,norm_neg] using H (WithLp.toLp 2 (v,-y)) h
  · intro H n hn
    have h : n.fst ∈ coderivative S x u (-n.snd) := by
      change WithLp.toLp 2 (n.fst,- -n.snd) ∈ normalCone (euclideanSvGraph S) (WithLp.toLp 2 (x,u))
      simpa only [neg_neg] using hn
    simpa only [norm_neg] using H _ _ h

omit [FiniteDimensional ℝ E] in
private theorem aubin_regularNormal_bound (h : AubinEstimate S univ x u k) (hu : u ∈ S x) {n : P}
    (hn : n ∈ regularNormalCone (euclideanSvGraph S) (WithLp.toLp 2 (x,u))) :
    ‖n.fst‖ ≤ k*‖n.snd‖ := by
  obtain ⟨z,hz,hd⟩ := h.exists_graphicalDerivative_norm_le hu n.fst
  have H := inner_nonpos_of_mem_regularNormalCone hn (show WithLp.toLp 2 (n.fst,z) ∈ _ from hz)
  rw [WithLp.prod_inner_apply] at H
  change ⟪n.fst,n.fst⟫_ℝ + ⟪n.snd,z⟫_ℝ ≤ 0 at H
  rw [real_inner_self_eq_norm_sq] at H
  have h₁ := (neg_le_abs ⟪n.snd,z⟫_ℝ).trans (abs_real_inner_le_norm n.snd z)
  have h₂ := mul_le_mul_of_nonneg_left hd (norm_nonneg n.snd)
  by_cases he : ‖n.fst‖ = 0
  · rw [he]; positivity
  · apply le_of_mul_le_mul_right (a := ‖n.fst‖) _ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm he))
    nlinarith

omit [FiniteDimensional ℝ E] in
/-- Necessity in **Theorem 9.40**. An actual Aubin constant bounds every
limiting normal to the graph. -/
theorem AubinEstimate.graphNormalBound (h : AubinEstimate S univ x u k) : GraphNormalBound S x u k := by
  intro n hn
  obtain ⟨_,q,s,hq,hq₀,hs,hs₀⟩ := hn
  let L := WithLp.prodContinuousLinearEquiv 2 ℝ E F
  have hnear := ((L.continuous.tendsto _).comp hq₀).eventually h.eventually
  apply le_of_tendsto_of_tendsto (((WithLp.continuous_fst 2 E F).tendsto _).comp hs₀).norm
    (tendsto_const_nhds.mul (((WithLp.continuous_snd 2 E F).tendsto _).comp hs₀).norm)
  filter_upwards [hnear] with i hi
  exact aubin_regularNormal_bound hi (hq i) (hs i)

/-- Compactness of normalized normals upgrades a bound at the base to a
uniform bound on nearby graph normals, with any strictly larger constant. -/
theorem GraphNormalBound.eventually_of_lt (h : GraphNormalBound S x u k) (hu : u ∈ S x) (hkl : k < l) :
    ∀ᶠ p : P in 𝓝 (WithLp.toLp 2 (x,u)), GraphNormalBound S p.fst p.snd l := by
  by_contra H
  obtain ⟨q,hq,hfail⟩ := exists_seq_forall_of_frequently (not_eventually.mp H)
  have he (i : ℕ) : ∃ n ∈ normalCone (euclideanSvGraph S) (q i), (l:ℝ)*‖n.snd‖ < ‖n.fst‖ := by
    simpa [GraphNormalBound,not_forall,not_le] using hfail i
  choose n hn hbad using he
  have hne (i : ℕ) : n i ≠ 0 := by
    intro heq
    have hh := hbad i
    simp [heq] at hh
  let m i := ‖n i‖⁻¹ • n i
  have hm (i : ℕ) : ‖m i‖ = 1 := by simp [m,norm_smul_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),hne i]
  obtain ⟨m₀,hm₀,φ,hφ,hlim⟩ := (isCompact_sphere (0:P) 1).tendsto_subseq
    (fun i ↦ mem_sphere_zero_iff_norm.mpr (hm i))
  have hnormal : m₀ ∈ normalCone (euclideanSvGraph S) (WithLp.toLp 2 (x,u)) :=
    mem_normalCone_of_tendsto (show WithLp.toLp 2 (x,u) ∈ euclideanSvGraph S from hu) (fun i ↦ (hn (φ i)).1) (hq.comp hφ.tendsto_atTop)
      (fun i ↦ (isCone_normalCone (hn (φ i)).1).2 (hn (φ i)) (inv_pos.mpr (norm_pos_iff.mpr (hne _)))) hlim
  have h₁ : (l:ℝ)*‖m₀.snd‖ ≤ ‖m₀.fst‖ := by
    apply le_of_tendsto_of_tendsto (tendsto_const_nhds.mul (((WithLp.continuous_snd 2 E F).tendsto _).comp hlim).norm)
      (((WithLp.continuous_fst 2 E F).tendsto _).comp hlim).norm
    filter_upwards with i
    let j := φ i
    change (l:ℝ)*‖‖n j‖⁻¹ • (n j).snd‖ ≤ ‖‖n j‖⁻¹ • (n j).fst‖
    rw [norm_smul_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),norm_smul_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left (hbad j).le (inv_nonneg.mpr (norm_nonneg _))
  have h₂ := h m₀ hnormal
  have hs : ‖m₀.snd‖ = 0 := by
    by_contra hs
    exact ((mul_lt_mul_of_pos_right (show (k:ℝ) < l from hkl) (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hs))).trans_le h₁).not_ge h₂
  have hf : ‖m₀.fst‖ = 0 := le_antisymm (by simpa only [hs,mul_zero] using h₂) (norm_nonneg _)
  have hzero : m₀ = 0 := by
    exact WithLp.ofLp_injective 2 (Prod.ext (norm_eq_zero.mp hf) (norm_eq_zero.mp hs))
  simpa [hzero] using (mem_sphere_zero_iff_norm.mp hm₀)

end RW
