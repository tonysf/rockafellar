/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Exact outer norms of cone-multiplier mappings
-/

import RockafellarWets.Chapter9.HomogeneousMappingNorms
import RockafellarWets.Chapter4.ConeSetDistances

open Filter Metric Set Topology
open scoped NNReal ENNReal

namespace RW

variable {E G P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  {K : Set E} {N : Set G} {B : G →L[ℝ] E} {T : G →L[ℝ] P}

/-- Multipliers in `N`, with the state normal absorbed by `K`. -/
def coneMultiplierMapping (K : Set E) (N : Set G) (B : G →L[ℝ] E) (T : G →L[ℝ] P) (v : E) : Set P :=
  T '' {y | y ∈ N ∧ -(v+B y) ∈ K}

private theorem multiplier_distance_pos (hK : IsCone K) (hKcl : IsClosed K)
    (hCQ : ∀ y ∈ N, -(B y) ∈ K → y = 0) {y : G} (hy : y ∈ N) (hy0 : y ≠ 0) :
    0 < infDist (-(B y)) K :=
  (hKcl.notMem_iff_infDist_pos ⟨0,hK.1⟩).mp (fun hn ↦ hy0 (hCQ y hy hn))

private theorem multiplier_ratio_smul (hK : IsCone K) {t : ℝ} (ht : 0 < t) (y : G) :
    ‖T (t • y)‖ / infDist (-(B (t • y))) K = ‖T y‖ / infDist (-(B y)) K := by
  rw [map_smul,map_smul,norm_smul,Real.norm_of_nonneg ht.le,← smul_neg,hK.infDist_smul ht]
  exact mul_div_mul_left _ _ ht.ne'

private theorem multiplier_ratio_le_outerNorm (hK : IsCone K) (hKcl : IsClosed K) (hN : IsCone N)
    (hCQ : ∀ y ∈ N, -(B y) ∈ K → y = 0) {y : G} (hy : y ∈ N) (hy0 : y ≠ 0) :
    ENNReal.ofReal (‖T y‖ / infDist (-(B y)) K) ≤ svOuterNorm (coneMultiplierMapping K N B T) := by
  let d := infDist (-(B y)) K
  have hd : 0 < d := multiplier_distance_pos hK hKcl hCQ hy hy0
  obtain ⟨n,hn,hmin⟩ := hKcl.exists_infDist_eq_dist ⟨0,hK.1⟩ (-(B y))
  let v := -(B y)-n
  have hv : ‖v‖ = d := by simpa only [v,dist_eq_norm] using hmin.symm
  have hnorm : ‖d⁻¹ • v‖ ≤ 1 := by rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hd.le),hv,inv_mul_cancel₀ hd.ne']
  have hmem : T (d⁻¹ • y) ∈ coneMultiplierMapping K N B T (d⁻¹ • v) := by
    refine ⟨d⁻¹ • y,⟨hN.smul_mem hy (by positivity),?_⟩,rfl⟩
    have he : -(d⁻¹ • v+B (d⁻¹ • y)) = d⁻¹ • n := by rw [map_smul]; dsimp [v]; module
    rw [he]
    exact hK.smul_mem hn (by positivity)
  have hh := coe_nnnorm_le_svOuterNorm hnorm hmem
  rw [← ENNReal.ofReal_coe_nnreal,coe_nnnorm,map_smul,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hd.le)] at hh
  simpa only [div_eq_mul_inv,mul_comm] using hh

/-- The outer norm is the unit-multiplier quotient, including a zero
supremum when the multiplier cone has no unit vectors. -/
theorem svOuterNorm_coneMultiplierMapping (hK : IsCone K) (hKcl : IsClosed K) (hN : IsCone N)
    (hCQ : ∀ y ∈ N, -(B y) ∈ K → y = 0) :
    svOuterNorm (coneMultiplierMapping K N B T) =
      ⨆ y : {y : G // y ∈ N ∧ ‖y‖ = 1}, ENNReal.ofReal (‖T y‖ / infDist (-(B y)) K) := by
  apply le_antisymm
  · apply svOuterNorm_le_iff_ball.mpr
    intro v hv z hz
    obtain ⟨y,hy,rfl⟩ := hz
    by_cases hy0 : y = 0
    · simp [hy0]
    have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    have hd := multiplier_distance_pos hK hKcl hCQ hy.1 hy0
    have hdy : infDist (-(B y)) K ≤ 1 := by
      have hh := infDist_le_dist_of_mem (x := -(B y)) hy.2
      have he : -(B y) - (-(v+B y)) = v := by abel
      rw [dist_eq_norm,he] at hh
      exact hh.trans hv
    let y' := ‖y‖⁻¹ • y
    have hy'N : y' ∈ N := hN.smul_mem hy.1 (by positivity)
    have hy'n : ‖y'‖ = 1 := by dsimp [y']; rw [norm_smul,Real.norm_of_nonneg (by positivity),inv_mul_cancel₀ hyn.ne']
    have hh : ‖T y‖ ≤ ‖T y‖ / infDist (-(B y)) K := by
      apply (le_div_iff₀ hd).mpr
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hdy (norm_nonneg (T y))
    have he := multiplier_ratio_smul (B := B) (T := T) hK (inv_pos.mpr hyn) y
    calc
      _ = ENNReal.ofReal ‖T y‖ := by rw [← ENNReal.ofReal_coe_nnreal]; rfl
      _ ≤ ENNReal.ofReal (‖T y‖ / infDist (-(B y)) K) := ENNReal.ofReal_le_ofReal hh
      _ = ENNReal.ofReal (‖T y'‖ / infDist (-(B y')) K) := congrArg ENNReal.ofReal he.symm
      _ ≤ _ := le_iSup (fun q : {q : G // q ∈ N ∧ ‖q‖ = 1} ↦ ENNReal.ofReal (‖T q‖ / infDist (-(B q)) K)) ⟨y',hy'N,hy'n⟩
  · refine iSup_le fun y ↦ ?_
    exact multiplier_ratio_le_outerNorm hK hKcl hN hCQ y.2.1 (by
      intro he; simpa [he] using y.2.2)

/-- The quotient attains its maximum on a nonempty closed cone's unit section. -/
theorem exists_max_coneMultiplierMapping (hK : IsCone K) (hKcl : IsClosed K)
    (hN : IsCone N) (hNcl : IsClosed N) (hCQ : ∀ y ∈ N, -(B y) ∈ K → y = 0)
    (hne : (N ∩ sphere (0:G) 1).Nonempty) :
    ∃ y ∈ N, ‖y‖ = 1 ∧ svOuterNorm (coneMultiplierMapping K N B T) =
      ENNReal.ofReal (‖T y‖ / infDist (-(B y)) K) := by
  let f := fun y : G ↦ ‖T y‖ / infDist (-(B y)) K
  have hcont : ContinuousOn f (N ∩ sphere (0:G) 1) := by
    apply T.continuous.norm.continuousOn.div
      ((continuous_infDist_pt K).comp B.continuous.neg).continuousOn
    intro y hy
    exact (multiplier_distance_pos hK hKcl hCQ hy.1 (by
      intro he; simpa [he] using hy.2)).ne'
  obtain ⟨y,hy,hm⟩ := ((isCompact_sphere (0:G) 1).inter_left hNcl).exists_isMaxOn hne hcont
  refine ⟨y,hy.1,mem_sphere_zero_iff_norm.mp hy.2,?_⟩
  rw [svOuterNorm_coneMultiplierMapping hK hKcl hN hCQ]
  apply le_antisymm (iSup_le fun z ↦ ENNReal.ofReal_le_ofReal (hm ⟨z.2.1,mem_sphere_zero_iff_norm.mpr z.2.2⟩))
  exact le_iSup (fun q : {q : G // q ∈ N ∧ ‖q‖ = 1} ↦ ENNReal.ofReal (‖T q‖ / infDist (-(B q)) K))
    ⟨y,hy.1,mem_sphere_zero_iff_norm.mp hy.2⟩

end RW
