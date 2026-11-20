/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: The first inclusion of Exercise 6.44 fails for closed factors

Exercise 6.44 prints, for closed `C₁, C₂ ⊂ ℝⁿ` and `x̄ = x̄₁ + x̄₂`, the
inclusion `T_{C₁}(x̄₁) + T_{C₂}(x̄₂) ⊂ T_{C₁ + C₂}(x̄)`. In the plane take
`C₁ = {0} ∪ {(2⁻ⁿ, 0)}` and `C₂ = {0} ∪ {(0, 2⁻ⁿ)}`, both compact, with
`x̄₁ = x̄₂ = 0`. Each factor has its positive coordinate ray as tangent cone
at the origin, so `(1, 3)` lies in the sum of the tangent cones. It is not
tangent to `C₁ + C₂`: a point of the sum with two positive coordinates has
coordinate ratio an integral power of two, which cannot approach `3`. The
tangent scales of the two factors cannot be synchronized, which is what the
geometric derivability hypothesis in `SetAdditionCones.lean` supplies.
-/

import RockafellarWets.Chapter6.SetAdditionCones

open Filter Metric Set Topology
open scoped BigOperators

namespace RW

namespace SetAdditionCounterexample

/-- The geometric sequence of scales `2⁻ⁿ`. -/
noncomputable def scale (n : ℕ) : ℝ := ((2 : ℝ) ^ n)⁻¹

theorem scale_pos (n : ℕ) : 0 < scale n := by
  unfold scale
  positivity

theorem scale_tendsto : Tendsto scale atTop (𝓝 0) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)
  refine h.congr fun n ↦ ?_
  simp [scale, inv_pow]

/-- The first axis direction. -/
noncomputable def e₀ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1

/-- The second axis direction. -/
noncomputable def e₁ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 1

/-- The first factor: the origin and the points `(2⁻ⁿ, 0)`. -/
noncomputable def C₁ : Set (EuclideanSpace ℝ (Fin 2)) :=
  insert 0 (range fun n ↦ scale n • e₀)

/-- The second factor: the origin and the points `(0, 2⁻ⁿ)`. -/
noncomputable def C₂ : Set (EuclideanSpace ℝ (Fin 2)) :=
  insert 0 (range fun n ↦ scale n • e₁)

theorem zero_mem_C₁ : (0 : EuclideanSpace ℝ (Fin 2)) ∈ C₁ := mem_insert _ _

theorem zero_mem_C₂ : (0 : EuclideanSpace ℝ (Fin 2)) ∈ C₂ := mem_insert _ _

theorem tendsto_scale_smul (v : EuclideanSpace ℝ (Fin 2)) :
    Tendsto (fun n ↦ scale n • v) cofinite (𝓝 0) := by
  rw [Nat.cofinite_eq_atTop]
  simpa using scale_tendsto.smul_const v

/-- Both factors are compact, hence closed. -/
theorem isCompact_C₁ : IsCompact C₁ :=
  (tendsto_scale_smul e₀).isCompact_insert_range_of_cofinite

theorem isCompact_C₂ : IsCompact C₂ :=
  (tendsto_scale_smul e₁).isCompact_insert_range_of_cofinite

theorem isClosed_C₁ : IsClosed C₁ := isCompact_C₁.isClosed

theorem isClosed_C₂ : IsClosed C₂ := isCompact_C₂.isClosed

theorem e₀_mem_tangentCone : e₀ ∈ tangentCone C₁ 0 := by
  refine mem_tangentCone_of_forall (xs := fun n ↦ scale n • e₀) (τs := scale)
    (fun n ↦ mem_insert_of_mem _ ⟨n, rfl⟩) scale_pos scale_tendsto ?_
  refine tendsto_const_nhds.congr fun n ↦ ?_
  simp [smul_smul, (scale_pos n).ne']

theorem e₁_mem_tangentCone : e₁ ∈ tangentCone C₂ 0 := by
  refine mem_tangentCone_of_forall (xs := fun n ↦ scale n • e₁) (τs := scale)
    (fun n ↦ mem_insert_of_mem _ ⟨n, rfl⟩) scale_pos scale_tendsto ?_
  refine tendsto_const_nhds.congr fun n ↦ ?_
  simp [smul_smul, (scale_pos n).ne']

/-- The direction `(1, 3)` lies in the sum of the tangent cones at the
decomposition `0 = 0 + 0`. -/
theorem mem_finiteSetSum_tangentCone :
    e₀ + (3 : ℝ) • e₁ ∈ finiteSetSum (fun i ↦ tangentCone (![C₁, C₂] i) 0) := by
  refine ⟨![e₀, (3 : ℝ) • e₁], ?_, by simp [Fin.sum_univ_two]⟩
  intro i
  fin_cases i
  · simpa using e₀_mem_tangentCone
  · simpa using (isCone_tangentCone zero_mem_C₂).2 e₁_mem_tangentCone
      (by norm_num : (0 : ℝ) < 3)

/-- Coordinates of the points of the first factor. -/
theorem coord_of_mem_C₁ {a : EuclideanSpace ℝ (Fin 2)} (ha : a ∈ C₁) :
    a 1 = 0 ∧ (a 0 = 0 ∨ ∃ k, a 0 = scale k) := by
  rcases ha with rfl | ⟨k, rfl⟩
  · simp
  · refine ⟨?_, Or.inr ⟨k, ?_⟩⟩ <;> simp [e₀]

/-- Coordinates of the points of the second factor. -/
theorem coord_of_mem_C₂ {a : EuclideanSpace ℝ (Fin 2)} (ha : a ∈ C₂) :
    a 0 = 0 ∧ (a 1 = 0 ∨ ∃ m, a 1 = scale m) := by
  rcases ha with rfl | ⟨m, rfl⟩
  · simp
  · refine ⟨?_, Or.inr ⟨m, ?_⟩⟩ <;> simp [e₁]

/-- No integral power of two lies strictly between `2.63` and `3.45`. -/
theorem not_pow_two_between {k m : ℕ}
    (h1 : (263 / 100 : ℝ) * 2 ^ m < 2 ^ k) (h2 : (2 : ℝ) ^ k < 345 / 100 * 2 ^ m) :
    False := by
  have hB : (0 : ℝ) < 2 ^ m := by positivity
  rcases le_or_gt k m with hkm | hmk
  · have : (2 : ℝ) ^ k ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hkm
    linarith
  · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hmk) with heq | hlt
    · rw [← heq, pow_succ] at h1
      linarith
    · have : (2 : ℝ) ^ (m + 2) ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
      rw [pow_add] at this
      norm_num at this
      linarith

/-- The direction `(1, 3)` is not tangent to `C₁ + C₂` at the origin. -/
theorem not_mem_tangentCone_finiteSetSum :
    e₀ + (3 : ℝ) • e₁ ∉ tangentCone (finiteSetSum ![C₁, C₂]) 0 := by
  rintro ⟨xs, τs, hxs, -, hτpos, -, hq⟩
  have hq0 : Tendsto (fun n ↦ (τs n)⁻¹ * xs n 0) atTop (𝓝 1) := by
    have h := ((PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0).tendsto _).comp hq
    simpa [e₀, e₁, Function.comp_def] using h
  have hq1 : Tendsto (fun n ↦ (τs n)⁻¹ * xs n 1) atTop (𝓝 3) := by
    have h := ((PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 1).tendsto _).comp hq
    simpa [e₀, e₁, Function.comp_def] using h
  have hev0 := hq0.eventually (Metric.ball_mem_nhds (1 : ℝ) (by norm_num : (0 : ℝ) < 1 / 10))
  have hev1 := hq1.eventually (Metric.ball_mem_nhds (3 : ℝ) (by norm_num : (0 : ℝ) < 1 / 10))
  obtain ⟨n, h0, h1⟩ := (hev0.and hev1).exists
  rw [Real.dist_eq, abs_sub_lt_iff] at h0 h1
  obtain ⟨a, ha, hsum⟩ := hxs n
  have ha0 := ha 0
  have ha1 := ha 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at ha0 ha1
  rw [Fin.sum_univ_two] at hsum
  obtain ⟨hc1, hc0⟩ := coord_of_mem_C₁ ha0
  obtain ⟨hd0, hd1⟩ := coord_of_mem_C₂ ha1
  have hs : xs n 0 = (a 0) 0 := by rw [← hsum, PiLp.add_apply, hd0, add_zero]
  have ht : xs n 1 = (a 1) 1 := by rw [← hsum, PiLp.add_apply, hc1, zero_add]
  have hτ : 0 < (τs n)⁻¹ := inv_pos.2 (hτpos n)
  have hspos : 0 < xs n 0 := by
    by_contra hle
    push_neg at hle
    have := mul_nonpos_of_nonneg_of_nonpos hτ.le hle
    linarith [h0.2]
  have htpos : 0 < xs n 1 := by
    by_contra hle
    push_neg at hle
    have := mul_nonpos_of_nonneg_of_nonpos hτ.le hle
    linarith [h1.2]
  obtain ⟨k, hk⟩ : ∃ k, xs n 0 = scale k := by
    rcases hc0 with h | ⟨k, hk⟩
    · rw [hs, h] at hspos
      exact absurd hspos (lt_irrefl 0)
    · exact ⟨k, hs.trans hk⟩
  obtain ⟨m, hm⟩ : ∃ m, xs n 1 = scale m := by
    rcases hd1 with h | ⟨m, hm⟩
    · rw [ht, h] at htpos
      exact absurd htpos (lt_irrefl 0)
    · exact ⟨m, ht.trans hm⟩
  have hlt : (263 / 100 : ℝ) * xs n 0 < xs n 1 := by
    by_contra hcon
    push_neg at hcon
    have := mul_le_mul_of_nonneg_left hcon hτ.le
    rw [mul_left_comm] at this
    linarith [h0.1, h1.2]
  have hgt : xs n 1 < (345 / 100 : ℝ) * xs n 0 := by
    by_contra hcon
    push_neg at hcon
    have := mul_le_mul_of_nonneg_left hcon hτ.le
    rw [mul_left_comm] at this
    linarith [h0.2, h1.1]
  rw [hk, hm] at hlt hgt
  unfold scale at hlt hgt
  have hA : (0 : ℝ) < 2 ^ k := by positivity
  have hB : (0 : ℝ) < 2 ^ m := by positivity
  rw [← div_eq_mul_inv, div_lt_iff₀ hA, inv_mul_eq_div, lt_div_iff₀ hB] at hlt
  rw [← div_eq_mul_inv, lt_div_iff₀ hA, inv_mul_eq_div, div_lt_iff₀ hB] at hgt
  exact not_pow_two_between hlt hgt

/-- **Exercise 6.44**, correction: the printed first inclusion fails for
these two compact plane sets at the decomposition `0 = 0 + 0`. -/
theorem not_finiteSetSum_tangentCone_subset :
    ¬ finiteSetSum (fun i ↦ tangentCone (![C₁, C₂] i) 0) ⊆
      tangentCone (finiteSetSum ![C₁, C₂]) 0 :=
  fun h ↦ not_mem_tangentCone_finiteSetSum (h mem_finiteSetSum_tangentCone)

end SetAdditionCounterexample

end RW
