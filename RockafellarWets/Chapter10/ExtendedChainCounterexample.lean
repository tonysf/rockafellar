/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Horizon scalarizations in the regular case of 10.49
-/
import RockafellarWets.Chapter10.SumRegularityCounterexample
import RockafellarWets.Chapter10.StrictlyContinuousMaxima
import RockafellarWets.Chapter8.NegativeNorm

open Filter Set Topology
open scoped InnerProductSpace Pointwise

namespace RW

/-- At the endpoint of the negative square root there is no finite supporting slope. -/
theorem subdifferential_negativeRoot_zero : subdifferential negativeRoot 0 = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro v hv
  let t : ℝ := (|v|+1)⁻¹
  have ht : 0 < t := by dsimp [t]; positivity
  have h := (mem_subdifferential_iff_of_convex convex_epigraph_negativeRoot negativeRoot_isProper
    (c := 0) negativeRoot_zero).mp hv (t^2)
  simp only [negativeRoot,if_pos (sq_nonneg t),Real.sqrt_sq ht.le,sub_zero,zero_add,
    real_inner_eq_mul',EReal.coe_le_coe_iff] at h
  have hgt : -1 < v*t := by
    dsimp [t]; rw [← div_eq_mul_inv,lt_div_iff₀ (by positivity : 0 < |v|+1)]
    linarith [neg_abs_le v]
  nlinarith [mul_lt_mul_of_pos_right hgt ht]

private theorem negativeRoot_abs_not_regular :
    ¬ IsSubdifferentiallyRegularAt (fun x : ℝ ↦ negativeRoot |x|) 0 := by
  let f : ℝ → EReal := fun x ↦ negativeRoot |x|
  have h0 : f 0 = ((0:ℝ):EReal) := by simp [f]
  let t (n : ℕ) : ℝ := 1 / ((n:ℝ)+1)
  have ht (n : ℕ) : 0 < t n := by dsimp [t]; positivity
  have ht0 : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hval (n : ℕ) : f ((t n)^2) = ((-t n:ℝ):EReal) := by
    simp [f,negativeRoot,abs_of_nonneg (sq_nonneg (t n)),Real.sqrt_sq (ht n).le]
  have hhor : (-1:ℝ) ∈ horizonSubdifferential f 0 := by
    apply (mem_horizonSubdifferential_iff_zero_or_scaledSeq h0).mpr
    refine Or.inr ⟨fun n ↦ (t n)^2,fun n ↦ -(2*t n)⁻¹,fun n ↦ 2*t n,
      tendsto_attentiveNhds_iff.mpr ⟨by simpa using ht0.pow 2,?_⟩,?_,
      fun n ↦ by positivity,by simpa only [mul_zero] using ht0.const_mul 2,?_⟩
    · simpa only [Function.comp_def,hval,h0,neg_zero] using
        continuous_coe_real_ereal.continuousAt.tendsto.comp ht0.neg
    · intro n
      have he : f =ᶠ[𝓝 ((t n)^2)] negativeRoot := by
        filter_upwards [Ioi_mem_nhds (sq_pos_of_pos (ht n))] with z hz
        exact congrArg negativeRoot (abs_of_pos hz)
      rw [regularSubdifferential_congr_nhds_of_finite (hval n) he]
      exact negativeRoot_regularSubgradient_sq (ht n)
    · have hscale (n : ℕ) : (2*t n) • (-(2*t n)⁻¹) = (-1:ℝ) := by
        rw [smul_eq_mul,mul_neg,mul_inv_cancel₀ (mul_ne_zero (by norm_num) (ht n).ne')]
      simp only [hscale]
      exact tendsto_const_nhds
  intro hr
  have hn := (hr.mem_horizonSubdifferential_iff_regularNormal h0).mp hhor
  let w := WithLp.toLp 2 ((-1:ℝ),(0:ℝ))
  have hmem (n : ℕ) : t n • w ∈ euclideanEpigraph f := by
    change negativeRoot |t n*(-1)| ≤ ((t n*0:ℝ):EReal)
    simp [negativeRoot,abs_nonneg,Real.sqrt_nonneg]
  have hw : w ∈ tangentCone (euclideanEpigraph f) (WithLp.toLp 2 ((0:ℝ),(0:ℝ))) := by
    apply mem_tangentCone_of_forall hmem ht ht0
    simpa only [show WithLp.toLp 2 ((0:ℝ),(0:ℝ)) = 0 from rfl, sub_zero,smul_smul,
      inv_mul_cancel₀ (ht _).ne',one_smul] using (tendsto_const_nhds (x := w) (f := atTop))
  have h := inner_nonpos_of_mem_regularNormalCone hn hw
  norm_num [w,WithLp.prod_inner_apply] at h

/-- The printed 10.49 regularity assumptions hold with `g = negativeRoot`
and `F = abs`. Ordinary scalarization regularity is vacuous, and the horizon
qualification holds, but the composite fails to be regular. -/
theorem extended_chain_regularity_counterexample :
    ∃ (g : ℝ → EReal) (F : ℝ → ℝ), LowerSemicontinuous g ∧ StrictlyContinuousAt F 0 ∧
      g (F 0) = 0 ∧ IsSubdifferentiallyRegularAt g (F 0) ∧
      (∀ y ∈ subdifferential g (F 0),
        IsSubdifferentiallyRegularAt (fun a ↦ ((⟪y,F a⟫_ℝ:ℝ):EReal)) 0) ∧
      (∀ y ∈ horizonSubdifferential g (F 0),
        (0:ℝ) ∈ subdifferential (fun a ↦ ((⟪y,F a⟫_ℝ:ℝ):EReal)) 0 → y = 0) ∧
      ¬ IsSubdifferentiallyRegularAt (g ∘ F) 0 := by
  refine ⟨negativeRoot,abs,negativeRoot_lowerSemicontinuous,
    strictlyContinuousAt_iff.mpr ⟨1,univ,univ_mem,lipschitzWith_one_norm.lipschitzOnWith⟩,
    by simp,by simpa using negativeRoot_regular,by simp [subdifferential_negativeRoot_zero],?_,negativeRoot_abs_not_regular⟩
  intro y hy hz
  rw [abs_zero] at hy
  have hN := horizonSubdifferential_subset_normalCone_domain convex_epigraph_negativeRoot
    negativeRoot_isProper (c := 0) negativeRoot_zero hy
  rw [normalCone_eq_of_convex (convex_effectiveDomain_of_convex_epigraph convex_epigraph_negativeRoot)
    (show (0:ℝ) ∈ effectiveDomain negativeRoot from by simp [effectiveDomain])] at hN
  have hy0 : y ≤ 0 := by
    have h := hN 1 (show (1:ℝ) ∈ effectiveDomain negativeRoot by
      change negativeRoot 1 < ⊤
      rw [negativeRoot,if_pos (by norm_num : (0:ℝ) ≤ 1)]
      exact EReal.coe_lt_top _)
    simpa using h
  by_contra hne
  have hpos := neg_pos.mpr (lt_of_le_of_ne hy0 hne)
  have hL : StrictlyContinuousAt (fun x : ℝ ↦ -‖x‖) 0 :=
    strictlyContinuousAt_iff.mpr ⟨1,univ,univ_mem,lipschitzWith_one_norm.neg.lipschitzOnWith⟩
  have he : (fun a : ℝ ↦ ((⟪y,|a|⟫_ℝ:ℝ):EReal)) = (fun a : ℝ ↦ (((-y)*(-‖a‖):ℝ):EReal)) := by
    funext a; rw [real_inner_eq_mul',Real.norm_eq_abs,neg_mul_neg]
  rw [he,subdifferential_const_mul hL hpos] at hz
  obtain ⟨v,hv,hvz⟩ := hz
  change -y*v = 0 at hvz
  have hv0 := (mul_eq_zero.mp hvz).resolve_left hpos.ne'
  change v ∈ subdifferential negNorm 0 at hv
  rw [hv0,subdifferential_negNorm_zero,frontier_closedBall _ one_ne_zero,mem_sphere_zero_iff_norm] at hv
  norm_num at hv

end RW
