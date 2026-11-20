/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: Single-valued derivatives and differentiability

Exercise 9.25(a,b), including the first-order expansion.
-/

import RockafellarWets.Chapter9.CalmGraphicalDerivatives
import Mathlib.Analysis.Calculus.FDeriv.Basic

open Asymptotics Filter Metric Set Topology
open scoped NNReal ENNReal

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  {f A : E → F} {x : E}

/-- For singleton-valued mappings, semidifferentiability already gives
calmness: the inner limit near the zero direction controls every quotient. -/
theorem HasMappingSemiderivative.calmAt_singleton
    (h : HasMappingSemiderivative (svSingleton f) x (f x) (svSingleton A)) : CalmAt f x := by
  have hom := (h.properties (show f x ∈ svSingleton f x from rfl)).2.1
  have hA0 : A 0 = 0 := (mem_singleton_iff.mp hom.1).symm
  have hi := (h 0).1.ge (show A 0 ∈ svSingleton A 0 from rfl)
    (ball 0 1) (by simpa [hA0] using ball_mem_nhds (0:F) one_pos)
  obtain ⟨T,hT,W,hW,hTW⟩ := mem_prod_iff.mp hi
  obtain ⟨a,ha,haT⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hT
  have ha : 0 < a := ha
  obtain ⟨b,hb,hbW⟩ := Metric.mem_nhds_iff.mp hW
  let k : ℝ≥0 := ⟨2/b,by positivity⟩
  refine ⟨k,?_⟩
  filter_upwards [ball_mem_nhds x (show 0 < a*b/4 by positivity)] with y hy
  by_cases hyx : y = x
  · simp [hyx]
  have hn : 0 < ‖y-x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyx)
  let t : ℝ := 2*‖y-x‖/b
  let w : E := t⁻¹ • (y-x)
  have ht : 0 < t := by dsimp [t]; positivity
  have hta : t < a := by
    have hh : ‖y-x‖ < a*b/4 := by simpa [dist_eq_norm] using hy
    dsimp [t]
    apply (div_lt_iff₀ hb).mpr
    nlinarith
  have hw : ‖w‖ = b/2 := by
    dsimp [w]
    rw [norm_smul_of_nonneg (inv_pos.mpr ht).le]
    dsimp [t]
    field_simp
  have htw : x+t•w = y := by
    dsimp [w]
    rw [smul_inv_smul₀ ht.ne',add_sub_cancel]
  obtain ⟨z,hz,hzB⟩ := hTW (a := (t,w)) ⟨haT ⟨ht,hta⟩,hbW (by
    rw [mem_ball,dist_zero_right,hw]; linarith)⟩
  obtain ⟨v,hv,hvz⟩ := hz
  have hv' : v = f y := by simpa only [htw] using hv
  change t⁻¹ • (v-f x) = z at hvz
  have hnz : ‖t⁻¹ • (f y-f x)‖ < 1 := by
    rw [← hv',hvz]
    exact mem_ball_zero_iff.mp hzB
  rw [norm_smul_of_nonneg (inv_pos.mpr ht).le,inv_mul_lt_iff₀ ht] at hnz
  rw [dist_eq_norm,dist_eq_norm]
  change ‖f y-f x‖ ≤ (2/b)*‖y-x‖
  have he : t*1 = (2/b)*‖y-x‖ := by dsimp [t]; ring
  exact he ▸ hnz.le

/-- **Exercise 9.25(a)**: the graphical derivative is the single-valued
semiderivative exactly when calmness holds and that derivative is single-valued. -/
theorem hasMappingSemiderivative_singleton_iff_calm_graphical :
    HasMappingSemiderivative (svSingleton f) x (f x) (svSingleton A) ↔
      CalmAt f x ∧ graphicalDerivative (svSingleton f) x (f x) = svSingleton A := by
  exact ⟨fun h ↦ ⟨h.calmAt_singleton,h.protoDerivative.2⟩,
    fun h ↦ hasMappingSemiderivative_of_linearGrowth h.2 (calmAt_iff_mappingLinearGrowth.mp h.1)⟩

/-- Formula 9(6), with its continuous positive-homogeneity conclusion. -/
theorem hasMappingSemiderivative_singleton_iff_expansion :
    HasMappingSemiderivative (svSingleton f) x (f x) (svSingleton A) ↔
      Continuous A ∧ SvPositivelyHomogeneous (svSingleton A) ∧
        HasMappingFirstOrderExpansion (svSingleton f) x (f x) A := by
  rw [hasMappingSemiderivative_singleton_iff_calm_graphical,calmAt_iff_mappingLinearGrowth,and_comm]
  exact graphicalDerivative_and_linearGrowth_iff_expansion

/-- **Exercise 9.25(b)**: linear graphical derivatives and calmness are
precisely ordinary differentiability. -/
theorem hasFDerivAt_iff_calm_graphical {L : E →L[ℝ] F} :
    HasFDerivAt f L x ↔ CalmAt f x ∧
      graphicalDerivative (svSingleton f) x (f x) = svSingleton L := by
  constructor
  · intro h
    have he : HasMappingFirstOrderExpansion (svSingleton f) x (f x) L := by
      intro ε hε
      filter_upwards [h.isLittleO.def hε] with y hy
      exact ⟨singleton_nonempty _,fun v hv ↦ by simpa only [show v = f y from hv] using hy⟩
    have hom : SvPositivelyHomogeneous (svSingleton L) :=
      ⟨by simp [svSingleton],fun w t ht ↦ by simp [svSingleton,map_smul,smul_set_singleton]⟩
    obtain ⟨hd,hc⟩ := graphicalDerivative_and_linearGrowth_of_expansion L.continuous hom he
    exact ⟨calmAt_iff_mappingLinearGrowth.mpr hc,hd⟩
  · rintro ⟨hc,hd⟩
    have he := (expansion_of_graphicalDerivative_and_linearGrowth hd
      (calmAt_iff_mappingLinearGrowth.mp hc)).2.2
    apply HasFDerivAtFilter.of_isLittleO
    apply IsLittleO.of_bound
    intro ε hε
    filter_upwards [he ε hε] with y hy
    exact hy.2 (f y) rfl

end RW
