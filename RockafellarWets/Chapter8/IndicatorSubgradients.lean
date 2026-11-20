/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Indicator subgradients and normal cones
-/

import RockafellarWets.Chapter8.SubdifferentialRegularityCriterion
import RockafellarWets.Chapter8.SubderivativeRegularityCriterion

open Filter Set Topology Metric
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {C : Set E} {x v : E}

/-- **Exercise 8.14**, regular subgradients of an indicator. -/
theorem regularSubdifferential_indicatorVA (C : Set E) (x : E) :
    regularSubdifferential (indicatorVA C) x = regularNormalCone C x := by
  ext v
  by_cases hx : x ∈ C
  · have hval : indicatorVA C x = ((0:ℝ):EReal) := by simp [hx]
    rw [mem_regularSubdifferential_iff_inner_le_subderivative hval, subderivative_indicatorVA hx,
      mem_regularNormalCone_iff_inner_nonpos hx]
    constructor
    · intro h w hw
      simpa [hw] using h w
    · intro h w
      by_cases hw : w ∈ tangentCone C x
      · simpa [hw] using h w hw
      · simp [hw]
  · rw [regularNormalCone_eq_empty hx]
    simp only [mem_empty_iff_false,iff_false]
    rintro ⟨c,hc,_⟩
    simp [hx] at hc

/-- **Exercise 8.14**, limiting subgradients of an indicator. -/
theorem subdifferential_indicatorVA (C : Set E) (x : E) :
    subdifferential (indicatorVA C) x = normalCone C x := by
  ext v
  rw [mem_subdifferential_iff_exists_seq]
  constructor
  · rintro ⟨⟨c,hc⟩,y,w,hy,_,hw,hwlim⟩
    have hx : x ∈ C := by by_contra h; simp [h] at hc
    apply mem_normalCone_of_forall hx hy _ hwlim
    intro n
    simpa only [regularSubdifferential_indicatorVA] using hw n
  · rintro ⟨hx,y,w,hyC,hy,hw,hwlim⟩
    refine ⟨⟨0,by simp [hx]⟩,y,w,hy,?_,?_,hwlim⟩
    · simpa [Function.comp_def,hx,hyC] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0:EReal)) atTop (𝓝 0))
    · simpa only [regularSubdifferential_indicatorVA] using hw

/-- **Exercise 8.14**, horizon subgradients of an indicator. Positive rescaling
does not change a regular normal cone. -/
theorem horizonSubdifferential_indicatorVA (C : Set E) (x : E) :
    horizonSubdifferential (indicatorVA C) x = normalCone C x := by
  ext v
  by_cases hx : x ∈ C
  · have hc : indicatorVA C x = ((0:ℝ):EReal) := by simp [hx]
    rw [mem_horizonSubdifferential_iff_zero_or_scaledSeq hc]
    simp only [regularSubdifferential_indicatorVA]
    constructor
    · rintro (rfl | ⟨y,w,t,hy,hw,ht,_,hlim⟩)
      · exact (isCone_normalCone hx).1
      · exact mem_normalCone_of_forall hx (tendsto_attentiveNhds_iff.mp hy).1
          (fun n ↦ (isCone_regularNormalCone (hw n).1).smul_mem (hw n) (ht n).le) hlim
    · rintro ⟨_,y,w,hyC,hy,hw,hwlim⟩
      let t := fun n : ℕ ↦ 1 / ((n:ℝ) + 1)
      have ht (n : ℕ) : 0 < t n := by dsimp [t]; positivity
      refine Or.inr ⟨y,fun n ↦ (t n)⁻¹ • w n,t,tendsto_attentiveNhds_iff.mpr ⟨hy,?_⟩,
        fun n ↦ (isCone_regularNormalCone (hyC n)).smul_mem (hw n) (inv_nonneg.mpr (ht n).le),
        ht,tendsto_one_div_add_atTop_nhds_zero_nat,?_⟩
      · simpa [Function.comp_def,hx,hyC] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0:EReal)) atTop (𝓝 0))
      · simpa [smul_smul, (ht _).ne'] using hwlim
  · rw [normalCone_eq_empty hx]
    simp only [mem_empty_iff_false,iff_false]
    rintro ⟨⟨c,hc⟩,_⟩
    simp [hx] at hc

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] in
/-- The indicator is locally lower semicontinuous at a feasible point exactly
when the set is locally closed there. -/
theorem isLocallyLscAt_indicatorVA_iff (hx : x ∈ C) :
    IsLocallyLscAt (indicatorVA C) x ↔ IsLocallyClosedAt C x := by
  have hc : indicatorVA C x = ((0:ℝ):EReal) := by simp [hx]
  have hlevel (a : ℝ) : {y | indicatorVA C y ≤ (a:EReal)} = if 0 ≤ a then C else ∅ := by
    ext y
    by_cases h : y ∈ C <;> by_cases ha : 0 ≤ a <;> simp [h,ha]
  constructor
  · rintro ⟨_,_,r,hr,hcl⟩
    have h := hcl 0 (by simpa [hc] using hr.le)
    rw [hlevel,if_pos le_rfl,inter_comm] at h
    exact ⟨closedBall x r,closedBall_mem_nhds x hr,isClosed_closedBall,h⟩
  · rintro ⟨V,hV,_,hCV⟩
    obtain ⟨r,hr,hrV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hV
    refine ⟨by simp [hx],by simp [hx],r,hr,fun a _ ↦ ?_⟩
    rw [hlevel]
    split_ifs
    · have heq : closedBall x r ∩ C = closedBall x r ∩ (C ∩ V) := by
        ext y
        exact ⟨fun h ↦ ⟨h.1,h.2,hrV h.1⟩,fun h ↦ ⟨h.1,h.2.1⟩⟩
      rw [heq]
      exact isClosed_closedBall.inter hCV
    · simp


/-- At a point in the set the horizon of the regular subdifferential equals
the same regular normal cone. -/
theorem horizonCone_regularSubdifferential_indicatorVA (hx : x ∈ C) :
    horizonCone (regularSubdifferential (indicatorVA C) x) = regularNormalCone C x := by
  rw [regularSubdifferential_indicatorVA]
  exact horizonCone_eq_self_of_isClosed_isCone (isClosed_regularNormalCone C x) (isCone_regularNormalCone hx)

/-- **Exercise 8.14**, equality of the set and indicator regularity criteria. -/
theorem isSubdifferentiallyRegularAt_indicatorVA_iff (hx : x ∈ C) :
    IsSubdifferentiallyRegularAt (indicatorVA C) x ↔ IsClarkeRegularAt C x := by
  have hc : indicatorVA C x = ((0:ℝ):EReal) := by simp [hx]
  have hne : (subdifferential (indicatorVA C) x).Nonempty := by
    rw [subdifferential_indicatorVA]
    exact ⟨0,(isCone_normalCone hx).1⟩
  rw [isSubdifferentiallyRegularAt_iff_subgradients hc hne,isLocallyLscAt_indicatorVA_iff hx,
    subdifferential_indicatorVA,horizonSubdifferential_indicatorVA,horizonCone_regularSubdifferential_indicatorVA hx,
    regularSubdifferential_indicatorVA,and_self]
  rfl

end RW
