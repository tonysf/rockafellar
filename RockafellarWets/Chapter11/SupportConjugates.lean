/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Indicator functions, support functions, and cone conjugacy
-/

import RockafellarWets.Chapter11.ConjugateGeometry
import RockafellarWets.Chapter8.SupportSubgradients
import RockafellarWets.Chapter11.PolarSets

open Set
open scoped InnerProductSpace Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The indicator/support conjugacy in Theorem 11.4(a), including the empty set. -/
theorem fenchelConjugate_indicatorVA (C : Set E) :
    fenchelConjugate (indicatorVA C) = supportFunction C := by
  funext v
  refine le_antisymm (iSup_le fun x ↦ ?_) ?_
  · by_cases hx : x ∈ C
    · simpa [indicatorVA_apply_mem hx, real_inner_comm v] using inner_le_supportFunction hx v
    · simp [indicatorVA_apply_not_mem hx]
  · apply iSup_le
    intro x
    simpa [indicatorVA_apply_mem x.property, real_inner_comm v] using
      le_fenchelConjugate (indicatorVA C) x v

/-- A finite affine minorant of a positively homogeneous function has a linear
minorant with the same slope. -/
theorem mem_linearMinorantSet_of_fenchelConjugate_lt_top {h : E → EReal}
    (hh : PositivelyHomogeneous h) {v : E} (hv : fenchelConjugate h v < ⊤) :
    v ∈ linearMinorantSet h := by
  obtain ⟨r,hr,_⟩ := EReal.exists_between_coe_real hv
  have hbound := (fenchelConjugate_le_coe_iff h v r).mp hr.le
  intro x
  cases hx : h x with
  | top => exact le_top
  | bot =>
    have hf := hbound x
    rw [hx] at hf
    exact ((EReal.bot_lt_coe _).not_ge hf).elim
  | coe c =>
    apply EReal.coe_le_coe_iff.mpr
    by_contra! hp
    let t : ℝ := (|r|+1)/(⟪v,x⟫_ℝ-c)
    have ht : 0 < t := div_pos (by positivity) (sub_pos.mpr hp)
    have hf := hbound (t • x)
    rw [hh.2 ht, hx, ← EReal.coe_mul, real_inner_smul_right, EReal.coe_le_coe_iff] at hf
    have he : t * (⟪v,x⟫_ℝ-c) = |r|+1 := div_mul_cancel₀ _ (sub_pos.mpr hp).ne'
    nlinarith [le_abs_self r]

/-- The homogeneous-function clause of Theorem 11.4(a). -/
theorem fenchelConjugate_positivelyHomogeneous {h : E → EReal}
    (hh : PositivelyHomogeneous h) :
    fenchelConjugate h = indicatorVA (linearMinorantSet h) := by
  funext v
  by_cases hv : v ∈ linearMinorantSet h
  · rw [indicatorVA_apply_mem hv]
    refine le_antisymm ((fenchelConjugate_le_iff _ _ _).mpr fun x ↦ EReal.sub_nonpos.mpr (hv x)) ?_
    rcases hh.zero_eq_zero_or_bot with hzero | hzero
    · simpa [hzero] using le_fenchelConjugate h 0 v
    · have hbad := hv 0
      simp [hzero] at hbad
  · rw [indicatorVA_apply_not_mem hv]
    exact eq_top_iff.mpr (by
      by_contra! hfin
      exact hv (mem_linearMinorantSet_of_fenchelConjugate_lt_top hh hfin))

/-- Cone polarity is indicator conjugacy, Theorem 11.4(b). -/
theorem fenchelConjugate_indicatorVA_cone {K : Set E} (hk : IsCone K) :
    fenchelConjugate (indicatorVA K) = indicatorVA (polarCone K) := by
  rw [fenchelConjugate_indicatorVA, supportFunction_cone hk]

variable [FiniteDimensional ℝ E]

theorem fenchelConjugate_supportFunction (C : Set E) :
    fenchelConjugate (supportFunction C) = indicatorVA (closure (convexHull ℝ C)) := by
  rw [fenchelConjugate_positivelyHomogeneous (sublinear_supportFunction C).1,
    linearMinorantSet_supportFunction]

/-- The reverse indicator/support conjugacy for closed convex sets. -/
theorem fenchelConjugate_supportFunction_of_closed_convex {C : Set E}
    (hc : Convex ℝ C) (hclosed : IsClosed C) :
    fenchelConjugate (supportFunction C) = indicatorVA C := by
  rw [fenchelConjugate_supportFunction, hc.convexHull_eq, hclosed.closure_eq]

/-- Gauge conjugacy in Example 11.19. -/
theorem fenchelConjugate_gaugeFunction {C : Set E} (hc : Convex ℝ C)
    (hclosed : IsClosed C) (h0 : (0 : E) ∈ C) :
    fenchelConjugate (gaugeFunction C) = indicatorVA (polarSet C) := by
  rw [← supportFunction_polarSet_eq_gaugeFunction hc hclosed h0]
  exact fenchelConjugate_supportFunction_of_closed_convex (convex_polarSet C) (isClosed_polarSet C)

theorem fenchelConjugate_gaugeFunction_polarSet {C : Set E} (hc : Convex ℝ C)
    (hclosed : IsClosed C) (h0 : (0 : E) ∈ C) :
    fenchelConjugate (gaugeFunction (polarSet C)) = indicatorVA C := by
  rw [gaugeFunction_polarSet_eq_supportFunction hc hclosed h0]
  exact fenchelConjugate_supportFunction_of_closed_convex hc hclosed

/-- Normal/support attainment equivalence, without a nonemptiness assumption. -/
theorem mem_normalCone_iff_supportFunction_eq {C : Set E} (hc : Convex ℝ C)
    {x v : E} : v ∈ normalCone C x ↔ x ∈ C ∧ (⟪v,x⟫_ℝ : EReal) = supportFunction C v := by
  by_cases hx : x ∈ C
  · rw [normalCone_eq_of_convex hc hx]
    refine ⟨fun hn ↦ ⟨hx, le_antisymm (by simpa [real_inner_comm] using inner_le_supportFunction hx v)
      ((supportFunction_le_iff _ _ _).mpr fun y hy ↦ ?_)⟩, ?_⟩
    · exact EReal.coe_le_coe_iff.mpr (by simpa [inner_sub_right, sub_nonpos, real_inner_comm] using hn y hy)
    · rintro ⟨_,he⟩ y hy
      have hle := EReal.coe_le_coe_iff.mp ((inner_le_supportFunction hy v).trans_eq he.symm)
      simpa [inner_sub_right, sub_nonpos, real_inner_comm] using hle
  · simp [normalCone_eq_empty hx, hx]

/-- The normal/subgradient reciprocity of Theorem 11.4(a), at arbitrary points. -/
theorem mem_normalCone_iff_mem_subdifferential_supportFunction {C : Set E}
    (hc : Convex ℝ C) (hclosed : IsClosed C) {x v : E} :
    v ∈ normalCone C x ↔ x ∈ subdifferential (supportFunction C) v := by
  rw [mem_normalCone_iff_supportFunction_eq hc]
  constructor
  · rintro ⟨hx,he⟩
    have hv : v ∈ effectiveDomain (supportFunction C) := he.symm.trans_lt (EReal.coe_lt_top _)
    rw [subdifferential_supportFunction hc hclosed ⟨x,hx⟩ hv]
    exact ⟨hx, by simpa [real_inner_comm] using he⟩
  · intro hv
    obtain ⟨r,hr⟩ := hv.1
    have hdom : v ∈ effectiveDomain (supportFunction C) := hr.trans_lt (EReal.coe_lt_top _)
    have hne : C.Nonempty := by
      by_contra! he
      rw [he, supportFunction_empty] at hr
      exact (EReal.coe_ne_bot r) hr.symm
    rw [subdifferential_supportFunction hc hclosed hne hdom] at hv
    simpa [real_inner_comm] using hv

/-- The complementarity form of cone normality, formula 11(5). -/
theorem mem_normalCone_cone_iff {K : Set E} (hc : Convex ℝ K) (hk : IsCone K)
    {x v : E} : v ∈ normalCone K x ↔ x ∈ K ∧ v ∈ polarCone K ∧ ⟪v,x⟫_ℝ = 0 := by
  rw [mem_normalCone_iff_supportFunction_eq hc, supportFunction_cone hk]
  refine and_congr_right fun _ ↦ ?_
  by_cases hv : v ∈ polarCone K
  · simp [indicatorVA_apply_mem hv, hv]
  · simp [indicatorVA_apply_not_mem hv, hv]

/-- Normal reciprocity for closed convex cones, formula 11(5). -/
theorem mem_normalCone_iff_mem_normalCone_polar {K : Set E} (hc : Convex ℝ K)
    (hclosed : IsClosed K) (hk : IsCone K) {x v : E} :
    v ∈ normalCone K x ↔ x ∈ normalCone (polarCone K) v := by
  letI := FiniteDimensional.complete ℝ E
  rw [mem_normalCone_cone_iff hc hk,
    mem_normalCone_cone_iff (convex_polarCone K) (isCone_polarCone K),
    polarCone_bipolar_eq_self hclosed hc hk]
  simp only [real_inner_comm x v]
  tauto

/-- Orthogonal subspace correspondence as conjugacy of indicators. -/
theorem fenchelConjugate_indicatorVA_submodule (M : Submodule ℝ E) :
    fenchelConjugate (indicatorVA (M : Set E)) = indicatorVA (Mᗮ : Set E) := by
  rw [fenchelConjugate_indicatorVA_cone ⟨M.zero_mem, fun {x} hx {t} _ ↦ M.smul_mem t hx⟩,
    polarCone_submodule]

end RW
