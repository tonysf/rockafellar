/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# General polar sets and their gauges
-/

import RockafellarWets.Chapter8.SupportCorrespondence
import RockafellarWets.Chapter3.PositiveHulls

open Set
open scoped InnerProductSpace Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The one-sided polar of a set, as in Example 11.19. -/
def polarSet (C : Set E) : Set E := {v | ∀ x ∈ C, ⟪v,x⟫_ℝ ≤ 1}

@[simp] theorem mem_polarSet {C : Set E} {v : E} :
    v ∈ polarSet C ↔ ∀ x ∈ C, ⟪v,x⟫_ℝ ≤ 1 := Iff.rfl

@[simp] theorem zero_mem_polarSet (C : Set E) : (0 : E) ∈ polarSet C := by
  simp [polarSet]

theorem polarSet_antitone {C D : Set E} (h : C ⊆ D) : polarSet D ⊆ polarSet C :=
  fun _ hv _ hx ↦ hv _ (h hx)

theorem isClosed_polarSet (C : Set E) : IsClosed (polarSet C) := by
  rw [show polarSet C = ⋂ x ∈ C, {v : E | ⟪v,x⟫_ℝ ≤ 1} by ext; simp [polarSet]]
  exact isClosed_biInter fun _ _ ↦ isClosed_le (by fun_prop) continuous_const

theorem convex_polarSet (C : Set E) : Convex ℝ (polarSet C) := by
  intro v hv u hu a b ha hb hab x hx
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  nlinarith [mul_le_mul_of_nonneg_left (hv x hx) ha,
    mul_le_mul_of_nonneg_left (hu x hx) hb]

theorem subset_polarSet_bipolar (C : Set E) : C ⊆ polarSet (polarSet C) := by
  intro x hx v hv
  simpa [real_inner_comm] using hv x hx

theorem mem_polarSet_iff_supportFunction_le {C : Set E} {v : E} :
    v ∈ polarSet C ↔ supportFunction C v ≤ 1 := by
  rw [supportFunction_le_iff]
  simp only [mem_polarSet, ← EReal.coe_one, EReal.coe_le_coe_iff, real_inner_comm v]

@[simp] theorem polarSet_closure (C : Set E) : polarSet (closure C) = polarSet C := by
  refine Subset.antisymm (polarSet_antitone subset_closure) ?_
  intro v hv
  have hsub : C ⊆ {x : E | ⟪v,x⟫_ℝ ≤ 1} := hv
  have hclosed : IsClosed {x : E | ⟪v,x⟫_ℝ ≤ 1} :=
    isClosed_le (by fun_prop) continuous_const
  exact closure_minimal hsub hclosed

@[simp] theorem polarSet_convexHull (C : Set E) :
    polarSet (convexHull ℝ C) = polarSet C := by
  refine Subset.antisymm (polarSet_antitone (subset_convexHull _ _)) ?_
  intro v hv
  exact convexHull_min hv (convex_halfSpace_le (innerSL ℝ v).toLinearMap.isLinear 1)

@[simp] theorem polarSet_closure_convexHull (C : Set E) :
    polarSet (closure (convexHull ℝ C)) = polarSet C := by simp

theorem polarSet_eq_polarCone_of_isCone {C : Set E} (hc : IsCone C) :
    polarSet C = polarCone C := by
  refine Subset.antisymm ?_ (fun v hv x hx ↦ (hv x hx).trans zero_le_one)
  intro v hv x hx
  by_contra! hp
  have ht : 0 < 2 / ⟪v,x⟫_ℝ := div_pos (by norm_num) hp
  have h := hv _ (hc.2 hx ht)
  rw [real_inner_smul_right, div_mul_cancel₀ _ hp.ne'] at h
  norm_num at h

theorem linearMinorantSet_gaugeFunction {C : Set E} (hc : Convex ℝ C)
    (hclosed : IsClosed C) (h0 : (0 : E) ∈ C) :
    linearMinorantSet (gaugeFunction C) = polarSet C := by
  refine Subset.antisymm (fun v hv x hx ↦ EReal.coe_le_coe_iff.mp
    ((hv x).trans (gaugeFunction_le_one_of_mem hx))) ?_
  intro v hv x
  by_contra! hn
  obtain ⟨r,hr,hrv⟩ := EReal.exists_between_coe_real hn
  have hrpos : 0 < r := EReal.coe_lt_coe_iff.mp ((nonneg_gaugeFunction C x).trans_lt hr)
  obtain ⟨z,hz,rfl⟩ := (gaugeFunction_le_iff_mem_smul hc hclosed h0 hrpos).mp hr.le
  have hle := mul_le_mul_of_nonneg_left (hv z hz) hrpos.le
  have hlt : r < r * ⟪v,z⟫_ℝ := by
    simpa only [real_inner_smul_right, EReal.coe_lt_coe_iff] using hrv
  linarith

variable [FiniteDimensional ℝ E]

/-- The first gauge identity in Example 11.19. -/
theorem supportFunction_polarSet_eq_gaugeFunction {C : Set E} (hc : Convex ℝ C)
    (hclosed : IsClosed C) (h0 : (0 : E) ∈ C) :
    supportFunction (polarSet C) = gaugeFunction C := by
  rw [← linearMinorantSet_gaugeFunction hc hclosed h0]
  exact supportFunction_linearMinorantSet (sublinear_gaugeFunction hc)
    (lowerSemicontinuous_gaugeFunction hc hclosed h0) (isProper_gaugeFunction C)

/-- General polarity is involutive on closed convex sets containing the origin. -/
theorem polarSet_bipolar_eq_self {C : Set E} (hc : Convex ℝ C)
    (hclosed : IsClosed C) (h0 : (0 : E) ∈ C) : polarSet (polarSet C) = C := by
  ext x
  rw [mem_polarSet_iff_supportFunction_le, supportFunction_polarSet_eq_gaugeFunction hc hclosed h0]
  exact gaugeFunction_le_one_iff_mem hc hclosed h0

/-- The bipolar identity in Example 11.19, for sets containing the origin. -/
theorem polarSet_bipolar {C : Set E} (h0 : (0 : E) ∈ C) :
    polarSet (polarSet C) = closure (convexHull ℝ C) := by
  rw [← polarSet_closure_convexHull C]
  exact polarSet_bipolar_eq_self (convex_convexHull ℝ C).closure isClosed_closure
    (subset_closure (subset_convexHull ℝ C h0))

/-- The symmetric gauge identity in Example 11.19. -/
theorem gaugeFunction_polarSet_eq_supportFunction {C : Set E} (hc : Convex ℝ C)
    (hclosed : IsClosed C) (h0 : (0 : E) ∈ C) :
    gaugeFunction (polarSet C) = supportFunction C := by
  rw [← supportFunction_polarSet_eq_gaugeFunction (convex_polarSet C)
    (isClosed_polarSet C) (zero_mem_polarSet C), polarSet_bipolar_eq_self hc hclosed h0]

end RW
