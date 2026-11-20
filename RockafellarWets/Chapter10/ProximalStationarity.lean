/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Subgradients in proximal mappings
-/

import RockafellarWets.Chapter10.FermatRule
import RockafellarWets.Chapter8.ProximalSubgradientPoints

open Set
open scoped InnerProductSpace Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The identity plus a scaled subgradient mapping in Example10.2. -/
noncomputable def subgradientShift (f : E → EReal) (lam : ℝ) (w : E) : Set E :=
  (fun v ↦ w + lam • v) '' subdifferential f w

/-- **Example 10.2**, proximal points satisfy the subgradient resolvent inclusion. -/
theorem proximalMappingEReal_subset_inverse_subgradientShift {f : E → EReal}
    (hp : IsProper f) {lam : ℝ} (hlam : 0 < lam) (x : E) :
    proximalMappingEReal f lam x ⊆ svInv (subgradientShift f lam) x := by
  intro w hw
  obtain ⟨c,hc,hglob,hv⟩ := global_inequality_of_mem_proximalMappingEReal hlam hw (hp.2 w).ne'
  have hs := regularSubdifferential_subset_subdifferential f w
    (proximalSubdifferential_subset_regularSubdifferential f w hv)
  refine ⟨lam⁻¹ • (x-w),hs,?_⟩
  simp only [smul_smul,mul_inv_cancel₀ hlam.ne',one_smul,add_sub_cancel]

variable [FiniteDimensional ℝ E]

/-- For a convex function, resolvent stationarity gives a global proximal
minimum. Closedness or existence of other proximal points is not assumed. -/
theorem mem_proximalMappingEReal_of_subgradient {f : E → EReal}
    (hconv : Convex ℝ (epigraph f)) (hp : IsProper f) {lam : ℝ} (hlam : 0 < lam)
    {x w v : E} (hv : v ∈ subdifferential f w) (hx : x = w + lam • v) :
    w ∈ proximalMappingEReal f lam x := by
  obtain ⟨c,hc⟩ := hv.1
  have hsupport := (mem_subdifferential_iff_of_convex hconv hp hc).mp hv
  have hmin (y : E) : proximalObjectiveEReal f lam x w ≤ proximalObjectiveEReal f lam x y := by
    by_cases hyt : f y = ⊤
    · simp only [proximalObjectiveEReal,hyt,EReal.top_add_coe,le_top]
    have hy : f y = ((f y).toReal : EReal) := (EReal.coe_toReal hyt (hp.2 y).ne').symm
    have hs := hsupport y
    rw [hy,EReal.coe_le_coe_iff] at hs
    unfold proximalObjectiveEReal
    rw [hc,hy,← EReal.coe_add,← EReal.coe_add,EReal.coe_le_coe_iff]
    have hwx : w-x = (-lam) • v := by rw [hx]; module
    have hcross : ⟪y-w,w-x⟫_ℝ = -lam * ⟪v,y-w⟫_ℝ := by
      rw [hwx,inner_smul_right,real_inner_comm]
    have hexp : ‖y-x‖^2 = ‖y-w‖^2 + 2 * (-lam * ⟪v,y-w⟫_ℝ) + ‖w-x‖^2 := by
      have he : y-x = (y-w)+(w-x) := by abel
      rw [he,norm_add_sq_real,hcross]
    have hcancel : (1/(2*lam)) * (2*(-lam*⟪v,y-w⟫_ℝ)) = -⟪v,y-w⟫_ℝ := by
      field_simp
    have hscaled := congrArg (fun r : ℝ ↦ (1/(2*lam))*r) hexp
    have hnonneg : 0 ≤ (1/(2*lam))*‖y-w‖^2 := by positivity
    nlinarith
  have hfinite : proximalObjectiveEReal f lam x w =
      ((c+(1/(2*lam))*‖w-x‖^2 : ℝ) : EReal) := by
    simp only [proximalObjectiveEReal,hc,EReal.coe_add]
  have he : proximalObjectiveEReal f lam x w = ⨅ y, proximalObjectiveEReal f lam x y :=
    le_antisymm (le_iInf hmin) (iInf_le _ w)
  exact ⟨he,he ▸ hfinite.trans_lt (EReal.coe_lt_top _)⟩

/-- **Example 10.2**, equality with the subgradient resolvent in the convex case. -/
theorem proximalMappingEReal_eq_inverse_subgradientShift {f : E → EReal}
    (hconv : Convex ℝ (epigraph f)) (hp : IsProper f) {lam : ℝ} (hlam : 0 < lam) :
    proximalMappingEReal f lam = svInv (subgradientShift f lam) := by
  funext x
  apply Subset.antisymm (proximalMappingEReal_subset_inverse_subgradientShift hp hlam x)
  rintro w ⟨v,hv,hvx⟩
  exact mem_proximalMappingEReal_of_subgradient hconv hp hlam hv hvx.symm

end RW
