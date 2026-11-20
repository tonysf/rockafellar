/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Regular subderivatives from subgradients
-/

import RockafellarWets.Chapter8.HorizontalEpigraphNormals
import RockafellarWets.Chapter8.SubderivativeRegularityCriterion
import RockafellarWets.Chapter8.SupportFunctions

open Set
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {x w : E} {a c : ℝ}

private theorem regularSubderivative_le_coe_iff_normal {f : E → EReal} {x w : E} {a c : ℝ}
    (hx : f x = c) (hl : IsLocallyLscAt f x) :
    regularSubderivative f x w ≤ (a : EReal) ↔ ∀ v (b : ℝ), WithLp.toLp 2 (v,b) ∈
      normalCone (euclideanEpigraph f) (WithLp.toLp 2 (x,c)) → ⟪v,w⟫_ℝ + b*a ≤ 0 := by
  let L := l2ProdEquiv E
  let p := WithLp.toLp 2 (x,c)
  let q := WithLp.toLp 2 (w,a)
  have hp : p ∈ euclideanEpigraph f := hx.le
  have hc : IsLocallyClosedAt (epigraph f) (x,c) := by simpa [hx] using hl.isLocallyClosedAt_epigraph
  have ht : regularTangentCone (euclideanEpigraph f) p = L ⁻¹' regularTangentCone (epigraph f) (x,c) :=
    regularTangentCone_preimage (Φ' := L) L.toContinuousLinearMap.hasStrictFDerivAt (epigraph f) hx.le
  have he : regularSubderivative f x w ≤ (a : EReal) ↔ q ∈ polarCone (normalCone (euclideanEpigraph f) p) := by
    change (w,a) ∈ epigraph (regularSubderivative f x) ↔ _
    rw [epigraph_regularSubderivative_eq_regularTangentCone hx hl.lowerSemicontinuousAt,
      ← regularTangentCone_eq_polarCone_normalCone hp (IsLocallyClosedAt.preimage_continuousLinearEquiv L hc), ht]
    rfl
  rw [he]
  constructor
  · intro h v b hn
    simpa [q, WithLp.prod_inner_apply, real_inner_comm w v, mul_comm] using h (WithLp.toLp 2 (v,b)) hn
  · rintro h z hz
    obtain ⟨⟨v,b⟩, rfl⟩ := (WithLp.toLp_surjective 2) z
    simpa [q, WithLp.prod_inner_apply, real_inner_comm w v, mul_comm] using h v b hz

/-- A real height bounds the regular subderivative exactly when it bounds
the support of the limiting subdifferential and the direction is polar to
every horizon subgradient. -/
theorem regularSubderivative_le_coe_iff_support_polar (hx : f x = c) (hl : IsLocallyLscAt f x) :
    regularSubderivative f x w ≤ (a : EReal) ↔ supportFunction (subdifferential f x) w ≤ (a : EReal) ∧
      w ∈ polarCone (horizonSubdifferential f x) := by
  rw [regularSubderivative_le_coe_iff_normal hx hl, supportFunction_le_iff]
  constructor
  · intro h
    constructor
    · intro v hv
      have hn := h v (-1) ((mem_subdifferential_iff_epigraph_normal hx).mp hv)
      exact EReal.coe_le_coe_iff.mpr (by linarith)
    · intro v hv
      simpa only [zero_mul, add_zero, real_inner_comm v w] using h v 0 (horizontal_normal_of_mem_horizonSubdifferential hx hv)
  · rintro ⟨hsub, hpolar⟩ v b hn
    rcases lt_or_eq_of_le (vertical_nonpos_of_mem_normalCone_epigraph hn) with hb | rfl
    · have hs := (isCone_normalCone (show WithLp.toLp 2 (x,c) ∈ euclideanEpigraph f from hx.le)
        ).smul_mem hn (inv_nonneg.mpr (neg_pos.mpr hb).le)
      have hz : (-b)⁻¹ • v ∈ subdifferential f x := by
        rw [mem_subdifferential_iff_epigraph_normal hx]
        convert hs using 1
        apply WithLp.ofLp_injective
        ext <;> simp [smul_eq_mul, hb.ne]
      have hv := EReal.coe_le_coe_iff.mp (hsub _ hz)
      rw [real_inner_smul_left, inv_mul_le_iff₀ (neg_pos.mpr hb)] at hv
      linarith
    · simpa only [zero_mul, add_zero, real_inner_comm v w] using hpolar v
        ((mem_horizonSubdifferential_iff_epigraph_normal_of_locallyLsc hl hx).mpr hn)

/-- **Exercise 8.23.** On the polar of the horizon subdifferential, the
regular subderivative is the support function of the limiting subdifferential. -/
theorem regularSubderivative_eq_supportFunction_of_mem_polar (hx : f x = c) (hl : IsLocallyLscAt f x)
    (hw : w ∈ polarCone (horizonSubdifferential f x)) :
    regularSubderivative f x w = supportFunction (subdifferential f x) w := by
  apply le_antisymm <;> by_contra! h
  · obtain ⟨r, hr, hr'⟩ := EReal.exists_between_coe_real h
    exact hr'.not_ge ((regularSubderivative_le_coe_iff_support_polar hx hl).mpr ⟨hr.le, hw⟩)
  · obtain ⟨r, hr, hr'⟩ := EReal.exists_between_coe_real h
    exact hr'.not_ge ((regularSubderivative_le_coe_iff_support_polar hx hl).mp hr.le).1

/-- Outside the horizon polar the regular subderivative is positive infinity. -/
theorem regularSubderivative_eq_top_of_not_mem_polar (hx : f x = c) (hl : IsLocallyLscAt f x)
    (hw : w ∉ polarCone (horizonSubdifferential f x)) : regularSubderivative f x w = ⊤ := by
  by_contra hn
  obtain ⟨r, hr, -⟩ := EReal.exists_between_coe_real (lt_top_iff_ne_top.mpr hn)
  exact hw ((regularSubderivative_le_coe_iff_support_polar hx hl).mp hr.le).2

theorem regularSubderivative_zero_eq_zero_iff (hx : f x = c) (hl : IsLocallyLscAt f x) :
    regularSubderivative f x 0 = 0 ↔ (subdifferential f x).Nonempty := by
  rw [regularSubderivative_eq_supportFunction_of_mem_polar hx hl (zero_mem_polarCone _)]
  constructor
  · intro he
    by_contra hn
    rw [not_nonempty_iff_eq_empty.mp hn, supportFunction_empty] at he
    exact EReal.coe_ne_bot 0 he.symm
  · exact supportFunction_zero

end RW
