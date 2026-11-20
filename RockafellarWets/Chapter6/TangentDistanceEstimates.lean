/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Distance to the Tangent Cone

Proposition 6.27(b). The projection witness used for tangent-normal polarity
can be normalized to a unit normal whenever the direction is outside the
tangent cone. Compactness of the normal cone intersected with the unit ball
then gives the attained minimum and maximum in the printed distance bounds.
This proof is independent of Proposition 6.27(a).
-/

import RockafellarWets.Chapter6.TangentNormalPolarity

open Metric Set
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **Proposition 6.27(b)**: outside the tangent cone, its distance is the
pairing with a unit limiting normal at the base point. -/
theorem exists_unit_normalCone_inner_eq_infDist_tangentCone
    {C : Set E} {x w : E} (hx : x ∈ C) (hlc : IsLocallyClosedAt C x)
    (hw : w ∉ tangentCone C x) :
    ∃ v ∈ normalCone C x, ‖v‖ = 1 ∧ ⟪v, w⟫_ℝ = infDist w (tangentCone C x) := by
  have hdpos : 0 < infDist w (tangentCone C x) :=
    ((isClosed_tangentCone C x).notMem_iff_infDist_pos
      ⟨0, (isCone_tangentCone hx).1⟩).1 hw
  obtain ⟨v, hv, hvnorm, hvinner⟩ :=
    exists_mem_normalCone_norm_eq_infDist_tangentCone hx hlc w
  have hvne : v ≠ 0 := by
    intro hzero
    simp only [hzero, norm_zero] at hvnorm
    linarith
  refine ⟨‖v‖⁻¹ • v,
    (isCone_normalCone hx).smul_mem hv (inv_nonneg.2 (norm_nonneg _)),
    norm_smul_inv_norm hvne, ?_⟩
  rw [real_inner_smul_left, hvnorm, hvinner]
  field_simp

/-- **Proposition 6.27(b)**: for every direction, some normal in the closed
unit ball pairs with that direction to give its distance to the tangent cone.
For a tangent direction, the zero normal is such a witness. -/
theorem exists_normalCone_closedBall_inner_eq_infDist_tangentCone
    {C : Set E} {x : E} (hx : x ∈ C) (hlc : IsLocallyClosedAt C x) (w : E) :
    ∃ v ∈ normalCone C x ∩ closedBall (0 : E) 1,
      ⟪v, w⟫_ℝ = infDist w (tangentCone C x) := by
  by_cases hw : w ∈ tangentCone C x
  · refine ⟨0, ⟨(isCone_normalCone hx).1, ?_⟩, ?_⟩
    · simp
    · rw [inner_zero_left, infDist_zero_of_mem hw]
  · obtain ⟨v, hv, hvnorm, hvinner⟩ :=
      exists_unit_normalCone_inner_eq_infDist_tangentCone hx hlc hw
    exact ⟨v, ⟨hv, by simp [mem_closedBall, dist_zero_right, hvnorm]⟩, hvinner⟩

/-- **Proposition 6.27(b)**, with attained extrema: the minimum and maximum
of the normal pairing on the closed unit ball bound the tangent distance. -/
theorem exists_normalCone_inner_extrema_bounds_infDist_tangentCone
    {C : Set E} {x : E} (hx : x ∈ C) (hlc : IsLocallyClosedAt C x) (w : E) :
    ∃ vmin ∈ normalCone C x ∩ closedBall (0 : E) 1,
      ∃ vmax ∈ normalCone C x ∩ closedBall (0 : E) 1,
        IsMinOn (fun v ↦ ⟪v, w⟫_ℝ) (normalCone C x ∩ closedBall (0 : E) 1) vmin ∧
        IsMaxOn (fun v ↦ ⟪v, w⟫_ℝ) (normalCone C x ∩ closedBall (0 : E) 1) vmax ∧
        ⟪vmin, w⟫_ℝ ≤ infDist w (tangentCone C x) ∧
        infDist w (tangentCone C x) ≤ ⟪vmax, w⟫_ℝ := by
  have hcompact : IsCompact (normalCone C x ∩ closedBall (0 : E) 1) :=
    (isCompact_closedBall (0 : E) 1).inter_left (isClosed_normalCone C x)
  have hzero : (0 : E) ∈ normalCone C x ∩ closedBall (0 : E) 1 :=
    ⟨(isCone_normalCone hx).1, by simp⟩
  have hcont : ContinuousOn (fun v : E ↦ ⟪v, w⟫_ℝ)
      (normalCone C x ∩ closedBall (0 : E) 1) := by fun_prop
  obtain ⟨vmin, hvmin, hmin⟩ := hcompact.exists_isMinOn ⟨0, hzero⟩ hcont
  obtain ⟨vmax, hvmax, hmax⟩ := hcompact.exists_isMaxOn ⟨0, hzero⟩ hcont
  obtain ⟨v, hv, hvinner⟩ :=
    exists_normalCone_closedBall_inner_eq_infDist_tangentCone hx hlc w
  refine ⟨vmin, hvmin, vmax, hvmax, hmin, hmax, ?_, ?_⟩
  · calc
      ⟪vmin, w⟫_ℝ ≤ ⟪v, w⟫_ℝ := hmin hv
      _ = infDist w (tangentCone C x) := hvinner
  · calc
      infDist w (tangentCone C x) = ⟪v, w⟫_ℝ := hvinner.symm
      _ ≤ ⟪vmax, w⟫_ℝ := hmax hv

/-- **Proposition 6.27(b)**, the printed double inequality expressed with
the infimum and supremum of the pairing values. Both extrema are attained,
as witnessed by `exists_normalCone_inner_extrema_bounds_infDist_tangentCone`. -/
theorem normalCone_inner_sInf_le_infDist_tangentCone_le_sSup
    {C : Set E} {x : E} (hx : x ∈ C) (hlc : IsLocallyClosedAt C x) (w : E) :
    sInf ((fun v ↦ ⟪v, w⟫_ℝ) '' (normalCone C x ∩ closedBall (0 : E) 1)) ≤
      infDist w (tangentCone C x) ∧
    infDist w (tangentCone C x) ≤
      sSup ((fun v ↦ ⟪v, w⟫_ℝ) '' (normalCone C x ∩ closedBall (0 : E) 1)) := by
  obtain ⟨vmin, hvmin, vmax, hvmax, hmin, hmax, hlow, hhigh⟩ :=
    exists_normalCone_inner_extrema_bounds_infDist_tangentCone hx hlc w
  have hleast : IsLeast
      ((fun v ↦ ⟪v, w⟫_ℝ) '' (normalCone C x ∩ closedBall (0 : E) 1)) ⟪vmin, w⟫_ℝ := by
    refine ⟨⟨vmin, hvmin, rfl⟩, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    exact hmin hv
  have hgreatest : IsGreatest
      ((fun v ↦ ⟪v, w⟫_ℝ) '' (normalCone C x ∩ closedBall (0 : E) 1)) ⟪vmax, w⟫_ℝ := by
    refine ⟨⟨vmax, hvmax, rfl⟩, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    exact hmax hv
  rw [hleast.csInf_eq, hgreatest.csSup_eq]
  exact ⟨hlow, hhigh⟩

end RW
