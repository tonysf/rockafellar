/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Regular and convex cases of the extremal separation principle
-/

import RockafellarWets.Chapter9.ExtremalSetSeparation

open Metric Set
open scoped InnerProductSpace Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- At regular sets the separating normals are regular and the separated
cones are the ordinary tangent cones. -/
theorem extremal_nonoverlap_separation_of_regular {C D : Set E} {x : E}
    (hC : IsClosed C) (hD : IsClosed D) (hxC : x ∈ C) (hxD : x ∈ D)
    (hrC : IsClarkeRegularAt C x) (hrD : IsClarkeRegularAt D x)
    {δ : ℝ} (hδ : 0 < δ)
    (hb : (0:E) ∉ interior ((C ∩ closedBall x δ) - (D ∩ closedBall x δ))) :
    ∃ v : E, v ≠ 0 ∧ v ∈ regularNormalCone C x ∧ -v ∈ regularNormalCone D x ∧
      (∀ w ∈ tangentCone C x, ⟪v,w⟫_ℝ ≤ 0) ∧
      (∀ w ∈ tangentCone D x, 0 ≤ ⟪v,w⟫_ℝ) := by
  obtain ⟨v,hv,hvC,hvD,hTC,hTD⟩ := extremal_nonoverlap_separation hC hD hxC hxD hδ hb
  refine ⟨v,hv,hrC.2 ▸ hvC,hrD.2 ▸ hvD,?_,?_⟩
  · simpa only [tangentCone_eq_regularTangentCone_of_isClarkeRegularAt hxC hrC] using hTC
  · simpa only [tangentCone_eq_regularTangentCone_of_isClarkeRegularAt hxD hrD] using hTD

/-- For convex sets, the extremal hyperplane separates the entire sets. -/
theorem extremal_nonoverlap_separation_of_convex {C D : Set E} {x : E}
    (hC : IsClosed C) (hD : IsClosed D) (hxC : x ∈ C) (hxD : x ∈ D)
    (hcC : Convex ℝ C) (hcD : Convex ℝ D)
    {δ : ℝ} (hδ : 0 < δ)
    (hb : (0:E) ∉ interior ((C ∩ closedBall x δ) - (D ∩ closedBall x δ))) :
    ∃ v : E, v ≠ 0 ∧
      (∀ c ∈ C, ⟪v,c⟫_ℝ ≤ ⟪v,x⟫_ℝ) ∧
      (∀ d ∈ D, ⟪v,x⟫_ℝ ≤ ⟪v,d⟫_ℝ) := by
  obtain ⟨v,hv,hvC,hvD⟩ := extremal_nonoverlap_normals hC hD hxC hxD hδ hb
  rw [normalCone_eq_of_convex hcC hxC] at hvC
  rw [normalCone_eq_of_convex hcD hxD] at hvD
  refine ⟨v,hv,?_,?_⟩
  · intro c hc
    have h := hvC c hc
    simpa only [inner_sub_right,sub_nonpos] using h
  · intro d hd
    have h := hvD d hd
    simp only [inner_neg_left,inner_sub_right] at h
    linarith

end RW
