/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3G*: Polyhedral-Operation Boundary Examples

Regression examples for the proper and improper boundary cases in
Proposition 3.55(b).
-/

import RockafellarWets.Chapter3.PolyhedralOperations

open Set EReal

namespace RW

/-- The proper zero function is stable under pointwise maximum. -/
example :
    IsConvexPiecewiseLinear
      (fun _ : ℝ => (0 : EReal) ⊔ (0 : EReal)) := by
  apply
    (isConvexPiecewiseLinear_zero (E := ℝ)).isConvexPiecewiseLinear_sup
      (isConvexPiecewiseLinear_zero (E := ℝ))
  exact ⟨0, by simp [effectiveDomain]⟩

/-- The proper zero function is stable under pointwise addition. -/
example :
    IsConvexPiecewiseLinear
      (fun _ : ℝ => (0 : EReal) + (0 : EReal)) := by
  apply
    (isConvexPiecewiseLinear_zero (E := ℝ)).isConvexPiecewiseLinear_add
      (isConvexPiecewiseLinear_zero (E := ℝ))
  exact ⟨0, by simp [effectiveDomain]⟩

/-- A proper polyhedral integrand has a proper polyhedral value function in
this elementary boundary case. -/
example :
    IsConvexPiecewiseLinear
      (valueFunction (fun _ : ℝ × ℝ => (0 : EReal))) := by
  have hf :
      HasClosedPolyhedralEpigraph
        (fun _ : ℝ × ℝ => (0 : EReal)) :=
    hasClosedPolyhedralEpigraph_zero
  apply hf.isConvexPiecewiseLinear_valueFunction
  constructor
  · exact ⟨0, by simp [valueFunction]⟩
  · intro u
    simp [valueFunction]

/-- The identically `+∞` integrand still has a polyhedral value-function
epigraph, although the value function is not proper. -/
example :
    HasClosedPolyhedralEpigraph
      (valueFunction (fun _ : ℝ × ℝ => (⊤ : EReal))) := by
  have hf :
      HasPolyhedralEpigraph
        (fun _ : ℝ × ℝ => (⊤ : EReal)) := by
    change IsPolyhedral (epigraph (fun _ : ℝ × ℝ => (⊤ : EReal)))
    have hepi :
        epigraph (fun _ : ℝ × ℝ => (⊤ : EReal)) =
          (∅ : Set ((ℝ × ℝ) × ℝ)) := by
      ext p
      simp [epigraph]
    rw [hepi]
    exact IsPolyhedral.empty
  exact
    hf.hasClosedPolyhedralEpigraph
      |>.hasClosedPolyhedralEpigraph_valueFunction

/-- The preceding all-`+∞` value function is genuinely outside the proper CPL
wrapper. -/
example :
    ¬ IsProper
      (valueFunction (fun _ : ℝ × ℝ => (⊤ : EReal))) := by
  simp [IsProper, valueFunction]

/-- The identically `-∞` integrand exercises the other improper boundary:
its epigraph and projected epigraph are both full and polyhedral. -/
example :
    HasClosedPolyhedralEpigraph
      (valueFunction (fun _ : ℝ × ℝ => (⊥ : EReal))) := by
  have hf :
      HasPolyhedralEpigraph
        (fun _ : ℝ × ℝ => (⊥ : EReal)) := by
    change IsPolyhedral (epigraph (fun _ : ℝ × ℝ => (⊥ : EReal)))
    have hepi :
        epigraph (fun _ : ℝ × ℝ => (⊥ : EReal)) =
          (Set.univ : Set ((ℝ × ℝ) × ℝ)) := by
      ext p
      simp [epigraph]
    rw [hepi]
    exact IsPolyhedral.univ
  exact
    hf.hasClosedPolyhedralEpigraph
      |>.hasClosedPolyhedralEpigraph_valueFunction

/-- The all-`-∞` value function is also not proper. -/
example :
    ¬ IsProper
      (valueFunction (fun _ : ℝ × ℝ => (⊥ : EReal))) := by
  simp [IsProper, valueFunction]

end RW
