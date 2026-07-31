/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3D: Horizon Cones from Constraints

This file formalizes Exercise 3.24 from Rockafellar and Wets,
*Variational Analysis*.  A feasible set is represented by an ambient set
and a family of finite lower-level constraints.
-/

import RockafellarWets.Chapter3.Coercivity

open Set EReal

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The feasible set cut out from `X` by the inequalities `f i x ≤ 0`. -/
def constraintSet {ι : Type*} (X : Set E) (f : ι → E → EReal) : Set E :=
  X ∩ ⋂ i, levelSet (f i) (0 : EReal)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
@[simp] theorem mem_constraintSet {ι : Type*} {X : Set E}
    {f : ι → E → EReal} {x : E} :
    x ∈ constraintSet X f ↔ x ∈ X ∧ ∀ i, f i x ≤ 0 := by
  simp [constraintSet, levelSet]

/-- **Exercise 3.24**, inclusion: a horizon direction of a constrained set is
a horizon direction of the ambient set and satisfies every horizon
constraint. -/
theorem horizonCone_constraintSet_subset {ι : Type*}
    (X : Set E) (f : ι → E → EReal) :
    horizonCone (constraintSet X f) ⊆
      horizonCone X ∩ ⋂ i, levelSet (horizonFunction (f i)) (0 : EReal) := by
  intro w hw
  refine ⟨horizonCone_mono (inter_subset_left : constraintSet X f ⊆ X) hw, ?_⟩
  refine Set.mem_iInter.2 fun i => ?_
  have hwLevel : w ∈ horizonCone (levelSet (f i) (0 : ℝ)) := by
    apply horizonCone_mono (D := levelSet (f i) (0 : ℝ)) ?_ hw
    intro x hx
    exact (mem_constraintSet.mp hx).2 i
  exact horizonCone_levelSet_subset_levelSet_horizonFunction (f := f i) 0 hwLevel

/-- **Exercise 3.24**, equality case: for a nonempty closed convex ambient
set and lower-semicontinuous convex constraints, the horizon cone is described
exactly by the horizon constraints. -/
theorem horizonCone_constraintSet_eq {ι : Type*}
    {X : Set E} {f : ι → E → EReal}
    (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (hfconv : ∀ i, Convex ℝ (epigraph (f i)))
    (hflsc : ∀ i, LowerSemicontinuous (f i))
    (hne : (constraintSet X f).Nonempty) :
    horizonCone (constraintSet X f) =
      horizonCone X ∩ ⋂ i, levelSet (horizonFunction (f i)) (0 : EReal) := by
  rcases hne with ⟨x, hx⟩
  have hxX : x ∈ X := (mem_constraintSet.mp hx).1
  have hxLevel : ∀ i, x ∈ levelSet (f i) (0 : ℝ) := by
    intro i
    exact (mem_constraintSet.mp hx).2 i
  have hlevelsNonempty : (⋂ i, levelSet (f i) (0 : ℝ)).Nonempty :=
    ⟨x, Set.mem_iInter.2 hxLevel⟩
  have hlevelsConvex : Convex ℝ (⋂ i, levelSet (f i) (0 : ℝ)) :=
    convex_iInter fun i => convex_levelSet_of_convex_epigraph (hfconv i) 0
  have hlevelsClosed : IsClosed (⋂ i, levelSet (f i) (0 : ℝ)) :=
    isClosed_iInter fun i => isClosed_levelSet_of_lsc_ereal (hflsc i) 0
  have hconstraintNonempty :
      (X ∩ ⋂ i, levelSet (f i) (0 : ℝ)).Nonempty :=
    ⟨x, hxX, Set.mem_iInter.2 hxLevel⟩
  calc
    horizonCone (constraintSet X f) =
        horizonCone X ∩ horizonCone (⋂ i, levelSet (f i) (0 : ℝ)) := by
      rw [constraintSet]
      exact horizonCone_inter_eq_inter_horizonCone
        hXconv hlevelsConvex hXclosed hlevelsClosed hconstraintNonempty
    _ = horizonCone X ∩ ⋂ i, horizonCone (levelSet (f i) (0 : ℝ)) := by
      rw [horizonCone_iInter_eq_iInter_horizonCone
        (fun i => convex_levelSet_of_convex_epigraph (hfconv i) 0)
        (fun i => isClosed_levelSet_of_lsc_ereal (hflsc i) 0)
        hlevelsNonempty]
    _ = horizonCone X ∩
        ⋂ i, levelSet (horizonFunction (f i)) (0 : EReal) := by
      congr 1
      apply Set.iInter_congr
      intro i
      exact horizonCone_levelSet_eq_levelSet_horizonFunction
        (hfconv i) (hflsc i) ⟨x, hxLevel i⟩

/-- **Exercise 3.24**, exact finite-valued specialization. In finite
dimensions, convexity of a real-valued function on the whole space supplies
the lower-semicontinuity hypothesis in `horizonCone_constraintSet_eq`. -/
theorem horizonCone_constraintSet_coe_real_eq
    [FiniteDimensional ℝ E] {ι : Type*}
    {X : Set E} {f : ι → E → ℝ}
    (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (hfconv :
      ∀ i, Convex ℝ (epigraph (fun x => ((f i x : ℝ) : EReal))))
    (hne :
      (constraintSet X (fun i x => ((f i x : ℝ) : EReal))).Nonempty) :
    horizonCone
        (constraintSet X (fun i x => ((f i x : ℝ) : EReal))) =
      horizonCone X ∩
        ⋂ i,
          levelSet
            (horizonFunction (fun x => ((f i x : ℝ) : EReal)))
            (0 : EReal) := by
  exact horizonCone_constraintSet_eq
    hXconv hXclosed hfconv
    (fun i => lowerSemicontinuous_coe_real_of_convex_epigraph (hfconv i))
    hne

end RW
