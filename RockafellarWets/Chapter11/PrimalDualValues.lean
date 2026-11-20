/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Primal and dual value functions
-/
import RockafellarWets.Chapter11.ConjugateRestrictions
import RockafellarWets.Chapter11.ConjugateSubgradientGraph
import RockafellarWets.Chapter10.ParametricEpigraphProjection

open Set
open scoped InnerProductSpace
namespace RW
noncomputable section
variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]

/-- The primal objective `φ(x)=f(x,0)` in 11.38–11.39. -/
def primalObjective (f : WithLp 2 (E × P) → EReal) : E → EReal := partialFunction f 0

/-- The dual maximization objective `ψ(y)=-f*(0,y)`. -/
def dualObjective (f : WithLp 2 (E × P) → EReal) (y : P) : EReal :=
  -fenchelConjugate f (WithLp.toLp 2 (0,y))

/-- The dual perturbation value `q(v)=inf_y f*(v,y)`. -/
def dualParametricValue (f : WithLp 2 (E × P) → EReal) (v : E) : EReal :=
  ⨅ y : P, fenchelConjugate f (WithLp.toLp 2 (v,y))

theorem dualParametricValue_eq_conjugateSliceValue (f : WithLp 2 (E × P) → EReal) :
    dualParametricValue f = conjugateSliceValue f 0 := by
  funext v
  simp only [dualParametricValue,conjugateSliceValue,inner_zero_right,EReal.coe_zero,sub_zero]

theorem fenchelConjugate_parametricValue (f : WithLp 2 (E × P) → EReal) :
    fenchelConjugate (parametricValue f) = fun y ↦ fenchelConjugate f (WithLp.toLp 2 (0,y)) := by
  funext y
  exact fenchelConjugate_valueFunction (fun p ↦ f (WithLp.toLp 2 p)) y

/-- **Lemma 11.38**, both value identities without any convexity assumptions. -/
theorem primal_dual_value_identities (f : WithLp 2 (E × P) → EReal) :
    parametricValue f 0 = (⨅ x, primalObjective f x) ∧
    fenchelConjugate (fenchelConjugate (parametricValue f)) 0 = (⨆ y, dualObjective f y) := by
  refine ⟨rfl,?_⟩
  rw [fenchelConjugate_parametricValue]
  simp only [fenchelConjugate,dualObjective,inner_zero_left,EReal.coe_zero,zero_sub]

theorem iSup_dualObjective_eq_neg_dualParametricValue (f : WithLp 2 (E × P) → EReal) :
    (⨆ y, dualObjective f y) = -dualParametricValue f 0 := by
  have he := ereal_coe_sub_iInf 0 (fun y : P ↦ fenchelConjugate f (WithLp.toLp 2 (0,y)))
  simpa only [EReal.coe_zero,zero_sub,dualObjective,dualParametricValue] using he.symm

/-- Weak duality, **11.39(a)**, valid even for nonconvex integrands. -/
theorem primal_dual_weak_duality (f : WithLp 2 (E × P) → EReal) :
    (⨆ y, dualObjective f y) ≤ (⨅ x, primalObjective f x) := by
  rw [← (primal_dual_value_identities f).1,← (primal_dual_value_identities f).2]
  exact fenchelConjugate_fenchelConjugate_le (parametricValue f) 0

theorem dualObjective_le_primalObjective (f : WithLp 2 (E × P) → EReal) (x : E) (y : P) :
    dualObjective f y ≤ primalObjective f x :=
  (le_iSup (dualObjective f) y).trans ((primal_dual_weak_duality f).trans (iInf_le (primalObjective f) x))

theorem effectiveDomain_parametricValue (f : WithLp 2 (E × P) → EReal) :
    effectiveDomain (parametricValue f) = WithLp.sndL 2 ℝ E P '' effectiveDomain f := by
  ext u
  change (⨅ x : E, f (WithLp.toLp 2 (x,u))) < ⊤ ↔ _
  rw [iInf_lt_iff]
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨WithLp.toLp 2 (x,u),hx,rfl⟩
  · rintro ⟨q,hq,he⟩
    change q.snd = u at he
    subst u
    exact ⟨q.fst,hq⟩

theorem effectiveDomain_dualParametricValue (f : WithLp 2 (E × P) → EReal) :
    effectiveDomain (dualParametricValue f) = WithLp.fstL 2 ℝ E P '' effectiveDomain (fenchelConjugate f) := by
  ext v
  change (⨅ y : P, fenchelConjugate f (WithLp.toLp 2 (v,y))) < ⊤ ↔ _
  rw [iInf_lt_iff]
  constructor
  · rintro ⟨y,hy⟩
    exact ⟨WithLp.toLp 2 (v,y),hy,rfl⟩
  · rintro ⟨q,hq,he⟩
    change q.fst = v at he
    subst v
    exact ⟨q.snd,hq⟩

/-- The two feasibility/value equivalences in **11.39(a)**. -/
theorem primal_dual_finite_sided_value_iff (f : WithLp 2 (E × P) → EReal) :
    ((⨅ x, primalObjective f x) < ⊤ ↔ (0:P) ∈ effectiveDomain (parametricValue f)) ∧
    (⊥ < (⨆ y, dualObjective f y) ↔ (0:E) ∈ effectiveDomain (dualParametricValue f)) := by
  refine ⟨Iff.rfl,?_⟩
  rw [iSup_dualObjective_eq_neg_dualParametricValue]
  change ⊥ < -dualParametricValue f 0 ↔ dualParametricValue f 0 < ⊤
  rw [EReal.lt_neg_comm,EReal.neg_bot]

/-- Interior primal feasibility gives strong duality, including infinite
optimal values, as asserted in **11.39(a)**. -/
theorem primal_dual_strong_duality_of_primal_interior {f : WithLp 2 (E × P) → EReal}
    (hp : IsProper f) (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f))
    (hu : (0:P) ∈ interior (effectiveDomain (parametricValue f))) :
    (⨅ x, primalObjective f x) = (⨆ y, dualObjective f y) := by
  rw [effectiveDomain_parametricValue] at hu
  have he := fenchelConjugate_partialFunction_of_interior hp hl hc hu
  rw [← dualParametricValue_eq_conjugateSliceValue] at he
  rw [iInf_eq_neg_fenchelConjugate_zero,iSup_dualObjective_eq_neg_dualParametricValue]
  exact congrArg (fun h : E → EReal ↦ -h 0) he

/-- The second conjugacy relation in Figure 11–5. -/
theorem fenchelConjugate_dualParametricValue {f : WithLp 2 (E × P) → EReal}
    (hp : IsProper f) (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) :
    fenchelConjugate (dualParametricValue f) = primalObjective f := by
  rw [dualParametricValue_eq_conjugateSliceValue,fenchelConjugate_conjugateSliceValue hp hl hc]
  rfl

end
end RW
