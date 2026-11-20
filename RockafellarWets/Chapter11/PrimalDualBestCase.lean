/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Equivalent best-case primal–dual conditions
-/
import RockafellarWets.Chapter11.PrimalDualSolutions

open Set Bornology
namespace RW
noncomputable section
variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]

/-- Simultaneous interior feasibility forces a finite common optimal value. -/
theorem primal_dual_finite_common_value_of_interiors {f : WithLp 2 (E × P) → EReal}
    (hp : IsProper f) (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f))
    (hu : (0:P) ∈ interior (effectiveDomain (parametricValue f)))
    (hv : (0:E) ∈ interior (effectiveDomain (dualParametricValue f))) :
    ∃ a : ℝ, parametricValue f 0 = (a:EReal) ∧ dualParametricValue f 0 = ((-a:ℝ):EReal) := by
  have ht : parametricValue f 0 < ⊤ := interior_subset (s := effectiveDomain _) hu
  have hqt : dualParametricValue f 0 < ⊤ := interior_subset (s := effectiveDomain _) hv
  have hqb : ⊥ < -dualParametricValue f 0 := by
    rw [EReal.lt_neg_comm,EReal.neg_bot]
    exact hqt
  have hw := primal_dual_weak_duality f
  rw [iSup_dualObjective_eq_neg_dualParametricValue,← (primal_dual_value_identities f).1] at hw
  have hb : ⊥ < parametricValue f 0 := hqb.trans_le hw
  let a := (parametricValue f 0).toReal
  have ha : parametricValue f 0 = (a:EReal) := (EReal.coe_toReal ht.ne hb.ne').symm
  refine ⟨a,ha,?_⟩
  have he := primal_dual_strong_duality_of_primal_interior hp hl hc hu
  rw [← (primal_dual_value_identities f).1,iSup_dualObjective_eq_neg_dualParametricValue,ha] at he
  simpa only [neg_neg,← EReal.coe_neg] using congrArg Neg.neg he.symm

/-- **Corollary 11.40**, all four printed conditions are equivalent.
The nested conjunction records `(a)↔(b)`, `(a)↔(c)`, and `(a)↔(d)`. -/
theorem primal_dual_best_case_equivalences {f : WithLp 2 (E × P) → EReal}
    (hp : IsProper f) (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) :
    let U := (0:P) ∈ interior (effectiveDomain (parametricValue f))
    let V := (0:E) ∈ interior (effectiveDomain (dualParametricValue f))
    let X := (argmin (primalObjective f)).Nonempty ∧ IsBounded (argmin (primalObjective f))
    let Y := (argmax (dualObjective f)).Nonempty ∧ IsBounded (argmax (dualObjective f))
    ((U ∧ V) ↔ (U ∧ X)) ∧ ((U ∧ V) ↔ (V ∧ Y)) ∧ ((U ∧ V) ↔ (X ∧ Y)) := by
  dsimp only
  have hboth : ((0:P) ∈ interior (effectiveDomain (parametricValue f)) ∧
      (0:E) ∈ interior (effectiveDomain (dualParametricValue f))) →
      ((argmin (primalObjective f)).Nonempty ∧ IsBounded (argmin (primalObjective f))) ∧
      ((argmax (dualObjective f)).Nonempty ∧ IsBounded (argmax (dualObjective f))) := by
    rintro ⟨hu,hv⟩
    obtain ⟨a,ha,hqa⟩ := primal_dual_finite_common_value_of_interiors hp hl hc hu hv
    exact ⟨(primal_optima_nonempty_bounded_iff hp hl hc).mpr ⟨hv,-a,hqa⟩,
      (dual_optima_nonempty_bounded_iff hp hc).mpr ⟨hu,a,ha⟩⟩
  exact ⟨⟨fun h ↦ ⟨h.1,(hboth h).1⟩,fun h ↦ ⟨h.1,((primal_optima_nonempty_bounded_iff hp hl hc).mp h.2).1⟩⟩,
    ⟨fun h ↦ ⟨h.2,(hboth h).2⟩,fun h ↦ ⟨((dual_optima_nonempty_bounded_iff hp hc).mp h.2).1,h.1⟩⟩,
    ⟨hboth,fun h ↦ ⟨((dual_optima_nonempty_bounded_iff hp hc).mp h.2).1,
      ((primal_optima_nonempty_bounded_iff hp hl hc).mp h.1).1⟩⟩⟩

/-- The common finite optimum is attained on both sides under any of the
equivalent conditions in 11.40; this wrapper uses condition (a). -/
theorem primal_dual_best_case_attainment {f : WithLp 2 (E × P) → EReal}
    (hp : IsProper f) (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f))
    (hu : (0:P) ∈ interior (effectiveDomain (parametricValue f)))
    (hv : (0:E) ∈ interior (effectiveDomain (dualParametricValue f))) :
    ∃ (a : ℝ) (x : E) (y : P),
      x ∈ argmin (primalObjective f) ∧ y ∈ argmax (dualObjective f) ∧
      (⨅ z, primalObjective f z) = (a:EReal) ∧ (⨆ v, dualObjective f v) = (a:EReal) := by
  obtain ⟨a,ha,hqa⟩ := primal_dual_finite_common_value_of_interiors hp hl hc hu hv
  obtain ⟨x,hx⟩ := ((primal_optima_nonempty_bounded_iff hp hl hc).mpr ⟨hv,-a,hqa⟩).1
  obtain ⟨y,hy⟩ := ((dual_optima_nonempty_bounded_iff hp hc).mpr ⟨hu,a,ha⟩).1
  refine ⟨a,x,y,hx,hy,ha,?_⟩
  rw [iSup_dualObjective_eq_neg_dualParametricValue,hqa,EReal.coe_neg,neg_neg]

end
end RW
