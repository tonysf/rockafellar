/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Interior feasibility and bounded optimal-solution sets
-/
import RockafellarWets.Chapter11.PrimalDualOptimality
import RockafellarWets.Chapter11.BoundedConvexMinimizers

open Set Bornology
open scoped InnerProductSpace
namespace RW
noncomputable section
variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]

theorem parametricValue_eq_fiberInfimum (f : WithLp 2 (E × P) → EReal) :
    parametricValue f = fiberInfimum (WithLp.sndL 2 ℝ E P) f := by
  funext u
  apply le_antisymm (le_iInf fun q ↦ iInf_le_of_le q.val.fst ?_) (le_iInf fun x ↦ ?_)
  · obtain ⟨q,hq⟩ := q
    change q.snd = u at hq
    subst u
    exact le_rfl
  · exact iInf_le_of_le ⟨WithLp.toLp 2 (x,u),rfl⟩ le_rfl

theorem dualParametricValue_eq_fiberInfimum (f : WithLp 2 (E × P) → EReal) :
    dualParametricValue f = fiberInfimum (WithLp.fstL 2 ℝ E P) (fenchelConjugate f) := by
  funext v
  apply le_antisymm (le_iInf fun q ↦ iInf_le_of_le q.val.snd ?_) (le_iInf fun y ↦ ?_)
  · obtain ⟨q,hq⟩ := q
    change q.fst = v at hq
    subst v
    exact le_rfl
  · exact iInf_le_of_le ⟨WithLp.toLp 2 (v,y),rfl⟩ le_rfl

/-- Inf-projection preserves convexity (2.22(a)); unlike the Chapter 10
`convex_epigraph_parametricValue`, no semicontinuity or level-boundedness is needed. -/
theorem convex_epigraph_parametricValue_of_convex {f : WithLp 2 (E × P) → EReal}
    (hc : Convex ℝ (epigraph f)) : Convex ℝ (epigraph (parametricValue f)) := by
  rw [parametricValue_eq_fiberInfimum]
  exact convex_epigraph_fiberInfimum _ hc

theorem convex_epigraph_dualParametricValue (f : WithLp 2 (E × P) → EReal) :
    Convex ℝ (epigraph (dualParametricValue f)) := by
  rw [dualParametricValue_eq_fiberInfimum]
  exact convex_epigraph_fiberInfimum _ (convex_epigraph_fenchelConjugate f)

/-- The remaining convexity assertions of the **11.39** preamble: the value
functions `p`, `q` and their domains `U = dom p`, `V = dom q` are convex. -/
theorem primal_dual_value_geometry {f : WithLp 2 (E × P) → EReal}
    (hc : Convex ℝ (epigraph f)) :
    Convex ℝ (epigraph (parametricValue f)) ∧ Convex ℝ (effectiveDomain (parametricValue f)) ∧
    Convex ℝ (epigraph (dualParametricValue f)) ∧
      Convex ℝ (effectiveDomain (dualParametricValue f)) :=
  ⟨convex_epigraph_parametricValue_of_convex hc,
    convex_effectiveDomain_of_convex_epigraph (convex_epigraph_parametricValue_of_convex hc),
    convex_epigraph_dualParametricValue f,
    convex_effectiveDomain_of_convex_epigraph (convex_epigraph_dualParametricValue f)⟩

/-- The convexity/semicontinuity preamble of **11.39**. Convexity of `-ψ`
is the concavity statement for the maximization objective. -/
theorem primal_dual_objective_geometry {f : WithLp 2 (E × P) → EReal}
    (hp : IsProper f) (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) :
    LowerSemicontinuous (primalObjective f) ∧ Convex ℝ (epigraph (primalObjective f)) ∧
    UpperSemicontinuous (dualObjective f) ∧ Convex ℝ (epigraph (fun y ↦ -dualObjective f y)) := by
  have he : dualObjective f = fun y ↦ -fenchelConjugate (parametricValue f) y := by
    rw [fenchelConjugate_parametricValue]
    rfl
  rw [← fenchelConjugate_dualParametricValue hp hl hc]
  refine ⟨lowerSemicontinuous_fenchelConjugate _,convex_epigraph_fenchelConjugate _,?_,?_⟩
  · rw [he]
    exact continuous_neg.comp_lowerSemicontinuous_antitone (lowerSemicontinuous_fenchelConjugate _)
      EReal.neg_strictAnti.antitone
  · simp only [he,neg_neg]
    exact convex_epigraph_fenchelConjugate _

/-- The other interior-feasibility alternative in **11.39(a)**. -/
theorem primal_dual_strong_duality_of_dual_interior {f : WithLp 2 (E × P) → EReal}
    (hp : IsProper f) (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f))
    (hv : (0:E) ∈ interior (effectiveDomain (dualParametricValue f))) :
    (⨅ x, primalObjective f x) = (⨆ y, dualObjective f y) := by
  rw [← fenchelConjugate_dualParametricValue hp hl hc,iInf_eq_neg_fenchelConjugate_zero,
    biconjugate_eq_of_mem_interior_domain (convex_epigraph_dualParametricValue f) hv,
    iSup_dualObjective_eq_neg_dualParametricValue]

private theorem argmax_dual_eq_argmin_conjugate (f : WithLp 2 (E × P) → EReal) :
    argmax (dualObjective f) = argmin (fenchelConjugate (parametricValue f)) := by
  have he : (⨆ y, dualObjective f y) = -(⨅ y, fenchelConjugate (parametricValue f) y) := by
    have h := ereal_coe_sub_iInf 0 (fenchelConjugate (parametricValue f))
    simpa only [fenchelConjugate_parametricValue,EReal.coe_zero,zero_sub,dualObjective] using h.symm
  ext y
  change (dualObjective f y = ⨆ z,dualObjective f z) ∧ ⊥ < (⨆ z,dualObjective f z) ↔ _
  rw [he]
  change (-fenchelConjugate f (WithLp.toLp 2 (0,y)) = -(⨅ z,fenchelConjugate (parametricValue f) z)) ∧
    ⊥ < -(⨅ z,fenchelConjugate (parametricValue f) z) ↔ _
  rw [← congrFun (fenchelConjugate_parametricValue f) y,neg_inj,EReal.lt_neg_comm,EReal.neg_bot]
  rfl

/-- **Theorem 11.39(b)**, the full iff and subgradient identification. -/
theorem dual_optima_nonempty_bounded_iff {f : WithLp 2 (E × P) → EReal}
    (hp : IsProper f) (hc : Convex ℝ (epigraph f)) :
    ((argmax (dualObjective f)).Nonempty ∧ IsBounded (argmax (dualObjective f))) ↔
      ((0:P) ∈ interior (effectiveDomain (parametricValue f)) ∧
        ∃ a : ℝ, parametricValue f 0 = (a:EReal)) := by
  rw [argmax_dual_eq_argmin_conjugate]
  apply argmin_conjugate_nonempty_bounded_iff_interior_finite (convex_epigraph_parametricValue_of_convex hc)
  rw [effectiveDomain_parametricValue]
  obtain ⟨q,hq⟩ := hp.1
  exact ⟨q.snd,q,hq,rfl⟩

theorem dual_optima_eq_subdifferential {f : WithLp 2 (E × P) → EReal}
    (hc : Convex ℝ (epigraph f)) (hu : (0:P) ∈ interior (effectiveDomain (parametricValue f)))
    {a : ℝ} (ha : parametricValue f 0 = (a:EReal)) :
    argmax (dualObjective f) = subdifferential (parametricValue f) 0 := by
  rw [argmax_dual_eq_argmin_conjugate]
  exact argmin_conjugate_eq_subdifferential_zero_of_interior (convex_epigraph_parametricValue_of_convex hc) hu ha

/-- **Theorem 11.39(c)**, using finiteness of `q(0)` equivalently to finiteness
of the dual optimum `-q(0)`. -/
theorem primal_optima_nonempty_bounded_iff {f : WithLp 2 (E × P) → EReal}
    (hp : IsProper f) (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) :
    ((argmin (primalObjective f)).Nonempty ∧ IsBounded (argmin (primalObjective f))) ↔
      ((0:E) ∈ interior (effectiveDomain (dualParametricValue f)) ∧
        ∃ a : ℝ, dualParametricValue f 0 = (a:EReal)) := by
  rw [← fenchelConjugate_dualParametricValue hp hl hc]
  apply argmin_conjugate_nonempty_bounded_iff_interior_finite (convex_epigraph_dualParametricValue f)
  rw [effectiveDomain_dualParametricValue]
  obtain ⟨q,hq⟩ := (isProper_fenchelConjugate hp hl hc).1
  exact ⟨q.fst,q,hq,rfl⟩

theorem primal_optima_eq_subdifferential {f : WithLp 2 (E × P) → EReal}
    (hp : IsProper f) (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f))
    (hv : (0:E) ∈ interior (effectiveDomain (dualParametricValue f)))
    {a : ℝ} (ha : dualParametricValue f 0 = (a:EReal)) :
    argmin (primalObjective f) = subdifferential (dualParametricValue f) 0 := by
  rw [← fenchelConjugate_dualParametricValue hp hl hc]
  exact argmin_conjugate_eq_subdifferential_zero_of_interior (convex_epigraph_dualParametricValue f) hv ha

end
end RW
