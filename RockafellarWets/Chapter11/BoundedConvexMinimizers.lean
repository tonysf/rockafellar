/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Bounded minimizers and convex conjugate interiors
-/
import RockafellarWets.Chapter11.ConvexMarginalGeometry
import RockafellarWets.Chapter11.DualMinimizationGrowth

open Set Bornology
namespace RW
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- For proper lsc convex functions, a nonempty bounded minimizer set is
 equivalent to level boundedness. -/
theorem argmin_nonempty_bounded_iff_levelBounded {f : E → EReal}
    (hp : IsProper f) (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) :
    ((argmin f).Nonempty ∧ IsBounded (argmin f)) ↔ IsLevelBounded f := by
  constructor
  · rintro ⟨⟨x,hx⟩,hb⟩
    have he := argmin_eq_levelSet_toReal_of_eq_iInf_of_isProper hx.1 hp
    have hn : (levelSet f ((f x).toReal)).Nonempty := he ▸ ⟨x,hx⟩
    have hh : horizonCone (levelSet f ((f x).toReal)) = ({0} : Set E) :=
      isBounded_iff_horizonCone_eq_singleton_zero.mp (he ▸ hb)
    rw [horizonCone_levelSet_eq_levelSet_horizonFunction hc hl hn] at hh
    exact (isLevelBounded_iff_horizonFunction_pos hc hl hp).mpr
      ((horizonFunction_pos_iff_levelSet_zero_eq_singleton_zero f).mpr hh)
  · intro hb
    have hi := isInfCompact_of_isLevelBounded_of_lsc hl hb
    exact ⟨argmin_nonempty_of_isInfCompact_of_lsc_of_isProper hi hl hp,
      (isCompact_argmin_of_isInfCompact_of_lsc_of_isProper hi hl hp).isBounded⟩

/-- A proper convex function need not be lsc for the bounded-solution
criterion for minimization of its conjugate. -/
theorem argmin_conjugate_nonempty_bounded_iff_interior_domain {f : E → EReal}
    (hp : IsProper f) (hc : Convex ℝ (epigraph f)) :
    ((argmin (fenchelConjugate f)).Nonempty ∧ IsBounded (argmin (fenchelConjugate f))) ↔
      (0:E) ∈ interior (effectiveDomain f) := by
  have hpc := isProper_fenchelConjugate_of_convex hp hc
  rw [argmin_nonempty_bounded_iff_levelBounded hpc (lowerSemicontinuous_fenchelConjugate f)
    (convex_epigraph_fenchelConjugate f),
    isLevelBounded_iff_zero_mem_interior_conjugate_domain hpc (lowerSemicontinuous_fenchelConjugate f)
    (convex_epigraph_fenchelConjugate f),
    biconjugate_eq_epiClosure_of_convex_closure hpc hc.closure,interior_domain_epiClosure hc]

/-- An interior finite value rules out every minus-infinite value of a
convex function, without a global lower-semicontinuity assumption. -/
theorem isProper_of_convex_finite_interior {f : E → EReal}
    (hc : Convex ℝ (epigraph f)) {x : E} {a : ℝ}
    (hx : x ∈ interior (effectiveDomain f)) (ha : f x = (a:EReal)) : IsProper f := by
  refine ⟨⟨x,ha.trans_lt (EReal.coe_lt_top a)⟩,fun y ↦ ?_⟩
  by_contra! hy
  have he := congrFun (epiClosure_of_convex_bot hc (le_bot_iff.mp hy)) x
  rw [epiClosure_eq_of_mem_interior_convex hc hx,ha,
    if_pos (subset_closure (interior_subset hx))] at he
  exact EReal.coe_ne_bot a he

/-- The bounded-solution criterion for a possibly improper convex marginal.
This is the abstract form underlying 11.39(b,c). -/
theorem argmin_conjugate_nonempty_bounded_iff_interior_finite {f : E → EReal}
    (hc : Convex ℝ (epigraph f)) (hne : (effectiveDomain f).Nonempty) :
    ((argmin (fenchelConjugate f)).Nonempty ∧ IsBounded (argmin (fenchelConjugate f))) ↔
      ((0:E) ∈ interior (effectiveDomain f) ∧ ∃ a : ℝ, f 0 = (a:EReal)) := by
  constructor
  · intro hm
    obtain ⟨v,hv⟩ := hm.1
    have hvt : fenchelConjugate f v < ⊤ := hv.1.trans_lt hv.2
    have hp : IsProper f := by
      refine ⟨hne,fun x ↦ ?_⟩
      by_contra! hx
      have hh := (le_fenchelConjugate f x v).trans_lt hvt
      rw [le_bot_iff.mp hx,EReal.coe_sub_bot] at hh
      exact lt_irrefl _ hh
    have hi := (argmin_conjugate_nonempty_bounded_iff_interior_domain hp hc).mp hm
    have ht : f 0 < ⊤ := interior_subset (s := effectiveDomain f) hi
    exact ⟨hi,⟨(f 0).toReal,(EReal.coe_toReal ht.ne (hp.2 0).ne').symm⟩⟩
  · rintro ⟨hi,a,ha⟩
    exact (argmin_conjugate_nonempty_bounded_iff_interior_domain
      (isProper_of_convex_finite_interior hc hi ha) hc).mpr hi

/-- At an interior finite point, conjugate minimizers are the subgradients
of the original convex function even if it is not globally lsc. -/
theorem argmin_conjugate_eq_subdifferential_zero_of_interior {f : E → EReal}
    (hc : Convex ℝ (epigraph f)) (hi : (0:E) ∈ interior (effectiveDomain f))
    {a : ℝ} (ha : f 0 = (a:EReal)) :
    argmin (fenchelConjugate f) = subdifferential f 0 := by
  have hp := isProper_of_convex_finite_interior hc hi ha
  have he : (⨅ v, fenchelConjugate f v) = ((-a:ℝ):EReal) := by
    rw [iInf_eq_neg_fenchelConjugate_zero,biconjugate_eq_of_mem_interior_domain hc hi,ha,EReal.coe_neg]
  ext v
  rw [mem_argmin_iff,he,mem_subdifferential_iff_fenchelConjugate_eq hp hc ha]
  simp only [inner_zero_right,zero_sub,and_iff_left (EReal.coe_lt_top (-a))]

end RW
