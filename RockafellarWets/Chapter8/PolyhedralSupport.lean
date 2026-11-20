/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Piecewise-linear support functions

Proposition 8.29(c) needs a closure on the set side. The open positive
half-line and the closed positive half-line have the same support function.
-/

import RockafellarWets.Chapter8.SupportCorrespondence
import RockafellarWets.Chapter3.PolyhedralFunctions.Core
import RockafellarWets.Chapter3.MinkowskiWeyl

open Set
open scoped InnerProductSpace Pointwise

namespace RW

section LinearBounds
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem nonpos_conicHull_iff (l : F →L[ℝ] ℝ) (B : Set F) :
    (∀ v ∈ conicHull B, l v ≤ 0) ↔ ∀ v ∈ B, l v ≤ 0 := by
  let H := {v : F | l v ≤ 0}
  have hcone : IsCone H := ⟨by simp [H], fun {x} hx {t} ht ↦ by
    change l (t • x) ≤ 0
    simpa [smul_eq_mul] using mul_nonpos_of_nonneg_of_nonpos ht.le (show l x ≤ 0 from hx)⟩
  exact conicHull_subset_iff (convex_halfSpace_le l.toLinearMap.isLinear 0) hcone

private theorem le_extendedConvexHull_iff (l : F →L[ℝ] ℝ) {A B : Set F} (hne : A.Nonempty) (c : ℝ) :
    (∀ v ∈ extendedConvexHull A B, l v ≤ c) ↔ (∀ v ∈ A, l v ≤ c) ∧ (∀ v ∈ B, l v ≤ 0) := by
  constructor
  · intro h
    refine ⟨fun v hv ↦ h _ (subset_extendedConvexHull_left _ _ hv), fun v hv ↦ ?_⟩
    obtain ⟨a,ha⟩ := hne
    by_contra! hpos
    let t := (|c-l a|+1)/l v
    have ht : 0 < t := by dsimp [t]; positivity
    have hle := h _ (show a+t • v ∈ extendedConvexHull A B from
      ⟨a,subset_convexHull _ _ ha,_,(isCone_conicHull B).2 (subset_conicHull hv) ht,rfl⟩)
    rw [map_add, map_smul, smul_eq_mul, show t*l v=|c-l a|+1 by dsimp [t]; field_simp] at hle
    linarith [le_abs_self (c-l a)]
  · rintro ⟨hA,hB⟩ _ ⟨a,ha,b,hb,rfl⟩
    have ha' : l a ≤ c := convexHull_min hA (convex_halfSpace_le l.toLinearMap.isLinear c) ha
    have hb' := (nonpos_conicHull_iff l B).2 hB b hb
    rw [map_add]; linarith

end LinearBounds

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- In the polyhedral case the support function is convex piecewise linear. -/
theorem isConvexPiecewiseLinear_supportFunction {C : Set E} (hC : IsPolyhedral C)
    (hne : C.Nonempty) : IsConvexPiecewiseLinear (supportFunction C) := by
  obtain ⟨s,t,rfl⟩ := hC
  have hs : (s : Set E).Nonempty := by
    by_contra! he
    simp [he] at hne
  apply HasPolyhedralEpigraph.isConvexPiecewiseLinear_of_isProper _ (isProper_supportFunction hne)
  let L := fun v : E ↦ (innerSL ℝ v).comp (ContinuousLinearMap.fst ℝ E ℝ)
  let P := fun v : E ↦ {p : E × ℝ | (L v - ContinuousLinearMap.snd ℝ E ℝ) p ≤ 0}
  let Q := fun v : E ↦ {p : E × ℝ | L v p ≤ 0}
  have heq : epigraph (supportFunction (extendedConvexHull (s : Set E) t)) =
      (⋂ v ∈ s, P v) ∩ (⋂ v ∈ t, Q v) := by
    ext p
    rw [mem_epigraph_iff, supportFunction_le_iff]
    have h := le_extendedConvexHull_iff (innerSL ℝ p.1) (B := (t:Set E)) hs p.2
    simpa only [mem_inter_iff, mem_iInter, mem_setOf_eq, P, Q, L, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.comp_apply, show (ContinuousLinearMap.fst ℝ E ℝ : E × ℝ → E) = Prod.fst from rfl,
      show (ContinuousLinearMap.snd ℝ E ℝ : E × ℝ → ℝ) = Prod.snd from rfl,
      innerSL_apply_apply, sub_nonpos, real_inner_comm p.1, EReal.coe_le_coe_iff, Finset.mem_coe] using h
  change IsPolyhedral (epigraph _)
  rw [heq]
  exact (IsPolyhedral.iInter_finset s P fun _ _ ↦ isPolyhedral_linearHalfspace _ _).inter
    (IsPolyhedral.iInter_finset t Q fun _ _ ↦ isPolyhedral_linearHalfspace _ _)

/-- **Proposition 8.29(c)** with the necessary closure. For a convex set
its support function can detect the polyhedrality of its closure. -/
theorem isConvexPiecewiseLinear_supportFunction_iff {C : Set E} (hc : Convex ℝ C) (hne : C.Nonempty) :
    IsConvexPiecewiseLinear (supportFunction C) ↔ IsPolyhedral (closure C) := by
  have hclose := supportFunction_closure_convexHull C
  rw [hc.convexHull_eq] at hclose
  refine ⟨fun hp ↦ ?_, fun h ↦ hclose ▸ isConvexPiecewiseLinear_supportFunction h (hne.mono subset_closure)⟩
  have hminor := linearMinorantSet_supportFunction C
  rw [hc.convexHull_eq] at hminor
  rw [← hminor]
  obtain ⟨s,hs⟩ := (isPolyhedral_iff_isFinitelyGeneratedCone_of_isCone
    (isCone_epigraph_of_positivelyHomogeneous (sublinear_supportFunction C).1)).1 hp.2.isPolyhedral
  let P := fun p : E × ℝ ↦ {v : E | innerSL ℝ p.1 v ≤ p.2}
  have heq : linearMinorantSet (supportFunction C) = ⋂ p ∈ s, P p := by
    ext v
    rw [mem_linearMinorantSet_iff_epigraph, hs]
    let l := (innerSL ℝ v).comp (ContinuousLinearMap.fst ℝ E ℝ) - ContinuousLinearMap.snd ℝ E ℝ
    have h := nonpos_conicHull_iff l (s : Set (E × ℝ))
    simpa only [l, P, mem_iInter, mem_setOf_eq, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.comp_apply, show (ContinuousLinearMap.fst ℝ E ℝ : E × ℝ → E) = Prod.fst from rfl,
      show (ContinuousLinearMap.snd ℝ E ℝ : E × ℝ → ℝ) = Prod.snd from rfl,
      innerSL_apply_apply, sub_nonpos, Finset.mem_coe, real_inner_comm v] using h
  rw [heq]
  exact IsPolyhedral.iInter_finset s P fun p _ ↦ isPolyhedral_linearHalfspace _ _

/-- The positive open half-line is a convex, nonpolyhedral set with a
convex piecewise-linear support function. -/
theorem supportFunction_open_halfLine_polyhedral_obstruction :
    ¬ IsPolyhedral (Ioi (0 : ℝ)) ∧ IsConvexPiecewiseLinear (supportFunction (Ioi (0 : ℝ))) := by
  constructor
  · intro hp
    have he := hp.isClosed.closure_eq
    rw [closure_Ioi] at he
    exact (lt_irrefl 0) (show (0:ℝ) ∈ Ioi 0 from he ▸ (show (0:ℝ) ∈ Ici 0 by simp))
  · apply (isConvexPiecewiseLinear_supportFunction_iff (convex_Ioi (0:ℝ)) nonempty_Ioi).2
    rw [closure_Ioi]
    exact IsPolyhedral.Ici _

end RW
