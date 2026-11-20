/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Conjugating a restriction to a parameter slice
-/

import RockafellarWets.Chapter11.DualOperationQualifications
import RockafellarWets.Chapter11.DualMinimization
import RockafellarWets.Chapter10.PartialSubgradients

open Set
open scoped InnerProductSpace

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The dual marginal for restriction to a parameter value `u` in 11.23(c). -/
noncomputable def conjugateSliceValue (f : WithLp 2 (E × F) → EReal) (u : F) (v : E) : EReal :=
  ⨅ y : F, fenchelConjugate f (WithLp.toLp 2 (v,y)) - (⟪y,u⟫_ℝ : EReal)

private noncomputable def sliceDualCost (f : WithLp 2 (E × F) → EReal) (u : F)
    (q : WithLp 2 (E × F)) : EReal :=
  fenchelConjugate f q - (⟪WithLp.toLp 2 (0,u),q⟫_ℝ : EReal)

private theorem sliceDualCost_conjugate {f : WithLp 2 (E × F) → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) (u : F) (q : WithLp 2 (E × F)) :
    fenchelConjugate (sliceDualCost f u) q = f (q + WithLp.toLp 2 (0,u)) := by
  unfold sliceDualCost
  rw [fenchelConjugate_sub_inner,fenchelConjugate_fenchelConjugate_eq hp hl hc]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem sliceValue_fiber (f : WithLp 2 (E × F) → EReal) (u : F) :
    conjugateSliceValue f u = fiberInfimum (WithLp.fstL 2 ℝ E F) (sliceDualCost f u) := by
  funext v
  apply le_antisymm (le_iInf fun q ↦ iInf_le_of_le q.val.snd ?_) (le_iInf fun y ↦ ?_)
  · obtain ⟨q,hq⟩ := q
    change q.fst = v at hq
    subst v
    simp [sliceDualCost,WithLp.prod_inner_apply,real_inner_comm u]
    exact le_rfl
  · apply iInf_le_of_le ⟨WithLp.toLp 2 (v,y),rfl⟩
    simp [sliceDualCost,WithLp.prod_inner_apply,real_inner_comm u]

/-- The dual marginal has the primal slice as its conjugate. -/
theorem fenchelConjugate_conjugateSliceValue {f : WithLp 2 (E × F) → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) (u : F) :
    fenchelConjugate (conjugateSliceValue f u) = partialFunction f u := by
  funext x
  rw [sliceValue_fiber,fenchelConjugate_fiberInfimum]
  change fenchelConjugate (sliceDualCost f u) ((WithLp.fstL 2 ℝ E F).adjoint x) = f _
  rw [sliceDualCost_conjugate hp hl hc]
  have he : (WithLp.fstL 2 ℝ E F).adjoint x = WithLp.toLp 2 (x,0) := by
    apply ext_inner_right ℝ
    intro q
    rw [ContinuousLinearMap.adjoint_inner_left]
    simp [WithLp.prod_inner_apply]
  rw [he]
  congr 1
  apply WithLp.ofLp_injective
  exact Prod.ext (add_zero x) (zero_add u)

/-- **Theorem 11.23(c)** on every slice in the projected domain. -/
theorem fenchelConjugate_partialFunction_eq_epiClosure {f : WithLp 2 (E × F) → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) {u : F} (hu : ∃ x, f (WithLp.toLp 2 (x,u)) < ⊤) :
    fenchelConjugate (partialFunction f u) = epiClosure (conjugateSliceValue f u) := by
  rw [← fenchelConjugate_conjugateSliceValue hp hl hc u]
  apply biconjugate_eq_epiClosure_of_convex_closure
  · rw [fenchelConjugate_conjugateSliceValue hp hl hc u]
    exact ⟨hu,fun x ↦ hp.2 _⟩
  · rw [sliceValue_fiber,closure_epigraph_fiberInfimum]
    exact ((convex_epigraph_sub_inner (convex_epigraph_fenchelConjugate f) _).linear_image _).closure

/-- **Theorem 11.23(c)**. Interior dual feasibility gives the formula with
no closure, including when the joint domain has empty interior. -/
theorem fenchelConjugate_partialFunction_of_interior {f : WithLp 2 (E × F) → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) {u : F}
    (hu : u ∈ interior (WithLp.sndL 2 ℝ E F '' effectiveDomain f)) :
    fenchelConjugate (partialFunction f u) = conjugateSliceValue f u := by
  obtain ⟨q,hq,he⟩ := interior_subset hu
  have hfin : ∃ x, f (WithLp.toLp 2 (x,u)) < ⊤ := by
    refine ⟨q.fst,?_⟩
    subst u
    exact hq
  rw [fenchelConjugate_partialFunction_eq_epiClosure hp hl hc hfin,sliceValue_fiber]
  apply epiClosure_eq_of_lowerSemicontinuous
  apply lowerSemicontinuous_of_isClosed_epigraph_ereal
  have hcp := isProper_sub_inner (isProper_fenchelConjugate hp hl hc) (WithLp.toLp 2 (0,u))
  have hcl := lowerSemicontinuous_sub_inner (lowerSemicontinuous_fenchelConjugate f) (WithLp.toLp 2 (0,u))
  have hcc := convex_epigraph_sub_inner (convex_epigraph_fenchelConjugate f) (WithLp.toLp 2 (0,u))
  apply isClosed_epigraph_fiberInfimum_of_horizon_ker _ hcl hcp
  intro w hw hh
  change w.fst = 0 at hw
  suffices hz : w.snd = 0 by
    apply WithLp.ofLp_injective
    exact Prod.ext hw hz
  by_contra hn
  have hpos := (mem_interior_iff_inner_lt_supportFunction
    ((convex_effectiveDomain_of_convex_epigraph hc).linear_image (WithLp.sndL 2 ℝ E F).toLinearMap)
    ⟨u,interior_subset hu⟩ u).mp hu w.snd hn
  apply (not_le_of_gt hpos)
  apply (supportFunction_le_iff _ _ _).mpr
  rintro y ⟨p,hy,rfl⟩
  let r := WithLp.toLp 2 (p.fst,p.snd-u)
  have hr : r ∈ effectiveDomain (fenchelConjugate (sliceDualCost f u)) := by
    change fenchelConjugate (sliceDualCost f u) r < ⊤
    rw [sliceDualCost_conjugate hp hl hc]
    have he : r + WithLp.toLp 2 (0,u) = p := by
      apply WithLp.ofLp_injective
      exact Prod.ext (add_zero _) (sub_add_cancel _ _)
    rwa [he]
  change horizonFunction (sliceDualCost f u) w ≤ 0 at hh
  rw [(horizon_conjugate_support_identities (f := sliceDualCost f u) hcp hcl hcc).1] at hh
  have hi := (supportFunction_le_iff _ _ _).mp hh r hr
  have hrw : ⟪r,w⟫_ℝ = ⟪p.snd,w.snd⟫_ℝ - ⟪u,w.snd⟫_ℝ := by
    simp [r,WithLp.prod_inner_apply,hw,inner_sub_left]
  rw [hrw, ← EReal.coe_zero, EReal.coe_le_coe_iff] at hi
  exact EReal.coe_le_coe_iff.mpr (sub_nonpos.mp hi)

end RW
