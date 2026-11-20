/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Exposed faces and subgradients
-/

import RockafellarWets.Chapter8.SupportCorrespondence
import RockafellarWets.Chapter8.ConvexSubgradients

open Set
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Corollary 8.25.** The subgradients of a support function are precisely
the points attaining its support value. -/
theorem subdifferential_supportFunction {D : Set E} (hc : Convex ℝ D) (hcl : IsClosed D)
    (hn : D.Nonempty) {w : E} (hw : w ∈ effectiveDomain (supportFunction D)) :
    subdifferential (supportFunction D) w =
      {v ∈ D | (⟪v,w⟫_ℝ : EReal) = supportFunction D w} := by
  have hp := isProper_supportFunction hn
  let c := (supportFunction D w).toReal
  have hval : supportFunction D w = (c : EReal) := (EReal.coe_toReal
    (show supportFunction D w < ⊤ from hw).ne (hp.2 w).ne').symm
  have hD : linearMinorantSet (supportFunction D) = D := by
    rw [linearMinorantSet_supportFunction, hc.convexHull_eq, hcl.closure_eq]
  ext v
  rw [mem_subdifferential_iff_of_convex (convex_epigraph_of_sublinear (sublinear_supportFunction D)) hp hval]
  constructor
  · intro h
    have hz := h 0
    have ht := h ((2:ℝ) • w)
    rw [supportFunction_zero hn] at hz
    have hdbl : (2:ℝ) • w - w = w := by module
    rw [hdbl, (sublinear_supportFunction D).1.2 (show (0:ℝ) < 2 by norm_num), hval, ← EReal.coe_mul] at ht
    have heq : ⟪v,w⟫_ℝ = c := by
      have h₂ := EReal.coe_le_coe_iff.1 ht
      have h₀ := EReal.coe_le_coe_iff.1 (show ((c+⟪v,0-w⟫_ℝ : ℝ) : EReal) ≤ ((0:ℝ):EReal) from hz)
      rw [zero_sub,inner_neg_right] at h₀
      linarith
    refine ⟨hD ▸ (show v ∈ linearMinorantSet (supportFunction D) from fun y ↦ ?_), by rw [heq,hval]⟩
    simpa [inner_sub_right, heq] using h y
  · rintro ⟨hv,hvw⟩ y
    have heq := EReal.coe_injective (hvw.trans hval)
    simpa [inner_sub_right,heq] using inner_le_supportFunction hv y

/-- The second description in 8.25 writes the exposed face in terms of
the normal cone to the representing set. -/
theorem subdifferential_supportFunction_eq_normal_face {D : Set E} (hc : Convex ℝ D) (hcl : IsClosed D)
    (hn : D.Nonempty) {w : E} (hw : w ∈ effectiveDomain (supportFunction D)) :
    subdifferential (supportFunction D) w = {v ∈ D | w ∈ normalCone D v} := by
  rw [subdifferential_supportFunction hc hcl hn hw]
  ext v
  refine and_congr_right fun hv ↦ ?_
  rw [normalCone_eq_of_convex hc hv]
  constructor
  · intro h u hu
    have hle := EReal.coe_le_coe_iff.1 ((inner_le_supportFunction hu w).trans_eq h.symm)
    simpa [inner_sub_right, real_inner_comm w, sub_nonpos] using hle
  · intro h
    apply le_antisymm (inner_le_supportFunction hv w)
    apply (supportFunction_le_iff _ _ _).2
    intro u hu
    exact EReal.coe_le_coe_iff.2 (by simpa [inner_sub_right, real_inner_comm w, sub_nonpos] using h u hu)

/-- **Corollary 8.25**, starting from a sublinear function. Its subgradients
are the maximizers of the inner product on its representing set, equivalently
the points of that set with the specified normal direction. -/
theorem subdifferential_sublinear_eq_maximizers {h : E → EReal} (hs : Sublinear h)
    (hl : LowerSemicontinuous h) (hp : IsProper h) {w : E} (hw : w ∈ effectiveDomain h) :
    subdifferential h w = {v ∈ linearMinorantSet h | IsMaxOn (fun u ↦ ⟪u,w⟫_ℝ) (linearMinorantSet h) v} ∧
      subdifferential h w = {v ∈ linearMinorantSet h | w ∈ normalCone (linearMinorantSet h) v} := by
  let D := linearMinorantSet h
  have he : supportFunction D = h := supportFunction_linearMinorantSet hs hl hp
  have hn : D.Nonempty := by
    by_contra! hn
    have hv := congrFun he 0
    rw [hn,supportFunction_empty] at hv
    exact (hp.2 0).ne hv
  have hw' : w ∈ effectiveDomain (supportFunction D) := he.symm ▸ hw
  have heq := subdifferential_supportFunction_eq_normal_face (convex_linearMinorantSet h)
    (isClosed_linearMinorantSet h) hn hw'
  rw [he] at heq
  refine ⟨heq.trans ?_,heq⟩
  ext v
  refine and_congr_right fun hv ↦ ?_
  rw [normalCone_eq_of_convex (convex_linearMinorantSet h) hv]
  constructor
  · intro hnorm
    exact isMaxOn_iff.mpr fun u hu ↦ by
      simpa only [inner_sub_right,real_inner_comm w,sub_nonpos] using hnorm u hu
  · intro hmax u hu
    simpa only [inner_sub_right,real_inner_comm w,sub_nonpos] using isMaxOn_iff.mp hmax u hu

/-- A finite convex function has trivial horizon subgradients, by 8.12. -/
theorem horizonSubdifferential_eq_zero_of_convex_finite {f : E → EReal} (hf : Convex ℝ (epigraph f))
    (hfin : ∀ x, ∃ c : ℝ, f x = c) (x : E) : horizonSubdifferential f x = {0} := by
  obtain ⟨c,hc⟩ := hfin x
  have hp : IsProper f := ⟨⟨x, hc.trans_lt (EReal.coe_lt_top _)⟩, fun y ↦ by
    obtain ⟨r,hr⟩ := hfin y; rw [hr]; exact EReal.bot_lt_coe _⟩
  have hd : effectiveDomain f = univ := eq_univ_of_forall fun y ↦ by
    obtain ⟨r,hr⟩ := hfin y; exact hr.trans_lt (EReal.coe_lt_top _)
  refine Subset.antisymm ?_ (singleton_subset_iff.2 ?_)
  · intro v hv
    have h := horizonSubdifferential_subset_normalCone_domain hf hp hc hv
    rw [hd, normalCone_eq_of_convex convex_univ (mem_univ x)] at h
    have h₀ := h (v+x) (mem_univ _)
    simp only [add_sub_cancel_right, real_inner_self_eq_norm_sq, sq_nonpos_iff, norm_eq_zero] at h₀
    exact h₀
  · rw [horizonSubdifferential_of_finite hc]
    exact (isCone_horizonOuterSetLimitAlong _ _).1

end RW
