/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Interior qualifications for dual operations
-/

import RockafellarWets.Chapter11.DualOperationClosures
import RockafellarWets.Chapter11.HorizonConjugacy
import RockafellarWets.Chapter3.EpiAdditionBookCompletion
import RockafellarWets.Chapter8.SupportInterior

open Set
open scoped Pointwise InnerProductSpace

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The interior-difference qualification is satisfied when either set
meets the other's interior. -/
theorem zero_mem_interior_sub_of_meets_interior {C D : Set E}
    (h : (C ∩ interior D).Nonempty ∨ (interior C ∩ D).Nonempty) : (0 : E) ∈ interior (C-D) := by
  rcases h with ⟨x,hC,hD⟩ | ⟨x,hC,hD⟩
  · exact subset_interior_sub_right ⟨x,hC,x,hD,sub_self x⟩
  · exact subset_interior_sub_left ⟨x,hC,x,hD,sub_self x⟩

private theorem ereal_pos_add_of_neg_lt {a b : EReal} (ha : a ≠ ⊥) (hb : b ≠ ⊥) (h : -b < a) :
    0 < a + b := by
  cases a <;> cases b <;> simp_all [← EReal.coe_add,← EReal.coe_neg] <;> linarith

/-- **Theorem 11.23(a)**. An interior overlap eliminates the closure in
the dual sum formula. -/
theorem fenchelConjugate_add_of_interior {f g : E → EReal}
    (hp : IsProper f) (hq : IsProper g) (hl : LowerSemicontinuous f) (hk : LowerSemicontinuous g)
    (hc : Convex ℝ (epigraph f)) (hd : Convex ℝ (epigraph g))
    (h : (0 : E) ∈ interior (effectiveDomain f - effectiveDomain g)) :
    fenchelConjugate (fun x ↦ f x + g x) = epiSum (fenchelConjugate f) (fenchelConjugate g) := by
  obtain ⟨x,hx,y,hy,hxy⟩ := interior_subset h
  have hm : (effectiveDomain f ∩ effectiveDomain g).Nonempty := ⟨x,hx,sub_eq_zero.mp hxy ▸ hy⟩
  rw [fenchelConjugate_add_eq_epiClosure hp hq hl hk hc hd hm]
  apply epiClosure_eq_of_lowerSemicontinuous
  apply lowerSemicontinuous_epiSum_of_pos_book (lowerSemicontinuous_fenchelConjugate _)
    (lowerSemicontinuous_fenchelConjugate _) (isProper_fenchelConjugate hp hl hc) (isProper_fenchelConjugate hq hk hd)
  intro w hw
  rw [(horizon_conjugate_support_identities hp hl hc).2,(horizon_conjugate_support_identities hq hk hd).2]
  have hs := (zero_mem_interior_sub_iff_supportFunction (convex_effectiveDomain_of_convex_epigraph hc)
    (convex_effectiveDomain_of_convex_epigraph hd) hp.1 hq.1).mp h (-w) (neg_ne_zero.mpr hw)
  simp only [neg_neg,not_le] at hs
  exact ereal_pos_add_of_neg_lt ((isProper_supportFunction hp.1).2 _).ne' ((isProper_supportFunction hq.1).2 _).ne' hs

/-- A horizon condition on the kernel gives exact epigraph projection and
lower semicontinuity of the infimum on the fibers. -/
theorem isClosed_epigraph_fiberInfimum_of_horizon_ker (A : F →L[ℝ] E) {g : F → EReal}
    (hl : LowerSemicontinuous g) (hp : IsProper g)
    (hk : ∀ w, A w = 0 → horizonFunction g w ≤ 0 → w = 0) :
    IsClosed (epigraph (fiberInfimum A g)) := by
  let L := A.toLinearMap.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ)
  have hclosed : IsClosed (L '' epigraph g) := by
    apply isClosed_linearImage_of_horizonCone_ker_trivial (isClosed_epigraph_of_lsc_ereal g hl)
    rintro ⟨w,b⟩ hw hL
    have hpair : (A w,b) = (0,0) := hL
    obtain rfl : b = 0 := congrArg Prod.snd hpair
    rw [← epigraph_horizonFunction_eq_horizonCone_epigraph_of_isProper hp] at hw
    exact Prod.ext (hk w (congrArg Prod.fst hpair) (by simpa only [mem_epigraph_iff,EReal.coe_zero] using hw)) rfl
  have himage : L '' epigraph g ⊆ epigraph (fiberInfimum A g) := by
    rintro _ ⟨⟨x,b⟩,hx,rfl⟩
    exact (iInf_le (fun z : {z // A z = A x} ↦ g z) ⟨x,rfl⟩).trans hx
  apply isClosed_of_closure_subset
  rw [closure_epigraph_fiberInfimum,hclosed.closure_eq]
  exact himage

/-- **Theorem 11.23(b)**. If the domain minus the range contains a
neighborhood of zero, precomposition dualizes without closure. -/
theorem fenchelConjugate_comp_of_interior {g : F → EReal} (A : E →L[ℝ] F) (hp : IsProper g)
    (hl : LowerSemicontinuous g) (hc : Convex ℝ (epigraph g))
    (h : (0 : F) ∈ interior (effectiveDomain g - (A.range : Set F))) :
    fenchelConjugate (fun x ↦ g (A x)) = fiberInfimum A.adjoint (fenchelConjugate g) := by
  obtain ⟨z,hz,_,⟨x,rfl⟩,hez⟩ := interior_subset h
  have hm : ∃ x, g (A x) < ⊤ := ⟨x,sub_eq_zero.mp hez ▸ hz⟩
  rw [fenchelConjugate_comp_eq_epiClosure A hp hl hc hm]
  apply epiClosure_eq_of_lowerSemicontinuous
  apply lowerSemicontinuous_of_isClosed_epigraph_ereal
  apply isClosed_epigraph_fiberInfimum_of_horizon_ker A.adjoint (lowerSemicontinuous_fenchelConjugate g)
    (isProper_fenchelConjugate hp hl hc)
  intro w hw hh
  by_contra hne
  have hpos := (mem_interior_iff_inner_lt_supportFunction
    ((convex_effectiveDomain_of_convex_epigraph hc).sub A.range.convex) ⟨0,interior_subset h⟩ 0).mp h w hne
  rw [inner_zero_left,EReal.coe_zero] at hpos
  apply (not_le_of_gt hpos)
  rw [(horizon_conjugate_support_identities hp hl hc).2] at hh
  apply (supportFunction_le_iff _ _ _).mpr
  rintro _ ⟨z,hz,_,⟨x,rfl⟩,rfl⟩
  have he : ⟪A x,w⟫_ℝ = 0 := by rw [← A.adjoint_inner_right,hw,inner_zero_right]
  change (⟪z-A x,w⟫_ℝ : EReal) ≤ 0
  simpa only [inner_sub_left,he,sub_zero] using ((supportFunction_le_iff _ _ _).mp hh z hz)

end RW
