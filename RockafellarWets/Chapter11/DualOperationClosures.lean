/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Closure in dual operations
-/

import RockafellarWets.Chapter11.DualOperations
import RockafellarWets.Chapter11.ConjugateInvariance
import RockafellarWets.Chapter7.TotalEpiProjection

open Set
open scoped InnerProductSpace

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Properness of the conjugate forces properness of the primal function. -/
theorem isProper_of_isProper_fenchelConjugate {f : E → EReal} (hp : IsProper (fenchelConjugate f)) :
    IsProper f := by
  obtain ⟨v,hv⟩ := hp.1
  constructor
  · by_contra! h
    have hall (x : E) : f x = ⊤ := top_le_iff.mp (h x)
    have hbad := hp.2 0
    simp [fenchelConjugate,hall] at hbad
  · intro x
    by_contra! h
    have hh := (le_fenchelConjugate f x v).trans_lt hv
    rw [le_bot_iff.mp h,EReal.coe_sub_bot] at hh
    exact lt_irrefl _ hh

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- A convex closure of the epigraph agrees with the biconjugate epigraph
as soon as the conjugate is proper. -/
theorem biconjugate_eq_epiClosure_of_convex_closure {f : E → EReal} (hp : IsProper (fenchelConjugate f))
    (hc : Convex ℝ (closure (epigraph f))) :
    fenchelConjugate (fenchelConjugate f) = epiClosure f := by
  rw [← fenchelConjugate_epiClosure f]
  apply fenchelConjugate_fenchelConjugate_eq
  · apply isProper_of_isProper_fenchelConjugate
    rwa [fenchelConjugate_epiClosure]
  · exact lowerSemicontinuous_epiLowerLimit _
  · rwa [epigraph_epiClosure]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The epigraph of a fiber infimum and the linear image of the epigraph
have the same closure, whether or not finite infima are attained. -/
theorem closure_epigraph_fiberInfimum (A : E →L[ℝ] F) (f : E → EReal) :
    closure (epigraph (fiberInfimum A f)) =
      closure (A.toLinearMap.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ) '' epigraph f) := by
  apply le_antisymm
  · apply closure_minimal _ isClosed_closure
    rintro ⟨u,b⟩ hu
    have h : Ioi b ⊆ (Prod.mk u) ⁻¹' closure (A.toLinearMap.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ) '' epigraph f) := by
      intro c hc
      have hc' := hu.trans_lt (EReal.coe_lt_coe_iff.mpr hc)
      obtain ⟨x,hx⟩ := iInf_lt_iff.mp (show (⨅ x : {x // A x = u},f x) < (c : EReal) from hc')
      exact subset_closure ⟨(x,c),hx.le,Prod.ext x.property rfl⟩
    exact closure_minimal h (isClosed_closure.preimage (continuous_const.prodMk continuous_id)) (by simp [closure_Ioi])
  · apply closure_mono
    rintro _ ⟨⟨x,b⟩,hx,rfl⟩
    exact (iInf_le (fun z : {z // A z = A x} ↦ f z) ⟨x,rfl⟩).trans hx

/-- **Theorem 11.23(a)**, conjugating a sum when the domains meet. -/
theorem fenchelConjugate_add_eq_epiClosure {f g : E → EReal}
    (hp : IsProper f) (hq : IsProper g) (hl : LowerSemicontinuous f) (hk : LowerSemicontinuous g)
    (hc : Convex ℝ (epigraph f)) (hd : Convex ℝ (epigraph g))
    (hm : (effectiveDomain f ∩ effectiveDomain g).Nonempty) :
    fenchelConjugate (fun x ↦ f x + g x) = epiClosure (epiSum (fenchelConjugate f) (fenchelConjugate g)) := by
  obtain ⟨hpf,_,hcf,hff⟩ := fenchelConjugate_properties hp hl hc
  obtain ⟨hpg,_,hcg,hgg⟩ := fenchelConjugate_properties hq hk hd
  have he := fenchelConjugate_epiSum hpf hpg
  rw [hff,hgg] at he
  rw [← he]
  apply biconjugate_eq_epiClosure_of_convex_closure
  · rw [he]
    obtain ⟨x,hxf,hxg⟩ := hm
    exact ⟨⟨x,EReal.add_lt_top hxf.ne hxg.ne⟩,fun y ↦ EReal.bot_lt_add_iff.mpr ⟨hp.2 y,hq.2 y⟩⟩
  · rw [epiSum,closure_epigraph_valueFunction]
    apply Convex.closure
    apply Convex.linear_image
    change Convex ℝ (epigraph (fun p : E × E ↦ fenchelConjugate f (p.2-p.1) + fenchelConjugate g p.1))
    rw [← image_epiSumLinearMap_eq_epigraph hpf.2 hpg.2]
    exact (hcf.prod hcg).linear_image _

/-- **Theorem 11.23(b)**, conjugating precomposition with a linear map. -/
theorem fenchelConjugate_comp_eq_epiClosure {g : F → EReal} (A : E →L[ℝ] F) (hp : IsProper g)
    (hl : LowerSemicontinuous g) (hc : Convex ℝ (epigraph g)) (hm : ∃ x, g (A x) < ⊤) :
    fenchelConjugate (fun x ↦ g (A x)) = epiClosure (fiberInfimum A.adjoint (fenchelConjugate g)) := by
  have he := fenchelConjugate_fiberInfimum A.adjoint (fenchelConjugate g)
  rw [ContinuousLinearMap.adjoint_adjoint,fenchelConjugate_fenchelConjugate_eq hp hl hc] at he
  rw [← he]
  apply biconjugate_eq_epiClosure_of_convex_closure
  · rw [he]
    exact ⟨hm,fun x ↦ hp.2 _⟩
  · rw [closure_epigraph_fiberInfimum]
    exact ((convex_epigraph_fenchelConjugate g).linear_image _).closure

/-- **Theorem 11.23(d)**, conjugating a proper pointwise supremum. -/
theorem fenchelConjugate_iSup_eq_epiClosure_convexHull {ι : Sort*} (f : ι → E → EReal)
    (hp : ∀ i, IsProper (f i)) (hl : ∀ i, LowerSemicontinuous (f i))
    (hc : ∀ i, Convex ℝ (epigraph (f i))) (hm : IsProper (fun x ↦ ⨆ i, f i x)) :
    fenchelConjugate (fun x ↦ ⨆ i, f i x) =
      epiClosure (convexHullFunction (fun x ↦ ⨅ i, fenchelConjugate (f i) x)) := by
  have he := fenchelConjugate_iInf (fun i ↦ fenchelConjugate (f i))
  simp only [fenchelConjugate_fenchelConjugate_eq (hp _) (hl _) (hc _)] at he
  rw [← he]
  apply fenchelConjugate_fenchelConjugate_eq_epiClosure_convexHullFunction
  apply isProper_of_isProper_fenchelConjugate
  rwa [fenchelConjugate_convexHullFunction,he]

end RW
