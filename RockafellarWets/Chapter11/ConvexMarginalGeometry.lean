/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Convex marginals and conjugacy in domain interiors
-/
import RockafellarWets.Chapter11.ImproperConjugates
import RockafellarWets.Chapter11.DualOperationClosures
import RockafellarWets.Chapter8.ConvexSubderivativeInteriors

open Set Filter Topology
open scoped InnerProductSpace
namespace RW
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Convexity of a marginal requires neither attainment nor level boundedness. -/
theorem convex_epigraph_fiberInfimum (A : E →L[ℝ] F) {f : E → EReal}
    (hc : Convex ℝ (epigraph f)) : Convex ℝ (epigraph (fiberInfimum A f)) := by
  rintro ⟨x,a⟩ hx ⟨y,b⟩ hy t s ht hs hts
  let r := t*a+s*b
  change fiberInfimum A f (t • x+s • y) ≤ (r:EReal)
  have hlim : Tendsto (fun n : ℕ ↦ ((r+((n:ℝ)+1)⁻¹:ℝ):EReal)) atTop (𝓝 (r:EReal)) := by
    apply continuous_coe_real_ereal.continuousAt.tendsto.comp
    simpa only [one_div,add_zero] using (tendsto_const_nhds (x := r)).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply ge_of_tendsto hlim
  apply Eventually.of_forall
  intro n
  let ε := ((n:ℝ)+1)⁻¹
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨u,hu⟩ := iInf_lt_iff.mp
    (hx.trans_lt (EReal.coe_lt_coe_iff.mpr (lt_add_of_pos_right a hε)))
  obtain ⟨v,hv⟩ := iInf_lt_iff.mp
    (hy.trans_lt (EReal.coe_lt_coe_iff.mpr (lt_add_of_pos_right b hε)))
  have hh := hc (show (u.val,a+ε) ∈ epigraph f from hu.le)
    (show (v.val,b+ε) ∈ epigraph f from hv.le) ht hs hts
  have he : t*(a+ε)+s*(b+ε) = r+ε := by
    dsimp [r]
    nlinarith [congrArg (fun z : ℝ ↦ z*ε) hts]
  apply (iInf_le (fun z : {z // A z = t • x+s • y} ↦ f z)
    ⟨t • u.val+s • v.val,by simp [u.property,v.property]⟩).trans
  simpa only [Prod.smul_mk,Prod.mk_add_mk,smul_eq_mul,he] using hh

variable [FiniteDimensional ℝ E]

/-- Interior closure invariance for finite-dimensional convex sets, including
sets with empty interior. -/
theorem Convex.interior_closure_eq {S : Set E} (hS : Convex ℝ S) :
    interior (closure S) = interior S := by
  by_cases hSne : (interior S).Nonempty
  · exact hS.interior_closure_eq_interior_of_nonempty_interior hSne
  · have hSempty : interior S = ∅ := not_nonempty_iff_eq_empty.1 hSne
    rw [hSempty]
    apply eq_empty_iff_forall_notMem.2
    intro x hx
    apply hSne
    rw [Convex.interior_nonempty_iff_affineSpan_eq_top hS]
    apply top_unique
    have hclosureSub : closure S ⊆ affineSpan ℝ S :=
      closure_minimal (subset_affineSpan ℝ S) (affineSpan ℝ S).closed_of_finiteDimensional
    have hspanClosure : affineSpan ℝ (closure S) = ⊤ :=
      (Convex.interior_nonempty_iff_affineSpan_eq_top hS.closure).1 ⟨x,hx⟩
    rw [← hspanClosure]
    exact affineSpan_le.2 hclosureSub

/-- Closing a convex epigraph preserves the interior of its effective domain. -/
theorem interior_domain_epiClosure {f : E → EReal} (hc : Convex ℝ (epigraph f)) :
    interior (effectiveDomain (epiClosure f)) = interior (effectiveDomain f) := by
  have hsub : effectiveDomain f ⊆ effectiveDomain (epiClosure f) := by
    have hle := epigraph_subset_epigraph_iff.mp (epigraph_epiClosure f ▸ (subset_closure : epigraph f ⊆ closure (epigraph f)))
    exact fun x hx ↦ (hle x).trans_lt hx
  apply Subset.antisymm _ (interior_mono hsub)
  have hdom : effectiveDomain (epiClosure f) ⊆ closure (effectiveDomain f) := by
    intro x hx
    obtain ⟨a,ha,_⟩ := EReal.exists_between_coe_real hx
    have he : (x,a) ∈ closure (epigraph f) := by
      rw [← epigraph_epiClosure]
      exact ha.le
    have h := mem_closure_image continuous_fst.continuousAt he
    rwa [epigraph_proj_eq_effectiveDomain] at h
  have hi := interior_mono hdom
  rwa [Convex.interior_closure_eq (convex_effectiveDomain_of_convex_epigraph hc)] at hi

/-- Proper convex functions have proper conjugates before lower closure. -/
theorem isProper_fenchelConjugate_of_convex {f : E → EReal}
    (hp : IsProper f) (hc : Convex ℝ (epigraph f)) : IsProper (fenchelConjugate f) := by
  rw [← fenchelConjugate_epiClosure f]
  exact isProper_fenchelConjugate (isProper_of_isLowerClosure hp hc (epigraph_epiClosure f))
    (lowerSemicontinuous_epiLowerLimit _) (by rw [epigraph_epiClosure]; exact hc.closure)

/-- At an interior domain point, every convex function equals its biconjugate,
including improper convex functions. -/
theorem biconjugate_eq_of_mem_interior_domain {f : E → EReal}
    (hc : Convex ℝ (epigraph f)) {x : E} (hx : x ∈ interior (effectiveDomain f)) :
    fenchelConjugate (fenchelConjugate f) x = f x := by
  by_cases hb : ∃ y, f y = ⊥
  · obtain ⟨y,hy⟩ := hb
    rw [fenchelConjugate_eq_top_of_bot hy,fenchelConjugate_top]
    have he := congrFun (epiClosure_of_convex_bot hc hy) x
    rw [epiClosure_eq_of_mem_interior_convex hc hx] at he
    simpa only [if_pos (subset_closure (interior_subset hx))] using he.symm
  · have hp : IsProper f := ⟨⟨x,show f x < ⊤ from interior_subset (s := effectiveDomain f) hx⟩,fun y ↦ lt_of_le_of_ne bot_le
        (fun he ↦ hb ⟨y,he.symm⟩)⟩
    rw [biconjugate_eq_epiClosure_of_convex_closure
      (isProper_fenchelConjugate_of_convex hp hc) hc.closure,
      epiClosure_eq_of_mem_interior_convex hc hx]

end
end RW
