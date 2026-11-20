/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Global corrected gauge conjugacy
-/
import RockafellarWets.Chapter11.GaugeComposition

open Set Bornology
open scoped InnerProductSpace Pointwise
namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem fenchelConjugate_even {f : E → EReal} (he : ∀x, f (-x)=f x) (v : E) :
    fenchelConjugate f (-v) = fenchelConjugate f v := by
  have hbound (w : E) : fenchelConjugate f (-w) ≤ fenchelConjugate f w := by
    apply iSup_le
    intro x
    have h := le_fenchelConjugate f (-x) w
    simpa only [he,inner_neg_left,inner_neg_right] using h
  exact le_antisymm (hbound v) (by simpa using hbound (-v))

/-- At an infinite polar gauge, one finite positive outer argument forces the
conjugate to be infinite as well. -/
theorem fenchelConjugate_extendedRescaling_gauge_eq_top {C : Set E}
    (hc : Convex ℝ C) (hclosed : IsClosed C) (h0 : (0:E) ∈ C)
    {θ : ℝ → EReal} (hp : IsProper θ) (hθ : Convex ℝ (epigraph θ))
    (he : ∀r, θ (-r)=θ r) (hpos : ∃r:ℝ, 0<r ∧ θ r<⊤)
    {v : E} (hv : gaugeFunction (polarSet C) v = ⊤) :
    fenchelConjugate (extendedRescaling θ (gaugeFunction C)) v = ⊤ := by
  by_contra hfin
  obtain ⟨a,ha,_⟩ := EReal.exists_between_coe_real (lt_top_iff_ne_top.mpr hfin)
  have hbound := (fenchelConjugate_le_coe_iff _ _ a).mp ha.le
  obtain ⟨r,hr,hrfin⟩ := hpos
  have hval : θ r = ((θ r).toReal:EReal) := (EReal.coe_toReal hrfin.ne (hp.2 r).ne').symm
  have hsup : supportFunction (r • C) v ≤ (((θ r).toReal+a:ℝ):EReal) := by
    apply (supportFunction_le_iff _ _ _).mpr
    intro x hx
    have hb := (hbound x).trans (extendedRescaling_gauge_le_of_mem_smul hc hclosed h0
      (monotoneOn_nonnegative_of_even_convex hp hθ he) hr hx)
    have hb' : ⟪v,x⟫_ℝ-a ≤ (θ r).toReal := EReal.coe_le_coe_iff.mp (hb.trans_eq hval)
    apply EReal.coe_le_coe_iff.mpr
    rw [real_inner_comm]
    linarith
  have hs : supportFunction C v = ⊤ := by
    rwa [gaugeFunction_polarSet_eq_supportFunction hc hclosed h0] at hv
  rw [supportFunction_smul C hr v,hs,EReal.coe_mul_top_of_pos hr] at hsup
  exact (EReal.coe_lt_top _).not_ge hsup

/-- Corrected unrestricted formula for 11.21: the outer domain must contain a
positive number. The counterexample shows that this cannot simply be omitted. -/
theorem fenchelConjugate_extendedRescaling_gauge {C : Set E}
    (hc : Convex ℝ C) (hclosed : IsClosed C) (h0 : (0:E) ∈ C)
    {θ : ℝ → EReal} (hp : IsProper θ) (hθ : Convex ℝ (epigraph θ))
    (he : ∀r, θ (-r)=θ r) (hpos : ∃r:ℝ, 0<r ∧ θ r<⊤) :
    fenchelConjugate (extendedRescaling θ (gaugeFunction C)) =
      extendedRescaling (fenchelConjugate θ) (gaugeFunction (polarSet C)) := by
  funext v
  by_cases hv : gaugeFunction (polarSet C) v=⊤
  · rw [fenchelConjugate_extendedRescaling_gauge_eq_top hc hclosed h0 hp hθ he hpos hv]
    simp [extendedRescaling,hv]
  · have hv' : gaugeFunction (polarSet C) v = ((gaugeFunction (polarSet C) v).toReal:EReal) :=
      (EReal.coe_toReal hv (gaugeFunction_ne_bot _ _)).symm
    rw [extendedRescaling_of_finite hv']
    exact fenchelConjugate_extendedRescaling_gauge_of_finite hc hclosed h0 hp hθ he hv'

/-- Full two-way conjugacy for gauge norms (indeed, symmetry of the unit set
is unnecessary). Both gauges are finite for bounded sets with zero in their interior. -/
theorem polar_gauge_conjugate_pair_of_bounded {C : Set E} (hc : Convex ℝ C)
    (hclosed : IsClosed C) (hb : IsBounded C) (h0 : (0:E) ∈ interior C)
    {θ : ℝ → EReal} (hp : IsProper θ) (hl : LowerSemicontinuous θ)
    (hθ : Convex ℝ (epigraph θ)) (he : ∀r, θ (-r)=θ r) :
    fenchelConjugate (extendedRescaling θ (gaugeFunction C)) =
        extendedRescaling (fenchelConjugate θ) (gaugeFunction (polarSet C)) ∧
      fenchelConjugate (extendedRescaling (fenchelConjugate θ) (gaugeFunction (polarSet C))) =
        extendedRescaling θ (gaugeFunction C) := by
  have hmem : (0:E) ∈ C := interior_subset h0
  refine ⟨fenchelConjugate_extendedRescaling_gauge_of_bounded hc hclosed hmem hb hp hθ he, ?_⟩
  have h := fenchelConjugate_extendedRescaling_gauge_of_bounded (convex_polarSet C)
    (isClosed_polarSet C) (zero_mem_polarSet C)
    ((isBounded_polarSet_iff_zero_mem_interior hc hclosed hmem).mpr h0)
    (isProper_fenchelConjugate hp hl hθ) (convex_epigraph_fenchelConjugate θ)
    (fenchelConjugate_even he)
  rwa [polarSet_bipolar_eq_self hc hclosed hmem, fenchelConjugate_fenchelConjugate_eq hp hl hθ] at h

end RW
