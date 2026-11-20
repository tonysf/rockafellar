/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Support of intersections and inverse images
-/
import RockafellarWets.Chapter11.SupportOperations
import RockafellarWets.Chapter11.DualOperationQualifications

open Set
open scoped InnerProductSpace Pointwise
namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Corollary 11.24(e), with closure of the epi-sum. -/
theorem supportFunction_inter_eq_epiClosure {C D : Set E} (hc : Convex ℝ C)
    (hd : Convex ℝ D) (hcl : IsClosed C) (hdl : IsClosed D) (hne : (C∩D).Nonempty) :
    supportFunction (C∩D) = epiClosure (epiSum (supportFunction C) (supportFunction D)) := by
  have hpc := (indicatorVA_isProper_iff C).mpr (hne.mono inter_subset_left)
  have hpd := (indicatorVA_isProper_iff D).mpr (hne.mono inter_subset_right)
  have hepic : Convex ℝ (epigraph (indicatorVA C)) := by
    rw [epigraph_indicatorVA]; exact hc.prod (convex_Ici 0)
  have hepid : Convex ℝ (epigraph (indicatorVA D)) := by
    rw [epigraph_indicatorVA]; exact hd.prod (convex_Ici 0)
  have h := fenchelConjugate_add_eq_epiClosure hpc hpd
    (lowerSemicontinuous_indicatorVA hcl) (lowerSemicontinuous_indicatorVA hdl) hepic hepid
    (by simpa only [effectiveDomain_indicatorVA] using hne)
  simpa only [← indicatorVA_inter,fenchelConjugate_indicatorVA] using h

/-- Corollary 11.24(d), with closure of the adjoint fiber infimum. -/
theorem supportFunction_linear_preimage_eq_epiClosure (A : E →L[ℝ] F) {D : Set F}
    (hd : Convex ℝ D) (hdl : IsClosed D) (hne : (A ⁻¹' D).Nonempty) :
    supportFunction (A ⁻¹' D) = epiClosure (fiberInfimum A.adjoint (supportFunction D)) := by
  obtain ⟨x,hx⟩ := hne
  change A x ∈ D at hx
  have hpd := (indicatorVA_isProper_iff D).mpr ⟨A x,hx⟩
  have hepid : Convex ℝ (epigraph (indicatorVA D)) := by
    rw [epigraph_indicatorVA]; exact hd.prod (convex_Ici 0)
  have h := fenchelConjugate_comp_eq_epiClosure A hpd (lowerSemicontinuous_indicatorVA hdl) hepid
    ⟨x,by simp [indicatorVA_apply_mem hx]⟩
  have hfun : (fun y ↦ indicatorVA D (A y)) = indicatorVA (A ⁻¹' D) := by
    rfl
  simpa only [hfun,fenchelConjugate_indicatorVA] using h

/-- The interior-difference qualification removes closure in 11.24(e). -/
theorem supportFunction_inter_of_zero_mem_interior {C D : Set E} (hc : Convex ℝ C)
    (hd : Convex ℝ D) (hcl : IsClosed C) (hdl : IsClosed D)
    (hq : (0:E) ∈ interior (C-D)) :
    supportFunction (C∩D) = epiSum (supportFunction C) (supportFunction D) := by
  obtain ⟨x,hx,y,hy,_⟩ := interior_subset hq
  have hpc := (indicatorVA_isProper_iff C).mpr ⟨x,hx⟩
  have hpd := (indicatorVA_isProper_iff D).mpr ⟨y,hy⟩
  have hepic : Convex ℝ (epigraph (indicatorVA C)) := by
    rw [epigraph_indicatorVA]; exact hc.prod (convex_Ici 0)
  have hepid : Convex ℝ (epigraph (indicatorVA D)) := by
    rw [epigraph_indicatorVA]; exact hd.prod (convex_Ici 0)
  have h := fenchelConjugate_add_of_interior hpc hpd
    (lowerSemicontinuous_indicatorVA hcl) (lowerSemicontinuous_indicatorVA hdl) hepic hepid
    (by simpa only [effectiveDomain_indicatorVA] using hq)
  simpa only [← indicatorVA_inter,fenchelConjugate_indicatorVA] using h

/-- Meeting either interior suffices for the exact support intersection rule. -/
theorem supportFunction_inter_of_meets_interior {C D : Set E} (hc : Convex ℝ C)
    (hd : Convex ℝ D) (hcl : IsClosed C) (hdl : IsClosed D)
    (hq : (C ∩ interior D).Nonempty ∨ (interior C ∩ D).Nonempty) :
    supportFunction (C∩D) = epiSum (supportFunction C) (supportFunction D) :=
  supportFunction_inter_of_zero_mem_interior hc hd hcl hdl (zero_mem_interior_sub_of_meets_interior hq)

/-- The interior-difference qualification removes closure in 11.24(d). -/
theorem supportFunction_linear_preimage_of_zero_mem_interior (A : E →L[ℝ] F) {D : Set F}
    (hd : Convex ℝ D) (hdl : IsClosed D) (hq : (0:F) ∈ interior (D-(A.range:Set F))) :
    supportFunction (A ⁻¹' D) = fiberInfimum A.adjoint (supportFunction D) := by
  obtain ⟨z,hz,y,hy,_⟩ := interior_subset hq
  have hpd := (indicatorVA_isProper_iff D).mpr ⟨z,hz⟩
  have hepid : Convex ℝ (epigraph (indicatorVA D)) := by
    rw [epigraph_indicatorVA]; exact hd.prod (convex_Ici 0)
  have h := fenchelConjugate_comp_of_interior A hpd (lowerSemicontinuous_indicatorVA hdl) hepid
    (by simpa only [effectiveDomain_indicatorVA] using hq)
  have hfun : (fun y ↦ indicatorVA D (A y)) = indicatorVA (A ⁻¹' D) := rfl
  simpa only [hfun,fenchelConjugate_indicatorVA] using h

/-- A range meeting the target interior suffices for the exact preimage rule. -/
theorem supportFunction_linear_preimage_of_meets_interior (A : E →L[ℝ] F) {D : Set F}
    (hd : Convex ℝ D) (hdl : IsClosed D) (hq : ((A.range:Set F) ∩ interior D).Nonempty) :
    supportFunction (A ⁻¹' D) = fiberInfimum A.adjoint (supportFunction D) := by
  apply supportFunction_linear_preimage_of_zero_mem_interior A hd hdl
  apply zero_mem_interior_sub_of_meets_interior
  right
  obtain ⟨x,hx,hdx⟩ := hq
  exact ⟨x,hdx,hx⟩

end RW
