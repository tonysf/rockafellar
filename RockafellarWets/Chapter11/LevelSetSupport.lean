/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Support functions of convex level sets
-/
import RockafellarWets.Chapter11.PositiveHullConjugacy

open Set
open scoped InnerProductSpace
namespace RW
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Exercise 11.6**, support functions of level sets.  The real-valued
presentation expresses precisely the printed finiteness assumption. -/
theorem supportFunction_zeroSublevel_eq_iInf_conjugate_perspective
    {f : E → ℝ} (hc : ConvexOn ℝ univ f) (hneg : ∃ x, f x < 0) {v : E} (hv : v ≠ 0) :
    supportFunction {x | f x ≤ 0} v =
      ⨅ t : {t : ℝ // 0 < t}, (t:ℝ) * fenchelConjugate (fun x ↦ (f x:EReal)) ((t:ℝ)⁻¹ • v) := by
  letI := FiniteDimensional.complete ℝ E
  let F : E → EReal := fun x ↦ (f x:EReal)
  have hp : IsProper F := ⟨⟨0,EReal.coe_lt_top _⟩,fun x ↦ EReal.bot_lt_coe _⟩
  have hF : Convex ℝ (epigraph F) := by
    have h := (convex_epigraph_iff_convexOn f univ convex_univ).2 hc
    simpa only [F,epigraph,mem_setOf_eq,mem_univ,true_and,EReal.coe_le_coe_iff] using h
  have hcont : Continuous f := continuousOn_univ.mp
    (continuous_of_convexOn_open isOpen_univ convex_univ hc)
  have hl : LowerSemicontinuous F := (continuous_coe_real_ereal.comp hcont).lowerSemicontinuous
  have hpc := isProper_fenchelConjugate hp hl hF
  have hminor : linearMinorantSet (fenchelConjugate F) = {x | f x ≤ 0} := by
    ext x
    have h := (fenchelConjugate_le_coe_iff (fenchelConjugate F) x 0)
    rw [fenchelConjugate_fenchelConjugate_eq hp hl hF] at h
    simpa [linearMinorantSet,F] using h.symm
  obtain ⟨x₀,hx₀⟩ := hneg
  have hm : (linearMinorantSet (fenchelConjugate F)).Nonempty := by
    rw [hminor]
    exact ⟨x₀,hx₀.le⟩
  have h0 : (0:EReal) < fenchelConjugate F 0 := by
    have h := le_fenchelConjugate F x₀ 0
    have he : (⟪(0:E),x₀⟫_ℝ:EReal)-F x₀ = ((-f x₀:ℝ):EReal) := by simp [F]
    rw [he] at h
    exact (EReal.coe_lt_coe_iff.mpr (neg_pos.mpr hx₀)).trans_le h
  have hhor : horizonFunction (fenchelConjugate F) = indicatorVA {0} := by
    rw [horizon_fenchelConjugate_eq_support_domain_of_proper hp hpc]
    have hd : effectiveDomain F = univ := by ext x; simp [effectiveDomain,F]
    rw [hd,supportFunction_univ]
  have hph := positivelyHomogeneous_positiveHullFunction (fenchelConjugate F)
  have hminpos : x₀ ∈ linearMinorantSet (positiveHullFunction (fenchelConjugate F)) := by
    rw [linearMinorantSet_positiveHullFunction,hminor]
    exact hx₀.le
  have hproper : IsProper (positiveHullFunction (fenchelConjugate F)) :=
    ⟨⟨0,hph.1⟩,fun x ↦ (EReal.bot_lt_coe _).trans_le (hminpos x)⟩
  have hsub := sublinear_positiveHullFunction_of_convex_of_ne_bot
    (convex_epigraph_fenchelConjugate F) (fun x ↦ (hproper.2 x).ne')
  have hlph := lowerSemicontinuous_positiveHullFunction_of_vertical_horizon hpc
    (lowerSemicontinuous_fenchelConjugate F) h0 hhor hm
  have he := supportFunction_linearMinorantSet hsub hlph hproper
  rw [linearMinorantSet_positiveHullFunction,hminor] at he
  rw [he,positiveHullFunction_eq_iInf_perspective hv]

/-- The same theorem with the book's strict infimum hypothesis. -/
theorem supportFunction_zeroSublevel_eq_iInf_conjugate_perspective_of_iInf_lt
    {f : E → ℝ} (hc : ConvexOn ℝ univ f)
    (hneg : (⨅ x, (f x:EReal)) < 0) {v : E} (hv : v ≠ 0) :
    supportFunction {x | f x ≤ 0} v =
      ⨅ t : {t : ℝ // 0 < t}, (t:ℝ) * fenchelConjugate (fun x ↦ (f x:EReal)) ((t:ℝ)⁻¹ • v) := by
  apply supportFunction_zeroSublevel_eq_iInf_conjugate_perspective hc _ hv
  obtain ⟨x,hx⟩ := iInf_lt_iff.mp hneg
  exact ⟨x,by exact_mod_cast hx⟩

end
end RW
