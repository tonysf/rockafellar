/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Conjugacy is unchanged by convexification and lower closure
-/
import RockafellarWets.Chapter11.FenchelMoreau
import RockafellarWets.Chapter11.ConvexHullEpigraphClosure

open Set
open scoped InnerProductSpace
namespace RW
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def fenchelEpigraphHalfspace (v : E) (b : ℝ) : Set (E × ℝ) :=
  {p | ⟪v,p.1⟫_ℝ-p.2 ≤ b}

theorem isClosed_fenchelEpigraphHalfspace (v : E) (b : ℝ) : IsClosed (fenchelEpigraphHalfspace v b) :=
  isClosed_le (by fun_prop) continuous_const

theorem convex_fenchelEpigraphHalfspace (v : E) (b : ℝ) : Convex ℝ (fenchelEpigraphHalfspace v b) := by
  let L : E × ℝ →L[ℝ] ℝ := (innerSL ℝ v).comp (ContinuousLinearMap.fst ℝ E ℝ)-ContinuousLinearMap.snd ℝ E ℝ
  exact (convex_Iic b).linear_preimage L.toLinearMap

theorem fenchelConjugate_le_coe_iff_epigraph (f : E → EReal) (v : E) (b : ℝ) :
    fenchelConjugate f v ≤ (b:EReal) ↔ epigraph f ⊆ fenchelEpigraphHalfspace v b := by
  have he : epigraph (fun x : E ↦ ((⟪v,x⟫_ℝ-b:ℝ):EReal)) = fenchelEpigraphHalfspace v b := by
    ext p
    change ((⟪v,p.1⟫_ℝ-b:ℝ):EReal) ≤ (p.2:EReal) ↔ ⟪v,p.1⟫_ℝ-p.2 ≤ b
    rw [EReal.coe_le_coe_iff]
    constructor <;> intro h <;> linarith
  rw [fenchelConjugate_le_coe_iff]
  change (fun x : E ↦ ((⟪v,x⟫_ℝ-b:ℝ):EReal)) ≤ f ↔ _
  rw [← epigraph_subset_epigraph_iff,he]

/-- **Theorem 11.1**, lower closure never changes the conjugate. -/
theorem fenchelConjugate_epiClosure (f : E → EReal) :
    fenchelConjugate (epiClosure f) = fenchelConjugate f := by
  apply eq_of_epigraph_eq
  ext p
  change fenchelConjugate (epiClosure f) p.1 ≤ (p.2:EReal) ↔ fenchelConjugate f p.1 ≤ (p.2:EReal)
  rw [fenchelConjugate_le_coe_iff_epigraph,fenchelConjugate_le_coe_iff_epigraph,epigraph_epiClosure]
  exact ⟨fun h ↦ subset_closure.trans h,fun h ↦ closure_minimal h (isClosed_fenchelEpigraphHalfspace _ _)⟩

/-- **Theorem 11.1**, convexification never changes the conjugate. -/
theorem fenchelConjugate_convexHullFunction (f : E → EReal) :
    fenchelConjugate (convexHullFunction f) = fenchelConjugate f := by
  apply eq_of_epigraph_eq
  ext p
  change fenchelConjugate (convexHullFunction f) p.1 ≤ (p.2:EReal) ↔ fenchelConjugate f p.1 ≤ (p.2:EReal)
  rw [fenchelConjugate_le_coe_iff_epigraph,fenchelConjugate_le_coe_iff_epigraph]
  constructor
  · intro h
    exact (subset_convexHull ℝ (epigraph f)).trans ((convexHull_epigraph_subset_epigraph_convexHullFunction f).trans h)
  · intro h
    exact (epigraph_convexHullFunction_subset_closure f).trans
      (closure_minimal (convexHull_min h (convex_fenchelEpigraphHalfspace _ _)) (isClosed_fenchelEpigraphHalfspace _ _))

theorem fenchelConjugate_epiClosure_convexHullFunction (f : E → EReal) :
    fenchelConjugate (epiClosure (convexHullFunction f)) = fenchelConjugate f := by
  rw [fenchelConjugate_epiClosure,fenchelConjugate_convexHullFunction]

variable [FiniteDimensional ℝ E]

/-- **Theorem 11.1**, general Fenchel–Moreau formula under the precise
hypothesis that the convex hull function is proper. -/
theorem fenchelConjugate_fenchelConjugate_eq_epiClosure_convexHullFunction {f : E → EReal}
    (hp : IsProper (convexHullFunction f)) :
    fenchelConjugate (fenchelConjugate f) = epiClosure (convexHullFunction f) := by
  have hpg := isProper_epiClosure_convexHullFunction hp
  have hlg : LowerSemicontinuous (epiClosure (convexHullFunction f)) := lowerSemicontinuous_epiLowerLimit _
  have he := fenchelConjugate_fenchelConjugate_eq hpg hlg (convex_epigraph_epiClosure_convexHullFunction f)
  rwa [fenchelConjugate_epiClosure_convexHullFunction] at he

/-- Both transforms are proper, lsc and convex under the hypothesis of 11.1. -/
theorem conjugate_properties_of_proper_convexHull {f : E → EReal}
    (hp : IsProper (convexHullFunction f)) :
    (IsProper (fenchelConjugate f) ∧ LowerSemicontinuous (fenchelConjugate f) ∧ Convex ℝ (epigraph (fenchelConjugate f))) ∧
    (IsProper (fenchelConjugate (fenchelConjugate f)) ∧ LowerSemicontinuous (fenchelConjugate (fenchelConjugate f)) ∧
      Convex ℝ (epigraph (fenchelConjugate (fenchelConjugate f)))) := by
  have hpc : IsProper (fenchelConjugate f) := by
    rw [← fenchelConjugate_epiClosure_convexHullFunction f]
    exact isProper_fenchelConjugate (isProper_epiClosure_convexHullFunction hp)
      (lowerSemicontinuous_epiLowerLimit _) (convex_epigraph_epiClosure_convexHullFunction f)
  exact ⟨⟨hpc,lowerSemicontinuous_fenchelConjugate f,convex_epigraph_fenchelConjugate f⟩,
    ⟨isProper_fenchelConjugate hpc (lowerSemicontinuous_fenchelConjugate f) (convex_epigraph_fenchelConjugate f),
      lowerSemicontinuous_fenchelConjugate _,convex_epigraph_fenchelConjugate _⟩⟩

end
end RW
