/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Local separable calculus for factors of different dimensions
-/
import RockafellarWets.Chapter10.DependentSeparableRegularity
import RockafellarWets.Chapter10.FiniteSeparableLocalization

open Filter Set Topology
open scoped InnerProductSpace
namespace RW
noncomputable section
variable {n : ℕ} {E : Fin n → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]

theorem exists_proper_dependentSeparable_germ (f : ∀ i, E i → EReal) (hf : ∀ i, LowerSemicontinuous (f i))
    (x : PiLp 2 E) (c : Fin n → ℝ) (hx : ∀ i, f i (x i) = c i) :
    ∃ g : ∀ i, E i → EReal, (∀ i, IsProper (g i)) ∧ (∀ i, LowerSemicontinuous (g i)) ∧
      (∀ i, g i =ᶠ[𝓝 (x i)] f i) ∧ dependentSeparablePi g =ᶠ[𝓝 x] dependentSeparablePi f := by
  choose g hpg hlg he using fun i ↦ exists_proper_lsc_germ (hf i) (hx i)
  refine ⟨g,hpg,hlg,he,?_⟩
  have hcoord (i : Fin n) : ∀ᶠ q : PiLp 2 E in 𝓝 x, g i (q i) = f i (q i) :=
    ((PiLp.continuous_apply 2 (E) i).tendsto x).eventually (he i)
  filter_upwards [Filter.eventually_all.mpr hcoord] with q hq
  exact Finset.sum_congr rfl (fun i _ ↦ hq i)

/-- **Proposition 10.5**, finite limiting and horizon product rules with
only the printed lower semicontinuity and finite-value assumptions. -/
theorem dependentSeparablePi_local_subgradients (f : ∀ i, E i → EReal) (hf : ∀ i, LowerSemicontinuous (f i))
    (x : PiLp 2 E) (c : Fin n → ℝ) (hx : ∀ i, f i (x i) = c i) :
    (∀ v, v ∈ subdifferential (dependentSeparablePi f) x ↔ ∀ i, v i ∈ subdifferential (f i) (x i)) ∧
    horizonSubdifferential (dependentSeparablePi f) x ⊆ {v | ∀ i, v i ∈ horizonSubdifferential (f i) (x i)} := by
  obtain ⟨g,hp,hl,he,hes⟩ := exists_proper_dependentSeparable_germ f hf x c hx
  have hg (i : Fin n) : g i (x i) = c i := (he i).eq_of_nhds.trans (hx i)
  have hval := dependentSeparablePi_eq_coe hg
  have hloc := locallyLscAt_of_lowerSemicontinuous_finite (lowerSemicontinuous_dependentSeparablePi hl (fun i ↦ (hp i).2)) hval
  constructor
  · intro v
    rw [← subdifferential_congr_nhds_of_finite hval hes,mem_subdifferential_dependentSeparableFin_iff n E g hp hl x v c hg]
    exact forall_congr' fun i ↦ by rw [subdifferential_congr_nhds_of_finite (hg i) (he i)]
  · rw [← horizonSubdifferential_congr_nhds_of_locallyLsc hval hloc (hloc.congr_nhds hes) hes]
    intro v hv i
    have h := horizonSubdifferential_dependentSeparableFin_subset n E g hp hl x c hg hv i
    rwa [horizonSubdifferential_congr_nhds_of_locallyLsc (hg i)
      (locallyLscAt_of_lowerSemicontinuous_finite (hl i) (hg i))
      (locallyLscAt_of_lowerSemicontinuous_finite (hf i) (hx i)) (he i)] at h

/-- **Proposition 10.5**, the finite regular-subderivative upper bound
without global properness. -/
theorem regularSubderivative_dependentSeparablePi_local_le (f : ∀ i, E i → EReal)
    (hf : ∀ i, LowerSemicontinuous (f i)) (x w : PiLp 2 E)
    (c : Fin n → ℝ) (hx : ∀ i, f i (x i) = c i) (h0 : ∀ i, subderivative (f i) (x i) 0 = 0) :
    regularSubderivative (dependentSeparablePi f) x w ≤ ∑ i, regularSubderivative (f i) (x i) (w i) := by
  obtain ⟨g,hp,hl,he,hes⟩ := exists_proper_dependentSeparable_germ f hf x c hx
  have hg (i : Fin n) : g i (x i) = c i := (he i).eq_of_nhds.trans (hx i)
  have hval := dependentSeparablePi_eq_coe hg
  have hloc := locallyLscAt_of_lowerSemicontinuous_finite (lowerSemicontinuous_dependentSeparablePi hl (fun i ↦ (hp i).2)) hval
  have hzero (i : Fin n) : subderivative (g i) (x i) 0 = 0 := (subderivative_congr_nhds (he i) 0).trans (h0 i)
  have h := regularSubderivative_dependentSeparableFin_le n E g hp hl x w c hg hzero
  rw [regularSubderivative_congr_nhds_of_locallyLsc hval hloc (hloc.congr_nhds hes) hes w] at h
  have hei (i : Fin n) := regularSubderivative_congr_nhds_of_locallyLsc (hg i)
    (locallyLscAt_of_lowerSemicontinuous_finite (hl i) (hg i))
    (locallyLscAt_of_lowerSemicontinuous_finite (hf i) (hx i)) (he i) (w i)
  simpa only [hei] using h

/-- **Proposition 10.5**, finite regularity and all exact formulas without
global properness of the component functions. -/
theorem dependentSeparablePi_local_regularity (f : ∀ i, E i → EReal)
    (hf : ∀ i, LowerSemicontinuous (f i)) (x : PiLp 2 E)
    (hr : ∀ i, IsSubdifferentiallyRegularAt (f i) (x i))
    (h0 : ∀ i, subderivative (f i) (x i) 0 = 0) :
    IsSubdifferentiallyRegularAt (dependentSeparablePi f) x ∧
    (∀ w, subderivative (dependentSeparablePi f) x w = ∑ i, subderivative (f i) (x i) (w i)) ∧
    horizonSubdifferential (dependentSeparablePi f) x = {v | ∀ i, v i ∈ horizonSubdifferential (f i) (x i)} := by
  let c := fun i ↦ (f i (x i)).toReal
  have hx (i : Fin n) : f i (x i) = (c i:EReal) := (EReal.coe_toReal (hr i).2.1 (hr i).1).symm
  obtain ⟨g,hp,hl,he,hes⟩ := exists_proper_dependentSeparable_germ f hf x c hx
  have hg (i : Fin n) : g i (x i) = c i := (he i).eq_of_nhds.trans (hx i)
  have hval := dependentSeparablePi_eq_coe hg
  have hloc := locallyLscAt_of_lowerSemicontinuous_finite (lowerSemicontinuous_dependentSeparablePi hl (fun i ↦ (hp i).2)) hval
  have hrg (i : Fin n) := (hr i).congr_nhds (he i).symm
  have hzero (i : Fin n) : subderivative (g i) (x i) 0 = 0 := (subderivative_congr_nhds (he i) 0).trans (h0 i)
  have hreg := dependentSeparablePi_regularity g hp hl x hrg hzero
  refine ⟨hreg.1.congr_nhds hes,?_,?_⟩
  · intro w
    have h := hreg.2 w
    rw [subderivative_congr_nhds hes w] at h
    simpa only [subderivative_congr_nhds (he _) _] using h
  · rw [← horizonSubdifferential_congr_nhds_of_locallyLsc hval hloc (hloc.congr_nhds hes) hes,
      horizonSubdifferential_dependentSeparablePi_eq_of_regular g hp hl x hrg hzero]
    ext v
    apply forall_congr'
    intro i
    rw [horizonSubdifferential_congr_nhds_of_locallyLsc (hg i)
      (locallyLscAt_of_lowerSemicontinuous_finite (hl i) (hg i))
      (locallyLscAt_of_lowerSemicontinuous_finite (hf i) (hx i)) (he i)]

end
end RW
