/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Local finite separable calculus

Truncating below away from the base values removes global properness from
the finite-family formulas in Proposition 10.5.
-/

import RockafellarWets.Chapter10.FiniteSeparableRegularity
import RockafellarWets.Chapter10.FiniteInfimumSubderivatives

open Filter Set Topology
open scoped InnerProductSpace

namespace RW

noncomputable section

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem regularSubderivative_congr_nhds_of_locallyLsc {f g : E → EReal} {x : E} {a : ℝ}
    (hx : f x = a) (hlf : IsLocallyLscAt f x) (hlg : IsLocallyLscAt g x)
    (he : f =ᶠ[𝓝 x] g) (w : E) : regularSubderivative f x w = regularSubderivative g x w := by
  have hg : g x = a := he.eq_of_nhds.symm.trans hx
  have hsub := subdifferential_congr_nhds_of_finite hx he
  have hhor := horizonSubdifferential_congr_nhds_of_locallyLsc hx hlf hlg he
  have hh (b : ℝ) : regularSubderivative f x w ≤ (b:EReal) ↔ regularSubderivative g x w ≤ (b:EReal) := by
    rw [regularSubderivative_le_coe_iff_support_polar hx hlf,
      regularSubderivative_le_coe_iff_support_polar hg hlg,hsub,hhor]
  apply le_antisymm
  · by_contra! h
    obtain ⟨b,hb,hb'⟩ := EReal.exists_between_coe_real h
    exact hb'.not_ge ((hh b).mpr hb.le)
  · by_contra! h
    obtain ⟨b,hb,hb'⟩ := EReal.exists_between_coe_real h
    exact hb'.not_ge ((hh b).mp hb.le)

theorem exists_proper_lsc_germ {f : E → EReal} {x : E} {c : ℝ}
    (hf : LowerSemicontinuous f) (hx : f x = c) :
    ∃ g : E → EReal, IsProper g ∧ LowerSemicontinuous g ∧ g =ᶠ[𝓝 x] f := by
  let g := fun z ↦ max (f z) ((c-1:ℝ):EReal)
  have hval : g x = (c:EReal) := by
    change max (f x) ((c-1:ℝ):EReal) = _
    rw [hx]
    exact max_eq_left (EReal.coe_le_coe_iff.mpr (by linarith))
  refine ⟨g,⟨⟨x,hval.trans_lt (EReal.coe_lt_top _)⟩,
    fun z ↦ (EReal.bot_lt_coe _).trans_le (le_max_right ..)⟩,
    hf.sup lowerSemicontinuous_const,?_⟩
  filter_upwards [hf x ((c-1:ℝ):EReal) (by change ((c-1:ℝ):EReal) < f x; rw [hx]; exact EReal.coe_lt_coe_iff.mpr (by linarith))] with z hz
  exact max_eq_left hz.le

theorem exists_proper_separable_germ (f : ι → E → EReal) (hf : ∀ i, LowerSemicontinuous (f i))
    (x : PiLp 2 (fun _ : ι ↦ E)) (c : ι → ℝ) (hx : ∀ i, f i (x i) = c i) :
    ∃ g : ι → E → EReal, (∀ i, IsProper (g i)) ∧ (∀ i, LowerSemicontinuous (g i)) ∧
      (∀ i, g i =ᶠ[𝓝 (x i)] f i) ∧ separablePi g =ᶠ[𝓝 x] separablePi f := by
  choose g hpg hlg he using fun i ↦ exists_proper_lsc_germ (hf i) (hx i)
  refine ⟨g,hpg,hlg,he,?_⟩
  have hcoord (i : ι) : ∀ᶠ q : PiLp 2 (fun _ : ι ↦ E) in 𝓝 x, g i (q i) = f i (q i) :=
    ((PiLp.continuous_apply 2 (fun _ : ι ↦ E) i).tendsto x).eventually (he i)
  filter_upwards [Filter.eventually_all.mpr hcoord] with q hq
  exact Finset.sum_congr rfl (fun i _ ↦ hq i)

/-- **Proposition 10.5**, finite limiting and horizon product rules with
only the printed lower semicontinuity and finite-value assumptions. -/
theorem separablePi_local_subgradients (f : ι → E → EReal) (hf : ∀ i, LowerSemicontinuous (f i))
    (x : PiLp 2 (fun _ : ι ↦ E)) (c : ι → ℝ) (hx : ∀ i, f i (x i) = c i) :
    (∀ v, v ∈ subdifferential (separablePi f) x ↔ ∀ i, v i ∈ subdifferential (f i) (x i)) ∧
    horizonSubdifferential (separablePi f) x ⊆ {v | ∀ i, v i ∈ horizonSubdifferential (f i) (x i)} := by
  obtain ⟨g,hp,hl,he,hes⟩ := exists_proper_separable_germ f hf x c hx
  have hg (i : ι) : g i (x i) = c i := (he i).eq_of_nhds.trans (hx i)
  have hval := separablePi_eq_coe hg
  have hloc := locallyLscAt_of_lowerSemicontinuous_finite (lowerSemicontinuous_separablePi hl (fun i ↦ (hp i).2)) hval
  constructor
  · intro v
    rw [← subdifferential_congr_nhds_of_finite hval hes,mem_subdifferential_separablePi_iff g hp hl x v c hg]
    exact forall_congr' fun i ↦ by rw [subdifferential_congr_nhds_of_finite (hg i) (he i)]
  · rw [← horizonSubdifferential_congr_nhds_of_locallyLsc hval hloc (hloc.congr_nhds hes) hes]
    intro v hv i
    have h := horizonSubdifferential_separablePi_subset g hp hl x c hg hv i
    rwa [horizonSubdifferential_congr_nhds_of_locallyLsc (hg i)
      (locallyLscAt_of_lowerSemicontinuous_finite (hl i) (hg i))
      (locallyLscAt_of_lowerSemicontinuous_finite (hf i) (hx i)) (he i)] at h

/-- **Proposition 10.5**, the finite regular-subderivative upper bound
without global properness. -/
theorem regularSubderivative_separablePi_local_le (f : ι → E → EReal)
    (hf : ∀ i, LowerSemicontinuous (f i)) (x w : PiLp 2 (fun _ : ι ↦ E))
    (c : ι → ℝ) (hx : ∀ i, f i (x i) = c i) (h0 : ∀ i, subderivative (f i) (x i) 0 = 0) :
    regularSubderivative (separablePi f) x w ≤ ∑ i, regularSubderivative (f i) (x i) (w i) := by
  obtain ⟨g,hp,hl,he,hes⟩ := exists_proper_separable_germ f hf x c hx
  have hg (i : ι) : g i (x i) = c i := (he i).eq_of_nhds.trans (hx i)
  have hval := separablePi_eq_coe hg
  have hloc := locallyLscAt_of_lowerSemicontinuous_finite (lowerSemicontinuous_separablePi hl (fun i ↦ (hp i).2)) hval
  have hzero (i : ι) : subderivative (g i) (x i) 0 = 0 := (subderivative_congr_nhds (he i) 0).trans (h0 i)
  have h := regularSubderivative_separablePi_le g hp hl x w c hg hzero
  rw [regularSubderivative_congr_nhds_of_locallyLsc hval hloc (hloc.congr_nhds hes) hes w] at h
  have hei (i : ι) := regularSubderivative_congr_nhds_of_locallyLsc (hg i)
    (locallyLscAt_of_lowerSemicontinuous_finite (hl i) (hg i))
    (locallyLscAt_of_lowerSemicontinuous_finite (hf i) (hx i)) (he i) (w i)
  simpa only [hei] using h

/-- **Proposition 10.5**, finite regularity and all exact formulas without
global properness of the component functions. -/
theorem separablePi_local_regularity (f : ι → E → EReal)
    (hf : ∀ i, LowerSemicontinuous (f i)) (x : PiLp 2 (fun _ : ι ↦ E))
    (hr : ∀ i, IsSubdifferentiallyRegularAt (f i) (x i))
    (h0 : ∀ i, subderivative (f i) (x i) 0 = 0) :
    IsSubdifferentiallyRegularAt (separablePi f) x ∧
    (∀ w, subderivative (separablePi f) x w = ∑ i, subderivative (f i) (x i) (w i)) ∧
    horizonSubdifferential (separablePi f) x = {v | ∀ i, v i ∈ horizonSubdifferential (f i) (x i)} := by
  let c := fun i ↦ (f i (x i)).toReal
  have hx (i : ι) : f i (x i) = (c i:EReal) := (EReal.coe_toReal (hr i).2.1 (hr i).1).symm
  obtain ⟨g,hp,hl,he,hes⟩ := exists_proper_separable_germ f hf x c hx
  have hg (i : ι) : g i (x i) = c i := (he i).eq_of_nhds.trans (hx i)
  have hval := separablePi_eq_coe hg
  have hloc := locallyLscAt_of_lowerSemicontinuous_finite (lowerSemicontinuous_separablePi hl (fun i ↦ (hp i).2)) hval
  have hrg (i : ι) := (hr i).congr_nhds (he i).symm
  have hzero (i : ι) : subderivative (g i) (x i) 0 = 0 := (subderivative_congr_nhds (he i) 0).trans (h0 i)
  have hreg := separablePi_regularity g hp hl x hrg hzero
  refine ⟨hreg.1.congr_nhds hes,?_,?_⟩
  · intro w
    have h := hreg.2 w
    rw [subderivative_congr_nhds hes w] at h
    simpa only [subderivative_congr_nhds (he _) _] using h
  · rw [← horizonSubdifferential_congr_nhds_of_locallyLsc hval hloc (hloc.congr_nhds hes) hes,
      horizonSubdifferential_separablePi_eq_of_regular g hp hl x hrg hzero]
    ext v
    apply forall_congr'
    intro i
    rw [horizonSubdifferential_congr_nhds_of_locallyLsc (hg i)
      (locallyLscAt_of_lowerSemicontinuous_finite (hl i) (hg i))
      (locallyLscAt_of_lowerSemicontinuous_finite (hf i) (hx i)) (he i)]

end

end RW
