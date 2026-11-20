/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Directional bounds for amenable sums with mixed infinite slopes
-/
import RockafellarWets.Chapter10.AmenableSumNeighborhoods

open Set Filter Topology Classical
open scoped InnerProductSpace BigOperators

namespace RW
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type u} [Fintype ι]

/-- The general directional sum rule gives two bounds. They agree when
no component derivative is negative infinity. -/
theorem AmenableAt.subderivative_finiteSum_bounds {f : ι → E → EReal} {x : E}
    (hf : ∀i,AmenableAt (f i) x)
    (hQ : IntersectionConstraintQualification (fun i ↦ effectiveDomain (f i)) x) (w : E) :
    (∑i,subderivative (f i) x w) ≤ subderivative (fun y ↦ ∑i,f i y) x w ∧
    subderivative (fun y ↦ ∑i,f i y) x w ≤ finiteInfAddition (fun i ↦ subderivative (f i) x w) := by
  let M := fun i ↦ Classical.choice (hf i)
  have hx (i : ι) : f i x = ((f i x).toReal:EReal) :=
    (EReal.coe_toReal (M i).finite.2 (M i).finite.1).symm
  refine ⟨subderivative_finiteSum_ge hx w,?_⟩
  choose g hp hl he using fun i ↦ (M i).exists_proper_lsc_germ le_rfl
  have hr (i : ι) := (hf i).isSubdifferentiallyRegularAt
  have hg (i : ι) := (hr i).congr_nhds (he i).symm
  have hval (i : ι) : g i x = ((f i x).toReal:EReal) := (he i).self_of_nhds.trans (hx i)
  have hh (i : ι) := horizonSubdifferential_congr_nhds_of_locallyLsc (hval i)
    (hg i).isLocallyLscAt (hr i).isLocallyLscAt (he i)
  have hq : ∀v : ι → E, (∀i,v i ∈ horizonSubdifferential (g i) x) → ∑i,v i = 0 → ∀i,v i = 0 := by
    intro v hv hz
    apply hQ v ?_ hz
    intro i
    rw [← (hf i).horizon_eq_normal_domain,← hh i]
    exact hv i
  have hsum : (fun y ↦ ∑i,g i y) =ᶠ[𝓝 x] (fun y ↦ ∑i,f i y) := by
    filter_upwards [Filter.eventually_all.mpr he] with y hy
    exact Finset.sum_congr rfl (fun i _ ↦ hy i)
  have hgsum := (AmenableAt.finiteSum hf hQ).isSubdifferentiallyRegularAt.congr_nhds hsum.symm
  have hupper := regularSubderivative_finiteSum_le_finiteInfAddition hp hl hval hq w
  have hsder := (isSubdifferentiallyRegularAt_iff_subderivative_eq_regularSubderivative.mp hgsum).2
  have hider (i : ι) := (isSubdifferentiallyRegularAt_iff_subderivative_eq_regularSubderivative.mp (hg i)).2
  rw [← hsder,subderivative_congr_nhds hsum w] at hupper
  simp_rw [← hider] at hupper
  have hdf (i : ι) : subderivative (g i) x w = subderivative (f i) x w := subderivative_congr_nhds (he i) w
  simpa only [hdf] using hupper

/-- These bounds hold at every nearby point where the sum is finite. -/
theorem AmenableAt.subderivative_finiteSum_bounds_eventually {f : ι → E → EReal} {x : E}
    (hf : ∀i,AmenableAt (f i) x)
    (hQ : IntersectionConstraintQualification (fun i ↦ effectiveDomain (f i)) x) :
    ∀ᶠ y in 𝓝 x, y ∈ effectiveDomain (fun z ↦ ∑i,f i z) → ∀w,
      (∑i,subderivative (f i) y w) ≤ subderivative (fun z ↦ ∑i,f i z) y w ∧
      subderivative (fun z ↦ ∑i,f i z) y w ≤ finiteInfAddition (fun i ↦ subderivative (f i) y w) := by
  filter_upwards [AmenableAt.finiteSum_qualification_eventually hf hQ] with y hy hyD w
  obtain ⟨hfy,hqy⟩ := hy hyD
  exact AmenableAt.subderivative_finiteSum_bounds (fun i ↦ (hfy i).2) hqy w

/-- In the general amenable case the exact nearby directional formula is
available at every point where the summands are calm from below. -/
theorem AmenableAt.subderivative_finiteSum_eventually_of_calm {f : ι → E → EReal} {x : E}
    (hf : ∀i,AmenableAt (f i) x)
    (hQ : IntersectionConstraintQualification (fun i ↦ effectiveDomain (f i)) x) :
    ∀ᶠ y in 𝓝 x, y ∈ effectiveDomain (fun z ↦ ∑i,f i z) →
      (∀i,subderivative (f i) y 0 = 0) → ∀w,
        subderivative (fun z ↦ ∑i,f i z) y w = ∑i,subderivative (f i) y w := by
  filter_upwards [AmenableAt.finiteSum_qualification_eventually hf hQ] with y hy hyD h0 w
  obtain ⟨hfy,hqy⟩ := hy hyD
  exact AmenableAt.subderivative_finiteSum_of_calm (fun i ↦ (hfy i).2) h0 hqy w

end RW
