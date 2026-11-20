/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Local subgradient calculus for amenable finite sums
-/
import RockafellarWets.Chapter10.AmenableFiniteSums
import RockafellarWets.Chapter10.FiniteSumSubderivatives

open Set Filter Topology Classical
open scoped InnerProductSpace BigOperators

namespace RW
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type u} [Fintype ι]

/-- Every local amenable representation has a globally proper and lower
semicontinuous representative of the same germ. -/
theorem AmenableFunctionModel.exists_proper_lsc_germ {f : E → EReal} {x : E} {r : ℕ} {full : Bool}
    (M : AmenableFunctionModel f x r full) (hr : 1 ≤ r) :
    ∃g : E → EReal, IsProper g ∧ LowerSemicontinuous g ∧ g =ᶠ[𝓝 x] f := by
  obtain ⟨G,hG,he⟩ := exists_contDiff_eventuallyEq_of_contDiffOn M.isOpen M.mem
    (M.smooth.of_le (by exact_mod_cast hr) : ContDiffOn ℝ 1 M.inner M.neighborhood)
  have hv : M.outer (G x) = f x := by rw [he.self_of_nhds,← M.eqOn x M.mem]
  refine ⟨M.outer ∘ G,⟨⟨x,?_⟩,fun y ↦ M.proper.2 _⟩,M.lsc.comp hG.continuous,?_⟩
  · change M.outer (G x) < ⊤
    rw [hv]
    exact lt_top_iff_ne_top.mpr M.finite.2
  · filter_upwards [he,M.isOpen.mem_nhds M.mem] with y hy hyV
    change M.outer (G y) = f y
    rw [hy,← M.eqOn y hyV]

/-- The exact finite subgradient rule only uses local amenability. -/
theorem AmenableAt.subdifferential_finiteSum {f : ι → E → EReal} {x : E}
    (hf : ∀i,AmenableAt (f i) x)
    (hQ : ∀v : ι → E, (∀i,v i ∈ normalCone (effectiveDomain (f i)) x) → ∑i,v i = 0 → ∀i,v i = 0) :
    subdifferential (fun y ↦ ∑i,f i y) x = finiteSetSum (fun i ↦ subdifferential (f i) x) := by
  let M := fun i ↦ Classical.choice (hf i)
  choose g hp hl he using fun i ↦ (M i).exists_proper_lsc_germ le_rfl
  have hr (i : ι) := (hf i).isSubdifferentiallyRegularAt
  have hg (i : ι) := (hr i).congr_nhds (he i).symm
  have hval (i : ι) : g i x = ((f i x).toReal:EReal) :=
    (he i).self_of_nhds.trans (EReal.coe_toReal (M i).finite.2 (M i).finite.1).symm
  have hs (i : ι) := subdifferential_congr_nhds_of_finite (hval i) (he i)
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
  have hxsum : (∑i,g i x) = ((∑i,(f i x).toReal:ℝ):EReal) := by
    simpa only [separablePi,finiteDiagonal_apply] using separablePi_eq_coe (x := finiteDiagonal x) (by simpa using hval)
  rw [← subdifferential_congr_nhds_of_finite (f := fun y : E ↦ ∑i,g i y) hxsum hsum,
    subdifferential_finiteSum_eq_of_regular hp hl hg hq]
  simp_rw [hs]

/-- The directional sum formula holds when the summands are calm from below,
so that no component derivative is negative infinity. -/
theorem AmenableAt.subderivative_finiteSum_of_calm {f : ι → E → EReal} {x : E}
    (hf : ∀i,AmenableAt (f i) x) (h0 : ∀i,subderivative (f i) x 0 = 0)
    (hQ : ∀v : ι → E, (∀i,v i ∈ normalCone (effectiveDomain (f i)) x) → ∑i,v i = 0 → ∀i,v i = 0)
    (w : E) : subderivative (fun y ↦ ∑i,f i y) x w = ∑i,subderivative (f i) x w := by
  let M := fun i ↦ Classical.choice (hf i)
  choose g hp hl he using fun i ↦ (M i).exists_proper_lsc_germ le_rfl
  have hr (i : ι) := (hf i).isSubdifferentiallyRegularAt
  have hg (i : ι) := (hr i).congr_nhds (he i).symm
  have hval (i : ι) : g i x = ((f i x).toReal:EReal) :=
    (he i).self_of_nhds.trans (EReal.coe_toReal (M i).finite.2 (M i).finite.1).symm
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
  rw [← subderivative_congr_nhds hsum w]
  have hz (i : ι) : subderivative (g i) x 0 = 0 := (subderivative_congr_nhds (he i) 0).trans (h0 i)
  rw [(finiteSum_regularity_of_calm hp hl hg hz hq).2 w]
  exact Finset.sum_congr rfl (fun i _ ↦ subderivative_congr_nhds (he i) w)

/-- Fully amenable functions automatically satisfy the zero-direction condition. -/
theorem FullyAmenableAt.subderivative_zero {f : E → EReal} {x : E} (hf : FullyAmenableAt f x) :
    subderivative f x 0 = 0 := by
  have hp := hf.polyhedral_properties.2.2.2.2
  obtain ⟨M⟩ := hf
  have hx : f x = ((f x).toReal:EReal) := (EReal.coe_toReal M.finite.2 M.finite.1).symm
  exact (lowerSemicontinuous_positivelyHomogeneous_subderivative hx).2.zero_eq_zero_or_bot.resolve_right
    (hp.isPiecewiseLinearQuadratic.ne_bot 0)

/-- The full-amenability directional sum formula needs no additional calmness hypothesis. -/
theorem FullyAmenableAt.subderivative_finiteSum {f : ι → E → EReal} {x : E}
    (hf : ∀i,FullyAmenableAt (f i) x)
    (hQ : ∀v : ι → E, (∀i,v i ∈ normalCone (effectiveDomain (f i)) x) → ∑i,v i = 0 → ∀i,v i = 0)
    (w : E) : subderivative (fun y ↦ ∑i,f i y) x w = ∑i,subderivative (f i) x w :=
  AmenableAt.subderivative_finiteSum_of_calm (fun i ↦ (hf i).amenableAt)
    (fun i ↦ (hf i).subderivative_zero) hQ w

end RW
