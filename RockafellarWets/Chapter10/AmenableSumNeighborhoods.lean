/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Nearby calculus for finite amenable sums
-/
import RockafellarWets.Chapter10.AmenableSumCalculus
import RockafellarWets.Chapter10.AmenableDomainClosures
import RockafellarWets.Chapter10.AmenableIntersectionCalculus

open Set Filter Topology Classical
open scoped InnerProductSpace BigOperators

namespace RW
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type u} [Fintype ι]

/-- The finite-sum qualification persists at nearby points of the sum's domain. -/
theorem AmenableAt.finiteSum_qualification_eventually {f : ι → E → EReal} {x : E}
    (hf : ∀i,AmenableAt (f i) x)
    (hQ : IntersectionConstraintQualification (fun i ↦ effectiveDomain (f i)) x) :
    ∀ᶠ y in 𝓝 x, y ∈ effectiveDomain (fun z ↦ ∑i,f i z) →
      (∀i,y ∈ effectiveDomain (f i) ∧ AmenableAt (f i) y) ∧
      IntersectionConstraintQualification (fun i ↦ effectiveDomain (f i)) y := by
  let M := fun i ↦ Classical.choice (hf i)
  let L := AmenableFunctionModel.finiteSum M le_rfl hQ
  have hQc : IntersectionConstraintQualification (fun i ↦ closure (effectiveDomain (f i))) x := by
    intro v hv hz
    exact hQ v (fun i ↦ (hf i).normal_closure_domain_eq ▸ hv i) hz
  have hnear := hQc.eventually (fun i ↦ RW.IsClosed.isLocallyClosedAt isClosed_closure x)
  filter_upwards [hnear,Filter.eventually_all.mpr (fun i ↦ (hf i).eventually),
    L.isOpen.mem_nhds L.mem] with y hyQ hyf hyV hyDom
  have houter : L.inner y ∈ effectiveDomain L.outer := by
    change L.outer (L.inner y) < ⊤
    rw [← L.eqOn y hyV]
    exact hyDom
  change (WithLp.toLp 2 (fun i ↦ (M i).inner y)) ∈
    effectiveDomain (dependentSeparablePi (fun i ↦ (M i).outer)) at houter
  rw [effectiveDomain_dependentSeparablePi (fun i ↦ (M i).proper)] at houter
  have hfi (i : ι) : y ∈ effectiveDomain (f i) := by
    change f i y < ⊤
    rw [(M i).eqOn y (mem_iInter.mp hyV i)]
    exact houter i
  have hfy (i : ι) := hyf i (hfi i)
  refine ⟨fun i ↦ ⟨hfi i,hfy i⟩,?_⟩
  intro v hv hz
  exact hyQ v (fun i ↦ (hfy i).normal_closure_domain_eq.symm ▸ hv i) hz

/-- **Exercise 10.26(a)**: the exact subgradient formula holds throughout
a neighborhood on the domain of the sum. -/
theorem AmenableAt.subdifferential_finiteSum_eventually {f : ι → E → EReal} {x : E}
    (hf : ∀i,AmenableAt (f i) x)
    (hQ : IntersectionConstraintQualification (fun i ↦ effectiveDomain (f i)) x) :
    ∀ᶠ y in 𝓝 x, y ∈ effectiveDomain (fun z ↦ ∑i,f i z) →
      subdifferential (fun z ↦ ∑i,f i z) y = finiteSetSum (fun i ↦ subdifferential (f i) y) := by
  filter_upwards [AmenableAt.finiteSum_qualification_eventually hf hQ] with y hy hyD
  obtain ⟨hfy,hqy⟩ := hy hyD
  exact AmenableAt.subdifferential_finiteSum (fun i ↦ (hfy i).2) hqy

/-- **Exercise 10.26(a)**: in the fully amenable case both displayed
formulas hold nearby, without any additional directional hypotheses. -/
theorem FullyAmenableAt.finiteSum_derivatives_eventually {f : ι → E → EReal} {x : E}
    (hf : ∀i,FullyAmenableAt (f i) x)
    (hQ : IntersectionConstraintQualification (fun i ↦ effectiveDomain (f i)) x) :
    ∀ᶠ y in 𝓝 x, y ∈ effectiveDomain (fun z ↦ ∑i,f i z) →
      subdifferential (fun z ↦ ∑i,f i z) y = finiteSetSum (fun i ↦ subdifferential (f i) y) ∧
      (∀w,subderivative (fun z ↦ ∑i,f i z) y w = ∑i,subderivative (f i) y w) := by
  filter_upwards [AmenableAt.finiteSum_qualification_eventually (fun i ↦ (hf i).amenableAt) hQ,
    Filter.eventually_all.mpr (fun i ↦ (hf i).eventually)] with y hy hyf hyD
  obtain ⟨hfy,hqy⟩ := hy hyD
  have hfull (i : ι) := hyf i (hfy i).1
  exact ⟨AmenableAt.subdifferential_finiteSum (fun i ↦ (hfy i).2) hqy,
    fun w ↦ FullyAmenableAt.subderivative_finiteSum hfull hqy w⟩

end RW
