/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Nearby cone formulas for amenable intersections
-/
import RockafellarWets.Chapter10.AmenableIntersections
import RockafellarWets.Chapter10.AmenabilityGerms

open Set Filter Topology
open scoped InnerProductSpace BigOperators

namespace RW
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type u} [Fintype ι]

/-- Local closedness is preserved by finite Euclidean products. -/
theorem isLocallyClosedAt_l2PiSet {C : ι → Set E} {x : PiLp 2 (fun _ : ι ↦ E)}
    (h : ∀i, IsLocallyClosedAt (C i) (x i)) : IsLocallyClosedAt (l2PiSet C) x := by
  choose V hV hVc hCV using h
  refine ⟨l2PiSet V,?_,isClosed_l2PiSet hVc,?_⟩
  · change ∀ᶠ y in 𝓝 x, ∀i, y i ∈ V i
    exact Filter.eventually_all.mpr (fun i ↦ ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι ↦ E) i).continuous.tendsto x).eventually (hV i))
  · have he : l2PiSet C ∩ l2PiSet V = l2PiSet (fun i ↦ C i ∩ V i) := by
      ext y
      simp only [mem_inter_iff,mem_l2PiSet]
      exact forall_and.symm
    rw [he]
    exact isClosed_l2PiSet hCV

/-- The finite-intersection qualification persists for locally closed factors. -/
theorem IntersectionConstraintQualification.eventually {C : ι → Set E} {x : E}
    (hQ : IntersectionConstraintQualification C x) (hC : ∀i, IsLocallyClosedAt (C i) x) :
    ∀ᶠ y in 𝓝 x, IntersectionConstraintQualification C y := by
  let A := l2PiDiag (ι := ι) (E := E)
  have hclosed : IsLocallyClosedAt (l2PiSet C) (A x) :=
    isLocallyClosedAt_l2PiSet (by simpa only [A,l2PiDiag_apply_coord] using hC)
  have hbase : ∀v ∈ normalCone (l2PiSet C) (A x), A.adjoint v = 0 → v = 0 := by
    intro v hv hz
    rw [normalCone_l2PiSet] at hv
    have hh := hQ (fun i ↦ v i) (by simpa only [A,l2PiDiag_apply_coord] using hv)
      (by simpa only [A,l2PiDiag_adjoint,l2PiSum_apply] using hz)
    ext i
    exact hh i
  have he := normalKernelQualification_eventually_of_locallyClosed hclosed A.continuous.continuousAt
    (continuousAt_const : ContinuousAt (fun _ : E ↦ A.adjoint) x) hbase
  filter_upwards [he] with y hy
  intro v hv hz i
  have hh := hy (WithLp.toLp 2 v) (by simpa only [normalCone_l2PiSet,mem_l2PiSet,A,l2PiDiag_apply_coord] using hv)
    (by simpa only [A,l2PiDiag_adjoint,l2PiSum_apply] using hz)
  exact congrArg (fun z : PiLp 2 (fun _ : ι ↦ E) ↦ z i) hh

/-- The exact cone formulas need only local closedness, already supplied
by amenability of the factors. -/
theorem SetAmenableAt.iInter_cones {C : ι → Set E} {x : E}
    (hC : ∀i, SetAmenableAt (C i) x) (hQ : IntersectionConstraintQualification C x) :
    normalCone (⋂i,C i) x = finiteSetSum (fun i ↦ normalCone (C i) x) ∧
      tangentCone (⋂i,C i) x = ⋂i,tangentCone (C i) x := by
  have hloc (i : ι) : ∃D : Set E, IsClosed D ∧ C i =ᶠ[𝓝 x] D := by
    obtain ⟨V,hV,_,hCV⟩ := (hC i).isClarkeRegularAt.1
    refine ⟨C i ∩ V,hCV,?_⟩
    filter_upwards [hV] with y hy
    exact propext ⟨fun hc ↦ ⟨hc,hy⟩,fun hc ↦ hc.1⟩
  choose D hD he using hloc
  have hinter : (⋂i,C i) =ᶠ[𝓝 x] (show Set E from ⋂i,D i) := by
    filter_upwards [Filter.eventually_all.mpr he] with y hy
    apply propext
    change y ∈ (⋂i,C i) ↔ y ∈ (⋂i,D i)
    simp only [mem_iInter]
    exact forall_congr' (fun i ↦ Iff.of_eq (hy i))
  have hxC (i : ι) : x ∈ C i := by obtain ⟨M⟩ := hC i; exact M.base
  have hxD : x ∈ ⋂i,D i := mem_iInter.mpr (fun i ↦ (Iff.of_eq (he i).self_of_nhds).mp (hxC i))
  have hQD : IntersectionConstraintQualification D x := by
    intro v hv hz
    exact hQ v (fun i ↦ (normalCone_congr_nhds (he i)).symm ▸ hv i) hz
  have hrD (i : ι) := (hC i).isClarkeRegularAt.congr_nhds (he i)
  have hh := clarkeRegularity_iInter hD hxD hQD hrD
  constructor
  · rw [normalCone_congr_nhds hinter,hh.2.2.2]
    congr 1
    funext i
    exact (normalCone_congr_nhds (he i)).symm
  · rw [tangentCone_congr_nhds hinter,hh.2.1]
    congr 1
    funext i
    exact (tangentCone_congr_nhds (he i)).symm

/-- **Exercise 10.26(c)**: the formulas hold at every feasible point in a
common neighborhood of the base point. -/
theorem SetAmenableAt.iInter_cones_eventually {C : ι → Set E} {x : E}
    (hC : ∀i, SetAmenableAt (C i) x) (hQ : IntersectionConstraintQualification C x) :
    ∀ᶠ y in 𝓝 x, y ∈ ⋂i,C i →
      normalCone (⋂i,C i) y = finiteSetSum (fun i ↦ normalCone (C i) y) ∧
      tangentCone (⋂i,C i) y = ⋂i,tangentCone (C i) y := by
  have hnear := Filter.eventually_all.mpr (fun i ↦ (hC i).eventually)
  have hqual := hQ.eventually (fun i ↦ (hC i).isClarkeRegularAt.1)
  filter_upwards [hnear,hqual] with y hy hqy hmem
  exact SetAmenableAt.iInter_cones (fun i ↦ hy i (mem_iInter.mp hmem i)) hqy

end RW
