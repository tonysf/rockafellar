/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Convex finite unions of polyhedra
-/
import RockafellarWets.Chapter10.PiecewiseLinearQuadratic
import RockafellarWets.Chapter8.ConvexSubgradients

open Set Classical
open scoped Pointwise

namespace RW
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A polyhedron has finite point and direction generators lying in the
polyhedron and its horizon cone respectively. Empty pieces cause no exception. -/
theorem IsPolyhedral.exists_contained_generators {C : Set E} (hC : IsPolyhedral C) :
    ∃ s t : Finset E, C = extendedConvexHull (s : Set E) (t : Set E) ∧
      (s : Set E) ⊆ C ∧ (t : Set E) ⊆ horizonCone C := by
  rcases C.eq_empty_or_nonempty with h | h
  · refine ⟨∅,∅,?_,by simp,by simp⟩
    simp [h,extendedConvexHull]
  · obtain ⟨s,t,hs,he⟩ := hC.exists_nonempty_generators_of_nonempty h
    refine ⟨s,t,he,?_,?_⟩
    · rw [he]
      exact subset_extendedConvexHull_left _ _
    · rw [he,horizonCone_extendedConvexHull_finset_eq_conicHull s t hs (isClosed_conicHull_finset t)]
      exact subset_conicHull

/-- A finite union of polyhedra is polyhedral whenever the union is convex. -/
theorem isPolyhedral_iUnion_of_convex {ι : Type*} [Fintype ι] {C : ι → Set E}
    (hC : ∀ i, IsPolyhedral (C i)) (hc : Convex ℝ (⋃ i, C i)) :
    IsPolyhedral (⋃ i, C i) := by
  choose s t he hs ht using fun i ↦ (hC i).exists_contained_generators
  let S := Finset.univ.biUnion s
  let T := Finset.univ.biUnion t
  have hS (i : ι) : (s i : Set E) ⊆ (S : Set E) := by
    intro y hy
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hy⟩
  have hT (i : ι) : (t i : Set E) ⊆ (T : Set E) := by
    intro y hy
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hy⟩
  have hSsub : (S : Set E) ⊆ ⋃ i, C i := by
    intro y hy
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hy
    exact mem_iUnion.mpr ⟨i,hs i hi⟩
  have hTsub : (T : Set E) ⊆ horizonCone (⋃ i, C i) := by
    intro y hy
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hy
    exact horizonCone_mono (subset_iUnion C i) (ht i hi)
  have hclosed : IsClosed (⋃ i, C i) := isClosed_iUnion_of_finite fun i ↦ (hC i).isClosed
  refine ⟨S,T,Subset.antisymm ?_ ?_⟩
  · intro y hy
    obtain ⟨i,hi⟩ := mem_iUnion.mp hy
    exact extendedConvexHull_mono (hS i) (hT i) (he i ▸ hi)
  · rintro y ⟨a,ha,b,hb,rfl⟩
    have haC := convexHull_minimal hSsub hc ha
    have hbC := conicHull_minimal (convex_horizonCone hc) (isCone_horizonCone _) hTsub hb
    simpa [add_comm] using smul_add_mem_of_mem_horizonCone hc hclosed haC hbC (τ := 1) zero_le_one


/-- **Proposition 10.21**, polyhedrality of the domain in the convex case. -/
theorem IsPiecewiseLinearQuadratic.isPolyhedral_effectiveDomain {f : E → EReal}
    (hf : IsPiecewiseLinearQuadratic f) (hc : Convex ℝ (epigraph f)) :
    IsPolyhedral (effectiveDomain f) := by
  obtain ⟨m,C,q,hC,hdom,hf⟩ := hf
  rw [hdom]
  exact isPolyhedral_iUnion_of_convex hC (hdom ▸ convex_effectiveDomain_of_convex_epigraph hc)

end RW
