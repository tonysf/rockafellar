/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3: Convexity in the Closed-Ball Cosmic Space

This file states Definition 3.41 and Exercises 3.42--3.44 on actual subsets
of the closed-ball compactification.  The existing ray-space results remain
the algebraic backend.
-/

import RockafellarWets.Chapter3.CosmicSetClosure

open Set
open scoped Pointwise

namespace RW

section CosmicConvexityClosedBall

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Definition 3.41**, as a predicate on a subset of the closed-ball cosmic
space.  Its ordinary and direction parts satisfy the book's three clauses. -/
def IsCosmicallyConvex (S : Set (CosmicSpace E)) : Prop :=
  CosmicConvex (cosmicOrdinaryPart S) (cosmicDirectionCone S)

/-- Definition 3.41 specialized to the book's notation `C ∪ dir K`. -/
theorem isCosmicallyConvex_cosmicSet_iff {C K : Set E} (hK : IsCone K) :
    IsCosmicallyConvex (cosmicSet C K) ↔ CosmicConvex C K := by
  simp only [IsCosmicallyConvex, cosmicOrdinaryPart_cosmicSet,
    cosmicDirectionCone_cosmicSet hK]

/-- **Exercise 3.42**, on an actual closed-ball cosmic subset: cosmic
convexity is equivalent to convexity of its corresponding ray-space cone. -/
theorem isCosmicallyConvex_iff_convex_cosmicRayCone
    {S : Set (CosmicSpace E)} :
    IsCosmicallyConvex S ↔ Convex ℝ (cosmicRayCone S) := by
  exact cosmicConvex_iff_convex_raySpaceCone (isCone_cosmicDirectionCone S)

/-- **Exercise 3.43**, in canonical-part form for an arbitrary closed-ball
cosmic subset. -/
theorem add_smul_mem_interior_of_isCosmicallyConvex
    {S : Set (CosmicSpace E)} (hS : IsCosmicallyConvex S)
    {x : E} (hx : x ∈ interior (cosmicOrdinaryPart S))
    {w : E} (hw : w ∈ cosmicDirectionCone S) {t : ℝ} (ht : 0 < t) :
    x + t • w ∈ interior (cosmicOrdinaryPart S) := by
  exact add_smul_mem_interior_of_cosmicConvex hS
    (isCone_cosmicDirectionCone S) hx hw ht

/-- Exercise 3.43 in the book's displayed `C ∪ dir K` notation. -/
theorem add_smul_mem_interior_of_isCosmicallyConvex_cosmicSet
    {C K : Set E} (hK : IsCone K)
    (hS : IsCosmicallyConvex (cosmicSet C K))
    {x : E} (hx : x ∈ interior C) {w : E} (hw : w ∈ K)
    {t : ℝ} (ht : 0 < t) :
    x + t • w ∈ interior C := by
  apply add_smul_mem_interior_of_cosmicConvex
    ((isCosmicallyConvex_cosmicSet_iff hK).1 hS) hK hx hw ht

/-- The closed-ball cosmic convex hull.  Since `CosmicSpace E` is a closed
ball subtype rather than a vector space, this is constructed from the
canonical ordinary and direction parts. -/
def cosmicConvexHull (S : Set (CosmicSpace E)) : Set (CosmicSpace E) :=
  cosmicSet
    (convexHull ℝ (cosmicOrdinaryPart S) +
      convexHull ℝ (cosmicDirectionCone S))
    (convexHull ℝ (cosmicDirectionCone S))

private theorem cosmicConvex_convexHullParts (S : Set (CosmicSpace E)) :
    CosmicConvex
      (convexHull ℝ (cosmicOrdinaryPart S) +
        convexHull ℝ (cosmicDirectionCone S))
      (convexHull ℝ (cosmicDirectionCone S)) := by
  let K := cosmicDirectionCone S
  have hKcone : IsCone K := isCone_cosmicDirectionCone S
  have hconvK : Convex ℝ (convexHull ℝ K) := convex_convexHull ℝ K
  have hconeK : IsCone (convexHull ℝ K) := isCone_convexHull hKcone
  refine ⟨(convex_convexHull ℝ (cosmicOrdinaryPart S)).add hconvK, hconvK, ?_⟩
  rintro z ⟨u, hu, v, hv, rfl⟩
  rcases hu with ⟨x, hx, y, hy, rfl⟩
  refine ⟨x, hx, y + v, add_mem_of_convex_isCone hconvK hconeK hy hv, ?_⟩
  ac_rfl

/-- The cosmic convex hull is cosmically convex. -/
theorem isCosmicallyConvex_cosmicConvexHull (S : Set (CosmicSpace E)) :
    IsCosmicallyConvex (cosmicConvexHull S) := by
  let K := cosmicDirectionCone S
  have hKcone : IsCone K := isCone_cosmicDirectionCone S
  have hHullCone : IsCone (convexHull ℝ K) := isCone_convexHull hKcone
  apply (isCosmicallyConvex_cosmicSet_iff hHullCone).2
  exact cosmicConvex_convexHullParts S

/-- Every cosmic set is contained in its cosmic convex hull. -/
theorem subset_cosmicConvexHull (S : Set (CosmicSpace E)) :
    S ⊆ cosmicConvexHull S := by
  intro p hp
  rcases cosmicEmbed_or_cosmicDirection p with ⟨x, rfl⟩ | ⟨u, rfl⟩
  · apply (cosmicEmbed_mem_cosmicSet_iff).2
    refine ⟨x, subset_convexHull ℝ _ hp, 0, ?_, by simp⟩
    exact subset_convexHull ℝ _ (isCone_cosmicDirectionCone S).1
  · apply (mem_cosmicSet).2
    right
    refine ⟨u, subset_convexHull ℝ _ ?_, rfl⟩
    right
    exact ⟨u, hp, 1, zero_lt_one, by simp⟩

/-- Universal property of the cosmic convex hull. -/
theorem cosmicConvexHull_min {S T : Set (CosmicSpace E)}
    (hST : S ⊆ T) (hT : IsCosmicallyConvex T) :
    cosmicConvexHull S ⊆ T := by
  let C := cosmicOrdinaryPart S
  let K := cosmicDirectionCone S
  let D := cosmicOrdinaryPart T
  let L := cosmicDirectionCone T
  have hCD : C ⊆ D := cosmicOrdinaryPart_mono hST
  have hKL : K ⊆ L := cosmicDirectionCone_mono hST
  have hconvD : Convex ℝ D := hT.1
  have hconvL : Convex ℝ L := hT.2.1
  have hDL : D + L ⊆ D := hT.2.2
  have hconvCD : convexHull ℝ C ⊆ D := convexHull_min hCD hconvD
  have hconvKL : convexHull ℝ K ⊆ L := convexHull_min hKL hconvL
  rw [← cosmicSet_parts T]
  apply cosmicSet_mono
  · rintro z ⟨x, hx, w, hw, rfl⟩
    exact hDL ⟨x, hconvCD hx, w, hconvKL hw, rfl⟩
  · exact hconvKL

/-- Characterization of the cosmic convex hull by its universal property. -/
theorem cosmicConvexHull_eq_self_iff {S : Set (CosmicSpace E)} :
    cosmicConvexHull S = S ↔ IsCosmicallyConvex S := by
  constructor
  · intro h
    rw [← h]
    exact isCosmicallyConvex_cosmicConvexHull S
  · intro hS
    exact Set.Subset.antisymm
      (cosmicConvexHull_min Set.Subset.rfl hS) (subset_cosmicConvexHull S)

/-- **Exercise 3.44**, exact closed-ball form. -/
theorem cosmicConvexHull_cosmicSet {C K : Set E} (hK : IsCone K) :
    cosmicConvexHull (cosmicSet C K) =
      cosmicSet (convexHull ℝ C + convexHull ℝ K) (convexHull ℝ K) := by
  simp only [cosmicConvexHull, cosmicOrdinaryPart_cosmicSet,
    cosmicDirectionCone_cosmicSet hK]

/-- The ray-space image of the exact cosmic convex-hull formula agrees with
the existing ray-space theorem. -/
theorem cosmicRayCone_cosmicConvexHull_cosmicSet {C K : Set E}
    (hK : IsCone K) :
    cosmicRayCone (cosmicConvexHull (cosmicSet C K)) =
      convexHull ℝ (raySpaceCone C K) := by
  rw [cosmicConvexHull_cosmicSet hK]
  rw [cosmicRayCone_cosmicSet (isCone_convexHull hK)]
  exact (convexHull_raySpaceCone hK).symm

@[simp]
theorem cosmicConvexHull_empty :
    cosmicConvexHull (∅ : Set (CosmicSpace E)) = ∅ := by
  apply Set.Subset.antisymm
  · exact cosmicConvexHull_min (Set.empty_subset _) (by
      rw [← cosmicSet_empty_zero (E := E)]
      exact (isCosmicallyConvex_cosmicSet_iff
        (⟨Set.mem_singleton 0, by simp⟩ : IsCone ({0} : Set E))).2
          ⟨convex_empty, convex_singleton 0, by simp⟩)
  · exact Set.empty_subset _

@[simp]
theorem cosmicConvexHull_univ :
    cosmicConvexHull (Set.univ : Set (CosmicSpace E)) = Set.univ := by
  exact Set.eq_univ_of_univ_subset (subset_cosmicConvexHull Set.univ)

end CosmicConvexityClosedBall

end RW
