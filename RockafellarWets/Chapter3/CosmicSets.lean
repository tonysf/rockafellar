/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3: Cosmic Sets in the Closed-Ball Model

This file connects the closed-ball compactification from `CosmicSpace` with
the ordinary/direction and ray-space encodings used later in Chapter 3.
-/

import RockafellarWets.Chapter3.CosmicSpace
import RockafellarWets.Chapter3.CosmicClosure

open Set

namespace RW

section CosmicSets

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The direction points in cosmic space represented by a set of vectors.
Only the unit representatives of the positive rays are inserted. -/
def cosmicDirections (K : Set E) : Set (CosmicSpace E) :=
  cosmicDirection '' {u : CosmicBoundary E | (u : E) ∈ K}

/-- The closed-ball realization of the book's set `C ∪ dir K`. -/
def cosmicSet (C K : Set E) : Set (CosmicSpace E) :=
  cosmicEmbed '' C ∪ cosmicDirections K

/-- The ordinary points of a subset of cosmic space, pulled back to `E`. -/
def cosmicOrdinaryPart (S : Set (CosmicSpace E)) : Set E :=
  cosmicEmbed ⁻¹' S

/-- The cone represented by the direction points of a subset of cosmic space.
The origin is included by the book's convention for cones. -/
def cosmicDirectionCone (S : Set (CosmicSpace E)) : Set E :=
  insert 0 {w : E | ∃ u : CosmicBoundary E, cosmicDirection u ∈ S ∧
    ∃ r : ℝ, 0 < r ∧ w = r • (u : E)}

/-- The ray-space cone canonically associated with a closed-ball cosmic set. -/
def cosmicRayCone (S : Set (CosmicSpace E)) : Set (E × ℝ) :=
  raySpaceCone (cosmicOrdinaryPart S) (cosmicDirectionCone S)

@[simp]
theorem mem_cosmicOrdinaryPart {S : Set (CosmicSpace E)} {x : E} :
    x ∈ cosmicOrdinaryPart S ↔ cosmicEmbed x ∈ S := by
  rfl

theorem mem_cosmicDirections {K : Set E} {p : CosmicSpace E} :
    p ∈ cosmicDirections K ↔
      ∃ u : CosmicBoundary E, (u : E) ∈ K ∧ cosmicDirection u = p := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩

theorem mem_cosmicSet {C K : Set E} {p : CosmicSpace E} :
    p ∈ cosmicSet C K ↔
      (∃ x ∈ C, cosmicEmbed x = p) ∨
        (∃ u : CosmicBoundary E, (u : E) ∈ K ∧ cosmicDirection u = p) := by
  simp only [cosmicSet, mem_union, mem_image, mem_cosmicDirections]

@[simp]
theorem cosmicEmbed_mem_cosmicSet_iff {C K : Set E} {x : E} :
    cosmicEmbed x ∈ cosmicSet C K ↔ x ∈ C := by
  constructor
  · rw [mem_cosmicSet]
    rintro (⟨y, hy, hxy⟩ | ⟨u, hu, hxu⟩)
    · have hyx : y = x := injective_cosmicEmbed hxy
      simpa [hyx] using hy
    · exact (cosmicEmbed_ne_cosmicDirection x u hxu.symm).elim
  · intro hx
    exact (mem_cosmicSet).2 (Or.inl ⟨x, hx, rfl⟩)

@[simp]
theorem cosmicOrdinaryPart_cosmicSet (C K : Set E) :
    cosmicOrdinaryPart (cosmicSet C K) = C := by
  ext x
  exact cosmicEmbed_mem_cosmicSet_iff

theorem isCone_cosmicDirectionCone (S : Set (CosmicSpace E)) :
    IsCone (cosmicDirectionCone S) := by
  refine ⟨mem_insert 0 _, ?_⟩
  intro w hw c hc
  rcases hw with rfl | ⟨u, hu, r, hr, rfl⟩
  · left
    simp
  · right
    refine ⟨u, hu, c * r, mul_pos hc hr, ?_⟩
    simp [smul_smul]

private theorem unit_mem_of_mem_cosmicDirectionCone
    {S : Set (CosmicSpace E)} {u : CosmicBoundary E}
    (hu : (u : E) ∈ cosmicDirectionCone S) :
    cosmicDirection u ∈ S := by
  rcases hu with hu0 | ⟨v, hvS, r, hr, huv⟩
  · have : ((u : E) : E) = 0 := hu0
    have hunorm : ‖(u : E)‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
    simp [this] at hunorm
  · have hunorm : ‖(u : E)‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
    have hvnorm : ‖(v : E)‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
    have hr1 : r = 1 := by
      have hnorm := congrArg norm huv
      rw [hunorm, norm_smul, Real.norm_eq_abs, abs_of_pos hr, hvnorm, mul_one] at hnorm
      linarith
    have huv' : u = v := by
      apply Subtype.ext
      simpa [hr1] using huv
    simpa [huv'] using hvS

@[simp]
theorem cosmicDirection_mem_cosmicDirections_directionCone_iff
    {S : Set (CosmicSpace E)} {u : CosmicBoundary E} :
    cosmicDirection u ∈ cosmicDirections (cosmicDirectionCone S) ↔
      cosmicDirection u ∈ S := by
  constructor
  · rintro ⟨v, hv, huv⟩
    have hvS := unit_mem_of_mem_cosmicDirectionCone hv
    exact huv ▸ hvS
  · intro hu
    refine ⟨u, ?_, rfl⟩
    right
    exact ⟨u, hu, 1, zero_lt_one, by simp⟩

/-- Every subset of the closed-ball cosmic space is recovered from its
ordinary part and its direction cone. -/
theorem cosmicSet_parts (S : Set (CosmicSpace E)) :
    cosmicSet (cosmicOrdinaryPart S) (cosmicDirectionCone S) = S := by
  ext p
  constructor
  · rw [mem_cosmicSet]
    rintro (⟨x, hx, rfl⟩ | ⟨u, hu, rfl⟩)
    · exact hx
    · exact unit_mem_of_mem_cosmicDirectionCone hu
  · intro hp
    rcases cosmicEmbed_or_cosmicDirection p with ⟨x, rfl⟩ | ⟨u, rfl⟩
    · exact (mem_cosmicSet).2 (Or.inl ⟨x, hp, rfl⟩)
    · apply (mem_cosmicSet).2
      right
      refine ⟨u, ?_, rfl⟩
      right
      exact ⟨u, hp, 1, zero_lt_one, by simp⟩

/-- A cone is determined by its unit direction representatives. -/
theorem cosmicDirectionCone_cosmicSet {C K : Set E} (hK : IsCone K) :
    cosmicDirectionCone (cosmicSet C K) = K := by
  ext w
  constructor
  · intro hw
    rcases hw with rfl | ⟨u, huS, r, hr, rfl⟩
    · exact hK.1
    · have huK : (u : E) ∈ K := by
        rw [mem_cosmicSet] at huS
        rcases huS with ⟨x, hx, hxu⟩ | ⟨v, hvK, hvu⟩
        · exact (cosmicEmbed_ne_cosmicDirection x u hxu).elim
        · have huv : u = v := injective_cosmicDirection hvu.symm
          simpa [huv] using hvK
      exact hK.2 huK hr
  · intro hwK
    by_cases hw0 : w = 0
    · subst w
      exact mem_insert 0 _
    · right
      let u : CosmicBoundary E := cosmicDirectionOf w hw0
      have huK : (u : E) ∈ K := by
        change NormedSpace.normalize w ∈ K
        exact hK.smul_mem hwK (inv_nonneg.mpr (norm_nonneg w))
      have huS : cosmicDirection u ∈ cosmicSet C K :=
        (mem_cosmicSet).2 (Or.inr ⟨u, huK, rfl⟩)
      refine ⟨u, huS, ‖w‖, norm_pos_iff.mpr hw0, ?_⟩
      exact (NormedSpace.norm_smul_normalize w).symm

@[simp]
theorem cosmicRayCone_cosmicSet {C K : Set E} (hK : IsCone K) :
    cosmicRayCone (cosmicSet C K) = raySpaceCone C K := by
  rw [cosmicRayCone, cosmicOrdinaryPart_cosmicSet,
    cosmicDirectionCone_cosmicSet hK]

theorem cosmicSet_mono {C D K L : Set E} (hCD : C ⊆ D) (hKL : K ⊆ L) :
    cosmicSet C K ⊆ cosmicSet D L := by
  intro p hp
  rw [mem_cosmicSet] at hp ⊢
  rcases hp with ⟨x, hx, hxp⟩ | ⟨u, hu, hup⟩
  · exact Or.inl ⟨x, hCD hx, hxp⟩
  · exact Or.inr ⟨u, hKL hu, hup⟩

theorem cosmicOrdinaryPart_mono {S T : Set (CosmicSpace E)} (hST : S ⊆ T) :
    cosmicOrdinaryPart S ⊆ cosmicOrdinaryPart T := by
  intro x hx
  exact hST hx

theorem cosmicDirectionCone_mono {S T : Set (CosmicSpace E)} (hST : S ⊆ T) :
    cosmicDirectionCone S ⊆ cosmicDirectionCone T := by
  intro w hw
  rcases hw with rfl | ⟨u, hu, r, hr, rfl⟩
  · exact mem_insert 0 _
  · exact Or.inr ⟨u, hST hu, r, hr, rfl⟩

theorem cosmicSet_subset_iff {C D K L : Set E} (hK : IsCone K) (hL : IsCone L) :
    cosmicSet C K ⊆ cosmicSet D L ↔ C ⊆ D ∧ K ⊆ L := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro x hx
      exact (cosmicEmbed_mem_cosmicSet_iff).1
        (h ((cosmicEmbed_mem_cosmicSet_iff).2 hx))
    · intro w hw
      have hw' : w ∈ cosmicDirectionCone (cosmicSet C K) := by
        rw [cosmicDirectionCone_cosmicSet hK]
        exact hw
      have hdirMono :
          cosmicDirectionCone (cosmicSet C K) ⊆
            cosmicDirectionCone (cosmicSet D L) := by
        intro z hz
        rcases hz with rfl | ⟨u, hu, r, hr, rfl⟩
        · exact mem_insert 0 _
        · exact Or.inr ⟨u, h hu, r, hr, rfl⟩
      rw [cosmicDirectionCone_cosmicSet hL] at hdirMono
      exact hdirMono hw'
  · rintro ⟨hCD, hKL⟩
    exact cosmicSet_mono hCD hKL

theorem cosmicSet_injective {C D K L : Set E} (hK : IsCone K) (hL : IsCone L) :
    cosmicSet C K = cosmicSet D L ↔ C = D ∧ K = L := by
  constructor
  · intro h
    have hsub := (cosmicSet_subset_iff hK hL).1 h.le
    have hsub' := (cosmicSet_subset_iff hL hK).1 h.ge
    exact ⟨Set.Subset.antisymm hsub.1 hsub'.1,
      Set.Subset.antisymm hsub.2 hsub'.2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp]
theorem cosmicDirections_zero : cosmicDirections ({0} : Set E) = ∅ := by
  ext p
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hu0 : (u : E) = 0 := by simpa using hu
    have hunorm : ‖(u : E)‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
    simp [hu0] at hunorm
  · simp

@[simp]
theorem cosmicSet_empty_zero : cosmicSet (∅ : Set E) ({0} : Set E) = ∅ := by
  simp [cosmicSet]

@[simp]
theorem cosmicSet_singleton_zero (x : E) :
    cosmicSet ({x} : Set E) ({0} : Set E) = {cosmicEmbed x} := by
  simp [cosmicSet]

@[simp]
theorem cosmicSet_univ_univ :
    cosmicSet (Set.univ : Set E) (Set.univ : Set E) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  rcases cosmicEmbed_or_cosmicDirection p with ⟨x, rfl⟩ | ⟨u, rfl⟩
  · exact (mem_cosmicSet).2 (Or.inl ⟨x, Set.mem_univ x, rfl⟩)
  · exact (mem_cosmicSet).2 (Or.inr ⟨u, Set.mem_univ (u : E), rfl⟩)

end CosmicSets

end RW
