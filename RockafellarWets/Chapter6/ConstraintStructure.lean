/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Sets with Constraint Structure

The elementary halves of Theorems 6.14, 6.31 and 6.42, for the constraint set
`C = {x ∈ X | F(x) ∈ D}` and for finite intersections.

These are the inclusions the book calls elementary, and they hold with no
constraint qualification and no closedness:

* regular normals *add* into a constraint system, `6.14` first display;
* tangent vectors *restrict*, `6.31` first display;
* the same two statements for a finite intersection, `6.42` first display.

Each rests on one fact of its own.  Regular normals add across an
intersection because the `ε` inequality of 6(5) splits as `ε/2 + ε/2`; the
normal contribution of the smooth constraint is
`adjoint_image_regularNormalCone_subset_preimage`, the one-way chain rule of
the regular-normal change of coordinates; and the tangent restriction is
monotonicity of the tangent cone together with the push-forward
`image_tangentCone_subset`.  The book's `Σ yᵢ ∇fᵢ(x̄)` is `∇F(x̄)* y` by
formula 6(9), so the adjoint form is the printed one.
-/

import RockafellarWets.Chapter6.ElementaryCones
import RockafellarWets.Chapter6.RegularNormalChangeOfCoordinates

open Filter Metric Set Topology
open scoped InnerProductSpace Pointwise

namespace RW

section RegularNormalIntersection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Regular normals add across an intersection: the `ε` inequality of 6(5) for
the sum is the two `ε/2` inequalities of the summands, both of which hold
along the smaller filter `𝓝[A ∩ B] x̄`. -/
theorem add_mem_regularNormalCone_inter {A B : Set E} {x v w : E}
    (hv : v ∈ regularNormalCone A x) (hw : w ∈ regularNormalCone B x) :
    v + w ∈ regularNormalCone (A ∩ B) x := by
  refine ⟨⟨hv.1, hw.1⟩, fun ε hε ↦ ?_⟩
  have hA : ∀ᶠ y in 𝓝[A ∩ B] x, ⟪v, y - x⟫_ℝ ≤ ε / 2 * ‖y - x‖ :=
    (hv.2 (ε / 2) (by linarith)).filter_mono (nhdsWithin_mono x inter_subset_left)
  have hB : ∀ᶠ y in 𝓝[A ∩ B] x, ⟪w, y - x⟫_ℝ ≤ ε / 2 * ‖y - x‖ :=
    (hw.2 (ε / 2) (by linarith)).filter_mono (nhdsWithin_mono x inter_subset_right)
  filter_upwards [hA, hB] with y hy1 hy2
  rw [inner_add_left]
  linarith

/-- The set form of the previous lemma. -/
theorem regularNormalCone_add_subset_inter (A B : Set E) (x : E) :
    regularNormalCone A x + regularNormalCone B x ⊆ regularNormalCone (A ∩ B) x := by
  rintro _ ⟨v, hv, w, hw, rfl⟩
  exact add_mem_regularNormalCone_inter hv hw

/-- **Theorem 6.42**, the regular-normal inclusion for a finite intersection.
The empty intersection is the whole space, where the regular normal cone is
the zero cone, so no membership hypothesis on `x̄` is needed. -/
theorem sum_mem_regularNormalCone_biInter {ι : Type*} {C : ι → Set E}
    {x : E} {v : ι → E} (s : Finset ι)
    (hv : ∀ i ∈ s, v i ∈ regularNormalCone (C i) x) :
    ∑ i ∈ s, v i ∈ regularNormalCone (⋂ i ∈ (s : Set ι), C i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [regularNormalCone_univ]
  | insert a s ha ih =>
      have hmem : ∀ i ∈ s, v i ∈ regularNormalCone (C i) x := fun i hi ↦
        hv i (Finset.mem_insert_of_mem hi)
      have hsum := add_mem_regularNormalCone_inter
        (hv a (Finset.mem_insert_self a s)) (ih hmem)
      rw [Finset.sum_insert ha, Finset.coe_insert, biInter_insert]
      exact hsum

/-- **Theorem 6.42**, the tangent inclusion for a finite intersection: the
tangent cone is monotone, so a tangent vector to the intersection is tangent
to each piece. -/
theorem tangentCone_biInter_subset {ι : Type*} (C : ι → Set E) (S : Set ι) (x : E) :
    tangentCone (⋂ i ∈ S, C i) x ⊆ ⋂ i ∈ S, tangentCone (C i) x :=
  subset_iInter₂ fun _ hi ↦ tangentCone_mono (biInter_subset_of_mem hi) x

/-- **Theorem 6.42** for two sets: tangent vectors restrict. -/
theorem tangentCone_inter_subset (A B : Set E) (x : E) :
    tangentCone (A ∩ B) x ⊆ tangentCone A x ∩ tangentCone B x :=
  subset_inter (tangentCone_mono inter_subset_left x)
    (tangentCone_mono inter_subset_right x)

end RegularNormalIntersection

section ConstraintSetDefs

variable {E F : Type*}

/-- The constraint set `C = {x ∈ X | F(x) ∈ D}` of Theorems 6.14 and 6.31. -/
def constrainedPreimage (X : Set E) (G : E → F) (D : Set F) : Set E := X ∩ G ⁻¹' D

@[simp]
theorem mem_constrainedPreimage {X : Set E} {G : E → F} {D : Set F} {x : E} :
    x ∈ constrainedPreimage X G D ↔ x ∈ X ∧ G x ∈ D := Iff.rfl

theorem constrainedPreimage_subset_left (X : Set E) (G : E → F) (D : Set F) :
    constrainedPreimage X G D ⊆ X := inter_subset_left

theorem image_constrainedPreimage_subset (X : Set E) (G : E → F) (D : Set F) :
    G '' constrainedPreimage X G D ⊆ D := by
  rintro _ ⟨z, hz, rfl⟩
  exact hz.2

end ConstraintSetDefs

section ConstraintSet

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Theorem 6.31**, the elementary inclusion.  A tangent vector to the
constraint set is tangent to `X`, by monotonicity, and its image under
`∇F(x̄)` is tangent to `D`, by the push-forward of tangent vectors through a
differentiable map. -/
theorem tangentCone_constrainedPreimage_subset {X : Set E} {G : E → F} {G' : E →L[ℝ] F}
    {D : Set F} {x : E} (hG : HasFDerivAt G G' x) :
    tangentCone (constrainedPreimage X G D) x
      ⊆ {w : E | w ∈ tangentCone X x ∧ G' w ∈ tangentCone D (G x)} := by
  intro w hw
  refine ⟨tangentCone_mono (constrainedPreimage_subset_left X G D) x hw, ?_⟩
  refine tangentCone_mono (image_constrainedPreimage_subset X G D) (G x) ?_
  exact image_tangentCone_subset hG _ ⟨w, hw, rfl⟩

end ConstraintSet

section ConstraintNormals

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- **Theorem 6.14**, the inclusion for regular normals.  The book's
`Σ yᵢ ∇fᵢ(x̄) + z` is `∇F(x̄)* y + z` by formula 6(9): the first summand is a
regular normal to `F⁻¹(D)` by the one-way chain rule, the second is a regular
normal to `X` by hypothesis, and regular normals add across the
intersection. -/
theorem adjoint_add_mem_regularNormalCone_constrainedPreimage {X : Set E} {G : E → F}
    {G' : E →L[ℝ] F} {D : Set F} {x : E} (hG : HasFDerivAt G G' x)
    {y : F} (hy : y ∈ regularNormalCone D (G x))
    {z : E} (hz : z ∈ regularNormalCone X x) :
    ContinuousLinearMap.adjoint G' y + z
      ∈ regularNormalCone (constrainedPreimage X G D) x := by
  have h1 : ContinuousLinearMap.adjoint G' y ∈ regularNormalCone (G ⁻¹' D) x :=
    adjoint_image_regularNormalCone_subset_preimage hG D ⟨y, hy, rfl⟩
  have h2 := add_mem_regularNormalCone_inter h1 hz
  rwa [inter_comm] at h2

/-- The set form of **Theorem 6.14**'s first display. -/
theorem adjoint_image_add_regularNormalCone_subset {X : Set E} {G : E → F}
    {G' : E →L[ℝ] F} {D : Set F} {x : E} (hG : HasFDerivAt G G' x) :
    ContinuousLinearMap.adjoint G' '' regularNormalCone D (G x)
        + regularNormalCone X x
      ⊆ regularNormalCone (constrainedPreimage X G D) x := by
  rintro _ ⟨_, ⟨y, hy, rfl⟩, z, hz, rfl⟩
  exact adjoint_add_mem_regularNormalCone_constrainedPreimage hG hy hz

end ConstraintNormals

end RW
