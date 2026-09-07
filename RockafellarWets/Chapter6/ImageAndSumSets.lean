/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Image Sets and Sums of Sets

The elementary displays of Theorem 6.43 and Exercise 6.44, for an image
`D = F(C)` and for a sum `C = C₁ + ⋯ + Cₘ`.

Both rest on the same two one-way rules already available: tangent vectors
push forward through a differentiable map, and regular normals pull back
through its adjoint.  What makes them apply to an *image* rather than a
preimage is that `C ⊆ F⁻¹(F(C))`, together with the antitonicity of the
regular normal cone in the set.  The sum displays need nothing analytic at
all: translating one summand by a fixed point of the other embeds a
neighbourhood of that summand into the sum, with the difference vectors
unchanged.
-/

import RockafellarWets.Chapter6.ConstraintStructure

open Filter Metric Set Topology
open scoped InnerProductSpace Pointwise

namespace RW

section Antitone

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The regular normal cone is antitone in the set: a larger set constrains
the `ε` inequality of 6(5) at more points. -/
theorem regularNormalCone_antitone {A B : Set E} (h : A ⊆ B) {x : E} (hx : x ∈ A) :
    regularNormalCone B x ⊆ regularNormalCone A x := by
  rintro v ⟨-, hv⟩
  exact ⟨hx, fun ε hε ↦ (hv ε hε).filter_mono (nhdsWithin_mono x h)⟩

end Antitone

section ImageSets

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Theorem 6.43**, the tangent display: every `∇F(x̄)w` with `w` tangent to
`C` at a preimage `x̄` of `ū` is tangent to `F(C)` at `ū`. -/
theorem iUnion_image_tangentCone_subset {C : Set E} {G : E → F} {G' : E → E →L[ℝ] F}
    (hG : ∀ x ∈ C, HasFDerivAt G (G' x) x) (u : F) :
    ⋃ x ∈ C ∩ G ⁻¹' {u}, (G' x) '' tangentCone C x ⊆ tangentCone (G '' C) u := by
  refine iUnion₂_subset fun x hx ↦ ?_
  have hu : G x = u := hx.2
  have h := image_tangentCone_subset (hG x hx.1) C
  rwa [hu] at h

/-- **Theorem 6.43**, the regular-normal display: a regular normal to `F(C)` at
`ū` pulls back through every adjoint `∇F(x̄)*` at a preimage `x̄` of `ū`. -/
theorem regularNormalCone_image_subset_iInter {C : Set E} {G : E → F}
    {G' : E → E →L[ℝ] F} (hG : ∀ x ∈ C, HasFDerivAt G (G' x) x) (u : F) :
    regularNormalCone (G '' C) u
      ⊆ ⋂ x ∈ C ∩ G ⁻¹' {u},
          {y : F | ContinuousLinearMap.adjoint (G' x) y ∈ regularNormalCone C x} := by
  refine subset_iInter₂ fun x hx ↦ fun y hy ↦ ?_
  have hu : G x = u := hx.2
  have h1 : ContinuousLinearMap.adjoint (G' x) y
      ∈ regularNormalCone (G ⁻¹' (G '' C)) x := by
    refine adjoint_image_regularNormalCone_subset_preimage (hG x hx.1) (G '' C)
      ⟨y, ?_, rfl⟩
    rwa [hu]
  exact regularNormalCone_antitone (subset_preimage_image G C) hx.1 h1

end ImageSets

section SumSets

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Exercise 6.44**, the regular-normal display for two summands.  Testing
the `ε` inequality on `A + B` along the translate `y + b` of `A` gives exactly
the inequality for `A` at `a`, the difference vectors being equal. -/
theorem regularNormalCone_add_subset_left {A B : Set E} {a b : E} (ha : a ∈ A)
    (hb : b ∈ B) : regularNormalCone (A + B) (a + b) ⊆ regularNormalCone A a := by
  intro v hv
  rw [mem_regularNormalCone_iff] at hv ⊢
  refine ⟨ha, fun ε hε ↦ ?_⟩
  obtain ⟨δ, hδ, hbound⟩ := hv.2 ε hε
  refine ⟨δ, hδ, fun y hy hyδ ↦ ?_⟩
  have heq : y + b - (a + b) = y - a := by abel
  have h := hbound (y + b) ⟨y, hy, b, hb, rfl⟩ (by rw [heq]; exact hyδ)
  rwa [heq] at h

theorem regularNormalCone_add_subset_right {A B : Set E} {a b : E} (ha : a ∈ A)
    (hb : b ∈ B) : regularNormalCone (A + B) (a + b) ⊆ regularNormalCone B b := by
  have h := regularNormalCone_add_subset_left hb ha
  rwa [add_comm B A, add_comm b a] at h

omit [InnerProductSpace ℝ E] in
/-- A sum of points, one from each summand, lies in the sum of the sets. -/
theorem sum_mem_finset_sum {ι : Type*} {C : ι → Set E} {x : ι → E} (s : Finset ι)
    (hx : ∀ i ∈ s, x i ∈ C i) : ∑ i ∈ s, x i ∈ ∑ i ∈ s, C i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact Set.add_mem_add (hx a (Finset.mem_insert_self a s))
        (ih fun i hi ↦ hx i (Finset.mem_insert_of_mem hi))

/-- **Exercise 6.44**, the regular-normal display for finitely many summands. -/
theorem regularNormalCone_finset_sum_subset {ι : Type*} {C : ι → Set E} {x : ι → E}
    {s : Finset ι} (hx : ∀ i ∈ s, x i ∈ C i) {i : ι} (hi : i ∈ s) :
    regularNormalCone (∑ j ∈ s, C j) (∑ j ∈ s, x j) ⊆ regularNormalCone (C i) (x i) := by
  classical
  have hCs : ∑ j ∈ s, C j = C i + ∑ j ∈ s.erase i, C j :=
    (Finset.add_sum_erase _ _ hi).symm
  have hxs : ∑ j ∈ s, x j = x i + ∑ j ∈ s.erase i, x j :=
    (Finset.add_sum_erase _ _ hi).symm
  rw [hCs, hxs]
  exact regularNormalCone_add_subset_left (hx i hi)
    (sum_mem_finset_sum _ fun j hj ↦ hx j (Finset.mem_of_mem_erase hj))

end SumSets

end RW
