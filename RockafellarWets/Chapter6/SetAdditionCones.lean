/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Tangents and normals under set addition

Exercise 6.44, with a necessary correction to its first inclusion. Ordinary
tangent directions in different factors need not admit common scales. For
example, the two closed sets in the plane consisting of zero and the points
`(2⁻ⁿ, 0)` and `(0, 2⁻ⁿ)`, respectively, have the positive coordinate rays as
tangent cones at zero. Their tangent sum contains `(1, 3)`, but the sum of the
sets does not have this tangent: all its points with positive coordinates
have coordinate ratio an integral power of two, which cannot approach three.
The proof guide's use of 6.41 therefore requires geometric derivability for
this first formula. We state that assumption explicitly. All other printed
clauses retain their hypotheses. The index type may be empty.
-/

import RockafellarWets.Chapter6.ImageSetCones
import RockafellarWets.Chapter6.FiniteProductCones
import RockafellarWets.Chapter3.FiniteConeSetOperations

open Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

noncomputable section

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Addition of the coordinates of a finite Euclidean product. -/
def l2PiSum : PiLp 2 (fun _ : ι ↦ E) →L[ℝ] E :=
  ∑ i, PiLp.proj 2 (fun _ : ι ↦ E) i

omit [FiniteDimensional ℝ E] in
@[simp]
theorem l2PiSum_apply (x : PiLp 2 (fun _ : ι ↦ E)) :
    l2PiSum x = ∑ i, x i := by
  simp [l2PiSum]

/-- The adjoint of addition repeats a vector in each coordinate. -/
theorem l2PiSum_adjoint_apply (v : E) :
    (l2PiSum (ι := ι) (E := E)).adjoint v = WithLp.toLp 2 (fun _ ↦ v) := by
  apply ext_inner_right ℝ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_left, l2PiSum_apply, l2Pi_inner_apply]
  simp [inner_sum]

omit [FiniteDimensional ℝ E] in
/-- The existing finite set sum is the image of its Euclidean product under addition. -/
theorem finiteSetSum_eq_l2PiSum_image (C : ι → Set E) :
    finiteSetSum C = l2PiSum '' l2PiSet C := by
  ext z
  constructor
  · rintro ⟨x, hx, hsum⟩
    exact ⟨WithLp.toLp 2 x, hx, by simpa using hsum⟩
  · rintro ⟨x, hx, hsum⟩
    exact ⟨WithLp.ofLp x, hx, by simpa using hsum⟩

omit [FiniteDimensional ℝ E] in
/-- Geometric derivability supplies the common scales missing from the
unrestricted ordinary tangent product formula. -/
theorem tangentCone_l2PiSet_of_isGeometricallyDerivable
    {C : ι → Set E} {x : PiLp 2 (fun _ : ι ↦ E)} (hx : x ∈ l2PiSet C)
    (hd : ∀ i, IsGeometricallyDerivable (C i) (x i)) :
    tangentCone (l2PiSet C) x = l2PiSet (fun i ↦ tangentCone (C i) (x i)) := by
  refine Subset.antisymm (tangentCone_l2PiSet_subset C x) ?_
  intro w hw
  apply derivableCone_subset_tangentCone hx
  rw [derivableCone_l2PiSet]
  exact fun i ↦ hd i (hw i)

omit [FiniteDimensional ℝ E] in
/-- **Exercise 6.44**, corrected first clause at each decomposition. Geometric
derivability synchronizes the tangent witnesses in the finitely many factors. -/
theorem finiteSetSum_tangentCone_subset_of_isGeometricallyDerivable
    {C : ι → Set E} {x : PiLp 2 (fun _ : ι ↦ E)} (hx : x ∈ l2PiSet C)
    (hd : ∀ i, IsGeometricallyDerivable (C i) (x i)) :
    finiteSetSum (fun i ↦ tangentCone (C i) (x i)) ⊆
      tangentCone (finiteSetSum C) (∑ i, x i) := by
  rw [finiteSetSum_eq_l2PiSum_image, ← tangentCone_l2PiSet_of_isGeometricallyDerivable hx hd,
    finiteSetSum_eq_l2PiSum_image, ← l2PiSum_apply]
  exact image_tangentCone_subset l2PiSum.hasFDerivAt _

omit [FiniteDimensional ℝ E] in
/-- **Exercise 6.44**, the corrected union formula over all decompositions. -/
theorem iUnion_finiteSetSum_tangentCone_subset_of_isGeometricallyDerivable
    {C : ι → Set E} {z : E}
    (hd : ∀ x ∈ l2PiSet C ∩ l2PiSum ⁻¹' {z},
      ∀ i, IsGeometricallyDerivable (C i) (x i)) :
    (⋃ x ∈ l2PiSet C ∩ l2PiSum ⁻¹' {z},
      finiteSetSum (fun i ↦ tangentCone (C i) (x i))) ⊆
        tangentCone (finiteSetSum C) z := by
  intro w hw
  obtain ⟨x, hx, hw⟩ := mem_iUnion₂.1 hw
  have hsum : ∑ i, x i = z := by
    have h := hx.2
    rwa [mem_preimage, mem_singleton_iff, l2PiSum_apply] at h
  simpa only [hsum] using
    finiteSetSum_tangentCone_subset_of_isGeometricallyDerivable hx.1 (hd x hx) hw

/-- **Exercise 6.44**, first normal inclusion over all decompositions. -/
theorem regularNormalCone_finiteSetSum_subset_iInter (C : ι → Set E) (z : E) :
    regularNormalCone (finiteSetSum C) z ⊆
      ⋂ x ∈ l2PiSet C ∩ l2PiSum ⁻¹' {z}, ⋂ i, regularNormalCone (C i) (x i) := by
  intro v hv
  rw [finiteSetSum_eq_l2PiSum_image] at hv
  have h := regularNormalCone_image_subset_iInter l2PiSum.differentiable z hv
  apply mem_iInter₂.2
  intro x hx
  have hvx := mem_iInter₂.1 h x hx
  have hvx' : l2PiSum.adjoint v ∈ regularNormalCone (l2PiSet C) x := by
    simpa only [ContinuousLinearMap.fderiv] using hvx
  rw [regularNormalCone_l2PiSet, l2PiSum_adjoint_apply] at hvx'
  exact mem_iInter.2 hvx'

omit [FiniteDimensional ℝ E] in
/-- Smoothness of summation, with the field and order fixed in advance: the
dot-notation form leaves both to unification, which is very slow here. -/
theorem l2PiSum_contDiff : ContDiff ℝ 1 (⇑(l2PiSum (ι := ι) (E := E))) :=
  ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := 1) _

/-- **Exercise 6.44**, limiting normals under local boundedness of the
set of decompositions. -/
theorem normalCone_finiteSetSum_subset_iUnion {C : ι → Set E} {z : E}
    (hC : ∀ i, IsClosed (C i))
    (hb : ∃ V ∈ 𝓝 z, Bornology.IsBounded (l2PiSet C ∩ l2PiSum ⁻¹' V)) :
    normalCone (finiteSetSum C) z ⊆
      ⋃ x ∈ l2PiSet C ∩ l2PiSum ⁻¹' {z}, ⋂ i, normalCone (C i) (x i) := by
  intro v hv
  rw [finiteSetSum_eq_l2PiSum_image] at hv
  obtain ⟨x, hx, hvx⟩ := mem_iUnion₂.1
    (normalCone_image_subset_iUnion (isClosed_l2PiSet hC) l2PiSum_contDiff hb hv)
  have hvx' : l2PiSum.adjoint v ∈ normalCone (l2PiSet C) x := by
    simpa only [ContinuousLinearMap.fderiv] using hvx
  rw [normalCone_l2PiSet, l2PiSum_adjoint_apply] at hvx'
  exact mem_iUnion₂.2 ⟨x, hx, mem_iInter.2 hvx'⟩

/-- **Exercise 6.44**, regular tangents under local boundedness of the
set of decompositions. -/
theorem iInter_finiteSetSum_regularTangentCone_subset {C : ι → Set E} {z : E}
    (hC : ∀ i, IsClosed (C i)) (hz : z ∈ finiteSetSum C)
    (hb : ∃ V ∈ 𝓝 z, Bornology.IsBounded (l2PiSet C ∩ l2PiSum ⁻¹' V)) :
    (⋂ x ∈ l2PiSet C ∩ l2PiSum ⁻¹' {z},
      finiteSetSum (fun i ↦ regularTangentCone (C i) (x i))) ⊆
        regularTangentCone (finiteSetSum C) z := by
  rw [finiteSetSum_eq_l2PiSum_image] at hz ⊢
  intro w hw
  apply iInter_image_regularTangentCone_subset (isClosed_l2PiSet hC)
    l2PiSum_contDiff hz hb
  apply mem_iInter₂.2
  intro x hx
  have hxw := mem_iInter₂.1 hw x hx
  rw [finiteSetSum_eq_l2PiSum_image, ← regularTangentCone_l2PiSet hx.1] at hxw
  simpa only [ContinuousLinearMap.fderiv] using hxw

omit [FiniteDimensional ℝ E] in
/-- Finite Euclidean products preserve convexity. -/
theorem convex_l2PiSet {C : ι → Set E} (hC : ∀ i, Convex ℝ (C i)) :
    Convex ℝ (l2PiSet C) := by
  intro x hx y hy a b ha hb hab i
  exact hC i (hx i) (hy i) ha hb hab

omit [FiniteDimensional ℝ E] in
/-- **Exercise 6.44**, the tangent formula for convex factors, at every
choice of decomposition. Closure is necessary even for closed factors. -/
theorem tangentCone_finiteSetSum_of_convex {C : ι → Set E}
    (hC : ∀ i, Convex ℝ (C i)) {x : PiLp 2 (fun _ : ι ↦ E)}
    (hx : x ∈ l2PiSet C) :
    tangentCone (finiteSetSum C) (∑ i, x i) =
      closure (finiteSetSum (fun i ↦ tangentCone (C i) (x i))) := by
  rw [finiteSetSum_eq_l2PiSum_image, ← l2PiSum_apply,
    tangentCone_linear_image_of_convex l2PiSum (convex_l2PiSet hC) hx,
    tangentCone_l2PiSet_of_isGeometricallyDerivable hx
      (fun i ↦ isGeometricallyDerivable_of_convex (hC i) (hx i)),
    finiteSetSum_eq_l2PiSum_image]

/-- **Exercise 6.44**, the normal formula for convex factors, at every
choice of decomposition. -/
theorem normalCone_finiteSetSum_of_convex {C : ι → Set E}
    (hC : ∀ i, Convex ℝ (C i)) {x : PiLp 2 (fun _ : ι ↦ E)}
    (hx : x ∈ l2PiSet C) :
    normalCone (finiteSetSum C) (∑ i, x i) = ⋂ i, normalCone (C i) (x i) := by
  rw [finiteSetSum_eq_l2PiSum_image, ← l2PiSum_apply,
    normalCone_linear_image_of_convex l2PiSum (convex_l2PiSet hC) hx,
    normalCone_l2PiSet]
  ext v
  simp only [mem_preimage, l2PiSum_adjoint_apply, mem_l2PiSet, mem_iInter]

end

end RW
