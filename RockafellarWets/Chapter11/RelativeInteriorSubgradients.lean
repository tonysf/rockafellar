/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Convex subgradients on the relative interior

Restriction to the direction space of the affine hull turns relative
interior into ordinary interior. A supporting vector there is also an
ambient supporting vector, because every finite point lies in that hull.
-/

import RockafellarWets.Chapter11.EssentialStrictConvexity
import RockafellarWets.Chapter10.PLQCalculus
import Mathlib.Analysis.Convex.Intrinsic

open Set Filter Topology
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Proper convex functions admit subgradients throughout the relative
interior of their effective domain, including lower-dimensional domains. -/
theorem subdifferential_nonempty_of_convex_intrinsicInterior {f : E → EReal}
    (hp : IsProper f) (hc : Convex ℝ (epigraph f)) {x : E}
    (hx : x ∈ intrinsicInterior ℝ (effectiveDomain f)) :
    (subdifferential f x).Nonempty := by
  let S := affineSpan ℝ (effectiveDomain f)
  let V := S.direction
  have hxD : x ∈ effectiveDomain f := intrinsicInterior_subset hx
  have hxS : x ∈ S := subset_affineSpan ℝ _ hxD
  have hxval : f x = ((f x).toReal:EReal) := (EReal.coe_toReal hxD.ne (hp.2 x).ne').symm
  let g : V → EReal := fun v ↦ f ((v:E)+x)
  have hg0 : g 0 = ((f x).toReal:EReal) := by simpa only [g,Submodule.coe_zero,zero_add] using hxval
  have hgp : IsProper g := ⟨⟨0,hg0.trans_lt (EReal.coe_lt_top _)⟩,fun v ↦ hp.2 _⟩
  have hgc : Convex ℝ (epigraph g) := convex_epigraph_compAffine hc V.subtypeL x
  have hint : (0:V) ∈ interior (effectiveDomain g) := by
    obtain ⟨p,hpint,hpx⟩ := mem_intrinsicInterior.mp hx
    let φ : V → S := fun v ↦ ⟨(v:E)+x,by
      simpa only [vadd_eq_add] using AffineSubspace.vadd_mem_of_mem_direction v.property hxS⟩
    have hφ : Continuous φ := (continuous_subtype_val.add continuous_const).subtype_mk _
    have hφ0 : φ 0 = p := Subtype.ext (by simpa [φ] using hpx.symm)
    apply mem_interior_iff_mem_nhds.mpr
    have ht : Tendsto φ (𝓝 0) (𝓝 p) := by rw [← hφ0]; exact hφ.continuousAt
    exact ht (mem_interior_iff_mem_nhds.mp hpint)
  obtain ⟨v,hv⟩ := subdifferential_nonempty_of_convex_interior hgc hgp hint
  refine ⟨(v:E),(mem_subdifferential_iff_of_convex hc hp hxval).mpr ?_⟩
  intro y
  by_cases hyt : f y = ⊤
  · rw [hyt]; exact le_top
  have hyD : y ∈ effectiveDomain f := lt_top_iff_ne_top.mpr hyt
  have hdir : y-x ∈ V := AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ _ hyD) hxS
  let w : V := ⟨y-x,hdir⟩
  have hh := (mem_subdifferential_iff_of_convex hgc hgp hg0).mp hv w
  simpa only [sub_zero,g,w,sub_add_cancel] using hh

/-- Relative interiors of finite-dimensional convex sets are convex. -/
theorem convex_intrinsicInterior {C : Set E} (hC : Convex ℝ C) :
    Convex ℝ (intrinsicInterior ℝ C) := by
  rcases C.eq_empty_or_nonempty with rfl | ⟨p,hp⟩
  · rw [intrinsicInterior_empty]; exact convex_empty
  let p' : affineSpan ℝ C := ⟨p,subset_affineSpan ℝ C hp⟩
  letI : Nonempty (affineSpan ℝ C) := ⟨p'⟩
  let e := (AffineIsometryEquiv.constVSub ℝ p').symm
  let A := (affineSpan ℝ C).subtype.comp e.toAffineEquiv.toAffineMap
  have he : intrinsicInterior ℝ C = A '' interior (A ⁻¹' C) := by
    change (Subtype.val : affineSpan ℝ C → E) '' interior ((Subtype.val : affineSpan ℝ C → E) ⁻¹' C) =
      (Subtype.val ∘ e.toHomeomorph) '' interior (e.toHomeomorph ⁻¹' ((Subtype.val : affineSpan ℝ C → E) ⁻¹' C))
    rw [← e.toHomeomorph.preimage_interior,Set.image_comp,e.toHomeomorph.image_preimage]
  rw [he]
  exact ((hC.affine_preimage A).interior).affine_image A

/-- The explicit relative-interior conclusion in **11.13(b)**. -/
theorem IsAlmostStrictlyConvex.strictConvexOn_intrinsicInterior {f : E → EReal}
    (hs : IsAlmostStrictlyConvex f) (hp : IsProper f) (hc : Convex ℝ (epigraph f)) :
    StrictConvexOn ℝ (intrinsicInterior ℝ (effectiveDomain f)) (fun x ↦ (f x).toReal) := by
  apply hs _ (convex_intrinsicInterior (convex_effectiveDomain_of_convex_epigraph hc))
  intro x hx
  exact subdifferential_nonempty_of_convex_intrinsicInterior hp hc hx

/-- **11.13**, almost differentiability gives continuous differentiability
on the open convex interior of the domain. -/
theorem IsAlmostDifferentiable.contDiffOn_interior {f : E → EReal}
    (hs : IsAlmostDifferentiable f) (hp : IsProper f) (hl : LowerSemicontinuous f)
    (hc : Convex ℝ (epigraph f)) :
    ContDiffOn ℝ 1 (fun x ↦ (f x).toReal) (interior (effectiveDomain f)) := by
  have hsingle := (isAlmostDifferentiable_iff_subdifferential_subsingleton hp hl hc).mp hs
  have hfin : ∀ x ∈ interior (effectiveDomain f), f x ≠ ⊥ ∧ f x ≠ ⊤ :=
    fun x hx ↦ ⟨(hp.2 x).ne',(interior_subset hx).ne⟩
  apply ((tfae_contDiffOn isOpen_interior hfin).out 0 1).mp
  intro x hx
  obtain ⟨v,hv⟩ := subdifferential_nonempty_of_convex_interior hc hp hx
  exact ⟨v,(subdifferential_eq_singleton_iff_hasStrictGradientAt_of_convex hp hl hc).mp
    ((hsingle x).eq_singleton_of_mem hv)⟩

end RW
