/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Interior directions of a convex radial derivative
-/

import RockafellarWets.Chapter7.ConvexEpiConvergence
import RockafellarWets.Chapter8.ConvexSubderivatives

open Filter Function Set Topology

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The epigraph interior of a convex function is precisely the strict
epigraph above the interior of its effective domain, also for improper functions. -/
theorem mem_interior_epigraph_iff_of_convex {f : E → EReal} (hf : Convex ℝ (epigraph f))
    {x : E} {a : ℝ} : (x,a) ∈ interior (epigraph f) ↔ x ∈ interior (effectiveDomain f) ∧ f x < (a : EReal) := by
  constructor
  · intro h
    have hd := isOpenMap_fst.image_interior_subset (epigraph f) (show x ∈ Prod.fst '' interior (epigraph f) from
      ⟨(x,a), h, rfl⟩)
    rw [epigraph_proj_eq_effectiveDomain] at hd
    exact ⟨hd, (show f x ≤ (a : EReal) from interior_subset (s := epigraph f) h).lt_of_ne
      (fun he ↦ graphPoint_not_mem_interior_epigraph he.symm h)⟩
  · exact fun ⟨h, ht⟩ ↦ mem_interior_epigraph_of_mem_interior_effectiveDomain hf h ht

/-- Convex functions agree with their lower closures in the interior of
their effective domains, including where their value is minus infinity. -/
theorem epiClosure_eq_of_mem_interior_convex {f : E → EReal} (hf : Convex ℝ (epigraph f))
    {x : E} (hx : x ∈ interior (effectiveDomain f)) : epiClosure f x = f x := by
  have hsub : epigraph f ⊆ epigraph (epiClosure f) := epigraph_epiClosure f ▸ subset_closure
  have hle := epigraph_subset_epigraph_iff.mp hsub
  apply le_antisymm (hle x)
  by_contra! hlt
  obtain ⟨r, hr, hr'⟩ := EReal.exists_between_coe_real hlt
  have hdom : effectiveDomain f ⊆ effectiveDomain (epiClosure f) := fun y hy ↦ (hle y).trans_lt hy
  have hconv : Convex ℝ (epigraph (epiClosure f)) := epigraph_epiClosure f ▸ hf.closure
  have hmem := mem_interior_epigraph_of_mem_interior_effectiveDomain hconv (interior_mono hdom hx) hr
  obtain ⟨s, hs, -⟩ := EReal.exists_between_coe_real (show f x < ⊤ from interior_subset (s := effectiveDomain f) hx)
  have hi : (interior (epigraph f)).Nonempty :=
    ⟨(x,s), mem_interior_epigraph_of_mem_interior_effectiveDomain hf hx hs⟩
  rw [epigraph_epiClosure, hf.interior_closure_eq_interior_of_nonempty_interior hi] at hmem
  exact hr'.not_ge (show f x ≤ (r : EReal) from interior_subset (s := epigraph f) hmem)

omit [FiniteDimensional ℝ E] in
theorem effectiveDomain_radialSubderivative {f : E → EReal} {x : E} {c : ℝ} (hx : f x = c) :
    effectiveDomain (radialSubderivative f x) = radialCone (effectiveDomain f) x := by
  ext w
  change (⨅ t : Ioi (0 : ℝ), differenceQuotient f x t w) < ⊤ ↔ _
  rw [iInf_lt_iff]
  constructor
  · rintro ⟨t, h⟩
    obtain ⟨a, ha, -⟩ := EReal.exists_between_coe_real h
    exact ⟨t, t.property, ((differenceQuotient_le_coe_iff hx t.property).mp ha.le).trans_lt (EReal.coe_lt_top _)⟩
  · rintro ⟨t, ht, h⟩
    obtain ⟨a, ha, -⟩ := EReal.exists_between_coe_real (show f (x + t • w) < ⊤ from h)
    have he : c + t * ((a-c)/t) = a := by field_simp; ring
    exact ⟨⟨t, ht⟩, ((differenceQuotient_le_coe_iff hx ht (α := (a-c)/t)).mpr (by rw [he]; exact ha.le)).trans_lt (EReal.coe_lt_top _)⟩

section Euclidean

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- **Proposition 8.21.** The three domain interiors are exactly the
directions reaching the interior of the original domain. -/
theorem convex_subderivative_interiors {f : F → EReal} {x : F} {c : ℝ}
    (hf : Convex ℝ (epigraph f)) (hx : f x = c) :
    let W := {w : F | ∃ t : ℝ, 0 ≤ t ∧ x + t • w ∈ interior (effectiveDomain f)}
    interior (effectiveDomain (regularSubderivative f x)) = W ∧
      interior (effectiveDomain (subderivative f x)) = W ∧
      interior (effectiveDomain (radialSubderivative f x)) = W := by
  let D := effectiveDomain f
  let R := radialCone (interior D) x
  let h := radialSubderivative f x
  let g := subderivative f x
  obtain ⟨hreg, hclosure⟩ := convex_subderivatives_eq_epiClosure_radial hf hx
  have hdom : effectiveDomain h ⊆ effectiveDomain g := by
    have sub : epigraph h ⊆ epigraph g := by rw [show g = epiClosure h from hclosure, epigraph_epiClosure]; exact subset_closure
    exact fun y hy ↦ (epigraph_subset_epigraph_iff.mp sub y).trans_lt hy
  have hc : Convex ℝ (epigraph g) := by
    rw [show g = epiClosure h from hclosure, epigraph_epiClosure]
    exact (convex_epigraph_radialSubderivative hf hx).closure
  have hR : R ⊆ interior (effectiveDomain h) := by
    change radialCone (interior D) x ⊆ interior (effectiveDomain (radialSubderivative f x))
    conv_lhs => rw [← (isOpen_radialCone (isOpen_interior (s := D)) x).interior_eq]
    apply interior_mono
    rw [effectiveDomain_radialSubderivative hx]
    exact radialCone_mono interior_subset x
  have hg : interior (effectiveDomain g) ⊆ R := by
    intro w hw
    obtain ⟨a, ha, -⟩ := EReal.exists_between_coe_real (show g w < ⊤ from interior_subset (s := effectiveDomain g) hw)
    have hwa := mem_interior_epigraph_of_mem_interior_effectiveDomain hc hw ha
    change (w,a) ∈ interior (epigraph (subderivative f x)) at hwa
    rw [epigraph_subderivative_eq_tangentCone hx,
      (convex_epigraph_tangent_geometry hf (show (x,c) ∈ epigraph f from hx.le)).2.2] at hwa
    obtain ⟨t, ht, hpoint⟩ := hwa
    exact ⟨t, ht, ((mem_interior_epigraph_iff_of_convex hf).mp hpoint).1⟩
  have hW : R = {w : F | ∃ t : ℝ, 0 ≤ t ∧ x + t • w ∈ interior D} := by
    ext w
    constructor
    · rintro ⟨t, ht, h⟩
      exact ⟨t, ht.le, h⟩
    · rintro ⟨t, ht, h⟩
      rcases eq_or_lt_of_le ht with rfl | ht
      · simp only [zero_smul, add_zero] at h
        have hp : Tendsto (fun s : ℝ ↦ x + s • w) (𝓝[>] 0) (𝓝 x) := by
          have hp0 : Continuous (fun s : ℝ ↦ x + s • w) := continuous_const.add (continuous_id.smul continuous_const)
          simpa using (hp0.tendsto 0).mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
        obtain ⟨s, hs, hm⟩ := ((show ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s from self_mem_nhdsWithin).and
          (hp.eventually (isOpen_interior.mem_nhds h))).exists
        exact ⟨s, hs, hm⟩
      · exact ⟨t, ht, h⟩
  change _ = _ ∧ _ = _ ∧ _ = _
  rw [hreg]
  have he := Subset.antisymm hg (hR.trans (interior_mono hdom))
  exact ⟨he.trans hW, he.trans hW, (Subset.antisymm ((interior_mono hdom).trans hg) hR).trans hW⟩

/-- In each of those directions the one-sided radial limit already equals
both closed subderivatives. -/
theorem convex_subderivatives_eq_on_interior {f : F → EReal} {x : F} {c : ℝ}
    (hf : Convex ℝ (epigraph f)) (hx : f x = c) {w : F}
    (hw : ∃ t : ℝ, 0 ≤ t ∧ x + t • w ∈ interior (effectiveDomain f)) :
    regularSubderivative f x w = radialSubderivative f x w ∧
      subderivative f x w = radialSubderivative f x w := by
  obtain ⟨he, hcl⟩ := convex_subderivatives_eq_epiClosure_radial hf hx
  rw [he, hcl]
  refine ⟨?_, ?_⟩ <;> apply epiClosure_eq_of_mem_interior_convex (convex_epigraph_radialSubderivative hf hx)
  all_goals rw [(convex_subderivative_interiors hf hx).2.2]; exact hw

end Euclidean

end RW
