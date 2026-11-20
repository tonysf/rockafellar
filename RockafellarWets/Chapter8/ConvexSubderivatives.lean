/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Radial subderivatives of convex functions
-/

import RockafellarWets.Chapter6.ImageSetCones
import RockafellarWets.Chapter7.EpiLimitProperties
import RockafellarWets.Chapter8.SubderivativeRegularityCriterion

open Filter Function Set Topology

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The infimum of the difference quotients along one fixed ray. -/
noncomputable def radialSubderivative (f : E → EReal) (x w : E) : EReal :=
  ⨅ t : Ioi (0 : ℝ), differenceQuotient f x t w

private theorem mem_epigraph_differenceQuotient_iff {f : E → EReal} {x : E} {c t : ℝ}
    (hx : f x = c) (ht : 0 < t) (p : E × ℝ) :
    p ∈ epigraph (differenceQuotient f x t) ↔ (x, c) + t • p ∈ epigraph f :=
  differenceQuotient_le_coe_iff hx ht

theorem monotoneOn_differenceQuotient_of_convex {f : E → EReal} {x : E} {c : ℝ}
    (hf : Convex ℝ (epigraph f)) (hx : f x = c) :
    MonotoneOn (differenceQuotient f x) (Ioi (0 : ℝ)) := by
  intro t ht s hs hts
  change 0 < s at hs
  change 0 < t at ht
  apply epigraph_subset_epigraph_iff.mp
  intro z hz
  rw [mem_epigraph_differenceQuotient_iff hx ht]
  have hzs := (mem_epigraph_differenceQuotient_iff hx hs z).mp hz
  have h := hf (show (x,c) ∈ epigraph f from hx.le) hzs (a := 1 - t / s) (b := t / s)
    (sub_nonneg.mpr ((div_le_one hs).mpr hts)) (div_nonneg ht.le hs.le) (by ring)
  simpa only [smul_add, smul_smul, div_mul_cancel₀ _ hs.ne', ← add_assoc, ← add_smul,
    sub_add_cancel, one_smul] using h

/-- **Proposition 8.21.** For a convex function finite at the base point,
each one-sided directional limit exists in the extended reals. -/
theorem tendsto_differenceQuotient_radialSubderivative {f : E → EReal} {x : E} {c : ℝ}
    (hf : Convex ℝ (epigraph f)) (hx : f x = c) (w : E) :
    Tendsto (fun t ↦ differenceQuotient f x t w) (𝓝[>] (0 : ℝ)) (𝓝 (radialSubderivative f x w)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ha.trans_le (iInf_le (fun s : Ioi (0 : ℝ) ↦ differenceQuotient f x s w) ⟨t, ht⟩)
  · intro b hb
    obtain ⟨s, hs⟩ := iInf_lt_iff.mp hb
    filter_upwards [Ioo_mem_nhdsGT s.property] with t ht
    exact (monotoneOn_differenceQuotient_of_convex hf hx ht.1 s.property ht.2.le w).trans_lt hs

/-- The radial subderivative bounds the increment on every positive ray,
including scale zero by the extended-real zero multiplication convention. -/
theorem radialSubderivative_growth {f : E → EReal} {x : E} {c t : ℝ} (hx : f x = c)
    (ht : 0 ≤ t) (w : E) :
    (c : EReal) + (t : EReal) * radialSubderivative f x w ≤ f (x + t • w) := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · simp [hx]
  · have hle := iInf_le (fun s : Ioi (0 : ℝ) ↦ differenceQuotient f x s w) ⟨t, ht⟩
    calc
      _ ≤ (c : EReal) + (t : EReal) * differenceQuotient f x t w :=
        add_le_add_right (mul_le_mul_of_nonneg_left hle (EReal.coe_nonneg.mpr ht.le)) _
      _ = _ := by
        rw [differenceQuotient, ← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ ht.ne',
          EReal.coe_one, one_mul, hx, add_comm, EReal.sub_add_cancel]

private theorem radialCone_epigraph_eq_iUnion {f : E → EReal} {x : E} {c : ℝ} (hx : f x = c) :
    radialCone (epigraph f) (x,c) = ⋃ t : Ioi (0 : ℝ), epigraph (differenceQuotient f x t) := by
  ext z
  simp only [mem_radialCone, mem_iUnion]
  exact ⟨fun ⟨t, ht, h⟩ ↦ ⟨⟨t, ht⟩, (mem_epigraph_differenceQuotient_iff hx ht z).mpr h⟩,
    fun ⟨t, h⟩ ↦ ⟨t, t.property, (mem_epigraph_differenceQuotient_iff hx t.property z).mp h⟩⟩

theorem radialSubderivative_eq_epiBoundary_radialCone {f : E → EReal} {x : E} {c : ℝ} (hx : f x = c) :
    radialSubderivative f x = epiBoundary (radialCone (epigraph f) (x,c)) := by
  rw [radialCone_epigraph_eq_iUnion hx]
  funext w
  apply le_antisymm
  · refine le_iInf fun a ↦ ?_
    obtain ⟨t, ht⟩ := mem_iUnion.mp a.property
    exact (iInf_le (fun s : Ioi (0 : ℝ) ↦ differenceQuotient f x s w) t).trans ht
  · refine le_iInf fun t ↦ ?_
    rw [← iInf_coe_real_ge_eq (differenceQuotient f x t w)]
    refine le_iInf fun a ↦ ?_
    exact iInf_le (fun b : {r : ℝ // (w,r) ∈ ⋃ t : Ioi (0 : ℝ), epigraph (differenceQuotient f x t)}
      ↦ ((b : ℝ) : EReal)) ⟨a, mem_iUnion_of_mem t a.property⟩

private theorem positiveHull_epigraph_differenceQuotient_one {f : E → EReal} {x : E} {c : ℝ}
    (hx : f x = c) :
    positiveHull (epigraph (differenceQuotient f x 1)) = radialCone (epigraph f) (x,c) := by
  ext z
  constructor
  · rintro (rfl | ⟨s, hs, p, hp, rfl⟩)
    · exact ⟨1, one_pos, by simpa using (show (x,c) ∈ epigraph f from hx.le)⟩
    · refine ⟨s⁻¹, inv_pos.mpr hs, ?_⟩
      simpa only [smul_smul, inv_mul_cancel₀ hs.ne', one_smul] using
        (mem_epigraph_differenceQuotient_iff hx one_pos p).mp hp
  · rintro ⟨s, hs, h⟩
    exact Or.inr ⟨s⁻¹, inv_pos.mpr hs, s • z,
      (mem_epigraph_differenceQuotient_iff hx one_pos _).mpr (by simpa only [one_smul] using h),
      by rw [smul_smul, inv_mul_cancel₀ hs.ne', one_smul]⟩

private theorem radialSubderivative_eq_positiveHull {f : E → EReal} {x : E} {c : ℝ}
    (hx : f x = c) :
    radialSubderivative f x = positiveHullFunction (differenceQuotient f x 1) := by
  rw [radialSubderivative_eq_epiBoundary_radialCone hx, ← positiveHull_epigraph_differenceQuotient_one hx]
  rfl

theorem positivelyHomogeneous_radialSubderivative {f : E → EReal} {x : E} {c : ℝ} (hx : f x = c) :
    PositivelyHomogeneous (radialSubderivative f x) := by
  rw [radialSubderivative_eq_positiveHull hx]
  exact positivelyHomogeneous_positiveHullFunction _

theorem convex_epigraph_radialSubderivative {f : E → EReal} {x : E} {c : ℝ}
    (hf : Convex ℝ (epigraph f)) (hx : f x = c) : Convex ℝ (epigraph (radialSubderivative f x)) := by
  rw [radialSubderivative_eq_positiveHull hx]
  apply convex_epigraph_positiveHullFunction
  intro z hz p hp a b ha hb hab
  rw [mem_epigraph_differenceQuotient_iff hx one_pos] at hz hp ⊢
  simp only [one_smul] at hz hp ⊢
  convert hf hz hp ha hb hab using 1
  match_scalars <;> linarith

/-- Subadditivity for the book's inf-addition convention at opposite infinities. -/
theorem radialSubderivative_subadditive {f : E → EReal} {x : E} {c : ℝ}
    (hf : Convex ℝ (epigraph f)) (hx : f x = c) (u v : E) :
    radialSubderivative f x (u + v) ≤ infAddition (radialSubderivative f x u) (radialSubderivative f x v) := by
  by_contra! h
  obtain ⟨b, hb, hb'⟩ := EReal.exists_between_coe_real h
  obtain ⟨r, s, hr, hs, rfl⟩ := (infAddition_le_coe_iff ..).mp hb.le
  have hc := isCone_epigraph_of_positivelyHomogeneous (positivelyHomogeneous_radialSubderivative hx)
  exact hb'.not_ge ((hc.convex_iff_add_mem.mp (convex_epigraph_radialSubderivative hf hx))
    (x := (u,r)) (y := (v,s)) hr hs)

section Euclidean

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
private theorem radialCone_preimage_l2ProdEquiv (C : Set (F × ℝ)) (p : F × ℝ) :
    radialCone (l2ProdEquiv F ⁻¹' C) (WithLp.toLp 2 p) = l2ProdEquiv F ⁻¹' radialCone C p := by
  ext z
  simp only [mem_radialCone, mem_preimage, map_add, map_smul, l2ProdEquiv_toLp]

/-- The convex tangent identities in the ordinary product norm used by
epigraphs, obtained from the Euclidean product form of Theorem 6.9. -/
theorem convex_epigraph_tangent_geometry {C : Set (F × ℝ)} {p : F × ℝ}
    (hC : Convex ℝ C) (hp : p ∈ C) :
    regularTangentCone C p = tangentCone C p ∧
      tangentCone C p = closure (radialCone C p) ∧
      interior (tangentCone C p) = radialCone (interior C) p := by
  let L := l2ProdEquiv F
  let z := WithLp.toLp 2 p
  have hpre : z ∈ L ⁻¹' C := hp
  have hc := convex_preimage_continuousLinearEquiv L hC
  have ht : tangentCone (L ⁻¹' C) z = L ⁻¹' tangentCone C p :=
    tangentCone_preimage_continuousLinearEquiv L C z
  have hr : regularTangentCone (L ⁻¹' C) z = L ⁻¹' regularTangentCone C p :=
    regularTangentCone_preimage (Φ' := L) L.toContinuousLinearMap.hasStrictFDerivAt C hp
  have hray (S : Set (F × ℝ)) : radialCone (L ⁻¹' S) z = L ⁻¹' radialCone S p :=
    radialCone_preimage_l2ProdEquiv S p
  have hi (S : Set (F × ℝ)) : L ⁻¹' interior S = interior (L ⁻¹' S) := L.toHomeomorph.preimage_interior S
  have hcl (S : Set (F × ℝ)) : L ⁻¹' closure S = closure (L ⁻¹' S) := L.toHomeomorph.preimage_closure S
  refine ⟨L.surjective.preimage_injective ?_, L.surjective.preimage_injective ?_,
    L.surjective.preimage_injective ?_⟩
  · rw [← ht, ← hr, regularTangentCone_eq_tangentCone_of_convex hc hpre]
  · rw [← ht, hcl, ← hray, tangentCone_eq_closure_radialCone hc hpre]
  · rw [hi, ← ht, interior_tangentCone_of_convex hc hpre, ← hray, hi]

/-- **Proposition 8.21.** Both subderivatives are the lower closure of the
radial derivative. The convex function itself need only be finite at the
base point. -/
theorem convex_subderivatives_eq_epiClosure_radial {f : F → EReal} {x : F} {c : ℝ}
    (hf : Convex ℝ (epigraph f)) (hx : f x = c) :
    regularSubderivative f x = subderivative f x ∧ subderivative f x = epiClosure (radialSubderivative f x) := by
  obtain ⟨hreg, htan, -⟩ := convex_epigraph_tangent_geometry hf (show (x,c) ∈ epigraph f from hx.le)
  constructor
  · apply le_antisymm _ (subderivative_le_regularSubderivative hx)
    apply epigraph_subset_epigraph_iff.mp
    rw [epigraph_subderivative_eq_tangentCone hx, ← hreg]
    exact regularTangentCone_epigraph_subset hx
  · apply eq_of_epigraph_eq
    rw [epigraph_subderivative_eq_tangentCone hx, htan, epigraph_epiClosure, radialCone_epigraph_eq_iUnion hx]
    exact (closure_epigraph_iInf (fun t : Ioi (0 : ℝ) ↦ differenceQuotient f x t)).symm

end Euclidean

end RW
