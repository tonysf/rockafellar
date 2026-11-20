/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Epigraph normal slices for nonlinear rescaling
-/

import RockafellarWets.Chapter10.MonotoneRescalingRepresentation
import RockafellarWets.Chapter10.ConstrainedSubgradients
import RockafellarWets.Chapter10.CoordinateSubgradients
import RockafellarWets.Chapter9.ImplicitGraphPermutations

open Filter Set Topology
open scoped InnerProductSpace Pointwise

namespace RW

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A negative vertical epigraph normal is a scaled subgradient. -/
theorem epigraph_normal_negative_slice {f : E → EReal} {x v : E} {c t : ℝ}
    (hx : f x = c) (ht : 0 < t) :
    WithLp.toLp 2 (v,-t) ∈ normalCone (euclideanEpigraph f) (WithLp.toLp 2 (x,c)) ↔
      ∃ w ∈ subdifferential f x, v = t • w := by
  constructor
  · intro hv
    have hn := (isCone_normalCone (show WithLp.toLp 2 (x,c) ∈ euclideanEpigraph f from hx.le)).smul_mem
      hv (inv_nonneg.mpr ht.le)
    have hw : t⁻¹ • v ∈ subdifferential f x := by
      apply (mem_subdifferential_iff_epigraph_normal hx).mpr
      convert hn using 1
      apply WithLp.ofLp_injective
      ext <;> simp [smul_eq_mul,ht.ne']
    exact ⟨t⁻¹ • v,hw,by rw [smul_smul,mul_inv_cancel₀ ht.ne',one_smul]⟩
  · rintro ⟨w,hw,rfl⟩
    have hn := (isCone_normalCone (show WithLp.toLp 2 (x,c) ∈ euclideanEpigraph f from hx.le)).smul_mem
      ((mem_subdifferential_iff_epigraph_normal hx).mp hw) ht.le
    convert hn using 1
    apply WithLp.ofLp_injective
    ext <;> simp [smul_eq_mul]

/-- Corrected rescaling formula: the horizon branch requires the zero
outer multiplier, whereas positive outer multipliers scale ordinary subgradients. -/
def rescalingSubgradientSet (Λ : Set ℝ) (f : E → EReal) (x : E) : Set E :=
  {v | (∃ t ∈ Λ, 0 < t ∧ ∃ w ∈ subdifferential f x, v = t • w) ∨
    (0 ∈ Λ ∧ v ∈ horizonSubdifferential f x)}

theorem mem_rescalingSubgradientSet_iff_epigraph_normal {f : E → EReal} {x v : E} {c : ℝ}
    (hx : f x = c) (hl : LowerSemicontinuous f) (Λ : Set ℝ) :
    v ∈ rescalingSubgradientSet Λ f x ↔
      ∃ t ∈ Λ, WithLp.toLp 2 (v,-t) ∈ normalCone (euclideanEpigraph f) (WithLp.toLp 2 (x,c)) := by
  constructor
  · rintro (⟨t,ht,hpos,hw⟩ | ⟨hzero,hv⟩)
    · exact ⟨t,ht,(epigraph_normal_negative_slice hx hpos).mpr hw⟩
    · exact ⟨0,hzero,by simpa only [neg_zero] using horizontal_normal_of_mem_horizonSubdifferential hx hv⟩
  · rintro ⟨t,ht,hn⟩
    have hnonneg : 0 ≤ t := neg_nonpos.mp (vertical_nonpos_of_mem_normalCone_epigraph hn)
    rcases eq_or_lt_of_le hnonneg with he | hpos
    · subst t
      exact Or.inr ⟨ht,(mem_horizonSubdifferential_iff_epigraph_normal_of_locallyLsc
        (locallyLscAt_of_lowerSemicontinuous_finite hl hx) hx).mpr (by simpa only [neg_zero] using hn)⟩
    · exact Or.inl ⟨t,ht,hpos,(epigraph_normal_negative_slice hx hpos).mp hn⟩

theorem rescalingSubgradientSet_subset_printed (Λ : Set ℝ) (f : E → EReal) (x : E) :
    rescalingSubgradientSet Λ f x ⊆
      {v | ∃ t ∈ Λ, ∃ w ∈ subdifferential f x, v = t • w} ∪ horizonSubdifferential f x := by
  rintro v (⟨t,ht,_,w,hw,he⟩ | ⟨_,hv⟩)
  · exact Or.inl ⟨t,ht,w,hw,he⟩
  · exact Or.inr hv

@[simp] theorem heightProjection_adjoint (t : ℝ) :
    (WithLp.fstL 2 ℝ ℝ E).adjoint t = WithLp.toLp 2 (t,(0:E)) := by
  apply ext_inner_right ℝ
  intro q
  rw [ContinuousLinearMap.adjoint_inner_left,WithLp.prod_inner_apply]
  simp [real_inner_comm]

theorem subdifferential_heightFunction {θ : ℝ → EReal} {c d : ℝ} (hc : θ c = d) (x : E) :
    subdifferential (fun q : WithLp 2 (ℝ × E) ↦ θ q.fst) (WithLp.toLp 2 (c,x)) =
      (fun t : ℝ ↦ WithLp.toLp 2 (t,(0:E))) '' subdifferential θ c := by
  have h := subdifferential_comp_eq_of_surjective (g := θ) (x := WithLp.toLp 2 (c,x)) (WithLp.fstL 2 ℝ ℝ E).contDiff hc
    (by rw [ContinuousLinearMap.fderiv]; intro a; exact ⟨WithLp.toLp 2 (a,(0:E)),rfl⟩)
  simpa only [ContinuousLinearMap.fderiv,heightProjection_adjoint] using h

theorem horizonSubdifferential_heightFunction {θ : ℝ → EReal} {c d : ℝ}
    (hθ : LowerSemicontinuous θ) (hc : θ c = d) (x : E) :
    horizonSubdifferential (fun q : WithLp 2 (ℝ × E) ↦ θ q.fst) (WithLp.toLp 2 (c,x)) =
      (fun t : ℝ ↦ WithLp.toLp 2 (t,(0:E))) '' horizonSubdifferential θ c := by
  have h := horizonSubdifferential_comp_eq_of_surjective (g := θ) (x := WithLp.toLp 2 (c,x)) (WithLp.fstL 2 ℝ ℝ E).contDiff hθ hc
    (by rw [ContinuousLinearMap.fderiv]; intro a; exact ⟨WithLp.toLp 2 (a,(0:E)),rfl⟩)
  simpa only [ContinuousLinearMap.fderiv,heightProjection_adjoint] using h

/-- Normal membership for the epigraph with its coordinates swapped. -/
theorem mem_normalCone_swapped_epigraph {f : E → EReal} (p v : WithLp 2 (ℝ × E)) :
    v ∈ normalCone ((LinearIsometryEquiv.withLpProdComm 2 ℝ ℝ E) ⁻¹' euclideanEpigraph f) p ↔
      WithLp.toLp 2 (v.snd,v.fst) ∈ normalCone (euclideanEpigraph f) (WithLp.toLp 2 (p.snd,p.fst)) := by
  let L := LinearIsometryEquiv.withLpProdComm 2 ℝ ℝ E
  rw [normalCone_preimage_linearIsometryEquiv L]
  rfl

end

end RW
