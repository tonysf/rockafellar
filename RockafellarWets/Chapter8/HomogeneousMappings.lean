/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Positively homogeneous and sublinear set-valued mappings
-/

import RockafellarWets.Chapter5.ConvexSemicontinuity
import RockafellarWets.Chapter3.Cones

open Set
open scoped Pointwise

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Positive homogeneity for mappings in formula 8(24). -/
def SvPositivelyHomogeneous (H : E → Set F) : Prop :=
  0 ∈ H 0 ∧ ∀ w (c : ℝ), 0 < c → H (c • w) = c • H w

/-- A sublinear mapping is graph-convex and positively homogeneous. -/
def SvSublinear (H : E → Set F) : Prop := SvPositivelyHomogeneous H ∧ SvGraphConvex H

/-- **Proposition 8.36**, characterization by the graph cone. -/
theorem svPositivelyHomogeneous_iff_isCone_svGraph {H : E → Set F} :
    SvPositivelyHomogeneous H ↔ IsCone (svGraph H) := by
  constructor
  · rintro ⟨h₀, h⟩
    refine ⟨h₀, ?_⟩
    rintro ⟨w,z⟩ hz c hc
    change c • z ∈ H (c • w)
    rw [h w c hc]
    exact smul_mem_smul_set hz
  · rintro ⟨h₀, hs⟩
    refine ⟨h₀, fun w c hc ↦ Subset.antisymm ?_ ?_⟩
    · intro z hz
      refine ⟨c⁻¹ • z, ?_, smul_inv_smul₀ hc.ne' _⟩
      have hh := hs (x := (c • w, z)) hz (inv_pos.mpr hc)
      change c⁻¹ • z ∈ H (c⁻¹ • c • w) at hh
      simpa [hc.ne'] using hh
    · rintro _ ⟨z, hz, rfl⟩
      exact hs (x := (w,z)) hz hc

theorem SvPositivelyHomogeneous.isCone_zero {H : E → Set F} (h : SvPositivelyHomogeneous H) :
    IsCone (H 0) := by
  refine ⟨h.1, fun {z} hz {c} hc ↦ ?_⟩
  simpa only [smul_zero] using
    (show c • z ∈ H (c • (0:E)) from (h.2 0 c hc).ge (smul_mem_smul_set hz))

theorem SvPositivelyHomogeneous.isCone_svDom {H : E → Set F} (h : SvPositivelyHomogeneous H) :
    IsCone (svDom H) := by
  refine ⟨⟨0, h.1⟩, ?_⟩
  rintro w ⟨z,hz⟩ c hc
  exact ⟨c • z, (h.2 w c hc).ge (smul_mem_smul_set hz)⟩

/-- **Proposition 8.36**, formula 8(25). -/
theorem SvPositivelyHomogeneous.graphConvex_iff {H : E → Set F} (h : SvPositivelyHomogeneous H) :
    SvGraphConvex H ↔ ∀ w w', H w + H w' ⊆ H (w + w') := by
  rw [SvGraphConvex, (svPositivelyHomogeneous_iff_isCone_svGraph.mp h).convex_iff_add_mem]
  constructor
  · rintro hadd w w' _ ⟨z, hz, z', hz', rfl⟩
    exact hadd (x := (w,z)) (y := (w',z')) hz hz'
  · rintro hh ⟨w,z⟩ ⟨w',z'⟩ hz hz'
    exact hh w w' (add_mem_add hz hz')

/-- **Proposition 8.36**, a sublinear mapping with full domain and trivial
vertical fiber is a single-valued linear map. -/
theorem SvSublinear.exists_linearMap_of_zero_fiber {H : E → Set F} (h : SvSublinear H)
    (hzero : H 0 = {0}) (hdom : svDom H = univ) : ∃ A : E →ₗ[ℝ] F, ∀ w, H w = {A w} := by
  classical
  have hne (w : E) : (H w).Nonempty := by change w ∈ svDom H; simp [hdom]
  choose A hA using hne
  have hadd := h.1.graphConvex_iff.mp h.2
  have hcancel {w : E} {z : F} (hz : z ∈ H w) : z + A (-w) = 0 := by
    have hh := hadd w (-w) (add_mem_add hz (hA _))
    simpa only [add_neg_cancel, hzero, mem_singleton_iff] using hh
  have heq {w : E} {z : F} (hz : z ∈ H w) : z = A w :=
    add_right_cancel ((hcancel hz).trans (hcancel (hA w)).symm)
  have hneg (w : E) : A (-w) = -A w := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hcancel (hA w)
  have hpos {c : ℝ} (hc : 0 < c) (w : E) : A (c • w) = c • A w :=
    (heq ((h.1.2 w c hc).ge (smul_mem_smul_set (hA w)))).symm
  let L : E →ₗ[ℝ] F := {
    toFun := A
    map_add' := fun w v ↦ (heq (hadd w v (add_mem_add (hA w) (hA v)))).symm
    map_smul' := by
      intro c w
      change A (c • w) = c • A w
      rcases lt_trichotomy c 0 with hc | rfl | hc
      · have hh := hpos (neg_pos.mpr hc) w
        simpa only [neg_smul, hneg, neg_inj] using hh
      · simpa only [zero_smul] using (heq h.1.1).symm
      · exact hpos hc w }
  exact ⟨L, fun w ↦ Subset.antisymm (fun z hz ↦ heq hz) (singleton_subset_iff.mpr (hA w))⟩

end RW
