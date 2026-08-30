/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Binary Product Cone Formulas

This file supplies the binary-product infrastructure behind Proposition 6.41.
The ambient product is `WithLp 2 (E × F)`, whose norm and inner product are
the Euclidean product ones.  In particular, none of the normal-cone formulas
below use the sup norm carried by the plain product type.
-/

import RockafellarWets.Chapter6.NormalCones
import Mathlib.Analysis.InnerProductSpace.ProdL2

open Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

section Products

variable {E F : Type*}

/-- The binary product of two sets, regarded as a subset of the Euclidean
`L²` product. -/
def l2ProdSet (C : Set E) (D : Set F) : Set (WithLp 2 (E × F)) :=
  {z | z.fst ∈ C ∧ z.snd ∈ D}

@[simp]
theorem mem_l2ProdSet {C : Set E} {D : Set F} {z : WithLp 2 (E × F)} :
    z ∈ l2ProdSet C D ↔ z.fst ∈ C ∧ z.snd ∈ D :=
  Iff.rfl

@[simp]
theorem toLp_mem_l2ProdSet {C : Set E} {D : Set F} {x : E} {y : F} :
    WithLp.toLp 2 (x, y) ∈ l2ProdSet C D ↔ x ∈ C ∧ y ∈ D :=
  Iff.rfl

section ClosedProducts

variable [TopologicalSpace E] [TopologicalSpace F]

/-- A binary Euclidean product of closed sets is closed. -/
theorem isClosed_l2ProdSet {C : Set E} {D : Set F} (hC : IsClosed C) (hD : IsClosed D) :
    IsClosed (l2ProdSet C D) := by
  change IsClosed
    ((fun z : WithLp 2 (E × F) ↦ z.fst) ⁻¹' C ∩ (fun z : WithLp 2 (E × F) ↦ z.snd) ⁻¹' D)
  exact (hC.preimage (WithLp.continuous_fst 2 E F)).inter
    (hD.preimage (WithLp.continuous_snd 2 E F))

end ClosedProducts

section TangentCones

variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A tangent vector to a binary product has tangent coordinate vectors. -/
theorem tangentCone_l2ProdSet_subset (C : Set E) (D : Set F) (x : E) (y : F) :
    tangentCone (l2ProdSet C D) (WithLp.toLp 2 (x, y)) ⊆
      l2ProdSet (tangentCone C x) (tangentCone D y) := by
  rintro w ⟨zs, τs, hzCD, -, hτpos, hτ0, hq⟩
  constructor
  · refine mem_tangentCone_of_forall (xs := fun n ↦ (zs n).fst) (hτ := hτpos)
      (hτ0 := hτ0) (fun n ↦ (hzCD n).1) ?_
    simpa using ((WithLp.continuous_fst 2 E F).tendsto w).comp hq
  · refine mem_tangentCone_of_forall (xs := fun n ↦ (zs n).snd) (hτ := hτpos)
      (hτ0 := hτ0) (fun n ↦ (hzCD n).2) ?_
    simpa using ((WithLp.continuous_snd 2 E F).tendsto w).comp hq

/-- Derivable tangent vectors commute with binary Euclidean products.  In the
reverse inclusion the two paths are restricted to the smaller radius. -/
theorem derivableCone_l2ProdSet (C : Set E) (D : Set F) (x : E) (y : F) :
    derivableCone (l2ProdSet C D) (WithLp.toLp 2 (x, y)) =
      l2ProdSet (derivableCone C x) (derivableCone D y) := by
  ext w
  constructor
  · rintro ⟨ε, hε, ξ, hξ0, hξCD, hξt⟩
    constructor
    · refine ⟨ε, hε, fun t ↦ (ξ t).fst, ?_, fun t ht ↦ (hξCD t ht).1, ?_⟩
      · simpa using congrArg WithLp.fst hξ0
      · simpa using ((WithLp.continuous_fst 2 E F).tendsto w).comp hξt
    · refine ⟨ε, hε, fun t ↦ (ξ t).snd, ?_, fun t ht ↦ (hξCD t ht).2, ?_⟩
      · simpa using congrArg WithLp.snd hξ0
      · simpa using ((WithLp.continuous_snd 2 E F).tendsto w).comp hξt
  · rintro ⟨⟨ε, hε, ξ, hξ0, hξC, hξt⟩, ⟨δ, hδ, η, hη0, hηD, hηt⟩⟩
    refine ⟨min ε δ, lt_min hε hδ, fun t ↦ WithLp.toLp 2 (ξ t, η t), ?_, ?_, ?_⟩
    · simp [hξ0, hη0]
    · intro t ht
      exact ⟨hξC t ⟨ht.1, ht.2.trans (min_le_left _ _)⟩,
        hηD t ⟨ht.1, ht.2.trans (min_le_right _ _)⟩⟩
    · have hp := hξt.prodMk_nhds hηt
      exact ((WithLp.prod_continuous_toLp 2 E F).tendsto (w.fst, w.snd) |>.comp hp).congr'
        (Filter.Eventually.of_forall fun t ↦ by
          simp only [Function.comp_apply]
          rw [← WithLp.toLp_sub, ← WithLp.toLp_smul]
          rfl)

/-- If both factors are geometrically derivable at their base points, the
ordinary tangent cone commutes with their binary Euclidean product. -/
theorem tangentCone_l2ProdSet (C : Set E) (D : Set F) {x : E} {y : F}
    (hx : x ∈ C) (hy : y ∈ D) (hC : IsGeometricallyDerivable C x)
    (hD : IsGeometricallyDerivable D y) :
    tangentCone (l2ProdSet C D) (WithLp.toLp 2 (x, y)) =
      l2ProdSet (tangentCone C x) (tangentCone D y) := by
  refine Subset.antisymm (tangentCone_l2ProdSet_subset C D x y) ?_
  intro w hw
  apply derivableCone_subset_tangentCone (C := l2ProdSet C D) (x := WithLp.toLp 2 (x, y))
    ⟨hx, hy⟩
  rw [derivableCone_l2ProdSet C D x y]
  exact ⟨hC hw.1, hD hw.2⟩

end TangentCones

section NormalCones

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Regular normal cones commute with binary Euclidean products. -/
theorem regularNormalCone_l2ProdSet (C : Set E) (D : Set F) (x : E) (y : F) :
    regularNormalCone (l2ProdSet C D) (WithLp.toLp 2 (x, y)) =
      l2ProdSet (regularNormalCone C x) (regularNormalCone D y) := by
  ext v
  constructor
  · rw [mem_regularNormalCone_iff]
    rintro ⟨hxy, hv⟩
    constructor
    · rw [mem_regularNormalCone_iff]
      refine ⟨hxy.1, fun ε hε ↦ ?_⟩
      obtain ⟨δ, hδ, hvδ⟩ := hv ε hε
      refine ⟨δ, hδ, fun x' hx'C hx'd ↦ ?_⟩
      have hpd :
          ‖WithLp.toLp 2 (x', y) - WithLp.toLp 2 (x, y)‖ < δ := by
        simpa only [← WithLp.toLp_sub, Prod.mk_sub_mk, sub_self,
          WithLp.norm_toLp_fst] using hx'd
      have h := hvδ (WithLp.toLp 2 (x', y)) ⟨hx'C, hxy.2⟩ hpd
      have hnorm :
          ‖WithLp.toLp 2 (x', y) - WithLp.toLp 2 (x, y)‖ = ‖x' - x‖ := by
        rw [← WithLp.toLp_sub, Prod.mk_sub_mk, sub_self, WithLp.norm_toLp_fst]
      rw [hnorm] at h
      simpa [WithLp.prod_inner_apply] using h
    · rw [mem_regularNormalCone_iff]
      refine ⟨hxy.2, fun ε hε ↦ ?_⟩
      obtain ⟨δ, hδ, hvδ⟩ := hv ε hε
      refine ⟨δ, hδ, fun y' hy'D hy'd ↦ ?_⟩
      have hpd :
          ‖WithLp.toLp 2 (x, y') - WithLp.toLp 2 (x, y)‖ < δ := by
        simpa only [← WithLp.toLp_sub, Prod.mk_sub_mk, sub_self,
          WithLp.norm_toLp_snd] using hy'd
      have h := hvδ (WithLp.toLp 2 (x, y')) ⟨hxy.1, hy'D⟩ hpd
      have hnorm :
          ‖WithLp.toLp 2 (x, y') - WithLp.toLp 2 (x, y)‖ = ‖y' - y‖ := by
        rw [← WithLp.toLp_sub, Prod.mk_sub_mk, sub_self, WithLp.norm_toLp_snd]
      rw [hnorm] at h
      simpa [WithLp.prod_inner_apply] using h
  · rintro ⟨hv, hw⟩
    rw [mem_regularNormalCone_iff] at hv hw ⊢
    refine ⟨⟨hv.1, hw.1⟩, fun ε hε ↦ ?_⟩
    obtain ⟨δE, hδE, hvδ⟩ := hv.2 (ε / 2) (by positivity)
    obtain ⟨δF, hδF, hwδ⟩ := hw.2 (ε / 2) (by positivity)
    refine ⟨min δE δF, lt_min hδE hδF, fun z hz hzd ↦ ?_⟩
    have hfst_le : ‖z.fst - x‖ ≤ ‖z - WithLp.toLp 2 (x, y)‖ := by
      simpa using WithLp.norm_fst_le E (z - WithLp.toLp 2 (x, y))
    have hsnd_le : ‖z.snd - y‖ ≤ ‖z - WithLp.toLp 2 (x, y)‖ := by
      simpa using WithLp.norm_snd_le E (z - WithLp.toLp 2 (x, y))
    have hv' := hvδ z.fst hz.1
      (lt_of_le_of_lt hfst_le (hzd.trans_le (min_le_left _ _)))
    have hw' := hwδ z.snd hz.2
      (lt_of_le_of_lt hsnd_le (hzd.trans_le (min_le_right _ _)))
    calc
      ⟪v, z - WithLp.toLp 2 (x, y)⟫_ℝ =
          ⟪v.fst, z.fst - x⟫_ℝ + ⟪v.snd, z.snd - y⟫_ℝ := by
            simp [WithLp.prod_inner_apply]
      _ ≤ (ε / 2) * ‖z.fst - x‖ + (ε / 2) * ‖z.snd - y‖ :=
        add_le_add hv' hw'
      _ ≤ (ε / 2) * ‖z - WithLp.toLp 2 (x, y)‖ +
          (ε / 2) * ‖z - WithLp.toLp 2 (x, y)‖ :=
        add_le_add (mul_le_mul_of_nonneg_left hfst_le (by positivity))
          (mul_le_mul_of_nonneg_left hsnd_le (by positivity))
      _ = ε * ‖z - WithLp.toLp 2 (x, y)‖ := by ring

/-- Limiting normal cones commute with binary Euclidean products.  The
reverse inclusion zips the two component witness sequences term by term. -/
theorem normalCone_l2ProdSet (C : Set E) (D : Set F) (x : E) (y : F) :
    normalCone (l2ProdSet C D) (WithLp.toLp 2 (x, y)) =
      l2ProdSet (normalCone C x) (normalCone D y) := by
  ext v
  constructor
  · rintro ⟨hxy, zs, ws, -, hzto, hws, hwto⟩
    constructor
    · refine mem_normalCone_of_forall hxy.1
        (xs := fun n ↦ (zs n).fst) (vs := fun n ↦ (ws n).fst) ?_ ?_ ?_
      · simpa using ((WithLp.continuous_fst 2 E F).tendsto
          (WithLp.toLp 2 (x, y))).comp hzto
      · intro n
        have hn : (ws n).fst ∈ regularNormalCone C (zs n).fst := by
          have hn' := hws n
          rw [show zs n = WithLp.toLp 2 ((zs n).fst, (zs n).snd) by rfl,
            regularNormalCone_l2ProdSet C D] at hn'
          exact hn'.1
        exact hn
      · simpa using ((WithLp.continuous_fst 2 E F).tendsto v).comp hwto
    · refine mem_normalCone_of_forall hxy.2
        (xs := fun n ↦ (zs n).snd) (vs := fun n ↦ (ws n).snd) ?_ ?_ ?_
      · simpa using ((WithLp.continuous_snd 2 E F).tendsto
          (WithLp.toLp 2 (x, y))).comp hzto
      · intro n
        have hn : (ws n).snd ∈ regularNormalCone D (zs n).snd := by
          have hn' := hws n
          rw [show zs n = WithLp.toLp 2 ((zs n).fst, (zs n).snd) by rfl,
            regularNormalCone_l2ProdSet C D] at hn'
          exact hn'.2
        exact hn
      · simpa using ((WithLp.continuous_snd 2 E F).tendsto v).comp hwto
  · rintro ⟨⟨hx, xs, vs, -, hxto, hvs, hvto⟩,
      ⟨hy, ys, ws, -, hyto, hws, hwto⟩⟩
    refine mem_normalCone_of_forall ⟨hx, hy⟩
      (xs := fun n ↦ WithLp.toLp 2 (xs n, ys n))
      (vs := fun n ↦ WithLp.toLp 2 (vs n, ws n)) ?_ ?_ ?_
    · exact ((WithLp.prod_continuous_toLp 2 E F).tendsto (x, y)).comp
        (hxto.prodMk_nhds hyto)
    · intro n
      rw [regularNormalCone_l2ProdSet C D]
      exact ⟨hvs n, hws n⟩
    · exact ((WithLp.prod_continuous_toLp 2 E F).tendsto (v.fst, v.snd)).comp
        (hvto.prodMk_nhds hwto)

/-- The closed-set binary-product part of Proposition 6.41: Clarke
regularity holds for the product exactly when it holds for both factors. -/
theorem isClarkeRegularAt_l2ProdSet_iff {C : Set E} {D : Set F} {x : E} {y : F}
    (hC : IsClosed C) (hD : IsClosed D) (hx : x ∈ C) (hy : y ∈ D) :
    IsClarkeRegularAt (l2ProdSet C D) (WithLp.toLp 2 (x, y)) ↔
      IsClarkeRegularAt C x ∧ IsClarkeRegularAt D y := by
  constructor
  · intro hp
    constructor
    · refine ⟨IsClosed.isLocallyClosedAt hC x, Subset.antisymm ?_
          (regularNormalCone_subset_normalCone C x)⟩
      intro v hv
      have h0D : (0 : F) ∈ normalCone D y :=
        regularNormalCone_subset_normalCone D y (isCone_regularNormalCone hy).1
      have hpNormal : WithLp.toLp 2 (v, (0 : F)) ∈
          normalCone (l2ProdSet C D) (WithLp.toLp 2 (x, y)) := by
        rw [normalCone_l2ProdSet C D x y]
        exact ⟨hv, h0D⟩
      have hpRegular : WithLp.toLp 2 (v, (0 : F)) ∈
          regularNormalCone (l2ProdSet C D) (WithLp.toLp 2 (x, y)) := by
        rw [← hp.2]
        exact hpNormal
      rw [regularNormalCone_l2ProdSet C D x y] at hpRegular
      exact hpRegular.1
    · refine ⟨IsClosed.isLocallyClosedAt hD y, Subset.antisymm ?_
          (regularNormalCone_subset_normalCone D y)⟩
      intro v hv
      have h0C : (0 : E) ∈ normalCone C x :=
        regularNormalCone_subset_normalCone C x (isCone_regularNormalCone hx).1
      have hpNormal : WithLp.toLp 2 ((0 : E), v) ∈
          normalCone (l2ProdSet C D) (WithLp.toLp 2 (x, y)) := by
        rw [normalCone_l2ProdSet C D x y]
        exact ⟨h0C, hv⟩
      have hpRegular : WithLp.toLp 2 ((0 : E), v) ∈
          regularNormalCone (l2ProdSet C D) (WithLp.toLp 2 (x, y)) := by
        rw [← hp.2]
        exact hpNormal
      rw [regularNormalCone_l2ProdSet C D x y] at hpRegular
      exact hpRegular.2
  · rintro ⟨hCR, hDR⟩
    refine ⟨IsClosed.isLocallyClosedAt (isClosed_l2ProdSet hC hD) _, ?_⟩
    calc
      normalCone (l2ProdSet C D) (WithLp.toLp 2 (x, y)) =
          l2ProdSet (normalCone C x) (normalCone D y) :=
        normalCone_l2ProdSet C D x y
      _ = l2ProdSet (regularNormalCone C x) (regularNormalCone D y) := by
        rw [hCR.2, hDR.2]
      _ = regularNormalCone (l2ProdSet C D) (WithLp.toLp 2 (x, y)) :=
        (regularNormalCone_l2ProdSet C D x y).symm

end NormalCones

end Products

end RW
