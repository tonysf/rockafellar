/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Normals to tangent cones

Proposition 6.27(a). Normal vectors to the tangent cone at any of its points
are normal vectors to the original locally closed set at the base point.
The proof uses proximal approximation, applying 6.18(b) to the blow-ups along
one tangent witness at a time. Their outer limit need only be contained in the
tangent cone: restriction preserves the proximal projection at the witness.
-/

import RockafellarWets.Chapter6.ElementaryCones
import RockafellarWets.Chapter6.NormalApproximation

open Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

section AffineScaling

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Positive affine dilations preserve proximal normal directions. -/
theorem proximalNormalCone_affine_image {C : Set E} {w v : E}
    (hv : v ∈ proximalNormalCone C w) (x : E) {a : ℝ} (ha : 0 < a) :
    v ∈ proximalNormalCone ((fun z ↦ x + a • z) '' C) (x + a • w) := by
  obtain ⟨ρ, hρ, hw, hmin⟩ := hv
  refine ⟨a * ρ, mul_pos ha hρ, ⟨w, hw, rfl⟩, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have hdiff (y : E) :
      (x + a • y) - ((x + a • w) + (a * ρ) • v) = a • (y - (w + ρ • v)) := by
    module
  rw [hdiff, hdiff, norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
  exact mul_le_mul_of_nonneg_left (hmin z hz) ha.le

/-- A nonzero blow-up is the preimage under its inverse affine dilation. -/
theorem blowUp_eq_preimage {C : Set E} {x : E} {τ : ℝ} (hτ : τ ≠ 0) :
    blowUp C x τ = (fun w ↦ x + τ • w) ⁻¹' C := by
  ext w
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [smul_smul, hτ] using hy
  · intro hw
    refine ⟨x + τ • w, hw, ?_⟩
    simp [smul_smul, hτ]

/-- Undoing a nonzero blow-up recovers the original set. -/
theorem affine_image_blowUp (C : Set E) (x : E) {τ : ℝ} (hτ : τ ≠ 0) :
    (fun w ↦ x + τ • w) '' blowUp C x τ = C := by
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    rwa [blowUp_eq_preimage hτ] at hw
  · intro hy
    refine ⟨τ⁻¹ • (y - x), ⟨y, hy, rfl⟩, ?_⟩
    simp [smul_smul, hτ]

/-- A blow-up of a closed set at a nonzero scale is closed. -/
theorem isClosed_blowUp {C : Set E} (hC : IsClosed C) (x : E) {τ : ℝ}
    (hτ : τ ≠ 0) : IsClosed (blowUp C x τ) := by
  rw [blowUp_eq_preimage hτ]
  exact hC.preimage (by fun_prop)

/-- Proximal normals to a positive blow-up are proximal normals to the
original set at the corresponding point. -/
theorem proximalNormalCone_blowUp_subset {C : Set E} {x w : E} {τ : ℝ}
    (hτ : 0 < τ) : proximalNormalCone (blowUp C x τ) w ⊆
      proximalNormalCone C (x + τ • w) := by
  intro v hv
  have h := proximalNormalCone_affine_image hv x hτ
  rwa [affine_image_blowUp C x hτ.ne'] at h

end AffineScaling

section NormalsToClosedCones

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Normal directions of a closed cone persist under positive dilation of
the point of attachment. -/
theorem normalCone_subset_smul_of_isCone {K : Set E} (hK : IsClosed K)
    (hcone : IsCone K) (w : E) {a : ℝ} (ha : 0 < a) :
    normalCone K w ⊆ normalCone K (a • w) := by
  intro v hv
  have himage : (fun z : E ↦ (0 : E) + a • z) '' K = K := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hcone.2 hy ha
    · intro hz
      refine ⟨a⁻¹ • z, hcone.2 hz (inv_pos.2 ha), ?_⟩
      simp [smul_smul, ha.ne']
  obtain ⟨xs, vs, hxsK, hvs, hxsto, hvsto⟩ :=
    exists_seq_mem_proximalNormalCone_tendsto_of_mem_normalCone hK hv
  apply mem_normalCone_of_forall (hcone.2 hv.1 ha)
    (xs := fun n ↦ a • xs n) (vs := vs) (hxsto.const_smul a) _ hvsto
  intro n
  apply proximalNormalCone_subset_regularNormalCone
  have hprox := proximalNormalCone_affine_image (hvs n) 0 ha
  rw [himage] at hprox
  simpa only [zero_add] using hprox

/-- The normal cone of a closed cone is unchanged along each positive ray. -/
theorem normalCone_smul_of_isCone {K : Set E} (hK : IsClosed K)
    (hcone : IsCone K) (w : E) {a : ℝ} (ha : 0 < a) :
    normalCone K (a • w) = normalCone K w := by
  refine Subset.antisymm ?_ (normalCone_subset_smul_of_isCone hK hcone w ha)
  simpa [smul_smul, ha.ne'] using
    normalCone_subset_smul_of_isCone hK hcone (a • w) (inv_pos.2 ha)

/-- At the vertex of a closed cone the normal cone contains every normal
direction occurring at any point of the cone. -/
theorem normalCone_subset_normalCone_zero_of_isCone {K : Set E}
    (hK : IsClosed K) (hcone : IsCone K) (w : E) :
    normalCone K w ⊆ normalCone K 0 := by
  intro v hv
  let τ : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hτ : ∀ n, 0 < τ n := fun n ↦ by dsimp [τ]; positivity
  have hτ0 : Tendsto τ atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  apply mem_normalCone_of_tendsto hcone.1
    (xs := fun n ↦ τ n • w) (vs := fun _ ↦ v)
    (fun n ↦ hcone.2 hv.1 (hτ n)) _
    (fun n ↦ normalCone_subset_smul_of_isCone hK hcone w (hτ n) hv)
    tendsto_const_nhds
  simpa using hτ0.smul (tendsto_const_nhds (x := w))

/-- The normal cone at the vertex is exactly the union of the normal cones
at all points of a closed cone. -/
theorem normalCone_zero_eq_iUnion_of_isCone {K : Set E}
    (hK : IsClosed K) (hcone : IsCone K) :
    normalCone K 0 = ⋃ w ∈ K, normalCone K w := by
  apply Subset.antisymm
  · intro v hv
    exact mem_iUnion.2 ⟨0, mem_iUnion.2 ⟨hcone.1, hv⟩⟩
  · intro v hv
    obtain ⟨w, hw⟩ := mem_iUnion.1 hv
    obtain ⟨_, hv⟩ := mem_iUnion.1 hw
    exact normalCone_subset_normalCone_zero_of_isCone hK hcone w hv

end NormalsToClosedCones

section NormalsToTangents

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- Every sequential outer limit of positive blow-ups with scale tending to
zero is contained in the tangent cone. -/
theorem outerSetLimit_blowUp_subset_tangentCone (C : Set E) (x : E)
    {τs : ℕ → ℝ} (hτpos : ∀ n, 0 < τs n) (hτ0 : Tendsto τs atTop (nhds 0)) :
    outerSetLimit (fun n ↦ blowUp C x (τs n)) ⊆ tangentCone C x := by
  intro w hw
  obtain ⟨φ, zs, hφ, hzs, hzsto⟩ := mem_outerSetLimit_iff_exists_subsequence.1 hw
  choose ys hysC hys using fun n ↦ hzs n
  apply mem_tangentCone_of_forall hysC (fun n ↦ hτpos (φ n))
    (hτ0.comp hφ.tendsto_atTop)
  simpa only [hys] using hzsto

/-- Proximal normals to the tangent cone are normal vectors to the original
closed set. Only a tangent witness for the point of attachment is needed. -/
theorem proximalNormalCone_tangentCone_subset_of_isClosed {C : Set E}
    (hC : IsClosed C) {x : E} (hx : x ∈ C) (w : E) :
    proximalNormalCone (tangentCone C x) w ⊆ normalCone C x := by
  intro v hv
  obtain ⟨δ, hδ, hwT, hmin⟩ := hv
  obtain ⟨ys, τs, hysC, -, hτpos, hτ0, hq⟩ := hwT
  let Cseq : ℕ → Set E := fun n ↦ blowUp C x (τs n)
  let D : Set E := outerSetLimit Cseq
  have hwD : w ∈ D :=
    mem_outerSetLimit_iff_exists_subsequence.2
      ⟨id, fun n ↦ (τs n)⁻¹ • (ys n - x), strictMono_id,
        fun n ↦ ⟨ys n, hysC n, rfl⟩, hq⟩
  have hDT : D ⊆ tangentCone C x :=
    outerSetLimit_blowUp_subset_tangentCone C x hτpos hτ0
  have hvD : v ∈ proximalNormalCone D w :=
    ⟨δ, hδ, hwD, fun z hz ↦ hmin z (hDT hz)⟩
  obtain ⟨φ, ws, vs, hφ, -, hvs, hwsto, hvsto⟩ :=
    exists_subsequence_mem_proximalNormalCone_tendsto_of_mem_proximalNormalCone
      (fun n ↦ isClosed_blowUp hC x (hτpos n).ne') rfl hvD
  have hvC : ∀ n, vs n ∈ proximalNormalCone C (x + τs (φ n) • ws n) :=
    fun n ↦ proximalNormalCone_blowUp_subset (hτpos (φ n)) (hvs n)
  apply mem_normalCone_of_forall hx
    (xs := fun n ↦ x + τs (φ n) • ws n) (vs := vs) _
    (fun n ↦ proximalNormalCone_subset_regularNormalCone (hvC n)) hvsto
  simpa using (tendsto_const_nhds (x := x)).add
    ((hτ0.comp hφ.tendsto_atTop).smul hwsto)

/-- Every normal to the tangent cone of a closed set is normal to the
original set at its base point. -/
theorem normalCone_tangentCone_subset_of_isClosed {C : Set E}
    (hC : IsClosed C) {x : E} (hx : x ∈ C) (w : E) :
    normalCone (tangentCone C x) w ⊆ normalCone C x := by
  intro v hv
  obtain ⟨ws, vs, -, hvs, -, hvsto⟩ :=
    exists_seq_mem_proximalNormalCone_tendsto_of_mem_normalCone (isClosed_tangentCone C x) hv
  exact (isClosed_normalCone C x).mem_of_tendsto hvsto
    (Eventually.of_forall fun n ↦
      proximalNormalCone_tangentCone_subset_of_isClosed hC hx (ws n) (hvs n))

/-- **Proposition 6.27(a)**, the inclusion: every normal to `T_C(x)` at any
point of that cone is normal to `C` at `x`, assuming local closedness there. -/
theorem normalCone_tangentCone_subset {C : Set E} {x : E}
    (hx : x ∈ C) (hC : IsLocallyClosedAt C x) (w : E) :
    normalCone (tangentCone C x) w ⊆ normalCone C x := by
  obtain ⟨V, hV, -, hCV⟩ := hC
  have h := normalCone_tangentCone_subset_of_isClosed hCV
    (show x ∈ C ∩ V from ⟨hx, mem_of_mem_nhds hV⟩) w
  simpa only [tangentCone_inter_nhds hV, normalCone_inter_nhds hV] using h

/-- **Proposition 6.27(a)**, the equality at the vertex of the tangent cone. -/
theorem normalCone_tangentCone_zero_eq_iUnion {C : Set E} {x : E} (hx : x ∈ C) :
    normalCone (tangentCone C x) 0 =
      ⋃ w ∈ tangentCone C x, normalCone (tangentCone C x) w :=
  normalCone_zero_eq_iUnion_of_isCone (isClosed_tangentCone C x) (isCone_tangentCone hx)

end NormalsToTangents

end RW
