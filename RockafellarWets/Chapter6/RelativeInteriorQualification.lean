/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Relative-interior constraint qualification

Exercise 6.39(b). The relative interior is Mathlib's `intrinsicInterior`, the
interior of a set within its affine span. Three facts about relative
interiors of convex cones are proved directly from that definition: a
relative-interior point can be pushed slightly beyond any point of the set,
the relative interior of a convex cone absorbs addition of cone elements, and
a polar functional vanishing at a relative-interior point annihilates the
whole cone. The equivalence with the surjectivity condition 6.39(a) then
needs no closedness, regularity, or dimension hypothesis beyond finite
dimensionality.
-/

import RockafellarWets.Chapter6.ConstraintQualifications
import Mathlib.Analysis.Convex.Intrinsic

open Filter Set Topology
open scoped InnerProductSpace Pointwise

namespace RW

section RelativeInterior

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A relative-interior point can be moved a little further away from any
point of the set without leaving it. -/
theorem exists_pos_add_smul_sub_mem_of_mem_intrinsicInterior {K : Set E} {w l : E}
    (hw : w ∈ intrinsicInterior ℝ K) (hl : l ∈ K) :
    ∃ ε > (0 : ℝ), w + ε • (w - l) ∈ K := by
  obtain ⟨p, hp, rfl⟩ := mem_intrinsicInterior.1 hw
  have hlS : l ∈ affineSpan ℝ K := subset_affineSpan ℝ K hl
  have hdir : ((p : E) - l) ∈ (affineSpan ℝ K).direction :=
    AffineSubspace.vsub_mem_direction p.2 hlS
  have hmem : ∀ t : ℝ, l + t • ((p : E) - l) ∈ affineSpan ℝ K := fun t ↦ by
    have := AffineSubspace.vadd_mem_of_mem_direction (Submodule.smul_mem _ t hdir) hlS
    rwa [vadd_eq_add, add_comm] at this
  let φ : ℝ → affineSpan ℝ K := fun t ↦ ⟨l + t • ((p : E) - l), hmem t⟩
  have hφ : Continuous φ :=
    (continuous_const.add (continuous_id.smul continuous_const)).subtype_mk _
  have hφ1 : φ 1 = p := Subtype.ext (by simp [φ])
  have hev : ∀ᶠ t in 𝓝 (1 : ℝ), φ t ∈ ((↑) ⁻¹' K : Set (affineSpan ℝ K)) := by
    have hc : Tendsto φ (𝓝 1) (𝓝 p) := by
      rw [← hφ1]
      exact hφ.continuousAt
    exact hc (mem_interior_iff_mem_nhds.1 hp)
  have hev' : ∀ᶠ t in 𝓝[>] (1 : ℝ),
      φ t ∈ ((↑) ⁻¹' K : Set (affineSpan ℝ K)) ∧ t ∈ Ioi (1 : ℝ) :=
    (hev.filter_mono nhdsWithin_le_nhds).and eventually_mem_nhdsWithin
  obtain ⟨t, ht, ht1⟩ := hev'.exists
  refine ⟨t - 1, sub_pos.2 ht1, ?_⟩
  have hK : (φ t : E) ∈ K := ht
  convert hK using 1
  simp only [φ]
  module

/-- The relative interior of a convex cone absorbs addition of cone elements. -/
theorem add_mem_intrinsicInterior_of_convex_isCone {K : Set E}
    (hconv : Convex ℝ K) (hcone : IsCone K) {w k : E}
    (hw : w ∈ intrinsicInterior ℝ K) (hk : k ∈ K) :
    w + k ∈ intrinsicInterior ℝ K := by
  obtain ⟨p, hp, rfl⟩ := mem_intrinsicInterior.1 hw
  have h0 : (0 : E) ∈ affineSpan ℝ K := subset_affineSpan ℝ K hcone.1
  have hkS : k ∈ affineSpan ℝ K := subset_affineSpan ℝ K hk
  have hkdir : k ∈ (affineSpan ℝ K).direction := by
    simpa using AffineSubspace.vsub_mem_direction hkS h0
  have hmem : ∀ q : affineSpan ℝ K, ∀ c : ℝ, (q : E) + c • k ∈ affineSpan ℝ K :=
    fun q c ↦ by
      have := AffineSubspace.vadd_mem_of_mem_direction (Submodule.smul_mem _ c hkdir) q.2
      rwa [vadd_eq_add, add_comm] at this
  let τ : affineSpan ℝ K → affineSpan ℝ K := fun q ↦ ⟨(q : E) + k, by simpa using hmem q 1⟩
  let σ : affineSpan ℝ K → affineSpan ℝ K := fun q ↦
    ⟨(q : E) - k, by simpa [sub_eq_add_neg] using hmem q (-1)⟩
  have hσ : Continuous σ := (continuous_subtype_val.sub continuous_const).subtype_mk _
  have hστ : σ (τ p) = p := Subtype.ext (by simp [σ, τ])
  refine mem_intrinsicInterior.2 ⟨τ p, ?_, rfl⟩
  apply mem_interior_iff_mem_nhds.2
  have hU : σ ⁻¹' interior ((↑) ⁻¹' K : Set (affineSpan ℝ K)) ∈ 𝓝 (τ p) := by
    apply (isOpen_interior.preimage hσ).mem_nhds
    rw [mem_preimage, hστ]
    exact hp
  apply mem_of_superset hU
  intro q hq
  have hq1 : σ q ∈ interior ((↑) ⁻¹' K : Set (affineSpan ℝ K)) := hq
  have hq2 : σ q ∈ ((↑) ⁻¹' K : Set (affineSpan ℝ K)) := interior_subset hq1
  have hq' : (q : E) - k ∈ K := hq2
  have := add_mem_of_convex_isCone hconv hcone hq' hk
  simpa using this

/-- A functional that is nonpositive on a set and vanishes at a
relative-interior point vanishes on the whole set. -/
theorem inner_eq_zero_of_mem_intrinsicInterior {K : Set E} {y w : E}
    (hy : ∀ l ∈ K, ⟪y, l⟫_ℝ ≤ 0) (hw : w ∈ intrinsicInterior ℝ K)
    (hyw : ⟪y, w⟫_ℝ = 0) :
    ∀ l ∈ K, ⟪y, l⟫_ℝ = 0 := by
  intro l hl
  obtain ⟨ε, hε, hmem⟩ := exists_pos_add_smul_sub_mem_of_mem_intrinsicInterior hw hl
  have h := hy _ hmem
  rw [inner_add_right, real_inner_smul_right, inner_sub_right, hyw] at h
  have : 0 ≤ ⟪y, l⟫_ℝ := by nlinarith
  exact le_antisymm (hy l hl) this

end RelativeInterior

section Qualification

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The surjectivity condition `L - A K = F` for convex cones is equivalent
to the relative-interior condition of Exercise 6.39(b). -/
theorem add_neg_image_eq_univ_iff_relativeInterior {K : Set E} {L : Set F}
    (A : E →L[ℝ] F) (hKc : Convex ℝ K) (hKcone : IsCone K)
    (hLc : Convex ℝ L) (hLcone : IsCone L) :
    L + -(A '' K) = univ ↔
      (∀ y : F, (∀ l ∈ L, ⟪y, l⟫_ℝ = 0) →
        (∀ k ∈ K, ⟪A.adjoint y, k⟫_ℝ = 0) → y = 0) ∧
      ∃ w ∈ intrinsicInterior ℝ K, A w ∈ intrinsicInterior ℝ L := by
  constructor
  · intro h
    refine ⟨fun y hyL hyK ↦ ?_, ?_⟩
    · have hall : ∀ z : F, ⟪y, z⟫_ℝ = 0 := by
        intro z
        have hz : z ∈ L + -(A '' K) := by
          rw [h]
          trivial
        obtain ⟨l, hl, b, hb, rfl⟩ := hz
        rw [Set.mem_neg] at hb
        obtain ⟨k, hk, hbk⟩ := hb
        rw [inner_add_right, hyL l hl, ← neg_neg b, ← hbk, inner_neg_right,
          ← ContinuousLinearMap.adjoint_inner_left, hyK k hk]
        simp
      exact inner_self_eq_zero.1 (hall y)
    · obtain ⟨k₀, hk₀⟩ := Set.Nonempty.intrinsicInterior hKc ⟨0, hKcone.1⟩
      obtain ⟨l₀, hl₀⟩ := Set.Nonempty.intrinsicInterior hLc ⟨0, hLcone.1⟩
      have hz : A k₀ - l₀ ∈ L + -(A '' K) := by
        rw [h]
        trivial
      obtain ⟨l₁, hl₁, b, hb, hsum⟩ := hz
      rw [Set.mem_neg] at hb
      obtain ⟨k₁, hk₁, hbk⟩ := hb
      refine ⟨k₀ + k₁, add_mem_intrinsicInterior_of_convex_isCone hKc hKcone hk₀ hk₁, ?_⟩
      have hA : A (k₀ + k₁) = l₀ + l₁ := by
        rw [map_add, hbk, eq_sub_of_add_eq' hsum]
        abel
      rw [hA]
      exact add_mem_intrinsicInterior_of_convex_isCone hLc hLcone hl₀ hl₁
  · rintro ⟨hker, w, hwK, hwL⟩
    by_contra hne
    have himc : Convex ℝ (A '' K) := hKc.linear_image A.toLinearMap
    have himcone : IsCone (A '' K) := LinearMap.isCone_image A.toLinearMap hKcone
    have hpolar : polarCone (L + -(A '' K)) ≠ ({0} : Set F) := by
      intro h0
      exact hne ((polarCone_eq_singleton_iff_eq_univ (hLc.add himc.neg)
        (isCone_add hLcone (isCone_neg himcone))).1 h0)
    obtain ⟨y, hy, hy0⟩ : ∃ y ∈ polarCone (L + -(A '' K)), y ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hpolar
      refine Subset.antisymm (fun y hy ↦ hcon y hy) ?_
      rintro y rfl
      exact zero_mem_polarCone _
    rw [polarCone_add_neg_image A hKcone hLcone] at hy
    obtain ⟨hyL, hyK⟩ := hy
    have h1 : ⟪y, A w⟫_ℝ ≤ 0 := hyL _ (intrinsicInterior_subset hwL)
    have h2 : ⟪-(A.adjoint y), w⟫_ℝ ≤ 0 := hyK _ (intrinsicInterior_subset hwK)
    have heq : ⟪A.adjoint y, w⟫_ℝ = ⟪y, A w⟫_ℝ := ContinuousLinearMap.adjoint_inner_left A w y
    rw [inner_neg_left, heq] at h2
    have h0 : ⟪y, A w⟫_ℝ = 0 := by linarith
    have hLz := inner_eq_zero_of_mem_intrinsicInterior (fun l hl ↦ hyL l hl) hwL h0
    have hKz := inner_eq_zero_of_mem_intrinsicInterior (fun k hk ↦ hyK k hk) hwK
      (by rw [inner_neg_left, heq, h0, neg_zero])
    apply hy0
    apply hker y hLz
    intro k hk
    have := hKz k hk
    rwa [inner_neg_left, neg_eq_zero] at this

/-- **Exercise 6.39(b)**: no nonzero target multiplier is orthogonal to the
target regular tangent cone with adjoint image orthogonal to the source
regular tangent cone, and some relative-interior source direction maps into
the relative interior of the target cone. -/
def RelativeInteriorConstraintQualification (X : Set E) (D : Set F) (A : E →L[ℝ] F)
    (x : E) (u : F) : Prop :=
  (∀ y : F, (∀ l ∈ regularTangentCone D u, ⟪y, l⟫_ℝ = 0) →
    (∀ k ∈ regularTangentCone X x, ⟪A.adjoint y, k⟫_ℝ = 0) → y = 0) ∧
  ∃ w ∈ intrinsicInterior ℝ (regularTangentCone X x),
    A w ∈ intrinsicInterior ℝ (regularTangentCone D u)

/-- **Exercise 6.39(a),(b)**: the surjectivity and relative-interior
qualifications are equivalent at every feasible pair. -/
theorem regularTangentConstraintQualification_iff_relativeInteriorConstraintQualification
    {X : Set E} {D : Set F} {A : E →L[ℝ] F} {x : E} {u : F}
    (hx : x ∈ X) (hu : u ∈ D) :
    RegularTangentConstraintQualification X D A x u ↔
      RelativeInteriorConstraintQualification X D A x u :=
  add_neg_image_eq_univ_iff_relativeInterior A (convex_regularTangentCone hx)
    (isCone_regularTangentCone hx) (convex_regularTangentCone hu)
    (isCone_regularTangentCone hu)

/-- **Exercise 6.39**, sufficiency of (b) for the original normal
constraint qualification. -/
theorem RelativeInteriorConstraintQualification.normalConstraintQualification
    {X : Set E} {D : Set F} {A : E →L[ℝ] F} {x : E} {u : F}
    (h : RelativeInteriorConstraintQualification X D A x u)
    (hx : x ∈ X) (hu : u ∈ D)
    (hXlc : IsLocallyClosedAt X x) (hDlc : IsLocallyClosedAt D u) :
    NormalConstraintQualification X D A x u :=
  RegularTangentConstraintQualification.normalConstraintQualification
    ((regularTangentConstraintQualification_iff_relativeInteriorConstraintQualification
      hx hu).2 h) hx hu hXlc hDlc

/-- **Exercise 6.39**, necessity of (b) in the regular case. -/
theorem relativeInteriorConstraintQualification_iff_normalConstraintQualification
    {X : Set E} {D : Set F} {A : E →L[ℝ] F} {x : E} {u : F}
    (hx : x ∈ X) (hu : u ∈ D)
    (hXreg : IsClarkeRegularAt X x) (hDreg : IsClarkeRegularAt D u) :
    RelativeInteriorConstraintQualification X D A x u ↔
      NormalConstraintQualification X D A x u := by
  rw [← regularTangentConstraintQualification_iff_relativeInteriorConstraintQualification hx hu,
    regularTangentConstraintQualification_iff_normalConstraintQualification hx hu hXreg hDreg]

/-- **Exercise 6.39(b),(c)**: the relative-interior and convexified-normal
qualifications are equivalent at locally closed feasible pairs. -/
theorem relativeInteriorConstraintQualification_iff_convexifiedNormalConstraintQualification
    {X : Set E} {D : Set F} {A : E →L[ℝ] F} {x : E} {u : F}
    (hx : x ∈ X) (hu : u ∈ D)
    (hXlc : IsLocallyClosedAt X x) (hDlc : IsLocallyClosedAt D u) :
    RelativeInteriorConstraintQualification X D A x u ↔
      ConvexifiedNormalConstraintQualification X D A x u := by
  rw [← regularTangentConstraintQualification_iff_relativeInteriorConstraintQualification hx hu,
    regularTangentConstraintQualification_iff_convexifiedNormalConstraintQualification
      hx hu hXlc hDlc]

end Qualification

end RW
