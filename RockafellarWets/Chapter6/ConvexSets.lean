/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Tangents and Normals to Convex Sets

Theorem 6.9: a convex set is geometrically derivable at each of its points,
its tangent cone is the closure of the cone of directions along which the set
is reached, its interior is computed from the interior of the set, and its
two normal cones coincide and are the vectors making a nonpositive inner
product with every difference `x - x̄`.
-/

import RockafellarWets.Chapter6.NormalCones

open Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

section RadialCone

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The set `K` of the proof of 6.9: the directions `w` for which `p + λw`
lands in `S` for some `λ > 0`. -/
def radialCone (S : Set E) (p : E) : Set E :=
  {w : E | ∃ lam : ℝ, 0 < lam ∧ p + lam • w ∈ S}

@[simp]
theorem mem_radialCone {S : Set E} {p w : E} :
    w ∈ radialCone S p ↔ ∃ lam : ℝ, 0 < lam ∧ p + lam • w ∈ S := Iff.rfl

theorem radialCone_mono {S T : Set E} (h : S ⊆ T) (p : E) :
    radialCone S p ⊆ radialCone T p := fun _ ⟨l, hl, hm⟩ ↦ ⟨l, hl, h hm⟩

/-- The radial cone of a convex set is convex.  The scaling that exhibits a
convex combination of `w₁` and `w₂` is the harmonic-style combination
`λ₁λ₂/(aλ₂ + bλ₁)` of the two scalings. -/
theorem convex_radialCone {S : Set E} (hS : Convex ℝ S) (p : E) :
    Convex ℝ (radialCone S p) := by
  rintro w₁ ⟨l₁, hl₁, hm₁⟩ w₂ ⟨l₂, hl₂, hm₂⟩ a b ha hb hab
  have h1 : 0 ≤ a * l₂ := mul_nonneg ha hl₂.le
  have h2 : 0 ≤ b * l₁ := mul_nonneg hb hl₁.le
  have hd : 0 < a * l₂ + b * l₁ := by
    rcases lt_or_ge 0 a with hA | hA
    · exact lt_add_of_pos_of_le (mul_pos hA hl₂) h2
    · have hb1 : (0 : ℝ) < b := by linarith
      exact lt_add_of_le_of_pos h1 (mul_pos hb1 hl₁)
  refine ⟨l₁ * l₂ / (a * l₂ + b * l₁), div_pos (mul_pos hl₁ hl₂) hd, ?_⟩
  have hmem := hS hm₁ hm₂ (a := a * l₂ / (a * l₂ + b * l₁))
    (b := b * l₁ / (a * l₂ + b * l₁)) (by positivity) (by positivity)
    (by field_simp)
  have heq : (a * l₂ / (a * l₂ + b * l₁)) • (p + l₁ • w₁)
      + (b * l₁ / (a * l₂ + b * l₁)) • (p + l₂ • w₂)
      = p + (l₁ * l₂ / (a * l₂ + b * l₁)) • (a • w₁ + b • w₂) := by
    match_scalars <;> field_simp
  rwa [heq] at hmem

/-- The radial cone of an open set is open. -/
theorem isOpen_radialCone {U : Set E} (hU : IsOpen U) (p : E) :
    IsOpen (radialCone U p) := by
  have hcover : radialCone U p = ⋃ lam ∈ Ioi (0 : ℝ), (fun w ↦ p + lam • w) ⁻¹' U := by
    ext w
    simp only [radialCone, mem_setOf_eq, mem_iUnion, mem_Ioi, mem_preimage, exists_prop]
  rw [hcover]
  exact isOpen_biUnion fun lam _ ↦
    hU.preimage (continuous_const.add (continuous_const_smul lam))

end RadialCone

section ConvexSets

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Theorem 6.9**: a direction along which a convex set is reached is a
*derivable* tangent vector, the straight path `t ↦ x̄ + tw` staying in the set
by convexity. -/
theorem mem_derivableCone_of_convex {C : Set E} {x : E} (hC : Convex ℝ C) (hx : x ∈ C)
    {w : E} (hw : w ∈ radialCone C x) : w ∈ derivableCone C x := by
  obtain ⟨lam, hlam, hmem⟩ := hw
  refine ⟨lam, hlam, fun t ↦ x + t • w, by simp, fun t ht ↦ ?_, ?_⟩
  · have hcomb := hC hx hmem (a := 1 - t / lam) (b := t / lam)
      (by rw [sub_nonneg, div_le_one hlam]; exact ht.2)
      (div_nonneg ht.1 hlam.le) (by ring)
    have heq : (1 - t / lam) • x + (t / lam) • (x + lam • w) = x + t • w := by
      match_scalars <;> field_simp
      ring
    rw [heq] at hcomb
    exact hcomb
  · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hval : t⁻¹ • ((x + t • w) - x) = w := by
      rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ (ne_of_gt ht), one_smul]
    exact hval.symm

/-- **Theorem 6.9**: every tangent vector to any set is a limit of radial
directions, since each difference quotient is itself one. -/
theorem tangentCone_subset_closure_radialCone (C : Set E) (x : E) :
    tangentCone C x ⊆ closure (radialCone C x) := by
  rintro w ⟨xs, τs, hxC, -, hτpos, -, hq⟩
  refine mem_closure_of_tendsto hq (Filter.Eventually.of_forall fun n ↦ ?_)
  refine ⟨τs n, hτpos n, ?_⟩
  have heq : x + τs n • ((τs n)⁻¹ • (xs n - x)) = xs n := by
    rw [smul_smul, mul_inv_cancel₀ (hτpos n).ne', one_smul]
    abel
  rw [heq]
  exact hxC n

/-- **Theorem 6.9**: the derivable cone of a convex set is the closure of its
radial cone. -/
theorem derivableCone_eq_closure_radialCone {C : Set E} {x : E} (hC : Convex ℝ C)
    (hx : x ∈ C) : derivableCone C x = closure (radialCone C x) :=
  Subset.antisymm
    ((derivableCone_subset_tangentCone hx).trans (tangentCone_subset_closure_radialCone C x))
    ((isClosed_derivableCone hx).closure_subset_iff.2 fun _ hw ↦
      mem_derivableCone_of_convex hC hx hw)

/-- **Theorem 6.9**: the tangent cone of a convex set is the closure of its
radial cone. -/
theorem tangentCone_eq_closure_radialCone {C : Set E} {x : E} (hC : Convex ℝ C)
    (hx : x ∈ C) : tangentCone C x = closure (radialCone C x) := by
  refine Subset.antisymm (tangentCone_subset_closure_radialCone C x) ?_
  rw [← derivableCone_eq_closure_radialCone hC hx]
  exact derivableCone_subset_tangentCone hx

/-- **Theorem 6.9**: a convex set is geometrically derivable at each of its
points. -/
theorem isGeometricallyDerivable_of_convex {C : Set E} {x : E} (hC : Convex ℝ C)
    (hx : x ∈ C) : IsGeometricallyDerivable C x := by
  have key : tangentCone C x ⊆ derivableCone C x := by
    rw [tangentCone_eq_closure_radialCone hC hx,
      derivableCone_eq_closure_radialCone hC hx]
  exact key

/-- **Theorem 6.9**: the regular normals to a convex set at `x̄` are the
vectors making a nonpositive inner product with every `x - x̄`, `x ∈ C`. -/
theorem regularNormalCone_eq_of_convex {C : Set E} {x : E} (hC : Convex ℝ C)
    (hx : x ∈ C) :
    regularNormalCone C x = {v : E | ∀ y ∈ C, ⟪v, y - x⟫_ℝ ≤ 0} := by
  ext v
  constructor
  · intro hv y hy
    refine inner_nonpos_of_mem_regularNormalCone hv
      (derivableCone_subset_tangentCone hx
        (mem_derivableCone_of_convex hC hx ⟨1, one_pos, ?_⟩))
    have heq : x + (1 : ℝ) • (y - x) = y := by module
    rw [heq]
    exact hy
  · intro hv
    refine ⟨hx, fun ε hε ↦ ?_⟩
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hv y hy).trans (mul_nonneg hε.le (norm_nonneg _))

/-- **Theorem 6.9**: the two normal cones to a convex set coincide.  Local
closedness plays no part here; it enters only through Definition 6.4. -/
theorem normalCone_eq_regularNormalCone_of_convex {C : Set E} {x : E}
    (hC : Convex ℝ C) (hx : x ∈ C) : normalCone C x = regularNormalCone C x := by
  refine Subset.antisymm ?_ (regularNormalCone_subset_normalCone C x)
  rintro v ⟨-, xs, vs, hxC, hxto, hvs, hvto⟩
  rw [regularNormalCone_eq_of_convex hC hx]
  intro y hy
  have hle : ∀ n, ⟪vs n, y - xs n⟫_ℝ ≤ 0 := by
    intro n
    have hmem : vs n ∈ {v : E | ∀ y ∈ C, ⟪v, y - xs n⟫_ℝ ≤ 0} := by
      rw [← regularNormalCone_eq_of_convex hC (hxC n)]
      exact hvs n
    exact hmem y hy
  exact le_of_tendsto (Filter.Tendsto.inner hvto (tendsto_const_nhds.sub hxto))
    (Filter.Eventually.of_forall hle)

/-- **Theorem 6.9**: the normal cone to a convex set. -/
theorem normalCone_eq_of_convex {C : Set E} {x : E} (hC : Convex ℝ C) (hx : x ∈ C) :
    normalCone C x = {v : E | ∀ y ∈ C, ⟪v, y - x⟫_ℝ ≤ 0} := by
  rw [normalCone_eq_regularNormalCone_of_convex hC hx,
    regularNormalCone_eq_of_convex hC hx]

/-- **Theorem 6.9**, the concluding clause: a convex set is Clarke regular at
each of its points at which it is locally closed. -/
theorem isClarkeRegularAt_of_convex {C : Set E} {x : E} (hC : Convex ℝ C)
    (hx : x ∈ C) (hlc : IsLocallyClosedAt C x) : IsClarkeRegularAt C x :=
  ⟨hlc, normalCone_eq_regularNormalCone_of_convex hC hx⟩

/-- **Theorem 6.9**: the interior of the tangent cone to a convex set is the
radial cone of its interior. -/
theorem interior_tangentCone_of_convex [FiniteDimensional ℝ E] {C : Set E} {x : E}
    (hC : Convex ℝ C) (hx : x ∈ C) :
    interior (tangentCone C x) = radialCone (interior C) x := by
  rw [tangentCone_eq_closure_radialCone hC hx]
  rcases eq_empty_or_nonempty (interior C) with hint | hint
  · have hK₀ : radialCone (interior C) x = ∅ := by
      rw [hint]
      refine eq_empty_of_forall_notMem fun w hw ↦ ?_
      obtain ⟨lam, hlam, hm⟩ := hw
      exact hm
    rw [hK₀]
    refine eq_empty_of_forall_notMem fun w hw ↦ ?_
    have hKV : radialCone C x
        ⊆ (Submodule.span ℝ ((fun y ↦ y - x) '' C) : Set E) := by
      rintro u ⟨l, hl, hm⟩
      have h1 : x + l • u - x ∈ (fun y ↦ y - x) '' C := ⟨x + l • u, hm, rfl⟩
      have hsimp : x + l • u - x = l • u := by module
      rw [hsimp] at h1
      have h3 := Submodule.smul_mem (Submodule.span ℝ ((fun y ↦ y - x) '' C)) l⁻¹
        (Submodule.subset_span h1)
      rwa [smul_smul, inv_mul_cancel₀ hl.ne', one_smul] at h3
    have hclosed : IsClosed ((Submodule.span ℝ ((fun y ↦ y - x) '' C) : Submodule ℝ E) : Set E) :=
      Submodule.closed_of_finiteDimensional _
    have hwV : w ∈ interior ((Submodule.span ℝ ((fun y ↦ y - x) '' C) : Submodule ℝ E) : Set E) :=
      interior_mono (hclosed.closure_subset_iff.2 hKV) hw
    have htop : Submodule.span ℝ ((fun y ↦ y - x) '' C) = ⊤ :=
      Submodule.eq_top_of_nonempty_interior' _ ⟨w, hwV⟩
    have hvs : vectorSpan ℝ C = ⊤ := by
      rw [vectorSpan_eq_span_vsub_set_right ℝ hx]
      exact htop
    have haff : affineSpan ℝ C = ⊤ :=
      (AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ E E
        ⟨x, hx⟩).2 hvs
    have hne := (hC.interior_nonempty_iff_affineSpan_eq_top).2 haff
    rw [hint] at hne
    exact hne.ne_empty rfl
  · have hK₀open : IsOpen (radialCone (interior C) x) := isOpen_radialCone isOpen_interior x
    have hK₀conv : Convex ℝ (radialCone (interior C) x) := convex_radialCone hC.interior x
    have hK₀ne : (radialCone (interior C) x).Nonempty := by
      obtain ⟨z, hz⟩ := hint
      refine ⟨z - x, 1, one_pos, ?_⟩
      have heq : x + (1 : ℝ) • (z - x) = z := by module
      rw [heq]
      exact hz
    have hKsub : radialCone C x ⊆ closure (radialCone (interior C) x) := by
      rintro u ⟨l, hl, hm⟩
      have hCcl : C ⊆ closure (interior C) := by
        rw [hC.closure_interior_eq_closure_of_nonempty_interior hint]
        exact subset_closure
      have hcont : Continuous fun y : E ↦ l⁻¹ • (y - x) :=
        (continuous_id.sub continuous_const).const_smul _
      have himg : (fun y : E ↦ l⁻¹ • (y - x)) '' interior C
          ⊆ radialCone (interior C) x := by
        rintro _ ⟨y, hy, rfl⟩
        refine ⟨l, hl, ?_⟩
        have heq : x + l • (l⁻¹ • (y - x)) = y := by
          rw [smul_smul, mul_inv_cancel₀ hl.ne', one_smul]
          abel
        rw [heq]
        exact hy
      have hmem : (fun y : E ↦ l⁻¹ • (y - x)) (x + l • u)
          ∈ closure ((fun y : E ↦ l⁻¹ • (y - x)) '' interior C) :=
        image_closure_subset_closure_image hcont ⟨x + l • u, hCcl hm, rfl⟩
      have hval : (fun y : E ↦ l⁻¹ • (y - x)) (x + l • u) = u := by
        dsimp only
        rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hl.ne', one_smul]
      rw [hval] at hmem
      exact closure_mono himg hmem
    have hclos : closure (radialCone C x) = closure (radialCone (interior C) x) :=
      Subset.antisymm (closure_minimal hKsub isClosed_closure)
        (closure_mono (radialCone_mono interior_subset x))
    rw [hclos, hK₀conv.interior_closure_eq_interior_of_nonempty_interior
      (by rwa [hK₀open.interior_eq]), hK₀open.interior_eq]

end ConvexSets

end RW
