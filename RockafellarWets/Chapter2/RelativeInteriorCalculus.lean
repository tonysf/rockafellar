/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 2H: Calculus of relative interiors

This file continues Section H of Chapter 2 of Rockafellar–Wets with
`rint = intrinsicInterior ℝ` in finite-dimensional real normed spaces.

* Proposition 2.43: relative interiors in product spaces through projections
  and fibers.
* Proposition 2.44: relative interiors (and closures) of linear images and
  preimages.
* Exercise 2.45: products, sums and scalar multiples, the interior condition
  (d), and proper separation (e).
-/

import RockafellarWets.Chapter2.RelativeInteriors

open Set Filter Topology Metric
open scoped Pointwise InnerProductSpace

noncomputable section

namespace RW

section Criterion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The criterion 2.41 with open segments. -/
theorem mem_intrinsicInterior_iff_openSegment {C : Set E} (hC : Convex ℝ C) {x : E} :
    x ∈ intrinsicInterior ℝ C ↔
      x ∈ C ∧ ∀ x₀ ∈ C, x₀ ≠ x → ∃ x₁ ∈ C, x ∈ openSegment ℝ x₀ x₁ := by
  rw [mem_intrinsicInterior_iff_segment hC]
  refine and_congr_right fun _ ↦ forall₂_congr fun x₀ _ ↦ imp_congr_right fun hne ↦
    exists_congr fun x₁ ↦ and_congr_right fun _ ↦ ?_
  by_cases h01 : x₀ = x₁
  · subst h01
    rw [segment_same, intrinsicInterior_singleton, openSegment_same]
  · rw [intrinsicInterior_segment h01]

end Criterion

/-! ## Proposition 2.43 -/

section Products

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The fiber `S(x) = {u | (x, u) ∈ G}`. -/
def productFiber (G : Set (E × F)) (x : E) : Set F := {u | (x, u) ∈ G}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem convex_productFiber {G : Set (E × F)} (hG : Convex ℝ G) (x : E) :
    Convex ℝ (productFiber G x) := by
  intro u hu v hv a b ha hb hab
  have := hG hu hv ha hb hab
  simp only [Prod.smul_mk, Prod.mk_add_mk, ← add_smul, hab, one_smul] at this
  exact this

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem openSegment_fst_snd {p₀ p₁ p : E × F} (h : p ∈ openSegment ℝ p₀ p₁) :
    p.1 ∈ openSegment ℝ p₀.1 p₁.1 ∧ p.2 ∈ openSegment ℝ p₀.2 p₁.2 := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := h
  exact ⟨⟨a, b, ha, hb, hab, rfl⟩, ⟨a, b, ha, hb, hab, rfl⟩⟩

/-- **Proposition 2.43**: for convex `G ⊆ E × F` with projection `X` and fibers
`S(x)`, `(x, u) ∈ rint G` if and only if `x ∈ rint X` and `u ∈ rint S(x)`. -/
theorem mem_intrinsicInterior_prod_iff {G : Set (E × F)} (hG : Convex ℝ G) {x : E} {u : F} :
    (x, u) ∈ intrinsicInterior ℝ G ↔
      x ∈ intrinsicInterior ℝ (Prod.fst '' G) ∧ u ∈ intrinsicInterior ℝ (productFiber G x) := by
  have hX : Convex ℝ (Prod.fst '' G) := hG.linear_image (LinearMap.fst ℝ E F)
  have hS := convex_productFiber hG
  rw [mem_intrinsicInterior_iff_openSegment hG, mem_intrinsicInterior_iff_openSegment hX,
    mem_intrinsicInterior_iff_openSegment (hS x)]
  constructor
  · rintro ⟨hxu, hcrit⟩
    refine ⟨⟨⟨(x, u), hxu, rfl⟩, fun x₀ hx₀ hne ↦ ?_⟩, ⟨hxu, fun u₀ hu₀ hne ↦ ?_⟩⟩
    · obtain ⟨⟨x₀', u₀⟩, hp₀, rfl⟩ := hx₀
      obtain ⟨p₁, hp₁, hseg⟩ := hcrit (x₀', u₀) hp₀ (fun h ↦ hne (congrArg Prod.fst h))
      exact ⟨p₁.1, ⟨p₁, hp₁, rfl⟩, (openSegment_fst_snd hseg).1⟩
    · obtain ⟨p₁, hp₁, hseg⟩ := hcrit (x, u₀) hu₀ (fun h ↦ hne (congrArg Prod.snd h))
      obtain ⟨a, b, ha, hb, hab, hcomb⟩ := hseg
      have hx1 : p₁.1 = x := by
        have h1 := congrArg Prod.fst hcomb
        simp only [Prod.smul_fst, Prod.fst_add] at h1
        have : b • (p₁.1 - x) = 0 := by
          rw [smul_sub]
          calc b • p₁.1 - b • x = (a • x + b • p₁.1) - (a + b) • x := by module
            _ = 0 := by rw [h1, hab, one_smul, sub_self]
        rcases smul_eq_zero.mp this with h0 | h0
        · exact absurd h0 hb.ne'
        · exact sub_eq_zero.mp h0
      refine ⟨p₁.2, ?_, a, b, ha, hb, hab, ?_⟩
      · change (x, p₁.2) ∈ G
        rw [← hx1]
        exact hp₁
      · have h2 := congrArg Prod.snd hcomb
        simpa using h2
  · rintro ⟨⟨_, hcritX⟩, ⟨hu, hcritS⟩⟩
    refine ⟨hu, fun p₀ hp₀ hne ↦ ?_⟩
    obtain ⟨x₀, u₀⟩ := p₀
    by_cases hx₀ : x₀ = x
    · subst hx₀
      have hne' : u₀ ≠ u := fun h ↦ hne (by rw [h])
      obtain ⟨u₁, hu₁, a, b, ha, hb, hab, hcomb⟩ := hcritS u₀ hp₀ hne'
      exact ⟨(x₀, u₁), hu₁, a, b, ha, hb, hab, by
        simp only [Prod.smul_mk, Prod.mk_add_mk, ← add_smul, hab, one_smul, hcomb]⟩
    obtain ⟨xb₁, ⟨⟨xb₁', ub₁⟩, hpb₁, rfl⟩, τ₀, τ, hτ₀, hτ, hττ, hxcomb⟩ :=
      hcritX x₀ ⟨(x₀, u₀), hp₀, rfl⟩ hx₀
    set w := τ₀ • u₀ + τ • ub₁ with hw
    have hwS : w ∈ productFiber G x := by
      have := hG hp₀ hpb₁ hτ₀.le hτ.le hττ
      simp only [Prod.smul_mk, Prod.mk_add_mk, hxcomb] at this
      exact this
    by_cases hwu : w = u
    · refine ⟨(xb₁', ub₁), hpb₁, τ₀, τ, hτ₀, hτ, hττ, ?_⟩
      simp only [Prod.smul_mk, Prod.mk_add_mk, hxcomb, ← hw, hwu]
    obtain ⟨u₁, hu₁, ν₀, μ, hν₀, hμ, hνμ, hucomb⟩ := hcritS w hwS hwu
    -- `(x, u) = ν₀ (x, w) + μ (x, u₁)` with `(x, w) = τ₀ (x₀, u₀) + τ (xb₁, ub₁)`
    have hc₀ : 0 < ν₀ * τ₀ := mul_pos hν₀ hτ₀
    have hcμ : 0 < ν₀ * τ + μ := add_pos (mul_pos hν₀ hτ) hμ
    have hne' : ν₀ * τ + μ ≠ 0 := hcμ.ne'
    have hsum : ν₀ * τ₀ + (ν₀ * τ + μ) = 1 := by
      rw [← add_assoc, ← mul_add, hττ, mul_one, hνμ]
    set q : E × F := ((ν₀ * τ) / (ν₀ * τ + μ)) • (xb₁', ub₁) + (μ / (ν₀ * τ + μ)) • (x, u₁)
      with hq
    have hqG : q ∈ G := hG hpb₁ hu₁ (by positivity) (by positivity) (by field_simp)
    refine ⟨q, hqG, ν₀ * τ₀, ν₀ * τ + μ, hc₀, hcμ, hsum, ?_⟩
    have hxcomb' : τ₀ • x₀ + τ • xb₁' = x := hxcomb
    have hscale : (ν₀ * τ + μ) • q = (ν₀ * τ) • (xb₁', ub₁) + μ • (x, u₁) := by
      rw [hq, smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ hne', mul_div_cancel₀ _ hne']
    have hxw : τ₀ • ((x₀, u₀) : E × F) + τ • (xb₁', ub₁) = (x, w) := by
      simp only [Prod.smul_mk, Prod.mk_add_mk, hxcomb', hw]
    calc (ν₀ * τ₀) • ((x₀, u₀) : E × F) + (ν₀ * τ + μ) • q
        = (ν₀ * τ₀) • ((x₀, u₀) : E × F) + ((ν₀ * τ) • (xb₁', ub₁) + μ • (x, u₁)) := by
          rw [hscale]
      _ = ν₀ • (τ₀ • ((x₀, u₀) : E × F) + τ • (xb₁', ub₁)) + μ • (x, u₁) := by module
      _ = ν₀ • ((x, w) : E × F) + μ • (x, u₁) := by rw [hxw]
      _ = (x, u) := by
          simp only [Prod.smul_mk, Prod.mk_add_mk, ← add_smul, hνμ, one_smul, hucomb]

end Products

/-! ## Proposition 2.44 -/

section Images

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] in
theorem combo_of_extension {x x₀ : E} {ε : ℝ} (hε : 0 < ε) :
    (ε / (1 + ε)) • x₀ + (1 / (1 + ε)) • (x + ε • (x - x₀)) = x := by
  have h1 : (1 + ε) ≠ 0 := by linarith
  match_scalars <;> (field_simp; try ring)

/-- **Proposition 2.44(a)**: `rint L(C) = L(rint C)` for linear `L` and convex `C`. -/
theorem intrinsicInterior_linear_image (L : E →ₗ[ℝ] F) {C : Set E} (hC : Convex ℝ C) :
    intrinsicInterior ℝ (L '' C) = L '' intrinsicInterior ℝ C := by
  have hLC : Convex ℝ (L '' C) := hC.linear_image L
  apply Subset.antisymm
  · intro y hy
    obtain ⟨c, hc, -⟩ := (intrinsicInterior_subset hy : y ∈ L '' C)
    obtain ⟨x', hx'⟩ := Set.Nonempty.intrinsicInterior hC ⟨c, hc⟩
    by_cases hLy : L x' = y
    · exact ⟨x', hx', hLy⟩
    obtain ⟨-, hcrit⟩ := (mem_intrinsicInterior_iff_openSegment hLC).mp hy
    obtain ⟨y₁, ⟨x₁, hx₁, rfl⟩, a, b, ha, hb, hab, hcomb⟩ :=
      hcrit (L x') ⟨x', intrinsicInterior_subset hx', rfl⟩ hLy
    refine ⟨b • x₁ + a • x', Convex.combo_mem_intrinsicInterior_normed hC (subset_closure hx₁)
      hx' hb.le ha (by linarith), ?_⟩
    rw [← hcomb, map_add, map_smul, map_smul, add_comm]
  · rintro _ ⟨x, hx, rfl⟩
    rw [mem_intrinsicInterior_iff_openSegment hLC]
    obtain ⟨hxC, hcrit⟩ := (mem_intrinsicInterior_iff_openSegment hC).mp hx
    refine ⟨⟨x, hxC, rfl⟩, ?_⟩
    rintro _ ⟨x₀, hx₀, rfl⟩ hne
    obtain ⟨x₁, hx₁, a, b, ha, hb, hab, hcomb⟩ :=
      hcrit x₀ hx₀ (fun h ↦ hne (by rw [h]))
    exact ⟨L x₁, ⟨x₁, hx₁, rfl⟩, a, b, ha, hb, hab, by rw [← hcomb, map_add, map_smul, map_smul]⟩

/-- **Proposition 2.44(b)**: if `rint D` meets the range of `L`, then
`rint L⁻¹(D) = L⁻¹(rint D)` and `cl L⁻¹(D) = L⁻¹(cl D)`. -/
theorem intrinsicInterior_linear_preimage (L : E →ₗ[ℝ] F) {D : Set F} (hD : Convex ℝ D)
    (hmeet : (intrinsicInterior ℝ D ∩ range L).Nonempty) :
    intrinsicInterior ℝ (L ⁻¹' D) = L ⁻¹' intrinsicInterior ℝ D ∧
      closure (L ⁻¹' D) = L ⁻¹' closure D := by
  have hLD : Convex ℝ (L ⁻¹' D) := hD.linear_preimage L
  obtain ⟨_, hyD, xb, rfl⟩ := hmeet
  have hLc : Continuous L := L.continuous_of_finiteDimensional
  refine ⟨Subset.antisymm ?_ ?_, Subset.antisymm ?_ ?_⟩
  · intro x hx
    change L x ∈ intrinsicInterior ℝ D
    by_cases hxb : x = xb
    · rw [hxb]; exact hyD
    have hxbD : xb ∈ L ⁻¹' D := (intrinsicInterior_subset hyD : L xb ∈ D)
    obtain ⟨ε, hε, hmem⟩ := exists_add_smul_sub_mem_of_mem_intrinsicInterior hx hxbD
    have hcomb := combo_of_extension (x := x) (x₀ := xb) hε
    have h := Convex.combo_mem_intrinsicInterior_normed hD (subset_closure hmem) hyD
      (a := 1 / (1 + ε)) (b := ε / (1 + ε)) (by positivity) (by positivity)
      (by field_simp)
    rw [← hcomb, map_add, map_smul, map_smul, add_comm]
    exact h
  · intro x hx
    rw [mem_intrinsicInterior_iff_openSegment hLD]
    have hLx : L x ∈ intrinsicInterior ℝ D := hx
    have hLxD : L x ∈ D := intrinsicInterior_subset hLx
    refine ⟨hLxD, fun x₀ hx₀ hne ↦ ?_⟩
    obtain ⟨ε, hε, hmem⟩ := exists_add_smul_sub_mem_of_mem_intrinsicInterior hLx
      (hx₀ : L x₀ ∈ D)
    refine ⟨x + ε • (x - x₀), ?_, ε / (1 + ε), 1 / (1 + ε), by positivity, by positivity,
      by field_simp; ring, combo_of_extension hε⟩
    change L (x + ε • (x - x₀)) ∈ D
    rw [map_add, map_smul, map_sub]
    exact hmem
  · exact closure_minimal (preimage_mono subset_closure) (isClosed_closure.preimage hLc)
  · intro x hx
    change L x ∈ closure D at hx
    have ht : Tendsto (fun t : ℝ ↦ x + t • (xb - x)) (𝓝[>] 0) (𝓝 x) := by
      have h : Tendsto (fun t : ℝ ↦ x + t • (xb - x)) (𝓝 0) (𝓝 (x + (0 : ℝ) • (xb - x))) :=
        (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
      rw [zero_smul, add_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with t ht
    change L (x + t • (xb - x)) ∈ D
    rw [map_add, map_smul, map_sub]
    exact intrinsicInterior_subset
      (Convex.add_smul_sub_mem_intrinsicInterior_normed hD hx hyD ht.1 ht.2.le)

end Images

/-! ## Exercise 2.45 -/

section SetAlgebra

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **Exercise 2.45(a)**: `rint(C₁ × C₂) = rint C₁ × rint C₂`. -/
theorem intrinsicInterior_prod {C₁ : Set E} {C₂ : Set F} (hC₁ : Convex ℝ C₁)
    (hC₂ : Convex ℝ C₂) :
    intrinsicInterior ℝ (C₁ ×ˢ C₂) = intrinsicInterior ℝ C₁ ×ˢ intrinsicInterior ℝ C₂ := by
  rcases C₂.eq_empty_or_nonempty with rfl | hne₂
  · simp
  rcases C₁.eq_empty_or_nonempty with rfl | hne₁
  · simp
  ext ⟨x, u⟩
  rw [mem_intrinsicInterior_prod_iff (hC₁.prod hC₂), fst_image_prod _ hne₂, mem_prod]
  constructor
  · rintro ⟨hx, hu⟩
    have hfib : productFiber (C₁ ×ˢ C₂) x = C₂ := by
      ext v
      simp [productFiber, intrinsicInterior_subset hx]
    rw [hfib] at hu
    exact ⟨hx, hu⟩
  · rintro ⟨hx, hu⟩
    have hfib : productFiber (C₁ ×ˢ C₂) x = C₂ := by
      ext v
      simp [productFiber, intrinsicInterior_subset hx]
    refine ⟨hx, ?_⟩
    rw [hfib]
    exact hu

/-- **Exercise 2.45(b)**: `rint(C₁ + C₂) = rint C₁ + rint C₂`. -/
theorem intrinsicInterior_add {C₁ C₂ : Set E} (hC₁ : Convex ℝ C₁) (hC₂ : Convex ℝ C₂) :
    intrinsicInterior ℝ (C₁ + C₂) = intrinsicInterior ℝ C₁ + intrinsicInterior ℝ C₂ := by
  set L : E × E →ₗ[ℝ] E := LinearMap.fst ℝ E E + LinearMap.snd ℝ E E
  have hsum : ∀ (A B : Set E), A + B = L '' (A ×ˢ B) := by
    intro A B
    rw [← image2_add, ← image_prod]
    rfl
  rw [hsum, hsum, intrinsicInterior_linear_image L (hC₁.prod hC₂),
    intrinsicInterior_prod hC₁ hC₂]

/-- **Exercise 2.45(c)**: `rint(λC) = λ rint C`. -/
theorem intrinsicInterior_smul {C : Set E} (hC : Convex ℝ C) (lam : ℝ) :
    intrinsicInterior ℝ (lam • C) = lam • intrinsicInterior ℝ C := by
  have h : ∀ A : Set E, lam • A = (lam • LinearMap.id : E →ₗ[ℝ] E) '' A := by
    intro A
    rw [← image_smul]
    rfl
  rw [h, h, intrinsicInterior_linear_image _ hC]

theorem intrinsicInterior_sub {C₁ C₂ : Set E} (hC₁ : Convex ℝ C₁) (hC₂ : Convex ℝ C₂) :
    intrinsicInterior ℝ (C₁ - C₂) = intrinsicInterior ℝ C₁ - intrinsicInterior ℝ C₂ := by
  have h : ∀ A B : Set E, A - B = A + (-1 : ℝ) • B := by
    intro A B
    rw [sub_eq_add_neg, neg_smul_set, one_smul]
  rw [h, h, intrinsicInterior_add hC₁ (hC₂.smul _), intrinsicInterior_smul hC₂]

end SetAlgebra

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem intrinsicInterior_eq_interior_of_affineSpan_eq_top {s : Set E}
    (h : affineSpan ℝ s = ⊤) : intrinsicInterior ℝ s = interior s := by
  ext z
  rw [mem_intrinsicInterior_iff_ball_normed, mem_interior_iff_mem_nhds, Metric.mem_nhds_iff, h]
  constructor
  · rintro ⟨-, r, hr, hball⟩
    exact ⟨r, hr, fun y hy ↦ hball y (AffineSubspace.mem_top ℝ E y) hy⟩
  · rintro ⟨r, hr, hball⟩
    exact ⟨hball (Metric.mem_ball_self hr), r, hr, fun y _ hy ↦ hball hy⟩

/-- **Exercise 2.45(d)**: `0 ∈ int(C₁ - C₂)` if and only if `0 ∈ rint(C₁ - C₂)`
and no hyperplane contains `C₁ ∪ C₂`. -/
theorem zero_mem_interior_sub_iff {C₁ C₂ : Set E} (hne₁ : C₁.Nonempty) (hne₂ : C₂.Nonempty) :
    (0 : E) ∈ interior (C₁ - C₂) ↔
      (0 : E) ∈ intrinsicInterior ℝ (C₁ - C₂) ∧ ¬∃ H, IsHyperplane H ∧ C₁ ∪ C₂ ⊆ H := by
  constructor
  · intro h0
    refine ⟨interior_subset_intrinsicInterior h0, ?_⟩
    rintro ⟨H, ⟨a, ha, α, rfl⟩, hsub⟩
    have hD : C₁ - C₂ ⊆ {x | ⟪a, x⟫_ℝ = 0} := by
      rintro _ ⟨x₁, hx₁, x₂, hx₂, rfl⟩
      have e₁ : ⟪a, x₁⟫_ℝ = α := hsub (Or.inl hx₁)
      have e₂ : ⟪a, x₂⟫_ℝ = α := hsub (Or.inr hx₂)
      change ⟪a, x₁ - x₂⟫_ℝ = 0
      rw [inner_sub_right, e₁, e₂, sub_self]
    have := interior_mono hD h0
    rw [interior_inner_eq_zero_eq_empty ha] at this
    exact this
  · rintro ⟨h0, hnoH⟩
    by_cases htop : affineSpan ℝ (C₁ - C₂) = ⊤
    · rwa [← intrinsicInterior_eq_interior_of_affineSpan_eq_top htop]
    exfalso
    apply hnoH
    have h0D : (0 : E) ∈ C₁ - C₂ := intrinsicInterior_subset h0
    have hdir : (affineSpan ℝ (C₁ - C₂)).direction ≠ ⊤ := fun h ↦
      htop ((AffineSubspace.direction_eq_top_iff_of_nonempty
        ⟨0, subset_affineSpan ℝ _ h0D⟩).mp h)
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (fun h ↦ hdir (Submodule.orthogonal_eq_bot_iff.mp h))
    have hzero : ∀ d ∈ C₁ - C₂, ⟪a, d⟫_ℝ = 0 := by
      intro d hd
      have hmem : d - 0 ∈ (affineSpan ℝ (C₁ - C₂)).direction :=
        AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ _ hd) (subset_affineSpan ℝ _ h0D)
      have := (Submodule.mem_orthogonal' _ a).mp ha _ hmem
      rwa [sub_zero] at this
    obtain ⟨x₂, hx₂⟩ := hne₂
    refine ⟨{x | ⟪a, x⟫_ℝ = ⟪a, x₂⟫_ℝ}, ⟨a, ha0, _, rfl⟩, ?_⟩
    rintro x (hx | hx)
    · have := hzero (x - x₂) (sub_mem_sub hx hx₂)
      rw [inner_sub_right] at this
      exact sub_eq_zero.mp this
    · obtain ⟨x₁, hx₁⟩ := hne₁
      have h1 := hzero (x₁ - x) (sub_mem_sub hx₁ hx)
      have h2 := hzero (x₁ - x₂) (sub_mem_sub hx₁ hx₂)
      rw [inner_sub_right] at h1 h2
      change ⟪a, x⟫_ℝ = ⟪a, x₂⟫_ℝ
      linarith

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Exercise 2.45(d)**: the condition holds in particular if `C₁ ∩ int C₂ ≠ ∅`
or `C₂ ∩ int C₁ ≠ ∅`. -/
theorem zero_mem_interior_sub_of_inter_interior {C₁ C₂ : Set E}
    (h : (C₁ ∩ interior C₂).Nonempty ∨ (C₂ ∩ interior C₁).Nonempty) :
    (0 : E) ∈ interior (C₁ - C₂) := by
  rcases h with ⟨x, hx₁, hx₂⟩ | ⟨x, hx₂, hx₁⟩
  · have hopen : IsOpen ((fun y ↦ x - y) '' interior C₂) :=
      (Homeomorph.subLeft x).isOpenMap _ isOpen_interior
    refine interior_maximal ?_ hopen ⟨x, hx₂, sub_self x⟩
    rintro _ ⟨y, hy, rfl⟩
    exact sub_mem_sub hx₁ (interior_subset hy)
  · have hopen : IsOpen ((fun y ↦ y - x) '' interior C₁) :=
      (Homeomorph.subRight x).isOpenMap _ isOpen_interior
    refine interior_maximal ?_ hopen ⟨x, hx₁, sub_self x⟩
    rintro _ ⟨y, hy, rfl⟩
    exact sub_mem_sub (interior_subset hy) hx₂

/-- A nonzero functional, nonpositive on a convex set `D` and negative somewhere
on it, exists exactly when `0 ∉ rint D` (the key step of 2.45(e)). -/
theorem exists_inner_nonpos_neg_of_zero_not_mem_intrinsicInterior {D : Set E}
    (hD : Convex ℝ D) (hne : D.Nonempty) (h0 : (0 : E) ∉ intrinsicInterior ℝ D) :
    ∃ b : E, (∀ d ∈ D, ⟪b, d⟫_ℝ ≤ 0) ∧ ∃ d ∈ D, ⟪b, d⟫_ℝ < 0 := by
  obtain ⟨p, hp⟩ := hne
  set V := (affineSpan ℝ D).direction with hV
  have hdirD : ∀ d ∈ D, d - p ∈ V := fun d hd ↦
    AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ _ hd) (subset_affineSpan ℝ _ hp)
  by_cases h0A : (0 : E) ∈ affineSpan ℝ D
  · have hDV : ∀ d ∈ D, d ∈ V := fun d hd ↦ by
      have := AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ _ hd) h0A
      rwa [vsub_eq_sub, sub_zero] at this
    set D' : Set E := D + (Vᗮ : Set E)
    have hD' : Convex ℝ D' := hD.add (Vᗮ).convex
    have h0D' : (0 : E) ∉ interior D' := by
      intro hint
      apply h0
      obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hint)
      have key : ∀ y ∈ V, dist y 0 < r → y ∈ D := by
        intro y hyV hy
        obtain ⟨d, hd, w, hw, hdw⟩ := hball hy
        have hwV : w ∈ V := by
          have : w = y - d := by rw [← hdw]; simp
          rw [this]
          exact V.sub_mem hyV (hDV d hd)
        have hw0 : w = 0 := by
          have := Submodule.inf_orthogonal_eq_bot V
          have hmem : w ∈ V ⊓ Vᗮ := ⟨hwV, hw⟩
          rw [this] at hmem
          exact hmem
        simp only [hw0, add_zero] at hdw
        rw [← hdw]
        exact hd
      refine mem_intrinsicInterior_iff_ball_normed.mpr ⟨key 0 V.zero_mem (by simpa using hr),
        r, hr, fun y hy hyz ↦ key y ?_ hyz⟩
      have := AffineSubspace.vsub_mem_direction hy h0A
      rwa [vsub_eq_sub, sub_zero] at this
    obtain ⟨b, hb0, hbD'⟩ := exists_inner_nonpos_of_zero_not_mem_interior hD' ⟨p, p, hp, 0,
      (Vᗮ).zero_mem, add_zero p⟩ h0D'
    have hbperp : ∀ w ∈ Vᗮ, ⟪b, w⟫_ℝ = 0 := by
      intro w hw
      have hle : ∀ t : ℝ, ⟪b, p⟫_ℝ + t * ⟪b, w⟫_ℝ ≤ 0 := by
        intro t
        have := hbD' (p + t • w) ⟨p, hp, t • w, (Vᗮ).smul_mem t hw, rfl⟩
        rwa [inner_add_right, real_inner_smul_right] at this
      by_contra hne
      have := hle ((1 - ⟪b, p⟫_ℝ) / ⟪b, w⟫_ℝ)
      rw [div_mul_cancel₀ _ hne] at this
      linarith
    have hbV : b ∈ V := by
      rw [← V.orthogonal_orthogonal]
      exact (Submodule.mem_orthogonal' _ b).mpr fun w hw ↦ hbperp w hw
    refine ⟨b, fun d hd ↦ hbD' d ⟨d, hd, 0, (Vᗮ).zero_mem, add_zero d⟩, ?_⟩
    by_contra hall
    push_neg at hall
    have hzero : ∀ d ∈ D, ⟪b, d⟫_ℝ = 0 := fun d hd ↦
      le_antisymm (hbD' d ⟨d, hd, 0, (Vᗮ).zero_mem, add_zero d⟩) (hall d hd)
    have hspan : ∀ v ∈ V, ⟪b, v⟫_ℝ = 0 := by
      intro v hv
      rw [hV, direction_affineSpan, vectorSpan_def] at hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨d₁, hd₁, d₂, hd₂, rfl⟩ := hx
        change ⟪b, d₁ - d₂⟫_ℝ = 0
        rw [inner_sub_right, hzero d₁ hd₁, hzero d₂ hd₂, sub_zero]
      | zero => simp
      | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
      | smul c x _ hx => rw [real_inner_smul_right, hx, mul_zero]
    exact hb0 (inner_self_eq_zero.mp (hspan b hbV))
  · have hpV : p ∉ V := by
      intro hpV
      apply h0A
      have := AffineSubspace.vadd_mem_of_mem_direction (V.neg_mem hpV) (subset_affineSpan ℝ _ hp)
      rwa [vadd_eq_add, neg_add_cancel] at this
    set w := p - V.starProjection p with hw
    have hwperp : w ∈ Vᗮ := Submodule.sub_starProjection_mem_orthogonal p
    have hw0 : w ≠ 0 := by
      intro h
      apply hpV
      have : p = V.starProjection p := sub_eq_zero.mp h
      rw [this]
      exact Submodule.starProjection_apply_mem _ _
    have hval : ∀ d ∈ D, ⟪w, d⟫_ℝ = ‖w‖ ^ 2 := by
      intro d hd
      have h1 : ⟪w, d - p⟫_ℝ = 0 := (Submodule.mem_orthogonal' _ w).mp hwperp _ (hdirD d hd)
      have h2 : ⟪w, V.starProjection p⟫_ℝ = 0 :=
        (Submodule.mem_orthogonal' _ w).mp hwperp _ (Submodule.starProjection_apply_mem V p)
      rw [inner_sub_right, sub_eq_zero] at h1
      rw [h1, ← real_inner_self_eq_norm_sq]
      conv_rhs => rw [hw]
      rw [inner_sub_right, h2, sub_zero]
    have hpos : 0 < ‖w‖ ^ 2 := by positivity
    refine ⟨-w, fun d hd ↦ ?_, p, hp, ?_⟩
    · rw [inner_neg_left, hval d hd]; linarith
    · rw [inner_neg_left, hval p hp]; linarith

/-- **Exercise 2.45(e)**: nonempty convex sets can be separated properly if and
only if `0 ∉ rint(C₁ - C₂)`, which holds exactly when `rint C₁ ∩ rint C₂ = ∅`. -/
theorem canBeSeparatedProperly_iff {C₁ C₂ : Set E} (hC₁ : Convex ℝ C₁) (hC₂ : Convex ℝ C₂)
    (hne₁ : C₁.Nonempty) (hne₂ : C₂.Nonempty) :
    (CanBeSeparatedProperly C₁ C₂ ↔ (0 : E) ∉ intrinsicInterior ℝ (C₁ - C₂)) ∧
      ((0 : E) ∉ intrinsicInterior ℝ (C₁ - C₂) ↔
        Disjoint (intrinsicInterior ℝ C₁) (intrinsicInterior ℝ C₂)) := by
  have hD : Convex ℝ (C₁ - C₂) := hC₁.sub hC₂
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨a, α, hsep, hprop⟩ h0
    obtain ⟨b, -, hb, hbD⟩ := inner_sub_nonpos_of_hyperplaneSeparates hsep
    have hneg : ∃ d ∈ C₁ - C₂, ⟪b, d⟫_ℝ < 0 := by
      by_contra hall
      push_neg at hall
      have hz : ∀ x₁ ∈ C₁, ∀ x₂ ∈ C₂, ⟪a, x₁⟫_ℝ = ⟪a, x₂⟫_ℝ := by
        intro x₁ h₁ x₂ h₂
        have e := le_antisymm (hbD _ (sub_mem_sub h₁ h₂)) (hall _ (sub_mem_sub h₁ h₂))
        rcases hb with rfl | rfl
        · rw [inner_sub_right] at e; linarith
        · rw [inner_neg_left, inner_sub_right] at e; linarith
      apply hprop
      obtain ⟨ha, (⟨h₁, h₂⟩ | ⟨h₂, h₁⟩)⟩ := hsep
      · constructor
        · intro x hx
          obtain ⟨y, hy⟩ := hne₂
          exact le_antisymm (h₁ x hx) (hz x hx y hy ▸ h₂ y hy)
        · intro x hx
          obtain ⟨y, hy⟩ := hne₁
          exact le_antisymm ((hz y hy x hx) ▸ h₁ y hy) (h₂ x hx)
      · constructor
        · intro x hx
          obtain ⟨y, hy⟩ := hne₂
          exact le_antisymm (hz x hx y hy ▸ h₂ y hy) (h₁ x hx)
        · intro x hx
          obtain ⟨y, hy⟩ := hne₁
          exact le_antisymm (h₂ x hx) ((hz y hy x hx) ▸ h₁ y hy)
    obtain ⟨d, hd, hbd⟩ := hneg
    obtain ⟨ε, hε, hmem⟩ := exists_add_smul_sub_mem_of_mem_intrinsicInterior h0 hd
    have := hbD _ hmem
    rw [zero_add, zero_sub, smul_neg, inner_neg_right, real_inner_smul_right] at this
    nlinarith
  · intro h0
    obtain ⟨b, hbD, d, hd, hbd⟩ :=
      exists_inner_nonpos_neg_of_zero_not_mem_intrinsicInterior hD (hne₁.sub hne₂) h0
    have hb0 : b ≠ 0 := by rintro rfl; simp at hbd
    obtain ⟨α, hα⟩ := hyperplaneSeparates_of_inner_nonpos hne₁ hne₂ hb0 hbD
    refine ⟨b, α, hα, fun ⟨h₁, h₂⟩ ↦ ?_⟩
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := hd
    have e₁ : ⟪b, x₁⟫_ℝ = α := h₁ hx₁
    have e₂ : ⟪b, x₂⟫_ℝ = α := h₂ hx₂
    rw [inner_sub_right, e₁, e₂, sub_self] at hbd
    exact lt_irrefl _ hbd
  · rw [intrinsicInterior_sub hC₁ hC₂, Set.disjoint_left]
    constructor
    · intro h x hx₁ hx₂
      exact h ⟨x, hx₁, x, hx₂, sub_self x⟩
    · rintro h ⟨x₁, hx₁, x₂, hx₂, h0⟩
      rw [sub_eq_zero] at h0
      exact h hx₁ (h0 ▸ hx₂)

end Euclidean

end RW
