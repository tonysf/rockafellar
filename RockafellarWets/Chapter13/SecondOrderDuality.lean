/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Second-order epi-differentiability in duality

Theorem 13.21.  The proof follows the book: the halved quotients
`φ_τ = ½Δ²_τ f(x̄ | v̄)` and `ψ_τ = ½Δ²_τ f*(v̄ | x̄)` are conjugate to each other
for `τ > 0`, and epi-convergence is preserved by conjugation (Theorem 11.34),
applied along sequences `τν ↓ 0`.
-/

import RockafellarWets.Chapter13.ConvexSecondSubderivatives
import RockafellarWets.Chapter11.ConjugateEpiConvergence
import RockafellarWets.Chapter11.SubgradientConjugacy

open Filter Set Topology Metric
open scoped InnerProductSpace

namespace RW

/-! ### Set limits under homeomorphisms and along positive sequences -/

section Limits

variable {ι X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem innerSetLimitAlong_image_homeomorph (T : X ≃ₜ Y) (l : Filter ι) (A : ι → Set X) :
    innerSetLimitAlong l (fun i ↦ T '' A i) = T '' innerSetLimitAlong l A := by
  ext y
  constructor
  · intro hy
    refine ⟨T.symm y, fun V hV ↦ ?_, T.apply_symm_apply y⟩
    have hV' : T '' V ∈ 𝓝 y := by
      rw [← T.apply_symm_apply y]
      exact T.isOpenMap.image_mem_nhds hV
    refine (hy _ hV').mono fun i hi ↦ ?_
    obtain ⟨z, ⟨a, ha, rfl⟩, haV⟩ := hi
    exact ⟨a, ha, (T.injective.mem_set_image).1 haV⟩
  · rintro ⟨x, hx, rfl⟩ V hV
    have hV' : T ⁻¹' V ∈ 𝓝 x := T.continuous.continuousAt.preimage_mem_nhds hV
    exact (hx _ hV').mono fun i ⟨a, ha, haV⟩ ↦ ⟨T a, mem_image_of_mem T ha, haV⟩

theorem outerSetLimitAlong_image_homeomorph (T : X ≃ₜ Y) (l : Filter ι) (A : ι → Set X) :
    outerSetLimitAlong l (fun i ↦ T '' A i) = T '' outerSetLimitAlong l A := by
  ext y
  constructor
  · intro hy
    refine ⟨T.symm y, fun V hV ↦ ?_, T.apply_symm_apply y⟩
    have hV' : T '' V ∈ 𝓝 y := by
      rw [← T.apply_symm_apply y]
      exact T.isOpenMap.image_mem_nhds hV
    refine (hy _ hV').mono fun i hi ↦ ?_
    obtain ⟨z, ⟨a, ha, rfl⟩, haV⟩ := hi
    exact ⟨a, ha, (T.injective.mem_set_image).1 haV⟩
  · rintro ⟨x, hx, rfl⟩ V hV
    have hV' : T ⁻¹' V ∈ 𝓝 x := T.continuous.continuousAt.preimage_mem_nhds hV
    exact (hx _ hV').mono fun i ⟨a, ha, haV⟩ ↦ ⟨T a, mem_image_of_mem T ha, haV⟩

theorem pkConvergesAlong_image_homeomorph_iff (T : X ≃ₜ Y) (l : Filter ι) (A : ι → Set X)
    (B : Set X) :
    PKConvergesAlong l (fun i ↦ T '' A i) (T '' B) ↔ PKConvergesAlong l A B := by
  unfold PKConvergesAlong
  rw [innerSetLimitAlong_image_homeomorph, outerSetLimitAlong_image_homeomorph,
    (T.injective.image_injective).eq_iff, (T.injective.image_injective).eq_iff]

/-- Convergence along `τ ↓ 0` can be tested with sequences of positive numbers tending to `0`. -/
theorem pkConvergesAlong_nhdsGT_iff [FirstCountableTopology X] {C : ℝ → Set X} {D : Set X} :
    PKConvergesAlong (𝓝[>] (0 : ℝ)) C D ↔
      ∀ τ : ℕ → ℝ, (∀ n, 0 < τ n) → Tendsto τ atTop (𝓝 0) → PKConverges (C ∘ τ) D := by
  rw [pkConvergesAlong_iff_forall_seq]
  constructor
  · intro h τ hτ hτ0
    exact h τ (tendsto_nhdsWithin_iff.2 ⟨hτ0, Eventually.of_forall hτ⟩)
  · intro h p hp
    obtain ⟨hp0, hpos⟩ := tendsto_nhdsWithin_iff.1 hp
    set τ : ℕ → ℝ := fun n ↦ if 0 < p n then p n else 1 / ((n : ℝ) + 1) with hτdef
    have hτpos : ∀ n, 0 < τ n := fun n ↦ by
      simp only [hτdef]
      split_ifs with h
      · exact h
      · positivity
    have heq : (fun n ↦ τ n) =ᶠ[atTop] p := by
      filter_upwards [hpos] with n hn
      simp only [hτdef, if_pos (show 0 < p n from hn)]
    have hτ0 : Tendsto τ atTop (𝓝 0) := hp0.congr' heq.symm
    have hconv := h τ hτpos hτ0
    have hC : (C ∘ τ) =ᶠ[atTop] (C ∘ p) := heq.fun_comp C
    exact ⟨(innerSetLimitAlong_congr hC).symm.trans hconv.1,
      (outerSetLimitAlong_congr hC).symm.trans hconv.2⟩

end Limits

/-! ### The halved quotients -/

section Halved

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `½Δ²_τ f(x̄ | v)(w) = τ⁻²[f(x̄ + τw) - f(x̄) - τ⟪v, w⟫]`. -/
noncomputable def halfSecondDifferenceQuotient (f : E → EReal) (x v : E) (τ : ℝ) (w : E) : EReal :=
  ((1 / 2 : ℝ) : EReal) * secondDifferenceQuotient f x v τ w

theorem halfSecondDifferenceQuotient_le_coe_iff {f : E → EReal} {x v w : E} {c τ α : ℝ}
    (hx : f x = c) (hτ : 0 < τ) :
    halfSecondDifferenceQuotient f x v τ w ≤ (α : EReal) ↔
      f (x + τ • w) ≤ ((c + τ * ⟪v, w⟫_ℝ + τ ^ 2 * α : ℝ) : EReal) := by
  have h2 : halfSecondDifferenceQuotient f x v τ w ≤ (α : EReal) ↔
      secondDifferenceQuotient f x v τ w ≤ ((2 * α : ℝ) : EReal) := by
    unfold halfSecondDifferenceQuotient
    constructor
    · intro h
      have := mul_le_mul_of_nonneg_left h (show (0 : EReal) ≤ ((2 : ℝ) : EReal) by norm_num)
      rwa [← mul_assoc, ← EReal.coe_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, EReal.coe_one,
        one_mul, ← EReal.coe_mul] at this
    · intro h
      have := mul_le_mul_of_nonneg_left h (show (0 : EReal) ≤ ((1 / 2 : ℝ) : EReal) by norm_num)
      rwa [← EReal.coe_mul, show (1 / 2 : ℝ) * (2 * α) = α by ring] at this
  rw [h2, secondDifferenceQuotient_le_coe_iff hx hτ]
  constructor <;> intro h <;> convert h using 3 <;> ring

theorem coe_le_halfSecondDifferenceQuotient_iff {f : E → EReal} {x v w : E} {c τ α : ℝ}
    (hx : f x = c) (hτ : 0 < τ) :
    (α : EReal) ≤ halfSecondDifferenceQuotient f x v τ w ↔
      ((c + τ * ⟪v, w⟫_ℝ + τ ^ 2 * α : ℝ) : EReal) ≤ f (x + τ • w) := by
  constructor
  · intro h
    by_contra hlt
    push_neg at hlt
    obtain ⟨b, hb1, hb2⟩ := EReal.exists_between_coe_real hlt
    have hτ2 : 0 < τ ^ 2 := by positivity
    have hb' : f (x + τ • w) ≤ ((c + τ * ⟪v, w⟫_ℝ + τ ^ 2 * ((b - c - τ * ⟪v, w⟫_ℝ) / τ ^ 2) :
        ℝ) : EReal) := by
      rw [show c + τ * ⟪v, w⟫_ℝ + τ ^ 2 * ((b - c - τ * ⟪v, w⟫_ℝ) / τ ^ 2) = b by field_simp; ring]
      exact hb1.le
    have := (halfSecondDifferenceQuotient_le_coe_iff hx hτ).2 hb'
    have hlt' : (b - c - τ * ⟪v, w⟫_ℝ) / τ ^ 2 < α := by
      rw [div_lt_iff₀ hτ2]
      have := EReal.coe_lt_coe_iff.1 hb2
      linarith
    exact absurd (h.trans this) (not_le.2 (EReal.coe_lt_coe_iff.2 hlt'))
  · intro h
    by_contra hlt
    push_neg at hlt
    obtain ⟨b, hb1, hb2⟩ := EReal.exists_between_coe_real hlt
    have := (halfSecondDifferenceQuotient_le_coe_iff hx hτ).1 hb1.le
    have hb2' : b < α := EReal.coe_lt_coe_iff.1 hb2
    have hτ2 : 0 < τ ^ 2 := by positivity
    have := h.trans this
    rw [EReal.coe_le_coe_iff] at this
    nlinarith

/-- The epigraph of `½h` is the image of the epigraph of `h` under `(w, β) ↦ (w, β/2)`. -/
noncomputable def halfHeightHomeomorph : E × ℝ ≃ₜ E × ℝ :=
  (Homeomorph.refl E).prodCongr (Homeomorph.mulLeft₀ (1 / 2 : ℝ) (by norm_num))

omit [InnerProductSpace ℝ E] in
theorem epigraph_half (h : E → EReal) :
    epigraph (fun w ↦ ((1 / 2 : ℝ) : EReal) * h w) = halfHeightHomeomorph '' epigraph h := by
  ext ⟨w, α⟩
  constructor
  · intro hw
    change ((1 / 2 : ℝ) : EReal) * h w ≤ (α : EReal) at hw
    refine ⟨(w, 2 * α), ?_, ?_⟩
    · change h w ≤ ((2 * α : ℝ) : EReal)
      have := mul_le_mul_of_nonneg_left hw (show (0 : EReal) ≤ ((2 : ℝ) : EReal) by norm_num)
      rwa [← mul_assoc, ← EReal.coe_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, EReal.coe_one,
        one_mul, ← EReal.coe_mul] at this
    · simp [halfHeightHomeomorph, Homeomorph.mulLeft₀]
  · rintro ⟨⟨u, β⟩, hu, heq⟩
    have heq' : u = w ∧ 1 / 2 * β = α := by
      simpa [halfHeightHomeomorph, Homeomorph.mulLeft₀] using heq
    obtain ⟨hu', hβ⟩ := heq'
    subst hu'
    change h u ≤ (β : EReal) at hu
    change ((1 / 2 : ℝ) : EReal) * h u ≤ (α : EReal)
    have := mul_le_mul_of_nonneg_left hu (show (0 : EReal) ≤ ((1 / 2 : ℝ) : EReal) by norm_num)
    rw [← EReal.coe_mul, hβ] at this
    exact this

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem mem_epigraph_half_iff (h : E → EReal) (w : E) (α : ℝ) :
    (w, α) ∈ epigraph (fun w ↦ ((1 / 2 : ℝ) : EReal) * h w) ↔ h w ≤ ((2 * α : ℝ) : EReal) := by
  change ((1 / 2 : ℝ) : EReal) * h w ≤ (α : EReal) ↔ _
  constructor
  · intro hw
    have := mul_le_mul_of_nonneg_left hw (show (0 : EReal) ≤ ((2 : ℝ) : EReal) by norm_num)
    rwa [← mul_assoc, ← EReal.coe_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, EReal.coe_one,
      one_mul, ← EReal.coe_mul] at this
  · intro hw
    have := mul_le_mul_of_nonneg_left hw (show (0 : EReal) ≤ ((1 / 2 : ℝ) : EReal) by norm_num)
    rwa [← EReal.coe_mul, show (1 / 2 : ℝ) * (2 * α) = α by ring] at this

theorem convex_epigraph_half {h : E → EReal} (hc : Convex ℝ (epigraph h)) :
    Convex ℝ (epigraph (fun w ↦ ((1 / 2 : ℝ) : EReal) * h w)) := by
  rw [epigraph_half]
  have : (halfHeightHomeomorph : E × ℝ ≃ₜ E × ℝ) =
      ((LinearMap.id : E →ₗ[ℝ] E).prodMap ((1 / 2 : ℝ) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) :
        E × ℝ → E × ℝ) := by
    funext p
    ext <;> simp [halfHeightHomeomorph, Homeomorph.mulLeft₀]
  rw [this]
  exact hc.linear_image _

/-- The epigraph of a halved quotient is the preimage of `epi f` under an affine map. -/
theorem epigraph_halfSecondDifferenceQuotient {f : E → EReal} {x v : E} {c τ : ℝ}
    (hx : f x = c) (hτ : 0 < τ) :
    epigraph (halfSecondDifferenceQuotient f x v τ) =
      (fun p : E × ℝ ↦ (x + τ • p.1, c + τ * ⟪v, p.1⟫_ℝ + τ ^ 2 * p.2)) ⁻¹' epigraph f := by
  ext ⟨w, α⟩
  rw [mem_epigraph_iff, halfSecondDifferenceQuotient_le_coe_iff hx hτ]
  rfl

theorem properties_halfSecondDifferenceQuotient {f : E → EReal} {x v : E} {c τ : ℝ}
    (hp : IsProper f) (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) (hx : f x = c)
    (hτ : 0 < τ) :
    IsProper (halfSecondDifferenceQuotient f x v τ) ∧
      LowerSemicontinuous (halfSecondDifferenceQuotient f x v τ) ∧
      Convex ℝ (epigraph (halfSecondDifferenceQuotient f x v τ)) := by
  have hT : Continuous fun p : E × ℝ ↦ (x + τ • p.1, c + τ * ⟪v, p.1⟫_ℝ + τ ^ 2 * p.2) := by
    fun_prop
  refine ⟨⟨⟨0, ?_⟩, fun w ↦ ?_⟩, ?_, ?_⟩
  · rw [halfSecondDifferenceQuotient, secondDifferenceQuotient_zero_right hx, mul_zero]
    exact EReal.zero_lt_top
  · have hne : secondDifferenceQuotient f x v τ w ≠ ⊥ := by
      rcases ereal_trichotomy (f (x + τ • w)) with h | h | ⟨r, h⟩
      · exact absurd h (hp.2 _).ne'
      · rw [secondDifferenceQuotient_of_top hτ.ne' hx h]
        exact top_ne_bot
      · rw [secondDifferenceQuotient_of_coe hx h]
        exact EReal.coe_ne_bot _
    rw [halfSecondDifferenceQuotient]
    rcases ereal_trichotomy (secondDifferenceQuotient f x v τ w) with h | h | ⟨r, h⟩
    · exact absurd h hne
    · rw [h, EReal.coe_mul_top_of_pos (by norm_num)]
      exact bot_lt_top
    · rw [h, ← EReal.coe_mul]
      exact EReal.bot_lt_coe _
  · apply lowerSemicontinuous_of_isClosed_epigraph_ereal
    rw [epigraph_halfSecondDifferenceQuotient hx hτ]
    exact (isClosed_epigraph_of_lsc_ereal f hl).preimage hT
  · rw [epigraph_halfSecondDifferenceQuotient hx hτ]
    rintro ⟨p1, p2⟩ hp' ⟨q1, q2⟩ hq a b ha hb hab
    have := hc hp' hq ha hb hab
    simp only [mem_preimage, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at this ⊢
    obtain rfl : b = 1 - a := by linarith
    convert this using 2
    · module
    · rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      ring

end Halved

/-! ### Theorem 13.21 -/

section Duality

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {x v : E}

/-- For `τ > 0` the halved quotients `½Δ²_τ f(x̄ | v̄)` and `½Δ²_τ f*(v̄ | x̄)` are conjugate. -/
theorem fenchelConjugate_halfSecondDifferenceQuotient (hp : IsProper f) (hl : LowerSemicontinuous f)
    (hc : Convex ℝ (epigraph f)) (hxv : v ∈ subdifferential f x) {τ : ℝ} (hτ : 0 < τ) :
    fenchelConjugate (halfSecondDifferenceQuotient f x v τ) =
      halfSecondDifferenceQuotient (fenchelConjugate f) v x τ := by
  obtain ⟨c, hx⟩ := hxv.1
  have hfs : fenchelConjugate f v = ((⟪v, x⟫_ℝ - c : ℝ) : EReal) :=
    (mem_subdifferential_iff_fenchelConjugate_eq hp hc hx).1 hxv
  have hps := isProper_fenchelConjugate hp hl hc
  have hτ2 : 0 < τ ^ 2 := by positivity
  funext z
  apply le_antisymm
  · by_contra hlt
    push_neg at hlt
    obtain ⟨b, hb1, hb2⟩ := EReal.exists_between_coe_real hlt
    have hψ := (halfSecondDifferenceQuotient_le_coe_iff hfs hτ).1 hb1.le
    have hφ : fenchelConjugate (halfSecondDifferenceQuotient f x v τ) z ≤ (b : EReal) := by
      rw [fenchelConjugate_le_coe_iff]
      intro w
      rw [coe_le_halfSecondDifferenceQuotient_iff hx hτ]
      have hfy := fenchel_young hp (x + τ • w) (v + τ • z)
      have hsne : fenchelConjugate f (v + τ • z) ≠ ⊤ :=
        ne_top_of_le_ne_top (EReal.coe_ne_top _) hψ
      have hsnb : fenchelConjugate f (v + τ • z) ≠ ⊥ := (hps.2 _).ne'
      set s := (fenchelConjugate f (v + τ • z)).toReal
      have hs : fenchelConjugate f (v + τ • z) = s := (EReal.coe_toReal hsne hsnb).symm
      rw [hs, EReal.coe_le_coe_iff] at hψ
      rw [hs] at hfy
      rcases ereal_trichotomy (f (x + τ • w)) with h | h | ⟨r, h⟩
      · exact absurd h (hp.2 _).ne'
      · rw [h]
        exact le_top
      · rw [h, ← EReal.coe_add, EReal.coe_le_coe_iff] at hfy
        rw [h, EReal.coe_le_coe_iff]
        have hexp : ⟪v + τ • z, x + τ • w⟫_ℝ = ⟪v, x⟫_ℝ + τ * ⟪v, w⟫_ℝ + τ * ⟪x, z⟫_ℝ +
            τ ^ 2 * ⟪z, w⟫_ℝ := by
          simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
            real_inner_comm x z]
          ring
        rw [hexp] at hfy
        nlinarith
    exact absurd hb2 (not_lt.2 hφ)
  · by_contra hlt
    push_neg at hlt
    obtain ⟨b, hb1, hb2⟩ := EReal.exists_between_coe_real hlt
    have hφ := (fenchelConjugate_le_coe_iff _ _ _).1 hb1.le
    have hψ : halfSecondDifferenceQuotient (fenchelConjugate f) v x τ z ≤ (b : EReal) := by
      rw [halfSecondDifferenceQuotient_le_coe_iff hfs hτ, fenchelConjugate_le_coe_iff]
      intro u
      have hw := hφ (τ⁻¹ • (u - x))
      rw [coe_le_halfSecondDifferenceQuotient_iff hx hτ, smul_smul, mul_inv_cancel₀ hτ.ne',
        one_smul, add_sub_cancel] at hw
      refine le_of_eq_of_le ?_ hw
      congr 1
      have hu : u = x + τ • (τ⁻¹ • (u - x)) := by
        rw [smul_smul, mul_inv_cancel₀ hτ.ne', one_smul, add_sub_cancel]
      conv_lhs => rw [hu]
      simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
        real_inner_comm x z]
      ring
    exact absurd hb2 (not_lt.2 hψ)

/-- One direction of **Theorem 13.21**, with the conjugacy relation. -/
theorem ProperlyTwiceEpiDifferentiableAt.fenchelConjugate (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) (hxv : v ∈ subdifferential f x)
    (h : ProperlyTwiceEpiDifferentiableAt f x v) :
    ProperlyTwiceEpiDifferentiableAt (RW.fenchelConjugate f) v x ∧
      RW.fenchelConjugate (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondSubderivative f x v w) =
        fun z ↦ ((1 / 2 : ℝ) : EReal) * secondSubderivative (RW.fenchelConjugate f) v x z := by
  obtain ⟨c, hx⟩ := hxv.1
  have hfs : RW.fenchelConjugate f v = ((⟪v, x⟫_ℝ - c : ℝ) : EReal) :=
    (mem_subdifferential_iff_fenchelConjugate_eq hp hc hx).1 hxv
  set L : E × ℝ ≃ₜ E × ℝ := halfHeightHomeomorph
  set φ₀ : E → EReal := fun w ↦ ((1 / 2 : ℝ) : EReal) * secondSubderivative f x v w
  set ψ₀ : E → EReal := fun z ↦
    ((1 / 2 : ℝ) : EReal) * secondSubderivative (RW.fenchelConjugate f) v x z
  -- the halved quotients epi-converge to `φ₀`
  have hPKφ : PKConvergesAlong (𝓝[>] (0 : ℝ))
      (fun τ ↦ epigraph (halfSecondDifferenceQuotient f x v τ)) (epigraph φ₀) := by
    have h1 := (pkConvergesAlong_image_homeomorph_iff L (𝓝[>] (0 : ℝ))
      (fun τ ↦ epigraph (secondDifferenceQuotient f x v τ))
      (epigraph (secondSubderivative f x v))).2 h.1.2.2
    have h2 : (fun τ ↦ L '' epigraph (secondDifferenceQuotient f x v τ)) =
        fun τ ↦ epigraph (halfSecondDifferenceQuotient f x v τ) :=
      funext fun τ ↦ (epigraph_half _).symm
    rw [h2, ← epigraph_half] at h1
    exact h1
  -- properties of `φ₀`
  have hφ0p : IsProper φ₀ := by
    obtain ⟨⟨w, hw⟩, hb⟩ := h.2
    refine ⟨⟨w, ?_⟩, fun z ↦ ?_⟩
    · simp only [φ₀]
      rcases ereal_trichotomy (secondSubderivative f x v w) with h1 | h1 | ⟨r, h1⟩
      · rw [h1, EReal.coe_mul_bot_of_pos (by norm_num)]
        exact bot_lt_top
      · rw [h1] at hw
        exact absurd hw (lt_irrefl _)
      · rw [h1, ← EReal.coe_mul]
        exact EReal.coe_lt_top _
    · rcases ereal_trichotomy (secondSubderivative f x v z) with h1 | h1 | ⟨r, h1⟩
      · exact absurd h1 (hb z).ne'
      · simp only [φ₀]
        rw [h1, EReal.coe_mul_top_of_pos (by norm_num)]
        exact bot_lt_top
      · simp only [φ₀]
        rw [h1, ← EReal.coe_mul]
        exact EReal.bot_lt_coe _
  have hφ0l : LowerSemicontinuous φ₀ := by
    apply lowerSemicontinuous_of_isClosed_epigraph_ereal
    rw [← hPKφ.outer_eq]
    exact isClosed_outerSetLimitAlong _ _
  have hφ0c : Convex ℝ (epigraph φ₀) :=
    convex_epigraph_half (convex_epigraph_secondSubderivative_of_convex hc hx h.1)
  -- conjugation along sequences
  have hPKψ : PKConvergesAlong (𝓝[>] (0 : ℝ))
      (fun τ ↦ epigraph (halfSecondDifferenceQuotient (RW.fenchelConjugate f) v x τ))
      (epigraph (RW.fenchelConjugate φ₀)) := by
    rw [pkConvergesAlong_nhdsGT_iff] at hPKφ ⊢
    intro τ hτ hτ0
    have hconv : EpiConverges (fun n ↦ halfSecondDifferenceQuotient f x v (τ n)) φ₀ :=
      hPKφ τ hτ hτ0
    have hprops := fun n ↦ properties_halfSecondDifferenceQuotient (v := v) hp hl hc hx (hτ n)
    have := hconv.fenchelConjugate (fun n ↦ (hprops n).1) (fun n ↦ (hprops n).2.1)
      (fun n ↦ (hprops n).2.2) hφ0p hφ0l hφ0c
    have heq : (fun n ↦ RW.fenchelConjugate (halfSecondDifferenceQuotient f x v (τ n))) =
        fun n ↦ halfSecondDifferenceQuotient (RW.fenchelConjugate f) v x (τ n) :=
      funext fun n ↦ fenchelConjugate_halfSecondDifferenceQuotient hp hl hc hxv (hτ n)
    rw [heq] at this
    exact this
  -- identification of the limit
  have hψ0 : ψ₀ = RW.fenchelConjugate φ₀ := by
    apply eq_of_epigraph_eq
    rw [← hPKψ.outer_eq, epigraph_half, epigraph_secondSubderivative,
      ← outerSetLimitAlong_image_homeomorph]
    congr 1
    funext τ
    exact (epigraph_half _).symm
  refine ⟨⟨⟨by rw [hfs]; exact EReal.coe_ne_bot _, by rw [hfs]; exact EReal.coe_ne_top _, ?_⟩, ?_⟩,
    hψ0.symm⟩
  · have hPK' : PKConvergesAlong (𝓝[>] (0 : ℝ))
        (fun τ ↦ L '' epigraph (secondDifferenceQuotient (RW.fenchelConjugate f) v x τ))
        (L '' epigraph (secondSubderivative (RW.fenchelConjugate f) v x)) := by
      have h3 : (fun τ ↦ L '' epigraph (secondDifferenceQuotient (RW.fenchelConjugate f) v x τ)) =
          fun τ ↦ epigraph (halfSecondDifferenceQuotient (RW.fenchelConjugate f) v x τ) :=
        funext fun τ ↦ (epigraph_half _).symm
      rw [h3, ← epigraph_half]
      change PKConvergesAlong _ _ (epigraph ψ₀)
      rw [hψ0]
      exact hPKψ
    exact (pkConvergesAlong_image_homeomorph_iff L _ _ _).1 hPK'
  · have hψp : IsProper ψ₀ := by
      rw [hψ0]
      exact isProper_fenchelConjugate hφ0p hφ0l hφ0c
    obtain ⟨⟨z, hz⟩, hb⟩ := hψp
    refine ⟨⟨z, ?_⟩, fun w ↦ ?_⟩
    · by_contra hge
      push_neg at hge
      rw [top_le_iff] at hge
      simp only [ψ₀, hge, EReal.coe_mul_top_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)] at hz
      exact lt_irrefl _ hz
    · by_contra hle
      push_neg at hle
      rw [le_bot_iff] at hle
      have := hb w
      simp only [ψ₀, hle, EReal.coe_mul_bot_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)] at this
      exact lt_irrefl _ this

/-- **Theorem 13.21**: for `f` lsc, proper and convex with `v̄ ∈ ∂f(x̄)` (so `v̄ ∈ dom f*` and
`x̄ ∈ ∂f*(v̄)`), `f` is properly twice epi-differentiable at `x̄` for `v̄` if and only if `f*` is
properly twice epi-differentiable at `v̄` for `x̄`, and then `½d²f(x̄ | v̄)` and
`½d²f*(v̄ | x̄)` are conjugate to each other. -/
theorem second_order_epi_differentiability_in_duality (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) (hxv : v ∈ subdifferential f x) :
    v ∈ effectiveDomain (RW.fenchelConjugate f) ∧ x ∈ subdifferential (RW.fenchelConjugate f) v ∧
      (ProperlyTwiceEpiDifferentiableAt f x v ↔
        ProperlyTwiceEpiDifferentiableAt (RW.fenchelConjugate f) v x) ∧
      (ProperlyTwiceEpiDifferentiableAt f x v →
        RW.fenchelConjugate (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondSubderivative f x v w) =
          (fun z ↦ ((1 / 2 : ℝ) : EReal) * secondSubderivative (RW.fenchelConjugate f) v x z) ∧
        RW.fenchelConjugate (fun z ↦ ((1 / 2 : ℝ) : EReal) *
          secondSubderivative (RW.fenchelConjugate f) v x z) =
          (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondSubderivative f x v w)) := by
  obtain ⟨c, hx⟩ := hxv.1
  have hfs : RW.fenchelConjugate f v = ((⟪v, x⟫_ℝ - c : ℝ) : EReal) :=
    (mem_subdifferential_iff_fenchelConjugate_eq hp hc hx).1 hxv
  have hps := isProper_fenchelConjugate hp hl hc
  have hls := lowerSemicontinuous_fenchelConjugate f
  have hcs := convex_epigraph_fenchelConjugate f
  have hxv' : x ∈ subdifferential (RW.fenchelConjugate f) v :=
    (mem_subdifferential_fenchelConjugate_iff hp hl hc x v).2 hxv
  have hff := fenchelConjugate_fenchelConjugate_eq hp hl hc
  refine ⟨by change RW.fenchelConjugate f v < ⊤; rw [hfs]; exact EReal.coe_lt_top _, hxv',
    ⟨fun h ↦ (h.fenchelConjugate hp hl hc hxv).1, fun h ↦ ?_⟩, fun h ↦ ?_⟩
  · have := (h.fenchelConjugate hps hls hcs hxv').1
    rwa [hff] at this
  · obtain ⟨h1, h2⟩ := h.fenchelConjugate hp hl hc hxv
    refine ⟨h2, ?_⟩
    have := (h1.fenchelConjugate hps hls hcs hxv').2
    rwa [hff] at this

end Duality

end RW
