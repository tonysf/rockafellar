/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: Monotone versus nonexpansive mappings

Proposition 12.11.  The one-to-one linear transformation
`J(x, v) = (v + x, v - x)` of `E × E` induces a one-to-one correspondence
`gph S = J(gph T)` between mappings `T` and `S`.  Under it, `S` is nonexpansive
exactly when `T` is monotone, and `S` is contractive exactly when `T` is
strictly monotone and single-valued on its domain.  The two mappings determine
each other by the formulas 12(2):

`S = I - 2I ∘ (I + T)⁻¹` and `T = (I - S)⁻¹ ∘ 2I - I`.

The key computation is 12(3): for corresponding pairs
`|z₁ - z₀|² - |w₁ - w₀|² = 4⟪v₁ - v₀, x₁ - x₀⟫`.
-/

import RockafellarWets.Chapter12.Resolvents

open Set
open scoped InnerProductSpace Pointwise

namespace RW

section Correspondence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem two_smul_inj {a b : E} (h : (2 : ℝ) • a = (2 : ℝ) • b) : a = b :=
  smul_right_injective E (two_ne_zero) h

/-- The linear transformation `J(x, v) = (v + x, v - x)` of Proposition 12.11,
with inverse `(z, w) ↦ (½(z - w), ½(z + w))`. -/
noncomputable def monotoneGraphJ : (E × E) ≃ₗ[ℝ] (E × E) where
  toFun p := (p.2 + p.1, p.2 - p.1)
  invFun q := ((2 : ℝ)⁻¹ • (q.1 - q.2), (2 : ℝ)⁻¹ • (q.1 + q.2))
  map_add' p q := by
    ext
    · simp only [Prod.fst_add, Prod.snd_add]; abel
    · simp only [Prod.fst_add, Prod.snd_add]; abel
  map_smul' c p := by
    ext
    · simp [smul_add]
    · simp [smul_sub]
  left_inv p := by
    ext
    · change (2 : ℝ)⁻¹ • ((p.2 + p.1) - (p.2 - p.1)) = p.1
      rw [show (p.2 + p.1) - (p.2 - p.1) = (2 : ℝ) • p.1 by rw [two_smul]; abel, smul_smul,
        inv_mul_cancel₀ two_ne_zero, one_smul]
    · change (2 : ℝ)⁻¹ • ((p.2 + p.1) + (p.2 - p.1)) = p.2
      rw [show (p.2 + p.1) + (p.2 - p.1) = (2 : ℝ) • p.2 by rw [two_smul]; abel, smul_smul,
        inv_mul_cancel₀ two_ne_zero, one_smul]
  right_inv q := by
    ext
    · change (2 : ℝ)⁻¹ • (q.1 + q.2) + (2 : ℝ)⁻¹ • (q.1 - q.2) = q.1
      rw [← smul_add, show (q.1 + q.2) + (q.1 - q.2) = (2 : ℝ) • q.1 by rw [two_smul]; abel,
        smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
    · change (2 : ℝ)⁻¹ • (q.1 + q.2) - (2 : ℝ)⁻¹ • (q.1 - q.2) = q.2
      rw [← smul_sub, show (q.1 + q.2) - (q.1 - q.2) = (2 : ℝ) • q.2 by rw [two_smul]; abel,
        smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

@[simp]
theorem monotoneGraphJ_apply (p : E × E) : monotoneGraphJ p = (p.2 + p.1, p.2 - p.1) := rfl

/-- The mapping `S` with `gph S = J(gph T)`. -/
def svCayley (T : E → Set E) : E → Set E :=
  fun z ↦ {w | ∃ x v, v ∈ T x ∧ v + x = z ∧ v - x = w}

/-- The mapping `T` with `gph T = J⁻¹(gph S)`. -/
def svCayleyInv (S : E → Set E) : E → Set E :=
  fun x ↦ {v | v - x ∈ S (v + x)}

omit [InnerProductSpace ℝ E] in
@[simp]
theorem mem_svCayley {T : E → Set E} {z w : E} :
    w ∈ svCayley T z ↔ ∃ x v, v ∈ T x ∧ v + x = z ∧ v - x = w :=
  Iff.rfl

omit [InnerProductSpace ℝ E] in
@[simp]
theorem mem_svCayleyInv {S : E → Set E} {x v : E} :
    v ∈ svCayleyInv S x ↔ v - x ∈ S (v + x) :=
  Iff.rfl

/-- **Proposition 12.11**: `gph S = J(gph T)`. -/
theorem svGraph_svCayley (T : E → Set E) :
    svGraph (svCayley T) = monotoneGraphJ '' svGraph T := by
  ext ⟨z, w⟩
  simp only [mem_svGraph, mem_svCayley, mem_image, monotoneGraphJ_apply, Prod.mk.injEq,
    Prod.exists]

/-- **Proposition 12.11**: `gph T = J⁻¹(gph S)`. -/
theorem svGraph_svCayleyInv (S : E → Set E) :
    svGraph (svCayleyInv S) = monotoneGraphJ ⁻¹' svGraph S := by
  ext ⟨x, v⟩
  simp only [mem_svGraph, mem_svCayleyInv, mem_preimage, monotoneGraphJ_apply]

theorem svCayleyInv_svCayley (T : E → Set E) : svCayleyInv (svCayley T) = T := by
  funext x
  ext v
  simp only [mem_svCayleyInv, mem_svCayley]
  constructor
  · rintro ⟨x', v', hv', h₁, h₂⟩
    have hv : v' = v := two_smul_inj (by
      rw [two_smul, two_smul]
      calc v' + v' = (v' + x') + (v' - x') := by abel
        _ = (v + x) + (v - x) := by rw [h₁, h₂]
        _ = v + v := by abel)
    have hx : x' = x := by
      subst hv
      have := congrArg (· - v') h₁
      simpa using this
    subst hv hx
    exact hv'
  · intro hv
    exact ⟨x, v, hv, rfl, rfl⟩

theorem svCayley_svCayleyInv (S : E → Set E) : svCayley (svCayleyInv S) = S := by
  funext z
  ext w
  simp only [mem_svCayley, mem_svCayleyInv]
  constructor
  · rintro ⟨x, v, hv, rfl, rfl⟩
    exact hv
  · intro hw
    refine ⟨(2 : ℝ)⁻¹ • (z - w), (2 : ℝ)⁻¹ • (z + w), ?_, ?_, ?_⟩
    · have h₁ : (2 : ℝ)⁻¹ • (z + w) - (2 : ℝ)⁻¹ • (z - w) = w := by
        rw [← smul_sub, show (z + w) - (z - w) = (2 : ℝ) • w by rw [two_smul]; abel, smul_smul,
          inv_mul_cancel₀ two_ne_zero, one_smul]
      have h₂ : (2 : ℝ)⁻¹ • (z + w) + (2 : ℝ)⁻¹ • (z - w) = z := by
        rw [← smul_add, show (z + w) + (z - w) = (2 : ℝ) • z by rw [two_smul]; abel, smul_smul,
          inv_mul_cancel₀ two_ne_zero, one_smul]
      rw [h₁, h₂]
      exact hw
    · rw [← smul_add, show (z + w) + (z - w) = (2 : ℝ) • z by rw [two_smul]; abel, smul_smul,
        inv_mul_cancel₀ two_ne_zero, one_smul]
    · rw [← smul_sub, show (z + w) - (z - w) = (2 : ℝ) • w by rw [two_smul]; abel, smul_smul,
        inv_mul_cancel₀ two_ne_zero, one_smul]

/-- **Proposition 12.11**: `J` induces a one-to-one correspondence between
mappings `T` and mappings `S`. -/
def monotoneNonexpansiveEquiv : (E → Set E) ≃ (E → Set E) where
  toFun := svCayley
  invFun := svCayleyInv
  left_inv := svCayleyInv_svCayley
  right_inv := svCayley_svCayleyInv

/-- The computation 12(3): `|z₁ - z₀|² - |w₁ - w₀|² = 4⟪v₁ - v₀, x₁ - x₀⟫` for
`(zᵢ, wᵢ) = J(xᵢ, vᵢ)`. -/
theorem norm_sq_sub_norm_sq_monotoneGraphJ (x₀ v₀ x₁ v₁ : E) :
    ‖(v₁ + x₁) - (v₀ + x₀)‖ ^ 2 - ‖(v₁ - x₁) - (v₀ - x₀)‖ ^ 2 =
      4 * ⟪v₁ - v₀, x₁ - x₀⟫_ℝ := by
  have e₁ : (v₁ + x₁) - (v₀ + x₀) = (v₁ - v₀) + (x₁ - x₀) := by abel
  have e₂ : (v₁ - x₁) - (v₀ - x₀) = (v₁ - v₀) - (x₁ - x₀) := by abel
  rw [e₁, e₂, norm_add_sq_real (v₁ - v₀) (x₁ - x₀), norm_sub_sq_real (v₁ - v₀) (x₁ - x₀)]
  ring

/-- **12(3).** For corresponding pairs, nonexpansivity of the pair is
equivalent to the monotonicity inequality. -/
theorem norm_le_norm_iff_inner_nonneg (x₀ v₀ x₁ v₁ : E) :
    ‖(v₁ - x₁) - (v₀ - x₀)‖ ≤ ‖(v₁ + x₁) - (v₀ + x₀)‖ ↔ 0 ≤ ⟪v₁ - v₀, x₁ - x₀⟫_ℝ := by
  have h := norm_sq_sub_norm_sq_monotoneGraphJ x₀ v₀ x₁ v₁
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  constructor <;> intro hle <;> nlinarith

/-- **12(3)**, strict form. -/
theorem norm_lt_norm_iff_inner_pos (x₀ v₀ x₁ v₁ : E) :
    ‖(v₁ - x₁) - (v₀ - x₀)‖ < ‖(v₁ + x₁) - (v₀ + x₀)‖ ↔ 0 < ⟪v₁ - v₀, x₁ - x₀⟫_ℝ := by
  have h := norm_sq_sub_norm_sq_monotoneGraphJ x₀ v₀ x₁ v₁
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)]
  constructor <;> intro hle <;> nlinarith

/-- **Proposition 12.11.** `S` is nonexpansive if and only if `T` is monotone. -/
theorem svNonexpansive_svCayley_iff {T : E → Set E} :
    SvNonexpansive (svCayley T) ↔ SvMonotone T := by
  constructor
  · intro hS x₀ v₀ h₀ x₁ v₁ h₁
    exact (norm_le_norm_iff_inner_nonneg x₀ v₀ x₁ v₁).1
      (hS (⟨x₀, v₀, h₀, rfl, rfl⟩ : v₀ - x₀ ∈ svCayley T (v₀ + x₀))
        (⟨x₁, v₁, h₁, rfl, rfl⟩ : v₁ - x₁ ∈ svCayley T (v₁ + x₁)))
  · rintro hT z₀ w₀ ⟨x₀, v₀, h₀, rfl, rfl⟩ z₁ w₁ ⟨x₁, v₁, h₁, rfl, rfl⟩
    exact (norm_le_norm_iff_inner_nonneg x₀ v₀ x₁ v₁).2 (hT h₀ h₁)

/-- **Proposition 12.11.** `S` is contractive if and only if `T` is strictly
monotone and single-valued on its domain. -/
theorem svContractive_svCayley_iff {T : E → Set E} :
    SvContractive (svCayley T) ↔
      SvStrictlyMonotone T ∧ ∀ x v₀ v₁, v₀ ∈ T x → v₁ ∈ T x → v₀ = v₁ := by
  constructor
  · rintro ⟨hS, hlt⟩
    have hT : SvMonotone T := svNonexpansive_svCayley_iff.1 hS
    have hmem : ∀ {x v}, v ∈ T x → v - x ∈ svCayley T (v + x) :=
      fun {x v} hv ↦ ⟨x, v, hv, rfl, rfl⟩
    refine ⟨fun x₀ v₀ h₀ x₁ v₁ h₁ hx ↦ ?_, fun x v₀ v₁ h₀ h₁ ↦ ?_⟩
    · by_cases hz : v₁ + x₁ = v₀ + x₀
      · exfalso
        have hw := hS.eq_of_mem (hmem h₀) (hz ▸ hmem h₁)
        apply hx
        apply two_smul_inj
        rw [two_smul, two_smul]
        calc x₀ + x₀ = (v₀ + x₀) - (v₀ - x₀) := by abel
          _ = (v₁ + x₁) - (v₁ - x₁) := by rw [← hz, hw]
          _ = x₁ + x₁ := by abel
      · exact (norm_lt_norm_iff_inner_pos x₀ v₀ x₁ v₁).1 (hlt (hmem h₀) (hmem h₁) hz)
    · by_contra hne
      have hz : v₁ + x ≠ v₀ + x := fun h ↦ hne (add_right_cancel h).symm
      have h := hlt (hmem h₀) (hmem h₁) hz
      rw [show (v₁ - x) - (v₀ - x) = (v₁ + x) - (v₀ + x) by abel] at h
      exact lt_irrefl _ h
  · rintro ⟨hT, hsingle⟩
    refine ⟨svNonexpansive_svCayley_iff.2 hT.svMonotone, ?_⟩
    rintro z₀ w₀ ⟨x₀, v₀, h₀, rfl, rfl⟩ z₁ w₁ ⟨x₁, v₁, h₁, rfl, rfl⟩ hz
    refine (norm_lt_norm_iff_inner_pos x₀ v₀ x₁ v₁).2 (hT h₀ h₁ fun hx ↦ hz ?_)
    subst hx
    rw [hsingle x₀ v₀ v₁ h₀ h₁]

/-- **Proposition 12.11**, from the side of `S`: the mapping `T` with
`gph T = J⁻¹(gph S)` is monotone if and only if `S` is nonexpansive. -/
theorem svMonotone_svCayleyInv_iff {S : E → Set E} :
    SvMonotone (svCayleyInv S) ↔ SvNonexpansive S := by
  conv_rhs => rw [← svCayley_svCayleyInv S]
  exact svNonexpansive_svCayley_iff.symm

/-- **Proposition 12.11**, from the side of `S`: `S` is contractive if and
only if the corresponding `T` is strictly monotone and single-valued on its
domain. -/
theorem svContractive_iff_svCayleyInv {S : E → Set E} :
    SvContractive S ↔ SvStrictlyMonotone (svCayleyInv S) ∧
      ∀ x v₀ v₁, v₀ ∈ svCayleyInv S x → v₁ ∈ svCayleyInv S x → v₀ = v₁ := by
  conv_lhs => rw [← svCayley_svCayleyInv S]
  exact svContractive_svCayley_iff

/-- **Formula 12(2)**, first part: `S = I - 2I ∘ (I + T)⁻¹`. -/
theorem svCayley_eq_sub_two_smul_svResolvent (T : E → Set E) :
    svCayley T = fun z ↦ ({z} : Set E) - (2 : ℝ) • svResolvent T 1 z := by
  funext z
  ext w
  simp only [mem_svCayley, mem_sub, mem_singleton_iff, mem_smul_set, mem_svResolvent, one_smul]
  constructor
  · rintro ⟨x, v, hv, rfl, rfl⟩
    exact ⟨v + x, rfl, (2 : ℝ) • x, ⟨x, ⟨v, hv, add_comm x v⟩, rfl⟩, by rw [two_smul]; abel⟩
  · rintro ⟨_, rfl, _, ⟨x, ⟨v, hv, rfl⟩, rfl⟩, rfl⟩
    exact ⟨x, v, hv, add_comm v x, by rw [two_smul]; abel⟩

/-- **Formula 12(2)**, second part: `T = (I - S)⁻¹ ∘ 2I - I` for the mapping
`T` with `gph T = J⁻¹(gph S)`. -/
theorem svCayleyInv_eq (S : E → Set E) :
    svCayleyInv S = fun x ↦ svInv (fun z ↦ ({z} : Set E) - S z) ((2 : ℝ) • x) - {x} := by
  funext x
  ext v
  simp only [mem_svCayleyInv, mem_sub, mem_singleton_iff, mem_svInv]
  constructor
  · intro hv
    exact ⟨v + x, ⟨v + x, rfl, v - x, hv, by rw [two_smul]; abel⟩, x, rfl, by abel⟩
  · rintro ⟨u, ⟨c, hc, w, hw, huw⟩, y, hy, hv⟩
    subst hc hy hv
    have hw' : w = (c - y) - y := by
      rw [two_smul] at huw
      rw [sub_sub, ← huw]; abel
    rw [show c - y + y = c by abel, ← hw']
    exact hw

/-- **Formula 12(2)**, second part, for `S = svCayley T`: `T = (I - S)⁻¹ ∘ 2I - I`. -/
theorem eq_svCayley_formula (T : E → Set E) :
    T = fun x ↦ svInv (fun z ↦ ({z} : Set E) - svCayley T z) ((2 : ℝ) • x) - {x} := by
  conv_lhs => rw [← svCayleyInv_svCayley T]
  exact svCayleyInv_eq (svCayley T)

/-- The domain of `S = svCayley T` is the domain of the resolvent `(I + T)⁻¹`. -/
theorem svDom_svCayley (T : E → Set E) : svDom (svCayley T) = svDom (svResolvent T 1) := by
  ext z
  simp only [mem_svDom]
  constructor
  · rintro ⟨w, x, v, hv, rfl, rfl⟩
    exact ⟨x, mem_svResolvent.2 ⟨v, hv, by rw [one_smul, add_comm]⟩⟩
  · rintro ⟨x, hx⟩
    obtain ⟨v, hv, hz⟩ := mem_svResolvent.1 hx
    rw [one_smul] at hz
    exact ⟨v - x, x, v, hv, by rw [← hz, add_comm], rfl⟩

end Correspondence

end RW
