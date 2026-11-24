/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: Strong monotonicity

Definition 12.53, Proposition 12.54, Corollary 12.55 and Theorem 12.56.

A mapping `T` is strongly monotone with constant `σ` when
`⟪v₁ - v₀, x₁ - x₀⟫ ≥ σ|x₁ - x₀|²` on its graph, equivalently when `T - σI` is
monotone (`svStronglyMonotoneWith_iff_svMonotone_svSubId`).  For maximal
monotone `T` and `σ > 0`, the mapping `T - σI` is again maximal monotone and
`T⁻¹ = (σI + (T - σI))⁻¹` is the Yosida `σ`-regularization of `(T - σI)⁻¹`, so
it is single-valued everywhere and Lipschitz with constant `1/σ`
(Proposition 12.54).  Corollary 12.55 is the same statement for `T⁻¹`.

Theorem 12.56 concerns `P_τ = I - τ(I + T⁻¹)⁻¹ = (1 - τ)I + τ(I + T)⁻¹`.  The
estimate `|P_τ(z₁) - P_τ(z₀)| ≤ (|1 - τ + τc| + τc)|z₁ - z₀|` with
`c = 1/(2(1 + σ))` is obtained from the observation that strong monotonicity
places `Δx = (I + T)⁻¹(z₁) - (I + T)⁻¹(z₀)` in the ball of radius `c|Δz|` around
`cΔz`.  This is the book's bound 12(10), and it gives both cases of 12(9).
-/

import RockafellarWets.Chapter12.YosidaRegularization

open Set
open scoped InnerProductSpace Pointwise

namespace RW

section StrongMonotonicity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Definition 12.53**, with a fixed constant: `T` is strongly monotone with
constant `σ` if `⟪v₁ - v₀, x₁ - x₀⟫ ≥ σ|x₁ - x₀|²` whenever `v₀ ∈ T(x₀)` and
`v₁ ∈ T(x₁)`. -/
def SvStronglyMonotoneWith (σ : ℝ) (T : E → Set E) : Prop :=
  ∀ ⦃x₀ v₀ : E⦄, v₀ ∈ T x₀ → ∀ ⦃x₁ v₁ : E⦄, v₁ ∈ T x₁ →
    σ * ‖x₁ - x₀‖ ^ 2 ≤ ⟪v₁ - v₀, x₁ - x₀⟫_ℝ

/-- **Definition 12.53 (strong monotonicity).** `T` is strongly monotone if it
is strongly monotone with some constant `σ > 0`. -/
def SvStronglyMonotone (T : E → Set E) : Prop :=
  ∃ σ, 0 < σ ∧ SvStronglyMonotoneWith σ T

/-- The mapping `T - σI`. -/
def svSubId (T : E → Set E) (σ : ℝ) : E → Set E :=
  fun x ↦ T x - {σ • x}

@[simp]
theorem mem_svSubId {T : E → Set E} {σ : ℝ} {x w : E} :
    w ∈ svSubId T σ x ↔ w + σ • x ∈ T x := by
  simp only [svSubId, mem_sub, mem_singleton_iff]
  constructor
  · rintro ⟨v, hv, _, rfl, rfl⟩
    rwa [sub_add_cancel]
  · intro h
    exact ⟨_, h, _, rfl, add_sub_cancel_right w _⟩

private theorem inner_shift_identity (σ : ℝ) (x₀ x₁ v₀ v₁ : E) :
    ⟪(v₁ - σ • x₁) - (v₀ - σ • x₀), x₁ - x₀⟫_ℝ =
      ⟪v₁ - v₀, x₁ - x₀⟫_ℝ - σ * ‖x₁ - x₀‖ ^ 2 := by
  have e : (v₁ - σ • x₁) - (v₀ - σ • x₀) = (v₁ - v₀) - σ • (x₁ - x₀) := by module
  rw [e, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]

/-- **Definition 12.53**, the equivalence of the two forms: `T` is strongly
monotone with constant `σ` exactly when `T - σI` is monotone. -/
theorem svStronglyMonotoneWith_iff_svMonotone_svSubId {T : E → Set E} {σ : ℝ} :
    SvStronglyMonotoneWith σ T ↔ SvMonotone (svSubId T σ) := by
  constructor
  · intro h x₀ w₀ h₀ x₁ w₁ h₁
    rw [mem_svSubId] at h₀ h₁
    have := h h₀ h₁
    have e := inner_shift_identity σ x₀ x₁ (w₀ + σ • x₀) (w₁ + σ • x₁)
    simp only [add_sub_cancel_right] at e
    linarith
  · intro h x₀ v₀ h₀ x₁ v₁ h₁
    have h₀' : v₀ - σ • x₀ ∈ svSubId T σ x₀ := by rwa [mem_svSubId, sub_add_cancel]
    have h₁' : v₁ - σ • x₁ ∈ svSubId T σ x₁ := by rwa [mem_svSubId, sub_add_cancel]
    have := h h₀' h₁'
    rw [inner_shift_identity] at this
    linarith

/-- **Definition 12.53** as printed: `T` is strongly monotone if and only if
`T - σI` is monotone for some `σ > 0`. -/
theorem svStronglyMonotone_iff_exists_svMonotone_svSubId {T : E → Set E} :
    SvStronglyMonotone T ↔ ∃ σ, 0 < σ ∧ SvMonotone (svSubId T σ) := by
  simp only [SvStronglyMonotone, svStronglyMonotoneWith_iff_svMonotone_svSubId]

theorem SvStronglyMonotoneWith.mono {T : E → Set E} {σ σ' : ℝ}
    (h : SvStronglyMonotoneWith σ T) (hσ : σ' ≤ σ) : SvStronglyMonotoneWith σ' T :=
  fun _ _ h₀ _ _ h₁ ↦ (mul_le_mul_of_nonneg_right hσ (sq_nonneg _)).trans (h h₀ h₁)

theorem SvStronglyMonotoneWith.svMonotone {T : E → Set E} {σ : ℝ}
    (h : SvStronglyMonotoneWith σ T) (hσ : 0 ≤ σ) : SvMonotone T :=
  fun _ _ h₀ _ _ h₁ ↦ (mul_nonneg hσ (sq_nonneg _)).trans (h h₀ h₁)

theorem svStronglyMonotoneWith_zero_iff {T : E → Set E} :
    SvStronglyMonotoneWith 0 T ↔ SvMonotone T := by
  constructor
  · exact fun h ↦ h.svMonotone le_rfl
  · intro h x₀ v₀ h₀ x₁ v₁ h₁
    rw [zero_mul]
    exact h h₀ h₁

/-- Strong monotonicity with a positive constant implies strict
monotonicity. -/
theorem SvStronglyMonotoneWith.svStrictlyMonotone {T : E → Set E} {σ : ℝ}
    (h : SvStronglyMonotoneWith σ T) (hσ : 0 < σ) : SvStrictlyMonotone T := by
  intro x₀ v₀ h₀ x₁ v₁ h₁ hx
  have hn : 0 < ‖x₁ - x₀‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hx))
  exact (mul_pos hσ (pow_pos hn 2)).trans_le (h h₀ h₁)

theorem SvStronglyMonotone.svStrictlyMonotone {T : E → Set E} (h : SvStronglyMonotone T) :
    SvStrictlyMonotone T := by
  obtain ⟨σ, hσ, h⟩ := h
  exact h.svStrictlyMonotone hσ

theorem SvStronglyMonotoneWith.mono_graph {S T : E → Set E} {σ : ℝ}
    (h : SvStronglyMonotoneWith σ T) (hST : ∀ x, S x ⊆ T x) : SvStronglyMonotoneWith σ S :=
  fun _ _ h₀ _ _ h₁ ↦ h (hST _ h₀) (hST _ h₁)

/-- For strongly monotone `T` with constant `σ ≥ 0`, maximal monotonicity of
`T` passes to `T - σI`: a proper monotone extension `T̄₀` of `T - σI` would give
the proper monotone extension `T̄₀ + σI` of `T`. -/
theorem SvMaximalMonotone.svMaximalMonotone_svSubId {T : E → Set E} {σ : ℝ}
    (hT : SvMaximalMonotone T) (hσ : 0 ≤ σ) (hs : SvStronglyMonotoneWith σ T) :
    SvMaximalMonotone (svSubId T σ) := by
  refine svMaximalMonotone_iff_forall_inner_nonneg.2
    ⟨svStronglyMonotoneWith_iff_svMonotone_svSubId.1 hs, fun x w h ↦ ?_⟩
  rw [mem_svSubId]
  refine hT.mem_of_forall_inner_nonneg fun x' v' hv' ↦ ?_
  have h' := h x' (v' - σ • x') (by rwa [mem_svSubId, sub_add_cancel])
  have e : (w + σ • x) - v' = (w - (v' - σ • x')) + σ • (x - x') := by module
  rw [e, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  exact add_nonneg h' (mul_nonneg hσ (sq_nonneg _))

/-- The inverse of `T` is the Yosida `σ`-regularization of `(T - σI)⁻¹`, that is
`T⁻¹ = (σI + (T - σI))⁻¹`. -/
theorem svInv_eq_svYosida_svInv_svSubId (T : E → Set E) (σ : ℝ) :
    svInv T = svYosida (svInv (svSubId T σ)) σ := by
  funext z
  ext x
  simp only [mem_svInv, mem_svYosida, mem_svSubId]
  constructor
  · intro hx
    exact ⟨z - σ • x, by rwa [sub_add_cancel], by abel⟩
  · rintro ⟨w, hw, rfl⟩
    rwa [add_comm]

/-- Strong monotonicity of `T⁻¹` with constant `σ`, written on the graph of `T`
as in Corollary 12.55: `⟪v₁ - v₀, x₁ - x₀⟫ ≥ σ|v₁ - v₀|²`. -/
theorem svStronglyMonotoneWith_svInv_iff {T : E → Set E} {σ : ℝ} :
    SvStronglyMonotoneWith σ (svInv T) ↔
      ∀ ⦃x₀ v₀ : E⦄, v₀ ∈ T x₀ → ∀ ⦃x₁ v₁ : E⦄, v₁ ∈ T x₁ →
        σ * ‖v₁ - v₀‖ ^ 2 ≤ ⟪v₁ - v₀, x₁ - x₀⟫_ℝ := by
  constructor
  · intro h x₀ v₀ h₀ x₁ v₁ h₁
    rw [real_inner_comm]
    exact h h₀ h₁
  · intro h v₀ x₀ h₀ v₁ x₁ h₁
    rw [real_inner_comm]
    exact h h₀ h₁

variable [FiniteDimensional ℝ E]

/-- **Proposition 12.54 (consequences of strong monotonicity).** If a maximal
monotone `T` is strongly monotone with constant `σ > 0`, then `T` is strictly
monotone, there is a unique `x̄` with `T(x̄) ∋ 0`, and `T⁻¹` is single-valued
everywhere and Lipschitz continuous globally with constant `κ = 1/σ`. -/
theorem SvMaximalMonotone.consequences_of_strongMonotonicity {T : E → Set E} {σ : ℝ}
    (hT : SvMaximalMonotone T) (hσ : 0 < σ) (hs : SvStronglyMonotoneWith σ T) :
    SvStrictlyMonotone T ∧ (∃! x, (0 : E) ∈ T x) ∧
      ∃ s : E → E, LipschitzWith (Real.toNNReal σ⁻¹) s ∧ ∀ v, svInv T v = {s v} := by
  have h₀ : SvMaximalMonotone (svInv (svSubId T σ)) :=
    (hT.svMaximalMonotone_svSubId hσ.le hs).inv
  have hinv : ∀ v, svInv T v = {yosidaMap (svInv (svSubId T σ)) σ v} := by
    intro v
    rw [svInv_eq_svYosida_svInv_svSubId T σ, h₀.svYosida_eq_fun hσ]
  refine ⟨hs.svStrictlyMonotone hσ, ?_, _, h₀.lipschitzWith_yosidaMap hσ, hinv⟩
  refine ⟨yosidaMap (svInv (svSubId T σ)) σ 0, ?_, fun y hy ↦ ?_⟩
  · have h := hinv 0
    have hm : yosidaMap (svInv (svSubId T σ)) σ 0 ∈ svInv T 0 := by
      rw [h]
      exact mem_singleton _
    exact hm
  · have hm : y ∈ svInv T 0 := hy
    rw [hinv 0] at hm
    exact hm

/-- **Proposition 12.54**, the solution mapping of `T(x) ∋ v` as a single
function: for maximal monotone `T` strongly monotone with constant `σ > 0`,
every equation `T(x) ∋ v` has exactly one solution, and the solution depends
Lipschitz continuously on `v` with constant `1/σ`. -/
theorem SvMaximalMonotone.existsUnique_mem_of_strongMonotonicity {T : E → Set E} {σ : ℝ}
    (hT : SvMaximalMonotone T) (hσ : 0 < σ) (hs : SvStronglyMonotoneWith σ T) (v : E) :
    ∃! x, v ∈ T x := by
  obtain ⟨-, -, s, -, hsv⟩ := hT.consequences_of_strongMonotonicity hσ hs
  refine ⟨s v, ?_, fun y hy ↦ ?_⟩
  · have hm : s v ∈ svInv T v := by rw [hsv v]; exact mem_singleton _
    exact hm
  · have hm : y ∈ svInv T v := hy
    rwa [hsv v] at hm

/-- **Corollary 12.55 (inverse strong monotonicity).** If `T` is maximal
monotone and `T⁻¹` is strongly monotone with constant `σ > 0`, i.e.
`⟪v₁ - v₀, x₁ - x₀⟫ ≥ σ|v₁ - v₀|²` whenever `v₀ ∈ T(x₀)`, `v₁ ∈ T(x₁)`, then `T`
is single-valued (everywhere) and Lipschitz continuous with constant `1/σ`. -/
theorem SvMaximalMonotone.inverse_strong_monotonicity {T : E → Set E} {σ : ℝ}
    (hT : SvMaximalMonotone T) (hσ : 0 < σ)
    (hs : ∀ ⦃x₀ v₀ : E⦄, v₀ ∈ T x₀ → ∀ ⦃x₁ v₁ : E⦄, v₁ ∈ T x₁ →
      σ * ‖v₁ - v₀‖ ^ 2 ≤ ⟪v₁ - v₀, x₁ - x₀⟫_ℝ) :
    ∃ s : E → E, LipschitzWith (Real.toNNReal σ⁻¹) s ∧ ∀ x, T x = {s x} := by
  have hs' : SvStronglyMonotoneWith σ (svInv T) := by
    intro v₀ x₀ h₀ v₁ x₁ h₁
    rw [real_inner_comm]
    exact hs h₀ h₁
  obtain ⟨-, -, s, hsl, hsv⟩ := hT.inv.consequences_of_strongMonotonicity hσ hs'
  exact ⟨s, hsl, hsv⟩

end StrongMonotonicity

section RelaxedResolvents

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The mapping `P_τ = I - τ(I + T⁻¹)⁻¹` of Theorem 12.56. -/
def svRelaxedResolvent (T : E → Set E) (τ : ℝ) : E → Set E :=
  fun z ↦ ({z} : Set E) - τ • svResolvent (svInv T) 1 z

/-- **Theorem 12.56**, the two expressions for `P_τ`, which agree for every
mapping by Lemma 12.14: `I - τ(I + T⁻¹)⁻¹ = (1 - τ)I + τ(I + T)⁻¹`. -/
theorem svRelaxedResolvent_eq (T : E → Set E) (τ : ℝ) :
    svRelaxedResolvent T τ = fun z ↦ (1 - τ) • ({z} : Set E) + τ • svResolvent T 1 z := by
  funext z
  rw [svRelaxedResolvent, ← sub_svResolvent_eq_svResolvent_svInv]
  ext w
  simp only [mem_sub, mem_add, mem_singleton_iff, mem_smul_set, smul_set_singleton,
    exists_eq_left]
  constructor
  · rintro ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    exact ⟨τ • x, ⟨x, hx, rfl⟩, by module⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨τ • (z - x), ⟨z - x, ⟨x, hx, rfl⟩, rfl⟩, by module⟩

/-- The single-valued form `P_τ(z) = (1 - τ)z + τ(I + T)⁻¹(z)`. -/
noncomputable def relaxedResolventMap (T : E → Set E) (τ : ℝ) (z : E) : E :=
  (1 - τ) • z + τ • resolventMap T 1 z

/-- The contraction bound `|1 - τ + τc| + τc` with `c = 1/(2(1 + σ))`, the right
side of 12(10). -/
noncomputable def relaxedResolventBound (σ τ : ℝ) : ℝ :=
  |1 - τ + τ / (2 * (1 + σ))| + τ / (2 * (1 + σ))

/-- The key estimate behind 12(10): if `xᵢ + vᵢ = zᵢ` with `vᵢ ∈ T(xᵢ)` for a
mapping strongly monotone with constant `σ ≥ 0`, then
`|(1 - τ)Δz + τΔx| ≤ (|1 - τ + τc| + τc)|Δz|` for `τ ≥ 0`, `c = 1/(2(1 + σ))`. -/
theorem norm_relaxed_sub_le {T : E → Set E} {σ τ : ℝ} (hσ : 0 ≤ σ) (hτ : 0 ≤ τ)
    (hs : SvStronglyMonotoneWith σ T) {x₀ x₁ z₀ z₁ : E}
    (h₀ : z₀ - x₀ ∈ T x₀) (h₁ : z₁ - x₁ ∈ T x₁) :
    ‖((1 - τ) • z₁ + τ • x₁) - ((1 - τ) • z₀ + τ • x₀)‖ ≤
      relaxedResolventBound σ τ * ‖z₁ - z₀‖ := by
  set a := x₁ - x₀
  set d := z₁ - z₀
  set c := 1 / (2 * (1 + σ)) with hc
  have h1σ : 0 < 1 + σ := by linarith
  have hc0 : 0 ≤ c := by positivity
  have hmono := hs h₀ h₁
  have e₁ : (z₁ - x₁) - (z₀ - x₀) = d - a := by simp only [a, d]; abel
  rw [e₁, inner_sub_left, real_inner_self_eq_norm_sq] at hmono
  -- `⟪d, a⟫ ≥ (1 + σ)|a|²`
  have hda : (1 + σ) * ‖a‖ ^ 2 ≤ ⟪d, a⟫_ℝ := by linarith
  -- `|a - cd| ≤ c|d|`
  have hball : ‖a - c • d‖ ≤ c * ‖d‖ := by
    have hsq : ‖a - c • d‖ ^ 2 ≤ (c * ‖d‖) ^ 2 := by
      rw [norm_sub_sq_real, norm_smul, real_inner_smul_right, Real.norm_of_nonneg hc0,
        real_inner_comm]
      have h2c : 2 * c * (1 + σ) = 1 := by rw [hc]; field_simp
      nlinarith [h2c, hda, sq_nonneg ‖a‖]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
  have e₂ : ((1 - τ) • z₁ + τ • x₁) - ((1 - τ) • z₀ + τ • x₀) =
      (1 - τ + τ * c) • d + τ • (a - c • d) := by
    simp only [a, d]
    module
  rw [e₂]
  calc ‖(1 - τ + τ * c) • d + τ • (a - c • d)‖
      ≤ ‖(1 - τ + τ * c) • d‖ + ‖τ • (a - c • d)‖ := norm_add_le _ _
    _ = |1 - τ + τ * c| * ‖d‖ + τ * ‖a - c • d‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_of_nonneg hτ]
    _ ≤ |1 - τ + τ * c| * ‖d‖ + τ * (c * ‖d‖) := by gcongr
    _ = relaxedResolventBound σ τ * ‖d‖ := by
        simp only [relaxedResolventBound, hc]
        ring_nf

/-- The threshold `τ̄ = 1 + 1/(1 + 2σ)` of 12(9). -/
noncomputable def relaxedResolventThreshold (σ : ℝ) : ℝ := 1 + 1 / (1 + 2 * σ)

theorem relaxedResolventBound_nonneg {σ τ : ℝ} (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) :
    0 ≤ relaxedResolventBound σ τ := by
  unfold relaxedResolventBound
  have h1 : 0 < 1 + σ := by linarith
  have : 0 ≤ τ / (2 * (1 + σ)) := by positivity
  exact add_nonneg (abs_nonneg _) this

/-- For a merely monotone mapping (`σ = 0`) the bound is `1` on `[0, 2]`. -/
theorem relaxedResolventBound_zero {τ : ℝ} (hτ2 : τ ≤ 2) :
    relaxedResolventBound 0 τ = 1 := by
  unfold relaxedResolventBound
  rw [abs_of_nonneg (by linarith)]
  ring

/-- **12(9)**, first alternative: `1 - τσ/(1 + σ)` when `0 ≤ τ ≤ τ̄`. -/
theorem relaxedResolventBound_of_le_threshold {σ τ : ℝ} (hσ : 0 ≤ σ)
    (h : τ ≤ relaxedResolventThreshold σ) :
    relaxedResolventBound σ τ = 1 - τ * σ / (1 + σ) := by
  unfold relaxedResolventBound
  unfold relaxedResolventThreshold at h
  have h1 : 0 < 1 + σ := by linarith
  have h2 : 0 < 1 + 2 * σ := by linarith
  have hτ' : τ * (1 + 2 * σ) ≤ 2 * (1 + σ) := by
    have := mul_le_mul_of_nonneg_right h h2.le
    rw [add_mul, one_div, inv_mul_cancel₀ h2.ne'] at this
    linarith
  have hnn : 0 ≤ 1 - τ + τ / (2 * (1 + σ)) := by
    rw [show 1 - τ + τ / (2 * (1 + σ)) = (2 * (1 + σ) - τ * (1 + 2 * σ)) / (2 * (1 + σ)) by
      field_simp; ring]
    exact div_nonneg (by linarith) (by positivity)
  rw [abs_of_nonneg hnn]
  field_simp
  ring

/-- **12(9)**, second alternative: `τ - 1` when `τ̄ ≤ τ`. -/
theorem relaxedResolventBound_of_threshold_le {σ τ : ℝ} (hσ : 0 ≤ σ)
    (h : relaxedResolventThreshold σ ≤ τ) :
    relaxedResolventBound σ τ = τ - 1 := by
  unfold relaxedResolventBound
  unfold relaxedResolventThreshold at h
  have h1 : 0 < 1 + σ := by linarith
  have h2 : 0 < 1 + 2 * σ := by linarith
  have hτ' : 2 * (1 + σ) ≤ τ * (1 + 2 * σ) := by
    have := mul_le_mul_of_nonneg_right h h2.le
    rw [add_mul, one_div, inv_mul_cancel₀ h2.ne'] at this
    linarith
  have hnp : 1 - τ + τ / (2 * (1 + σ)) ≤ 0 := by
    rw [show 1 - τ + τ / (2 * (1 + σ)) = (2 * (1 + σ) - τ * (1 + 2 * σ)) / (2 * (1 + σ)) by
      field_simp; ring]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  rw [abs_of_nonpos hnp]
  ring

/-- **Theorem 12.56**, the lowest bound: `1/(1 + 2σ)` is attained at `τ̄` and no
bound with `τ ≥ 0` is lower. -/
theorem relaxedResolventBound_threshold {σ : ℝ} (hσ : 0 ≤ σ) :
    relaxedResolventBound σ (relaxedResolventThreshold σ) = 1 / (1 + 2 * σ) := by
  rw [relaxedResolventBound_of_threshold_le hσ le_rfl, relaxedResolventThreshold]
  ring

theorem one_div_le_relaxedResolventBound {σ : ℝ} (hσ : 0 ≤ σ) (τ : ℝ) :
    1 / (1 + 2 * σ) ≤ relaxedResolventBound σ τ := by
  have h1 : 0 < 1 + σ := by linarith
  have h2 : 0 < 1 + 2 * σ := by linarith
  rcases le_total τ (relaxedResolventThreshold σ) with h | h
  · rw [relaxedResolventBound_of_le_threshold hσ h]
    unfold relaxedResolventThreshold at h
    have hτ' : τ * (1 + 2 * σ) ≤ 2 * (1 + σ) := by
      have := mul_le_mul_of_nonneg_right h h2.le
      rw [add_mul, one_div, inv_mul_cancel₀ h2.ne'] at this
      linarith
    rw [div_le_iff₀ h2]
    have e : (1 - τ * σ / (1 + σ)) * (1 + 2 * σ) =
        1 + 2 * σ - σ * (τ * (1 + 2 * σ)) / (1 + σ) := by
      field_simp
    rw [e]
    have : σ * (τ * (1 + 2 * σ)) / (1 + σ) ≤ σ * (2 * (1 + σ)) / (1 + σ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hτ' hσ) h1.le
    have e2 : σ * (2 * (1 + σ)) / (1 + σ) = 2 * σ := by field_simp
    linarith
  · rw [relaxedResolventBound_of_threshold_le hσ h]
    unfold relaxedResolventThreshold at h
    linarith

theorem relaxedResolventBound_lt_one {σ τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) (hτ2 : τ < 2) :
    relaxedResolventBound σ τ < 1 := by
  rcases le_total τ (relaxedResolventThreshold σ) with h | h
  · rw [relaxedResolventBound_of_le_threshold hσ.le h]
    have : 0 < τ * σ / (1 + σ) := by positivity
    linarith
  · rw [relaxedResolventBound_of_threshold_le hσ.le h]
    linarith

theorem relaxedResolventBound_pos {σ : ℝ} (hσ : 0 ≤ σ) (τ : ℝ) :
    0 < relaxedResolventBound σ τ :=
  (by have : 0 < 1 + 2 * σ := by linarith
      positivity : (0 : ℝ) < 1 / (1 + 2 * σ)).trans_le (one_div_le_relaxedResolventBound hσ τ)

variable [FiniteDimensional ℝ E]

theorem SvMaximalMonotone.sub_resolventMap_mem {T : E → Set E} (hT : SvMaximalMonotone T)
    (z : E) : z - resolventMap T 1 z ∈ T (resolventMap T 1 z) := by
  obtain ⟨v, hv, hxv⟩ :=
    (hT.resolventMap_eq_iff (z := z) (x := resolventMap T 1 z) one_pos).1 rfl
  rw [one_smul] at hxv
  have : z - resolventMap T 1 z = v := by rw [sub_eq_iff_eq_add']; exact hxv.symm
  rwa [this]

/-- **Theorem 12.56**: for maximal monotone `T`, `P_τ` is single-valued
everywhere, with value `(1 - τ)z + τ(I + T)⁻¹(z)`. -/
theorem SvMaximalMonotone.svRelaxedResolvent_eq_singleton {T : E → Set E}
    (hT : SvMaximalMonotone T) (τ : ℝ) (z : E) :
    svRelaxedResolvent T τ z = {relaxedResolventMap T τ z} := by
  rw [svRelaxedResolvent_eq]
  dsimp only
  rw [hT.svResolvent_eq_singleton_resolventMap one_pos z,
    smul_set_singleton, smul_set_singleton, singleton_add_singleton, relaxedResolventMap]

/-- The other expression `P_τ(z) = z - τ(I + T⁻¹)⁻¹(z)` of the single-valued map. -/
theorem SvMaximalMonotone.relaxedResolventMap_eq_sub {T : E → Set E}
    (hT : SvMaximalMonotone T) (τ : ℝ) (z : E) :
    relaxedResolventMap T τ z = z - τ • resolventMap (svInv T) 1 z := by
  have h := hT.svRelaxedResolvent_eq_singleton τ z
  rw [svRelaxedResolvent, hT.inv.svResolvent_eq_singleton_resolventMap one_pos z,
    smul_set_singleton, singleton_sub_singleton] at h
  exact (singleton_eq_singleton_iff.1 h).symm

/-- The general Lipschitz estimate 12(10): for maximal monotone `T` strongly
monotone with constant `σ ≥ 0` and `τ ≥ 0`, `P_τ` is Lipschitz continuous with
constant `(|1 + (1 + 2σ)(1 - τ)| + τ)/(2(1 + σ)) = |1 - τ + τc| + τc`. -/
theorem SvMaximalMonotone.lipschitzWith_relaxedResolventMap {T : E → Set E} {σ τ : ℝ}
    (hT : SvMaximalMonotone T) (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) (hs : SvStronglyMonotoneWith σ T) :
    LipschitzWith (Real.toNNReal (relaxedResolventBound σ τ)) (relaxedResolventMap T τ) := by
  refine LipschitzWith.of_dist_le_mul fun z₁ z₀ ↦ ?_
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (relaxedResolventBound_nonneg hσ hτ)]
  exact norm_relaxed_sub_le hσ hτ hs (hT.sub_resolventMap_mem z₀) (hT.sub_resolventMap_mem z₁)

/-- The book's form of the bound 12(10). -/
theorem relaxedResolventBound_eq_book (σ τ : ℝ) (hσ : 0 ≤ σ) :
    relaxedResolventBound σ τ = (|1 + (1 + 2 * σ) * (1 - τ)| + τ) / (2 * (1 + σ)) := by
  have h1 : 0 < 1 + σ := by linarith
  have h2 : 0 < 2 * (1 + σ) := by linarith
  unfold relaxedResolventBound
  have e : 1 - τ + τ / (2 * (1 + σ)) = (1 + (1 + 2 * σ) * (1 - τ)) / (2 * (1 + σ)) := by
    field_simp
    ring
  rw [e, abs_div, abs_of_pos h2]
  field_simp

/-- The fixed points of `P_τ`, `τ ≠ 0`, are the solutions of `T(x) ∋ 0`. -/
theorem SvMaximalMonotone.relaxedResolventMap_eq_self_iff {T : E → Set E}
    (hT : SvMaximalMonotone T) {τ : ℝ} (hτ : τ ≠ 0) {z : E} :
    relaxedResolventMap T τ z = z ↔ (0 : E) ∈ T z := by
  have e : relaxedResolventMap T τ z = z ↔ resolventMap T 1 z = z := by
    unfold relaxedResolventMap
    constructor
    · intro h
      have h' : τ • (resolventMap T 1 z - z) = 0 := by
        rw [smul_sub]
        rw [← sub_eq_zero] at h
        rw [← h]
        module
      rcases smul_eq_zero.1 h' with h'' | h''
      · exact absurd h'' hτ
      · exact sub_eq_zero.1 h''
    · intro h
      rw [h]
      module
  rw [e, hT.resolventMap_eq_iff one_pos]
  constructor
  · rintro ⟨v, hv, hzv⟩
    rw [one_smul, add_eq_left] at hzv
    rwa [← hzv]
  · intro h
    exact ⟨0, h, by simp⟩

/-- **Theorem 12.56 (contractions from strongly monotone mappings)**, first
assertion: for maximal monotone `T` and `τ ∈ (0, 2]`, the mapping
`P_τ = I - τ(I + T⁻¹)⁻¹ = (1 - τ)I + τ(I + T)⁻¹` is single-valued and
nonexpansive, and its fixed points are the solutions of `T(x) ∋ 0`. -/
theorem SvMaximalMonotone.relaxedResolvent_nonexpansive {T : E → Set E}
    (hT : SvMaximalMonotone T) {τ : ℝ} (hτ : 0 < τ) (hτ2 : τ ≤ 2) :
    svRelaxedResolvent T τ = (fun z ↦ (1 - τ) • ({z} : Set E) + τ • svResolvent T 1 z) ∧
      svRelaxedResolvent T τ = (fun z ↦ ({relaxedResolventMap T τ z} : Set E)) ∧
      SvNonexpansive (svRelaxedResolvent T τ) ∧ LipschitzWith 1 (relaxedResolventMap T τ) ∧
      {z | relaxedResolventMap T τ z = z} = svInv T 0 := by
  have hL : LipschitzWith 1 (relaxedResolventMap T τ) := by
    have h := hT.lipschitzWith_relaxedResolventMap le_rfl hτ.le
      (svStronglyMonotoneWith_zero_iff.2 hT.1)
    rwa [relaxedResolventBound_zero hτ2, Real.toNNReal_one] at h
  have hfun : svRelaxedResolvent T τ = fun z ↦ ({relaxedResolventMap T τ z} : Set E) :=
    funext (hT.svRelaxedResolvent_eq_singleton τ)
  refine ⟨svRelaxedResolvent_eq T τ, hfun, ?_, hL, ?_⟩
  · rw [hfun]
    exact svNonexpansive_singleton_iff.2 hL
  · ext z
    exact hT.relaxedResolventMap_eq_self_iff hτ.ne'

/-- **Theorem 12.56**, strongly monotone case: if `T` is maximal monotone and
strongly monotone with constant `σ > 0`, then for `τ ∈ (0, 2)` the mapping `P_τ`
is contractive with the Lipschitz bounds 12(9), namely `1 - τσ/(1 + σ)` for
`0 < τ ≤ τ̄` and `τ - 1` for `τ̄ ≤ τ < 2`, where `τ̄ = 1 + 1/(1 + 2σ)`.  The
lowest of these bounds is `lip P_τ̄ ≤ 1/(1 + 2σ)`, and `P = (I + T)⁻¹` is
contractive with `lip P ≤ 1/(1 + σ)`. -/
theorem SvMaximalMonotone.contractions_of_strongMonotonicity {T : E → Set E} {σ : ℝ}
    (hT : SvMaximalMonotone T) (hσ : 0 < σ) (hs : SvStronglyMonotoneWith σ T) :
    (∀ τ, 0 < τ → τ < 2 → SvContractive (svRelaxedResolvent T τ)) ∧
      (∀ τ, 0 < τ → τ ≤ relaxedResolventThreshold σ →
        LipschitzWith (Real.toNNReal (1 - τ * σ / (1 + σ))) (relaxedResolventMap T τ)) ∧
      (∀ τ, relaxedResolventThreshold σ ≤ τ → τ < 2 →
        LipschitzWith (Real.toNNReal (τ - 1)) (relaxedResolventMap T τ)) ∧
      LipschitzWith (Real.toNNReal (1 / (1 + 2 * σ)))
        (relaxedResolventMap T (relaxedResolventThreshold σ)) ∧
      (∀ τ, 0 < τ → τ < 2 → 1 / (1 + 2 * σ) ≤ relaxedResolventBound σ τ) ∧
      SvContractive (svResolvent T 1) ∧
      LipschitzWith (Real.toNNReal (1 / (1 + σ))) (resolventMap T 1) := by
  have hthr : 0 < relaxedResolventThreshold σ := by
    unfold relaxedResolventThreshold
    have : 0 < 1 + 2 * σ := by linarith
    positivity
  have hcontr : ∀ τ, 0 < τ → τ < 2 → SvContractive (svRelaxedResolvent T τ) := by
    intro τ hτ hτ2
    rw [funext (hT.svRelaxedResolvent_eq_singleton τ)]
    have hL := hT.lipschitzWith_relaxedResolventMap hσ.le hτ.le hs
    have hb := relaxedResolventBound_lt_one hσ hτ hτ2
    have hb0 := relaxedResolventBound_nonneg hσ.le hτ.le
    refine svContractive_singleton_iff.2 ⟨?_, fun z₀ z₁ hz ↦ ?_⟩
    · exact hL.weaken (by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hb0, NNReal.coe_one]
        exact hb.le)
    · have h := hL.dist_le_mul z₁ z₀
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hb0] at h
      rw [dist_eq_norm, dist_eq_norm]
      have hn : 0 < ‖z₁ - z₀‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
      calc ‖relaxedResolventMap T τ z₁ - relaxedResolventMap T τ z₀‖
          ≤ relaxedResolventBound σ τ * ‖z₁ - z₀‖ := h
        _ < 1 * ‖z₁ - z₀‖ := mul_lt_mul_of_pos_right hb hn
        _ = ‖z₁ - z₀‖ := one_mul _
  have hP : ∀ z, relaxedResolventMap T 1 z = resolventMap T 1 z := by
    intro z
    simp [relaxedResolventMap]
  have h1thr : 1 ≤ relaxedResolventThreshold σ := by
    unfold relaxedResolventThreshold
    have : 0 < 1 + 2 * σ := by linarith
    have : 0 < 1 / (1 + 2 * σ) := by positivity
    linarith
  refine ⟨hcontr, fun τ hτ h ↦ ?_, fun τ h _ ↦ ?_, ?_,
    fun τ _ _ ↦ one_div_le_relaxedResolventBound hσ.le τ, ?_, ?_⟩
  · have hL := hT.lipschitzWith_relaxedResolventMap hσ.le hτ.le hs
    rwa [relaxedResolventBound_of_le_threshold hσ.le h] at hL
  · have hL := hT.lipschitzWith_relaxedResolventMap hσ.le (hthr.le.trans h) hs
    rwa [relaxedResolventBound_of_threshold_le hσ.le h] at hL
  · have hL := hT.lipschitzWith_relaxedResolventMap hσ.le hthr.le hs
    rwa [relaxedResolventBound_threshold hσ.le] at hL
  · have h := hcontr 1 one_pos one_lt_two
    rw [funext (hT.svRelaxedResolvent_eq_singleton 1), funext hP,
      ← hT.svResolvent_eq_fun one_pos] at h
    exact h
  · have hL := hT.lipschitzWith_relaxedResolventMap hσ.le zero_le_one hs
    rw [relaxedResolventBound_of_le_threshold hσ.le h1thr, funext hP] at hL
    have e : 1 - 1 * σ / (1 + σ) = 1 / (1 + σ) := by
      have : 0 < 1 + σ := by linarith
      field_simp
      ring
    rwa [e] at hL

end RelaxedResolvents

end RW
