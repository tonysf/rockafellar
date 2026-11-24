/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: Monotone variational inequalities

Example 12.48, Exercise 12.49, Theorem 12.51(a), Exercise 12.52(a) and
Example 12.57.

For a nonempty closed convex set `C` and a mapping `F : C → ℝⁿ` (carried as a
total map `E → E` whose values off `C` are irrelevant), the variational
inequality of Example 6.13 at `x̄` is `T(x̄) ∋ 0` for `T = F + N_C`, with
`T(x) = ∅` off `C`.

**Maximality without 12.37.**  The book shows that a maximal monotone extension
`T̄` of `T` has `dom T̄ ⊂ C` through the normal-cone description 12.37 of the
closure of the domain.  Here a pair `(x̄, v̄)` satisfying the monotonicity
inequality against `gph T` is shown directly to have `x̄ ∈ C`: with `p` the
projection of `x̄` on `C`, the pairs `(p, F(p) + t(x̄ - p))`, `t ≥ 0`, lie in
`gph T`, and the inequality against them forces `x̄ = p`.  The rest is the
book's segment argument, which uses the continuity of `F` relative to `C`.
Only completeness of the space is needed for this part.

Theorem 12.51(a) is proved with the resolvents `(I + λT)⁻¹` centered at an
arbitrary point `a`, which also yields 12.52(a) without a shift of domain.
-/

import RockafellarWets.Chapter12.StrongMonotonicity
import RockafellarWets.Chapter6.VariationalComplementarity

open Set Filter Topology Metric
open scoped InnerProductSpace Pointwise

namespace RW

section VariationalInequalities

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `F` is monotone relative to `C`: `⟪F x₁ - F x₀, x₁ - x₀⟫ ≥ 0` for `x₀, x₁ ∈ C`. -/
def MonotoneRelativeTo (F : E → E) (C : Set E) : Prop :=
  ∀ ⦃x₀⦄, x₀ ∈ C → ∀ ⦃x₁⦄, x₁ ∈ C → 0 ≤ ⟪F x₁ - F x₀, x₁ - x₀⟫_ℝ

/-- `F` is strictly monotone relative to `C`. -/
def StrictlyMonotoneRelativeTo (F : E → E) (C : Set E) : Prop :=
  ∀ ⦃x₀⦄, x₀ ∈ C → ∀ ⦃x₁⦄, x₁ ∈ C → x₀ ≠ x₁ → 0 < ⟪F x₁ - F x₀, x₁ - x₀⟫_ℝ

/-- `F` is strongly monotone relative to `C` with constant `σ`. -/
def StronglyMonotoneRelativeTo (σ : ℝ) (F : E → E) (C : Set E) : Prop :=
  ∀ ⦃x₀⦄, x₀ ∈ C → ∀ ⦃x₁⦄, x₁ ∈ C → σ * ‖x₁ - x₀‖ ^ 2 ≤ ⟪F x₁ - F x₀, x₁ - x₀⟫_ℝ

/-- The mapping `T = F + N_C` of Example 12.48 (Chapter 5 sum of the
single-valued `F` and the normal cone mapping). -/
def viMapping (C : Set E) (F : E → E) : E → Set E :=
  svAdd (fun x ↦ ({F x} : Set E)) (normalCone C)

theorem mem_viMapping {C : Set E} {F : E → E} {x v : E} :
    v ∈ viMapping C F x ↔ v - F x ∈ normalCone C x := by
  simp only [viMapping, mem_svAdd, mem_singleton_iff, exists_eq_left]
  constructor
  · rintro ⟨b, hb, rfl⟩
    rwa [add_sub_cancel_left]
  · intro h
    exact ⟨v - F x, h, add_sub_cancel _ _⟩

/-- `T(x) = ∅` when `x ∉ C`. -/
theorem viMapping_eq_empty {C : Set E} {F : E → E} {x : E} (hx : x ∉ C) :
    viMapping C F x = ∅ := by
  ext v
  simp [mem_viMapping, normalCone_eq_empty hx]

theorem mem_of_mem_viMapping {C : Set E} {F : E → E} {x v : E} (h : v ∈ viMapping C F x) :
    x ∈ C := by
  by_contra hx
  rw [viMapping_eq_empty hx] at h
  exact h

/-- `F(x) ∈ T(x)` at points of `C`. -/
theorem apply_mem_viMapping {C : Set E} {F : E → E} {x : E} (hx : x ∈ C) :
    F x ∈ viMapping C F x := by
  rw [mem_viMapping, sub_self]
  exact (isCone_normalCone hx).1

/-- **Example 12.48**: the variational inequality for `C` and `F` at `x̄` is the
condition `T(x̄) ∋ 0`. -/
theorem isVariationalSolution_iff_zero_mem_viMapping {C : Set E} {F : E → E} {x : E} :
    IsVariationalSolution C F x ↔ (0 : E) ∈ viMapping C F x := by
  rw [isVariationalSolution_iff_neg_mem_normalCone, mem_viMapping, zero_sub]

/-- The normal-cone description of Theorem 6.9 at a point of a convex set. -/
theorem mem_normalCone_iff_of_convex {C : Set E} (hC : Convex ℝ C) {x v : E} (hx : x ∈ C) :
    v ∈ normalCone C x ↔ ∀ y ∈ C, ⟪v, y - x⟫_ℝ ≤ 0 := by
  rw [normalCone_eq_of_convex hC hx]
  rfl

/-- The normal cone mapping of a convex set is monotone (12.18 without
closedness). -/
theorem svMonotone_normalCone_of_convex {C : Set E} (hC : Convex ℝ C) :
    SvMonotone (normalCone C) := by
  intro x₀ v₀ h₀ x₁ v₁ h₁
  have hx₀ : x₀ ∈ C := by
    by_contra hx; rw [normalCone_eq_empty hx] at h₀; exact h₀
  have hx₁ : x₁ ∈ C := by
    by_contra hx; rw [normalCone_eq_empty hx] at h₁; exact h₁
  have a₀ := (mem_normalCone_iff_of_convex hC hx₀).1 h₀ x₁ hx₁
  have a₁ := (mem_normalCone_iff_of_convex hC hx₁).1 h₁ x₀ hx₀
  have e : ⟪v₁ - v₀, x₁ - x₀⟫_ℝ = -⟪v₁, x₀ - x₁⟫_ℝ - ⟪v₀, x₁ - x₀⟫_ℝ := by
    rw [inner_sub_left, ← neg_sub x₁ x₀, inner_neg_right]
    ring
  rw [e]
  linarith

/-- The inner product of `T = F + N_C` splits into the `F` part and a
nonnegative normal-cone part. -/
private theorem viMapping_inner_ge {C : Set E} {F : E → E} (hC : Convex ℝ C)
    {x₀ v₀ x₁ v₁ : E} (h₀ : v₀ ∈ viMapping C F x₀) (h₁ : v₁ ∈ viMapping C F x₁) :
    ⟪F x₁ - F x₀, x₁ - x₀⟫_ℝ ≤ ⟪v₁ - v₀, x₁ - x₀⟫_ℝ := by
  have hn := svMonotone_normalCone_of_convex hC (mem_viMapping.1 h₀) (mem_viMapping.1 h₁)
  have e : v₁ - v₀ = (F x₁ - F x₀) + ((v₁ - F x₁) - (v₀ - F x₀)) := by abel
  rw [e, inner_add_left]
  linarith

/-- **Example 12.48**: `T = F + N_C` is monotone when `F` is monotone relative
to the convex set `C` (the addition rule 12.4(b) with 12.18). -/
theorem svMonotone_viMapping {C : Set E} {F : E → E} (hC : Convex ℝ C)
    (hF : MonotoneRelativeTo F C) : SvMonotone (viMapping C F) :=
  fun _ _ h₀ _ _ h₁ ↦ (hF (mem_of_mem_viMapping h₀) (mem_of_mem_viMapping h₁)).trans
    (viMapping_inner_ge hC h₀ h₁)

/-- **Example 12.48**: `T` is strictly monotone when `F` is strictly monotone
relative to `C`. -/
theorem svStrictlyMonotone_viMapping {C : Set E} {F : E → E} (hC : Convex ℝ C)
    (hF : StrictlyMonotoneRelativeTo F C) : SvStrictlyMonotone (viMapping C F) :=
  fun _ _ h₀ _ _ h₁ hx ↦ (hF (mem_of_mem_viMapping h₀) (mem_of_mem_viMapping h₁) hx).trans_le
    (viMapping_inner_ge hC h₀ h₁)

/-- Strong monotonicity of `F` relative to `C` passes to `T = F + N_C`. -/
theorem svStronglyMonotoneWith_viMapping {C : Set E} {F : E → E} {σ : ℝ} (hC : Convex ℝ C)
    (hF : StronglyMonotoneRelativeTo σ F C) : SvStronglyMonotoneWith σ (viMapping C F) :=
  fun _ _ h₀ _ _ h₁ ↦ (hF (mem_of_mem_viMapping h₀) (mem_of_mem_viMapping h₁)).trans
    (viMapping_inner_ge hC h₀ h₁)

/-- The maximality step of Example 12.48: a pair satisfying the monotonicity
inequality against `gph(F + N_C)` lies in the graph.  Only closedness,
convexity and nonemptiness of `C`, continuity of `F` relative to `C` and
completeness of the space are used. -/
theorem mem_viMapping_of_forall_inner_nonneg [CompleteSpace E] {C : Set E} {F : E → E}
    (hCc : IsClosed C) (hC : Convex ℝ C) (hCne : C.Nonempty) (hFc : ContinuousOn F C) {x v : E}
    (h : ∀ x' v', v' ∈ viMapping C F x' → 0 ≤ ⟪v - v', x - x'⟫_ℝ) :
    v ∈ viMapping C F x := by
  -- Step 1: `x ∈ C`, through the projection `p` of `x` on `C`.
  have hxC : x ∈ C := by
    obtain ⟨p, hp, hmin⟩ := exists_norm_eq_iInf_of_complete_convex hCne hCc.isComplete hC x
    have hproj := (norm_eq_iInf_iff_real_inner_le_zero hC hp).1 hmin
    by_contra hxC
    have hxp : x - p ≠ 0 := sub_ne_zero.2 fun e ↦ hxC (e ▸ hp)
    have hn : 0 < ‖x - p‖ ^ 2 := pow_pos (norm_pos_iff.2 hxp) 2
    set t := (|⟪v - F p, x - p⟫_ℝ| + 1) / ‖x - p‖ ^ 2 with ht
    have ht0 : 0 ≤ t := by positivity
    have hmem : F p + t • (x - p) ∈ viMapping C F p := by
      rw [mem_viMapping, add_sub_cancel_left, mem_normalCone_iff_of_convex hC hp]
      intro y hy
      rw [real_inner_smul_left]
      exact mul_nonpos_of_nonneg_of_nonpos ht0 (hproj y hy)
    have h' := h p _ hmem
    have e : ⟪v - (F p + t • (x - p)), x - p⟫_ℝ = ⟪v - F p, x - p⟫_ℝ - t * ‖x - p‖ ^ 2 := by
      rw [sub_add_eq_sub_sub, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    rw [e] at h'
    have htn : t * ‖x - p‖ ^ 2 = |⟪v - F p, x - p⟫_ℝ| + 1 := by
      rw [ht]; field_simp
    have := le_abs_self ⟪v - F p, x - p⟫_ℝ
    linarith
  -- Step 2: `v - F(x) ∈ N_C(x)`, by the segment argument.
  rw [mem_viMapping, mem_normalCone_iff_of_convex hC hxC]
  intro y hy
  have hseg : ∀ τ ∈ Ioo (0 : ℝ) 1, x + τ • (y - x) ∈ C := by
    intro τ hτ
    have := hC hxC hy (by linarith [hτ.2] : 0 ≤ 1 - τ) hτ.1.le (by ring)
    convert this using 1
    module
  have hle : ∀ τ ∈ Ioo (0 : ℝ) 1, ⟪v - F (x + τ • (y - x)), y - x⟫_ℝ ≤ 0 := by
    intro τ hτ
    have h' := h _ _ (apply_mem_viMapping (hseg τ hτ))
    have e : x - (x + τ • (y - x)) = (-τ) • (y - x) := by module
    rw [e, real_inner_smul_right] at h'
    have := hτ.1
    nlinarith
  have hpath : Tendsto (fun τ : ℝ ↦ x + τ • (y - x)) (𝓝[>] 0) (𝓝[C] x) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hc : Continuous (fun τ : ℝ ↦ x + τ • (y - x)) := by fun_prop
      have := hc.tendsto 0
      simp only [zero_smul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with τ hτ
      exact hseg τ hτ
  have hlim : Tendsto (fun τ : ℝ ↦ ⟪v - F (x + τ • (y - x)), y - x⟫_ℝ) (𝓝[>] 0)
      (𝓝 ⟪v - F x, y - x⟫_ℝ) :=
    ((tendsto_const_nhds.sub ((hFc x hxC).tendsto.comp hpath)).inner tendsto_const_nhds)
  exact le_of_tendsto hlim (by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with τ hτ
    exact hle τ hτ)

/-- **Example 12.48 (monotonicity in variational inequalities)**: for a
nonempty closed convex `C` and `F` continuous and monotone relative to `C`, the
mapping `T = F + N_C` is maximal monotone. -/
theorem svMaximalMonotone_viMapping [CompleteSpace E] {C : Set E} {F : E → E}
    (hCc : IsClosed C) (hC : Convex ℝ C) (hCne : C.Nonempty) (hFc : ContinuousOn F C)
    (hFm : MonotoneRelativeTo F C) : SvMaximalMonotone (viMapping C F) :=
  svMaximalMonotone_iff_forall_inner_nonneg.2 ⟨svMonotone_viMapping hC hFm,
    fun _ _ h ↦ mem_viMapping_of_forall_inner_nonneg hCc hC hCne hFc h⟩

/-- **Example 12.48**, collected: the variational inequality is `T(x̄) ∋ 0` for
`T = F + N_C` (with `T(x) = ∅` off `C`); `T` is maximal monotone when `F` is
continuous and monotone relative to `C`, and then the solution set `T⁻¹(0)` is
closed and convex; `T` is strictly monotone when `F` is strictly monotone
relative to `C`, and then there is at most one solution. -/
theorem monotonicity_in_variational_inequalities [CompleteSpace E] {C : Set E} {F : E → E}
    (hCc : IsClosed C) (hC : Convex ℝ C) (hCne : C.Nonempty) :
    (∀ x, IsVariationalSolution C F x ↔ (0 : E) ∈ viMapping C F x) ∧
      (∀ x, x ∉ C → viMapping C F x = ∅) ∧
      (ContinuousOn F C → MonotoneRelativeTo F C →
        SvMaximalMonotone (viMapping C F) ∧ IsClosed (svInv (viMapping C F) 0) ∧
          Convex ℝ (svInv (viMapping C F) 0)) ∧
      (StrictlyMonotoneRelativeTo F C →
        SvStrictlyMonotone (viMapping C F) ∧ (svInv (viMapping C F) 0).Subsingleton) := by
  refine ⟨fun _ ↦ isVariationalSolution_iff_zero_mem_viMapping, fun _ hx ↦ viMapping_eq_empty hx,
    fun hFc hFm ↦ ?_, fun hF ↦ ?_⟩
  · have hT := svMaximalMonotone_viMapping hCc hC hCne hFc hFm
    exact ⟨hT, hT.isClosed_svInv_apply 0, hT.convex_svInv_apply 0⟩
  · have hT := svStrictlyMonotone_viMapping hC hF
    refine ⟨hT, fun x₀ h₀ x₁ h₁ ↦ ?_⟩
    by_contra hne
    have := hT h₀ h₁ hne
    simp at this

/-- **Exercise 12.49 (alternative expression of a variational inequality)**:
for a nonempty closed convex `C` and `F` continuous and monotone relative to
`C`, `x̄` solves the variational inequality exactly when `x̄ ∈ C` and
`⟪F(x), x̄ - x⟫ ≤ 0` for all `x ∈ C`.  As in the book's guide, the proof goes
through the maximal monotonicity of `T = F + N_C`. -/
theorem isVariationalSolution_iff_forall_inner_nonpos [CompleteSpace E] {C : Set E} {F : E → E}
    (hCc : IsClosed C) (hC : Convex ℝ C) (hCne : C.Nonempty) (hFc : ContinuousOn F C)
    (hFm : MonotoneRelativeTo F C) {x : E} :
    IsVariationalSolution C F x ↔ x ∈ C ∧ ∀ y ∈ C, ⟪F y, x - y⟫_ℝ ≤ 0 := by
  have hT := svMaximalMonotone_viMapping hCc hC hCne hFc hFm
  rw [isVariationalSolution_iff_zero_mem_viMapping]
  constructor
  · intro h
    refine ⟨mem_of_mem_viMapping h, fun y hy ↦ ?_⟩
    have := hT.1 h (apply_mem_viMapping hy)
    rw [sub_zero, ← neg_sub x y, inner_neg_right] at this
    linarith
  · rintro ⟨hx, hineq⟩
    refine hT.mem_of_forall_inner_nonneg fun y w hw ↦ ?_
    have hy := mem_of_mem_viMapping hw
    have hn := (mem_normalCone_iff_of_convex hC hy).1 (mem_viMapping.1 hw) x hx
    have e : ⟪0 - w, x - y⟫_ℝ = -⟪F y, x - y⟫_ℝ - ⟪w - F y, x - y⟫_ℝ := by
      rw [zero_sub, inner_neg_left, inner_sub_left]
      ring
    rw [e]
    linarith [hineq y hy]

end VariationalInequalities

section Existence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Theorem 12.51(a)**, centered at an arbitrary point `a`: if `T` is maximal
monotone and `⟪v, x - a⟫ ≥ 0` whenever `v ∈ T(x)` and `|x - a| > ρ`, then
`T⁻¹(0)` meets the closed ball of radius `ρ` around `a`.  The points
`xλ = (I + λT)⁻¹(a)` stay in that ball, the vectors `λ⁻¹(a - xλ) ∈ T(xλ)` tend
to `0` as `λ → ∞`, and the graph of `T` is closed. -/
theorem SvMaximalMonotone.exists_zero_mem_closedBall {T : E → Set E}
    (hT : SvMaximalMonotone T) (a : E) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : ∀ x v, v ∈ T x → ρ < ‖x - a‖ → 0 ≤ ⟪v, x - a⟫_ℝ) :
    ∃ x ∈ closedBall a ρ, (0 : E) ∈ T x := by
  let lam : ℕ → ℝ := fun n ↦ n + 1
  have hlam : ∀ n, 0 < lam n := fun n ↦ by positivity
  let xs : ℕ → E := fun n ↦ resolventMap T (lam n) a
  let vs : ℕ → E := fun n ↦ (lam n)⁻¹ • (a - xs n)
  have hvs : ∀ n, vs n ∈ T (xs n) := by
    intro n
    obtain ⟨v, hv, hxv⟩ := (hT.resolventMap_eq_iff (z := a) (x := xs n) (hlam n)).1 rfl
    have e : vs n = v := by
      simp only [vs]
      rw [← hxv, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ (hlam n).ne', one_smul]
    rw [e]
    exact hv
  have hxs : ∀ n, xs n ∈ closedBall a ρ := by
    intro n
    rw [mem_closedBall, dist_eq_norm]
    by_contra hlt
    push_neg at hlt
    have h' := h _ _ (hvs n) hlt
    have e : ⟪vs n, xs n - a⟫_ℝ = -((lam n)⁻¹ * ‖xs n - a‖ ^ 2) := by
      simp only [vs]
      rw [real_inner_smul_left, ← neg_sub (xs n) a, inner_neg_left, real_inner_self_eq_norm_sq]
      ring
    rw [e] at h'
    have : 0 < (lam n)⁻¹ * ‖xs n - a‖ ^ 2 := by
      have : 0 < ‖xs n - a‖ := hρ.trans_lt hlt
      have := hlam n
      positivity
    linarith
  have hvs_le : ∀ n, ‖vs n‖ ≤ ρ / lam n := by
    intro n
    simp only [vs]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (hlam n).le), ← norm_neg, neg_sub,
      div_eq_inv_mul]
    gcongr
    have := hxs n
    rwa [mem_closedBall, dist_eq_norm] at this
  have hvs_lim : Tendsto vs atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun n ↦ norm_nonneg _) hvs_le ?_
    have : Tendsto (fun n : ℕ ↦ ρ * (1 / ((n : ℝ) + 1))) atTop (𝓝 (ρ * 0)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ρ
    rw [mul_zero] at this
    refine this.congr fun n ↦ ?_
    simp only [lam]
    ring
  obtain ⟨xb, hxb, φ, hφ, hlim⟩ := (isCompact_closedBall a ρ).tendsto_subseq hxs
  refine ⟨xb, hxb, ?_⟩
  have hpair : Tendsto (fun n ↦ (xs (φ n), vs (φ n))) atTop (𝓝 (xb, (0 : E))) :=
    hlim.prodMk_nhds (hvs_lim.comp hφ.tendsto_atTop)
  exact hT.isClosed_svGraph.mem_of_tendsto hpair (Eventually.of_forall fun n ↦ hvs (φ n))

/-- **Theorem 12.51(a) (solutions to a monotone generalized equation)**: for
maximal monotone `T`, the solution set `T⁻¹(0)` is closed and convex, and
`T⁻¹(0) ∩ ρB` is nonempty if `⟪v, x⟫ ≥ 0` whenever `v ∈ T(x)` and `|x| > ρ`. -/
theorem SvMaximalMonotone.solutions_generalized_equation {T : E → Set E}
    (hT : SvMaximalMonotone T) :
    IsClosed (svInv T 0) ∧ Convex ℝ (svInv T 0) ∧
      ∀ ρ : ℝ, 0 ≤ ρ → (∀ x v, v ∈ T x → ρ < ‖x‖ → 0 ≤ ⟪v, x⟫_ℝ) →
        (svInv T 0 ∩ closedBall 0 ρ).Nonempty := by
  refine ⟨hT.isClosed_svInv_apply 0, hT.convex_svInv_apply 0, fun ρ hρ h ↦ ?_⟩
  obtain ⟨x, hx, h0⟩ := hT.exists_zero_mem_closedBall 0 hρ (by simpa using h)
  exact ⟨x, h0, hx⟩

/-- **Exercise 12.52(a) (existence of solutions to variational
inequalities)**: for a nonempty closed convex `C`, `F` continuous and monotone
relative to `C`, and `a ∈ C`, the solution set `X_{C,F}` meets `B(a, ρ)` if
`⟪F(x), x - a⟫ ≥ 0` for all `x ∈ C` with `|x - a| > ρ`. -/
theorem exists_isVariationalSolution_mem_closedBall {C : Set E} {F : E → E}
    (hCc : IsClosed C) (hC : Convex ℝ C) (hFc : ContinuousOn F C)
    (hFm : MonotoneRelativeTo F C) {a : E} (ha : a ∈ C) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : ∀ x ∈ C, ρ < ‖x - a‖ → 0 ≤ ⟪F x, x - a⟫_ℝ) :
    ∃ x ∈ closedBall a ρ, IsVariationalSolution C F x := by
  have hT := svMaximalMonotone_viMapping hCc hC ⟨a, ha⟩ hFc hFm
  obtain ⟨x, hx, h0⟩ := hT.exists_zero_mem_closedBall a hρ (fun x v hv hlt ↦ by
    have hxC := mem_of_mem_viMapping hv
    have hn := (mem_normalCone_iff_of_convex hC hxC).1 (mem_viMapping.1 hv) a ha
    have e : ⟪v, x - a⟫_ℝ = ⟪F x, x - a⟫_ℝ - ⟪v - F x, a - x⟫_ℝ := by
      rw [show a - x = -(x - a) by abel, inner_neg_right, inner_sub_left]
      ring
    rw [e]
    linarith [h x hxC hlt])
  exact ⟨x, hx, isVariationalSolution_iff_zero_mem_viMapping.2 h0⟩

end Existence

section ContractionIterations

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Example 12.57**, the subproblems: `(I + T)⁻¹(z)` for `T = F + N_C` is the
solution of the variational inequality for `C` and `F^z(x) = F(x) + x - z`. -/
theorem resolventMap_viMapping_eq_iff {C : Set E} {F : E → E}
    (hT : SvMaximalMonotone (viMapping C F)) (z x : E) :
    resolventMap (viMapping C F) 1 z = x ↔ IsVariationalSolution C (fun y ↦ F y + y - z) x := by
  rw [hT.resolventMap_eq_iff one_pos, isVariationalSolution_iff_zero_mem_viMapping]
  simp only [mem_viMapping, one_smul]
  constructor
  · rintro ⟨v, hv, rfl⟩
    convert hv using 1
    abel
  · intro h
    refine ⟨z - x, ?_, by abel⟩
    convert h using 1
    abel

/-- **Example 12.57 (contractions in solving variational inequalities)**: for
a nonempty closed convex `C`, `F` continuous and monotone relative to `C`, and
`τ ∈ (0, 2)`, the mapping `P_τ` of Theorem 12.56 for `T = F + N_C` is
nonexpansive with the solutions of the variational inequality as fixed points.
The iteration `x^{ν+1} = P_τ(x^ν)` computes the unique solution `x̄^ν` of the
variational inequality for `C` and `F^ν(x) = F(x) + x - x^ν` and sets
`x^{ν+1} = (1 - τ)x^ν + τx̄^ν`.  If `F` is strongly monotone relative to `C` with
constant `σ > 0`, the variational inequality has a unique solution `x̄`, and every
such sequence converges to `x̄` at the linear rate `κ_τ ∈ (0, 1)` of 12(9). -/
theorem contractions_in_variational_inequalities {C : Set E} {F : E → E}
    (hCc : IsClosed C) (hC : Convex ℝ C) (hCne : C.Nonempty) (hFc : ContinuousOn F C)
    (hFm : MonotoneRelativeTo F C) {τ : ℝ} (hτ : 0 < τ) (hτ2 : τ < 2) :
    LipschitzWith 1 (relaxedResolventMap (viMapping C F) τ) ∧
      {x | relaxedResolventMap (viMapping C F) τ x = x} = {x | IsVariationalSolution C F x} ∧
      (∀ z, ∃! xb, IsVariationalSolution C (fun y ↦ F y + y - z) xb) ∧
      (∀ z xb, IsVariationalSolution C (fun y ↦ F y + y - z) xb →
        relaxedResolventMap (viMapping C F) τ z = (1 - τ) • z + τ • xb) ∧
      (∀ σ, 0 < σ → StronglyMonotoneRelativeTo σ F C →
        ∃ xb, IsVariationalSolution C F xb ∧ (∀ y, IsVariationalSolution C F y → y = xb) ∧
          0 < relaxedResolventBound σ τ ∧ relaxedResolventBound σ τ < 1 ∧
          ∀ xs : ℕ → E, (∀ ν, xs (ν + 1) = relaxedResolventMap (viMapping C F) τ (xs ν)) →
            (∀ ν, ‖xs (ν + 1) - xb‖ ≤ relaxedResolventBound σ τ * ‖xs ν - xb‖) ∧
              Tendsto xs atTop (𝓝 xb)) := by
  have hT := svMaximalMonotone_viMapping hCc hC hCne hFc hFm
  obtain ⟨-, -, -, hL, hfix⟩ := hT.relaxedResolvent_nonexpansive hτ hτ2.le
  refine ⟨hL, ?_, fun z ↦ ?_, fun z xb hxb ↦ ?_, fun σ hσ hFs ↦ ?_⟩
  · rw [hfix]
    ext x
    exact isVariationalSolution_iff_zero_mem_viMapping.symm
  · refine ⟨resolventMap (viMapping C F) 1 z, (resolventMap_viMapping_eq_iff hT z _).1 rfl,
      fun y hy ↦ ((resolventMap_viMapping_eq_iff hT z y).2 hy).symm⟩
  · rw [relaxedResolventMap, (resolventMap_viMapping_eq_iff hT z xb).2 hxb]
  · have hs := svStronglyMonotoneWith_viMapping hC hFs
    obtain ⟨-, ⟨xb, hxb, huniq⟩, -⟩ := hT.consequences_of_strongMonotonicity hσ hs
    have hxb' : IsVariationalSolution C F xb := isVariationalSolution_iff_zero_mem_viMapping.2 hxb
    have hb0 := relaxedResolventBound_pos hσ.le τ
    have hb1 := relaxedResolventBound_lt_one hσ hτ hτ2
    refine ⟨xb, hxb', fun y hy ↦ huniq y (isVariationalSolution_iff_zero_mem_viMapping.1 hy),
      hb0, hb1, fun xs hxs ↦ ?_⟩
    have hLσ := hT.lipschitzWith_relaxedResolventMap hσ.le hτ.le hs
    have hfixb : relaxedResolventMap (viMapping C F) τ xb = xb :=
      (hT.relaxedResolventMap_eq_self_iff hτ.ne').2 hxb
    have hstep : ∀ ν, ‖xs (ν + 1) - xb‖ ≤ relaxedResolventBound σ τ * ‖xs ν - xb‖ := by
      intro ν
      have := hLσ.dist_le_mul (xs ν) xb
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hb0.le, hfixb, ← hxs ν] at this
      exact this
    refine ⟨hstep, ?_⟩
    have hgeom : ∀ ν, ‖xs ν - xb‖ ≤ relaxedResolventBound σ τ ^ ν * ‖xs 0 - xb‖ := by
      intro ν
      induction ν with
      | zero => simp
      | succ n ih =>
        calc ‖xs (n + 1) - xb‖ ≤ relaxedResolventBound σ τ * ‖xs n - xb‖ := hstep n
          _ ≤ relaxedResolventBound σ τ * (relaxedResolventBound σ τ ^ n * ‖xs 0 - xb‖) :=
            mul_le_mul_of_nonneg_left ih hb0.le
          _ = relaxedResolventBound σ τ ^ (n + 1) * ‖xs 0 - xb‖ := by ring
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ ↦ norm_nonneg _) hgeom ?_
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hb0.le hb1).mul_const ‖xs 0 - xb‖
    rwa [zero_mul] at this

end ContractionIterations

end RW
