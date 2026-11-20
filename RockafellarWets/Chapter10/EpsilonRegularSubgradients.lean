/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 10: ε-regular subgradients

**Proposition 10.46** introduces the `ε`-regular subgradients
`∂_ε f(x̄) = {v | f(x) ≥ f(x̄) + ⟪v, x - x̄⟫ - ε|x - x̄| + o(|x - x̄|)}` (`epsRegularSubdifferential`)
and shows that limits `v` of `vᵛ ∈ ∂_{εᵛ} f(xᵛ)` with `xᵛ →_f x̄` and `εᵛ ↘ 0` are limiting
subgradients (`mem_subdifferential_of_epsRegular_limits`).  As in the book the proof passes
through `∂_ε f(x) = ∂̂(f + ε|· - x|)(x)` and the sum rule 10.10 with the `ε`-Lipschitz function
`ε|· - x|`, which gives `∂_ε f(x) ⊂ ∂f(x) + εIB` (`epsRegularSubdifferential_subset`).

The horizon part (`λᵛvᵛ → v` with `λᵛ ↘ 0` gives `v ∈ ∂^∞f(x̄)`) is
`mem_horizonSubdifferential_of_epsRegular_limits`, through the cosmic outer semicontinuity 8.7.
The library's sum rule 10.10 needs `f` lsc and proper, so the statements here assume that; the
book's hypothesis (`f` only locally lsc at `x̄`) is recovered in `EpsilonRegularLocalization`
through a truncated localization of `f`.  The resulting cosmic formula
`limsup ∂_ε f(x) = ∂f(x̄) ∪ dir ∂^∞f(x̄)` as `x →_f x̄`, `ε ↘ 0` is stated in sequential form as
the characterizations `mem_subdifferential_iff_epsRegular_limits` and
`mem_horizonSubdifferential_iff_epsRegular_limits`.
-/

import RockafellarWets.Chapter10.LipschitzSums
import RockafellarWets.Chapter9.StrictContinuityCriteria
import RockafellarWets.Chapter8.SubgradientLimits
import RockafellarWets.Chapter8.SubderivativeFormulas
import RockafellarWets.Chapter8.SubgradientRelationships

open Filter Function Metric Set Topology
open scoped NNReal ENNReal InnerProductSpace Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The `ε`-regular subgradients `∂_ε f(x̄)` of **Proposition 10.46**. -/
def epsRegularSubdifferential (f : E → EReal) (ε : ℝ) (x : E) : Set E :=
  {v | ∃ c : ℝ, f x = c ∧ ∀ η : ℝ, 0 < η → ∀ᶠ y in 𝓝 x,
    ((c + ⟪v, y - x⟫_ℝ - (ε + η) * ‖y - x‖ : ℝ) : EReal) ≤ f y}

omit [FiniteDimensional ℝ E] in
/-- Regular subgradients are `ε`-regular for every `ε ≥ 0`. -/
theorem regularSubdifferential_subset_eps {f : E → EReal} {ε : ℝ} (hε : 0 ≤ ε) (x : E) :
    regularSubdifferential f x ⊆ epsRegularSubdifferential f ε x := by
  rintro v ⟨c, hc, h⟩
  refine ⟨c, hc, fun η hη ↦ ?_⟩
  filter_upwards [h η hη] with y hy
  refine le_trans ?_ hy
  rw [EReal.coe_le_coe_iff]
  nlinarith [norm_nonneg (y - x)]

omit [FiniteDimensional ℝ E] in
/-- `∂_ε f(x̄) ⊂ ∂̂(f + ε|· - x̄|)(x̄)` (in fact equality holds). -/
theorem mem_regularSubdifferential_add_norm {f : E → EReal} {ε : ℝ} {x v : E}
    (hv : v ∈ epsRegularSubdifferential f ε x) :
    v ∈ regularSubdifferential (fun y ↦ ((ε * ‖y - x‖ : ℝ) : EReal) + f y) x := by
  obtain ⟨c, hc, h⟩ := hv
  refine ⟨c, ?_, fun η hη ↦ ?_⟩
  · show ((ε * ‖x - x‖ : ℝ) : EReal) + f x = c
    rw [hc, sub_self, norm_zero, mul_zero, EReal.coe_zero, zero_add]
  filter_upwards [h η hη] with y hy
  rw [show c + ⟪v, y - x⟫_ℝ - η * ‖y - x‖ =
      ε * ‖y - x‖ + (c + ⟪v, y - x⟫_ℝ - (ε + η) * ‖y - x‖) by ring, EReal.coe_add]
  exact add_le_add le_rfl hy

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem lipschitzWith_mul_norm_sub {ε : ℝ} (hε : 0 ≤ ε) (x : E) :
    LipschitzWith ⟨ε, hε⟩ (fun y ↦ ε * ‖y - x‖) := by
  refine LipschitzWith.of_dist_le_mul fun a b ↦ ?_
  rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg hε, NNReal.coe_mk, dist_eq_norm]
  refine mul_le_mul_of_nonneg_left ?_ hε
  calc |‖a - x‖ - ‖b - x‖| ≤ ‖(a - x) - (b - x)‖ := abs_norm_sub_norm_le _ _
    _ = ‖a - b‖ := by rw [sub_sub_sub_cancel_right]

/-- **Proposition 10.46**, the key estimate: `∂_ε f(x) ⊂ ∂f(x) + εIB` for `f` lsc and proper. -/
theorem epsRegularSubdifferential_subset {f : E → EReal} (hl : LowerSemicontinuous f)
    (hp : IsProper f) {ε : ℝ} (hε : 0 ≤ ε) (x : E) :
    epsRegularSubdifferential f ε x ⊆ subdifferential f x + closedBall 0 ε := by
  intro v hv
  obtain ⟨c, hc, -⟩ := id hv
  have hreg := mem_regularSubdifferential_add_norm hv
  have hk : ERealStrictlyContinuousAt (fun y ↦ ((ε * ‖y - x‖ : ℝ) : EReal)) x :=
    eRealStrictlyContinuousAt_coe_of_lipschitz (lipschitzWith_mul_norm_sub hε x)
  have hsum := subdifferential_add_subset_of_strictlyContinuous hk hl hp hc
    (regularSubdifferential_subset_subdifferential _ x hreg)
  obtain ⟨a, ha, b, hb, rfl⟩ := hsum
  have hab : ‖a‖ ≤ ε := by
    have h := norm_le_of_mem_subdifferential_of_lipschitzOnWith (U := univ) isOpen_univ
      (fun y _ ↦ by rw [EReal.toReal_coe])
      (by simpa only [EReal.toReal_coe] using
        (lipschitzWith_mul_norm_sub hε x).lipschitzOnWith (s := univ))
      (mem_univ x) ha
    simpa using h
  refine ⟨b, hb, a, mem_closedBall_zero_iff.2 hab, add_comm b a⟩

/-- **Proposition 10.46**: if `xᵛ →_f x̄`, `εᵛ ↘ 0`, `vᵛ ∈ ∂_{εᵛ} f(xᵛ)` and `vᵛ → v`, then
`v ∈ ∂f(x̄)` (for `f` lsc and proper). -/
theorem mem_subdifferential_of_epsRegular_limits {f : E → EReal} (hl : LowerSemicontinuous f)
    (hp : IsProper f) {x v : E} {c : ℝ} (hx : f x = c) {xs : ℕ → E} {εs : ℕ → ℝ}
    {vs : ℕ → E} (hxs : Tendsto xs atTop (attentiveNhds f x)) (hε0 : ∀ n, 0 ≤ εs n)
    (hε : Tendsto εs atTop (𝓝 0)) (hvs : ∀ n, vs n ∈ epsRegularSubdifferential f (εs n) (xs n))
    (hv : Tendsto vs atTop (𝓝 v)) : v ∈ subdifferential f x := by
  have hex : ∀ n, ∃ w ∈ subdifferential f (xs n), ‖vs n - w‖ ≤ εs n := by
    intro n
    obtain ⟨b, hb, a, ha, hab⟩ := epsRegularSubdifferential_subset hl hp (hε0 n) (xs n) (hvs n)
    refine ⟨b, hb, ?_⟩
    rw [← hab, add_sub_cancel_left]
    exact mem_closedBall_zero_iff.1 ha
  choose ws hws hwd using hex
  have hwl : Tendsto ws atTop (𝓝 v) := by
    have h1 : Tendsto (fun n ↦ vs n - ws n) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n ↦ hwd n) hε
    have h2 := hv.sub h1
    simp only [sub_sub_cancel, sub_zero] at h2
    exact h2
  apply outerSetLimitAlong_subdifferential_subset hx
  exact mem_outerSetLimitAlong_iff_exists_seq.2 ⟨xs, ws, hxs, hws, hwl⟩

/-- **Proposition 10.46**, horizon part: if `xᵛ →_f x̄`, `εᵛ ↘ 0`, `vᵛ ∈ ∂_{εᵛ} f(xᵛ)` and
`λᵛvᵛ → v` with `λᵛ ↘ 0`, then `v ∈ ∂^∞f(x̄)` (for `f` lsc and proper). -/
theorem mem_horizonSubdifferential_of_epsRegular_limits {f : E → EReal}
    (hl : LowerSemicontinuous f) (hp : IsProper f) {x v : E} {c : ℝ} (hx : f x = c)
    {xs : ℕ → E} {εs ts : ℕ → ℝ} {vs : ℕ → E} (hxs : Tendsto xs atTop (attentiveNhds f x))
    (hε0 : ∀ n, 0 ≤ εs n) (hε : Tendsto εs atTop (𝓝 0))
    (hvs : ∀ n, vs n ∈ epsRegularSubdifferential f (εs n) (xs n)) (ht0 : ∀ n, 0 < ts n)
    (ht : Tendsto ts atTop (𝓝 0)) (hv : Tendsto (fun n ↦ ts n • vs n) atTop (𝓝 v)) :
    v ∈ horizonSubdifferential f x := by
  have hex : ∀ n, ∃ w ∈ subdifferential f (xs n), ‖vs n - w‖ ≤ εs n := by
    intro n
    obtain ⟨b, hb, a, ha, hab⟩ := epsRegularSubdifferential_subset hl hp (hε0 n) (xs n) (hvs n)
    refine ⟨b, hb, ?_⟩
    rw [← hab, add_sub_cancel_left]
    exact mem_closedBall_zero_iff.1 ha
  choose ws hws hwd using hex
  have hwl : Tendsto (fun n ↦ ts n • ws n) atTop (𝓝 v) := by
    have h1 : Tendsto (fun n ↦ ts n • (vs n - ws n)) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n ↦ ?_) (by simpa using ht.mul hε)
      rw [norm_smul, Real.norm_of_nonneg (ht0 n).le]
      exact mul_le_mul_of_nonneg_left (hwd n) (ht0 n).le
    have h2 := hv.sub h1
    simp only [smul_sub, sub_sub_cancel, sub_zero] at h2
    exact h2
  have hmem : v ∈ horizonOuterSetLimitAlong (attentiveNhds f x) (subdifferential f) :=
    mem_horizonOuterSetLimitAlong_iff_zero_or_scaledSeq.2
      (Or.inr ⟨xs, ws, ts, hxs, hws, ht0, ht, hwl⟩)
  have hK : IsCone (horizonSubdifferential f x) := (subdifferential_properties hx).2.2.2.2.1
  rw [← cosmicDirectionCone_cosmicSet (C := subdifferential f x) hK]
  refine cosmicDirectionCone_mono ?_ hmem
  refine (outerSetLimitAlong_mono fun y ↦ ?_).trans (outerSetLimitAlong_cosmicSubdifferential_subset hx)
  show cosmicSet (subdifferential f y) {0} ⊆
    cosmicSet (subdifferential f y) (horizonSubdifferential f y)
  simp only [cosmicSet, cosmicDirections_zero, union_empty]
  exact subset_union_left

/-- **Proposition 10.46**, the formula `limsup_{x →_f x̄, ε ↘ 0} ∂_ε f(x) = ∂f(x̄) ∪ dir ∂^∞f(x̄)`,
finite part in sequential form: `v ∈ ∂f(x̄)` iff `v` is a limit of `vᵛ ∈ ∂_{εᵛ} f(xᵛ)` with
`xᵛ →_f x̄`, `εᵛ ↘ 0`. -/
theorem mem_subdifferential_iff_epsRegular_limits {f : E → EReal} (hl : LowerSemicontinuous f)
    (hp : IsProper f) {x v : E} {c : ℝ} (hx : f x = c) :
    v ∈ subdifferential f x ↔ ∃ (xs : ℕ → E) (εs : ℕ → ℝ) (vs : ℕ → E),
      Tendsto xs atTop (attentiveNhds f x) ∧ (∀ n, 0 ≤ εs n) ∧ Tendsto εs atTop (𝓝 0) ∧
        (∀ n, vs n ∈ epsRegularSubdifferential f (εs n) (xs n)) ∧ Tendsto vs atTop (𝓝 v) := by
  constructor
  · intro hv
    rw [subdifferential_of_finite hx] at hv
    obtain ⟨xs, vs, hxs, hvs, hvl⟩ := mem_outerSetLimitAlong_iff_exists_seq.1 hv
    exact ⟨xs, fun _ ↦ 0, vs, hxs, fun _ ↦ le_rfl, tendsto_const_nhds,
      fun n ↦ regularSubdifferential_subset_eps le_rfl (xs n) (hvs n), hvl⟩
  · rintro ⟨xs, εs, vs, hxs, hε0, hε, hvs, hvl⟩
    exact mem_subdifferential_of_epsRegular_limits hl hp hx hxs hε0 hε hvs hvl

/-- **Proposition 10.46**, the limsup formula, direction part in sequential form:
`v ∈ ∂^∞f(x̄)` iff `v = 0` or `v` is a limit of `tᵛvᵛ` with `vᵛ ∈ ∂_{εᵛ} f(xᵛ)`, `xᵛ →_f x̄`,
`εᵛ ↘ 0` and `tᵛ ↘ 0`. -/
theorem mem_horizonSubdifferential_iff_epsRegular_limits {f : E → EReal}
    (hl : LowerSemicontinuous f) (hp : IsProper f) {x v : E} {c : ℝ} (hx : f x = c) :
    v ∈ horizonSubdifferential f x ↔ v = 0 ∨ ∃ (xs : ℕ → E) (εs ts : ℕ → ℝ) (vs : ℕ → E),
      Tendsto xs atTop (attentiveNhds f x) ∧ (∀ n, 0 ≤ εs n) ∧ Tendsto εs atTop (𝓝 0) ∧
        (∀ n, vs n ∈ epsRegularSubdifferential f (εs n) (xs n)) ∧ (∀ n, 0 < ts n) ∧
        Tendsto ts atTop (𝓝 0) ∧ Tendsto (fun n ↦ ts n • vs n) atTop (𝓝 v) := by
  constructor
  · intro hv
    rcases (mem_horizonSubdifferential_iff_zero_or_scaledSeq hx).1 hv with h0 | ⟨xs, vs, ts, hxs,
      hvs, ht0, ht, hvl⟩
    · exact Or.inl h0
    · exact Or.inr ⟨xs, fun _ ↦ 0, ts, vs, hxs, fun _ ↦ le_rfl, tendsto_const_nhds,
        fun n ↦ regularSubdifferential_subset_eps le_rfl (xs n) (hvs n), ht0, ht, hvl⟩
  · rintro (rfl | ⟨xs, εs, ts, vs, hxs, hε0, hε, hvs, ht0, ht, hvl⟩)
    · exact (subdifferential_properties hx).2.2.2.2.1.1
    · exact mem_horizonSubdifferential_of_epsRegular_limits hl hp hx hxs hε0 hε hvs ht0 ht hvl

end RW
