/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Proximal and sharp augmenting functions, and exactness of their penalties

The augmenting functions `½|u|²` of Example 11.57 and `‖u‖` (any norm) of
Example 11.58, and Example 11.62: under the assumptions of Theorem 11.59 a
vector supports an exact quadratic penalty exactly when it is a proximal
subgradient of `p` at `0`, and `0` supports an exact linear penalty exactly
when `p` is calm from below at `0`. Finiteness of both augmenting functions
forces `p(0)` to be finite under exact penalization, so no feasibility
hypothesis is needed here.
-/
import RockafellarWets.Chapter11.NonconvexDuality
import RockafellarWets.Chapter8.ProximalSubgradients
import RockafellarWets.Chapter8.Calmness

open Set Filter Topology Metric
open scoped InnerProductSpace
namespace RW
noncomputable section

/-- Moving a finite summand across an extended-real inequality. -/
theorem ereal_coe_le_add_coe_iff (a : EReal) (x y : ℝ) :
    (x : EReal) ≤ a + (y : EReal) ↔ ((x - y : ℝ) : EReal) ≤ a := by
  induction a using EReal.rec with
  | bot =>
    rw [EReal.bot_add]
    exact ⟨fun h ↦ absurd (le_bot_iff.mp h) (EReal.coe_ne_bot _),
      fun h ↦ absurd (le_bot_iff.mp h) (EReal.coe_ne_bot _)⟩
  | top => simp
  | coe a =>
    rw [← EReal.coe_add, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
    constructor <;> intro h <;> linarith

section Augmenting

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]

/-- A real convex function has a convex epigraph in `EReal`. -/
theorem convex_epigraph_coe_of_convexOn_univ {g : P → ℝ} (hg : ConvexOn ℝ univ g) :
    Convex ℝ (epigraph (fun u ↦ (g u : EReal))) := by
  convert hg.convex_epigraph using 1
  ext p
  simp [epigraph]

/-- **Example 11.57**, the proximal augmenting function `σ(u) = ½|u|²`. -/
def proximalAugmentingFunction (P : Type*) [NormedAddCommGroup P] : P → EReal :=
  fun u ↦ ((‖u‖ ^ 2 / 2 : ℝ) : EReal)

theorem isAugmentingFunction_proximal : IsAugmentingFunction (proximalAugmentingFunction P) where
  isProper := ⟨⟨0, EReal.coe_lt_top _⟩, fun _ ↦ EReal.bot_lt_coe _⟩
  lowerSemicontinuous := (continuous_coe_real_ereal.comp (by fun_prop)).lowerSemicontinuous
  convex := by
    apply convex_epigraph_coe_of_convexOn_univ
    have h := ((convexOn_norm (convex_univ : Convex ℝ (univ : Set P))).pow
      (fun x _ ↦ norm_nonneg x) 2).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
    convert h using 1
    funext u
    simp only [Pi.pow_apply, smul_eq_mul]
    ring
  zero := by simp [proximalAugmentingFunction]
  pos := fun u hu ↦ EReal.coe_pos.mpr (div_pos (pow_pos (norm_pos_iff.mpr hu) 2) two_pos)

/-- **Example 11.58**, the sharp augmenting function `σ(u) = N(u)` of a norm. -/
def sharpAugmentingFunction (N : Seminorm ℝ P) : P → EReal := fun u ↦ ((N u : ℝ) : EReal)

variable [FiniteDimensional ℝ P]

/-- Seminorms on finite-dimensional spaces are continuous. -/
theorem seminorm_continuous_of_finiteDimensional (N : Seminorm ℝ P) : Continuous N := by
  have h := N.convexOn.continuousOn_interior
  rw [interior_univ] at h
  exact continuousOn_univ.mp h

theorem isAugmentingFunction_sharp {N : Seminorm ℝ P} (hN : ∀ u, N u = 0 → u = 0) :
    IsAugmentingFunction (sharpAugmentingFunction N) where
  isProper := ⟨⟨0, EReal.coe_lt_top _⟩, fun _ ↦ EReal.bot_lt_coe _⟩
  lowerSemicontinuous :=
    (continuous_coe_real_ereal.comp (seminorm_continuous_of_finiteDimensional N)).lowerSemicontinuous
  convex := convex_epigraph_coe_of_convexOn_univ N.convexOn
  zero := by simp [sharpAugmentingFunction]
  pos := fun u hu ↦ EReal.coe_pos.mpr
    (lt_of_le_of_ne (apply_nonneg N u) fun h ↦ hu (hN u h.symm))

/-- Every norm on a finite-dimensional space dominates a multiple of the
Euclidean norm. -/
theorem exists_norm_le_mul_seminorm {N : Seminorm ℝ P} (hN : ∀ u, N u = 0 → u = 0) :
    ∃ C, 0 < C ∧ ∀ u, ‖u‖ ≤ C * N u := by
  obtain ⟨c, hc, hgrowth⟩ := (isAugmentingFunction_sharp hN).exists_linear_growth one_pos
  refine ⟨c⁻¹, inv_pos.mpr hc, fun u ↦ ?_⟩
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hn : ‖‖u‖⁻¹ • u‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hu0.ne']
  have hv := hgrowth (‖u‖⁻¹ • u) hn.ge
  rw [hn, mul_one] at hv
  change ((c : ℝ) : EReal) ≤ ((N (‖u‖⁻¹ • u) : ℝ) : EReal) at hv
  rw [EReal.coe_le_coe_iff, map_smul_eq_mul, norm_inv, norm_norm] at hv
  rw [inv_mul_eq_div, le_div_iff₀ hu0] at hv
  rw [← div_eq_inv_mul, le_div_iff₀ hc]
  linarith

end Augmenting

section Examples

variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
  {f : WithLp 2 (E × P) → EReal}

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ P] in
/-- With a finite augmenting function, 11(32) forces `p(0)` to be finite. -/
theorem parametricValue_zero_ne_top_of_forall_le {σ : P → EReal} (hσt : ∀ u, σ u ≠ ⊤)
    (hσ : IsAugmentingFunction σ) (hpp : IsProper (parametricValue f)) {yb : P} {rb : ℝ}
    (h32 : ∀ u, parametricValue f 0 + (⟪yb, u⟫_ℝ : EReal) ≤
      parametricValue f u + (rb : EReal) * σ u) :
    parametricValue f 0 ≠ ⊤ := by
  intro htop
  obtain ⟨u, hu⟩ := hpp.1
  have h := h32 u
  rw [htop, EReal.top_add_coe, top_le_iff] at h
  have hσb : σ u ≠ ⊥ := (hσ.isProper.2 u).ne'
  obtain ⟨s, hs⟩ : ∃ s : ℝ, σ u = s := ⟨_, (EReal.coe_toReal (hσt u) hσb).symm⟩
  rw [hs, ← EReal.coe_mul] at h
  have hlt : parametricValue f u + ((rb * s : ℝ) : EReal) < ⊤ := by
    rw [lt_top_iff_ne_top]
    exact EReal.add_ne_top hu.ne (EReal.coe_ne_top _)
  exact hlt.ne h

/-- **Example 11.62(a)**: for the proximal Lagrangian, `ȳ` supports an exact
penalty representation exactly when it is a proximal subgradient of
`p(u) = inf_x f(x,u)` at `u = 0`. -/
theorem supportsExactPenaltyRepresentation_proximal_iff
    (hf : IsDualizingParameterization (primalObjective f) f) (hl : LowerSemicontinuous f)
    (hb : IsParametricallyLevelBounded f)
    (hψ : ∃ (y : P) (r : ℝ), 0 < r ∧
      ⊥ < augmentedDualObjective f (proximalAugmentingFunction P) y r) {yb : P} :
    SupportsExactPenaltyRepresentation f (proximalAugmentingFunction P) yb ↔
      yb ∈ proximalSubdifferential (parametricValue f) 0 := by
  have hσ := isAugmentingFunction_proximal (P := P)
  have hpp := isProper_parametricValue hl hf.isProper hb
  constructor
  · intro hs
    obtain ⟨rb, hmax⟩ :=
      (supportsExactPenaltyRepresentation_iff_exists_maximizer hf hl hb hσ hψ).mp hs
    have h32 := (isAugmentedDualMaximizer_iff hf hl hb hσ hψ hmax.1).mp hmax
    have hp0 := parametricValue_zero_ne_top_of_forall_le (fun _ ↦ EReal.coe_ne_top _) hσ hpp
      h32
    obtain ⟨c, hc⟩ : ∃ c : ℝ, parametricValue f 0 = c :=
      ⟨_, (EReal.coe_toReal hp0 (hpp.2 0).ne').symm⟩
    refine ⟨c, hc, rb, hmax.1, 1, one_pos, fun y _ ↦ ?_⟩
    have h := h32 y
    rw [hc, ← EReal.coe_add] at h
    change ((c + ⟪yb, y⟫_ℝ : ℝ) : EReal) ≤ parametricValue f y +
      (rb : EReal) * ((‖y‖ ^ 2 / 2 : ℝ) : EReal) at h
    rw [← EReal.coe_mul, ereal_coe_le_add_coe_iff] at h
    rw [sub_zero]
    convert h using 2
    ring
  · rintro ⟨c, hc, ρ, hρ, δ, hδ, hprox⟩
    have hfeas : (⨅ x, primalObjective f x) < ⊤ := by
      rw [← parametricValue_zero_eq, hc]
      exact EReal.coe_lt_top c
    refine (supportsExactPenaltyRepresentation_iff hf hl hb hσ hψ hfeas).mpr
      ⟨closedBall 0 δ, closedBall_mem_nhds 0 hδ, ρ, hρ, fun u hu ↦ ?_⟩
    have h := hprox u (by simpa using hu)
    rw [sub_zero] at h
    rw [hc, ← EReal.coe_add]
    change ((c + ⟪yb, u⟫_ℝ : ℝ) : EReal) ≤ parametricValue f u +
      (ρ : EReal) * ((‖u‖ ^ 2 / 2 : ℝ) : EReal)
    rw [← EReal.coe_mul, ereal_coe_le_add_coe_iff]
    convert h using 2
    ring

/-- **Example 11.62(b)**: for the sharp Lagrangian of a norm `N`, the vector
`0` supports an exact penalty representation exactly when `p` is calm from
below at `0`. -/
theorem supportsExactPenaltyRepresentation_sharp_iff {N : Seminorm ℝ P}
    (hN : ∀ u, N u = 0 → u = 0)
    (hf : IsDualizingParameterization (primalObjective f) f) (hl : LowerSemicontinuous f)
    (hb : IsParametricallyLevelBounded f)
    (hψ : ∃ r : ℝ, 0 < r ∧ ⊥ < augmentedDualObjective f (sharpAugmentingFunction N) 0 r) :
    SupportsExactPenaltyRepresentation f (sharpAugmentingFunction N) 0 ↔
      IsCalmFromBelowAt (parametricValue f) 0 := by
  have hσ := isAugmentingFunction_sharp hN
  have hψ' : ∃ (y : P) (r : ℝ), 0 < r ∧
      ⊥ < augmentedDualObjective f (sharpAugmentingFunction N) y r := ⟨0, hψ⟩
  have hpp := isProper_parametricValue hl hf.isProper hb
  obtain ⟨C₁, hC₁, hle⟩ :=
    N.bound_of_continuous_normedSpace (seminorm_continuous_of_finiteDimensional N)
  obtain ⟨C₂, hC₂, hge⟩ := exists_norm_le_mul_seminorm hN
  constructor
  · intro hs
    obtain ⟨rb, hmax⟩ :=
      (supportsExactPenaltyRepresentation_iff_exists_maximizer hf hl hb hσ hψ').mp hs
    have h32 := (isAugmentedDualMaximizer_iff hf hl hb hσ hψ' hmax.1).mp hmax
    have hp0 := parametricValue_zero_ne_top_of_forall_le (fun _ ↦ EReal.coe_ne_top _) hσ hpp
      h32
    obtain ⟨c, hc⟩ : ∃ c : ℝ, parametricValue f 0 = c :=
      ⟨_, (EReal.coe_toReal hp0 (hpp.2 0).ne').symm⟩
    refine ⟨rb * C₁, mul_nonneg hmax.1.le hC₁.le, c, hc, Eventually.of_forall fun y ↦ ?_⟩
    have h := h32 y
    rw [hc, inner_zero_left, EReal.coe_zero, add_zero] at h
    change (c : EReal) ≤ parametricValue f y + (rb : EReal) * ((N y : ℝ) : EReal) at h
    rw [← EReal.coe_mul, ereal_coe_le_add_coe_iff] at h
    refine le_trans (EReal.coe_le_coe_iff.mpr ?_) h
    rw [sub_zero]
    have := mul_le_mul_of_nonneg_left (hle y) hmax.1.le
    nlinarith
  · rintro ⟨κ, hκ, c, hc, hev⟩
    have hfeas : (⨅ x, primalObjective f x) < ⊤ := by
      rw [← parametricValue_zero_eq, hc]
      exact EReal.coe_lt_top c
    refine (supportsExactPenaltyRepresentation_iff hf hl hb hσ hψ' hfeas).mpr
      ⟨_, hev, κ * C₂ + 1, by positivity, fun u hu ↦ ?_⟩
    change ((c - κ * ‖u - 0‖ : ℝ) : EReal) ≤ parametricValue f u at hu
    rw [hc, inner_zero_left, EReal.coe_zero, add_zero]
    change (c : EReal) ≤ parametricValue f u + ((κ * C₂ + 1 : ℝ) : EReal) * ((N u : ℝ) : EReal)
    rw [← EReal.coe_mul, ereal_coe_le_add_coe_iff]
    refine le_trans (EReal.coe_le_coe_iff.mpr ?_) hu
    rw [sub_zero]
    have h1 := mul_le_mul_of_nonneg_left (hge u) hκ
    have h2 : 0 ≤ N u := apply_nonneg N u
    nlinarith

end Examples

end
end RW
