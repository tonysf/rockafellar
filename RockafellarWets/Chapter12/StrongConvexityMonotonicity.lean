/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: Strong monotonicity versus strong convexity

Exercise 12.59 and Exercise 12.61.

For a proper lsc `f` and any real `σ`, the following are equivalent
(`subdifferential_strongMonotonicity_tfae`):

* `∂f` is strongly monotone with constant `σ`;
* `f` satisfies the strong convexity inequality of 12.58 with constant `σ`;
* `f - (σ/2)|·|²` is convex.

The equivalence of the last two holds for every function without the value
`-∞`, and the second implies the first for every proper function; these are
the strong-convexity lane's `stronglyConvexWith_iff_convex_epigraph_sub` and
`StronglyConvexWith.inner_sub_ge_of_mem_subdifferential`.  The first implies the
third through the converse half of Theorem 12.17 applied to `f - (σ/2)|·|²`.

**Correction to 12.59.**  The exercise is printed for an arbitrary
`f : ℝⁿ → ℝ̄`, but the implication from (a) needs lower semicontinuity (and
properness, as in 12.17).  The function equal to `|x|²` for `x ≠ 0` and to `1`
at `0` is proper, its subgradient mapping is `x ↦ {2x}` on `x ≠ 0` and empty at
`0`, hence strongly monotone with constant `2`, yet `f - |·|²` is not convex
(`strongMonotonicityCounterexample_spec`).  Exercise 12.59 is therefore proved
for proper lsc `f`.

Exercise 12.61 is the case `σ = -λ⁻¹`: for a proper lsc `f` and `λ > 0`,
`h_λ f = f` (11.26(d): `f + (2λ)⁻¹|·|²` convex), `∂f + λ⁻¹I` monotone, and the
hypoconvexity inequality with `+ ½λ⁻¹τ(1 - τ)|x₀ - x₁|²` are equivalent.
-/

import RockafellarWets.Chapter12.StrongConvexity
import RockafellarWets.Chapter12.StrongMonotonicity
import RockafellarWets.Chapter12.ConvexityFromMonotoneSubgradients
import RockafellarWets.Chapter11.ProximalHullConjugacy

open Set Filter Topology
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem ereal_sub_coe_eq_add_coe_neg (a : EReal) (r : ℝ) :
    a - (r : EReal) = a + ((-r : ℝ) : EReal) := by
  rw [sub_eq_add_neg, EReal.coe_neg]

omit [InnerProductSpace ℝ E] in
theorem lowerSemicontinuous_sub_quadratic {f : E → EReal} (hl : LowerSemicontinuous f) (σ : ℝ) :
    LowerSemicontinuous (fun x ↦ f x - ((σ / 2 * ‖x‖ ^ 2 : ℝ) : EReal)) := by
  have h := lowerSemicontinuous_add_coe hl (g := fun x ↦ -(σ / 2 * ‖x‖ ^ 2)) (by fun_prop)
  convert h using 2 with x

/-- **12.59 (b) ⇒ (a)** for every proper function: the strong convexity
inequality with constant `σ` makes `∂f` strongly monotone with constant `σ`. -/
theorem StronglyConvexWith.svStronglyMonotoneWith_subdifferential [FiniteDimensional ℝ E]
    {f : E → EReal} {σ : ℝ} (hp : IsProper f) (h : StronglyConvexWith σ f) :
    SvStronglyMonotoneWith σ (subdifferential f) :=
  fun _ _ h₀ _ _ h₁ ↦ h.inner_sub_ge_of_mem_subdifferential hp h₀ h₁

/-- **12.59 (a) ⇒ (c)** for proper lsc `f` and any real `σ`, through the
converse half of Theorem 12.17 applied to `f - (σ/2)|·|²`. -/
theorem SvStronglyMonotoneWith.convex_epigraph_sub_quadratic [FiniteDimensional ℝ E]
    {f : E → EReal} {σ : ℝ} (hp : IsProper f) (hl : LowerSemicontinuous f)
    (h : SvStronglyMonotoneWith σ (subdifferential f)) :
    Convex ℝ (epigraph (fun x ↦ f x - ((σ / 2 * ‖x‖ ^ 2 : ℝ) : EReal))) := by
  have hmono : SvMonotone (subdifferential (fun z ↦ f z - ((σ / 2 * ‖z‖ ^ 2 : ℝ) : EReal))) :=
    subdifferential_inner_ge_iff_svMonotone_sub.1 fun _ _ _ _ h₀ h₁ ↦ h h₀ h₁
  exact convex_epigraph_of_svMonotone_subdifferential
    (isProper_sub_coe hp fun z ↦ σ / 2 * ‖z‖ ^ 2) (lowerSemicontinuous_sub_quadratic hl σ) hmono

/-- The equivalences of Exercise 12.59 for a proper lsc function and an
arbitrary real constant `σ`. -/
theorem subdifferential_strongMonotonicity_tfae [FiniteDimensional ℝ E] {f : E → EReal}
    (hp : IsProper f) (hl : LowerSemicontinuous f) (σ : ℝ) :
    List.TFAE [SvStronglyMonotoneWith σ (subdifferential f), StronglyConvexWith σ f,
      Convex ℝ (epigraph (fun x ↦ f x - ((σ / 2 * ‖x‖ ^ 2 : ℝ) : EReal)))] := by
  tfae_have 2 ↔ 3 := stronglyConvexWith_iff_convex_epigraph_sub (fun x ↦ (hp.2 x).ne') σ
  tfae_have 2 → 1 := StronglyConvexWith.svStronglyMonotoneWith_subdifferential hp
  tfae_have 1 → 3 := SvStronglyMonotoneWith.convex_epigraph_sub_quadratic hp hl
  tfae_finish

/-- **Exercise 12.59 (strong monotonicity versus strong convexity)**, with the
lower semicontinuity and properness needed for (a) ⇒ (b), (c): for a proper
lsc `f` and `σ > 0`, the following are equivalent: (a) `∂f` is strongly monotone
with constant `σ`; (b) `f` is strongly convex with constant `σ`; (c)
`f - ½σ|·|²` is convex. -/
theorem strongMonotonicity_versus_strongConvexity [FiniteDimensional ℝ E] {f : E → EReal}
    (hp : IsProper f) (hl : LowerSemicontinuous f) {σ : ℝ} (_hσ : 0 < σ) :
    List.TFAE [SvStronglyMonotoneWith σ (subdifferential f), StronglyConvexWith σ f,
      Convex ℝ (epigraph (fun x ↦ f x - ((σ / 2 * ‖x‖ ^ 2 : ℝ) : EReal)))] :=
  subdifferential_strongMonotonicity_tfae hp hl σ

section Counterexample

/-- Locality of regular subgradients. -/
theorem regularSubdifferential_congr {f g : E → EReal} {x : E} (h : f =ᶠ[𝓝 x] g) :
    regularSubdifferential f x = regularSubdifferential g x := by
  have hx : f x = g x := h.eq_of_nhds
  ext v
  simp only [regularSubdifferential, mem_setOf_eq, hx]
  refine exists_congr fun c ↦ and_congr_right fun _ ↦ forall_congr' fun ε ↦
    imp_congr_right fun _ ↦ ⟨fun hv ↦ ?_, fun hv ↦ ?_⟩
  · filter_upwards [hv, h] with y hy hfg
    rwa [← hfg]
  · filter_upwards [hv, h] with y hy hfg
    rwa [hfg]

/-- The function `f(x) = |x|²` for `x ≠ 0`, `f(0) = 1`, which is not lsc. -/
noncomputable def strongMonotonicityCounterexample (x : E) : EReal :=
  open Classical in if x = 0 then 1 else ((‖x‖ ^ 2 : ℝ) : EReal)

omit [InnerProductSpace ℝ E] in
theorem strongMonotonicityCounterexample_zero :
    strongMonotonicityCounterexample (0 : E) = 1 := by
  simp [strongMonotonicityCounterexample]

omit [InnerProductSpace ℝ E] in
theorem strongMonotonicityCounterexample_of_ne {x : E} (hx : x ≠ 0) :
    strongMonotonicityCounterexample x = ((‖x‖ ^ 2 : ℝ) : EReal) := by
  simp [strongMonotonicityCounterexample, hx]

variable [FiniteDimensional ℝ E]

private theorem cex_regular_ne {y : E} (hy : y ≠ 0) :
    regularSubdifferential (strongMonotonicityCounterexample (E := E)) y = {(2 : ℝ) • y} := by
  have hev : strongMonotonicityCounterexample (E := E) =ᶠ[𝓝 y]
      fun z ↦ ((‖z‖ ^ 2 : ℝ) : EReal) := by
    filter_upwards [isOpen_ne.mem_nhds hy] with z hz
    exact strongMonotonicityCounterexample_of_ne hz
  have hk : HasGradientAt (fun z : E ↦ ‖z‖ ^ 2) ((2 : ℝ) • y) y := by
    have := hasGradientAt_half_mul_norm_sq (E := E) 2 y
    simpa using this
  rw [regularSubdifferential_congr hev]
  exact (regularSubdifferential_of_hasGradientAt hk).1

omit [FiniteDimensional ℝ E] in
private theorem cex_regular_zero [Nontrivial E] :
    regularSubdifferential (strongMonotonicityCounterexample (E := E)) 0 = ∅ := by
  ext v
  simp only [mem_empty_iff_false, iff_false]
  rintro ⟨c, hc, hv⟩
  have hc1 : c = 1 := by
    rw [strongMonotonicityCounterexample_zero] at hc
    exact_mod_cast hc.symm
  subst hc1
  have h1 := hv 1 one_pos
  have hcont : ∀ᶠ z in 𝓝 (0 : E), ‖z‖ ^ 2 < 1 + ⟪v, z - 0⟫_ℝ - 1 * ‖z - 0‖ := by
    have hc : Continuous fun z : E ↦ 1 + ⟪v, z - 0⟫_ℝ - 1 * ‖z - 0‖ - ‖z‖ ^ 2 := by fun_prop
    have := hc.continuousAt (x := 0) |>.eventually (isOpen_Ioi.mem_nhds
      (show (0 : ℝ) < 1 + ⟪v, (0 : E) - 0⟫_ℝ - 1 * ‖(0 : E) - 0‖ - ‖(0 : E)‖ ^ 2 by simp))
    filter_upwards [this] with z hz
    linarith [show (0 : ℝ) < 1 + ⟪v, z - 0⟫_ℝ - 1 * ‖z - 0‖ - ‖z‖ ^ 2 from hz]
  have hzero : ∀ᶠ z in 𝓝 (0 : E), z = 0 := by
    filter_upwards [h1, hcont] with z hz hlt
    by_contra hne
    rw [strongMonotonicityCounterexample_of_ne hne, EReal.coe_le_coe_iff] at hz
    linarith
  obtain ⟨z, hz, hne⟩ := ((hzero.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin (s := {(0 : E)}ᶜ))).exists
  exact hne hz

private theorem cex_subdifferential [Nontrivial E] (x : E) :
    subdifferential (strongMonotonicityCounterexample (E := E)) x ⊆
      {v | x ≠ 0 ∧ v = (2 : ℝ) • x} := by
  intro v hv
  obtain ⟨-, xs, vs, hxs, hfx, hvs, hvlim⟩ := mem_subdifferential_iff_exists_seq.1 hv
  have hne : ∀ n, xs n ≠ 0 := by
    intro n h
    have := hvs n
    rw [h, cex_regular_zero] at this
    exact this
  have hvs' : ∀ n, vs n = (2 : ℝ) • xs n := by
    intro n
    have := hvs n
    rwa [cex_regular_ne (hne n), mem_singleton_iff] at this
  refine ⟨fun hx ↦ ?_, ?_⟩
  · subst hx
    have hval : ∀ n, strongMonotonicityCounterexample (xs n) = ((‖xs n‖ ^ 2 : ℝ) : EReal) :=
      fun n ↦ strongMonotonicityCounterexample_of_ne (hne n)
    have hlim0 : Tendsto (fun n ↦ ((‖xs n‖ ^ 2 : ℝ) : EReal)) atTop (𝓝 ((0 : ℝ) : EReal)) := by
      have : Tendsto (fun n ↦ ‖xs n‖ ^ 2) atTop (𝓝 (‖(0 : E)‖ ^ 2)) :=
        (hxs.norm).pow 2
      rw [norm_zero, zero_pow two_ne_zero] at this
      exact (continuous_coe_real_ereal.tendsto 0).comp this
    have hlim1 : Tendsto (fun n ↦ ((‖xs n‖ ^ 2 : ℝ) : EReal)) atTop
        (𝓝 (strongMonotonicityCounterexample (0 : E))) := by
      refine hfx.congr fun n ↦ ?_
      exact hval n
    have := tendsto_nhds_unique hlim0 hlim1
    rw [strongMonotonicityCounterexample_zero] at this
    norm_num at this
  · have : Tendsto vs atTop (𝓝 ((2 : ℝ) • x)) :=
      (hxs.const_smul (2 : ℝ)).congr fun n ↦ (hvs' n).symm
    exact tendsto_nhds_unique hvlim this

/-- **Correction to 12.59**: lower semicontinuity cannot be dropped.  The proper
function `f(x) = |x|²` (`x ≠ 0`), `f(0) = 1` has `∂f` strongly monotone with
constant `2`, but `f - |·|²` is not convex and `f` is not strongly convex with
constant `2`; in particular `f` is not lsc. -/
theorem strongMonotonicityCounterexample_spec [Nontrivial E] :
    IsProper (strongMonotonicityCounterexample (E := E)) ∧
      SvStronglyMonotoneWith 2 (subdifferential (strongMonotonicityCounterexample (E := E))) ∧
      ¬ Convex ℝ (epigraph (fun x ↦ strongMonotonicityCounterexample (E := E) x -
        (((2 : ℝ) / 2 * ‖x‖ ^ 2 : ℝ) : EReal))) ∧
      ¬ StronglyConvexWith 2 (strongMonotonicityCounterexample (E := E)) ∧
      ¬ LowerSemicontinuous (strongMonotonicityCounterexample (E := E)) := by
  obtain ⟨e, he⟩ := exists_ne (0 : E)
  have hne_bot : ∀ x, strongMonotonicityCounterexample (E := E) x ≠ ⊥ := by
    intro x
    by_cases hx : x = 0
    · rw [hx, strongMonotonicityCounterexample_zero]
      exact EReal.coe_ne_bot 1
    · rw [strongMonotonicityCounterexample_of_ne hx]
      exact EReal.coe_ne_bot _
  have hp : IsProper (strongMonotonicityCounterexample (E := E)) := by
    refine ⟨⟨0, ?_⟩, fun x ↦ bot_lt_iff_ne_bot.2 (hne_bot x)⟩
    rw [strongMonotonicityCounterexample_zero]
    exact EReal.coe_lt_top 1
  have hmono : SvStronglyMonotoneWith 2
      (subdifferential (strongMonotonicityCounterexample (E := E))) := by
    intro x₀ v₀ h₀ x₁ v₁ h₁
    obtain ⟨-, rfl⟩ := cex_subdifferential x₀ h₀
    obtain ⟨-, rfl⟩ := cex_subdifferential x₁ h₁
    rw [← smul_sub, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hnc : ¬ Convex ℝ (epigraph (fun x ↦ strongMonotonicityCounterexample (E := E) x -
      (((2 : ℝ) / 2 * ‖x‖ ^ 2 : ℝ) : EReal))) := by
    intro hc
    have hval : ∀ x : E, x ≠ 0 → strongMonotonicityCounterexample x -
        (((2 : ℝ) / 2 * ‖x‖ ^ 2 : ℝ) : EReal) = 0 := by
      intro x hx
      rw [strongMonotonicityCounterexample_of_ne hx, ← EReal.coe_sub]
      norm_num
    have hmem₁ : ((e, 0) : E × ℝ) ∈ epigraph (fun x ↦ strongMonotonicityCounterexample (E := E) x -
        (((2 : ℝ) / 2 * ‖x‖ ^ 2 : ℝ) : EReal)) := by
      change (((0 : ℝ) : EReal)) ≥ strongMonotonicityCounterexample e -
        (((2 : ℝ) / 2 * ‖e‖ ^ 2 : ℝ) : EReal)
      rw [hval e he]
      simp
    have hmem₂ : ((-e, 0) : E × ℝ) ∈ epigraph (fun x ↦ strongMonotonicityCounterexample (E := E) x -
        (((2 : ℝ) / 2 * ‖x‖ ^ 2 : ℝ) : EReal)) := by
      change (((0 : ℝ) : EReal)) ≥ strongMonotonicityCounterexample (-e) -
        (((2 : ℝ) / 2 * ‖-e‖ ^ 2 : ℝ) : EReal)
      rw [hval (-e) (neg_ne_zero.2 he)]
      simp
    have hmid := hc hmem₁ hmem₂ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    have e₁ : (1 / 2 : ℝ) • ((e, 0) : E × ℝ) + (1 / 2 : ℝ) • ((-e, 0) : E × ℝ) = (0, 0) := by
      ext <;> simp
    rw [e₁] at hmid
    change (((0 : ℝ) : EReal)) ≥ strongMonotonicityCounterexample (0 : E) -
      (((2 : ℝ) / 2 * ‖(0 : E)‖ ^ 2 : ℝ) : EReal) at hmid
    rw [strongMonotonicityCounterexample_zero, norm_zero] at hmid
    norm_num at hmid
    exact absurd hmid (not_le.2 zero_lt_one)
  have hnsc : ¬ StronglyConvexWith 2 (strongMonotonicityCounterexample (E := E)) := fun h ↦
    hnc ((stronglyConvexWith_iff_convex_epigraph_sub hne_bot 2).1 h)
  refine ⟨hp, hmono, hnc, hnsc, fun hl ↦ hnc ?_⟩
  exact hmono.convex_epigraph_sub_quadratic hp hl

end Counterexample

section ProximalFunctions

variable [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- The mapping `∂f + λ⁻¹I` is `∂f - (-λ⁻¹)I`. -/
theorem svAdd_subdifferential_smul_eq_svSubId (f : E → EReal) (lam : ℝ) :
    svAdd (subdifferential f) (fun x ↦ ({lam⁻¹ • x} : Set E)) =
      svSubId (subdifferential f) (-lam⁻¹) := by
  funext x
  ext w
  simp only [mem_svAdd, mem_singleton_iff, exists_eq_left, mem_svSubId, neg_smul]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rwa [add_neg_cancel_right]
  · intro h
    exact ⟨_, h, neg_add_cancel_right w _⟩

/-- **Exercise 12.61 (hypoconvexity properties of proximal functions)**: for a
proper lsc `f` and `λ > 0`, the following are equivalent: (a) `f` is
`λ`-proximal, `h_λ f = f`; (b) `∂f + λ⁻¹I` is monotone; (c)
`f((1 - τ)x₀ + τx₁) ≤ (1 - τ)f(x₀) + τf(x₁) + ½λ⁻¹τ(1 - τ)|x₀ - x₁|²` for all
`x₀, x₁` and `τ ∈ (0, 1)`. -/
theorem hypoconvexity_of_proximal_functions {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) {lam : ℝ} (hlam : 0 < lam) :
    List.TFAE [proximalHull f lam = f,
      SvMonotone (svAdd (subdifferential f) (fun x ↦ ({lam⁻¹ • x} : Set E))),
      ∀ ⦃x₀ x₁ : E⦄ ⦃τ : ℝ⦄, 0 < τ → τ < 1 →
        f ((1 - τ) • x₀ + τ • x₁) ≤ ((1 - τ : ℝ) : EReal) * f x₀ + (τ : EReal) * f x₁ +
          ((1 / 2 * lam⁻¹ * τ * (1 - τ) * ‖x₀ - x₁‖ ^ 2 : ℝ) : EReal)] := by
  have htfae := subdifferential_strongMonotonicity_tfae hp hl (-lam⁻¹)
  have hab : SvMonotone (svAdd (subdifferential f) (fun x ↦ ({lam⁻¹ • x} : Set E))) ↔
      SvStronglyMonotoneWith (-lam⁻¹) (subdifferential f) := by
    rw [svAdd_subdifferential_smul_eq_svSubId, svStronglyMonotoneWith_iff_svMonotone_svSubId]
  have hcc : (∀ ⦃x₀ x₁ : E⦄ ⦃τ : ℝ⦄, 0 < τ → τ < 1 →
        f ((1 - τ) • x₀ + τ • x₁) ≤ ((1 - τ : ℝ) : EReal) * f x₀ + (τ : EReal) * f x₁ +
          ((1 / 2 * lam⁻¹ * τ * (1 - τ) * ‖x₀ - x₁‖ ^ 2 : ℝ) : EReal)) ↔
      StronglyConvexWith (-lam⁻¹) f := by
    unfold StronglyConvexWith
    refine forall_congr' fun x₀ ↦ forall_congr' fun x₁ ↦ forall_congr' fun τ ↦
      imp_congr_right fun _ ↦ imp_congr_right fun _ ↦ ?_
    rw [ereal_sub_coe_eq_add_coe_neg]
    have e : -(-lam⁻¹ / 2 * τ * (1 - τ) * ‖x₀ - x₁‖ ^ 2) =
        1 / 2 * lam⁻¹ * τ * (1 - τ) * ‖x₀ - x₁‖ ^ 2 := by ring
    rw [e]
  have hac : proximalHull f lam = f ↔
      Convex ℝ (epigraph (fun x ↦ f x - ((-lam⁻¹ / 2 * ‖x‖ ^ 2 : ℝ) : EReal))) := by
    rw [proximalHull_eq_self_iff hp hlam]
    have e : (fun y ↦ f y + (moreauQuadratic lam y : EReal)) =
        fun x ↦ f x - ((-lam⁻¹ / 2 * ‖x‖ ^ 2 : ℝ) : EReal) := by
      funext x
      rw [ereal_sub_coe_eq_add_coe_neg, moreauQuadratic]
      congr 2
      field_simp
    rw [e]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨hl, h⟩⟩
  tfae_have 2 ↔ 3 := hab.trans ((htfae.out 0 1).trans hcc.symm)
  tfae_have 1 ↔ 3 := hac.trans ((htfae.out 2 1).trans hcc.symm)
  tfae_finish

end ProximalFunctions

end RW
