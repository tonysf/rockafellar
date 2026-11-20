/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 10: the nonsmooth Lagrange multiplier rule

**Exercise 10.52** for the problem of minimizing `f₀(x) + θ(F(x))` over `x ∈ X`, with `X` closed,
`f₀` and `F` strictly continuous at the local minimizer `x̄`, and `θ` proper, lsc and convex with
effective domain `D`: under the constraint qualification
`0 ∈ ∂(yF)(x̄) + N_X(x̄), y ∈ N_D(F(x̄)) ⟹ y = 0`, there is `ȳ ∈ ∂θ(F(x̄))` with
`0 ∈ ∂(f₀ + ȳF)(x̄) + N_X(x̄)` (`exists_nonsmooth_multiplier`).

As in the book's guide, the problem is `f = g ∘ G` with `G(x) = (f₀(x), (F(x), x))` and the
separable `g(w₀, (w, z)) = w₀ + θ(w) + δ_X(z)`, whose subgradients (10.5, 8.12, 8.14) are
`{1} × ∂θ × N_X` and whose horizon subgradients lie in `{0} × N_D × N_X`; the extended chain rule
10.49 and the Fermat rule 10.1 then give the multiplier.  Only strict continuity at `x̄` is used.
Not formalized: the compactness of the set of multipliers `ȳ`.
-/

import RockafellarWets.Chapter10.StrictlyContinuousMaxima
import RockafellarWets.Chapter10.SeparableSubgradients
import RockafellarWets.Chapter10.SeparableSubderivatives
import RockafellarWets.Chapter10.FermatRule
import RockafellarWets.Chapter10.DistanceSubsmoothness
import RockafellarWets.Chapter8.ConvexSubgradients
import RockafellarWets.Chapter8.SubgradientsAndGradients

open Filter Function Metric Set Topology
open scoped NNReal ENNReal InnerProductSpace Pointwise Gradient

namespace RW

variable {E F H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] in
/-- A pair of mappings strictly continuous at `x̄` is strictly continuous at `x̄` into the
Euclidean product. -/
theorem strictlyContinuousAt_toLp_prod {G₁ : E → F} {G₂ : E → H} {x : E}
    (h₁ : StrictlyContinuousAt G₁ x) (h₂ : StrictlyContinuousAt G₂ x) :
    StrictlyContinuousAt (fun a ↦ WithLp.toLp 2 (G₁ a, G₂ a)) x := by
  obtain ⟨k₁, U₁, hU₁, hL₁⟩ := strictlyContinuousAt_iff.1 h₁
  obtain ⟨k₂, U₂, hU₂, hL₂⟩ := strictlyContinuousAt_iff.1 h₂
  refine strictlyContinuousAt_iff.2 ⟨k₁ + k₂, U₁ ∩ U₂, inter_mem hU₁ hU₂,
    LipschitzOnWith.of_dist_le_mul fun a ha b hb ↦ ?_⟩
  have e₁ := hL₁.dist_le_mul a ha.1 b hb.1
  have e₂ := hL₂.dist_le_mul a ha.2 b hb.2
  have d₁ := dist_nonneg (x := G₁ a) (y := G₁ b)
  have d₂ := dist_nonneg (x := G₂ a) (y := G₂ b)
  rw [WithLp.prod_dist_eq_of_L2, Real.sqrt_le_iff]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd, NNReal.coe_add]
  constructor
  · positivity
  · nlinarith [dist_nonneg (x := a) (y := b), (k₁ : ℝ≥0).2, (k₂ : ℝ≥0).2]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem strictlyContinuousAt_id' (x : E) : StrictlyContinuousAt (fun a : E ↦ a) x :=
  strictlyContinuousAt_iff.2 ⟨1, univ, univ_mem, LipschitzWith.id.lipschitzOnWith⟩

/-- Adding a linear function translates subgradients: `∂(h + ⟪v, ·⟫)(x̄) = ∂h(x̄) + v`. -/
theorem subdifferential_add_inner {h : E → ℝ} {x : E} (v : E) :
    subdifferential (fun a ↦ ((h a + ⟪v, a⟫_ℝ : ℝ) : EReal)) x =
      (fun u ↦ u + v) '' subdifferential (fun a ↦ ((h a : ℝ) : EReal)) x := by
  have hk : ContDiffAt ℝ 1 (fun a : E ↦ ⟪v, a⟫_ℝ) x := (innerSL ℝ v).contDiff.contDiffAt
  have hgrad : ∇ (fun a : E ↦ ⟪v, a⟫_ℝ) x = v :=
    (hasGradientAt_iff_hasFDerivAt.2 (innerSL ℝ v).hasFDerivAt).gradient
  have h := (subdifferentials_add_smooth (g := fun a ↦ ((h a : ℝ) : EReal)) (c := h x) rfl hk).2.1
  simp only [hgrad] at h
  rw [← h]
  congr 1

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] in
theorem withLp_prod_eq_zero {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    {p : WithLp 2 (A × B)} (h₁ : p.fst = 0) (h₂ : p.snd = 0) : p = 0 := by
  apply WithLp.ofLp_injective 2
  rw [WithLp.ofLp_zero]
  exact Prod.ext h₁ h₂

/-- The identity `ℝ → ℝ̄` has strict gradient `1`. -/
theorem hasStrictGradientAt_coe (t : ℝ) : HasStrictGradientAt (fun s : ℝ ↦ (s : EReal)) 1 t := by
  refine ⟨Eventually.of_forall fun s ↦ by rw [EReal.toReal_coe], ?_⟩
  simp only [EReal.toReal_coe]
  exact (hasStrictFDerivAt_id t).congr_fderiv (by ext; simp)

/-- **Exercise 10.52** (nonsmooth Lagrange multiplier rule): if `x̄ ∈ X` locally minimizes
`f₀ + θ ∘ F + δ_X` and the constraint qualification holds, there is `ȳ ∈ ∂θ(F(x̄))` with
`0 ∈ ∂(f₀ + ȳF)(x̄) + N_X(x̄)`. -/
theorem exists_nonsmooth_multiplier {X : Set E} {f₀ : E → ℝ} {G : E → F} {θ : F → EReal}
    {x : E} {c : ℝ} (hX : IsClosed X) (hf₀ : StrictlyContinuousAt f₀ x)
    (hG : StrictlyContinuousAt G x) (hθp : IsProper θ) (hθl : LowerSemicontinuous θ)
    (hθc : Convex ℝ (epigraph θ)) (hxX : x ∈ X) (hc : θ (G x) = c)
    (hmin : IsLocalMin (fun a ↦ ((f₀ a : ℝ) : EReal) + (θ (G a) + indicatorVA X a)) x)
    (hQ : ∀ y ∈ normalCone (effectiveDomain θ) (G x),
      (0 : E) ∈ subdifferential (fun a ↦ ((⟪y, G a⟫_ℝ : ℝ) : EReal)) x + normalCone X x →
        y = 0) :
    ∃ y ∈ subdifferential θ (G x),
      (0 : E) ∈ subdifferential (fun a ↦ ((f₀ a + ⟪y, G a⟫_ℝ : ℝ) : EReal)) x +
        normalCone X x := by
  set Ĝ : E → WithLp 2 (ℝ × WithLp 2 (F × E)) :=
    fun a ↦ WithLp.toLp 2 (f₀ a, WithLp.toLp 2 (G a, a)) with hĜdef
  set g₁ : WithLp 2 (F × E) → EReal := separableSum θ (indicatorVA X) with hg₁
  set g : WithLp 2 (ℝ × WithLp 2 (F × E)) → EReal :=
    separableSum (fun t : ℝ ↦ (t : EReal)) g₁ with hg
  have hĜ : StrictlyContinuousAt Ĝ x :=
    strictlyContinuousAt_toLp_prod hf₀ (strictlyContinuousAt_toLp_prod hG
      (strictlyContinuousAt_id' x))
  have hXp : IsProper (indicatorVA X) := isProper_indicatorVA ⟨x, hxX⟩
  have hXl : LowerSemicontinuous (indicatorVA X) := lowerSemicontinuous_indicatorVA hX
  have hcl : LowerSemicontinuous (fun t : ℝ ↦ (t : EReal)) :=
    continuous_coe_real_ereal.lowerSemicontinuous
  have hcp : IsProper (fun t : ℝ ↦ (t : EReal)) :=
    ⟨⟨0, EReal.coe_lt_top _⟩, fun t ↦ EReal.bot_lt_coe t⟩
  have hX0 : indicatorVA X x = ((0 : ℝ) : EReal) := indicatorVA_eq_zero_of_mem hxX
  have hg₁v : g₁ (WithLp.toLp 2 (G x, x)) = ((c + 0 : ℝ) : EReal) := by
    show θ (G x) + indicatorVA X x = _
    rw [hc, hX0, EReal.coe_add]
  have hg₁p : IsProper g₁ := by
    refine ⟨⟨WithLp.toLp 2 (G x, x), ?_⟩, fun p ↦ ?_⟩
    · rw [hg₁v]
      exact EReal.coe_lt_top _
    · show ⊥ < θ p.fst + indicatorVA X p.snd
      exact EReal.bot_lt_add_iff.2 ⟨hθp.2 _, hXp.2 _⟩
  have hg₁l : LowerSemicontinuous g₁ := lowerSemicontinuous_separableSum hθl hXl hθp hXp
  have hgl : LowerSemicontinuous g := lowerSemicontinuous_separableSum hcl hg₁l hcp hg₁p
  have hval : g (Ĝ x) = ((f₀ x + (c + 0) : ℝ) : EReal) := by
    show ((f₀ x : ℝ) : EReal) + g₁ (WithLp.toLp 2 (G x, x)) = _
    rw [hg₁v, ← EReal.coe_add]
  have hcoe1 : subdifferential (fun s : ℝ ↦ (s : EReal)) (f₀ x) = {1} :=
    (hasStrictGradientAt_coe (f₀ x)).subdifferential_eq
  have hcoe0 : horizonSubdifferential (fun s : ℝ ↦ (s : EReal)) (f₀ x) = {0} :=
    (eRealStrictlyContinuousAt_iff_horizonSubdifferential_eq_zero (c := f₀ x) rfl
      (hasStrictGradientAt_coe (f₀ x)).eRealStrictlyContinuousAt.isLocallyLscAt).1
      (hasStrictGradientAt_coe (f₀ x)).eRealStrictlyContinuousAt
  have hinner : ∀ (y' : WithLp 2 (ℝ × WithLp 2 (F × E))) (a : E),
      ⟪y', Ĝ a⟫_ℝ = (y'.fst * f₀ a + ⟪y'.snd.fst, G a⟫_ℝ) + ⟪y'.snd.snd, a⟫_ℝ := by
    intro y' a
    change ⟪y'.fst, f₀ a⟫_ℝ + (⟪y'.snd.fst, G a⟫_ℝ + ⟪y'.snd.snd, a⟫_ℝ) = _
    rw [real_inner_eq_mul', add_assoc]
  have hsplit : ∀ y' : WithLp 2 (ℝ × WithLp 2 (F × E)),
      subdifferential (fun a ↦ ((⟪y', Ĝ a⟫_ℝ : ℝ) : EReal)) x =
        (fun u ↦ u + y'.snd.snd) '' subdifferential
          (fun a ↦ ((y'.fst * f₀ a + ⟪y'.snd.fst, G a⟫_ℝ : ℝ) : EReal)) x := by
    intro y'
    rw [← subdifferential_add_inner]
    simp only [hinner]
  have hQ' : ∀ y' ∈ horizonSubdifferential g (Ĝ x),
      (0 : E) ∈ subdifferential (fun a ↦ ((⟪y', Ĝ a⟫_ℝ : ℝ) : EReal)) x → y' = 0 := by
    intro y' hy' h0
    obtain ⟨hy1, hy2⟩ := horizonSubdifferential_separableSum_subset (hcl (f₀ x)) (hg₁l _) rfl
      hg₁v hy'
    obtain ⟨hy21, hy22⟩ := horizonSubdifferential_separableSum_subset (hθl (G x)) (hXl x) hc
      hX0 hy2
    rw [hcoe0, mem_singleton_iff] at hy1
    rw [horizonSubdifferential_indicatorVA] at hy22
    have hyD := horizonSubdifferential_subset_normalCone_domain hθc hθp hc hy21
    rw [hsplit, hy1] at h0
    obtain ⟨u, hu, huv⟩ := h0
    simp only [zero_mul, zero_add] at hu
    have hy0 : y'.snd.fst = 0 := hQ _ hyD ⟨u, hu, y'.snd.snd, hy22, huv⟩
    rw [hy0] at hu
    simp only [inner_zero_left] at hu
    rw [(hasStrictGradientAt_zero_of_eventually_eq (c := 0)
      (Eventually.of_forall fun _ ↦ rfl)).subdifferential_eq, mem_singleton_iff] at hu
    rw [hu] at huv
    have hv0 : y'.snd.snd = 0 := by simpa using huv
    exact withLp_prod_eq_zero hy1 (withLp_prod_eq_zero hy0 hv0)
  have h0 : (0 : E) ∈ subdifferential (fun a ↦ g (Ĝ a)) x :=
    RW.IsLocalMin.zero_mem_subdifferential hmin hval
  obtain ⟨y', hy', h0'⟩ := (subdifferential_comp_subset_of_strictlyContinuous hgl hĜ hval hQ').1 h0
  obtain ⟨hy1, hy2⟩ := (mem_subdifferential_separableSum_iff (hcl (f₀ x)) (hg₁l _) rfl hg₁v y').1
    hy'
  obtain ⟨hy21, hy22⟩ := (mem_subdifferential_separableSum_iff (hθl (G x)) (hXl x) hc hX0
    y'.snd).1 hy2
  rw [hcoe1, mem_singleton_iff] at hy1
  rw [subdifferential_indicatorVA] at hy22
  rw [hsplit, hy1] at h0'
  obtain ⟨u, hu, huv⟩ := h0'
  simp only [one_mul] at hu
  exact ⟨y'.snd.fst, hy21, u, hu, y'.snd.snd, hy22, huv⟩

end RW
