/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: Subgradient convergence for convex functions

Theorem 12.35 (Attouch), Exercise 12.36 and Exercise 12.40.

Exercise 12.36 follows the guide.  The upper estimate comes from the
subgradient inequality at `xν` tested at a recovery sequence for `x̄`.  For the
conjugates, `fν*(vν) = ⟪vν, xν⟫ - fν(xν)` converges to `⟪v̄, x̄⟫ - f(x̄)`, and this
limit dominates `⟪v̄, y⟫ - f(y)` for every `y` through a recovery sequence for
`y`, so it equals `f*(v̄)`.  Neither lower semicontinuity nor properness of the
`fν`, nor any property of the limit `f`, is needed beyond convexity of the `fν`.

For Theorem 12.35 the proximal mappings are the resolvents `(I + λ∂fν)⁻¹`
(12.19) and the envelopes are `eλfν(z) = fν(Pλfν(z)) + (2λ)⁻¹|Pλfν(z) - z|²`.
(a) ⇒ (c) is Exercise 7.38 and Theorem 7.37, whose threshold condition holds
because convex sequences with a proper epi-limit have infinite eventual
prox-threshold.  (b) ⇔ (c) is the resolvent characterization of 12.32 together
with the correspondence `x̃ = x̄ + λv̄` between graph points and centers.  For
(c) ⇒ (a) the envelopes satisfy the two-sided estimate
`|eλf(y) - eλf(x) - ⟪λ⁻¹(x - Pλf(x)), y - x⟫| ≤ (2λ)⁻¹|y - x|²` of 12.23, so their
values are recovered from the gradients `λ⁻¹(I - Pλf)` by telescoping along a
segment, without integration.  Pointwise convergence of the envelopes then
gives epi-convergence by the convex form of 7.37.

Exercise 12.40(a) is proved without the simplex construction of the guide: if
the `Tν` were not uniformly bounded near `x̄`, normalized unbounded graph
points would give a nonzero `u` with `⟪u, a - x̄⟫ ≤ 0` for all `a ∈ dom T`,
contradicting `x̄ ∈ int(dom T)`.  Near `x̄` the `Tν` are then locally bounded,
and 12.38 with a connectedness argument shows that a neighborhood of `x̄` lies
in `dom Tν` for large `ν`, which gives `Tν(xν) → T(x̄)` when `T(x̄)` is a
singleton.
-/

import RockafellarWets.Chapter12.MonotoneDomains
import RockafellarWets.Chapter12.MoreauYosida
import RockafellarWets.Chapter7.ConvexMoreauCharacterization
import RockafellarWets.Chapter7.ProximalMappingLimits
import RockafellarWets.Chapter7.SemidifferentiabilityCharacterizations
import RockafellarWets.Chapter9.ConvexLipschitzBounds
import RockafellarWets.Chapter11.Lagrangians

open Bornology Filter Metric Set Topology
open scoped InnerProductSpace Pointwise

namespace RW

section ERealLimits

/-- Subtracting a convergent extended real from a convergent real. -/
theorem tendsto_coe_sub_ereal {α : Type*} {l : Filter α} {a : α → ℝ} {b : α → EReal} {a₀ : ℝ}
    {b₀ : EReal} (ha : Tendsto a l (𝓝 a₀)) (hb : Tendsto b l (𝓝 b₀)) :
    Tendsto (fun t ↦ ((a t : ℝ) : EReal) - b t) l (𝓝 ((a₀ : EReal) - b₀)) := by
  have hcont : ContinuousAt (fun p : EReal × EReal ↦ p.1 + p.2) ((a₀ : EReal), -b₀) :=
    EReal.continuousAt_add (Or.inl (EReal.coe_ne_top a₀)) (Or.inl (EReal.coe_ne_bot a₀))
  have h := hcont.tendsto.comp ((EReal.tendsto_coe.2 ha).prodMk_nhds
    ((continuous_neg.tendsto b₀).comp hb))
  simpa only [sub_eq_add_neg, Function.comp_def] using h

/-- Adding a convergent real to a convergent extended real. -/
theorem tendsto_ereal_add_coe {α : Type*} {l : Filter α} {a : α → ℝ} {b : α → EReal} {a₀ : ℝ}
    {b₀ : EReal} (hb : Tendsto b l (𝓝 b₀)) (ha : Tendsto a l (𝓝 a₀)) :
    Tendsto (fun t ↦ b t + ((a t : ℝ) : EReal)) l (𝓝 (b₀ + (a₀ : EReal))) := by
  have hcont : ContinuousAt (fun p : EReal × EReal ↦ p.1 + p.2) (b₀, (a₀ : EReal)) :=
    EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot a₀)) (Or.inr (EReal.coe_ne_top a₀))
  exact hcont.tendsto.comp (hb.prodMk_nhds (EReal.tendsto_coe.2 ha))

end ERealLimits

section ConvexValues

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Exercise 12.36**, function values: if `fν →e f` with `fν` convex and
`vν ∈ ∂fν(xν)` with `xν → x̄` and `vν → v̄`, then `fν(xν) → f(x̄)`. -/
theorem tendsto_apply_of_mem_subdifferential {f : ℕ → E → EReal} {g : E → EReal}
    (hfc : ∀ n, Convex ℝ (epigraph (f n))) (h : EpiConverges f g) {x v : ℕ → E}
    {xbar vbar : E} (hv : ∀ n, v n ∈ subdifferential (f n) (x n))
    (hx : Tendsto x atTop (𝓝 xbar)) (hvl : Tendsto v atTop (𝓝 vbar)) :
    Tendsto (fun n ↦ f n (x n)) atTop (𝓝 (g xbar)) := by
  obtain ⟨hlo, -⟩ := epiConverges_iff_liminf_limsup.1 h xbar
  have hlow := hlo x hx
  obtain ⟨y, hy, hfy⟩ := h.exists_tendsto_values xbar
  choose c hc using fun n ↦ (hv n).1
  have hsub : ∀ n, ((c n + ⟪v n, y n - x n⟫_ℝ : ℝ) : EReal) ≤ f n (y n) := fun n ↦
    forall_le_of_mem_subdifferential_of_convex (hfc n) (hc n) (hv n) (y n)
  have hr : Tendsto (fun n ↦ ⟪v n, y n - x n⟫_ℝ) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n ↦ ⟪v n, y n - x n⟫_ℝ) atTop (𝓝 ⟪vbar, xbar - xbar⟫_ℝ) :=
      hvl.inner (hy.sub hx)
    rwa [sub_self, inner_zero_right] at h1
  refine tendsto_order.2 ⟨fun a ha ↦ eventually_lt_of_lt_liminf (ha.trans_le hlow),
    fun b hb ↦ ?_⟩
  obtain ⟨β₂, hβ₂, hβ₂b⟩ := EReal.lt_iff_exists_real_btwn.1 hb
  obtain ⟨β₁, hβ₁, hβ₁₂⟩ := EReal.lt_iff_exists_real_btwn.1 hβ₂
  have hβ : β₁ < β₂ := EReal.coe_lt_coe_iff.1 hβ₁₂
  filter_upwards [hfy.eventually (gt_mem_nhds hβ₁),
    hr.eventually (Metric.ball_mem_nhds 0 (sub_pos.2 hβ))] with n h1 h2
  rw [Real.dist_eq, sub_zero] at h2
  have h3 : c n + ⟪v n, y n - x n⟫_ℝ < β₁ := EReal.coe_lt_coe_iff.1 ((hsub n).trans_lt h1)
  rw [hc n]
  refine lt_trans (EReal.coe_lt_coe_iff.2 ?_) hβ₂b
  linarith [neg_abs_le ⟪v n, y n - x n⟫_ℝ]

/-- For a convex function, a subgradient attains the supremum defining the
conjugate: `f*(v) = ⟪v, x⟫ - f(x)` when `v ∈ ∂f(x)`. -/
theorem fenchelConjugate_eq_of_mem_subdifferential_of_convex {f : E → EReal}
    (hc : Convex ℝ (epigraph f)) {x v : E} (hv : v ∈ subdifferential f x) :
    fenchelConjugate f v = (⟪v, x⟫_ℝ : EReal) - f x := by
  obtain ⟨c, hcx⟩ := hv.1
  refine le_antisymm ((fenchelConjugate_le_iff f v _).2 fun y ↦ ?_) (le_fenchelConjugate f x v)
  have hy := forall_le_of_mem_subdifferential_of_convex hc hcx hv y
  rw [hcx, ← EReal.coe_sub]
  rcases eq_top_or_lt_top (f y) with hfy | hfy
  · rw [hfy, EReal.sub_top]
    exact bot_le
  · have hfy' : f y = ((f y).toReal : EReal) :=
      (EReal.coe_toReal hfy.ne ((EReal.bot_lt_coe _).trans_le hy).ne').symm
    rw [hfy', ← EReal.coe_sub, EReal.coe_le_coe_iff]
    rw [hfy', EReal.coe_le_coe_iff, inner_sub_right] at hy
    linarith

/-- **Exercise 12.36**, conjugate values: under the hypotheses of the first part,
`fν*(vν) → f*(v̄)`. -/
theorem tendsto_fenchelConjugate_of_mem_subdifferential {f : ℕ → E → EReal} {g : E → EReal}
    (hfc : ∀ n, Convex ℝ (epigraph (f n))) (h : EpiConverges f g) {x v : ℕ → E}
    {xbar vbar : E} (hv : ∀ n, v n ∈ subdifferential (f n) (x n))
    (hx : Tendsto x atTop (𝓝 xbar)) (hvl : Tendsto v atTop (𝓝 vbar)) :
    Tendsto (fun n ↦ fenchelConjugate (f n) (v n)) atTop (𝓝 (fenchelConjugate g vbar)) := by
  have hval := tendsto_apply_of_mem_subdifferential hfc h hv hx hvl
  have hconj : ∀ n, fenchelConjugate (f n) (v n) = (⟪v n, x n⟫_ℝ : EReal) - f n (x n) :=
    fun n ↦ fenchelConjugate_eq_of_mem_subdifferential_of_convex (hfc n) (hv n)
  have hlim : Tendsto (fun n ↦ fenchelConjugate (f n) (v n)) atTop
      (𝓝 ((⟪vbar, xbar⟫_ℝ : EReal) - g xbar)) := by
    simp only [hconj]
    exact tendsto_coe_sub_ereal (hvl.inner hx) hval
  have heq : fenchelConjugate g vbar = (⟪vbar, xbar⟫_ℝ : EReal) - g xbar := by
    refine le_antisymm ((fenchelConjugate_le_iff g vbar _).2 fun z ↦ ?_)
      (le_fenchelConjugate g xbar vbar)
    obtain ⟨y, hy, hfy⟩ := h.exists_tendsto_values z
    exact le_of_tendsto_of_tendsto (tendsto_coe_sub_ereal (hvl.inner hy) hfy) hlim
      (Eventually.of_forall fun n ↦ le_fenchelConjugate (f n) (y n) (v n))
  rw [heq]
  exact hlim

/-- **Exercise 12.36 (convergence of convex function values)**: if `fν →e f`
with `fν` convex, `vν ∈ ∂fν(xν)`, `xν → x̄` and `vν → v̄`, then `fν(xν) → f(x̄)` and
`fν*(vν) → f*(v̄)`. -/
theorem convergence_of_convex_function_values {f : ℕ → E → EReal} {g : E → EReal}
    (hfc : ∀ n, Convex ℝ (epigraph (f n))) (h : EpiConverges f g) {x v : ℕ → E}
    {xbar vbar : E} (hv : ∀ n, v n ∈ subdifferential (f n) (x n))
    (hx : Tendsto x atTop (𝓝 xbar)) (hvl : Tendsto v atTop (𝓝 vbar)) :
    Tendsto (fun n ↦ f n (x n)) atTop (𝓝 (g xbar)) ∧
      Tendsto (fun n ↦ fenchelConjugate (f n) (v n)) atTop (𝓝 (fenchelConjugate g vbar)) :=
  ⟨tendsto_apply_of_mem_subdifferential hfc h hv hx hvl,
    tendsto_fenchelConjugate_of_mem_subdifferential hfc h hv hx hvl⟩

end ConvexValues

section Telescoping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Telescoping a quadratic first-order estimate along a segment cut into `m`
steps: `ψ(x) - ψ(x₀)` is the Riemann sum of `⟪γ, ·⟫` up to `C|x - x₀|²/m`. -/
theorem abs_sub_sub_sum_le {ψ : E → ℝ} {γ : E → E} {C : ℝ}
    (hψ : ∀ x y, |ψ y - ψ x - ⟪γ x, y - x⟫_ℝ| ≤ C * ‖y - x‖ ^ 2) (x₀ x : E) {m : ℕ}
    (hm : 0 < m) :
    |ψ x - ψ x₀ - ∑ k ∈ Finset.range m,
        ⟪γ (x₀ + ((k : ℝ) / m) • (x - x₀)), (1 / (m : ℝ)) • (x - x₀)⟫_ℝ| ≤
      C * ‖x - x₀‖ ^ 2 / m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set z : ℕ → E := fun k ↦ x₀ + ((k : ℝ) / m) • (x - x₀) with hz
  have hstep : ∀ k : ℕ, z (k + 1) - z k = (1 / (m : ℝ)) • (x - x₀) := by
    intro k
    simp only [hz]
    rw [add_sub_add_left_eq_sub, ← sub_smul]
    congr 1
    push_cast
    ring
  have hz0 : z 0 = x₀ := by simp [hz]
  have hzm : z m = x := by
    simp only [hz]
    rw [div_self hm'.ne', one_smul, add_sub_cancel]
  have htel : ψ x - ψ x₀ = ∑ k ∈ Finset.range m, (ψ (z (k + 1)) - ψ (z k)) := by
    rw [Finset.sum_range_sub (fun k ↦ ψ (z k)), hzm, hz0]
  rw [htel, ← Finset.sum_sub_distrib]
  calc |∑ k ∈ Finset.range m, (ψ (z (k + 1)) - ψ (z k) -
          ⟪γ (z k), (1 / (m : ℝ)) • (x - x₀)⟫_ℝ)|
        ≤ ∑ k ∈ Finset.range m, |ψ (z (k + 1)) - ψ (z k) -
          ⟪γ (z k), (1 / (m : ℝ)) • (x - x₀)⟫_ℝ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ Finset.range m, C * ‖(1 / (m : ℝ)) • (x - x₀)‖ ^ 2 := by
        refine Finset.sum_le_sum fun k _ ↦ ?_
        have := hψ (z k) (z (k + 1))
        rwa [hstep k] at this
      _ = C * ‖x - x₀‖ ^ 2 / m := by
        have hm'' : (m : ℝ) ≠ 0 := hm'.ne'
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, norm_smul,
          Real.norm_of_nonneg (by positivity)]
        field_simp

/-- Functions with a uniform quadratic first-order estimate are determined by
their gradients: pointwise convergence of the gradients and convergence at
one point give pointwise convergence everywhere. -/
theorem tendsto_of_quadratic_estimate {φs : ℕ → E → ℝ} {φ : E → ℝ} {γs : ℕ → E → E}
    {γ : E → E} {C : ℝ}
    (hs : ∀ n x y, |φs n y - φs n x - ⟪γs n x, y - x⟫_ℝ| ≤ C * ‖y - x‖ ^ 2)
    (h : ∀ x y, |φ y - φ x - ⟪γ x, y - x⟫_ℝ| ≤ C * ‖y - x‖ ^ 2)
    (hγ : ∀ x, Tendsto (fun n ↦ γs n x) atTop (𝓝 (γ x))) {x₀ : E}
    (h₀ : Tendsto (fun n ↦ φs n x₀) atTop (𝓝 (φ x₀))) (x : E) :
    Tendsto (fun n ↦ φs n x) atTop (𝓝 (φ x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_gt (max 0 (4 * C * ‖x - x₀‖ ^ 2 / ε))
  have hmR : (0 : ℝ) < m := (le_max_left _ _).trans_lt hm
  have hm0 : 0 < m := by exact_mod_cast hmR
  have hsmall : C * ‖x - x₀‖ ^ 2 / m < ε / 4 := by
    have h1 : 4 * C * ‖x - x₀‖ ^ 2 / ε < m := (le_max_right _ _).trans_lt hm
    rw [div_lt_iff₀ hε] at h1
    rw [div_lt_iff₀ hmR]
    nlinarith
  set S : ℕ → ℝ := fun n ↦ ∑ k ∈ Finset.range m,
    ⟪γs n (x₀ + ((k : ℝ) / m) • (x - x₀)), (1 / (m : ℝ)) • (x - x₀)⟫_ℝ with hS
  set S₀ : ℝ := ∑ k ∈ Finset.range m,
    ⟪γ (x₀ + ((k : ℝ) / m) • (x - x₀)), (1 / (m : ℝ)) • (x - x₀)⟫_ℝ with hS₀
  have hSlim : Tendsto S atTop (𝓝 S₀) :=
    tendsto_finset_sum _ fun k _ ↦ (hγ _).inner tendsto_const_nhds
  have hev : ∀ᶠ n in atTop, |S n - S₀| < ε / 4 ∧ |φs n x₀ - φ x₀| < ε / 4 := by
    have h1 := (Metric.tendsto_nhds.1 hSlim) (ε / 4) (by positivity)
    have h2 := (Metric.tendsto_nhds.1 h₀) (ε / 4) (by positivity)
    filter_upwards [h1, h2] with n hn1 hn2
    exact ⟨by rwa [Real.dist_eq] at hn1, by rwa [Real.dist_eq] at hn2⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun n hn ↦ ?_⟩
  obtain ⟨h1, h2⟩ := hN n hn
  have e1 := abs_sub_sub_sum_le (hs n) x₀ x hm0
  have e2 := abs_sub_sub_sum_le h x₀ x hm0
  rw [Real.dist_eq]
  have key : φs n x - φ x = (φs n x - φs n x₀ - S n) - (φ x - φ x₀ - S₀) + (S n - S₀) +
      (φs n x₀ - φ x₀) := by ring
  rw [key]
  calc |(φs n x - φs n x₀ - S n) - (φ x - φ x₀ - S₀) + (S n - S₀) + (φs n x₀ - φ x₀)|
      ≤ |φs n x - φs n x₀ - S n| + |φ x - φ x₀ - S₀| + |S n - S₀| + |φs n x₀ - φ x₀| := by
        have := abs_add_le ((φs n x - φs n x₀ - S n) - (φ x - φ x₀ - S₀) + (S n - S₀))
          (φs n x₀ - φ x₀)
        have := abs_add_le ((φs n x - φs n x₀ - S n) - (φ x - φ x₀ - S₀)) (S n - S₀)
        have := abs_sub (φs n x - φs n x₀ - S n) (φ x - φ x₀ - S₀)
        linarith
    _ < ε := by linarith

end Telescoping

section Attouch

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The envelope of a proper lsc convex function in terms of the proximal point:
`eλφ(z) = φ(Pλφ(z)) + (2λ)⁻¹|Pλφ(z) - z|²`. -/
theorem moreauEnvelopeEReal_eq_add_resolventMap {φ : E → EReal} (hp : IsProper φ)
    (hl : LowerSemicontinuous φ) (hc : Convex ℝ (epigraph φ)) {lam : ℝ} (hlam : 0 < lam)
    (z : E) :
    moreauEnvelopeEReal φ lam z = φ (resolventMap (subdifferential φ) lam z) +
      (((1 / (2 * lam)) * ‖resolventMap (subdifferential φ) lam z - z‖ ^ 2 : ℝ) : EReal) := by
  have hz : resolventMap (subdifferential φ) lam z ∈ proximalMappingEReal φ lam z := by
    rw [proximalMappingEReal_eq_singleton_of_convex hp hl hc hlam]
    exact mem_singleton _
  obtain ⟨h1, h2⟩ := moreauEnvelope_eq_of_mem_proximalMapping hp hz
  rw [h2, EReal.coe_add, ← h1]

/-- Pointwise convergence of the proximal mappings of proper lsc convex
functions is pointwise convergence of the single-valued resolvents
`(I + λ∂fν)⁻¹` (12.19). -/
theorem pointwiseConverges_proximalMappingEReal_iff {f : ℕ → E → EReal} {g : E → EReal}
    (hfp : ∀ n, IsProper (f n)) (hfl : ∀ n, LowerSemicontinuous (f n))
    (hfc : ∀ n, Convex ℝ (epigraph (f n))) (hgp : IsProper g) (hgl : LowerSemicontinuous g)
    (hgc : Convex ℝ (epigraph g)) {lam : ℝ} (hlam : 0 < lam) :
    PointwiseConverges (fun n ↦ proximalMappingEReal (f n) lam) (proximalMappingEReal g lam) ↔
      ∀ z, Tendsto (fun n ↦ resolventMap (subdifferential (f n)) lam z) atTop
        (𝓝 (resolventMap (subdifferential g) lam z)) := by
  have e : ∀ n z, proximalMappingEReal (f n) lam z =
      {resolventMap (subdifferential (f n)) lam z} := fun n z ↦
    proximalMappingEReal_eq_singleton_of_convex (hfp n) (hfl n) (hfc n) hlam z
  have e₀ : ∀ z, proximalMappingEReal g lam z = {resolventMap (subdifferential g) lam z} :=
    proximalMappingEReal_eq_singleton_of_convex hgp hgl hgc hlam
  simp only [PointwiseConverges, e, e₀]
  exact forall_congr' fun z ↦ pkConverges_singleton_iff

/-- Epi-convergence of proper lsc convex functions makes their resolvents
`(I + λ∂fν)⁻¹` converge pointwise (Exercise 7.38 and nonexpansiveness). -/
theorem tendsto_resolventMap_subdifferential_of_epiConverges {f : ℕ → E → EReal}
    {g : E → EReal} (hfp : ∀ n, IsProper (f n)) (hfl : ∀ n, LowerSemicontinuous (f n))
    (hfc : ∀ n, Convex ℝ (epigraph (f n))) (hgp : IsProper g) (hgl : LowerSemicontinuous g)
    (hgc : Convex ℝ (epigraph g)) (h : EpiConverges f g) {lam : ℝ} (hlam : 0 < lam) (z : E) :
    Tendsto (fun n ↦ resolventMap (subdifferential (f n)) lam z) atTop
      (𝓝 (resolventMap (subdifferential g) lam z)) := by
  have hthr := eventualProxThreshold_eq_top_of_convex_epiConverges h hfc hfl hfp hgp
  have hgr := graphicalConverges_proximalMappingEReal_of_convex h hfl hgp hgc
    (tendsto_const_nhds (x := lam)) hlam (by rw [hthr]; exact EReal.coe_lt_top lam)
  have hmem : resolventMap (subdifferential g) lam z ∈
      graphicalInnerLimit (fun n ↦ proximalMappingEReal (f n) lam) z := by
    apply (graphicalConverges_iff.1 hgr).2 z
    rw [proximalMappingEReal_eq_singleton_of_convex hgp hgl hgc hlam]
    exact mem_singleton _
  obtain ⟨zs, ps, hev, hzs, hps⟩ := mem_graphicalInnerLimit_iff.1 hmem
  have hps' : Tendsto (fun n ↦ resolventMap (subdifferential (f n)) lam (zs n)) atTop
      (𝓝 (resolventMap (subdifferential g) lam z)) := by
    refine hps.congr' ?_
    filter_upwards [hev] with n hn
    rw [proximalMappingEReal_eq_singleton_of_convex (hfp n) (hfl n) (hfc n) hlam,
      mem_singleton_iff] at hn
    exact hn
  exact tendsto_of_lipschitzWith_one (fun n ↦
    (svMaximalMonotone_subdifferential_of_convex (hfp n) (hfl n) (hfc n)).lipschitzWith_resolventMap
      hlam) tendsto_const_nhds hzs hps'

/-- Graph points `(x̄ν, v̄ν) → (x̄, v̄)` with `fν(x̄ν) → f(x̄)` give centers
`x̃ν = x̄ν + λv̄ν → x̃ = x̄ + λv̄` with `eλfν(x̃ν) → eλf(x̃)`. -/
theorem tendsto_moreauEnvelopeEReal_add_smul {f : ℕ → E → EReal} {g : E → EReal}
    (hfp : ∀ n, IsProper (f n)) (hfl : ∀ n, LowerSemicontinuous (f n))
    (hfc : ∀ n, Convex ℝ (epigraph (f n))) (hgp : IsProper g) (hgl : LowerSemicontinuous g)
    (hgc : Convex ℝ (epigraph g)) {lam : ℝ} (hlam : 0 < lam) {xs vs : ℕ → E} {x v : E}
    (hvs : ∀ n, vs n ∈ subdifferential (f n) (xs n)) (hv : v ∈ subdifferential g x)
    (hxs : Tendsto xs atTop (𝓝 x)) (hvsl : Tendsto vs atTop (𝓝 v))
    (hval : Tendsto (fun n ↦ f n (xs n)) atTop (𝓝 (g x))) :
    Tendsto (fun n ↦ moreauEnvelopeEReal (f n) lam (xs n + lam • vs n)) atTop
      (𝓝 (moreauEnvelopeEReal g lam (x + lam • v))) := by
  have hres : ∀ n, resolventMap (subdifferential (f n)) lam (xs n + lam • vs n) = xs n :=
    fun n ↦ (svMaximalMonotone_subdifferential_of_convex (hfp n) (hfl n)
      (hfc n)).resolventMap_add_smul hlam (hvs n)
  have hres₀ : resolventMap (subdifferential g) lam (x + lam • v) = x :=
    (svMaximalMonotone_subdifferential_of_convex hgp hgl hgc).resolventMap_add_smul hlam hv
  simp only [moreauEnvelopeEReal_eq_add_resolventMap (hfp _) (hfl _) (hfc _) hlam, hres,
    moreauEnvelopeEReal_eq_add_resolventMap hgp hgl hgc hlam, hres₀]
  refine tendsto_ereal_add_coe hval ?_
  exact tendsto_const_nhds.mul ((hxs.sub (hxs.add (hvsl.const_smul lam))).norm.pow 2)

/-- Centers `x̃ν → x̃` with `eλfν(x̃ν) → eλf(x̃)`, together with pointwise
convergence of the resolvents, give graph points `(Pλfν(x̃ν), λ⁻¹(x̃ν - Pλfν(x̃ν)))`
converging to `(Pλf(x̃), λ⁻¹(x̃ - Pλf(x̃)))` with convergent function values. -/
theorem tendsto_apply_resolventMap_of_tendsto_moreauEnvelopeEReal {f : ℕ → E → EReal}
    {g : E → EReal} (hfp : ∀ n, IsProper (f n)) (hfl : ∀ n, LowerSemicontinuous (f n))
    (hfc : ∀ n, Convex ℝ (epigraph (f n))) (hgp : IsProper g) (hgl : LowerSemicontinuous g)
    (hgc : Convex ℝ (epigraph g)) {lam : ℝ} (hlam : 0 < lam)
    (hP : ∀ z, Tendsto (fun n ↦ resolventMap (subdifferential (f n)) lam z) atTop
      (𝓝 (resolventMap (subdifferential g) lam z)))
    {zs : ℕ → E} {z : E} (hzs : Tendsto zs atTop (𝓝 z))
    (he : Tendsto (fun n ↦ moreauEnvelopeEReal (f n) lam (zs n)) atTop
      (𝓝 (moreauEnvelopeEReal g lam z))) :
    Tendsto (fun n ↦ resolventMap (subdifferential (f n)) lam (zs n)) atTop
        (𝓝 (resolventMap (subdifferential g) lam z)) ∧
      Tendsto (fun n ↦ f n (resolventMap (subdifferential (f n)) lam (zs n))) atTop
        (𝓝 (g (resolventMap (subdifferential g) lam z))) := by
  set P : ℕ → E → E := fun n ↦ resolventMap (subdifferential (f n)) lam with hPdef
  set P₀ := resolventMap (subdifferential g) lam with hP₀def
  have hxs : Tendsto (fun n ↦ P n (zs n)) atTop (𝓝 (P₀ z)) :=
    tendsto_of_lipschitzWith_one (fun n ↦
      (svMaximalMonotone_subdifferential_of_convex (hfp n) (hfl n)
        (hfc n)).lipschitzWith_resolventMap hlam) hzs tendsto_const_nhds (hP z)
  refine ⟨hxs, ?_⟩
  have hmem : ∀ n, P n (zs n) ∈ proximalMappingEReal (f n) lam (zs n) := fun n ↦ by
    rw [proximalMappingEReal_eq_singleton_of_convex (hfp n) (hfl n) (hfc n) hlam]
    exact mem_singleton _
  have hmem₀ : P₀ z ∈ proximalMappingEReal g lam z := by
    rw [proximalMappingEReal_eq_singleton_of_convex hgp hgl hgc hlam]
    exact mem_singleton _
  have hfin : ∀ n, f n (P n (zs n)) = ((f n (P n (zs n))).toReal : EReal) := fun n ↦
    (moreauEnvelope_eq_of_mem_proximalMapping (hfp n) (hmem n)).1
  obtain ⟨hfin₀, he₀⟩ := moreauEnvelope_eq_of_mem_proximalMapping hgp hmem₀
  have hen : ∀ n, moreauEnvelopeEReal (f n) lam (zs n) =
      (((f n (P n (zs n))).toReal + (1 / (2 * lam)) * ‖P n (zs n) - zs n‖ ^ 2 : ℝ) : EReal) :=
    fun n ↦ (moreauEnvelope_eq_of_mem_proximalMapping (hfp n) (hmem n)).2
  simp only [hen, he₀] at he
  have hreal := EReal.tendsto_coe.1 he
  have hq : Tendsto (fun n ↦ (1 / (2 * lam)) * ‖P n (zs n) - zs n‖ ^ 2) atTop
      (𝓝 ((1 / (2 * lam)) * ‖P₀ z - z‖ ^ 2)) :=
    tendsto_const_nhds.mul ((hxs.sub hzs).norm.pow 2)
  have hr := hreal.sub hq
  simp only [add_sub_cancel_right] at hr
  rw [hfin₀]
  exact (EReal.tendsto_coe.2 hr).congr fun n ↦ (hfin n).symm

/-- **Theorem 12.35**, (c) ⇒ (a): pointwise convergence of the proximal mappings
and convergence of the envelopes along one convergent sequence of centers give
epi-convergence. -/
theorem epiConverges_of_tendsto_resolventMap_of_tendsto_moreauEnvelopeEReal
    {f : ℕ → E → EReal} {g : E → EReal} (hfp : ∀ n, IsProper (f n))
    (hfl : ∀ n, LowerSemicontinuous (f n)) (hfc : ∀ n, Convex ℝ (epigraph (f n)))
    (hgp : IsProper g) (hgl : LowerSemicontinuous g) (hgc : Convex ℝ (epigraph g)) {lam : ℝ}
    (hlam : 0 < lam)
    (hP : ∀ z, Tendsto (fun n ↦ resolventMap (subdifferential (f n)) lam z) atTop
      (𝓝 (resolventMap (subdifferential g) lam z)))
    {zs : ℕ → E} {z : E} (hzs : Tendsto zs atTop (𝓝 z))
    (he : Tendsto (fun n ↦ moreauEnvelopeEReal (f n) lam (zs n)) atTop
      (𝓝 (moreauEnvelopeEReal g lam z))) :
    EpiConverges f g := by
  set γs : ℕ → E → E := fun n x ↦ lam⁻¹ • (x - resolventMap (subdifferential (f n)) lam x)
    with hγs
  set γ : E → E := fun x ↦ lam⁻¹ • (x - resolventMap (subdifferential g) lam x) with hγ
  have hs : ∀ n x y, |moreauEnvelopeReal (f n) lam y - moreauEnvelopeReal (f n) lam x -
      ⟪γs n x, y - x⟫_ℝ| ≤ 1 / (2 * lam) * ‖y - x‖ ^ 2 := fun n x y ↦
    abs_moreauEnvelopeReal_sub_le (hfp n) (hfl n) (hfc n) hlam x y
  have h₀ : ∀ x y, |moreauEnvelopeReal g lam y - moreauEnvelopeReal g lam x -
      ⟪γ x, y - x⟫_ℝ| ≤ 1 / (2 * lam) * ‖y - x‖ ^ 2 := fun x y ↦
    abs_moreauEnvelopeReal_sub_le hgp hgl hgc hlam x y
  have hγlim : ∀ x, Tendsto (fun n ↦ γs n x) atTop (𝓝 (γ x)) := fun x ↦
    ((tendsto_const_nhds (x := x)).sub (hP x)).const_smul lam⁻¹
  have hcoe : ∀ n x, moreauEnvelopeEReal (f n) lam x = (moreauEnvelopeReal (f n) lam x : EReal) :=
    fun n x ↦ (moreauEnvelopeReal_eq_of_convex (hfp n) (hfl n) (hfc n) hlam x).1
  have hcoe₀ : ∀ x, moreauEnvelopeEReal g lam x = (moreauEnvelopeReal g lam x : EReal) :=
    fun x ↦ (moreauEnvelopeReal_eq_of_convex hgp hgl hgc hlam x).1
  -- convergence at the moving centers, as real numbers
  have hzr : Tendsto (fun n ↦ moreauEnvelopeReal (f n) lam (zs n)) atTop
      (𝓝 (moreauEnvelopeReal g lam z)) := by
    simp only [hcoe, hcoe₀] at he
    exact EReal.tendsto_coe.1 he
  -- the gradients at the moving centers converge
  have hγz : Tendsto (fun n ↦ γs n (zs n)) atTop (𝓝 (γ z)) := by
    have hPz : Tendsto (fun n ↦ resolventMap (subdifferential (f n)) lam (zs n)) atTop
        (𝓝 (resolventMap (subdifferential g) lam z)) :=
      tendsto_of_lipschitzWith_one (fun n ↦
        (svMaximalMonotone_subdifferential_of_convex (hfp n) (hfl n)
          (hfc n)).lipschitzWith_resolventMap hlam) hzs tendsto_const_nhds (hP z)
    exact (hzs.sub hPz).const_smul lam⁻¹
  -- convergence at the fixed point `z`
  have hz : Tendsto (fun n ↦ moreauEnvelopeReal (f n) lam z) atTop
      (𝓝 (moreauEnvelopeReal g lam z)) := by
    have hd : Tendsto (fun n ↦ moreauEnvelopeReal (f n) lam z -
        moreauEnvelopeReal (f n) lam (zs n)) atTop (𝓝 0) := by
      have hb : Tendsto (fun n ↦ ‖γs n (zs n)‖ * ‖z - zs n‖ + 1 / (2 * lam) * ‖z - zs n‖ ^ 2)
          atTop (𝓝 (‖γ z‖ * ‖z - z‖ + 1 / (2 * lam) * ‖z - z‖ ^ 2)) :=
        (hγz.norm.mul (tendsto_const_nhds.sub hzs).norm).add
          (tendsto_const_nhds.mul ((tendsto_const_nhds.sub hzs).norm.pow 2))
      rw [sub_self, norm_zero, mul_zero, zero_add, zero_pow two_ne_zero, mul_zero] at hb
      refine squeeze_zero_norm (fun n ↦ ?_) hb
      have h1 := hs n (zs n) z
      have h2 := abs_real_inner_le_norm (γs n (zs n)) (z - zs n)
      rw [Real.norm_eq_abs]
      have h3 := abs_sub_abs_le_abs_sub
        (moreauEnvelopeReal (f n) lam z - moreauEnvelopeReal (f n) lam (zs n))
        ⟪γs n (zs n), z - zs n⟫_ℝ
      linarith
    have := hd.add hzr
    simpa only [sub_add_cancel, zero_add] using this
  have hall : ∀ x, Tendsto (fun n ↦ moreauEnvelopeReal (f n) lam x) atTop
      (𝓝 (moreauEnvelopeReal g lam x)) :=
    tendsto_of_quadratic_estimate hs h₀ hγlim hz
  refine (convex_epiConverges_iff_tendsto_one_moreauEnvelope hfc hfl hfp hgc hgl hgp).2
    ⟨lam, hlam, fun x ↦ ?_⟩
  simp only [hcoe, hcoe₀]
  exact EReal.tendsto_coe.2 (hall x)

/-- **Theorem 12.35 (subgradient convergence for convex functions; Attouch).**
For proper lsc convex `fν` and `f` and any `λ > 0`, the following are
equivalent:
(a) `fν →e f`;
(b) `∂fν →g ∂f`, and `fν(x̄ν) → f(x̄)` for some `v̄ν ∈ ∂fν(x̄ν)` and `v̄ ∈ ∂f(x̄)` with
`(x̄ν, v̄ν) → (x̄, v̄)`;
(c) `Pλfν →p Pλf`, and `eλfν(x̃ν) → eλf(x̃)` for some `x̃` and some `x̃ν → x̃`. -/
theorem subgradient_convergence_tfae {f : ℕ → E → EReal} {g : E → EReal}
    (hfp : ∀ n, IsProper (f n)) (hfl : ∀ n, LowerSemicontinuous (f n))
    (hfc : ∀ n, Convex ℝ (epigraph (f n))) (hgp : IsProper g) (hgl : LowerSemicontinuous g)
    (hgc : Convex ℝ (epigraph g)) {lam : ℝ} (hlam : 0 < lam) :
    List.TFAE [EpiConverges f g,
      GraphicalConverges (fun n ↦ subdifferential (f n)) (subdifferential g) ∧
        ∃ (xs vs : ℕ → E) (x v : E), (∀ n, vs n ∈ subdifferential (f n) (xs n)) ∧
          v ∈ subdifferential g x ∧ Tendsto xs atTop (𝓝 x) ∧ Tendsto vs atTop (𝓝 v) ∧
          Tendsto (fun n ↦ f n (xs n)) atTop (𝓝 (g x)),
      PointwiseConverges (fun n ↦ proximalMappingEReal (f n) lam) (proximalMappingEReal g lam) ∧
        ∃ (zs : ℕ → E) (z : E), Tendsto zs atTop (𝓝 z) ∧
          Tendsto (fun n ↦ moreauEnvelopeEReal (f n) lam (zs n)) atTop
            (𝓝 (moreauEnvelopeEReal g lam z))] := by
  have hT : ∀ n, SvMaximalMonotone (subdifferential (f n)) := fun n ↦
    svMaximalMonotone_subdifferential_of_convex (hfp n) (hfl n) (hfc n)
  have hT₀ : SvMaximalMonotone (subdifferential g) :=
    svMaximalMonotone_subdifferential_of_convex hgp hgl hgc
  have hpw := pointwiseConverges_proximalMappingEReal_iff hfp hfl hfc hgp hgl hgc hlam
  tfae_have 1 → 3 := fun h ↦ by
    have hthr := eventualProxThreshold_eq_top_of_convex_epiConverges h hfc hfl hfp hgp
    refine ⟨hpw.2 fun z ↦ tendsto_resolventMap_subdifferential_of_epiConverges hfp hfl hfc
      hgp hgl hgc h hlam z, fun _ ↦ 0, 0, tendsto_const_nhds, ?_⟩
    exact (tendsto_moreauEnvelopeEReal_of_epiConverges h hfl hgp tendsto_const_nhds
      tendsto_const_nhds hlam (by rw [hthr]; exact EReal.coe_lt_top lam)).2
  tfae_have 3 → 2 := fun ⟨hp, zs, z, hzs, he⟩ ↦ by
    have hP := hpw.1 hp
    refine ⟨graphicalConverges_of_tendsto_resolventMap hT hT₀ hlam hP, ?_⟩
    obtain ⟨hx, hval⟩ := tendsto_apply_resolventMap_of_tendsto_moreauEnvelopeEReal hfp hfl hfc
      hgp hgl hgc hlam hP hzs he
    exact ⟨fun n ↦ resolventMap (subdifferential (f n)) lam (zs n),
      fun n ↦ lam⁻¹ • (zs n - resolventMap (subdifferential (f n)) lam (zs n)),
      resolventMap (subdifferential g) lam z,
      lam⁻¹ • (z - resolventMap (subdifferential g) lam z),
      fun n ↦ (hT n).inv_smul_sub_resolventMap_mem hlam (zs n),
      hT₀.inv_smul_sub_resolventMap_mem hlam z, hx, (hzs.sub hx).const_smul lam⁻¹, hval⟩
  tfae_have 2 → 3 := fun ⟨hg, xs, vs, x, v, hvs, hv, hxs, hvsl, hval⟩ ↦
    ⟨hpw.2 ((graphicalConverges_iff_tendsto_resolventMap hT hT₀ hlam).1 hg),
      fun n ↦ xs n + lam • vs n, x + lam • v, hxs.add (hvsl.const_smul lam),
      tendsto_moreauEnvelopeEReal_add_smul hfp hfl hfc hgp hgl hgc hlam hvs hv hxs hvsl hval⟩
  tfae_have 3 → 1 := fun ⟨hp, zs, z, hzs, he⟩ ↦
    epiConverges_of_tendsto_resolventMap_of_tendsto_moreauEnvelopeEReal hfp hfl hfc hgp hgl hgc
      hlam (hpw.1 hp) hzs he
  tfae_finish

/-- **Theorem 12.35**, (a) ⇒ (b), graphical part: epi-convergence of proper lsc
convex functions gives graphical convergence of their subgradient mappings. -/
theorem EpiConverges.graphicalConverges_subdifferential {f : ℕ → E → EReal} {g : E → EReal}
    (h : EpiConverges f g) (hfp : ∀ n, IsProper (f n)) (hfl : ∀ n, LowerSemicontinuous (f n))
    (hfc : ∀ n, Convex ℝ (epigraph (f n))) (hgp : IsProper g) (hgl : LowerSemicontinuous g)
    (hgc : Convex ℝ (epigraph g)) :
    GraphicalConverges (fun n ↦ subdifferential (f n)) (subdifferential g) :=
  (graphicalConverges_iff_tendsto_resolventMap
    (fun n ↦ svMaximalMonotone_subdifferential_of_convex (hfp n) (hfl n) (hfc n))
    (svMaximalMonotone_subdifferential_of_convex hgp hgl hgc) one_pos).2 fun z ↦
      tendsto_resolventMap_subdifferential_of_epiConverges hfp hfl hfc hgp hgl hgc h one_pos z

/-- **Theorem 12.35**, the final assertion: when `fν →e f` for proper lsc convex
functions and `λν → λ` with `λ, λν > 0`, the single-valued proximal mappings
`Pλν fν` converge to `Pλ f` uniformly on bounded sets, and so do the envelopes
`eλν fν` to `eλ f`. -/
theorem EpiConverges.tendstoUniformlyOn_proximal_envelope {f : ℕ → E → EReal}
    {g : E → EReal} (h : EpiConverges f g) (hfp : ∀ n, IsProper (f n))
    (hfl : ∀ n, LowerSemicontinuous (f n)) (hfc : ∀ n, Convex ℝ (epigraph (f n)))
    (hgp : IsProper g) (hgl : LowerSemicontinuous g) (hgc : Convex ℝ (epigraph g))
    {lams : ℕ → ℝ} {lam : ℝ} (hpos : ∀ n, 0 < lams n) (hlam : 0 < lam)
    (hlim : Tendsto lams atTop (𝓝 lam)) {B : Set E} (hB : IsBounded B) :
    (∀ n z, proximalMappingEReal (f n) (lams n) z =
      {resolventMap (subdifferential (f n)) (lams n) z}) ∧
    (∀ z, proximalMappingEReal g lam z = {resolventMap (subdifferential g) lam z}) ∧
    TendstoUniformlyOn (fun n ↦ resolventMap (subdifferential (f n)) (lams n))
      (resolventMap (subdifferential g) lam) atTop B ∧
    TendstoUniformlyOn (fun n ↦ moreauEnvelopeReal (f n) (lams n))
      (moreauEnvelopeReal g lam) atTop B := by
  have hT : ∀ n, SvMaximalMonotone (subdifferential (f n)) := fun n ↦
    svMaximalMonotone_subdifferential_of_convex (hfp n) (hfl n) (hfc n)
  have hT₀ : SvMaximalMonotone (subdifferential g) :=
    svMaximalMonotone_subdifferential_of_convex hgp hgl hgc
  have hgr : GraphicalConverges (fun n ↦ subdifferential (f n)) (subdifferential g) :=
    h.graphicalConverges_subdifferential hfp hfl hfc hgp hgl hgc
  have hthr := eventualProxThreshold_eq_top_of_convex_epiConverges h hfc hfl hfp hgp
  refine ⟨fun n z ↦ proximalMappingEReal_eq_singleton_of_convex (hfp n) (hfl n) (hfc n)
      (hpos n) z, proximalMappingEReal_eq_singleton_of_convex hgp hgl hgc hlam,
    hgr.tendstoUniformlyOn_resolventMap hT hT₀ hpos hlam hlim hB, ?_⟩
  exact (moreauEnvelope_tendstoUniformlyOn_of_bounded h hfl hgp hlim hlam
    (by rw [hthr]; exact EReal.coe_lt_top lam) hB).2

end Attouch

section UniformBoundedness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Exercise 12.40(a)**, the uniform bound: if `Tν →g T` with `Tν` maximal
monotone and `x̄ ∈ int(dom T)`, there are a neighborhood `V` of `x̄` and a bounded
set `B` with `T(V) ⊂ B` and `Tν(V) ⊂ B` for all large `ν`. -/
theorem exists_eventually_svImage_subset_of_graphicalConverges {T : ℕ → E → Set E}
    {T₀ : E → Set E} (hT : ∀ n, SvMaximalMonotone (T n)) (h : GraphicalConverges T T₀)
    {xbar : E} (hx : xbar ∈ interior (svDom T₀)) :
    ∃ V ∈ 𝓝 xbar, ∃ B : Set E, IsBounded B ∧ svImage T₀ V ⊆ B ∧
      ∀ᶠ n in atTop, svImage (T n) V ⊆ B := by
  have hdom : xbar ∈ svDom T₀ := interior_subset hx
  have hT₀ : SvMaximalMonotone T₀ := h.svMaximalMonotone hT ⟨xbar, hdom⟩
  have hlb : SvLocallyBoundedAt T₀ xbar := by
    rw [hT₀.svLocallyBoundedAt_iff_notMem_frontier]
    intro hfr
    exact hfr.2 (interior_mono subset_closure hx)
  obtain ⟨V₀, hV₀, hbdd₀⟩ := hlb
  obtain ⟨R, hR⟩ := hbdd₀.subset_closedBall (0 : E)
  have hkey : ∃ k : ℕ, ∀ᶠ n in atTop,
      svImage (T n) (ball xbar (1 / ((k : ℝ) + 1))) ⊆ closedBall (0 : E) k := by
    by_contra hcon
    push_neg at hcon
    have hP : ∀ k : ℕ, ∃ᶠ n in atTop,
        ∃ y ∈ ball xbar (1 / ((k : ℝ) + 1)), ∃ w ∈ T n y, (k : ℝ) < ‖w‖ := by
      intro k
      refine (hcon k).mono fun n hn ↦ ?_
      obtain ⟨w, hw, hwk⟩ := not_subset.1 hn
      obtain ⟨y, hy, hwy⟩ := mem_svImage.1 hw
      exact ⟨y, hy, w, hwy, by simpa [mem_closedBall_zero_iff, not_le] using hwk⟩
    obtain ⟨φ, hφ, hφP⟩ := extraction_forall_of_frequently hP
    choose y hy w hw hwk using hφP
    have hyl : Tendsto y atTop (𝓝 xbar) := by
      rw [tendsto_iff_dist_tendsto_zero]
      exact squeeze_zero (fun _ ↦ dist_nonneg) (fun k ↦ (mem_ball.1 (hy k)).le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    have hwl : Tendsto (fun k ↦ ‖w k‖) atTop atTop :=
      tendsto_atTop_mono (fun k ↦ (hwk k).le) tendsto_natCast_atTop_atTop
    obtain ⟨ψ, u, hψ, hu1, hu⟩ := exists_subseq_tendsto_normalize hwl
    have hdomu : ∀ a ∈ svDom T₀, ⟪u, a - xbar⟫_ℝ ≤ 0 := by
      rintro a ⟨b, hb⟩
      obtain ⟨as, bs, hev, has, hbs⟩ :=
        mem_graphicalInnerLimit_iff.1 ((graphicalConverges_iff.1 h).2 a hb)
      have hev' : ∀ᶠ k in atTop, bs (φ (ψ k)) ∈ T (φ (ψ k)) (as (φ (ψ k))) :=
        (hφ.comp hψ).tendsto_atTop.eventually hev
      exact inner_nonpos_of_inner_sub_nonneg (x := fun k ↦ y (ψ k)) (v := fun k ↦ w (ψ k))
        (a := fun k ↦ as (φ (ψ k))) (b := fun k ↦ bs (φ (ψ k)))
        (hev'.mono fun k hk ↦ (hT (φ (ψ k))).1 hk (hw (ψ k)))
        (hyl.comp hψ.tendsto_atTop) (has.comp (hφ.comp hψ).tendsto_atTop)
        (hbs.comp (hφ.comp hψ).tendsto_atTop) (hwl.comp hψ.tendsto_atTop) hu
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 isOpen_interior xbar hx
    have hmem : xbar + (δ / 2) • u ∈ svDom T₀ := by
      apply interior_subset
      apply hball
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hu1, mul_one,
        Real.norm_of_nonneg (by positivity)]
      linarith
    have h1 := hdomu _ hmem
    rw [add_sub_cancel_left, real_inner_smul_right, real_inner_self_eq_norm_sq, hu1] at h1
    nlinarith
  obtain ⟨k, hk⟩ := hkey
  refine ⟨ball xbar (1 / ((k : ℝ) + 1)) ∩ V₀, inter_mem (ball_mem_nhds _ (by positivity)) hV₀,
    closedBall 0 (max k R), isBounded_closedBall, ?_, ?_⟩
  · exact (svImage_mono inter_subset_right).trans
      (hR.trans (closedBall_subset_closedBall (le_max_right _ _)))
  · filter_upwards [hk] with n hn
    exact (svImage_mono inter_subset_left).trans
      (hn.trans (closedBall_subset_closedBall (le_max_left _ _)))

/-- **Exercise 12.40(a)**, single-valued limits: if moreover `T(x̄) = {v̄}`, then
`Tν(xν) → {v̄}` whenever `xν → x̄`. -/
theorem pkConverges_apply_of_graphicalConverges {T : ℕ → E → Set E} {T₀ : E → Set E}
    (hT : ∀ n, SvMaximalMonotone (T n)) (h : GraphicalConverges T T₀) {xbar vbar : E}
    (hx : xbar ∈ interior (svDom T₀)) (hsingle : T₀ xbar = {vbar}) {x : ℕ → E}
    (hxl : Tendsto x atTop (𝓝 xbar)) : PKConverges (fun n ↦ T n (x n)) {vbar} := by
  obtain ⟨V, hV, B, hB, -, hTV⟩ := exists_eventually_svImage_subset_of_graphicalConverges hT h hx
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.1 hV
  have hvbar : vbar ∈ T₀ xbar := by
    rw [hsingle]
    exact mem_singleton _
  obtain ⟨as, bs, hev, has, -⟩ :=
    mem_graphicalInnerLimit_iff.1 ((graphicalConverges_iff.1 h).2 xbar hvbar)
  -- for large `ν` the ball `IB(x̄, r)` lies in `dom Tν`
  have hball : ∀ᶠ n in atTop, ball xbar r ⊆ svDom (T n) := by
    filter_upwards [hTV, hev, has (ball_mem_nhds xbar hr)] with n hn hbn han
    have hlb : ∀ y ∈ ball xbar r, SvLocallyBoundedAt (T n) y := fun y hy ↦
      ⟨ball xbar r, isOpen_ball.mem_nhds hy, hB.subset ((svImage_mono hrV).trans hn)⟩
    have hfr : ∀ y ∈ ball xbar r, y ∉ frontier (closure (svDom (T n))) := fun y hy ↦
      (hT n).svLocallyBoundedAt_iff_notMem_frontier.1 (hlb y hy)
    have hsub : ball xbar r ⊆ interior (closure (svDom (T n))) ∪ (closure (svDom (T n)))ᶜ := by
      intro y hy
      by_cases hyD : y ∈ closure (svDom (T n))
      · left
        by_contra hint
        exact hfr y hy ⟨subset_closure hyD, hint⟩
      · exact Or.inr hyD
    have hinter : (ball xbar r ∩ interior (closure (svDom (T n)))).Nonempty := by
      refine ⟨as n, han, ?_⟩
      by_contra hint
      exact hfr (as n) han ⟨subset_closure (subset_closure ⟨_, hbn⟩), hint⟩
    have hsub' := (convex_ball xbar r).isPreconnected.subset_left_of_subset_union
      isOpen_interior isClosed_closure.isOpen_compl
      (disjoint_compl_right.mono_left interior_subset) hsub hinter
    intro y hy
    exact mem_svDom_of_mem_closure (hT n).isClosed_svGraph (interior_subset (hsub' hy)) (hlb y hy)
  have hout : outerSetLimit (fun n ↦ T n (x n)) ⊆ {vbar} := by
    intro v hv
    obtain ⟨φ, ws, hφ, hws, hwl⟩ := mem_outerSetLimit_iff_exists_subsequence.1 hv
    have hmem : v ∈ graphicalOuterLimit T xbar :=
      mem_graphicalOuterLimit_iff.2 ⟨φ, x ∘ φ, ws, hφ, hws, hxl.comp hφ.tendsto_atTop, hwl⟩
    rw [← hsingle]
    exact (graphicalConverges_iff.1 h).1 xbar hmem
  have hin : vbar ∈ innerSetLimit (fun n ↦ T n (x n)) := by
    intro U hU
    by_contra hcon
    rw [not_eventually] at hcon
    have hev2 : ∀ᶠ n in atTop, x n ∈ svDom (T n) ∧ T n (x n) ⊆ B := by
      filter_upwards [hball, hTV, hxl (ball_mem_nhds xbar hr)] with n h1 h2 h3
      exact ⟨h1 h3, fun w hw ↦ h2 (mem_svImage.2 ⟨x n, hrV h3, hw⟩)⟩
    have hfreq : ∃ᶠ n in atTop, ∃ w ∈ T n (x n), w ∉ U ∧ w ∈ B :=
      (hcon.and_eventually hev2).mono fun n ⟨hn1, ⟨w, hw⟩, hn3⟩ ↦
        ⟨w, hw, fun hwU ↦ hn1 ⟨w, hw, hwU⟩, hn3 hw⟩
    obtain ⟨φ, hφ, hφP⟩ := extraction_of_frequently_atTop hfreq
    choose w hw hwU hwB using hφP
    obtain ⟨wbar, -, ψ, hψ, hwl⟩ := tendsto_subseq_of_bounded hB hwB
    have hwbar : wbar ∈ outerSetLimit (fun n ↦ T n (x n)) :=
      mem_outerSetLimit_iff_exists_subsequence.2
        ⟨φ ∘ ψ, w ∘ ψ, hφ.comp hψ, fun k ↦ hw (ψ k), hwl⟩
    have heq : wbar = vbar := hout hwbar
    rw [heq] at hwl
    obtain ⟨k, hk⟩ := (hwl.eventually hU).exists
    exact hwU (ψ k) hk
  have hio := innerSetLimit_subset_outerSetLimit (fun n ↦ T n (x n))
  exact ⟨Subset.antisymm (hio.trans hout) (singleton_subset_iff.2 hin),
    Subset.antisymm hout (singleton_subset_iff.2 (hio hin))⟩

/-- **Exercise 12.40(a) (uniform local boundedness in convergence)**, collected. -/
theorem uniform_local_boundedness_in_convergence {T : ℕ → E → Set E} {T₀ : E → Set E}
    (hT : ∀ n, SvMaximalMonotone (T n)) (h : GraphicalConverges T T₀) {xbar : E}
    (hx : xbar ∈ interior (svDom T₀)) :
    (∃ V ∈ 𝓝 xbar, ∃ B : Set E, IsBounded B ∧ svImage T₀ V ⊆ B ∧
      ∀ᶠ n in atTop, svImage (T n) V ⊆ B) ∧
    ∀ vbar, T₀ xbar = {vbar} → ∀ x : ℕ → E, Tendsto x atTop (𝓝 xbar) →
      PKConverges (fun n ↦ T n (x n)) {vbar} :=
  ⟨exists_eventually_svImage_subset_of_graphicalConverges hT h hx,
    fun _ hs _ hxl ↦ pkConverges_apply_of_graphicalConverges hT h hx hs hxl⟩

omit [FiniteDimensional ℝ E] in
/-- A lower semicontinuous convex function with a finite value is proper: a
value `-∞` would spread along segments and contradict lower semicontinuity at
the finite point. -/
theorem isProper_of_convex_of_eq_coe {φ : E → EReal} (hc : Convex ℝ (epigraph φ))
    (hl : LowerSemicontinuous φ) {x₀ : E} {c : ℝ} (hx₀ : φ x₀ = c) : IsProper φ := by
  refine ⟨⟨x₀, by rw [hx₀]; exact EReal.coe_lt_top c⟩, fun y ↦ ?_⟩
  by_contra hy
  rw [not_lt, le_bot_iff] at hy
  have hz : ∀ t : ℝ, 0 < t → t ≤ 1 → φ (x₀ + t • (y - x₀)) = ⊥ := by
    intro t ht0 ht1
    refine (EReal.eq_bot_iff_forall_lt _).2 fun a ↦ ?_
    set r : ℝ := (a - (1 - t) * c) / t - 1 with hr
    have hx₀e : ((x₀, c) : E × ℝ) ∈ epigraph φ := by
      change ((c : ℝ) : EReal) ≥ φ x₀
      rw [hx₀]
    have hye : ((y, r) : E × ℝ) ∈ epigraph φ := by
      change ((r : ℝ) : EReal) ≥ φ y
      rw [hy]
      exact bot_le
    have hmem := hc hx₀e hye (sub_nonneg.2 ht1) ht0.le (by ring)
    have e : (1 - t) • ((x₀, c) : E × ℝ) + t • (y, r) =
        (x₀ + t • (y - x₀), (1 - t) * c + t * r) := by
      ext
      · simp only [Prod.fst_add, Prod.smul_fst]
        module
      · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    rw [e] at hmem
    have hlt : (1 - t) * c + t * r < a := by
      rw [hr, mul_sub, mul_div_cancel₀ _ ht0.ne']
      linarith
    exact lt_of_le_of_lt hmem (EReal.coe_lt_coe_iff.2 hlt)
  have hlt : (((c - 1 : ℝ)) : EReal) < φ x₀ := by
    rw [hx₀]
    exact EReal.coe_lt_coe_iff.2 (by linarith)
  have hev : ∀ᶠ z in 𝓝 x₀, (((c - 1 : ℝ)) : EReal) < φ z := hl x₀ _ hlt
  have hpath : Tendsto (fun t : ℝ ↦ x₀ + t • (y - x₀)) (𝓝[>] 0) (𝓝 x₀) := by
    have h1 : Tendsto (fun t : ℝ ↦ x₀ + t • (y - x₀)) (𝓝 0) (𝓝 (x₀ + (0 : ℝ) • (y - x₀))) :=
      (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
    rw [zero_smul, add_zero] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have h1 : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 := nhdsWithin_le_nhds (Iio_mem_nhds (zero_lt_one' ℝ))
  obtain ⟨t, ht, ht1, ht0⟩ :=
    ((hpath.eventually hev).and (h1.and eventually_mem_nhdsWithin)).exists
  rw [hz t ht0 ht1.le] at ht
  exact not_lt_bot ht

/-- For a proper convex function differentiable at an interior point of its
domain (formula 7(16)), the subdifferential there is the gradient. -/
theorem subdifferential_eq_singleton_of_hasERealGradientAt {g : E → EReal}
    (hgc : Convex ℝ (epigraph g)) (hgp : IsProper g) {xbar : E}
    (hx : xbar ∈ interior (effectiveDomain g)) {L : E →L[ℝ] ℝ}
    (hd : HasERealGradientAt g xbar L) :
    subdifferential g xbar = {(InnerProductSpace.toDual ℝ E).symm L} := by
  obtain ⟨hbot, htop, hfin, ho⟩ := hd
  have hderiv : HasFDerivAt (fun y ↦ (g y).toReal) L xbar := HasFDerivAtFilter.of_isLittleO ho
  have hne := subdifferential_nonempty_of_convex_interior hgc hgp hx
  refine eq_singleton_iff_nonempty_unique_mem.2 ⟨hne, fun v hv ↦ ?_⟩
  have hc : g xbar = ((g xbar).toReal : EReal) := (EReal.coe_toReal htop hbot).symm
  have hsub := forall_le_of_mem_subdifferential_of_convex hgc hc hv
  have hL : ∀ w, ⟪v, w⟫_ℝ = L w := by
    intro w
    have hline : HasDerivAt (fun t : ℝ ↦ xbar + t • w) w 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add xbar
    have h2 : HasDerivAt (fun t : ℝ ↦ (g (xbar + t • w)).toReal) (L w) 0 :=
      hderiv.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hline (by simp)
    have hG : HasDerivAt (fun t : ℝ ↦ (g (xbar + t • w)).toReal - t * ⟪v, w⟫_ℝ)
        (L w - ⟪v, w⟫_ℝ) 0 := by
      simpa using h2.sub ((hasDerivAt_id (0 : ℝ)).mul_const ⟪v, w⟫_ℝ)
    have hmin : IsLocalMin (fun t : ℝ ↦ (g (xbar + t • w)).toReal - t * ⟪v, w⟫_ℝ) 0 := by
      have hpath : Tendsto (fun t : ℝ ↦ xbar + t • w) (𝓝 0) (𝓝 xbar) := by
        have h1 : Tendsto (fun t : ℝ ↦ xbar + t • w) (𝓝 0) (𝓝 (xbar + (0 : ℝ) • w)) :=
          (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
        rwa [zero_smul, add_zero] at h1
      filter_upwards [hpath.eventually hfin] with t ht
      have h3 := hsub (xbar + t • w)
      rw [add_sub_cancel_left, real_inner_smul_right] at h3
      have hgt : g (xbar + t • w) = ((g (xbar + t • w)).toReal : EReal) :=
        (EReal.coe_toReal ht.2 ht.1).symm
      rw [hgt, EReal.coe_le_coe_iff] at h3
      simp only [zero_smul, add_zero, zero_mul, sub_zero]
      linarith
    have := hmin.hasDerivAt_eq_zero hG
    linarith
  have hdual : InnerProductSpace.toDual ℝ E v = L := by
    ext w
    rw [InnerProductSpace.toDual_apply_apply]
    exact hL w
  rw [← hdual, LinearIsometryEquiv.symm_apply_apply]

/-- **Exercise 12.40(b)**, the uniform bound: if `fν →e f` with `fν` proper, lsc
and convex, and `x̄ ∈ int(dom f)` with `f(x̄)` finite, there are a neighborhood
`V` of `x̄` and a bounded `B` with `∂f(V) ⊂ B` and `∂fν(V) ⊂ B` for large `ν`. -/
theorem exists_eventually_svImage_subdifferential_subset {f : ℕ → E → EReal}
    {g : E → EReal} (hfp : ∀ n, IsProper (f n)) (hfl : ∀ n, LowerSemicontinuous (f n))
    (hfc : ∀ n, Convex ℝ (epigraph (f n))) (h : EpiConverges f g) {xbar : E}
    (hx : xbar ∈ interior (effectiveDomain g)) {c : ℝ} (hgx : g xbar = c) :
    ∃ V ∈ 𝓝 xbar, ∃ B : Set E, IsBounded B ∧ svImage (subdifferential g) V ⊆ B ∧
      ∀ᶠ n in atTop, svImage (subdifferential (f n)) V ⊆ B := by
  have hgc : Convex ℝ (epigraph g) := h.convex_epigraph hfc
  have hgl : LowerSemicontinuous g :=
    lowerSemicontinuous_of_isClosed_epigraph_ereal g (PKConverges.isClosed h)
  have hgp : IsProper g := isProper_of_convex_of_eq_coe hgc hgl hgx
  have hT : ∀ n, SvMaximalMonotone (subdifferential (f n)) := fun n ↦
    svMaximalMonotone_subdifferential_of_convex (hfp n) (hfl n) (hfc n)
  have hgr : GraphicalConverges (fun n ↦ subdifferential (f n)) (subdifferential g) :=
    h.graphicalConverges_subdifferential hfp hfl hfc hgp hgl hgc
  have hint : xbar ∈ interior (svDom (subdifferential g)) :=
    interior_maximal (fun y hy ↦ subdifferential_nonempty_of_convex_interior hgc hgp hy)
      isOpen_interior hx
  exact exists_eventually_svImage_subset_of_graphicalConverges hT hgr hint

/-- **Exercise 12.40(b)**, differentiable limits: if moreover `f` is
differentiable at `x̄` (formula 7(16)), then `∂fν(xν) → {∇f(x̄)}` whenever `xν → x̄`. -/
theorem pkConverges_subdifferential_of_hasERealGradientAt {f : ℕ → E → EReal}
    {g : E → EReal} (hfp : ∀ n, IsProper (f n)) (hfl : ∀ n, LowerSemicontinuous (f n))
    (hfc : ∀ n, Convex ℝ (epigraph (f n))) (h : EpiConverges f g) {xbar : E}
    (hx : xbar ∈ interior (effectiveDomain g)) {L : E →L[ℝ] ℝ}
    (hd : HasERealGradientAt g xbar L) {x : ℕ → E} (hxl : Tendsto x atTop (𝓝 xbar)) :
    PKConverges (fun n ↦ subdifferential (f n) (x n))
      {(InnerProductSpace.toDual ℝ E).symm L} := by
  have hgc : Convex ℝ (epigraph g) := h.convex_epigraph hfc
  have hgl : LowerSemicontinuous g :=
    lowerSemicontinuous_of_isClosed_epigraph_ereal g (PKConverges.isClosed h)
  have hgp : IsProper g :=
    isProper_of_convex_of_eq_coe hgc hgl (EReal.coe_toReal hd.2.1 hd.1).symm
  have hT : ∀ n, SvMaximalMonotone (subdifferential (f n)) := fun n ↦
    svMaximalMonotone_subdifferential_of_convex (hfp n) (hfl n) (hfc n)
  have hgr : GraphicalConverges (fun n ↦ subdifferential (f n)) (subdifferential g) :=
    h.graphicalConverges_subdifferential hfp hfl hfc hgp hgl hgc
  have hint : xbar ∈ interior (svDom (subdifferential g)) :=
    interior_maximal (fun y hy ↦ subdifferential_nonempty_of_convex_interior hgc hgp hy)
      isOpen_interior hx
  exact pkConverges_apply_of_graphicalConverges hT hgr hint
    (subdifferential_eq_singleton_of_hasERealGradientAt hgc hgp hx hd) hxl

/-- **Exercise 12.40(b)**, collected: for `fν →e f` with `fν` proper, lsc and
convex and `x̄ ∈ int(dom f)` with `f(x̄)` finite, the subgradient mappings are
uniformly bounded near `x̄` for large `ν`; if `f` is differentiable at `x̄`, then
`∂fν(xν) → {∇f(x̄)}` whenever `xν → x̄`. -/
theorem uniform_local_boundedness_of_subgradients {f : ℕ → E → EReal} {g : E → EReal}
    (hfp : ∀ n, IsProper (f n)) (hfl : ∀ n, LowerSemicontinuous (f n))
    (hfc : ∀ n, Convex ℝ (epigraph (f n))) (h : EpiConverges f g) {xbar : E}
    (hx : xbar ∈ interior (effectiveDomain g)) {c : ℝ} (hgx : g xbar = c) :
    (∃ V ∈ 𝓝 xbar, ∃ B : Set E, IsBounded B ∧ svImage (subdifferential g) V ⊆ B ∧
      ∀ᶠ n in atTop, svImage (subdifferential (f n)) V ⊆ B) ∧
    ∀ L : E →L[ℝ] ℝ, HasERealGradientAt g xbar L → ∀ x : ℕ → E, Tendsto x atTop (𝓝 xbar) →
      PKConverges (fun n ↦ subdifferential (f n) (x n))
        {(InnerProductSpace.toDual ℝ E).symm L} :=
  ⟨exists_eventually_svImage_subdifferential_subset hfp hfl hfc h hx hgx,
    fun _ hd _ hxl ↦ pkConverges_subdifferential_of_hasERealGradientAt hfp hfl hfc h hx hd hxl⟩

end UniformBoundedness

end RW
