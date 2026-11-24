/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Dualization of strong convexity (Proposition 12.60)

For a proper, lsc, convex `f` and `σ > 0`, `RW.stronglyConvexWith_dualization_tfae`
proves the equivalence of
(a) `f*` strongly convex with constant `σ` (`f*` is automatically proper);
(b) `f` finite and differentiable with `∇f` Lipschitz with constant `1/σ`;
(c) `⟪v₁ - v₀, x₁ - x₀⟫ ≥ σ‖v₁ - v₀‖²` on `gph ∂f`;
(d) `f = f₀ □ ½σ⁻¹‖·‖²` for a convex `f₀` (`epiSum`);
(e) `f` finite, differentiable, with `f(x') ≤ f(x) + ⟪∇f(x), x' - x⟫ + (2σ)⁻¹‖x' - x‖²`.

The cycle is (a) ⇒ (c) ⇒ (b) ⇒ (e) ⇒ (a) together with (a) ⇔ (d).  The book's
step (c) ⇒ (b) uses maximal monotonicity of `∂f` (12.17) and 12.55; here it is
replaced by a direct argument: the displacement `z ↦ z - P₁f(z)` is a contraction
with constant `1/(1 + σ)`, and its fixed points give `∂f(x) ≠ ∅` for every `x`.
(b) ⇒ (e) is the mean value theorem, (e) ⇒ (a) writes `f*` as a supremum of
quadratics with curvature `σ`, and (a) ⇔ (d) is 11.23(a) and 11.26(b).
-/

import RockafellarWets.Chapter12.StrongConvexity
import RockafellarWets.Chapter11.MoreauConjugacy
import RockafellarWets.Chapter11.SubgradientConjugacy
import RockafellarWets.Chapter11.DualMinimization
import RockafellarWets.Chapter10.ProximalStationarity
import Mathlib.Topology.MetricSpace.Contracting

open Set Filter Topology
open scoped InnerProductSpace NNReal

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
/-- The quadratic `moreauQuadratic σ⁻¹` is `(σ/2)‖·‖²`. -/
theorem moreauQuadratic_inv_eq (σ : ℝ) (x : E) : moreauQuadratic σ⁻¹ x = σ / 2 * ‖x‖ ^ 2 := by
  rw [moreauQuadratic, one_div, mul_inv, inv_inv]
  ring

omit [InnerProductSpace ℝ E] in
/-- The quadratic `moreauQuadratic σ` is `½σ⁻¹‖·‖²`. -/
theorem moreauQuadratic_eq_inv_div (σ : ℝ) (x : E) : moreauQuadratic σ x = σ⁻¹ / 2 * ‖x‖ ^ 2 := by
  rw [moreauQuadratic, one_div, mul_inv]
  ring

/-- **12.60 (b) ⇒ (e)**, the quadratic upper bound of a function whose gradient
is Lipschitz continuous with constant `1/σ`. -/
theorem le_add_inner_gradient_add_of_lipschitz_gradient [CompleteSpace E] {F : E → ℝ} {σ : ℝ}
    (hσ : 0 < σ) (hd : Differentiable ℝ F)
    (hL : ∀ x₀ x₁, ‖gradient F x₁ - gradient F x₀‖ ≤ σ⁻¹ * ‖x₁ - x₀‖) (x x' : E) :
    F x' ≤ F x + ⟪gradient F x, x' - x⟫_ℝ + 1 / (2 * σ) * ‖x' - x‖ ^ 2 := by
  set d := x' - x with hd_def
  set g := gradient F x with hg_def
  set k := 1 / (2 * σ) * ‖d‖ ^ 2 with hk_def
  let ψ : ℝ → ℝ := fun t ↦ F (x + t • d) - t * ⟪g, d⟫_ℝ - t ^ 2 * k
  let ψ' : ℝ → ℝ := fun t ↦ ⟪gradient F (x + t • d), d⟫_ℝ - ⟪g, d⟫_ℝ - 2 * t * k
  have hderiv : ∀ t, HasDerivAt ψ (ψ' t) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ ↦ x + t • d) d t := by
      simpa using ((hasDerivAt_id t).smul_const d).const_add x
    have h2 : HasDerivAt (fun t ↦ F (x + t • d)) ⟪gradient F (x + t • d), d⟫_ℝ t := by
      have := (hd (x + t • d)).hasGradientAt.hasFDerivAt.comp_hasDerivAt t h1
      simpa [InnerProductSpace.toDual_apply_apply] using this
    have h3 : HasDerivAt (fun t : ℝ ↦ t * ⟪g, d⟫_ℝ) ⟪g, d⟫_ℝ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪g, d⟫_ℝ
    have h4 : HasDerivAt (fun t : ℝ ↦ t ^ 2 * k) (2 * t * k) t := by
      simpa using (hasDerivAt_pow 2 t).mul_const k
    exact (h2.sub h3).sub h4
  obtain ⟨c, hc, hEq⟩ := exists_hasDerivAt_eq_slope ψ ψ' zero_lt_one
    (fun t _ ↦ (hderiv t).continuousAt.continuousWithinAt) (fun t _ ↦ hderiv t)
  have hneg : ψ' c ≤ 0 := by
    have hcs := real_inner_le_norm (gradient F (x + c • d) - g) d
    have hlip := hL x (x + c • d)
    have hnorm : ‖x + c • d - x‖ = c * ‖d‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hc.1.le]
    rw [hnorm] at hlip
    have hmul := mul_le_mul_of_nonneg_right hlip (norm_nonneg d)
    have hk' : 2 * c * k = σ⁻¹ * (c * ‖d‖) * ‖d‖ := by
      rw [hk_def]; field_simp
    simp only [ψ', ← inner_sub_left]
    rw [hk']
    linarith
  have h01 : ψ 1 - ψ 0 = ψ' c := by rw [hEq]; ring
  have hψ1 : ψ 1 = F x' - ⟪g, d⟫_ℝ - k := by
    simp only [ψ, one_smul, one_mul, one_pow, hd_def, add_sub_cancel]
  have hψ0 : ψ 0 = F x := by simp [ψ]
  rw [hψ1, hψ0] at h01
  linarith

/-- **12.60 (e) ⇒ (a)**, the conjugate computation: if `F` lies below its
quadratic upper models `F x + ⟪G x, · - x⟫ + (2σ)⁻¹‖· - x‖²` for a slope field
`G` (in 12.60, `G = ∇F`), then `F*` is the supremum of the quadratics
`v ↦ ⟪x, v⟫ - F x + (σ/2)‖v - G x‖²`, hence strongly convex with constant `σ`. -/
theorem fenchelConjugate_eq_iSup_quadratic_of_upper {F : E → ℝ} {G : E → E} {σ : ℝ}
    (hσ : 0 < σ) (hup : ∀ x x', F x' ≤ F x + ⟪G x, x' - x⟫_ℝ + 1 / (2 * σ) * ‖x' - x‖ ^ 2) :
    fenchelConjugate (fun x ↦ (F x : EReal)) =
      fun v ↦ ⨆ x, ((⟪x, v⟫_ℝ + -F x + σ / 2 * ‖v - G x‖ ^ 2 : ℝ) : EReal) := by
  funext v
  apply le_antisymm
  · refine iSup_le fun x' ↦ le_iSup_of_le x' ?_
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff, real_inner_comm]
    have : 0 ≤ σ / 2 * ‖v - G x'‖ ^ 2 := by positivity
    linarith
  · refine iSup_le fun x ↦ ?_
    set g := G x
    refine le_trans ?_ (le_fenchelConjugate _ (x + σ • (v - g)) v)
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
    have h := hup x (x + σ • (v - g))
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hσ.le, real_inner_smul_right] at h
    have hq : 1 / (2 * σ) * (σ * ‖v - g‖) ^ 2 = σ / 2 * ‖v - g‖ ^ 2 := by
      field_simp
    have hi : ⟪v, x + σ • (v - g)⟫_ℝ = ⟪x, v⟫_ℝ + σ * ⟪v, v - g⟫_ℝ := by
      rw [inner_add_right, real_inner_smul_right, real_inner_comm]
    have hn : ⟪v, v - g⟫_ℝ - ⟪g, v - g⟫_ℝ = ‖v - g‖ ^ 2 := by
      rw [← inner_sub_left, real_inner_self_eq_norm_sq]
    rw [hi]
    nlinarith

/-- **12.60 (e) ⇒ (a)**. -/
theorem stronglyConvexWith_fenchelConjugate_of_upper {F : E → ℝ} {G : E → E} {σ : ℝ}
    (hσ : 0 < σ) (hup : ∀ x x', F x' ≤ F x + ⟪G x, x' - x⟫_ℝ + 1 / (2 * σ) * ‖x' - x‖ ^ 2) :
    StronglyConvexWith σ (fenchelConjugate (fun x ↦ (F x : EReal))) := by
  rw [fenchelConjugate_eq_iSup_quadratic_of_upper hσ hup]
  exact StronglyConvexWith.iSup fun x ↦ stronglyConvexWith_quadratic σ x (G x) (-F x)

variable [FiniteDimensional ℝ E]

/-- **12.60 (a) ⇒ (c)**: strong convexity of `f*` makes `∂f = (∂f*)⁻¹` inversely
strongly monotone (11.3 and 12.59 (b) ⇒ (a) for `f*`). -/
theorem inner_sub_ge_of_stronglyConvexWith_fenchelConjugate {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) {σ : ℝ}
    (ha : StronglyConvexWith σ (fenchelConjugate f)) {x₀ v₀ x₁ v₁ : E}
    (h₀ : v₀ ∈ subdifferential f x₀) (h₁ : v₁ ∈ subdifferential f x₁) :
    σ * ‖v₁ - v₀‖ ^ 2 ≤ ⟪v₁ - v₀, x₁ - x₀⟫_ℝ := by
  have h₀' := (mem_subdifferential_fenchelConjugate_iff hp hl hc x₀ v₀).mpr h₀
  have h₁' := (mem_subdifferential_fenchelConjugate_iff hp hl hc x₁ v₁).mpr h₁
  have := ha.inner_sub_ge_of_mem_subdifferential (isProper_fenchelConjugate hp hl hc) h₀' h₁'
  rwa [real_inner_comm] at this

/-- Every point of a proper lsc convex function is a proximal point: the
selection `z ↦ J z ∈ P₁ f(z)` satisfies `z - J z ∈ ∂f(J z)` (1.25 and 10.2). -/
theorem exists_sub_mem_subdifferential_of_convex {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) (z : E) :
    ∃ x, z - x ∈ subdifferential f x := by
  obtain ⟨x, hx⟩ := proximalMappingEReal_nonempty hc hl hp one_pos z
  obtain ⟨v, hv, hvz⟩ := proximalMappingEReal_subset_inverse_subgradientShift hp one_pos z hx
  refine ⟨x, ?_⟩
  have : v = z - x := by rw [← hvz]; simp
  rwa [← this]

/-- **12.60 (c) ⇒ (b)**.  Inverse strong monotonicity of `∂f` makes the
displacement `z ↦ z - P₁f(z)` a contraction with constant `1/(1 + σ)`; its
fixed-point equations `P₁f(z) = x` show that `∂f(x) ≠ ∅` for every `x`, and the
inequality makes `∂f` single-valued with Lipschitz constant `1/σ`. -/
theorem exists_lipschitz_gradient_of_inner_sub_ge {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) {σ : ℝ} (hσ : 0 < σ)
    (hcoc : ∀ ⦃x₀ v₀ x₁ v₁ : E⦄, v₀ ∈ subdifferential f x₀ → v₁ ∈ subdifferential f x₁ →
      σ * ‖v₁ - v₀‖ ^ 2 ≤ ⟪v₁ - v₀, x₁ - x₀⟫_ℝ) :
    ∃ F : E → ℝ, f = (fun x ↦ (F x : EReal)) ∧ Differentiable ℝ F ∧
      ∀ x₀ x₁, ‖gradient F x₁ - gradient F x₀‖ ≤ σ⁻¹ * ‖x₁ - x₀‖ := by
  choose J hJ using exists_sub_mem_subdifferential_of_convex hp hl hc
  let R : E → E := fun z ↦ z - J z
  have hR : ∀ z₀ z₁, ‖R z₁ - R z₀‖ ≤ (1 + σ)⁻¹ * ‖z₁ - z₀‖ := by
    intro z₀ z₁
    have h := hcoc (hJ z₀) (hJ z₁)
    have hJd : J z₁ - J z₀ = (z₁ - z₀) - (R z₁ - R z₀) := by simp only [R]; abel
    rw [hJd, inner_sub_right, real_inner_self_eq_norm_sq] at h
    have hcs := real_inner_le_norm (z₁ - J z₁ - (z₀ - J z₀)) (z₁ - z₀)
    change σ * ‖R z₁ - R z₀‖ ^ 2 ≤ ⟪R z₁ - R z₀, z₁ - z₀⟫_ℝ - ‖R z₁ - R z₀‖ ^ 2 at h
    change ⟪R z₁ - R z₀, z₁ - z₀⟫_ℝ ≤ ‖R z₁ - R z₀‖ * ‖z₁ - z₀‖ at hcs
    rw [le_inv_mul_iff₀ (by positivity)]
    rcases (norm_nonneg (R z₁ - R z₀)).eq_or_lt with h0 | hpos
    · rw [← h0, mul_zero]
      exact norm_nonneg _
    · nlinarith
  have hdom : ∀ x, ∃ v, v ∈ subdifferential f x := by
    intro x
    let Ψ : E → E := fun z ↦ x + R z
    have hK : ContractingWith ⟨(1 + σ)⁻¹, by positivity⟩ Ψ := by
      refine ⟨?_, LipschitzWith.of_dist_le_mul fun z₀ z₁ ↦ ?_⟩
      · change (1 + σ)⁻¹ < (1 : ℝ)
        exact inv_lt_one_of_one_lt₀ (by linarith)
      · simp only [Ψ, dist_eq_norm, NNReal.coe_mk, add_sub_add_left_eq_sub]
        exact hR z₁ z₀
    let z := ContractingWith.fixedPoint Ψ hK
    have hz : Ψ z = z := hK.fixedPoint_isFixedPt
    have hJz : J z = x := by
      simp only [Ψ, R] at hz
      have : x - J z = 0 := by
        calc x - J z = x + (z - J z) - z := by abel
          _ = 0 := by rw [hz, sub_self]
      exact (sub_eq_zero.mp this).symm
    exact ⟨R z, hJz ▸ hJ z⟩
  choose G hG using hdom
  have hsingle : ∀ x, subdifferential f x = {G x} := by
    intro x
    ext w
    refine ⟨fun hw ↦ ?_, fun hw ↦ (mem_singleton_iff.mp hw) ▸ hG x⟩
    have h := hcoc (hG x) hw
    rw [sub_self, inner_zero_right] at h
    have hsq : ‖w - G x‖ ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg ‖w - G x‖]) (sq_nonneg _)
    exact mem_singleton_iff.mpr (sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq)))
  have hfin : ∀ x, f x = ((f x).toReal : EReal) := fun x ↦ by
    obtain ⟨c, hc'⟩ := (hG x).1
    rw [hc', EReal.toReal_coe]
  have hgrad : ∀ x, HasGradientAt (fun y ↦ (f y).toReal) (G x) x := fun x ↦
    ((subdifferential_eq_singleton_iff_hasGradientAt_of_convex hp hl hc).mp (hsingle x)).2
  refine ⟨fun y ↦ (f y).toReal, funext hfin, fun x ↦ (hgrad x).differentiableAt, ?_⟩
  intro x₀ x₁
  rw [(hgrad x₀).gradient, (hgrad x₁).gradient]
  have h := hcoc (hG x₀) (hG x₁)
  have hcs := real_inner_le_norm (G x₁ - G x₀) (x₁ - x₀)
  rw [← div_eq_inv_mul, le_div_iff₀ hσ]
  rcases (norm_nonneg (G x₁ - G x₀)).eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]
    exact norm_nonneg _
  · nlinarith

/-- **12.60 (a) ⇒ (d)**: with `f* = g + (σ/2)‖·‖²` for the proper lsc convex
`g`, Fenchel–Moreau and 11.26(b) give `f = g* □ ½σ⁻¹‖·‖²`. -/
theorem exists_eq_epiSum_of_stronglyConvexWith_fenchelConjugate {f : E → EReal}
    (hp : IsProper f) (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) {σ : ℝ}
    (hσ : 0 < σ) (ha : StronglyConvexWith σ (fenchelConjugate f)) :
    ∃ f₀ : E → EReal, Convex ℝ (epigraph f₀) ∧
      f = epiSum f₀ (fun x ↦ ((σ⁻¹ / 2 * ‖x‖ ^ 2 : ℝ) : EReal)) := by
  have hfsp : IsProper (fenchelConjugate f) := isProper_fenchelConjugate hp hl hc
  let g : E → EReal := fun v ↦ fenchelConjugate f v - ((σ / 2 * ‖v‖ ^ 2 : ℝ) : EReal)
  have hgc : Convex ℝ (epigraph g) := ha.convex_epigraph_sub
  have hgp : IsProper g := isProper_sub_coe hfsp _
  have hgl : LowerSemicontinuous g := by
    have he : g = fun v ↦ fenchelConjugate f v + ((-(σ / 2 * ‖v‖ ^ 2) : ℝ) : EReal) := by
      funext v
      simp only [g, sub_eq_add_neg, EReal.coe_neg]
    rw [he]
    exact lowerSemicontinuous_add_coe (lowerSemicontinuous_fenchelConjugate f) (by fun_prop)
  refine ⟨fenchelConjugate g, convex_epigraph_fenchelConjugate g, ?_⟩
  have hreg := fenchelConjugate_regularized_dual (isProper_fenchelConjugate hgp hgl hgc)
    (lowerSemicontinuous_fenchelConjugate g) (convex_epigraph_fenchelConjugate g) hσ
  rw [fenchelConjugate_fenchelConjugate_eq hgp hgl hgc] at hreg
  have hgq : (fun v ↦ g v + (moreauQuadratic σ⁻¹ v : EReal)) = fenchelConjugate f := by
    funext v
    simp only [g, moreauQuadratic_inv_eq, EReal.sub_add_cancel]
  rw [hgq, fenchelConjugate_fenchelConjugate_eq hp hl hc, moreauEnvelopeEReal_eq_epiSum,
    epiSum_comm] at hreg
  rw [hreg]
  congr 1
  funext x
  rw [moreauQuadratic_eq_inv_div]

omit [FiniteDimensional ℝ E] in
/-- **12.60 (d) ⇒ (a)**: by 11.23(a), `f = f₀ □ ½σ⁻¹‖·‖²` gives
`f* = f₀* + (σ/2)‖·‖²`.  Properness of `f` forces properness of `f₀`, and the
convexity of `f₀` is not needed for this direction. -/
theorem stronglyConvexWith_fenchelConjugate_of_eq_epiSum {f f₀ : E → EReal} (hp : IsProper f)
    {σ : ℝ} (hσ : 0 < σ) (hd : f = epiSum f₀ (fun x ↦ ((σ⁻¹ / 2 * ‖x‖ ^ 2 : ℝ) : EReal))) :
    StronglyConvexWith σ (fenchelConjugate f) := by
  set j : E → EReal := fun x ↦ ((σ⁻¹ / 2 * ‖x‖ ^ 2 : ℝ) : EReal) with hj_def
  have hj : j = fun x ↦ (moreauQuadratic σ x : EReal) := by
    funext x
    rw [moreauQuadratic_eq_inv_div]
  have hjp : IsProper j := ⟨⟨0, EReal.coe_lt_top _⟩, fun _ ↦ EReal.bot_lt_coe _⟩
  have hf₀p : IsProper f₀ := by
    constructor
    · obtain ⟨x, hx⟩ := hp.1
      rw [hd, epiSum_apply] at hx
      obtain ⟨w, hw⟩ := iInf_lt_iff.mp hx
      refine ⟨x - w, lt_top_iff_ne_top.mpr fun htop ↦ ?_⟩
      rw [htop, hj_def, EReal.top_add_coe] at hw
      exact lt_irrefl _ hw
    · intro z
      refine lt_of_le_of_ne bot_le fun hbot ↦ ?_
      have h := hp.2 z
      rw [hd, epiSum_apply] at h
      have hle := iInf_le (fun w ↦ f₀ (z - w) + j w) 0
      simp only [sub_zero, ← hbot, EReal.bot_add] at hle
      exact (lt_irrefl _ (h.trans_le hle))
  have hconj : fenchelConjugate f = fun v ↦ fenchelConjugate f₀ v + fenchelConjugate j v := by
    rw [hd]
    exact fenchelConjugate_epiSum hf₀p hjp
  have hjc : fenchelConjugate j = fun v ↦ ((σ / 2 * ‖v‖ ^ 2 : ℝ) : EReal) := by
    rw [hj, fenchelConjugate_moreauQuadratic hσ]
    funext v
    rw [moreauQuadratic_inv_eq]
  rw [hconj, hjc]
  obtain ⟨z, hz⟩ := hf₀p.1
  have hzr : f₀ z = ((f₀ z).toReal : EReal) := (EReal.coe_toReal hz.ne (hf₀p.2 z).ne').symm
  exact (stronglyConvexWith_add_quadratic_iff_convex
    (fun v ↦ (bot_lt_fenchelConjugate_of_finite hzr v).ne') σ).mpr
    (convex_epigraph_fenchelConjugate f₀)

/-- **Proposition 12.60** (dualization of strong convexity). -/
theorem stronglyConvexWith_dualization_tfae {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) {σ : ℝ} (hσ : 0 < σ) :
    List.TFAE [
      StronglyConvexWith σ (fenchelConjugate f),
      ∃ F : E → ℝ, f = (fun x ↦ (F x : EReal)) ∧ Differentiable ℝ F ∧
        ∀ x₀ x₁, ‖gradient F x₁ - gradient F x₀‖ ≤ σ⁻¹ * ‖x₁ - x₀‖,
      ∀ ⦃x₀ v₀ x₁ v₁ : E⦄, v₀ ∈ subdifferential f x₀ → v₁ ∈ subdifferential f x₁ →
        σ * ‖v₁ - v₀‖ ^ 2 ≤ ⟪v₁ - v₀, x₁ - x₀⟫_ℝ,
      ∃ f₀ : E → EReal, Convex ℝ (epigraph f₀) ∧
        f = epiSum f₀ (fun x ↦ ((σ⁻¹ / 2 * ‖x‖ ^ 2 : ℝ) : EReal)),
      ∃ F : E → ℝ, f = (fun x ↦ (F x : EReal)) ∧ Differentiable ℝ F ∧
        ∀ x x', F x' ≤ F x + ⟪gradient F x, x' - x⟫_ℝ + 1 / (2 * σ) * ‖x' - x‖ ^ 2] := by
  tfae_have 1 → 3 := fun ha _ _ _ _ h₀ h₁ ↦
    inner_sub_ge_of_stronglyConvexWith_fenchelConjugate hp hl hc ha h₀ h₁
  tfae_have 3 → 2 := exists_lipschitz_gradient_of_inner_sub_ge hp hl hc hσ
  tfae_have 2 → 5 := fun ⟨F, hF, hd, hL⟩ ↦
    ⟨F, hF, hd, le_add_inner_gradient_add_of_lipschitz_gradient hσ hd hL⟩
  tfae_have 5 → 1 := fun ⟨F, hF, _, hup⟩ ↦ by
    rw [hF]
    exact stronglyConvexWith_fenchelConjugate_of_upper hσ hup
  tfae_have 1 → 4 := exists_eq_epiSum_of_stronglyConvexWith_fenchelConjugate hp hl hc hσ
  tfae_have 4 → 1 := fun ⟨_, _, hd⟩ ↦ stronglyConvexWith_fenchelConjugate_of_eq_epiSum hp hσ hd
  tfae_finish

end RW
