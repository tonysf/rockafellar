/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: Hypoconvexity and subsmoothness of double envelopes

Proposition 12.62.  For a proper lsc `f` that is prox-bounded with threshold
`λ_f` and `0 < μ < λ < λ_f`, the Lasry–Lions double envelope

`e_{λ,μ}f(x) = sup_w {e_λ f(w) - (1/2μ)|w - x|²} = -e_μ[-e_λ f](x)`

of Example 1.46 is `μ`-proximal, `-e_{λ,μ}f` is `(λ - μ)`-proximal, and
`e_{λ,μ}f` is of class `C¹⁺`.

* `μ`-proximality holds for every `f`: `-e_μ g` is `μ`-proximal for every `g`
  by the proximal transform of Example 11.64.
* As in the book, `g₀ = -e_λ f + (2λ)⁻¹|·|²` is convex; here it is the
  conjugate `(f + (2λ)⁻¹|·|²)*(λ⁻¹·)` (11.26 via `moreauEnvelopeEReal_eq_sub_conjugate`),
  hence proper, lsc and convex, `e_λ f` being finite because `λ < λ_f`.
* With `η = λμ/(λ - μ)`, the identity
  `(2μ)⁻¹|w - x|² = (2λ)⁻¹|w|² + (2η)⁻¹|w - (η/μ)x|² - (2(λ - μ))⁻¹|x|²`
  gives `-e_{λ,μ}f(x) = e_η g₀((η/μ)x) - (2(λ - μ))⁻¹|x|²`.
* By Exercise 12.23, `e_η g₀` is finite and `C¹` with a gradient that is the
  Yosida regularization of `∂g₀`, maximal monotone and Lipschitz with constant
  `η⁻¹`.  A monotone gradient makes `e_η g₀` convex (Theorem 12.17), so
  `-e_{λ,μ}f + (2(λ - μ))⁻¹|·|²` is convex and finite, and 11.26(d) gives the
  `(λ - μ)`-proximality.  The formula also shows that `e_{λ,μ}f` is `C¹` with a
  globally Lipschitz gradient, in particular `C¹⁺`.
-/

import RockafellarWets.Chapter12.MoreauYosida
import RockafellarWets.Chapter12.StrongConvexityMonotonicity
import RockafellarWets.Chapter11.ProximalTransform
import RockafellarWets.Chapter11.ProductConjugacy

open Set Filter Topology
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Lasry–Lions double envelope `e_{λ,μ}f(x) = sup_w {e_λ f(w) - (1/2μ)|w - x|²}`
of Example 1.46. -/
noncomputable def doubleEnvelope (f : E → EReal) (lam mu : ℝ) (x : E) : EReal :=
  ⨆ w, moreauEnvelopeEReal f lam w - (((1 / (2 * mu)) * ‖w - x‖ ^ 2 : ℝ) : EReal)

omit [InnerProductSpace ℝ E] in
theorem ereal_neg_neg_add_coe (a : EReal) (r : ℝ) : -(-a + (r : EReal)) = a - (r : EReal) := by
  induction a using EReal.rec with
  | bot => simp
  | top => simp
  | coe a =>
    rw [← EReal.coe_neg, ← EReal.coe_add, ← EReal.coe_neg, ← EReal.coe_sub]
    congr 1
    ring

omit [InnerProductSpace ℝ E] in
/-- **Example 1.46**: `e_{λ,μ}f = -e_μ[-e_λ f]`. -/
theorem doubleEnvelope_eq_neg_moreauEnvelope_neg (f : E → EReal) (lam mu : ℝ) :
    doubleEnvelope f lam mu =
      fun x ↦ -moreauEnvelopeEReal (fun y ↦ -moreauEnvelopeEReal f lam y) mu x := by
  funext x
  rw [moreauEnvelopeEReal, ereal_neg_iInf]
  refine iSup_congr fun w ↦ ?_
  rw [ereal_neg_neg_add_coe]

/-- **Example 11.64**: every negative Moreau envelope `-e_t g` is `t`-proximal. -/
theorem proximalHull_neg_moreauEnvelope (t : ℝ) (g : E → EReal) :
    proximalHull (fun y ↦ -moreauEnvelopeEReal g t y) t = fun y ↦ -moreauEnvelopeEReal g t y := by
  rw [← isPairingEnvelope_proximalCoupling_iff, ← pairingConjugate_proximalCoupling]
  have h := isPairingEnvelope_conjugate (proximalCoupling t) g
  rwa [proximalCoupling_swap] at h

/-- **Proposition 12.62**, first assertion, valid for every `f` and `μ`:
`e_{λ,μ}f` is `μ`-proximal. -/
theorem proximalHull_doubleEnvelope (f : E → EReal) (lam mu : ℝ) :
    proximalHull (doubleEnvelope f lam mu) mu = doubleEnvelope f lam mu := by
  rw [doubleEnvelope_eq_neg_moreauEnvelope_neg]
  exact proximalHull_neg_moreauEnvelope mu _

/-- Infima commute with the addition of a real constant. -/
theorem ereal_iInf_add_coe {ι : Sort*} (g : ι → EReal) (r : ℝ) :
    (⨅ i, g i) + (r : EReal) = ⨅ i, g i + (r : EReal) :=
  (erealAddRightOrderIso r).map_iInf g

/-- The quadratic identity behind the double-envelope formula, with
`η = λμ/(λ - μ)`. -/
theorem double_envelope_quadratic_identity {lam mu : ℝ} (hmu : 0 < mu) (hml : mu < lam) (w x : E) :
    1 / (2 * mu) * ‖w - x‖ ^ 2 =
      1 / (2 * lam) * ‖w‖ ^ 2 + 1 / (2 * (lam * mu / (lam - mu))) *
        ‖w - (lam * mu / (lam - mu) / mu) • x‖ ^ 2 - 1 / (2 * (lam - mu)) * ‖x‖ ^ 2 := by
  have hl : 0 < lam := hmu.trans hml
  have hd : 0 < lam - mu := sub_pos.2 hml
  rw [norm_sub_sq_real, norm_sub_sq_real, norm_smul, real_inner_smul_right, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < lam * mu / (lam - mu) / mu)]
  field_simp
  ring

/-- Gradients of compositions with a scalar multiplication. -/
theorem hasGradientAt_comp_smul [CompleteSpace E] {G : E → ℝ} {g : E} {s : ℝ} {x : E}
    (h : HasGradientAt G g (s • x)) : HasGradientAt (fun y ↦ G (s • y)) (s • g) x := by
  rw [hasGradientAt_iff_hasFDerivAt] at h ⊢
  have hl : HasFDerivAt (fun y : E ↦ s • y) (s • ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id x).const_smul s
  have := h.comp x hl
  convert this using 1
  ext v
  simp [InnerProductSpace.toDual_apply_apply]

omit [InnerProductSpace ℝ E] in
/-- Composition with a scalar multiplication preserves convexity. -/
theorem convex_epigraph_comp_smul [Module ℝ E] {g : E → EReal} (hg : Convex ℝ (epigraph g))
    (c : ℝ) : Convex ℝ (epigraph (fun w ↦ g (c • w))) := by
  intro p hp q hq a b ha hb hab
  have h := hg (x := (c • p.1, p.2)) (y := (c • q.1, q.2)) hp hq ha hb hab
  change ((a • p + b • q).2 : EReal) ≥ g (c • (a • p + b • q).1)
  change (((a • (c • p.1, p.2) + b • (c • q.1, q.2)).2 : ℝ) : EReal) ≥
    g (a • (c • p.1, p.2) + b • (c • q.1, q.2)).1 at h
  simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add] at h ⊢
  rwa [smul_add, smul_comm c a, smul_comm c b]

section Setup

variable [FiniteDimensional ℝ E]

/-- Below the prox-threshold the Moreau envelope is finite. -/
theorem moreauEnvelopeEReal_eq_coe_of_lt_proxThreshold {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) {lam : ℝ} (hlam : 0 < lam)
    (hthr : (lam : EReal) < proxThreshold f) (x : E) :
    moreauEnvelopeEReal f lam x = (moreauEnvelopeReal f lam x : EReal) := by
  obtain ⟨y, hy⟩ := proximalMappingEReal_nonempty_of_lt_proxThreshold hp hl hlam hthr x
  obtain ⟨-, he⟩ := moreauEnvelope_eq_of_mem_proximalMapping hp hy
  rw [moreauEnvelopeReal, he, EReal.toReal_coe]

/-- The convex function `g₀ = (f + (2λ)⁻¹|·|²)*(λ⁻¹·)` of the proof of 12.62. -/
noncomputable def doubleEnvelopeKernel (f : E → EReal) (lam : ℝ) (w : E) : EReal :=
  fenchelConjugate (fun y ↦ f y + (moreauQuadratic lam y : EReal)) (lam⁻¹ • w)

/-- `g₀ = -e_λ f + (2λ)⁻¹|·|²`, a real-valued function below the threshold. -/
theorem doubleEnvelopeKernel_eq {f : E → EReal} (hp : IsProper f) (hl : LowerSemicontinuous f)
    {lam : ℝ} (hlam : 0 < lam) (hthr : (lam : EReal) < proxThreshold f) (w : E) :
    doubleEnvelopeKernel f lam w =
      ((moreauQuadratic lam w - moreauEnvelopeReal f lam w : ℝ) : EReal) := by
  have h := moreauEnvelopeEReal_eq_sub_conjugate f hlam w
  rw [moreauEnvelopeEReal_eq_coe_of_lt_proxThreshold hp hl hlam hthr w] at h
  change _ = _ - doubleEnvelopeKernel f lam w at h
  induction hk : doubleEnvelopeKernel f lam w using EReal.rec with
  | bot =>
    rw [hk] at h
    simp at h
  | top =>
    rw [hk] at h
    simp at h
  | coe c =>
    rw [hk, ← EReal.coe_sub, EReal.coe_eq_coe_iff] at h
    rw [EReal.coe_eq_coe_iff]
    linarith

omit [FiniteDimensional ℝ E] in
theorem convex_epigraph_doubleEnvelopeKernel (f : E → EReal) (lam : ℝ) :
    Convex ℝ (epigraph (doubleEnvelopeKernel f lam)) :=
  convex_epigraph_comp_smul (convex_epigraph_fenchelConjugate _) lam⁻¹

omit [FiniteDimensional ℝ E] in
theorem lowerSemicontinuous_doubleEnvelopeKernel (f : E → EReal) (lam : ℝ) :
    LowerSemicontinuous (doubleEnvelopeKernel f lam) :=
  (lowerSemicontinuous_fenchelConjugate _).comp (continuous_const_smul lam⁻¹)

end Setup

section MainResult

variable [FiniteDimensional ℝ E]

/-- The data of the proof of Proposition 12.62: with `η = λμ/(λ - μ)`, the
envelope `e_η g₀` is finite, convex, and `C¹` with a Lipschitz gradient, and
`-e_{λ,μ}f(x) = e_η g₀((η/μ)x) - (2(λ - μ))⁻¹|x|²`. -/
theorem doubleEnvelope_structure {f : E → EReal} (hp : IsProper f) (hl : LowerSemicontinuous f)
    {lam mu : ℝ} (hmu : 0 < mu) (hml : mu < lam) (hthr : (lam : EReal) < proxThreshold f) :
    ∃ G : E → ℝ, ContDiff ℝ 1 G ∧
      LipschitzWith (Real.toNNReal (lam * mu / (lam - mu))⁻¹) (gradient G) ∧
      Convex ℝ (epigraph (fun y ↦ (G y : EReal))) ∧
      ∀ x, -doubleEnvelope f lam mu x =
        ((G ((lam * mu / (lam - mu) / mu) • x) - 1 / (2 * (lam - mu)) * ‖x‖ ^ 2 : ℝ) : EReal) := by
  have hlam : 0 < lam := hmu.trans hml
  have hd : 0 < lam - mu := sub_pos.2 hml
  set η := lam * mu / (lam - mu) with hη
  have hηpos : 0 < η := by positivity
  set s := η / mu with hs
  -- the convex kernel `g₀`
  have hg₀eq := doubleEnvelopeKernel_eq hp hl hlam hthr
  have hg₀p : IsProper (doubleEnvelopeKernel f lam) := by
    refine ⟨⟨0, ?_⟩, fun w ↦ ?_⟩
    · rw [hg₀eq]; exact EReal.coe_lt_top _
    · rw [hg₀eq]; exact EReal.bot_lt_coe _
  have hg₀l := lowerSemicontinuous_doubleEnvelopeKernel f lam
  have hg₀c := convex_epigraph_doubleEnvelopeKernel f lam
  obtain ⟨hG, -, hYos, hYmax, hLip, hC1⟩ := moreauEnvelope_yosida hg₀p hg₀l hg₀c hηpos
  refine ⟨moreauEnvelopeReal (doubleEnvelopeKernel f lam) η, hC1, hLip, ?_, fun x ↦ ?_⟩
  · -- a `C¹` function with monotone gradient is convex (Theorem 12.17)
    set G := moreauEnvelopeReal (doubleEnvelopeKernel f lam) η with hGdef
    have hsub : subdifferential (fun y ↦ (G y : EReal)) = fun x ↦ {gradient G x} := by
      funext x
      exact (subdifferentials_of_smooth (hC1.contDiffAt (x := x))).1
    have hmono : SvMonotone (subdifferential (fun y ↦ (G y : EReal))) := by
      rw [hsub, ← hYos]
      exact hYmax.svMonotone
    refine convex_epigraph_of_svMonotone_subdifferential ⟨⟨0, EReal.coe_lt_top _⟩,
      fun y ↦ EReal.bot_lt_coe _⟩ ?_ hmono
    exact continuous_coe_real_ereal.comp_lowerSemicontinuous hC1.continuous.lowerSemicontinuous
      (fun a b hab ↦ EReal.coe_le_coe_iff.2 hab)
  · -- the formula for `-e_{λ,μ}f`
    have hrhs : ((moreauEnvelopeReal (doubleEnvelopeKernel f lam) η (s • x) -
          1 / (2 * (lam - mu)) * ‖x‖ ^ 2 : ℝ) : EReal) =
        ⨅ w, (doubleEnvelopeKernel f lam w + (((1 / (2 * η)) * ‖w - s • x‖ ^ 2 : ℝ) : EReal) +
          ((-(1 / (2 * (lam - mu)) * ‖x‖ ^ 2) : ℝ) : EReal)) := by
      rw [← ereal_iInf_add_coe]
      rw [show (⨅ w, (doubleEnvelopeKernel f lam w +
          (((1 / (2 * η)) * ‖w - s • x‖ ^ 2 : ℝ) : EReal))) =
          moreauEnvelopeEReal (doubleEnvelopeKernel f lam) η (s • x) from rfl, hG,
        ← EReal.coe_add]
      congr 1
    rw [hrhs, doubleEnvelope_eq_neg_moreauEnvelope_neg]
    simp only [neg_neg]
    rw [moreauEnvelopeEReal]
    refine iInf_congr fun w ↦ ?_
    rw [moreauEnvelopeEReal_eq_coe_of_lt_proxThreshold hp hl hlam hthr w, hg₀eq,
      ← EReal.coe_neg, ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_eq_coe_iff]
    have hid := double_envelope_quadratic_identity hmu hml w x
    simp only [moreauQuadratic]
    linarith

/-- **Proposition 12.62 (hypoconvexity and subsmoothness of double
envelopes)**: for a proper lsc `f`, prox-bounded with threshold `λ_f`, and
`0 < μ < λ < λ_f`, the double envelope `e_{λ,μ}f` is `μ`-proximal, `-e_{λ,μ}f` is
`(λ - μ)`-proximal, and `e_{λ,μ}f` is of class `C¹⁺`: it is finite and `C¹` with
a globally Lipschitz gradient. -/
theorem doubleEnvelope_hypoconvexity {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) {lam mu : ℝ} (hmu : 0 < mu) (hml : mu < lam)
    (hthr : (lam : EReal) < proxThreshold f) :
    proximalHull (doubleEnvelope f lam mu) mu = doubleEnvelope f lam mu ∧
      proximalHull (fun x ↦ -doubleEnvelope f lam mu x) (lam - mu) =
        (fun x ↦ -doubleEnvelope f lam mu x) ∧
      ∃ D : E → ℝ, (∀ x, doubleEnvelope f lam mu x = (D x : EReal)) ∧ ContDiff ℝ 1 D ∧
        ∃ K, LipschitzWith K (gradient D) := by
  have hd : 0 < lam - mu := sub_pos.2 hml
  obtain ⟨G, hC1, hLip, hconv, hformula⟩ := doubleEnvelope_structure hp hl hmu hml hthr
  set s := lam * mu / (lam - mu) / mu with hs
  set c : E → ℝ := fun x ↦ 1 / (2 * (lam - mu)) * ‖x‖ ^ 2 with hc
  refine ⟨proximalHull_doubleEnvelope f lam mu, ?_, ?_⟩
  · -- `(λ - μ)`-proximality through 11.26(d)
    have hg : (fun x ↦ -doubleEnvelope f lam mu x) = fun x ↦ ((G (s • x) - c x : ℝ) : EReal) :=
      funext hformula
    have hGc : Continuous G := hC1.continuous
    have hcont : Continuous fun x : E ↦ G (s • x) - c x := by
      simp only [hc]
      fun_prop
    rw [hg, proximalHull_eq_self_iff (f := fun x ↦ ((G (s • x) - c x : ℝ) : EReal))
      ⟨⟨0, EReal.coe_lt_top _⟩, fun _ ↦ EReal.bot_lt_coe _⟩ hd]
    refine ⟨continuous_coe_real_ereal.comp_lowerSemicontinuous hcont.lowerSemicontinuous
      (fun a b hab ↦ EReal.coe_le_coe_iff.2 hab), ?_⟩
    have he : (fun y ↦ ((G (s • y) - c y : ℝ) : EReal) + (moreauQuadratic (lam - mu) y : EReal)) =
        fun y ↦ (G (s • y) : EReal) := by
      funext y
      rw [← EReal.coe_add, EReal.coe_eq_coe_iff, moreauQuadratic, hc]
      ring
    rw [he]
    exact convex_epigraph_comp_smul hconv s
  · -- `C¹⁺`
    refine ⟨fun x ↦ c x - G (s • x), fun x ↦ ?_, ?_, ?_⟩
    · have := hformula x
      rw [← neg_neg (doubleEnvelope f lam mu x), this, ← EReal.coe_neg]
      congr 1
      ring
    · have : ContDiff ℝ 1 fun x : E ↦ G (s • x) := hC1.comp (contDiff_const_smul s)
      exact (contDiff_const.mul (contDiff_norm_sq ℝ)).sub this
    · have hgrad : ∀ x, HasGradientAt (fun x ↦ c x - G (s • x))
          ((1 / (lam - mu)) • x - s • gradient G (s • x)) x := by
        intro x
        have h1 : HasGradientAt c ((1 / (lam - mu)) • x) x := by
          have := hasGradientAt_half_mul_norm_sq (E := E) (1 / (lam - mu)) x
          have hd' : lam - mu ≠ 0 := hd.ne'
          have hfun : (fun z : E ↦ 1 / (lam - mu) / 2 * ‖z‖ ^ 2) = c := by
            funext z
            simp only [hc]
            field_simp
          rwa [hfun] at this
        have h2 : HasGradientAt (fun y ↦ G (s • y)) (s • gradient G (s • x)) x :=
          hasGradientAt_comp_smul
            ((hC1.differentiable one_ne_zero (s • x)).hasGradientAt)
        have h12 := (hasGradientAt_iff_hasFDerivAt.1 h1).sub (hasGradientAt_iff_hasFDerivAt.1 h2)
        rw [hasGradientAt_iff_hasFDerivAt, map_sub]
        exact h12
      have hgr : gradient (fun x ↦ c x - G (s • x)) =
          fun x ↦ (1 / (lam - mu)) • x - s • gradient G (s • x) :=
        funext fun x ↦ (hgrad x).gradient
      rw [hgr]
      have hL1 : LipschitzWith (Real.toNNReal (1 / (lam - mu)))
          (fun x : E ↦ (1 / (lam - mu)) • x) := by
        have := lipschitzWith_smul (β := E) (1 / (lam - mu))
        have he : ‖1 / (lam - mu)‖₊ = Real.toNNReal (1 / (lam - mu)) := by
          ext
          simp [abs_of_pos hd, hml.le]
        rwa [he] at this
      have hL2 : LipschitzWith (‖s‖₊ * (Real.toNNReal (lam * mu / (lam - mu))⁻¹ * ‖s‖₊))
          (fun x : E ↦ s • gradient G (s • x)) :=
        (lipschitzWith_smul s).comp (hLip.comp (lipschitzWith_smul s))
      exact ⟨_, hL1.sub hL2⟩

end MainResult

end RW
